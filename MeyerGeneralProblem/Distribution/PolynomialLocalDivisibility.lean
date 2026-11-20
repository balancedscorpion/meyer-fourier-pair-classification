module

public import MeyerGeneralProblem.Distribution.LocalPolynomialRootProjection
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

/-!
# Polynomial divisibility from local containment in a nontrivial fiber

A nonzero Bézout coefficient depending only on the transverse
parameters cannot vanish on a complex-open parameter box. Clearing
the denominators in the fraction field supplies that coefficient
whenever the polynomial fibers would be coprime.
-/

namespace MeyerGeneralProblem

noncomputable section

open Complex Metric Set
open scoped Polynomial

private theorem infinite_complex_ball (z : ℂ) (r : ℝ) (hr : 0 < r) :
    (ball z r).Infinite := by
  let e (t : ℝ) : ℂ := z + (t : ℂ)
  have he : Function.Injective e := fun x y h => Complex.ofReal_injective (add_left_cancel h)
  apply ((Set.Ioo_infinite hr).image he.injOn).mono
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_ball, dist_eq_norm]
  simpa only [e, add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2

/-- A complex multivariate polynomial vanishing on an open neighborhood
is the zero polynomial. -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open
    {ι : Type*} [Fintype ι] (D : MvPolynomial ι ℂ)
    (V : Set (ι → ℂ)) (hV : IsOpen V) (x₀ : ι → ℂ) (hx₀ : x₀ ∈ V)
    (hD : ∀ x ∈ V, MvPolynomial.eval x D = 0) : D = 0 := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx₀)
  apply MvPolynomial.funext_set (fun i => ball (x₀ i) r) (fun i => infinite_complex_ball (x₀ i) r hr)
  intro x hx
  rw [map_zero]
  apply hD x (hsub (mem_ball.mpr ((dist_pi_lt_iff hr).mpr ?_)))
  intro i
  exact mem_ball.mp (hx i (mem_univ i))

private theorem exists_cleared_polynomial_bezout
    (A : Type*) [CommRing A] [IsDomain A] (p q : A[X])
    (h : IsCoprime (p.map (algebraMap A (FractionRing A))) (q.map (algebraMap A (FractionRing A)))) :
    ∃ D : A, D ≠ 0 ∧ ∃ E F : A[X], E * p + F * q = Polynomial.C D := by
  let K := FractionRing A
  let j := algebraMap A K
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨du, hdu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) u
  obtain ⟨dv, hdv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) v
  let U := IsLocalization.integerNormalization (nonZeroDivisors A) u
  let V := IsLocalization.integerNormalization (nonZeroDivisors A) v
  refine ⟨du * dv, mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hdu)
    (mem_nonZeroDivisors_iff_ne_zero.mp hdv), Polynomial.C dv * U, Polynomial.C du * V, ?_⟩
  apply Polynomial.map_injective j (IsFractionRing.injective A K)
  have hu' : U.map j = Polynomial.C (j du) * u := by
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hu
  have hv' : V.map j = Polynomial.C (j dv) * v := by
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hv
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
    hu', hv', map_mul, Polynomial.C_mul]
  calc
    _ = (Polynomial.C (j du) * Polynomial.C (j dv)) * (u * p.map j + v * q.map j) := by ring
    _ = _ := by rw [huv, mul_one]

/-- Specialize the transverse coordinates and separately evaluate the
distinguished polynomial variable. -/
def polynomialCoordinateFiber {ι : Type*} (p : (MvPolynomial ι ℂ)[X])
    (x : ι → ℂ) (z : ℂ) : ℂ :=
  p.eval₂ (MvPolynomial.eval x) z

private theorem polynomialCoordinateFiber_continuous {ι : Type*} [Fintype ι]
    (p : (MvPolynomial ι ℂ)[X]) :
    Continuous (fun v : (ι → ℂ) × ℂ => polynomialCoordinateFiber p v.1 v.2) := by
  simp only [polynomialCoordinateFiber, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply continuous_finsetSum
  intro i _
  exact ((MvPolynomial.continuous_eval (p := p.coeff i)).comp continuous_fst).mul
    (continuous_snd.pow i)

private theorem polynomialCoordinateFiber_entire {ι : Type*}
    (p : (MvPolynomial ι ℂ)[X]) (x : ι → ℂ) :
    AnalyticOnNhd ℂ (polynomialCoordinateFiber p x) univ := by
  have hf : polynomialCoordinateFiber p x =
      (fun y : ℂ => ∑ i ∈ p.support, MvPolynomial.eval x (p.coeff i) * y ^ i) := by
    funext y
    simp only [polynomialCoordinateFiber, Polynomial.eval₂_eq_sum, Polynomial.sum]
  rw [hf]
  intro z _
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    analyticAt_const.mul (analyticAt_id.pow i))

/-- If an irreducible polynomial has a root on a fiber where it is
nonzero as a polynomial, then local containment of its zeros forces
divisibility in the actual coefficient ring. -/
theorem irreducible_dvd_of_local_polynomialFiber_zeroSet_containment
    {ι : Type*} [Fintype ι] (p q : (MvPolynomial ι ℂ)[X])
    (hirr : Irreducible p)
    (x₀ : ι → ℂ) (c : ℂ) (hzero : polynomialCoordinateFiber p x₀ c = 0)
    (hnz : ∃ z, polynomialCoordinateFiber p x₀ z ≠ 0)
    (W : Set ((ι → ℂ) × ℂ)) (hW : IsOpen W) (h₀ : (x₀, c) ∈ W)
    (hcontained : ∀ x z, (x, z) ∈ W →
      polynomialCoordinateFiber p x z = 0 → polynomialCoordinateFiber q x z = 0) :
    p ∣ q := by
  by_contra h
  let A := MvPolynomial ι ℂ
  let K := FractionRing A
  let _ : Field K := inferInstanceAs (Field (FractionRing (MvPolynomial ι ℂ)))
  let _ : GCDMonoid A := UniqueFactorizationMonoid.toGCDMonoid _
  let _ : IsBezout K[X] := inferInstance
  let j := algebraMap A K
  have hdegree : p.natDegree ≠ 0 := by
    intro hd
    obtain ⟨z, hz⟩ := hnz
    have hp := Polynomial.eq_C_of_natDegree_eq_zero hd
    apply hz
    rw [hp] at hzero ⊢
    simpa only [polynomialCoordinateFiber, Polynomial.eval₂_C] using hzero
  have hp := hirr.isPrimitive hdegree
  have hirr' : Irreducible (p.map j) :=
    (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr
  have hndvd : ¬ p.map j ∣ q.map j := fun hd =>
    h (hp.dvd_of_fraction_map_dvd_fraction_map hd)
  have hcop : IsCoprime (p.map j) (q.map j) := hirr'.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨D, hDne, E, F, hD⟩ := exists_cleared_polynomial_bezout A p q hcop
  have hev (x : ι → ℂ) (z : ℂ) :
      MvPolynomial.eval x D =
        polynomialCoordinateFiber E x z * polynomialCoordinateFiber p x z +
          polynomialCoordinateFiber F x z * polynomialCoordinateFiber q x z := by
    have h' := congrArg (Polynomial.eval₂RingHom (MvPolynomial.eval x) z) hD
    rw [map_add, map_mul, map_mul] at h'
    change polynomialCoordinateFiber E x z * polynomialCoordinateFiber p x z +
      polynomialCoordinateFiber F x z * polynomialCoordinateFiber q x z =
        (Polynomial.C D).eval₂ (MvPolynomial.eval x) z at h'
    rw [Polynomial.eval₂_C] at h'
    exact h'.symm
  obtain ⟨V, hV, hV₀, hVzero⟩ := parameter_obstruction_eq_zero_on_neighborhood
    (polynomialCoordinateFiber p) (polynomialCoordinateFiber q)
    (polynomialCoordinateFiber_continuous p) (polynomialCoordinateFiber_entire p)
    x₀ c hzero hnz W hW h₀ hcontained (fun v => MvPolynomial.eval v D)
    (polynomialCoordinateFiber E) (polynomialCoordinateFiber F) hev
  exact hDne (mvPolynomial_eq_zero_of_eval_eq_zero_on_open D V hV x₀ hV₀ hVzero)

end

end MeyerGeneralProblem
