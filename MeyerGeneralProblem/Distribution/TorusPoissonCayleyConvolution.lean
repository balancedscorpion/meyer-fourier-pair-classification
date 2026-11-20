module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyBoundaryMeasure
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyFourier

@[expose] public section

/-!
# Convolution by the unit-modulus Cayley boundary

Multiplication by the actual boundary is a complex linear isometric
equivalence of Haar `L²`. In torus Fourier coordinates its matrix
is convolution by the boundary coefficients.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal Topology

section Multiplication

variable {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ}

theorem memLp_mul_of_norm_eq_one {u : Θ → ℂ} (hMeas : AEStronglyMeasurable u μ)
    (hUnit : ∀ᵐ θ ∂μ, ‖u θ‖ = 1) (f : Lp ℂ 2 μ) :
    MemLp (fun θ => u θ * f θ) 2 μ :=
  (Lp.memLp f).congr_norm (hMeas.mul (Lp.aestronglyMeasurable f)) (by
    filter_upwards [hUnit] with θ hθ
    rw [norm_mul, hθ, one_mul])

def unitModulusMul {u : Θ → ℂ} (hMeas : AEStronglyMeasurable u μ)
    (hUnit : ∀ᵐ θ ∂μ, ‖u θ‖ = 1) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_mul_of_norm_eq_one hMeas hUnit f).toLp _

theorem coeFn_unitModulusMul {u : Θ → ℂ} (hMeas : AEStronglyMeasurable u μ)
    (hUnit : ∀ᵐ θ ∂μ, ‖u θ‖ = 1) (f : Lp ℂ 2 μ) :
    unitModulusMul hMeas hUnit f =ᵐ[μ] fun θ => u θ * f θ :=
  MemLp.coeFn_toLp _

theorem unitModulusMul_comp_eq {u v : Θ → ℂ}
    (hu : AEStronglyMeasurable u μ) (hU : ∀ᵐ θ ∂μ, ‖u θ‖ = 1)
    (hv : AEStronglyMeasurable v μ) (hV : ∀ᵐ θ ∂μ, ‖v θ‖ = 1)
    (h : ∀ᵐ θ ∂μ, u θ * v θ = 1) (f : Lp ℂ 2 μ) :
    unitModulusMul hu hU (unitModulusMul hv hV f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_unitModulusMul hu hU (unitModulusMul hv hV f), coeFn_unitModulusMul hv hV f, h]
    with θ h1 h2 h3
  rw [h1, h2, ← mul_assoc, h3, one_mul]

def unitModulusMultiplier {u : Θ → ℂ} (hMeas : AEStronglyMeasurable u μ)
    (hUnit : ∀ᵐ θ ∂μ, ‖u θ‖ = 1) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ := by
  have hConj := Complex.continuous_conj.comp_aestronglyMeasurable hMeas
  have hConjUnit : ∀ᵐ θ ∂μ, ‖conj (u θ)‖ = 1 := by
    filter_upwards [hUnit] with θ hθ
    rw [Complex.norm_conj, hθ]
  have hInv : ∀ᵐ θ ∂μ, u θ * conj (u θ) = 1 := by
    filter_upwards [hUnit] with θ hθ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ, one_pow, Complex.ofReal_one]
  refine
    { toLinearEquiv :=
        { toFun := unitModulusMul hMeas hUnit
          invFun := unitModulusMul hConj hConjUnit
          left_inv := unitModulusMul_comp_eq hConj hConjUnit hMeas hUnit
            (hInv.mono fun θ hθ => (mul_comm _ _).trans hθ)
          right_inv := unitModulusMul_comp_eq hMeas hUnit hConj hConjUnit hInv
          map_add' := ?_
          map_smul' := ?_ }
      norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [coeFn_unitModulusMul hMeas hUnit (f + g), coeFn_unitModulusMul hMeas hUnit f,
      coeFn_unitModulusMul hMeas hUnit g, Lp.coeFn_add f g,
      Lp.coeFn_add (unitModulusMul hMeas hUnit f) (unitModulusMul hMeas hUnit g)]
      with θ h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h5, h2, h3, h4, mul_add]
  · intro c f
    apply Lp.ext
    filter_upwards [coeFn_unitModulusMul hMeas hUnit (c • f), coeFn_unitModulusMul hMeas hUnit f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (unitModulusMul hMeas hUnit f)]
      with θ h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    rw [RingHom.id_apply, h1, h4, h2, h3]
    ring
  · intro f
    change ‖unitModulusMul hMeas hUnit f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [coeFn_unitModulusMul hMeas hUnit f, hUnit] with θ h1 h2
    rw [h1, norm_mul, h2, one_mul]

end Multiplication

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyConvolutionCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

section PhaseConvolution

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The unitary convolution operator obtained from the actual Cayley boundary. -/
def torusPoissonCayleyConvolution :
    lp (fun _ : d → ℤ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : d → ℤ => ℂ) 2 := by
  let u := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let e := (mFourierBasis (d := d)).repr
  exact e.symm.trans ((unitModulusMultiplier (Lp.aestronglyMeasurable u)
    (ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance)).trans e)

/-- The actual Cayley boundary differs from one almost everywhere, so
multiplication by it has no nonzero fixed vector. -/
theorem eq_zero_of_torusPoissonCayleyConvolution_fixed
    (f : lp (fun _ : d → ℤ => ℂ) 2)
    (hf : torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance f = f) :
    f = 0 := by
  let u := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let e := (mFourierBasis (d := d)).repr
  let hU := ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let g := e.symm f
  have hFix : unitModulusMul (Lp.aestronglyMeasurable u) hU g = g := by
    apply e.injective
    rw [show e g = f from e.apply_symm_apply f]
    exact hf
  have hG : g = 0 := by
    apply Lp.ext
    filter_upwards [coeFn_unitModulusMul (Lp.aestronglyMeasurable u) hU g,
      ae_ne_one_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance,
      Lp.coeFn_zero ℂ 2 volume] with θ hEval hOne hZero
    rw [hFix] at hEval
    have hMul : (u θ - 1) * g θ = 0 := by
      rw [sub_mul, one_mul, ← hEval, sub_self]
    rw [hZero]
    exact (mul_eq_zero.mp hMul).resolve_left (sub_ne_zero.mpr hOne)
  rw [← e.apply_symm_apply f]
  change e g = 0
  rw [hG, map_zero]

/-- The q-th finite difference along Cayley powers has trivial kernel. -/
theorem torusPoissonCayleyConvolution_sub_one_pow_injective (q : ℕ) :
    let U : (lp (fun _ : d → ℤ => ℂ) 2) →L[ℂ] (lp (fun _ : d → ℤ => ℂ) 2) :=
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance : _ ≃ₗᵢ[ℂ] _)
    let D := U - (1 : (lp (fun _ : d → ℤ => ℂ) 2) →L[ℂ] _)
    Function.Injective (fun f => (D ^ q) f) := by
  intro U D
  have hInjective : Function.Injective (fun f => D f) := by
    intro f g hfg
    change D f = D g at hfg
    have hZero : D (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    have hFixed : torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance (f - g) = f - g :=
      sub_eq_zero.mp hZero
    exact sub_eq_zero.mp
      (eq_zero_of_torusPoissonCayleyConvolution_fixed β S T hT hCont hCount hAdvance (f - g) hFixed)
  induction q with
  | zero =>
    rw [pow_zero]
    exact Function.injective_id
  | succ q ih =>
    rw [pow_succ]
    exact ih.comp hInjective

/-- A matrix entry of the actual unitary is the boundary coefficient at
the difference of its two indices. -/
theorem torusPoissonCayleyConvolution_single (m n : d → ℤ) :
    torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)) n =
      mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) (n - m) := by
  let u := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let e := (mFourierBasis (d := d)).repr
  let hU := ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  change e (unitModulusMul (Lp.aestronglyMeasurable u) hU (e.symm (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)))) n =
    mFourierCoeff u (n - m)
  change (mFourierBasis (d := d)).repr
      (unitModulusMul (Lp.aestronglyMeasurable u) hU
        ((mFourierBasis (d := d)).repr.symm (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)))) n = _
  rw [HilbertBasis.repr_symm_single, coe_mFourierBasis, mFourierBasis_repr]
  simp only [mFourierCoeff, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [coeFn_unitModulusMul (Lp.aestronglyMeasurable u) hU (mFourierLp 2 m),
    coeFn_mFourierLp 2 m] with θ h1 h2
  rw [h1, h2]
  calc
    mFourier (-n) θ * (u θ * mFourier m θ) =
        (mFourier (-n) θ * mFourier m θ) * u θ := by ring
    _ = mFourier (-(n - m)) θ * u θ := by
        rw [← mFourier_add, neg_sub, sub_eq_add_neg, add_comm m (-n)]

/-- Each output coordinate is the convergent convolution sum for an
arbitrary square-summable input. -/
theorem hasSum_torusPoissonCayleyConvolution (f : lp (fun _ : d → ℤ => ℂ) 2) (n : d → ℤ) :
    HasSum (fun m : d → ℤ =>
      mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) (n - m) * f m)
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance f n) := by
  let C := torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance
  let L := (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 n).comp C.toContinuousLinearEquiv.toContinuousLinearMap
  have h : HasSum (fun m : d → ℤ => C (lp.single 2 m (f m)) n) (C f n) :=
    L.hasSum (lp.hasSum_single (by norm_num) f)
  have hTerm (m : d → ℤ) : C (lp.single 2 m (f m)) n =
      mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) (n - m) * f m := by
    have hSingle : lp.single 2 m (f m) = (f m) • lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ) := by
      ext j
      by_cases hj : j = m
      · subst j
        simp [lp.coeFn_smul]
      · simp [lp.coeFn_smul, Pi.single_eq_of_ne hj, Pi.smul_apply]
    rw [hSingle, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      show C (lp.single (E := fun _ : d → ℤ => ℂ) 2 m (1 : ℂ)) n = _ from
        torusPoissonCayleyConvolution_single β S T hT hCont hCount hAdvance m n, mul_comm]
  simpa only [hTerm] using h


/-- Every matrix entry for a negative physical shift vanishes. -/
theorem torusPoissonCayleyConvolution_single_eq_zero_of_neg (m n : d → ℤ)
    (hn : torusDirectionalFrequency β (n - m) < 0) :
    torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance (lp.single 2 m 1) n = 0 := by
  rw [torusPoissonCayleyConvolution_single]
  exact mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance _ hn

end PhaseConvolution

end
end MeyerGeneralProblem
