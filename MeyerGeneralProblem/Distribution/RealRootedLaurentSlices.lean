module

public import MeyerGeneralProblem.Distribution.FrequencyTorusNonvanishing
public import MeyerGeneralProblem.Distribution.OrderedLaurentGrowth
public import MeyerGeneralProblem.Distribution.FiniteIntegerGrading
public import MeyerGeneralProblem.Distribution.LaurentSpectralRealization
public import MeyerGeneralProblem.Distribution.PolynomialDiscDeformation
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Root-free integral slices of a real-rooted exponential polynomial

Damp the positive real frequencies by moving into the upper half-plane.
Full torus nonvanishing keeps each damped polynomial nonvanishing on
the unit circle. For sufficiently large damping the constant term
dominates on the closed disk. Deforming to zero damping gives the
required root-free graded slice.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped Topology
open Adaptive

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

private theorem exists_character_one_eq_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ y : ℝ, combModulationCharacter 1 y = z := by
  refine ⟨Complex.arg z / (2 * Real.pi), ?_⟩
  have ha := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at ha
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I * (1 : ℂ) * ((Complex.arg z / (2 * Real.pi) : ℝ) : ℂ)) :=
      combModulationCharacter_eq_exp _ _
    _ = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
      congr 1
      push_cast
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    _ = z := ha

private theorem character_at_integral_realFrequency
    (d : ℤ) (hd : 0 ≤ d) (y : ℝ) :
    combModulationCharacter (d : ℝ) y = (combModulationCharacter 1 y) ^ d.toNat := by
  rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  have h : (d.toNat : ℂ) = (d : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hd
  push_cast
  rw [h]
  ring

private theorem imaginaryExponential_eq_damping (a t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.exp (-(2 * Real.pi * a) * t) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (a : ℂ) * (t : ℂ)) * Complex.I_sq

private theorem exists_damping_tail_small [DecidableEq G]
    (L : G →+ ℝ) (p : G →₀ ℂ) (hp₀ : p 0 ≠ 0)
    (hpos : ∀ m ∈ p.support, m ≠ 0 → 0 < L m) :
    ∃ t : ℝ, 0 < t ∧
      ∑ m ∈ p.support.erase 0, ‖p m‖ * Real.exp (-(2 * Real.pi * L m) * t) < ‖p 0‖ := by
  classical
  let E := p.support.erase 0
  have hlim : Tendsto (fun t : ℝ => ∑ m ∈ E, ‖p m‖ * Real.exp (-(2 * Real.pi * L m) * t)) atTop (𝓝 0) := by
    have hterm (m : G) (hm : m ∈ E) :
        Tendsto (fun y : ℝ => ‖p m‖ * Real.exp (-(2 * Real.pi * L m) * y)) atTop (𝓝 0) := by
      have hm' := Finset.mem_erase.mp hm
      have hδ := hpos m hm'.2 hm'.1
      have hneg : -(2 * Real.pi * L m) < 0 := neg_lt_zero.mpr (by positivity)
      have ht := Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id)
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (tendsto_const_nhds (x := ‖p m‖)).mul ht
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum E hterm
  exact ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (norm_pos_iff.mpr hp₀)))).exists

/-- Real-rootedness gives every positive integral slice root-free in the
open disk when the denominator's minimal label has been shifted to zero. -/
theorem realRooted_normalized_phaseGradedPolynomial_ne_zero
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (ν : G →+ ℤ) (p : AddMonoidAlgebra ℂ G) (hp₀ : p.coeff 0 ≠ 0)
    (hLpos : ∀ m ∈ p.coeff.support, m ≠ 0 → 0 < L m)
    (hνpos : ∀ m ∈ p.coeff.support, m ≠ 0 → 0 < ν m)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    (phaseGradedPolynomial ν (originalLaurentPhase L x) p).eval z ≠ 0 := by
  classical
  let a (t : ℝ) (m : G) := p.coeff m * combModulationCharacter (L m) x *
    (Real.exp (-(2 * Real.pi * L m) * t) : ℂ)
  let P (t : ℝ) : Polynomial ℂ := ∑ m ∈ p.coeff.support, Polynomial.monomial (ν m).toNat (a t m)
  have hEval (t : ℝ) (w : ℂ) :
      (P t).eval w = ∑ m ∈ p.coeff.support, a t m * w ^ (ν m).toNat := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  have hnu (m : G) (hm : m ∈ p.coeff.support) : 0 ≤ ν m := by
    by_cases he : m = 0
    · simp [he]
    · exact (hνpos m hm he).le
  have h0 : (0 : G) ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hp₀
  have ha0 (t : ℝ) : a t 0 = p.coeff 0 := by
    simp [a, combModulationCharacter_zero_left]
  have heq : P 0 = phaseGradedPolynomial ν (originalLaurentPhase L x) p := by
    rw [phaseGradedPolynomial_eq_sum_monomial ν _ p hnu]
    apply Finset.sum_congr rfl
    intro m _
    change Polynomial.monomial (ν m).toNat (a 0 m) =
      Polynomial.monomial (ν m).toNat (p.coeff m * combModulationCharacter (L m) x)
    simp [a]
  rw [← heq]
  apply polynomial_openUnitDisc_ne_zero_of_deformation P
  · simp_rw [hEval]
    apply continuous_finsetSum
    intro m _
    dsimp [a]
    fun_prop
  · intro t
    rw [hEval, Finset.sum_eq_single_of_mem 0 h0]
    · simpa [ha0] using hp₀
    · intro m hm hne
      have hp := hνpos m hm hne
      have hpos : (ν m).toNat ≠ 0 := by omega
      simp [hpos]
  · intro t ht w hw
    obtain ⟨y, hy⟩ := exists_character_one_eq_of_norm_eq_one w hw
    let νR : G →+ ℝ := (Int.castAddHom ℝ).comp ν
    let θ := torusLinearFlow (fun i => L (b i)) x + torusLinearFlow (fun i => νR (b i)) y
    have hθ : ∑ m ∈ p.coeff.support, a t m * w ^ (ν m).toNat =
        ∑ m ∈ p.coeff.support, p.coeff m * basisTorusCharacter b m θ *
          Complex.exp (2 * Real.pi * Complex.I * (L m : ℂ) * ((t : ℂ) * Complex.I)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [show basisTorusCharacter b m θ =
        combModulationCharacter (L m) x * combModulationCharacter (ν m : ℝ) y by
          unfold θ
          rw [basisTorusCharacter_add_phase, basisTorusCharacter_flow, basisTorusCharacter_flow]
          rfl, imaginaryExponential_eq_damping,
        character_at_integral_realFrequency _ (hnu m hm), hy]
      unfold a
      ac_rfl
    rw [hEval, hθ]
    have hp : p.coeff ≠ 0 := fun he => hp₀ (by simp [he])
    apply realRooted_exponentialSum_basisTorus_ne_zero b L hL p.coeff hp hroot
    simpa only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero] using ht.ne'
  · obtain ⟨t, ht, hsmall⟩ := exists_damping_tail_small L p.coeff hp₀ hLpos
    refine ⟨t, ht, fun w hw => ?_⟩
    let Z m := a t m * w ^ (ν m).toNat
    have hsplit : (P t).eval w = (∑ m ∈ p.coeff.support.erase 0, Z m) + p.coeff 0 := by
      rw [hEval, ← Finset.sum_erase_add p.coeff.support Z h0]
      congr 1
      simp [Z, ha0]
    have hlt : ‖∑ m ∈ p.coeff.support.erase 0, Z m‖ < ‖p.coeff 0‖ := by
      apply ((norm_sum_le _ _).trans ?_).trans_lt hsmall
      apply Finset.sum_le_sum
      intro m _
      change ‖Z m‖ ≤ ‖p.coeff m‖ * Real.exp (-(2 * Real.pi * L m) * t)
      simp only [Z, a, norm_mul, norm_pow, norm_combModulationCharacter, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hw)
    intro he
    have h := eq_neg_of_add_eq_zero_left (hsplit.symm.trans he)
    have hx := congrArg norm h
    rw [norm_neg] at hx
    exact (ne_of_lt hlt) hx
  · exact hz

/-- Evaluation of a single Laurent label in the original entire frequency direction. -/
def complexExponentialCharacter (L : G →+ ℝ) (z : ℂ) : Multiplicative G →* ℂ where
  toFun m := Complex.exp (2 * Real.pi * Complex.I * (L m.toAdd : ℂ) * z)
  map_one' := by simp
  map_mul' m n := by
    change Complex.exp (2 * Real.pi * Complex.I * (L (m.toAdd + n.toAdd) : ℂ) * z) = _
    rw [← Complex.exp_add]
    simp only [map_add, Complex.ofReal_add]
    congr 1
    ring

private def exponentialLaurentEvaluation (L : G →+ ℝ) (z : ℂ) : AddMonoidAlgebra ℂ G →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ) (complexExponentialCharacter L z)
    (fun _ _ => Commute.all _ _)

private theorem exponentialLaurentEvaluation_apply (L : G →+ ℝ) (z : ℂ)
    (p : AddMonoidAlgebra ℂ G) :
    exponentialLaurentEvaluation L z p = complexExponentialSum L p.coeff z := by
  classical
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  simp only [Finsupp.sum, map_sum, exponentialLaurentEvaluation,
    AddMonoidAlgebra.liftNCRingHom_single, RingHom.id_apply, complexExponentialCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, complexExponentialSum]
  rfl

/-- Entire exponential evaluation of finite Laurent polynomials preserves products. -/
theorem complexExponentialSum_laurent_mul (L : G →+ ℝ) (z : ℂ)
    (p q : AddMonoidAlgebra ℂ G) :
    complexExponentialSum L (p * q).coeff z =
      complexExponentialSum L p.coeff z * complexExponentialSum L q.coeff z := by
  simp only [← exponentialLaurentEvaluation_apply, map_mul]

private theorem complexExponentialSum_laurent_single (L : G →+ ℝ) (z : ℂ)
    (m : G) (c : ℂ) :
    complexExponentialSum L (AddMonoidAlgebra.single m c).coeff z =
      c * Complex.exp (2 * Real.pi * Complex.I * (L m : ℂ) * z) := by
  rw [← exponentialLaurentEvaluation_apply]
  simp [exponentialLaurentEvaluation, complexExponentialCharacter]

/-- Reversing the ordering of frequencies reflects the entire symbol. -/
theorem complexExponentialSum_neg_frequency (L : G →+ ℝ) (p : G →₀ ℂ) (z : ℂ) :
    complexExponentialSum (-L) p z = complexExponentialSum L p (-z) := by
  unfold complexExponentialSum
  apply Finset.sum_congr rfl
  intro m _
  simp only [AddMonoidHom.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul]

/-- Every integral direction sharing the original extremum is root-free
for a real-rooted denominator. -/
theorem realRooted_rootFreeNormalizedLaurentSlices
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (ν : G →+ ℤ) (p : AddMonoidAlgebra ℂ G) (m : G) (hm : p.coeff m ≠ 0)
    (hLmin : ∀ n ∈ p.coeff.support, n ≠ m → L m < L n)
    (hνmin : ∀ n ∈ p.coeff.support, n ≠ m → ν m < ν n)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0) :
    RootFreeNormalizedLaurentSlices ν L p m := by
  let P := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹ * p
  have hP₀ : P.coeff 0 ≠ 0 := by
    have h : P.coeff 0 = 1 := by
      dsimp [P]
      rw [normalizedLaurent_coeff, add_zero, inv_mul_cancel₀ hm]
    rw [h]
    exact one_ne_zero
  have hpos (n : G) (hn : n ∈ P.coeff.support) : m + n ∈ p.coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    intro he
    have hh := Finsupp.mem_support_iff.mp hn
    dsimp [P] at hh
    exact hh (by rw [normalizedLaurent_coeff, he, mul_zero])
  have hLP (n : G) (hn : n ∈ P.coeff.support) (he : n ≠ 0) : 0 < L n := by
    have h := hLmin (m + n) (hpos n hn) (by simpa using he)
    rwa [map_add, lt_add_iff_pos_right] at h
  have hνP (n : G) (hn : n ∈ P.coeff.support) (he : n ≠ 0) : 0 < ν n := by
    have h := hνmin (m + n) (hpos n hn) (by simpa using he)
    rwa [map_add, lt_add_iff_pos_right] at h
  have hrootP (z : ℂ) (hz : z.im ≠ 0) : complexExponentialSum L P.coeff z ≠ 0 := by
    dsimp [P]
    rw [complexExponentialSum_laurent_mul, complexExponentialSum_laurent_single]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hm) (Complex.exp_ne_zero _)) (hroot z hz)
  intro x z hz
  exact realRooted_normalized_phaseGradedPolynomial_ne_zero b L hL ν P hP₀ hLP hνP hrootP x z hz

private theorem shiftedNumerator_orderedExpansion (p R : AddMonoidAlgebra ℂ G)
    (m b n : G) :
    orderedLaurentExpansion p (AddMonoidAlgebra.single b 1 * R) m (b + n) =
      orderedLaurentExpansion p R m n := by
  let S : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single (-m) (p.coeff m)⁻¹
  let q := 1 - S * p
  let B : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single b 1
  change (∑' k : ℕ, (q ^ k * (S * (B * R))).coeff (b + n)) =
    ∑' k : ℕ, (q ^ k * (S * R)).coeff n
  apply tsum_congr
  intro k
  rw [show q ^ k * (S * (B * R)) = B * (q ^ k * (S * R)) by ac_rfl]
  simp [B]

/-- For a real-rooted denominator, an arbitrary finite Laurent numerator
has polynomially bounded coefficients in the expansion at its minimum. -/
theorem orderedLaurentExpansion_polynomialGrowth_of_realRooted
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (m : G) (hm : p.coeff m ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ m → L m < L n)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0) :
    ∃ M : ℝ, ∃ k : ℕ, 0 ≤ M ∧ ∀ n : G,
      ‖orderedLaurentExpansion p R m n‖ ≤ M * (1 + |L n|) ^ k := by
  classical
  by_cases hR : R = 0
  · subst R
    exact ⟨0, 0, le_rfl, fun n => by simp [orderedLaurentExpansion, orderedGeometricExpansion]⟩
  have hR' : R.coeff ≠ 0 := fun h => hR (by ext j; simp [h])
  obtain ⟨r, _, hr⟩ := R.coeff.support.exists_min_image L (Finsupp.support_nonempty_iff.mpr hR')
  let g := m - r
  let A : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.single g 1 * R
  have hA (n : G) (hn : n ∈ A.coeff.support) : L m ≤ L n := by
    have hcoeff : A.coeff n = R.coeff (-g + n) := by simp [A]
    have hsup : -g + n ∈ R.coeff.support := Finsupp.mem_support_iff.mpr
      (hcoeff ▸ Finsupp.mem_support_iff.mp hn)
    have hh := hr _ hsup
    rw [map_add, map_neg] at hh
    dsimp [g] at hh
    rw [map_sub] at hh
    linarith
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := G)
  obtain ⟨ν, hν, hAν⟩ := exists_integralGrading_preserving_extreme L hL
    p.coeff.support A.coeff.support m hmin hA
  obtain ⟨C, k, hC, h⟩ := orderedLaurentExpansion_polynomialGrowth_of_rootFreeNormalizedSlices
    ν L hL p A m hm hν hmin hAν hA (realRooted_rootFreeNormalizedLaurentSlices b L hL ν p m hm hmin hν hroot)
  refine ⟨C * (1 + |L g|) ^ k, k, by positivity, fun n => ?_⟩
  have hle : 1 + |L (g + n)| ≤ (1 + |L g|) * (1 + |L n|) := by
    rw [map_add]
    nlinarith [abs_add_le (L g) (L n), mul_nonneg (abs_nonneg (L g)) (abs_nonneg (L n))]
  rw [← shiftedNumerator_orderedExpansion p R m g n]
  change ‖orderedLaurentExpansion p A m (g + n)‖ ≤ _
  exact (h (g + n)).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle k) hC).trans_eq
    (by rw [mul_pow, mul_assoc]))

/-- Real-rootedness alone supplies the polynomial coefficient bound on the
full original Laurent jump, for every finite numerator. -/
theorem orderedLaurentJump_polynomialGrowth_of_realRooted
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0) :
    ∃ M : ℝ, ∃ k : ℕ, 0 ≤ M ∧ ∀ n : G,
      ‖orderedLaurentJump p R lo hi n‖ ≤ M * (1 + |L n|) ^ k := by
  have hL' : Function.Injective (-L) := by
    intro x y h
    apply hL
    simpa only [AddMonoidHom.neg_apply, neg_inj] using h
  have hmax' : ∀ n ∈ p.coeff.support, n ≠ hi → (-L) hi < (-L) n := by
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax
  have hroot' (z : ℂ) (hz : z.im ≠ 0) : complexExponentialSum (-L) p.coeff z ≠ 0 := by
    rw [complexExponentialSum_neg_frequency]
    exact hroot (-z) (by simpa using hz)
  obtain ⟨Mlo, klo, hMlo, hblo⟩ :=
    orderedLaurentExpansion_polynomialGrowth_of_realRooted L hL p R lo hlo hmin hroot
  obtain ⟨Mhi, khi, hMhi, hbhi⟩ :=
    orderedLaurentExpansion_polynomialGrowth_of_realRooted (-L) hL' p R hi hhi hmax' hroot'
  simp only [AddMonoidHom.neg_apply, abs_neg] at hbhi
  let k := max klo khi
  refine ⟨Mlo + Mhi, k, add_nonneg hMlo hMhi, fun n => ?_⟩
  have hb : 1 ≤ 1 + |L n| := by linarith [abs_nonneg (L n)]
  have hc (M : ℝ) (hM : 0 ≤ M) (l : ℕ) (hl : l ≤ k) :
      M * (1 + |L n|) ^ l ≤ M * (1 + |L n|) ^ k :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hl) hM
  change ‖orderedLaurentExpansion p R lo n - orderedLaurentExpansion p R hi n‖ ≤ _
  calc
    _ ≤ ‖orderedLaurentExpansion p R lo n‖ + ‖orderedLaurentExpansion p R hi n‖ :=
      norm_sub_le _ _
    _ ≤ Mlo * (1 + |L n|) ^ k + Mhi * (1 + |L n|) ^ k :=
      add_le_add ((hblo n).trans (hc Mlo hMlo klo (le_max_left _ _)))
        ((hbhi n).trans (hc Mhi hMhi khi (le_max_right _ _)))
    _ = _ := by rw [add_mul]

open scoped FourierTransform in
/-- The exact spectral record of each real-rooted Laurent quotient in a
literal numerator window is a genuine weighted atomic Fourier transform.
Its tempered inverse satisfies the finite exponential equation. -/
theorem exists_tempered_inverse_with_realRooted_orderedLaurentJump
    [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s) :
    let u := orderedLaurentJump p R lo hi
    ∃ k : ℕ, ∃ B : LocallyFiniteCarrier, B.carrier = L '' Function.support u ∧
      ∃ T : TemperedDistribution ℝ ℂ,
        𝓕 T ∈ stronglyTemperedAtomicAtExponent B k ∧
        (∀ n, originalFourierArray L B T n = u n) ∧
        (∀ n, cutArrayNumerator L p.coeff s (originalFourierArray L B T) n = R.coeff n) ∧
        finiteExponentialMultiplication (fun m : p.coeff.support => L m) (fun m => p.coeff m) T = 0 := by
  obtain ⟨M, k, hM, h⟩ := orderedLaurentJump_polynomialGrowth_of_realRooted L hL p R
    lo hi hlo hhi hmin hmax hroot
  exact ⟨k + (p.coeff.support.card + 2),
    exists_tempered_inverse_with_orderedLaurentJump L hL p R
      lo hi hlo hhi hmin hmax s hR M k hM h⟩

end

end MeyerGeneralProblem
