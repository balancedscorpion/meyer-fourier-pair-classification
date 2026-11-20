module

public import MeyerGeneralProblem.Distribution.BlaschkeJensen
public import MeyerGeneralProblem.Distribution.BlaschkeProduct
public import MeyerGeneralProblem.Distribution.HeatLogarithmicTail
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.HasPrimitives

@[expose] public section

/-!
# Transfer of the Blaschke condition to the upper half-plane

The scaled Cayley map transfers disk zero weights and preserves
analytic order. It applies to the positive-time Fourier–Laplace
transform with its checked radial half-moment bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set MeromorphicOn
open scoped FourierTransform Topology

/-- The inverse of the Cayley chart of height `y` on the upper half-plane. -/
def scaledUpperHalfPlaneToDisk (y : ℝ) (z : ℂ) : ℂ :=
  (z - (y : ℂ) * Complex.I) / (z + (y : ℂ) * Complex.I)

private theorem add_scaled_I_ne_zero {z : ℂ} {y : ℝ} (hz : 0 < z.im) (hy : 0 < y) :
    z + (y : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, Complex.zero_im] at hi
  linarith only [hz, hy, hi]

private theorem one_sub_norm_sq_scaledUpperHalfPlaneToDisk {z : ℂ} {y : ℝ}
    (hz : 0 < z.im) (hy : 0 < y) :
    1 - ‖scaledUpperHalfPlaneToDisk y z‖ ^ 2 =
      (4 * y * z.im) / ‖z + (y : ℂ) * Complex.I‖ ^ 2 := by
  rw [scaledUpperHalfPlaneToDisk, norm_div, div_pow]
  have hN : ‖z + (y : ℂ) * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (add_scaled_I_ne_zero hz hy)
  field_simp [hN]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  ring

/-- The scaled inverse chart takes the open upper half-plane into the disk. -/
theorem norm_scaledUpperHalfPlaneToDisk_lt_one {z : ℂ} {y : ℝ} (hz : 0 < z.im) (hy : 0 < y) :
    ‖scaledUpperHalfPlaneToDisk y z‖ < 1 := by
  have hDen := norm_pos_iff.mpr (add_scaled_I_ne_zero hz hy)
  have hP : 0 < 1 - ‖scaledUpperHalfPlaneToDisk y z‖ ^ 2 := by
    rw [one_sub_norm_sq_scaledUpperHalfPlaneToDisk hz hy]
    positivity
  nlinarith only [hP, norm_nonneg (scaledUpperHalfPlaneToDisk y z)]

/-- The inverse chart recovers each point of the actual upper half-plane. -/
theorem scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk {z : ℂ} {y : ℝ}
    (hz : 0 < z.im) (hy : 0 < y) :
    (y : ℂ) * cayleyToUpperHalfPlane (scaledUpperHalfPlaneToDisk y z) = z := by
  have hDen := add_scaled_I_ne_zero hz hy
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hPlus : 1 + scaledUpperHalfPlaneToDisk y z =
      (2 * z) / (z + (y : ℂ) * Complex.I) := by
    rw [scaledUpperHalfPlaneToDisk]
    field_simp [hDen]
    ring
  have hMinus : 1 - scaledUpperHalfPlaneToDisk y z =
      (2 * (y : ℂ) * Complex.I) / (z + (y : ℂ) * Complex.I) := by
    rw [scaledUpperHalfPlaneToDisk]
    field_simp [hDen]
    ring
  rw [cayleyToUpperHalfPlane, hPlus, hMinus]
  field_simp [hDen, hy', Complex.I_ne_zero]

/-- In the chart of height at least one the upper-half-plane Blaschke
weight is controlled by the disk weight multiplied by that height. -/
theorem upperHalfPlaneBlaschkeWeight_le_scaled_diskWeight {z : ℂ} {y : ℝ}
    (hz : 0 < z.im) (hy : 1 ≤ y) :
    upperHalfPlaneBlaschkeWeight z ≤ y * (1 - ‖scaledUpperHalfPlaneToDisk y z‖) := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hNorm : ‖z + (y : ℂ) * Complex.I‖ ≤ ‖z‖ + y := by
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hy₀.le]
      using norm_add_le z ((y : ℂ) * Complex.I)
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hySq : 1 ≤ y ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hy 2
  have hBound : ‖z + (y : ℂ) * Complex.I‖ ^ 2 ≤ 2 * (y ^ 2 * (1 + ‖z‖ ^ 2)) := by
    have hProd := mul_le_mul_of_nonneg_right hySq (sq_nonneg ‖z‖)
    nlinarith only [hSq, hProd, sq_nonneg (‖z‖ - y)]
  have hD := norm_pos_iff.mpr (add_scaled_I_ne_zero hz hy₀)
  have hCore : 2 * upperHalfPlaneBlaschkeWeight z ≤
      y * (1 - ‖scaledUpperHalfPlaneToDisk y z‖ ^ 2) := by
    rw [upperHalfPlaneBlaschkeWeight, one_sub_norm_sq_scaledUpperHalfPlaneToDisk hz hy₀]
    simp only [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hBound (show 0 ≤ z.im by exact hz.le)]
  have hQ : 1 - ‖scaledUpperHalfPlaneToDisk y z‖ ^ 2 ≤
      2 * (1 - ‖scaledUpperHalfPlaneToDisk y z‖) := by
    nlinarith only [sq_nonneg (1 - ‖scaledUpperHalfPlaneToDisk y z‖)]
  linarith only [hCore, mul_le_mul_of_nonneg_left hQ hy₀.le]

private theorem hasDerivAt_scaled_cayleyToUpperHalfPlane (y : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun q : ℂ => (y : ℂ) * cayleyToUpperHalfPlane q)
      ((y : ℂ) * (2 * Complex.I / (1 - w) ^ 2)) w := by
  have hDen : 1 - w ≠ 0 := by
    intro h
    have he : w = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hw
  have h₁ : HasDerivAt (fun q : ℂ => Complex.I * (1 + q)) Complex.I w := by
    have h := ((hasDerivAt_id w).const_add (1 : ℂ)).const_mul Complex.I
    rw [mul_one] at h
    exact h
  have h₂ : HasDerivAt (fun q : ℂ => 1 - q) (-1) w := (hasDerivAt_id w).const_sub 1
  have h := (h₁.div h₂ hDen).const_mul (y : ℂ)
  have hEq : (y : ℂ) * ((Complex.I * (1 - w) - Complex.I * (1 + w) * (-1)) / (1 - w) ^ 2) =
      (y : ℂ) * (2 * Complex.I / (1 - w) ^ 2) := by ring
  rw [← hEq]
  exact h

private theorem analyticOrderNatAt_comp_scaled_cayley {H : ℂ → ℂ} {z : ℂ} {y : ℝ}
    (hy : 0 < y) (hz : 0 < z.im) :
    analyticOrderNatAt (H ∘ fun w : ℂ => (y : ℂ) * cayleyToUpperHalfPlane w)
      (scaledUpperHalfPlaneToDisk y z) = analyticOrderNatAt H z := by
  let w := scaledUpperHalfPlaneToDisk y z
  let g (q : ℂ) := (y : ℂ) * cayleyToUpperHalfPlane q
  have hw : ‖w‖ < 1 := norm_scaledUpperHalfPlaneToDisk_lt_one hz hy
  have hDen : 1 - w ≠ 0 := by
    intro h
    have he : w = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hw
  have hG : DifferentiableOn ℂ g (ball 0 1) :=
    differentiableOn_cayleyToUpperHalfPlane.const_mul _
  have hA : AnalyticAt ℂ g w := hG.analyticOnNhd isOpen_ball w (by simpa only [mem_ball_zero_iff] using hw)
  have hd : deriv g w ≠ 0 := by
    rw [(hasDerivAt_scaled_cayleyToUpperHalfPlane y hw).deriv]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') (div_ne_zero
      (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero _ hDen))
  change analyticOrderNatAt (H ∘ g) w = analyticOrderNatAt H z
  rw [analyticOrderNatAt, analyticOrderAt_comp_of_deriv_ne_zero hA hd,
    show g w = z from scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk hz hy]
  rfl

/-- A radial half-moment bound in a Cayley chart gives the upper-half-plane
Blaschke condition with every analytic multiplicity. -/
theorem summable_upperHalfPlane_weightedZeroOrder_of_halfMoment {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {y : ℝ} (hy : 1 ≤ y) (hCenter : H ((y : ℂ) * Complex.I) ≠ 0)
    {M : ℝ} (hHalf : ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun w => Real.sqrt ‖H ((y : ℂ) * cayleyToUpperHalfPlane w)‖) 0 r ≤ M) :
    Summable (fun z : {z : ℂ // 0 < z.im} =>
      (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1) := by
  let F := H ∘ fun w : ℂ => (y : ℂ) * cayleyToUpperHalfPlane w
  let q (z : {z : ℂ // 0 < z.im}) := scaledUpperHalfPlaneToDisk y z.1
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hF : DifferentiableOn ℂ F (ball 0 1) :=
    hH.comp_differentiableOn (differentiableOn_cayleyToUpperHalfPlane.const_mul _)
  have hF₀ : F 0 ≠ 0 := by simpa [F, cayleyToUpperHalfPlane] using hCenter
  have hQ : Function.Injective q := by
    intro z w hzw
    apply Subtype.ext
    have hz := scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk z.2 hy₀
    have hw := scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk w.2 hy₀
    exact hz.symm.trans ((congrArg (fun u : ℂ => (y : ℂ) * cayleyToUpperHalfPlane u) hzw).trans hw)
  have hDisk := summable_diskBlaschkeZeroWeight_of_circleAverage_sqrt_norm_le hF hF₀ hHalf
  refine ((hDisk.comp_injective hQ).mul_left y).of_nonneg_of_le ?_ ?_
  · intro z
    have hPos := z.2
    unfold upperHalfPlaneBlaschkeWeight
    positivity
  · intro z
    have hNorm : ‖q z‖ < 1 := norm_scaledUpperHalfPlaneToDisk_lt_one z.2 hy₀
    have hOrder : analyticOrderNatAt F (q z) = analyticOrderNatAt H z.1 :=
      analyticOrderNatAt_comp_scaled_cayley hy₀ z.2
    change (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1 ≤
      y * diskBlaschkeZeroWeight F (q z)
    simp only [diskBlaschkeZeroWeight, ite_eq_left hNorm, hOrder]
    rw [mul_left_comm y]
    exact mul_le_mul_of_nonneg_left (upperHalfPlaneBlaschkeWeight_le_scaled_diskWeight z.2 hy) (Nat.cast_nonneg _)

/-- The actual edge-normalized heated transform satisfies the
upper-half-plane Blaschke condition for all sufficiently small
positive heat times. A single chart center serves these times. -/
theorem exists_height_eventually_summable_edgeNormalizedHeat_weightedZeroOrder
    {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) :
    ∃ y : ℝ, 1 < y ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      H ((y : ℂ) * Complex.I) ≠ 0 ∧
      Summable (fun z : {z : ℂ // 0 < z.im} =>
        (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1) := by
  obtain ⟨y, hy, _, hCenter⟩ :=
    exists_large_height_eventually_edgeNormalizedHeatFourierLaplace_norm_gt_exp
      hf hb hEdge (ε := 1) zero_lt_one 1
  refine ⟨y, hy, ?_⟩
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hCenter, hPos] with t htCenter ht
  have hNonzero : edgeNormalizedHeatFourierLaplace t f b ((y : ℂ) * Complex.I) ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans htCenter)
  exact ⟨hNonzero, summable_upperHalfPlane_weightedZeroOrder_of_halfMoment
    (differentiable_edgeNormalizedHeatFourierLaplace hf ht b) hy.le hNonzero
    (fun _ hr hr₁ => circleAverage_sqrt_norm_edgeNormalizedHeatFourierLaplace_mul_le
      hf ht b hy.le hr.le hr₁)⟩

/-- One index for every copy of each upper-half-plane zero. -/
def UpperHalfPlaneZeroIndex (H : ℂ → ℂ) :=
  Σ z : {z : ℂ // 0 < z.im}, Fin (analyticOrderNatAt H z.1)

/-- The complex zero attached to a multiplicity index. -/
def upperHalfPlaneZeroAtIndex (H : ℂ → ℂ) (i : UpperHalfPlaneZeroIndex H) : ℂ := i.1.1

private def upperHalfPlaneZeroFiberEquiv (H : ℂ → ℂ) (z : {z : ℂ // 0 < z.im}) :
    {i : UpperHalfPlaneZeroIndex H // upperHalfPlaneZeroAtIndex H i = z.1} ≃
      Fin (analyticOrderNatAt H z.1) where
  toFun i := Fin.cast (congrArg (analyticOrderNatAt H) i.property) i.val.2
  invFun i := ⟨⟨z, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨w, i⟩, hi⟩
    have he : w = z := Subtype.ext hi
    subst w
    rfl
  right_inv := by intro i; rfl

/-- Summability of the multiplicity-weighted zero weights is the
summability of the family with every zero repeated by its order. -/
theorem summable_upperHalfPlaneZeroAtIndex {H : ℂ → ℂ}
    (h : Summable (fun z : {z : ℂ // 0 < z.im} =>
      (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1)) :
    Summable (fun i : UpperHalfPlaneZeroIndex H =>
      upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) := by
  have hPos (i : UpperHalfPlaneZeroIndex H) : 0 ≤ upperHalfPlaneBlaschkeWeight
      (upperHalfPlaneZeroAtIndex H i) := by
    exact div_nonneg i.1.2.le (by positivity)
  refine (summable_sigma_of_nonneg hPos).2 ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [upperHalfPlaneZeroAtIndex, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

/-- The multiplicity indices of a nonzero entire function are finite
in every bounded complex disk. -/
theorem finite_upperHalfPlaneZeroAtIndex_norm_le {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hNonzero : ∃ z, H z ≠ 0) (R : ℝ) :
    {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite := by
  let Z := H ⁻¹' {(0 : ℂ)}
  have hA : AnalyticOnNhd ℂ H univ := hH.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₀, hz₀⟩ := hNonzero
  have hCod : Zᶜ ∈ codiscrete ℂ := by
    dsimp only [Z]
    rw [← preimage_compl]
    exact hA.preimage_zero_mem_codiscrete hz₀
  obtain ⟨hClosed, hDisc⟩ := compl_mem_codiscrete_iff.mp hCod
  have hBase : (closedBall (0 : ℂ) R ∩ Z).Finite :=
    ((isCompact_closedBall _ _).inter_right hClosed).finite (hDisc.mono inter_subset_right)
  have hFib (z : ℂ) (_ : z ∈ closedBall (0 : ℂ) R ∩ Z) :
      (upperHalfPlaneZeroAtIndex H ⁻¹' {z}).Finite := by
    by_cases hz : 0 < z.im
    · let e := upperHalfPlaneZeroFiberEquiv H ⟨z, hz⟩
      exact Finite.of_injective e e.injective
    · have hEmpty : upperHalfPlaneZeroAtIndex H ⁻¹' {z} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        have he : upperHalfPlaneZeroAtIndex H i = z := hi
        exact hz (he ▸ i.1.2)
      rw [hEmpty]
      exact finite_empty
  refine (hBase.preimage' hFib).subset fun i hi => ⟨?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hi
  · change H (upperHalfPlaneZeroAtIndex H i) = 0
    have hOrd : 0 < analyticOrderNatAt H (upperHalfPlaneZeroAtIndex H i) :=
      (Nat.zero_le i.2.val).trans_lt i.2.isLt
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hOrd.ne'

private theorem analyticOrderAt_ne_top_of_entire_nonzero {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hNonzero : ∃ z, H z ≠ 0) (z : ℂ) :
    analyticOrderAt H z ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ H univ := hH.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨w, hw⟩ := hNonzero
  intro he
  have h : H = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (f := H) z (fun x => hA x (mem_univ x))).1 he
  exact hw (by simp [h])

/-- The normalized Blaschke product of the indexed zeros has the same
analytic order as the original entire function throughout the upper half-plane. -/
theorem analyticOrderAt_upperHalfPlaneBlaschkeProduct_of_entire {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hNonzero : ∃ z, H z ≠ 0)
    (hSum : Summable (fun z : {z : ℂ // 0 < z.im} =>
      (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1)) {z : ℂ} (hz : 0 < z.im) :
    analyticOrderAt (upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)) z =
      analyticOrderAt H z := by
  rw [analyticOrderAt_upperHalfPlaneBlaschkeProduct (fun i => i.1.2)
    (finite_upperHalfPlaneZeroAtIndex_norm_le hH hNonzero) (summable_upperHalfPlaneZeroAtIndex hSum) hz]
  have hCard : {i | upperHalfPlaneZeroAtIndex H i = z}.ncard = analyticOrderNatAt H z := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (upperHalfPlaneZeroFiberEquiv H ⟨z, hz⟩)).trans (by simp)
  rw [hCard, analyticOrderNatAt]
  exact ENat.natCast_toNat (analyticOrderAt_ne_top_of_entire_nonzero hH hNonzero z)

/-- Dividing by the actual Blaschke product leaves an analytic,
zero-free factor on the upper half-plane. The quotient is put into
meromorphic normal form to give its values at the cancelled zeros. -/
theorem exists_analytic_zeroFree_factor_upperHalfPlaneBlaschkeProduct {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hNonzero : ∃ z, H z ≠ 0)
    (hSum : Summable (fun z : {z : ℂ // 0 < z.im} =>
      (analyticOrderNatAt H z.1 : ℝ) * upperHalfPlaneBlaschkeWeight z.1)) :
    let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
    let U : Set ℂ := {z : ℂ | 0 < z.im}
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧ (∀ z ∈ U, G z ≠ 0) ∧
      EqOn H (fun z => B z * G z) U := by
  let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let Q : ℂ → ℂ := H / B
  let G := toMeromorphicNFOn Q U
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hA : AnalyticOnNhd ℂ H U := hH.differentiableOn.analyticOnNhd hOpen
  have hB : AnalyticOnNhd ℂ B U :=
    (differentiableOn_upperHalfPlaneBlaschkeProduct (fun i => i.1.2)
      (finite_upperHalfPlaneZeroAtIndex_norm_le hH hNonzero)
      (summable_upperHalfPlaneZeroAtIndex hSum)).analyticOnNhd hOpen
  have hQ : MeromorphicOn Q U := hA.meromorphicOn.div hB.meromorphicOn
  have hNF : MeromorphicNFOn G U := meromorphicNFOn_toMeromorphicNFOn Q U
  have hOrd (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt G z = 0 := by
    have hSame : analyticOrderAt B z = analyticOrderAt H z :=
      analyticOrderAt_upperHalfPlaneBlaschkeProduct_of_entire hH hNonzero hSum hz
    have hM : meromorphicOrderAt H z ≠ ⊤ := by
      rw [(hA z hz).meromorphicOrderAt_eq]
      exact fun he => analyticOrderAt_ne_top_of_entire_nonzero hH hNonzero z
        (ENat.map_eq_top_iff.mp he)
    have he : meromorphicOrderAt B z = meromorphicOrderAt H z := by
      rw [(hB z hz).meromorphicOrderAt_eq, (hA z hz).meromorphicOrderAt_eq, hSame]
    dsimp only [G, Q]
    rw [meromorphicOrderAt_toMeromorphicNFOn hQ hz,
      meromorphicOrderAt_div (hA z hz).meromorphicAt (hB z hz).meromorphicAt, he]
    cases hr : meromorphicOrderAt H z with
    | top => exact (hM hr).elim
    | coe a => simp
  refine ⟨G, fun z hz => (hNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 (hOrd z hz).symm.le,
    fun z hz => (hNF hz).meromorphicOrderAt_eq_zero_iff.1 (hOrd z hz), ?_⟩
  intro z hz
  change H z = B z * G z
  by_cases hzB : B z = 0
  · have hSame := analyticOrderAt_upperHalfPlaneBlaschkeProduct_of_entire hH hNonzero hSum hz
    have hNe : analyticOrderAt H z ≠ 0 := by
      rw [← hSame]
      exact (hB z hz).analyticOrderAt_ne_zero.mpr hzB
    rw [(hA z hz).analyticOrderAt_ne_zero.mp hNe, hzB, zero_mul]
  · have hQN : MeromorphicNFAt Q z := ((hA z hz).div (hB z hz) hzB).meromorphicNFAt
    have hEq : G z = Q z := by
      dsimp only [G]
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQ hz, toMeromorphicNFAt_eq_self.mpr hQN]
    rw [hEq]
    change H z = B z * (H z / B z)
    field_simp [hzB]

private theorem exists_differentiable_log_on_disk {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hNe : ∀ z ∈ ball (0 : ℂ) 1, F z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 1) ∧
      EqOn (Complex.exp ∘ L) F (ball 0 1) := by
  have hLog : DifferentiableOn ℂ (logDeriv F) (ball 0 1) :=
    (hF.deriv isOpen_ball).div hF hNe
  obtain ⟨P, hP⟩ := hLog.isExactOn_ball
  have hPd : DifferentiableOn ℂ P (ball 0 1) := fun z hz =>
    (hP z hz).differentiableAt.differentiableWithinAt
  let G := Complex.exp ∘ P
  have hG : DifferentiableOn ℂ G (ball 0 1) := Complex.differentiable_exp.comp_differentiableOn hPd
  have hG₀ (z : ℂ) (_ : z ∈ ball (0 : ℂ) 1) : G z ≠ 0 := Complex.exp_ne_zero _
  have hEq : EqOn (logDeriv F) (logDeriv G) (ball 0 1) := by
    intro z hz
    change logDeriv F z = logDeriv (Complex.exp ∘ P) z
    rw [logDeriv_comp Complex.differentiable_exp.differentiableAt (hP z hz).differentiableAt,
      Complex.logDeriv_exp, Pi.one_apply, one_mul, (hP z hz).deriv]
  obtain ⟨c, hc, hFG⟩ := (logDeriv_eqOn_iff hF hG isOpen_ball
    ((convex_ball (0 : ℂ) 1).isPreconnected) hG₀ hNe).mp hEq
  refine ⟨fun z => Complex.log c + P z, (differentiableOn_const (Complex.log c)).add hPd, ?_⟩
  intro z hz
  change Complex.exp (Complex.log c + P z) = F z
  rw [Complex.exp_add, Complex.exp_log hc]
  exact (hFG hz).symm

/-- A zero-free analytic function on the upper half-plane has a
holomorphic logarithm, obtained from a primitive on the disk. -/
theorem exists_analytic_log_upperHalfPlane {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.im})
    (hNe : ∀ z : ℂ, 0 < z.im → G z ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L {z : ℂ | 0 < z.im} ∧
      EqOn (Complex.exp ∘ L) G {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let q := scaledUpperHalfPlaneToDisk 1
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hCay : MapsTo cayleyToUpperHalfPlane (ball 0 1) U := fun _ hz =>
    im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hz)
  obtain ⟨L, hL, hEq⟩ := exists_differentiable_log_on_disk
    (hG.differentiableOn.comp differentiableOn_cayleyToUpperHalfPlane hCay) (fun z hz => hNe _ (hCay hz))
  have hq : DifferentiableOn ℂ q U := by
    unfold q scaledUpperHalfPlaneToDisk
    exact ((differentiable_id.sub_const _).differentiableOn).div
      ((differentiable_id.add_const _).differentiableOn) (fun _ hz => add_scaled_I_ne_zero hz zero_lt_one)
  have hMaps : MapsTo q U (ball 0 1) := fun _ hz =>
    mem_ball_zero_iff.mpr (norm_scaledUpperHalfPlaneToDisk_lt_one hz zero_lt_one)
  refine ⟨L ∘ q, (hL.comp hq hMaps).analyticOnNhd hOpen, ?_⟩
  intro z hz
  have he : cayleyToUpperHalfPlane (q z) = z := by
    simpa only [Complex.ofReal_one, one_mul] using
      scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk hz (zero_lt_one : (0 : ℝ) < 1)
  exact (hEq (hMaps hz)).trans (congrArg G he)

/-- At sufficiently small positive heat times the actual edge-normalized
transform factors into its Blaschke product and the exponential of
an analytic function. -/
theorem eventually_edgeNormalizedHeat_has_blaschke_exponential_factorization
    {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧
        EqOn H (fun z => B z * Complex.exp (L z)) U := by
  obtain ⟨y, _, h⟩ := exists_height_eventually_summable_edgeNormalizedHeat_weightedZeroOrder hf hb hEdge
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [h, hPos] with t ht htPos
  have hDiff := differentiable_edgeNormalizedHeatFourierLaplace hf htPos b
  have hNonzero : ∃ z, edgeNormalizedHeatFourierLaplace t f b z ≠ 0 :=
    ⟨(y : ℂ) * Complex.I, ht.1⟩
  obtain ⟨G, hG, hGNe, hFactor⟩ :=
    exists_analytic_zeroFree_factor_upperHalfPlaneBlaschkeProduct hDiff hNonzero ht.2
  obtain ⟨L, hL, hExp⟩ := exists_analytic_log_upperHalfPlane hG hGNe
  refine ⟨summable_upperHalfPlaneZeroAtIndex ht.2,
    finite_upperHalfPlaneZeroAtIndex_norm_le hDiff hNonzero, L, hL, ?_⟩
  intro z hz
  exact (hFactor hz).trans (congrArg _ (hExp hz).symm)

/-- The heated positive-frequency part of an actual Fourier-gap input
has the Blaschke factorization with its common Fourier-edge linear term. -/
theorem exists_eventually_heatFourierLaplace_blaschke_factorization_of_gap
    {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s)) :
    ∃ b : ℝ, s ≤ b ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn (heatFourierLaplace t f 0)
        (fun z => Complex.exp ((↑(2 * Real.pi * b) * Complex.I) * z) * B z * Complex.exp (L z)) U := by
  obtain ⟨b, hb, hZero, hNear, _⟩ :=
    exists_common_positiveFourier_lower_edge hf hfCont hf₀ hs hGap
  refine ⟨b, hb, ?_⟩
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hPos, eventually_edgeNormalizedHeat_has_blaschke_exponential_factorization
    hf (hs.trans hb) hNear] with t ht hFactor
  obtain ⟨hSum, hFin, L, hL, hLFactor⟩ := hFactor
  refine ⟨hSum, hFin, L, hL, ?_⟩
  intro z hz
  have hCut := heatFourierLaplace_eq_of_zero_Ioo hf ht (hs.trans hb) hZero
  let a : ℂ := (↑(2 * Real.pi * b) : ℂ) * Complex.I
  have he : Complex.exp (a * z) * edgeNormalizedHeatFourierLaplace t f b z =
      heatFourierLaplace t f b z := by
    change Complex.exp (a * z) * (Complex.exp (-a * z) * heatFourierLaplace t f b z) = _
    rw [← mul_assoc, ← Complex.exp_add, show a * z + -a * z = 0 by ring,
      Complex.exp_zero, one_mul]
  calc
    _ = Complex.exp (a * z) * edgeNormalizedHeatFourierLaplace t f b z :=
      (congrFun hCut z).trans he.symm
    _ = _ := (congrArg (fun v : ℂ => Complex.exp (a * z) * v) (hLFactor hz)).trans
      (mul_assoc _ _ _).symm

end
end MeyerGeneralProblem
