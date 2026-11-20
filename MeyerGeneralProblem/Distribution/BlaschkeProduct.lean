module

public import MeyerGeneralProblem.Distribution.BlaschkeBoundaryPhase
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

@[expose] public section

/-!
# Convergence of the upper-half-plane Blaschke product

Normalize each factor at zero on the real boundary. The normalized
factor differs from one by a summable quantity on each compact set.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter Set
open scoped Topology

/-- The Blaschke factor divided by its value at the real observation point zero. -/
def upperHalfPlaneNormalizedBlaschkeFactor (w z : ℂ) : ℂ :=
  upperHalfPlaneBlaschkeFactor w z / upperHalfPlaneBlaschkeFactor w 0

/-- The product of the normalized factors, including its real boundary values. -/
def upperHalfPlaneBlaschkeProduct {ι : Type*} (w : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, upperHalfPlaneNormalizedBlaschkeFactor (w i) z

private theorem sub_conj_ne_zero_of_im_nonneg {w z : ℂ} (hw : 0 < w.im) (hz : 0 ≤ z.im) :
    z - conj w ≠ 0 := by
  intro h
  have he := congrArg Complex.im (sub_eq_zero.mp h)
  rw [Complex.conj_im] at he
  linarith only [hz, hw, he]

private theorem upperHalfPlaneBlaschkeFactor_zero {w : ℂ} :
    upperHalfPlaneBlaschkeFactor w 0 = w / conj w := by
  simp [upperHalfPlaneBlaschkeFactor]

private theorem ne_zero_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  intro h
  exact hw.ne' (by simp [h])

private theorem upperHalfPlaneBlaschkeFactor_zero_ne_zero {w : ℂ} (hw : 0 < w.im) :
    upperHalfPlaneBlaschkeFactor w 0 ≠ 0 := by
  rw [upperHalfPlaneBlaschkeFactor_zero]
  exact div_ne_zero (ne_zero_of_im_pos hw) (by simpa using ne_zero_of_im_pos hw)

private theorem normalizedBlaschkeFactor_eq_zero_iff {w z : ℂ} (hw : 0 < w.im) (hz : 0 ≤ z.im) :
    upperHalfPlaneNormalizedBlaschkeFactor w z = 0 ↔ z = w := by
  by_cases he : z = w
  · simp [he, upperHalfPlaneNormalizedBlaschkeFactor, upperHalfPlaneBlaschkeFactor]
  have hne := div_ne_zero (div_ne_zero (sub_ne_zero.mpr he) (sub_conj_ne_zero_of_im_nonneg hw hz))
    (upperHalfPlaneBlaschkeFactor_zero_ne_zero hw)
  simp only [he, iff_false]
  exact hne

private theorem one_add_sub_one_complex (z : ℂ) : 1 + (z - 1) = z := by ring

private theorem conj_sub_eq_im (w : ℂ) :
    conj w - w = ((-2 * w.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.mul_re]
  · simp [Complex.sub_im, Complex.mul_im]
    ring

private theorem norm_normalizedBlaschkeFactor_sub_one {w z : ℂ} (hw : 0 < w.im)
    (hz : z ≠ conj w) :
    ‖upperHalfPlaneNormalizedBlaschkeFactor w z - 1‖ =
      (2 * ‖z‖ * w.im) / (‖w‖ * ‖z - conj w‖) := by
  have hw₀ : w ≠ 0 := ne_zero_of_im_pos hw
  have hw₁ : conj w ≠ 0 := by simpa using hw₀
  have he : upperHalfPlaneNormalizedBlaschkeFactor w z - 1 =
      (z * (conj w - w)) / (w * (z - conj w)) := by
    rw [upperHalfPlaneNormalizedBlaschkeFactor, upperHalfPlaneBlaschkeFactor_zero,
      upperHalfPlaneBlaschkeFactor]
    field_simp [hw₀, hw₁, sub_ne_zero.mpr hz]
    ring
  rw [he, conj_sub_eq_im, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hw] : -2 * w.im ≤ 0)]
  ring

/-- On a bounded complex disk the normalized factors of distant zeros
are uniformly close to one at the rate of their Blaschke weights. -/
theorem norm_upperHalfPlaneNormalizedBlaschkeFactor_sub_one_le_of_far {w z : ℂ}
    (hw : 0 < w.im) {R : ℝ} (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) (hFar : 2 * R + 1 ≤ ‖w‖) :
    ‖upperHalfPlaneNormalizedBlaschkeFactor w z - 1‖ ≤
      (8 * R) * upperHalfPlaneBlaschkeWeight w := by
  have hwNorm : 1 ≤ ‖w‖ := by linarith only [hR, hFar]
  have hLower : ‖w‖ - ‖z‖ ≤ ‖z - conj w‖ := by
    simpa only [Complex.norm_conj, norm_sub_rev] using norm_sub_norm_le (conj w) z
  have hDist : ‖w‖ ≤ 2 * ‖z - conj w‖ := by linarith only [hFar, hz, hLower]
  have hDist₀ : 0 < ‖z - conj w‖ := by linarith only [hwNorm, hDist]
  rw [norm_normalizedBlaschkeFactor_sub_one hw
    (sub_ne_zero.mp (norm_pos_iff.mp hDist₀)), upperHalfPlaneBlaschkeWeight, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (zero_lt_one.trans_le hwNorm) hDist₀) (by positivity)).2
  have hSq : 1 ≤ ‖w‖ ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hwNorm 2
  have hDen : 1 + ‖w‖ ^ 2 ≤ 4 * (‖w‖ * ‖z - conj w‖) := by
    nlinarith only [hSq, mul_le_mul_of_nonneg_left hDist (norm_nonneg w)]
  calc
    _ ≤ (2 * R * w.im) * (1 + ‖w‖ ^ 2) := by gcongr
    _ ≤ _ := by
      have hd := mul_le_mul_of_nonneg_left hDen (show 0 ≤ 2 * R * w.im by positivity)
      nlinarith only [hd]

private theorem differentiableOn_normalizedBlaschkeFactor_of_avoids_pole {w : ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, z ≠ conj w) :
    DifferentiableOn ℂ (upperHalfPlaneNormalizedBlaschkeFactor w) S := by
  have h : DifferentiableOn ℂ (fun z : ℂ => (z - w) / (z - conj w)) S :=
    ((differentiable_id.sub_const _).differentiableOn).div
      ((differentiable_id.sub_const _).differentiableOn)
      (fun z hz => sub_ne_zero.mpr (hS z hz))
  exact h.div_const _

/-- A single normalized factor is holomorphic in a neighborhood of each point
of the closed upper half-plane. -/
theorem differentiableOn_upperHalfPlaneNormalizedBlaschkeFactor {w : ℂ}
    (hw : 0 < w.im) :
    DifferentiableOn ℂ (upperHalfPlaneNormalizedBlaschkeFactor w) {z : ℂ | 0 ≤ z.im} :=
  differentiableOn_normalizedBlaschkeFactor_of_avoids_pole (fun _ hz =>
    sub_ne_zero.mp (sub_conj_ne_zero_of_im_nonneg hw hz))

private theorem differentiableOn_finset_normalizedBlaschkeFactor_prod_of_avoids_poles
    {ι : Type*} {w : ι → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, ∀ i, z ≠ conj (w i)) (s : Finset ι) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z) S := by
  have he : (∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i)) =
      (fun z => ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z) := by
    funext z
    rw [Finset.prod_apply]
  rw [← he]
  exact DifferentiableOn.finsetProd (u := s) (fun i _ =>
    differentiableOn_normalizedBlaschkeFactor_of_avoids_pole (fun z hz => hS z hz i))

/-- Any finite product of normalized factors is differentiable on the closed
upper half-plane. -/
theorem differentiableOn_finset_normalizedBlaschkeFactor_prod {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (s : Finset ι) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z)
      {z : ℂ | 0 ≤ z.im} :=
  differentiableOn_finset_normalizedBlaschkeFactor_prod_of_avoids_poles
    (fun _ hz i => sub_ne_zero.mp (sub_conj_ne_zero_of_im_nonneg (hw i) hz)) s

private theorem hasProdUniformlyOn_upperHalfPlaneBlaschkeProduct_of_avoids_poles
    {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {K : Set ℂ} (hK : IsCompact K) (hAvoid : ∀ z ∈ K, ∀ i, z ≠ conj (w i)) :
    HasProdUniformlyOn (fun i => upperHalfPlaneNormalizedBlaschkeFactor (w i))
      (upperHalfPlaneBlaschkeProduct w) K := by
  obtain ⟨z₀, _, hMax⟩ := (hK.insert (0 : ℂ)).exists_isMaxOn
    ⟨0, mem_insert 0 K⟩ continuous_norm.continuousOn
  let R := ‖z₀‖
  let F (i : ι) (z : ℂ) := upperHalfPlaneNormalizedBlaschkeFactor (w i) z - 1
  have hBd : ∀ᶠ i in cofinite, ∀ z ∈ K, ‖F i z‖ ≤ (8 * R) * upperHalfPlaneBlaschkeWeight (w i) := by
    filter_upwards [(hFin (2 * R + 1)).compl_mem_cofinite] with i hi z hz
    have hR : ‖z‖ ≤ R := hMax (mem_insert_of_mem 0 hz)
    exact norm_upperHalfPlaneNormalizedBlaschkeFactor_sub_one_le_of_far (hw i) (norm_nonneg z₀) hR
      (le_of_not_ge (show ¬ ‖w i‖ ≤ 2 * R + 1 from hi))
  have hCont (i : ι) : ContinuousOn (F i) K :=
    (differentiableOn_normalizedBlaschkeFactor_of_avoids_pole
      (fun z hz => hAvoid z hz i)).continuousOn.sub continuousOn_const
  let ringStructure : NormedCommRing ℂ := @NormedField.toNormedCommRing ℂ Complex.instNormedField
  have hP := @Summable.hasProdUniformlyOn_one_add ℂ ι K _ ℂ ringStructure
    inferInstance inferInstance inferInstance F hK (hWeight.mul_left (8 * R)) hBd hCont
  simp only [F, one_add_sub_one_complex] at hP
  have hMonoid : ringStructure.toCommRing.toCommMonoid = Complex.commRing.toCommMonoid := rfl
  rw [hMonoid] at hP
  exact hP

/-- The normalized factors converge uniformly on every compact set in
the closed upper half-plane. -/
theorem hasProdUniformlyOn_upperHalfPlaneBlaschkeProduct {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {K : Set ℂ} (hK : IsCompact K) (hUpper : K ⊆ {z : ℂ | 0 ≤ z.im}) :
    HasProdUniformlyOn (fun i => upperHalfPlaneNormalizedBlaschkeFactor (w i))
      (upperHalfPlaneBlaschkeProduct w) K :=
  hasProdUniformlyOn_upperHalfPlaneBlaschkeProduct_of_avoids_poles hw hFin hWeight hK
    (fun _ hz i => sub_ne_zero.mp (sub_conj_ne_zero_of_im_nonneg (hw i) (hUpper hz)))

private theorem isOpen_avoids_blaschke_poles {ι : Type*} {w : ι → ℂ}
    (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) : IsOpen {z | ∀ i, z ≠ conj (w i)} := by
  have hLocal : LocallyFinite (fun i => {conj (w i)}) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, (hFin (‖z‖ + 1)).subset ?_⟩
    rintro i ⟨y, hy, hball⟩
    have hy' : y = conj (w i) := mem_singleton_iff.mp hy
    have hdist : ‖y - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hball
    change ‖w i‖ ≤ ‖z‖ + 1
    rw [← Complex.norm_conj, ← hy']
    linarith only [norm_le_norm_sub_add y z, hdist]
  have hClosed := hLocal.isClosed_iUnion fun _ => isClosed_singleton
  convert hClosed.isOpen_compl using 1
  ext z
  simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_singleton_iff, not_exists]

/-- The product is holomorphic off the reflected zeros. Its real
boundary values therefore extend across every point of the real axis. -/
theorem analyticAt_upperHalfPlaneBlaschkeProduct_of_avoids_poles {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {z : ℂ} (hz : ∀ i, z ≠ conj (w i)) :
    AnalyticAt ℂ (upperHalfPlaneBlaschkeProduct w) z := by
  let U : Set ℂ := {u | ∀ i, u ≠ conj (w i)}
  have hOpen : IsOpen U := isOpen_avoids_blaschke_poles hFin
  have hProd : HasProdLocallyUniformlyOn (fun i => upperHalfPlaneNormalizedBlaschkeFactor (w i))
      (upperHalfPlaneBlaschkeProduct w) U := by
    apply hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
    intro u hu
    obtain ⟨ε, hε, hU⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hu)
    have hK : Metric.closedBall u (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hU
    refine ⟨Metric.closedBall u (ε / 2),
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds u (half_pos hε)), ?_⟩
    exact hasProdUniformlyOn_upperHalfPlaneBlaschkeProduct_of_avoids_poles hw hFin hWeight
      (isCompact_closedBall _ _) (fun _ hx => hK hx)
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hProd
  have hDiff : DifferentiableOn ℂ (upperHalfPlaneBlaschkeProduct w) U :=
    hProd.differentiableOn (Eventually.of_forall fun s =>
      differentiableOn_finset_normalizedBlaschkeFactor_prod_of_avoids_poles
        (fun _ hu => hu) s) hOpen
  exact hDiff.analyticOnNhd hOpen z hz

/-- The normalized product is locally uniform up to the real boundary. -/
theorem hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) :
    HasProdLocallyUniformlyOn (fun i => upperHalfPlaneNormalizedBlaschkeFactor (w i))
      (upperHalfPlaneBlaschkeProduct w) {z : ℂ | 0 ≤ z.im} := by
  let H : Set ℂ := {z : ℂ | 0 ≤ z.im}
  have hClosed : IsClosed H := isClosed_le continuous_const Complex.continuous_im
  apply hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z _
  refine ⟨Metric.closedBall z 1 ∩ H, ?_,
    hasProdUniformlyOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight
      ((isCompact_closedBall _ _).inter_right hClosed) inter_subset_right⟩
  exact inter_mem (nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ zero_lt_one)) self_mem_nhdsWithin

/-- The boundary values vary continuously from within the closed upper half-plane. -/
theorem continuousOn_upperHalfPlaneBlaschkeProduct {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) :
    ContinuousOn (upperHalfPlaneBlaschkeProduct w) {z : ℂ | 0 ≤ z.im} := by
  have hProd := hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hProd
  exact hProd.continuousOn (Eventually.of_forall fun s =>
    (differentiableOn_finset_normalizedBlaschkeFactor_prod hw s).continuousOn).frequently

/-- The normalized product is holomorphic in the open upper half-plane. -/
theorem differentiableOn_upperHalfPlaneBlaschkeProduct {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) :
    DifferentiableOn ℂ (upperHalfPlaneBlaschkeProduct w) {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hSub : U ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz => (show 0 < z.im from hz).le
  have hProd := (hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight).mono hSub
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hProd
  exact hProd.differentiableOn (Eventually.of_forall fun s =>
    (differentiableOn_finset_normalizedBlaschkeFactor_prod hw s).mono hSub) hU

/-- The product vanishes exactly at the listed zeros on the closed
upper half-plane. Absolute convergence of the deviations prevents
extra zeros of the infinite product. -/
theorem upperHalfPlaneBlaschkeProduct_eq_zero_iff {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {z : ℂ} (hz : 0 ≤ z.im) :
    upperHalfPlaneBlaschkeProduct w z = 0 ↔ ∃ i, z = w i := by
  by_cases h : ∃ i, z = w i
  · obtain ⟨i, hi⟩ := h
    exact iff_of_true (tprod_of_exists_eq_zero ⟨i, (normalizedBlaschkeFactor_eq_zero_iff (hw i) hz).2 hi⟩)
      ⟨i, hi⟩
  have hSum : Summable (fun i => ‖upperHalfPlaneNormalizedBlaschkeFactor (w i) z - 1‖) := by
    apply (hWeight.mul_left (8 * ‖z‖)).of_norm_bounded_eventually
    filter_upwards [(hFin (2 * ‖z‖ + 1)).compl_mem_cofinite] with i hi
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_upperHalfPlaneNormalizedBlaschkeFactor_sub_one_le_of_far (hw i) (norm_nonneg z) le_rfl
      (le_of_not_ge (show ¬ ‖w i‖ ≤ 2 * ‖z‖ + 1 from hi))
  have hNe (i : ι) : 1 + (upperHalfPlaneNormalizedBlaschkeFactor (w i) z - 1) ≠ 0 := by
    rw [one_add_sub_one_complex]
    exact fun he => h ⟨i, (normalizedBlaschkeFactor_eq_zero_iff (hw i) hz).1 he⟩
  exact iff_of_false (by simpa only [one_add_sub_one_complex, upperHalfPlaneBlaschkeProduct] using
    tprod_one_add_ne_zero_of_summable hNe hSum) h

/-- Split the product into the factors indexed by a finite set and its complement. -/
theorem upperHalfPlaneBlaschkeProduct_split {ι : Type*} {w : ι → ℂ}
    (s : Finset ι) {ζ : ℂ}
    (hTail : HasProd (fun i : {i // i ∉ s} => upperHalfPlaneNormalizedBlaschkeFactor (w i.1) ζ)
      (upperHalfPlaneBlaschkeProduct (fun i : {i // i ∉ s} => w i.1) ζ)) :
    upperHalfPlaneBlaschkeProduct w ζ =
      (∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) ζ) *
        upperHalfPlaneBlaschkeProduct (fun i : {i // i ∉ s} => w i.1) ζ := by
  let f (i : ι) := upperHalfPlaneNormalizedBlaschkeFactor (w i) ζ
  exact ((s.hasProd f).mul_compl hTail).tprod_eq

private theorem normalizedBlaschkeFactor_eq_sub_mul (z ζ : ℂ) :
    upperHalfPlaneNormalizedBlaschkeFactor z ζ =
      (ζ - z) * ((ζ - conj z)⁻¹ / upperHalfPlaneBlaschkeFactor z 0) := by
  unfold upperHalfPlaneNormalizedBlaschkeFactor
  rw [show upperHalfPlaneBlaschkeFactor z ζ = (ζ - z) / (ζ - conj z) from rfl]
  simp only [div_eq_mul_inv, mul_assoc]

/-- The analytic order of the product counts the indices for that zero,
so a repeated zero gives the prescribed multiplicity. -/
theorem analyticOrderAt_upperHalfPlaneBlaschkeProduct {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {z : ℂ} (hz : 0 < z.im) :
    analyticOrderAt (upperHalfPlaneBlaschkeProduct w) z = ({i | w i = z}.ncard : ℕ∞) := by
  let I : Set ι := {i | w i = z}
  have hI : I.Finite := (hFin ‖z‖).subset fun i hi => by
    change w i = z at hi
    change ‖w i‖ ≤ ‖z‖
    rw [hi]
  let s := hI.toFinset
  let v (i : {i // i ∉ s}) := w i
  let G (ζ : ℂ) := (ζ - conj z)⁻¹ / upperHalfPlaneBlaschkeFactor z 0
  have hV (R : ℝ) : {i | ‖v i‖ ≤ R}.Finite :=
    (hFin R).preimage (Subtype.val_injective.injOn)
  have hW : Summable (fun i => upperHalfPlaneBlaschkeWeight (v i)) :=
    hWeight.subtype (fun i => i ∉ s)
  have hU : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hA : AnalyticAt ℂ (upperHalfPlaneBlaschkeProduct w) z :=
    (differentiableOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight).analyticOnNhd hU z hz
  have hB : AnalyticAt ℂ (upperHalfPlaneBlaschkeProduct v) z :=
    (differentiableOn_upperHalfPlaneBlaschkeProduct (w := v)
      (fun i => hw i.1) hV hW).analyticOnNhd hU z hz
  have hB₀ : upperHalfPlaneBlaschkeProduct v z ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ :=
      (upperHalfPlaneBlaschkeProduct_eq_zero_iff (w := v) (fun i => hw i.1) hV hW hz.le).1 he
    exact i.property (hI.mem_toFinset.mpr hi.symm)
  have hDen := sub_conj_ne_zero_of_im_nonneg hz hz.le
  have hConst := upperHalfPlaneBlaschkeFactor_zero_ne_zero hz
  have hG : AnalyticAt ℂ G z :=
    (((analyticAt_id.sub analyticAt_const).inv hDen).div analyticAt_const hConst)
  have hG₀ : G z ≠ 0 := div_ne_zero (inv_ne_zero hDen) hConst
  rw [Set.ncard_eq_toFinset_card I hI]
  apply (hA.analyticOrderAt_eq_natCast (n := s.card)).2
  refine ⟨fun ζ => G ζ ^ s.card * upperHalfPlaneBlaschkeProduct v ζ,
    (hG.pow _).mul hB, mul_ne_zero (pow_ne_zero _ hG₀) hB₀, ?_⟩
  filter_upwards [hU.mem_nhds hz] with ζ hζ
  have hTail := (hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct (w := v)
    (fun i => hw i.1) hV hW).hasProd (show 0 ≤ ζ.im from (show 0 < ζ.im from hζ).le)
  have hSplit := upperHalfPlaneBlaschkeProduct_split s hTail
  have hF : ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) ζ =
      ((ζ - z) * G ζ) ^ s.card := by
    calc
      _ = ∏ _i ∈ s, ((ζ - z) * G ζ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have he : w i = z := hI.mem_toFinset.mp hi
        rw [he, normalizedBlaschkeFactor_eq_sub_mul]
      _ = _ := Finset.prod_const _
  rw [hSplit, hF, mul_pow, smul_eq_mul, mul_assoc]

private theorem norm_upperHalfPlaneNormalizedBlaschkeFactor_le_one {w z : ℂ}
    (hw : 0 < w.im) (hz : 0 ≤ z.im) :
    ‖upperHalfPlaneNormalizedBlaschkeFactor w z‖ ≤ 1 := by
  have hNorm₀ : ‖upperHalfPlaneBlaschkeFactor w 0‖ = 1 := by
    rw [upperHalfPlaneBlaschkeFactor_zero, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr (ne_zero_of_im_pos hw))]
  rw [upperHalfPlaneNormalizedBlaschkeFactor, norm_div, hNorm₀, div_one, upperHalfPlaneBlaschkeFactor,
    norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_conj_ne_zero_of_im_nonneg hw hz)), one_mul]
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith only [mul_nonneg hz hw.le]

/-- The normalized Blaschke product is bounded by one in modulus
throughout the closed upper half-plane. -/
theorem norm_upperHalfPlaneBlaschkeProduct_le_one {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖upperHalfPlaneBlaschkeProduct w z‖ ≤ 1 := by
  have hProd : Tendsto (fun s : Finset ι => ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z)
      atTop (𝓝 (upperHalfPlaneBlaschkeProduct w z)) :=
    (hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight).hasProd
      (show z ∈ {z : ℂ | 0 ≤ z.im} from hz)
  refine le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hProd) (Eventually.of_forall fun s => ?_)
  change ‖∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z‖ ≤ 1
  rw [Complex.norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ =>
    norm_upperHalfPlaneNormalizedBlaschkeFactor_le_one (hw i) hz)

/-- The actual real boundary of the holomorphic product has the
continuous, nondecreasing argument constructed from its factors. -/
theorem upperHalfPlaneBlaschkeProduct_real {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i))) (x : ℝ) :
    upperHalfPlaneBlaschkeProduct w (x : ℂ) =
      Complex.exp ((upperHalfPlaneBlaschkePhaseSum w x : ℂ) * Complex.I) :=
  (hasProd_upperHalfPlaneBlaschkeFactor_real hw hFin hWeight x).tprod_eq

end
end MeyerGeneralProblem
