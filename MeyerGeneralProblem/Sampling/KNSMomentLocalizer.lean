module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic

@[expose] public section

/-!
# The actual order-dependent KNS box-convolution localizer

These are the compactly supported real kernels from Kulikov–Nazarov–Sodin,
arXiv:2306.14013v1, Section 5.2. The normalized short box has width u/n;
convolving n copies places its support in [-u/2,u/2]. No infinite smoothness
or regularity of a future function being localized is part of the construction.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Convolution
open scoped Pointwise

/-- The actual real indicator of a symmetric closed interval. -/
def knsBox (r : ℝ) : ℝ → ℝ := (Icc (-r) r).indicator (fun _ => 1)

/-- The unit-mass short box of width u/n, when n and u are positive. -/
def knsBeta (n : ℕ) (u : ℝ) : ℝ → ℝ := fun x => (n : ℝ)/u * knsBox (u/(2*n)) x

/-- Iterated actual convolution, with index j denoting j+1 copies. -/
def knsBoxConvolution (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | j+1 => g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBoxConvolution g j

/-- The actual n-fold convolution of the normalized short box (n positive). -/
def knsBSpline (n : ℕ) (u : ℝ) : ℝ → ℝ := knsBoxConvolution (knsBeta n u) (n-1)

/-- The KNS localizer: its normalized B-spline convolved with the long box. -/
def knsMomentLocalizer (n : ℕ) (u : ℝ) : ℝ → ℝ :=
  knsBSpline n u ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox u

/-- The symmetric box is nonnegative. -/
theorem knsBox_nonneg (r x : ℝ) : 0 ≤ knsBox r x := by
  unfold knsBox
  exact indicator_nonneg (fun _ _ => zero_le_one) x

/-- The symmetric box is bounded by one. -/
theorem knsBox_le_one (r x : ℝ) : knsBox r x ≤ 1 := by
  by_cases hx : x ∈ Icc (-r) r <;> simp [knsBox, hx]

/-- The box has the stated pointwise support, including its boundary. -/
theorem support_knsBox_subset (r : ℝ) : Function.support (knsBox r) ⊆ Icc (-r) r :=
  support_indicator_subset

/-- Every finite box is integrable, including when its defining interval is empty. -/
theorem integrable_knsBox (r : ℝ) : Integrable (knsBox r) := by
  exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- The exact box mass is its interval length. -/
theorem integral_knsBox {r : ℝ} (hr : 0 ≤ r) : ∫ x, knsBox r x = 2*r := by
  rw [knsBox, integral_indicator measurableSet_Icc]
  simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Measure.real, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r)]
  ring

/-- The normalized short box is integrable. -/
theorem integrable_knsBeta (n : ℕ) (u : ℝ) : Integrable (knsBeta n u) :=
  (integrable_knsBox _).const_mul _

/-- The normalized short box is nonnegative. -/
theorem knsBeta_nonneg (n : ℕ) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    0 ≤ knsBeta n u x := mul_nonneg (div_nonneg (Nat.cast_nonneg _) hu.le) (knsBox_nonneg _ _)

/-- The normalized short box has height at most n/u. -/
theorem knsBeta_le (n : ℕ) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    knsBeta n u x ≤ (n : ℝ)/u := by
  exact mul_le_of_le_one_right (div_nonneg (Nat.cast_nonneg _) hu.le) (knsBox_le_one _ _)

/-- The true normalization of the short box gives exactly unit mass. -/
theorem integral_knsBeta {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    ∫ x, knsBeta n u x = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold knsBeta
  rw [integral_const_mul, integral_knsBox (by positivity)]
  field_simp

/-- The normalized short box is supported in its exact short interval. -/
theorem support_knsBeta_subset (n : ℕ) (u : ℝ) :
    Function.support (knsBeta n u) ⊆ Icc (-(u/(2*n))) (u/(2*n)) := by
  intro x hx
  apply support_knsBox_subset (u/(2*n))
  intro h
  exact hx (by simp [knsBeta, h])

/-- The first-order spline really is the normalized box, not a limiting distribution. -/
theorem knsBSpline_one (u : ℝ) : knsBSpline 1 u = knsBeta 1 u := rfl

/-- Integrability is preserved by every actual box convolution. -/
theorem integrable_knsBoxConvolution {g : ℝ → ℝ} (hg : Integrable g) (j : ℕ) :
    Integrable (knsBoxConvolution g j) := by
  induction j with
  | zero => exact hg
  | succ j ih => exact hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) ih

/-- Nonnegativity is preserved pointwise by actual convolution. -/
theorem knsBoxConvolution_nonneg {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (j : ℕ) (x : ℝ) :
    0 ≤ knsBoxConvolution g j x := by
  induction j generalizing x with
  | zero => exact hg x
  | succ j ih => exact integral_nonneg (fun y => mul_nonneg (hg y) (ih (x-y)))

/-- A probability-density box convolution retains exactly unit mass. -/
theorem integral_knsBoxConvolution {g : ℝ → ℝ} (hg : Integrable g)
    (hm : ∫ x, g x = 1) (j : ℕ) : ∫ x, knsBoxConvolution g j x = 1 := by
  induction j with
  | zero => exact hm
  | succ j ih =>
    rw [knsBoxConvolution, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      hg (integrable_knsBoxConvolution hg j)]
    simp only [ContinuousLinearMap.mul_apply', hm, ih, mul_one]

private theorem support_realConvolution_subset {f g : ℝ → ℝ} {r s : ℝ}
    (hf : Function.support f ⊆ Icc (-r) r) (hg : Function.support g ⊆ Icc (-s) s) :
    Function.support (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⊆ Icc (-(r+s)) (r+s) := by
  intro x hx
  rcases support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx with ⟨y, hy, z, hz, rfl⟩
  obtain ⟨hy₁, hy₂⟩ := hf hy
  obtain ⟨hz₁, hz₂⟩ := hg hz
  constructor <;> linarith

/-- The exact support radius of j+1 short-box convolutions is at most
(j+1) times the short-box radius. -/
theorem support_knsBoxConvolution_subset {g : ℝ → ℝ} {r : ℝ}
    (hg : Function.support g ⊆ Icc (-r) r) (j : ℕ) :
    Function.support (knsBoxConvolution g j) ⊆ Icc (-(((j+1:ℕ):ℝ)*r)) (((j+1:ℕ):ℝ)*r) := by
  induction j with
  | zero => simpa only [knsBoxConvolution, Nat.zero_add, Nat.cast_one, one_mul] using hg
  | succ j ih =>
    have h := support_realConvolution_subset hg ih
    have he : r+((j+1:ℕ):ℝ)*r = ((j+1+1:ℕ):ℝ)*r := by push_cast; ring
    rw [he] at h
    exact h

/-- The actual B-spline is integrable. -/
theorem integrable_knsBSpline (n : ℕ) (u : ℝ) : Integrable (knsBSpline n u) :=
  integrable_knsBoxConvolution (integrable_knsBeta n u) (n-1)

/-- The actual B-spline is nonnegative. -/
theorem knsBSpline_nonneg (n : ℕ) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    0 ≤ knsBSpline n u x := knsBoxConvolution_nonneg (knsBeta_nonneg n hu) (n-1) x

/-- The actual positive-order B-spline has exactly unit mass. -/
theorem integral_knsBSpline {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    ∫ x, knsBSpline n u x = 1 :=
  integral_knsBoxConvolution (integrable_knsBeta n u) (integral_knsBeta hn hu) (n-1)

/-- The actual n-fold short-box convolution stays in [-u/2,u/2]. -/
theorem support_knsBSpline_subset {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    Function.support (knsBSpline n u) ⊆ Icc (-(u/2)) (u/2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h := support_knsBoxConvolution_subset (support_knsBeta_subset n u) (n-1)
  have hnat : n-1+1=n := by omega
  rw [hnat] at h
  have he : (n:ℝ)*(u/(2*n)) = u/2 := by field_simp
  rw [he] at h
  exact h

/-- The true localizer is integrable. -/
theorem integrable_knsMomentLocalizer (n : ℕ) (u : ℝ) : Integrable (knsMomentLocalizer n u) :=
  (integrable_knsBSpline n u).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_knsBox u)

/-- The actual localizer is pointwise nonnegative. -/
theorem knsMomentLocalizer_nonneg (n : ℕ) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    0 ≤ knsMomentLocalizer n u x :=
  integral_nonneg (fun y => mul_nonneg (knsBSpline_nonneg n hu y) (knsBox_nonneg u (x-y)))

/-- Convolution with a probability density keeps the localizer at most one. -/
theorem knsMomentLocalizer_le_one {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    knsMomentLocalizer n u x ≤ 1 := by
  rw [← integral_knsBSpline hn hu]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun y => mul_nonneg (knsBSpline_nonneg n hu y)
      (knsBox_nonneg u (x-y)))) (integrable_knsBSpline n u)
    (Filter.Eventually.of_forall (fun y => mul_le_of_le_one_right
      (knsBSpline_nonneg n hu y) (knsBox_le_one u (x-y))))

/-- The exact support of the localizer is contained in [-3u/2,3u/2]. -/
theorem support_knsMomentLocalizer_subset {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    Function.support (knsMomentLocalizer n u) ⊆ Icc (-(3*u/2)) (3*u/2) := by
  have h := support_realConvolution_subset (support_knsBSpline_subset hn u) (support_knsBox_subset u)
  rwa [show u/2+u=3*u/2 by ring] at h

/-- The localizer equals one on the full central closed interval, including
its two endpoints. -/
theorem knsMomentLocalizer_eq_one {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {x : ℝ} (hx : |x| ≤ u/2) : knsMomentLocalizer n u x = 1 := by
  rw [knsMomentLocalizer, convolution_def, ← integral_knsBSpline hn hu]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : knsBSpline n u y=0
  · simp [hy]
  · obtain ⟨hy₁, hy₂⟩ := support_knsBSpline_subset hn u hy
    obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
    have hxy : x-y ∈ Icc (-u) u := by constructor <;> linarith
    simp [knsBox, hxy]

/-- Commutativity identifies the definition with the source's long-box
followed by short-box convolution order. -/
theorem knsMomentLocalizer_eq_box_convolution (n : ℕ) (u : ℝ) :
    knsMomentLocalizer n u = knsBox u ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBSpline n u := by
  unfold knsMomentLocalizer
  rw [← convolution_flip (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure ℝ)) (f := knsBSpline n u) (g := knsBox u)]
  funext x
  simp only [convolution_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  congr 1
  funext y
  ring

/-- The localizer's exact L1 mass is the long-box length 2u. -/
theorem integral_knsMomentLocalizer {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    ∫ x, knsMomentLocalizer n u x = 2*u := by
  rw [knsMomentLocalizer, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_knsBSpline n u) (integrable_knsBox u)]
  simp only [ContinuousLinearMap.mul_apply', integral_knsBSpline hn hu,
    integral_knsBox hu.le, one_mul]

/-- The actual localizer is square integrable; boundedness and L1
integrability suffice, without any extra smoothness premise. -/
theorem integrable_knsMomentLocalizer_sq {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ => |knsMomentLocalizer n u x|^2) := by
  have hF := integrable_knsMomentLocalizer n u
  have hm : AEStronglyMeasurable (fun x : ℝ => |knsMomentLocalizer n u x|^2) volume := by
    have he : (fun x : ℝ => |knsMomentLocalizer n u x|^2) =
        (fun x => ‖knsMomentLocalizer n u x‖) * (fun x => ‖knsMomentLocalizer n u x‖) := by
      funext x
      simp only [pow_two, Real.norm_eq_abs, Pi.mul_apply]
    rw [he]
    exact hF.aestronglyMeasurable.norm.mul hF.aestronglyMeasurable.norm
  apply hF.mono' hm
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
  have hnF := knsMomentLocalizer_nonneg n hu x
  have hleF := knsMomentLocalizer_le_one hn hu x
  nlinarith

/-- The true L2 mass is at least u because the whole central interval
of length u is a plateau of height one. -/
theorem integral_knsMomentLocalizer_sq_ge {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    u ≤ ∫ x : ℝ, |knsMomentLocalizer n u x|^2 := by
  have hmass : (∫ x, knsBox (u/2) x) = u := by
    rw [integral_knsBox (by positivity)]
    ring
  conv_lhs => rw [← hmass]
  apply integral_mono (integrable_knsBox _) (integrable_knsMomentLocalizer_sq hn hu)
  intro x
  by_cases hx : x ∈ Icc (-(u/2)) (u/2)
  · have hplateau := knsMomentLocalizer_eq_one hn hu (abs_le.mpr hx)
    simp [knsBox, hx, hplateau]
  · simp only [knsBox, indicator_of_notMem hx]
    positivity

end

end MeyerGeneralProblem
