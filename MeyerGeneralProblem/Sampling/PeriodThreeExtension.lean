module

public import MeyerGeneralProblem.Sampling.AmplitudeMultiplier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# Fixed period-three torus extension

This file constructs a fixed smooth cutoff and periodizes a mixed-`C⁴`
amplitude on `[-1,2]²`.  It proves absolute summability of the resulting
two-dimensional Fourier coefficients with a uniform quantitative bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Metric Topology

/-- Normalized Haar measure used for unit-circle Fourier coefficients in this module. -/
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Fixed smooth cutoff for the physical logarithmic coordinate. -/
def periodThreeCutoffBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 5 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed cutoff equals one on `[0,1]` and vanishes well before the
period-three endpoints `-1` and `2`. -/
def periodThreeCutoff (u : ℝ) : ℝ := periodThreeCutoffBump u

/-- Complex-valued form of the fixed cutoff used in Leibniz estimates. -/
def periodThreeCutoffC (u : ℝ) : ℂ := periodThreeCutoff u

theorem periodThreeCutoff_contDiff (n : ℕ∞) :
    ContDiff ℝ n periodThreeCutoff := by
  exact periodThreeCutoffBump.contDiff

theorem periodThreeCutoffC_contDiff (n : ℕ∞) :
    ContDiff ℝ n periodThreeCutoffC := by
  exact Complex.ofRealCLM.contDiff.comp (periodThreeCutoff_contDiff n)

theorem hasCompactSupport_iteratedDeriv
    {q : ℝ → ℂ} (hq : HasCompactSupport q) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n q) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hq
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem periodThreeCutoffC_hasCompactSupport :
    HasCompactSupport periodThreeCutoffC := by
  exact periodThreeCutoffBump.hasCompactSupport.comp_left rfl

/-- One fixed real constant bounds the cutoff and its first two derivatives. -/
theorem exists_periodThreeCutoffC_deriv_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (i : ℕ), i ≤ 2 → ∀ u : ℝ,
      ‖iteratedDeriv i periodThreeCutoffC u‖ ≤ K := by
  have hcont (i : ℕ) : Continuous (iteratedDeriv i periodThreeCutoffC) :=
    (periodThreeCutoffC_contDiff ⊤).continuous_iteratedDeriv i (by simp)
  obtain ⟨K0, hK0⟩ := (hcont 0).bounded_above_of_compact_support
    (hasCompactSupport_iteratedDeriv periodThreeCutoffC_hasCompactSupport 0)
  obtain ⟨K1, hK1⟩ := (hcont 1).bounded_above_of_compact_support
    (hasCompactSupport_iteratedDeriv periodThreeCutoffC_hasCompactSupport 1)
  obtain ⟨K2, hK2⟩ := (hcont 2).bounded_above_of_compact_support
    (hasCompactSupport_iteratedDeriv periodThreeCutoffC_hasCompactSupport 2)
  refine ⟨|K0| + |K1| + |K2| + 1, by
    nlinarith [abs_nonneg K0, abs_nonneg K1, abs_nonneg K2], ?_⟩
  intro i hi u
  interval_cases i
  · exact (hK0 u).trans (by
      nlinarith [le_abs_self K0, abs_nonneg K1, abs_nonneg K2])
  · exact (hK1 u).trans (by
      nlinarith [le_abs_self K1, abs_nonneg K0, abs_nonneg K2])
  · exact (hK2 u).trans (by
      nlinarith [le_abs_self K2, abs_nonneg K0, abs_nonneg K1])

/-- A fixed bound for the cutoff and its first two derivatives. -/
noncomputable def periodThreeCutoffDerivativeBound : ℝ :=
  Classical.choose exists_periodThreeCutoffC_deriv_bound

theorem periodThreeCutoffDerivativeBound_one_le :
    1 ≤ periodThreeCutoffDerivativeBound :=
  (Classical.choose_spec exists_periodThreeCutoffC_deriv_bound).1

theorem norm_iteratedDeriv_periodThreeCutoffC_le
    (i : ℕ) (hi : i ≤ 2) (u : ℝ) :
    ‖iteratedDeriv i periodThreeCutoffC u‖ ≤
      periodThreeCutoffDerivativeBound :=
  (Classical.choose_spec exists_periodThreeCutoffC_deriv_bound).2 i hi u

theorem iteratedDeriv_comp_three_sub_one
    {q : ℝ → ℂ} (n : ℕ) (hq : ContDiff ℝ n q) (x : ℝ) :
    iteratedDeriv n (fun t => q (3 * t - 1)) x =
      (3 : ℝ) ^ n • iteratedDeriv n q (3 * x - 1) := by
  have hshift : ContDiff ℝ n (fun z : ℝ => q (z - 1)) :=
    hq.comp (by fun_prop)
  have hscale := congrFun (iteratedDeriv_comp_const_smul hshift (3 : ℝ)) x
  rw [iteratedDeriv_comp_sub_const] at hscale
  simpa only [sub_eq_add_neg] using hscale

theorem periodThreeCutoff_eq_one {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    periodThreeCutoff u = 1 := by
  apply periodThreeCutoffBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq]
  change |u - 1 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

theorem periodThreeCutoff_eq_zero_of_le_neg_one {u : ℝ} (hu : u ≤ -1) :
    periodThreeCutoff u = 0 := by
  apply periodThreeCutoffBump.zero_of_le_dist
  rw [Real.dist_eq, abs_of_nonpos]
  · change 5 / 4 ≤ -(u - 1 / 2)
    linarith
  · linarith

theorem periodThreeCutoff_eq_zero_of_two_le {u : ℝ} (hu : 2 ≤ u) :
    periodThreeCutoff u = 0 := by
  apply periodThreeCutoffBump.zero_of_le_dist
  rw [Real.dist_eq, abs_of_nonneg]
  · change 5 / 4 ≤ u - 1 / 2
    linarith
  · linarith

theorem periodThreeCutoff_eq_zero_of_le_neg_three_fourths
    {u : ℝ} (hu : u ≤ -(3 / 4 : ℝ)) :
    periodThreeCutoff u = 0 := by
  apply periodThreeCutoffBump.zero_of_le_dist
  rw [Real.dist_eq, abs_of_nonpos]
  · change 5 / 4 ≤ -(u - 1 / 2)
    linarith
  · linarith

theorem periodThreeCutoff_eq_zero_of_seven_fourths_le
    {u : ℝ} (hu : (7 / 4 : ℝ) ≤ u) :
    periodThreeCutoff u = 0 := by
  apply periodThreeCutoffBump.zero_of_le_dist
  rw [Real.dist_eq, abs_of_nonneg]
  · change 5 / 4 ≤ u - 1 / 2
    linarith
  · linarith

@[simp]
theorem periodThreeCutoff_neg_one : periodThreeCutoff (-1) = 0 :=
  periodThreeCutoff_eq_zero_of_le_neg_one le_rfl

@[simp]
theorem periodThreeCutoff_two : periodThreeCutoff 2 = 0 :=
  periodThreeCutoff_eq_zero_of_two_le le_rfl

/-- Cut off an amplitude before periodizing the square `[-1,2]²`. -/
def periodThreeCutoffAmplitude (f : ℝ → ℝ → ℂ) (u v : ℝ) : ℂ :=
  (periodThreeCutoff u * periodThreeCutoff v : ℝ) * f u v

theorem periodThreeCutoffAmplitude_contDiff
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f)) :
    ContDiff ℝ 4 (Function.uncurry (periodThreeCutoffAmplitude f)) := by
  change ContDiff ℝ 4 (fun p : ℝ × ℝ =>
    (periodThreeCutoff p.1 * periodThreeCutoff p.2 : ℝ) * f p.1 p.2)
  have hscalar : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      periodThreeCutoff p.1 * periodThreeCutoff p.2) := by
    exact ((periodThreeCutoff_contDiff 4).comp contDiff_fst).mul
      ((periodThreeCutoff_contDiff 4).comp contDiff_snd)
  exact (Complex.ofRealCLM.contDiff.comp hscalar).mul hf

theorem periodThreeCutoffAmplitude_eq
    {f : ℝ → ℝ → ℂ} {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    periodThreeCutoffAmplitude f u v = f u v := by
  simp [periodThreeCutoffAmplitude,
    periodThreeCutoff_eq_one hu, periodThreeCutoff_eq_one hv]

/-- The cut-off amplitude in normalized unit-square coordinates. -/
def periodThreeScaledCutoffAmplitude (f : ℝ → ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  periodThreeCutoffAmplitude f (3 * p.1 - 1) (3 * p.2 - 1)

theorem periodThreeScaledCutoffAmplitude_contDiff
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f)) :
    ContDiff ℝ 4 (periodThreeScaledCutoffAmplitude f) := by
  have hcut := periodThreeCutoffAmplitude_contDiff hf
  change ContDiff ℝ 4 (fun p : ℝ × ℝ =>
    periodThreeCutoffAmplitude f p.1 p.2) at hcut
  have hscale : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      (3 * p.1 - 1, 3 * p.2 - 1)) := by fun_prop
  change ContDiff ℝ 4 (fun p : ℝ × ℝ =>
    periodThreeCutoffAmplitude f (3 * p.1 - 1) (3 * p.2 - 1))
  exact hcut.comp hscale

theorem periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_zero
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    periodThreeScaledCutoffAmplitude f =ᶠ[𝓝 ((0 : ℝ), y)] 0 := by
  filter_upwards [continuousAt_fst
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 12))] with p hp
  change p.1 < 1 / 12 at hp
  simp only [periodThreeScaledCutoffAmplitude, periodThreeCutoffAmplitude]
  rw [periodThreeCutoff_eq_zero_of_le_neg_three_fourths (by linarith)]
  norm_num

theorem periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_one
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    periodThreeScaledCutoffAmplitude f =ᶠ[𝓝 ((1 : ℝ), y)] 0 := by
  filter_upwards [continuousAt_fst
    (eventually_gt_nhds (by norm_num : (11 / 12 : ℝ) < 1))] with p hp
  change 11 / 12 < p.1 at hp
  simp only [periodThreeScaledCutoffAmplitude, periodThreeCutoffAmplitude]
  rw [periodThreeCutoff_eq_zero_of_seven_fourths_le (by linarith)]
  norm_num

theorem periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_zero
    (f : ℝ → ℝ → ℂ) (x : ℝ) :
    periodThreeScaledCutoffAmplitude f =ᶠ[𝓝 (x, (0 : ℝ))] 0 := by
  filter_upwards [continuousAt_snd
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 12))] with p hp
  change p.2 < 1 / 12 at hp
  simp only [periodThreeScaledCutoffAmplitude, periodThreeCutoffAmplitude]
  rw [show periodThreeCutoff (3 * p.2 - 1) = 0 by
    exact periodThreeCutoff_eq_zero_of_le_neg_three_fourths (by linarith)]
  norm_num

theorem periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_one
    (f : ℝ → ℝ → ℂ) (x : ℝ) :
    periodThreeScaledCutoffAmplitude f =ᶠ[𝓝 (x, (1 : ℝ))] 0 := by
  filter_upwards [continuousAt_snd
    (eventually_gt_nhds (by norm_num : (11 / 12 : ℝ) < 1))] with p hp
  change 11 / 12 < p.2 at hp
  simp only [periodThreeScaledCutoffAmplitude, periodThreeCutoffAmplitude]
  rw [show periodThreeCutoff (3 * p.2 - 1) = 0 by
    exact periodThreeCutoff_eq_zero_of_seven_fourths_le (by linarith)]
  norm_num

/-- A lift through `liftIco` agrees at the right endpoint as well when the
two endpoint values match. -/
theorem liftIco_coe_apply_of_mem_unitIcc
    {B : Type*} {f : ℝ → B} (hf : f 0 = f 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    AddCircle.liftIco 1 0 f (x : UnitAddCircle) = f x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hx1
  · rw [show ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by
      simp]
    rw [AddCircle.liftIco_coe_apply]
    · exact hf
    · norm_num
  · exact AddCircle.liftIco_coe_apply ⟨hx.1, by simpa using hx1⟩

/-- The closed unit square maps onto the two-dimensional unit torus. -/
def unitSquareToTorus
    (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : UnitAddTorus (Fin 2) :=
  ![(p.1.1 : UnitAddCircle), (p.2.1 : UnitAddCircle)]

theorem unitSquareToTorus_surjective : Function.Surjective unitSquareToTorus := by
  intro z
  obtain ⟨x, hx, hxz⟩ := AddCircle.eq_coe_Ico (z 0)
  obtain ⟨y, hy, hyz⟩ := AddCircle.eq_coe_Ico (z 1)
  refine ⟨(⟨x, hx.1, hx.2.le⟩, ⟨y, hy.1, hy.2.le⟩), ?_⟩
  funext i
  fin_cases i
  · exact hxz
  · exact hyz

theorem unitSquareToTorus_continuous : Continuous unitSquareToTorus := by
  unfold unitSquareToTorus
  fun_prop

@[simp]
theorem unitAddTorusPair_eta (z : UnitAddTorus (Fin 2)) :
    unitAddTorusPair (z 0) (z 1) = z := by
  funext i
  fin_cases i <;> simp

theorem unitSquareToTorus_isQuotientMap :
    IsQuotientMap unitSquareToTorus :=
  IsQuotientMap.of_surjective_continuous
    unitSquareToTorus_surjective unitSquareToTorus_continuous

/-- Fixed period-three periodization of a physical amplitude. -/
def periodThreeTorusExtension (f : ℝ → ℝ → ℂ) :
    UnitAddTorus (Fin 2) → ℂ := fun z =>
  AddCircle.liftIco 1 0
    (fun x => AddCircle.liftIco 1 0
      (fun y => periodThreeCutoffAmplitude f (3 * x - 1) (3 * y - 1))
      (z 1))
    (z 0)

theorem periodThreeTorusExtension_unitSquare
    (f : ℝ → ℝ → ℂ) (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) :
    periodThreeTorusExtension f (unitSquareToTorus p) =
      periodThreeCutoffAmplitude f (3 * p.1.1 - 1) (3 * p.2.1 - 1) := by
  let H : ℝ → ℝ → ℂ := fun x y =>
    periodThreeCutoffAmplitude f (3 * x - 1) (3 * y - 1)
  have hyEnd (x : ℝ) : H x 0 = H x 1 := by
    change periodThreeCutoffAmplitude f (3 * x - 1) (3 * 0 - 1) =
      periodThreeCutoffAmplitude f (3 * x - 1) (3 * 1 - 1)
    rw [show (3 : ℝ) * 0 - 1 = -1 by norm_num,
      show (3 : ℝ) * 1 - 1 = 2 by norm_num]
    simp [periodThreeCutoffAmplitude]
  have hxEnd (z : UnitAddCircle) :
      AddCircle.liftIco 1 0 (H 0) z =
        AddCircle.liftIco 1 0 (H 1) z := by
    have hfun : H 0 = H 1 := by
      funext y
      change periodThreeCutoffAmplitude f (3 * 0 - 1) (3 * y - 1) =
        periodThreeCutoffAmplitude f (3 * 1 - 1) (3 * y - 1)
      rw [show (3 : ℝ) * 0 - 1 = -1 by norm_num,
        show (3 : ℝ) * 1 - 1 = 2 by norm_num]
      simp [periodThreeCutoffAmplitude]
    rw [hfun]
  change AddCircle.liftIco 1 0
      (fun x => AddCircle.liftIco 1 0 (H x) (p.2.1 : UnitAddCircle))
      (p.1.1 : UnitAddCircle) = H p.1.1 p.2.1
  rw [liftIco_coe_apply_of_mem_unitIcc (hxEnd _ ) p.1.2]
  rw [liftIco_coe_apply_of_mem_unitIcc (hyEnd _) p.2.2]

theorem periodThreeTorusExtension_continuous
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f)) :
    Continuous (periodThreeTorusExtension f) := by
  rw [unitSquareToTorus_isQuotientMap.continuous_iff]
  have hcut := (periodThreeCutoffAmplitude_contDiff hf).continuous
  have hphysical : Continuous (fun p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      periodThreeCutoffAmplitude f (3 * p.1.1 - 1) (3 * p.2.1 - 1)) := by
    let g : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℝ × ℝ := fun p =>
      (3 * p.1.1 - 1, 3 * p.2.1 - 1)
    have hg : Continuous g := by
      unfold g
      fun_prop
    change Continuous (Function.uncurry (periodThreeCutoffAmplitude f) ∘ g)
    exact hcut.comp hg
  have heq : periodThreeTorusExtension f ∘ unitSquareToTorus =
      fun p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
        periodThreeCutoffAmplitude f (3 * p.1.1 - 1) (3 * p.2.1 - 1) := by
    funext p
    exact periodThreeTorusExtension_unitSquare f p
  rw [heq]
  exact hphysical

/-- Continuous-map package of the fixed period-three extension. -/
def periodThreeTorusExtensionC
    (f : ℝ → ℝ → ℂ) (hf : ContDiff ℝ 4 (Function.uncurry f)) :
    C(UnitAddTorus (Fin 2), ℂ) :=
  ⟨periodThreeTorusExtension f, periodThreeTorusExtension_continuous hf⟩

theorem periodThreeTorusExtensionC_apply_physical
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    periodThreeTorusExtensionC f hf
        (unitAddTorusPair (periodThreeTorusPoint u) (periodThreeTorusPoint v)) =
      f u v := by
  have hu' : (u + 1) / 3 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hv' : (v + 1) / 3 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  let p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 :=
    (⟨(u + 1) / 3, hu'⟩, ⟨(v + 1) / 3, hv'⟩)
  have hp : unitSquareToTorus p =
      unitAddTorusPair (periodThreeTorusPoint u) (periodThreeTorusPoint v) := by
    funext i
    fin_cases i <;> rfl
  change periodThreeTorusExtension f
      (unitAddTorusPair (periodThreeTorusPoint u) (periodThreeTorusPoint v)) = f u v
  rw [← hp, periodThreeTorusExtension_unitSquare]
  change periodThreeCutoffAmplitude f
      (3 * ((u + 1) / 3) - 1) (3 * ((v + 1) / 3) - 1) = f u v
  rw [show 3 * ((u + 1) / 3) - 1 = u by ring,
    show 3 * ((v + 1) / 3) - 1 = v by ring]
  exact periodThreeCutoffAmplitude_eq hu hv

/-- Two integrations by parts give quadratic decay of every nonzero
one-dimensional Fourier mode when the function and its first derivative
match at the endpoints. -/
theorem fourierCoeffOn_eq_neg_inv_sq_mul
    {f f' f'' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hper : f 0 = f 1) (hper' : f' 0 = f' 1)
    {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one f n =
      (1 / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ 2) *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one f'' n := by
  have hf'int : IntervalIntegrable f' MeasureTheory.volume 0 1 :=
    (continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt).intervalIntegrable _ _
  have hf''int : IntervalIntegrable f'' MeasureTheory.volume 0 1 :=
    hf''.intervalIntegrable _ _
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn (fun x _ => hf x) hf'int,
    fourierCoeffOn_of_hasDerivAt zero_lt_one hn (fun x _ => hf' x) hf''int,
    hper, hper']
  simp only [sub_self, mul_zero, zero_sub]
  norm_num
  ring_nf
  rw [Complex.inv_I]
  ring

theorem norm_fourierCoeffOn_le_of_norm_le
    {f : ℝ → ℂ} {B : ℝ} (_hB : 0 ≤ B)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B) (n : ℤ) :
    ‖fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one f n‖ ≤ B := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, one_div, one_smul]
  have hbound : ‖∫ x in (0 : ℝ)..1,
      fourier (-n) (x : UnitAddCircle) • f x‖ ≤ B := by
    calc
      ‖∫ x in (0 : ℝ)..1,
          fourier (-n) (x : UnitAddCircle) • f x‖ ≤ B * |(1 : ℝ) - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
        have hx' : x ∈ Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hx
        exact hf x ⟨hx'.1.le, hx'.2⟩
      _ = B := by simp
  convert hbound using 1
  all_goals norm_num

/-- Quadratic Fourier decay phrased using the canonical iterated derivative. -/
theorem fourierCoeffOn_eq_inv_sq_mul_iteratedDeriv
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : f 0 = f 1) (hper' : deriv f 0 = deriv f 1)
    {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one f n =
      (1 / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ 2) *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (iteratedDeriv 2 f) n := by
  apply fourierCoeffOn_eq_neg_inv_sq_mul
  · intro x
    exact (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · intro x
    have hd : HasDerivAt (iteratedDeriv 1 f)
        (deriv (iteratedDeriv 1 f) x) x :=
      (hf.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    convert hd using 1
    all_goals rw [iteratedDeriv_one]
  · exact hf.continuous_iteratedDeriv 2 (by norm_num)
  · exact hper
  · exact hper'
  · exact hn

/-- Fubini commutes the two normalized one-dimensional coefficients. -/
theorem fourierCoeffOn_fourierCoeffOn_comm
    {h : ℝ → ℝ → ℂ} (hh : Continuous (Function.uncurry h))
    (n₀ n₁ : ℤ) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun x => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (h x) n₁) n₀ =
      fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun y => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => h x y) n₀) n₁ := by
  simp only [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, one_div, one_smul]
  simp only [smul_eq_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  let G : ℝ → ℝ → ℂ := fun x y =>
    fourier (-n₀) (x : UnitAddCircle) *
      (fourier (-n₁) (y : UnitAddCircle) * h x y)
  have hG : Continuous (Function.uncurry G) := by
    unfold G
    fun_prop
  have hGint : MeasureTheory.IntegrableOn (Function.uncurry G)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) :=
    (hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono (by simpa using (uIoc_subset_uIcc : uIoc (0 : ℝ) 1 ⊆ uIcc 0 1))
        (by simpa using (uIoc_subset_uIcc : uIoc (0 : ℝ) 1 ⊆ uIcc 0 1)))
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap hGint
  simp only [G] at hswap
  convert hswap using 1 <;> norm_num
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

/-- First Cartesian partial derivatives, expressed using the Fréchet derivative
so their parameter dependence remains visible to the `ContDiff` API. -/
def partialDerivX (g : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ g p (1, 0)

/-- First derivative in the second Cartesian coordinate. -/
def partialDerivY (g : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ g p (0, 1)

/-- Second derivative in the second Cartesian coordinate. -/
def partialDerivYY (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  partialDerivY (partialDerivY g)

/-- Second derivative in the first Cartesian coordinate. -/
def partialDerivXX (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  partialDerivX (partialDerivX g)

/-- Two derivatives in each Cartesian coordinate. -/
def partialDerivXXYY (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  partialDerivX (partialDerivX (partialDerivYY g))

theorem partialDerivY_contDiff_three
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 3 (partialDerivY g) := by
  unfold partialDerivY
  exact (hg.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem partialDerivYY_contDiff_two
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 2 (partialDerivYY g) := by
  unfold partialDerivYY
  exact ((partialDerivY_contDiff_three hg).fderiv_right (by norm_num)).clm_apply
    contDiff_const

theorem partialDerivX_contDiff_three
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 3 (partialDerivX g) := by
  unfold partialDerivX
  exact (hg.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem partialDerivXX_contDiff_two
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 2 (partialDerivXX g) := by
  unfold partialDerivXX
  exact ((partialDerivX_contDiff_three hg).fderiv_right (by norm_num)).clm_apply
    contDiff_const

theorem partialDerivX_partialDerivYY_contDiff_one
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 1 (partialDerivX (partialDerivYY g)) := by
  unfold partialDerivX
  exact ((partialDerivYY_contDiff_two hg).fderiv_right (by norm_num)).clm_apply
    contDiff_const

theorem partialDerivXXYY_continuous
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) :
    Continuous (partialDerivXXYY g) := by
  unfold partialDerivXXYY partialDerivX
  have hfd := (partialDerivX_partialDerivYY_contDiff_one hg).fderiv_right
    (m := 0) (by norm_num)
  exact (hfd.clm_apply contDiff_const).continuous

theorem partialDerivY_eventuallyEq_zero
    {g : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : g =ᶠ[𝓝 p] (0 : (ℝ × ℝ) → ℂ)) :
    partialDerivY g =ᶠ[𝓝 p] (0 : (ℝ × ℝ) → ℂ) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  unfold partialDerivY
  rw [hq]
  simp

theorem partialDerivX_eventuallyEq_zero
    {g : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : g =ᶠ[𝓝 p] (0 : (ℝ × ℝ) → ℂ)) :
    partialDerivX g =ᶠ[𝓝 p] (0 : (ℝ × ℝ) → ℂ) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  unfold partialDerivX
  rw [hq]
  simp

theorem periodThreeScaledCutoffAmplitude_periodic_y
    (f : ℝ → ℝ → ℂ) (x : ℝ) :
    periodThreeScaledCutoffAmplitude f (x, 0) =
      periodThreeScaledCutoffAmplitude f (x, 1) := by
  have h0 := periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_zero f x
  have h1 := periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_one f x
  calc
    periodThreeScaledCutoffAmplitude f (x, 0) = 0 := by
      simpa using h0.eq_of_nhds
    _ = periodThreeScaledCutoffAmplitude f (x, 1) := by
      simpa using h1.eq_of_nhds.symm

theorem periodThreeScaledCutoffAmplitude_partialDerivY_periodic
    (f : ℝ → ℝ → ℂ) (x : ℝ) :
    partialDerivY (periodThreeScaledCutoffAmplitude f) (x, 0) =
      partialDerivY (periodThreeScaledCutoffAmplitude f) (x, 1) := by
  have h0 := partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_zero f x)
  have h1 := partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_y_one f x)
  calc
    partialDerivY (periodThreeScaledCutoffAmplitude f) (x, 0) = 0 := by
      simpa using h0.eq_of_nhds
    _ = partialDerivY (periodThreeScaledCutoffAmplitude f) (x, 1) := by
      simpa using h1.eq_of_nhds.symm

theorem periodThreeScaledCutoffAmplitude_periodic_x
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    periodThreeScaledCutoffAmplitude f (0, y) =
      periodThreeScaledCutoffAmplitude f (1, y) := by
  have h0 := periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_zero f y
  have h1 := periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_one f y
  calc
    periodThreeScaledCutoffAmplitude f (0, y) = 0 := by
      simpa using h0.eq_of_nhds
    _ = periodThreeScaledCutoffAmplitude f (1, y) := by
      simpa using h1.eq_of_nhds.symm

theorem periodThreeScaledCutoffAmplitude_partialDerivX_periodic
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    partialDerivX (periodThreeScaledCutoffAmplitude f) (0, y) =
      partialDerivX (periodThreeScaledCutoffAmplitude f) (1, y) := by
  have h0 := partialDerivX_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_zero f y)
  have h1 := partialDerivX_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_one f y)
  calc
    partialDerivX (periodThreeScaledCutoffAmplitude f) (0, y) = 0 := by
      simpa using h0.eq_of_nhds
    _ = partialDerivX (periodThreeScaledCutoffAmplitude f) (1, y) := by
      simpa using h1.eq_of_nhds.symm

theorem periodThreeScaledCutoffAmplitude_partialDerivYY_periodic_x
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    partialDerivYY (periodThreeScaledCutoffAmplitude f) (0, y) =
      partialDerivYY (periodThreeScaledCutoffAmplitude f) (1, y) := by
  have h0 := partialDerivY_eventuallyEq_zero (partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_zero f y))
  have h1 := partialDerivY_eventuallyEq_zero (partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_one f y))
  change partialDerivY (partialDerivY (periodThreeScaledCutoffAmplitude f)) (0, y) =
    partialDerivY (partialDerivY (periodThreeScaledCutoffAmplitude f)) (1, y)
  calc
    partialDerivY (partialDerivY (periodThreeScaledCutoffAmplitude f)) (0, y) = 0 := by
      simpa using h0.eq_of_nhds
    _ = partialDerivY (partialDerivY (periodThreeScaledCutoffAmplitude f)) (1, y) := by
      simpa using h1.eq_of_nhds.symm

theorem periodThreeScaledCutoffAmplitude_partialDerivXYY_periodic_x
    (f : ℝ → ℝ → ℂ) (y : ℝ) :
    partialDerivX (partialDerivYY (periodThreeScaledCutoffAmplitude f)) (0, y) =
      partialDerivX (partialDerivYY (periodThreeScaledCutoffAmplitude f)) (1, y) := by
  have h0yy := partialDerivY_eventuallyEq_zero (partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_zero f y))
  have h1yy := partialDerivY_eventuallyEq_zero (partialDerivY_eventuallyEq_zero
    (periodThreeScaledCutoffAmplitude_eventuallyEq_zero_x_one f y))
  have h0 := partialDerivX_eventuallyEq_zero h0yy
  have h1 := partialDerivX_eventuallyEq_zero h1yy
  calc
    partialDerivX (partialDerivYY (periodThreeScaledCutoffAmplitude f)) (0, y) = 0 := by
      simpa [partialDerivYY] using h0.eq_of_nhds
    _ = partialDerivX (partialDerivYY (periodThreeScaledCutoffAmplitude f)) (1, y) := by
      simpa [partialDerivYY] using h1.eq_of_nhds.symm

theorem hasDerivAt_slice_y
    {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (x y : ℝ) :
    HasDerivAt (fun y' => g (x, y')) (partialDerivY g (x, y)) y := by
  have hline : HasDerivAt (fun y' : ℝ => (x, y')) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  simpa only [Function.comp_def, partialDerivY] using
    hg.differentiableAt.hasFDerivAt.comp_hasDerivAt y hline

theorem hasDerivAt_slice_x
    {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (x y : ℝ) :
    HasDerivAt (fun x' => g (x', y)) (partialDerivX g (x, y)) x := by
  have hline : HasDerivAt (fun x' : ℝ => (x', y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  simpa only [Function.comp_def, partialDerivX] using
    hg.differentiableAt.hasFDerivAt.comp_hasDerivAt x hline

theorem iteratedDeriv_two_slice_y_eq_partialDerivYY
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) (x y : ℝ) :
    iteratedDeriv 2 (fun y' => g (x, y')) y = partialDerivYY g (x, y) := by
  have hgDiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hYDiff : Differentiable ℝ (partialDerivY g) :=
    (partialDerivY_contDiff_three hg).differentiable (by norm_num)
  rw [show iteratedDeriv 2 (fun y' => g (x, y')) =
      deriv (deriv (fun y' => g (x, y'))) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (fun y' => g (x, y')) =
      fun y' => partialDerivY g (x, y') by
    funext y'
    exact (hasDerivAt_slice_y hgDiff x y').deriv]
  exact (hasDerivAt_slice_y hYDiff x y).deriv

theorem iteratedDeriv_two_slice_x_eq_partialDerivXX
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) (x y : ℝ) :
    iteratedDeriv 2 (fun x' => g (x', y)) x = partialDerivXX g (x, y) := by
  have hgDiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hXDiff : Differentiable ℝ (partialDerivX g) :=
    (partialDerivX_contDiff_three hg).differentiable (by norm_num)
  rw [show iteratedDeriv 2 (fun x' => g (x', y)) =
      deriv (deriv (fun x' => g (x', y))) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (fun x' => g (x', y)) =
      fun x' => partialDerivX g (x', y) by
    funext x'
    exact (hasDerivAt_slice_x hgDiff x' y).deriv]
  exact (hasDerivAt_slice_x hXDiff x y).deriv

theorem iteratedDeriv_two_slice_x_partialDerivYY_eq_partialDerivXXYY
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) (x y : ℝ) :
    iteratedDeriv 2 (fun x' => partialDerivYY g (x', y)) x =
      partialDerivXXYY g (x, y) := by
  have hYYDiff : Differentiable ℝ (partialDerivYY g) :=
    (partialDerivYY_contDiff_two hg).differentiable (by norm_num)
  have hXYYDiff : Differentiable ℝ (partialDerivX (partialDerivYY g)) :=
    (partialDerivX_partialDerivYY_contDiff_one hg).differentiable (by norm_num)
  rw [show iteratedDeriv 2 (fun x' => partialDerivYY g (x', y)) =
      deriv (deriv (fun x' => partialDerivYY g (x', y))) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (fun x' => partialDerivYY g (x', y)) =
      fun x' => partialDerivX (partialDerivYY g) (x', y) by
    funext x'
    exact (hasDerivAt_slice_x hYYDiff x' y).deriv]
  exact (hasDerivAt_slice_x hXYYDiff x y).deriv

/-- Scalar produced by two integrations by parts at a nonzero mode. -/
def quadraticFourierFactor (n : ℤ) : ℂ :=
  1 / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ 2

theorem norm_quadraticFourierFactor_le_integerUnitSlabEnvelope
    {n : ℤ} (hn : n ≠ 0) :
    ‖quadraticFourierFactor n‖ ≤
      (1 / Real.pi ^ 2) * integerUnitSlabEnvelope n := by
  unfold quadraticFourierFactor integerUnitSlabEnvelope
  simp only [norm_div, norm_one, norm_pow, norm_mul, Complex.norm_two,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
    Complex.norm_intCast, mul_one]
  have hnAbs : 1 ≤ |(n : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hn)
  have hden : Real.pi ^ 2 * (1 + |(n : ℝ)|) ^ 2 ≤
      (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
    nlinarith [Real.pi_pos, sq_nonneg (|(n : ℝ)| - 1)]
  calc
    1 / (2 * Real.pi * |(n : ℝ)|) ^ 2 ≤
        1 / (Real.pi ^ 2 * (1 + |(n : ℝ)|) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = (1 / Real.pi ^ 2) * (1 / (1 + |(n : ℝ)|) ^ 2) := by
      field_simp [Real.pi_pos.ne']

theorem fourierCoeffOn_slice_y_eq_quadraticFourierFactor
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hper : ∀ x, g (x, 0) = g (x, 1))
    (hper' : ∀ x, partialDerivY g (x, 0) = partialDerivY g (x, 1))
    (x : ℝ) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun y => g (x, y)) n =
      quadraticFourierFactor n *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun y => partialDerivYY g (x, y)) n := by
  have hslice : ContDiff ℝ 2 (fun y => g (x, y)) := by
    exact (hg.of_le (by norm_num)).comp (by fun_prop)
  have hderiv (y : ℝ) : deriv (fun y' => g (x, y')) y =
      partialDerivY g (x, y) :=
    (hasDerivAt_slice_y (hg.differentiable (by norm_num)) x y).deriv
  rw [fourierCoeffOn_eq_inv_sq_mul_iteratedDeriv hslice
    (hper x) (by simpa only [hderiv] using hper' x) hn]
  unfold quadraticFourierFactor
  congr 1
  apply congrArg (fun q : ℝ → ℂ =>
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one q n)
  funext y
  exact iteratedDeriv_two_slice_y_eq_partialDerivYY hg x y

theorem fourierCoeffOn_slice_x_eq_quadraticFourierFactor
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hper : ∀ y, g (0, y) = g (1, y))
    (hper' : ∀ y, partialDerivX g (0, y) = partialDerivX g (1, y))
    (y : ℝ) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun x => g (x, y)) n =
      quadraticFourierFactor n *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => partialDerivXX g (x, y)) n := by
  have hslice : ContDiff ℝ 2 (fun x => g (x, y)) := by
    exact (hg.of_le (by norm_num)).comp (by fun_prop)
  have hderiv (x : ℝ) : deriv (fun x' => g (x', y)) x =
      partialDerivX g (x, y) :=
    (hasDerivAt_slice_x (hg.differentiable (by norm_num)) x y).deriv
  rw [fourierCoeffOn_eq_inv_sq_mul_iteratedDeriv hslice
    (hper y) (by simpa only [hderiv] using hper' y) hn]
  unfold quadraticFourierFactor
  congr 1
  apply congrArg (fun q : ℝ → ℂ =>
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one q n)
  funext x
  exact iteratedDeriv_two_slice_x_eq_partialDerivXX hg x y

theorem fourierCoeffOn_slice_x_partialDerivYY_eq_quadraticFourierFactor
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hper : ∀ y, partialDerivYY g (0, y) = partialDerivYY g (1, y))
    (hper' : ∀ y, partialDerivX (partialDerivYY g) (0, y) =
      partialDerivX (partialDerivYY g) (1, y))
    (y : ℝ) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun x => partialDerivYY g (x, y)) n =
      quadraticFourierFactor n *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => partialDerivXXYY g (x, y)) n := by
  have hslice : ContDiff ℝ 2 (fun x => partialDerivYY g (x, y)) := by
    exact (partialDerivYY_contDiff_two hg).comp (by fun_prop)
  have hderiv (x : ℝ) : deriv (fun x' => partialDerivYY g (x', y)) x =
      partialDerivX (partialDerivYY g) (x, y) :=
    (hasDerivAt_slice_x
      ((partialDerivYY_contDiff_two hg).differentiable (by norm_num)) x y).deriv
  rw [fourierCoeffOn_eq_inv_sq_mul_iteratedDeriv hslice
    (hper y) (by simpa only [hderiv] using hper' y) hn]
  unfold quadraticFourierFactor
  congr 1
  apply congrArg (fun q : ℝ → ℂ =>
    fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one q n)
  funext x
  exact iteratedDeriv_two_slice_x_partialDerivYY_eq_partialDerivXXYY hg x y

/-- A two-dimensional torus Fourier coefficient is the iterated pair of
one-dimensional normalized Haar coefficients. -/
theorem mFourierCoeff_finTwo_eq_iterated
    (F : C(UnitAddTorus (Fin 2), ℂ)) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff F n =
      ∫ x : UnitAddCircle, fourier (-(n 0)) x *
        (∫ y : UnitAddCircle, fourier (-(n 1)) y *
          F (unitAddTorusPair x y)) := by
  unfold UnitAddTorus.mFourierCoeff
  let g : UnitAddCircle × UnitAddCircle → ℂ := fun p =>
    UnitAddTorus.mFourier (-n) (unitAddTorusPair p.1 p.2) •
      F (unitAddTorusPair p.1 p.2)
  have hgcont : Continuous g := by
    have hpair : Continuous (fun p : UnitAddCircle × UnitAddCircle =>
        unitAddTorusPair p.1 p.2) := by
      unfold unitAddTorusPair
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
    exact ((UnitAddTorus.mFourier (-n)).continuous.comp hpair).smul
      (F.continuous.comp hpair)
  have hgint : MeasureTheory.Integrable g :=
    hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hchange := (MeasureTheory.volume_preserving_finTwoArrow UnitAddCircle).integral_comp' g
  rw [show (∫ z : Fin 2 → UnitAddCircle,
      UnitAddTorus.mFourier (-n) z • F z) =
      ∫ p : UnitAddCircle × UnitAddCircle, g p by
        simpa only [g, MeasurableEquiv.finTwoArrow_apply,
          unitAddTorusPair_eta]
          using hchange]
  change (∫ p : UnitAddCircle × UnitAddCircle, g p
      ∂(MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle).prod
        MeasureTheory.volume) = _
  rw [MeasureTheory.integral_prod g hgint]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp [g, UnitAddTorus.mFourier, Fin.prod_univ_two,
    unitAddTorusPair, smul_eq_mul]
  ring

/-- Iterated normalized Fourier coefficient of a function on the unit square. -/
def iteratedFourierCoeffOn (h : ℝ → ℝ → ℂ) (n : Fin 2 → ℤ) : ℂ :=
  fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
    (fun x => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one (h x) (n 1))
    (n 0)

theorem iteratedFourierCoeffOn_comm
    {g : ℝ × ℝ → ℂ} (hg : Continuous g) (n : Fin 2 → ℤ) :
    iteratedFourierCoeffOn (Function.curry g) n =
      fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun y => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => g (x, y)) (n 0)) (n 1) := by
  exact fourierCoeffOn_fourierCoeffOn_comm
    (h := Function.curry g)
    (by simpa only [Function.uncurry_curry] using hg) (n 0) (n 1)

theorem iteratedFourierCoeffOn_eq_factor_y
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hperY : ∀ x, g (x, 0) = g (x, 1))
    (hperY' : ∀ x, partialDerivY g (x, 0) = partialDerivY g (x, 1))
    (n : Fin 2 → ℤ) (hn₁ : n 1 ≠ 0) :
    iteratedFourierCoeffOn (Function.curry g) n =
      quadraticFourierFactor (n 1) *
        iteratedFourierCoeffOn (Function.curry (partialDerivYY g)) n := by
  unfold iteratedFourierCoeffOn Function.curry
  rw [show (fun x => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
      (fun y => g (x, y)) (n 1)) =
      fun x => quadraticFourierFactor (n 1) *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun y => partialDerivYY g (x, y)) (n 1) by
    funext x
    exact fourierCoeffOn_slice_y_eq_quadraticFourierFactor
      hg hperY hperY' x hn₁]
  exact fourierCoeffOn.const_mul _ _ _ _

theorem iteratedFourierCoeffOn_eq_factor_x
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hperX : ∀ y, g (0, y) = g (1, y))
    (hperX' : ∀ y, partialDerivX g (0, y) = partialDerivX g (1, y))
    (n : Fin 2 → ℤ) (hn₀ : n 0 ≠ 0) :
    iteratedFourierCoeffOn (Function.curry g) n =
      quadraticFourierFactor (n 0) *
        iteratedFourierCoeffOn (Function.curry (partialDerivXX g)) n := by
  rw [iteratedFourierCoeffOn_comm hg.continuous n]
  rw [show (fun y => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
      (fun x => g (x, y)) (n 0)) =
      fun y => quadraticFourierFactor (n 0) *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => partialDerivXX g (x, y)) (n 0) by
    funext y
    exact fourierCoeffOn_slice_x_eq_quadraticFourierFactor
      hg hperX hperX' y hn₀]
  rw [fourierCoeffOn.const_mul]
  rw [← iteratedFourierCoeffOn_comm
    (partialDerivXX_contDiff_two hg).continuous n]

theorem iteratedFourierCoeffOn_eq_factor_x_factor_y
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hperY : ∀ x, g (x, 0) = g (x, 1))
    (hperY' : ∀ x, partialDerivY g (x, 0) = partialDerivY g (x, 1))
    (hperXYY : ∀ y, partialDerivYY g (0, y) = partialDerivYY g (1, y))
    (hperXYY' : ∀ y, partialDerivX (partialDerivYY g) (0, y) =
      partialDerivX (partialDerivYY g) (1, y))
    (n : Fin 2 → ℤ) (hn₀ : n 0 ≠ 0) (hn₁ : n 1 ≠ 0) :
    iteratedFourierCoeffOn (Function.curry g) n =
      quadraticFourierFactor (n 1) * quadraticFourierFactor (n 0) *
        iteratedFourierCoeffOn (Function.curry (partialDerivXXYY g)) n := by
  rw [iteratedFourierCoeffOn_eq_factor_y hg hperY hperY' n hn₁]
  rw [iteratedFourierCoeffOn_comm
    (partialDerivYY_contDiff_two hg).continuous n]
  rw [show (fun y => fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
      (fun x => partialDerivYY g (x, y)) (n 0)) =
      fun y => quadraticFourierFactor (n 0) *
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun x => partialDerivXXYY g (x, y)) (n 0) by
    funext y
    exact fourierCoeffOn_slice_x_partialDerivYY_eq_quadraticFourierFactor
      hg hperXYY hperXYY' y hn₀]
  rw [fourierCoeffOn.const_mul]
  rw [← iteratedFourierCoeffOn_comm
    (partialDerivXXYY_continuous hg) n]
  ring

/-- One-dimensional summable envelope accommodating the zero mode and the
quadratic integration-by-parts bound at every nonzero mode. -/
def integerFourierEnvelope (k : ℤ) : ℝ :=
  if k = 0 then 1 else (1 / Real.pi ^ 2) * integerUnitSlabEnvelope k

theorem integerFourierEnvelope_nonneg (k : ℤ) :
    0 ≤ integerFourierEnvelope k := by
  by_cases hk : k = 0
  · simp [integerFourierEnvelope, hk]
  · simp only [integerFourierEnvelope, hk, ↓reduceIte, integerUnitSlabEnvelope]
    positivity

theorem summable_integerFourierEnvelope :
    Summable integerFourierEnvelope := by
  have hbase : Summable (fun k : ℤ =>
      (1 / Real.pi ^ 2) * integerUnitSlabEnvelope k) :=
    summable_integerUnitSlabEnvelope.mul_left (1 / Real.pi ^ 2)
  apply hbase.congr_cofinite
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
  have hk0 : k ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hk
  simp only [integerFourierEnvelope, hk0, ↓reduceIte]

theorem summable_finTwo_integerFourierEnvelope_product :
    Summable (fun n : Fin 2 → ℤ =>
      integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1)) := by
  have hprod : Summable (fun p : ℤ × ℤ =>
      integerFourierEnvelope p.1 * integerFourierEnvelope p.2) :=
    summable_integerFourierEnvelope.mul_of_nonneg summable_integerFourierEnvelope
      integerFourierEnvelope_nonneg integerFourierEnvelope_nonneg
  have he := (finTwoArrowEquiv ℤ).summable_iff.mpr hprod
  apply he.congr
  intro n
  rfl

theorem norm_iteratedFourierCoeffOn_le_of_norm_le
    {q : ℝ → ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hq : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖q x y‖ ≤ B) (n : Fin 2 → ℤ) :
    ‖iteratedFourierCoeffOn q n‖ ≤ B := by
  unfold iteratedFourierCoeffOn
  apply norm_fourierCoeffOn_le_of_norm_le hB
  intro x hx
  apply norm_fourierCoeffOn_le_of_norm_le hB
  intro y hy
  exact hq x hx y hy

theorem norm_iteratedFourierCoeffOn_le_envelope
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g)
    (hperY : ∀ x, g (x, 0) = g (x, 1))
    (hperY' : ∀ x, partialDerivY g (x, 0) = partialDerivY g (x, 1))
    (hperX : ∀ y, g (0, y) = g (1, y))
    (hperX' : ∀ y, partialDerivX g (0, y) = partialDerivX g (1, y))
    (hperXYY : ∀ y, partialDerivYY g (0, y) = partialDerivYY g (1, y))
    (hperXYY' : ∀ y, partialDerivX (partialDerivYY g) (0, y) =
      partialDerivX (partialDerivYY g) (1, y))
    {B : ℝ} (hB : 0 ≤ B)
    (hgBound : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖g (x, y)‖ ≤ B)
    (hXXBound : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖partialDerivXX g (x, y)‖ ≤ B)
    (hYYBound : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖partialDerivYY g (x, y)‖ ≤ B)
    (hXXYYBound : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖partialDerivXXYY g (x, y)‖ ≤ B)
    (n : Fin 2 → ℤ) :
    ‖iteratedFourierCoeffOn (Function.curry g) n‖ ≤
      B * integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1) := by
  by_cases hn₀ : n 0 = 0
  · by_cases hn₁ : n 1 = 0
    · have hbase := norm_iteratedFourierCoeffOn_le_of_norm_le
        (q := Function.curry g) hB (by
          intro x hx y hy
          exact hgBound x hx y hy) n
      simpa [integerFourierEnvelope, hn₀, hn₁] using hbase
    · rw [iteratedFourierCoeffOn_eq_factor_y hg hperY hperY' n hn₁,
        norm_mul]
      have hfac : ‖quadraticFourierFactor (n 1)‖ ≤
          integerFourierEnvelope (n 1) := by
        simpa [integerFourierEnvelope, hn₁] using
          norm_quadraticFourierFactor_le_integerUnitSlabEnvelope hn₁
      have hcoeff := norm_iteratedFourierCoeffOn_le_of_norm_le
        (q := Function.curry (partialDerivYY g)) hB (by
          intro x hx y hy
          exact hYYBound x hx y hy) n
      have hmul := mul_le_mul hfac hcoeff (norm_nonneg _)
        (integerFourierEnvelope_nonneg (n 1))
      calc
        ‖quadraticFourierFactor (n 1)‖ *
            ‖iteratedFourierCoeffOn (Function.curry (partialDerivYY g)) n‖ ≤
          integerFourierEnvelope (n 1) * B := hmul
        _ = B * integerFourierEnvelope (n 0) *
            integerFourierEnvelope (n 1) := by
          simp [integerFourierEnvelope, hn₀, hn₁, mul_comm]
  · by_cases hn₁ : n 1 = 0
    · rw [iteratedFourierCoeffOn_eq_factor_x hg hperX hperX' n hn₀,
        norm_mul]
      have hfac : ‖quadraticFourierFactor (n 0)‖ ≤
          integerFourierEnvelope (n 0) := by
        simpa [integerFourierEnvelope, hn₀] using
          norm_quadraticFourierFactor_le_integerUnitSlabEnvelope hn₀
      have hcoeff := norm_iteratedFourierCoeffOn_le_of_norm_le
        (q := Function.curry (partialDerivXX g)) hB (by
          intro x hx y hy
          exact hXXBound x hx y hy) n
      have hmul := mul_le_mul hfac hcoeff (norm_nonneg _)
        (integerFourierEnvelope_nonneg (n 0))
      calc
        ‖quadraticFourierFactor (n 0)‖ *
            ‖iteratedFourierCoeffOn (Function.curry (partialDerivXX g)) n‖ ≤
          integerFourierEnvelope (n 0) * B := hmul
        _ = B * integerFourierEnvelope (n 0) *
            integerFourierEnvelope (n 1) := by
          simp [integerFourierEnvelope, hn₁, mul_comm]
    · rw [iteratedFourierCoeffOn_eq_factor_x_factor_y hg hperY hperY'
        hperXYY hperXYY' n hn₀ hn₁, norm_mul, norm_mul]
      have hfac₀ : ‖quadraticFourierFactor (n 0)‖ ≤
          integerFourierEnvelope (n 0) := by
        simpa [integerFourierEnvelope, hn₀] using
          norm_quadraticFourierFactor_le_integerUnitSlabEnvelope hn₀
      have hfac₁ : ‖quadraticFourierFactor (n 1)‖ ≤
          integerFourierEnvelope (n 1) := by
        simpa [integerFourierEnvelope, hn₁] using
          norm_quadraticFourierFactor_le_integerUnitSlabEnvelope hn₁
      have hfac : ‖quadraticFourierFactor (n 1)‖ *
          ‖quadraticFourierFactor (n 0)‖ ≤
          integerFourierEnvelope (n 1) * integerFourierEnvelope (n 0) :=
        mul_le_mul hfac₁ hfac₀ (norm_nonneg _)
          (integerFourierEnvelope_nonneg (n 1))
      have hcoeff := norm_iteratedFourierCoeffOn_le_of_norm_le
        (q := Function.curry (partialDerivXXYY g)) hB (by
          intro x hx y hy
          exact hXXYYBound x hx y hy) n
      have hmul := mul_le_mul hfac hcoeff (norm_nonneg _)
        (mul_nonneg (integerFourierEnvelope_nonneg (n 1))
          (integerFourierEnvelope_nonneg (n 0)))
      calc
        ‖quadraticFourierFactor (n 1)‖ *
              ‖quadraticFourierFactor (n 0)‖ *
            ‖iteratedFourierCoeffOn (Function.curry (partialDerivXXYY g)) n‖ ≤
          (integerFourierEnvelope (n 1) * integerFourierEnvelope (n 0)) * B := hmul
        _ = B * integerFourierEnvelope (n 0) *
            integerFourierEnvelope (n 1) := by ring

theorem summable_and_tsum_norm_le_of_finTwo_envelope
    {a : (Fin 2 → ℤ) → ℂ} {B : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ B * integerFourierEnvelope (n 0) *
      integerFourierEnvelope (n 1)) :
    Summable a ∧
      ∑' n, ‖a n‖ ≤ B * ∑' n : Fin 2 → ℤ,
        integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1) := by
  let E : (Fin 2 → ℤ) → ℝ := fun n =>
    integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1)
  have hE : Summable E := summable_finTwo_integerFourierEnvelope_product
  have hmajorant : Summable (fun n => B * E n) := hE.mul_left B
  have ha' : Summable a := hmajorant.of_norm_bounded (by
    intro n
    simpa only [E, mul_assoc] using ha n)
  refine ⟨ha', ?_⟩
  calc
    (∑' n, ‖a n‖) ≤ ∑' n, B * E n :=
      ha'.norm.tsum_le_tsum (fun n => by
        simpa only [E, mul_assoc] using ha n) hmajorant
    _ = B * ∑' n, E n := hE.tsum_mul_left B
    _ = B * ∑' n : Fin 2 → ℤ,
        integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1) := rfl

theorem norm_iteratedDeriv_two_mul_le
    {r s : ℝ → ℂ} (hr : ContDiff ℝ 2 r) (hs : ContDiff ℝ 2 s)
    {K M : ℝ} (hK : 0 ≤ K) (_hM : 0 ≤ M)
    (hrBound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i r x‖ ≤ K)
    (hsBound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i s x‖ ≤ M) :
    ‖iteratedDeriv 2 (fun t => r t * s t) x‖ ≤ 4 * K * M := by
  change ‖iteratedDeriv 2 (r * s) x‖ ≤ 4 * K * M
  rw [iteratedDeriv_mul hr.contDiffAt hs.contDiffAt]
  norm_num [Finset.sum_range_succ]
  have hr0 : ‖r x‖ ≤ K := by simpa using hrBound 0 (by norm_num)
  have hr1 : ‖deriv r x‖ ≤ K := by
    simpa only [iteratedDeriv_one] using hrBound 1 (by norm_num)
  have hr2 : ‖iteratedDeriv 2 r x‖ ≤ K := hrBound 2 le_rfl
  have hs0 : ‖s x‖ ≤ M := by simpa using hsBound 0 (by norm_num)
  have hs1 : ‖deriv s x‖ ≤ M := by
    simpa only [iteratedDeriv_one] using hsBound 1 (by norm_num)
  have hs2 : ‖iteratedDeriv 2 s x‖ ≤ M := hsBound 2 le_rfl
  have h02 : ‖r x‖ * ‖iteratedDeriv 2 s x‖ ≤ K * M :=
    mul_le_mul hr0 hs2 (norm_nonneg _) hK
  have h11 : ‖deriv r x‖ * ‖deriv s x‖ ≤ K * M :=
    mul_le_mul hr1 hs1 (norm_nonneg _) hK
  have h20 : ‖iteratedDeriv 2 r x‖ * ‖s x‖ ≤ K * M :=
    mul_le_mul hr2 hs0 (norm_nonneg _) hK
  calc
    ‖r x * iteratedDeriv 2 s x + 2 * deriv r x * deriv s x +
        iteratedDeriv 2 r x * s x‖ ≤
      ‖r x * iteratedDeriv 2 s x‖ + ‖2 * deriv r x * deriv s x‖ +
        ‖iteratedDeriv 2 r x * s x‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖r x‖ * ‖iteratedDeriv 2 s x‖ +
        2 * (‖deriv r x‖ * ‖deriv s x‖) +
          ‖iteratedDeriv 2 r x‖ * ‖s x‖ := by
      simp only [norm_mul, Complex.norm_two]
      ring
    _ ≤ 4 * K * M := by nlinarith

theorem periodThreeCutoffAmplitude_eq_cutoffC_mul
    (f : ℝ → ℝ → ℂ) (u v : ℝ) :
    periodThreeCutoffAmplitude f u v =
      periodThreeCutoffC u * (periodThreeCutoffC v * f u v) := by
  simp only [periodThreeCutoffAmplitude, periodThreeCutoffC]
  push_cast
  ring

theorem norm_iteratedDeriv_const_mul_le
    {s : ℝ → ℂ} {c : ℂ} {K M : ℝ} (hK : 0 ≤ K)
    (hc : ‖c‖ ≤ K)
    (hs : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i s x‖ ≤ M)
    (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedDeriv i (fun t => c * s t) x‖ ≤ K * M := by
  rw [iteratedDeriv_const_mul_field, norm_mul]
  exact mul_le_mul hc (hs i hi) (norm_nonneg _) hK

theorem norm_periodThreeCutoffAmplitude_le
    {f : ℝ → ℝ → ℂ} {M : NNReal}
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 2)
    (hv : v ∈ Icc (-1 : ℝ) 2) :
    ‖periodThreeCutoffAmplitude f u v‖ ≤
      periodThreeCutoffDerivativeBound ^ 2 * (M : ℝ) := by
  rw [periodThreeCutoffAmplitude_eq_cutoffC_mul, norm_mul, norm_mul]
  have hcu := norm_iteratedDeriv_periodThreeCutoffC_le 0 (by norm_num) u
  have hcv := norm_iteratedDeriv_periodThreeCutoffC_le 0 (by norm_num) v
  simp only [iteratedDeriv_zero] at hcu hcv
  have hf0 := hderiv 0 0 (by norm_num) hu hv
  simp only [iteratedDeriv_zero] at hf0
  have hK : 0 ≤ periodThreeCutoffDerivativeBound :=
    le_trans zero_le_one periodThreeCutoffDerivativeBound_one_le
  have hprod := mul_le_mul
    (mul_le_mul hcu hcv (norm_nonneg _) hK) hf0 (norm_nonneg _)
    (mul_nonneg hK hK)
  nlinarith

theorem norm_iteratedDeriv_two_periodThreeCutoffAmplitude_x_le
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    {M : NNReal}
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 2)
    (hv : v ∈ Icc (-1 : ℝ) 2) :
    ‖iteratedDeriv 2 (fun u' => periodThreeCutoffAmplitude f u' v) u‖ ≤
      4 * periodThreeCutoffDerivativeBound ^ 2 * (M : ℝ) := by
  let K := periodThreeCutoffDerivativeBound
  have hK : 0 ≤ K := le_trans zero_le_one periodThreeCutoffDerivativeBound_one_le
  have hfTwo : ContDiff ℝ 2 (Function.uncurry f) := hf.of_le (by norm_num)
  have hfSlice : ContDiff ℝ 2 (fun u' : ℝ => f u' v) :=
    hfTwo.comp (contDiff_id.prodMk contDiff_const)
  have hs : ContDiff ℝ 2 (fun u' : ℝ =>
      periodThreeCutoffC v * f u' v) := contDiff_const.mul hfSlice
  have hsBound : ∀ i : ℕ, i ≤ 2 →
      ‖iteratedDeriv i (fun u' : ℝ =>
        periodThreeCutoffC v * f u' v) u‖ ≤ K * (M : ℝ) := by
    intro i hi
    apply norm_iteratedDeriv_const_mul_le hK
    · exact norm_iteratedDeriv_periodThreeCutoffC_le 0 (by norm_num) v
    · intro j hj
      have h := hderiv j 0 (by omega) hu hv
      simpa only [iteratedDeriv_zero] using h
    · exact hi
  rw [show (fun u' => periodThreeCutoffAmplitude f u' v) =
      fun u' => periodThreeCutoffC u' *
        (periodThreeCutoffC v * f u' v) by
    funext u'
    exact periodThreeCutoffAmplitude_eq_cutoffC_mul f u' v]
  have h := norm_iteratedDeriv_two_mul_le
    (periodThreeCutoffC_contDiff 2) hs hK (mul_nonneg hK M.coe_nonneg)
    (fun i hi => norm_iteratedDeriv_periodThreeCutoffC_le i hi u)
    hsBound
  dsimp only [K] at h
  convert h using 1
  all_goals ring

theorem norm_iteratedDeriv_two_periodThreeCutoffAmplitude_y_le
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    {M : NNReal}
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 2)
    (hv : v ∈ Icc (-1 : ℝ) 2) :
    ‖iteratedDeriv 2 (fun v' => periodThreeCutoffAmplitude f u v') v‖ ≤
      4 * periodThreeCutoffDerivativeBound ^ 2 * (M : ℝ) := by
  let K := periodThreeCutoffDerivativeBound
  have hK : 0 ≤ K := le_trans zero_le_one periodThreeCutoffDerivativeBound_one_le
  have hfTwo : ContDiff ℝ 2 (Function.uncurry f) := hf.of_le (by norm_num)
  have hfSlice : ContDiff ℝ 2 (fun v' : ℝ => f u v') :=
    hfTwo.comp (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ 2 (fun v' : ℝ =>
      periodThreeCutoffC u * f u v') := contDiff_const.mul hfSlice
  have hsBound : ∀ i : ℕ, i ≤ 2 →
      ‖iteratedDeriv i (fun v' : ℝ =>
        periodThreeCutoffC u * f u v') v‖ ≤ K * (M : ℝ) := by
    intro i hi
    apply norm_iteratedDeriv_const_mul_le hK
    · exact norm_iteratedDeriv_periodThreeCutoffC_le 0 (by norm_num) u
    · intro j hj
      have h := hderiv 0 j (by omega) hu hv
      simpa only [iteratedDeriv_zero] using h
    · exact hi
  rw [show (fun v' => periodThreeCutoffAmplitude f u v') =
      fun v' => periodThreeCutoffC v' *
        (periodThreeCutoffC u * f u v') by
    funext v'
    rw [periodThreeCutoffAmplitude_eq_cutoffC_mul]
    ring]
  have h := norm_iteratedDeriv_two_mul_le
    (periodThreeCutoffC_contDiff 2) hs hK (mul_nonneg hK M.coe_nonneg)
    (fun i hi => norm_iteratedDeriv_periodThreeCutoffC_le i hi v)
    hsBound
  simpa only [K, pow_two, mul_assoc] using h

theorem iteratedDeriv_one_slice_y_eq_partialDerivY
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 4 g) (x y : ℝ) :
    iteratedDeriv 1 (fun y' => g (x, y')) y = partialDerivY g (x, y) := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_slice_y (hg.differentiable (by norm_num)) x y).deriv

/-- Leibniz expansion of the second `v` derivative after inserting the cutoff. -/
def periodThreeCutoffYSecondCore (f : ℝ → ℝ → ℂ) (v u : ℝ) : ℂ :=
  periodThreeCutoffC v * iteratedDeriv 2 (fun v' => f u v') v +
    (2 : ℂ) * deriv periodThreeCutoffC v *
      iteratedDeriv 1 (fun v' => f u v') v +
    iteratedDeriv 2 periodThreeCutoffC v * f u v

theorem periodThreeCutoffYSecondCore_eq
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (u v : ℝ) :
    iteratedDeriv 2 (fun v' => periodThreeCutoffC v' * f u v') v =
      periodThreeCutoffYSecondCore f v u := by
  have hfSlice : ContDiff ℝ 2 (fun v' : ℝ => f u v') :=
    (hf.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id)
  change iteratedDeriv 2 (periodThreeCutoffC * fun v' => f u v') v = _
  rw [iteratedDeriv_mul (periodThreeCutoffC_contDiff 2).contDiffAt
    hfSlice.contDiffAt]
  norm_num [Finset.sum_range_succ]
  simp only [periodThreeCutoffYSecondCore, iteratedDeriv_one]

theorem periodThreeCutoffYSecondCore_contDiff_two
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (v : ℝ) : ContDiff ℝ 2 (periodThreeCutoffYSecondCore f v) := by
  have h0 : ContDiff ℝ 2 (fun u : ℝ => f u v) :=
    (hf.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have h1 : ContDiff ℝ 2
      (fun u : ℝ => iteratedDeriv 1 (fun v' => f u v') v) := by
    rw [show (fun u : ℝ => iteratedDeriv 1 (fun v' => f u v') v) =
        fun u => partialDerivY (Function.uncurry f) (u, v) by
      funext u
      exact iteratedDeriv_one_slice_y_eq_partialDerivY hf u v]
    exact (partialDerivY_contDiff_three hf).of_le (by norm_num) |>.comp
      (contDiff_id.prodMk contDiff_const)
  have h2 : ContDiff ℝ 2
      (fun u : ℝ => iteratedDeriv 2 (fun v' => f u v') v) := by
    rw [show (fun u : ℝ => iteratedDeriv 2 (fun v' => f u v') v) =
        fun u => partialDerivYY (Function.uncurry f) (u, v) by
      funext u
      exact iteratedDeriv_two_slice_y_eq_partialDerivYY hf u v]
    exact (partialDerivYY_contDiff_two hf).comp
      (contDiff_id.prodMk contDiff_const)
  unfold periodThreeCutoffYSecondCore
  exact ((contDiff_const.mul h2).add
    ((contDiff_const.mul contDiff_const).mul h1)).add
      (contDiff_const.mul h0)

theorem norm_iteratedDeriv_periodThreeCutoffYSecondCore_le
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    {M : NNReal}
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 2)
    (hv : v ∈ Icc (-1 : ℝ) 2) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedDeriv i (periodThreeCutoffYSecondCore f v) u‖ ≤
      4 * periodThreeCutoffDerivativeBound * (M : ℝ) := by
  let K := periodThreeCutoffDerivativeBound
  have hK : 0 ≤ K := le_trans zero_le_one periodThreeCutoffDerivativeBound_one_le
  have h0 : ContDiff ℝ 2 (fun u : ℝ => f u v) :=
    (hf.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have h1 : ContDiff ℝ 2
      (fun u : ℝ => iteratedDeriv 1 (fun v' => f u v') v) := by
    rw [show (fun u : ℝ => iteratedDeriv 1 (fun v' => f u v') v) =
        fun u => partialDerivY (Function.uncurry f) (u, v) by
      funext u
      exact iteratedDeriv_one_slice_y_eq_partialDerivY hf u v]
    exact (partialDerivY_contDiff_three hf).of_le (by norm_num) |>.comp
      (contDiff_id.prodMk contDiff_const)
  have h2 : ContDiff ℝ 2
      (fun u : ℝ => iteratedDeriv 2 (fun v' => f u v') v) := by
    rw [show (fun u : ℝ => iteratedDeriv 2 (fun v' => f u v') v) =
        fun u => partialDerivYY (Function.uncurry f) (u, v) by
      funext u
      exact iteratedDeriv_two_slice_y_eq_partialDerivYY hf u v]
    exact (partialDerivYY_contDiff_two hf).comp
      (contDiff_id.prodMk contDiff_const)
  let A : ℝ → ℂ := fun u =>
    periodThreeCutoffC v * iteratedDeriv 2 (fun v' => f u v') v
  let B : ℝ → ℂ := fun u =>
    (2 : ℂ) * deriv periodThreeCutoffC v *
      iteratedDeriv 1 (fun v' => f u v') v
  let C : ℝ → ℂ := fun u =>
    iteratedDeriv 2 periodThreeCutoffC v * f u v
  have hA : ContDiff ℝ 2 A := contDiff_const.mul h2
  have hB : ContDiff ℝ 2 B := (contDiff_const.mul contDiff_const).mul h1
  have hC : ContDiff ℝ 2 C := contDiff_const.mul h0
  have hi' : (i : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hi
  change ‖iteratedDeriv i (fun u => A u + B u + C u) u‖ ≤ _
  rw [iteratedDeriv_fun_add ((hA.add hB).of_le hi').contDiffAt
      (hC.of_le hi').contDiffAt,
    iteratedDeriv_fun_add (hA.of_le hi').contDiffAt (hB.of_le hi').contDiffAt]
  simp only [A, B, C, iteratedDeriv_const_mul_field]
  have hc0 := norm_iteratedDeriv_periodThreeCutoffC_le 0 (by norm_num) v
  have hc1 := norm_iteratedDeriv_periodThreeCutoffC_le 1 (by norm_num) v
  have hc2 := norm_iteratedDeriv_periodThreeCutoffC_le 2 (by norm_num) v
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hc0 hc1
  have hf0 := hderiv i 0 (by omega) hu hv
  have hf1 := hderiv i 1 (by omega) hu hv
  have hf2 := hderiv i 2 (by omega) hu hv
  simp only [iteratedDeriv_zero] at hf0
  have hA' : ‖periodThreeCutoffC v *
      iteratedDeriv i (fun u => iteratedDeriv 2 (fun v' => f u v') v) u‖ ≤
      K * (M : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul hc0 hf2 (norm_nonneg _) hK
  have hB' : ‖(2 : ℂ) * deriv periodThreeCutoffC v *
      iteratedDeriv i (fun u => iteratedDeriv 1 (fun v' => f u v') v) u‖ ≤
      2 * K * (M : ℝ) := by
    simp only [norm_mul, Complex.norm_two]
    have := mul_le_mul hc1 hf1 (norm_nonneg _) hK
    nlinarith
  have hC' : ‖iteratedDeriv 2 periodThreeCutoffC v *
      iteratedDeriv i (fun u => f u v) u‖ ≤ K * (M : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul hc2 hf0 (norm_nonneg _) hK
  calc
    ‖periodThreeCutoffC v *
          iteratedDeriv i (fun u => iteratedDeriv 2 (fun v' => f u v') v) u +
        (2 : ℂ) * deriv periodThreeCutoffC v *
          iteratedDeriv i (fun u => iteratedDeriv 1 (fun v' => f u v') v) u +
        iteratedDeriv 2 periodThreeCutoffC v *
          iteratedDeriv i (fun u => f u v) u‖ ≤
      ‖periodThreeCutoffC v *
          iteratedDeriv i (fun u => iteratedDeriv 2 (fun v' => f u v') v) u‖ +
        ‖(2 : ℂ) * deriv periodThreeCutoffC v *
          iteratedDeriv i (fun u => iteratedDeriv 1 (fun v' => f u v') v) u‖ +
        ‖iteratedDeriv 2 periodThreeCutoffC v *
          iteratedDeriv i (fun u => f u v) u‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 * periodThreeCutoffDerivativeBound * (M : ℝ) := by
      dsimp only [K] at hA' hB' hC'
      nlinarith

theorem norm_iteratedDeriv_two_two_periodThreeCutoffAmplitude_le
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    {M : NNReal}
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 2)
    (hv : v ∈ Icc (-1 : ℝ) 2) :
    ‖iteratedDeriv 2 (fun u' =>
        iteratedDeriv 2 (fun v' => periodThreeCutoffAmplitude f u' v') v) u‖ ≤
      16 * periodThreeCutoffDerivativeBound ^ 2 * (M : ℝ) := by
  let K := periodThreeCutoffDerivativeBound
  have hK : 0 ≤ K := le_trans zero_le_one periodThreeCutoffDerivativeBound_one_le
  have hcore : ContDiff ℝ 2 (periodThreeCutoffYSecondCore f v) :=
    periodThreeCutoffYSecondCore_contDiff_two hf v
  have hcoreBound : ∀ i : ℕ, i ≤ 2 →
      ‖iteratedDeriv i (periodThreeCutoffYSecondCore f v) u‖ ≤
        4 * K * (M : ℝ) := by
    intro i hi
    exact norm_iteratedDeriv_periodThreeCutoffYSecondCore_le
      hf hderiv hu hv i hi
  have heq (u' : ℝ) :
      iteratedDeriv 2 (fun v' => periodThreeCutoffAmplitude f u' v') v =
        periodThreeCutoffC u' * periodThreeCutoffYSecondCore f v u' := by
    rw [show (fun v' => periodThreeCutoffAmplitude f u' v') =
        fun v' => periodThreeCutoffC u' *
          (periodThreeCutoffC v' * f u' v') by
      funext v'
      exact periodThreeCutoffAmplitude_eq_cutoffC_mul f u' v']
    rw [iteratedDeriv_const_mul_field, periodThreeCutoffYSecondCore_eq hf]
  rw [show (fun u' =>
      iteratedDeriv 2 (fun v' => periodThreeCutoffAmplitude f u' v') v) =
      fun u' => periodThreeCutoffC u' *
        periodThreeCutoffYSecondCore f v u' by
    funext u'
    exact heq u']
  have h := norm_iteratedDeriv_two_mul_le
    (periodThreeCutoffC_contDiff 2) hcore hK
    (mul_nonneg (mul_nonneg (by norm_num) hK) M.coe_nonneg)
    (fun i hi => norm_iteratedDeriv_periodThreeCutoffC_le i hi u)
    hcoreBound
  dsimp only [K] at h
  convert h using 1
  all_goals ring

theorem partialDerivXX_periodThreeScaledCutoffAmplitude
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (x y : ℝ) :
    partialDerivXX (periodThreeScaledCutoffAmplitude f) (x, y) =
      (3 : ℝ) ^ 2 • iteratedDeriv 2
        (fun u => periodThreeCutoffAmplitude f u (3 * y - 1)) (3 * x - 1) := by
  rw [← iteratedDeriv_two_slice_x_eq_partialDerivXX
    (periodThreeScaledCutoffAmplitude_contDiff hf) x y]
  change iteratedDeriv 2
      (fun x' => periodThreeCutoffAmplitude f (3 * x' - 1) (3 * y - 1)) x = _
  exact iteratedDeriv_comp_three_sub_one 2
    ((periodThreeCutoffAmplitude_contDiff hf).of_le (by norm_num) |>.comp
      (contDiff_id.prodMk contDiff_const)) x

theorem partialDerivYY_periodThreeScaledCutoffAmplitude
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (x y : ℝ) :
    partialDerivYY (periodThreeScaledCutoffAmplitude f) (x, y) =
      (3 : ℝ) ^ 2 • iteratedDeriv 2
        (fun v => periodThreeCutoffAmplitude f (3 * x - 1) v) (3 * y - 1) := by
  rw [← iteratedDeriv_two_slice_y_eq_partialDerivYY
    (periodThreeScaledCutoffAmplitude_contDiff hf) x y]
  change iteratedDeriv 2
      (fun y' => periodThreeCutoffAmplitude f (3 * x - 1) (3 * y' - 1)) y = _
  exact iteratedDeriv_comp_three_sub_one 2
    ((periodThreeCutoffAmplitude_contDiff hf).of_le (by norm_num) |>.comp
      (contDiff_const.prodMk contDiff_id)) y

theorem partialDerivXXYY_periodThreeScaledCutoffAmplitude
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (x y : ℝ) :
    partialDerivXXYY (periodThreeScaledCutoffAmplitude f) (x, y) =
      (3 : ℝ) ^ 2 • ((3 : ℝ) ^ 2 •
        iteratedDeriv 2 (fun u =>
          iteratedDeriv 2 (fun v => periodThreeCutoffAmplitude f u v)
            (3 * y - 1)) (3 * x - 1)) := by
  let A : ℝ → ℝ → ℂ := periodThreeCutoffAmplitude f
  let T : ℝ → ℂ := fun u =>
    iteratedDeriv 2 (fun v => A u v) (3 * y - 1)
  have hA : ContDiff ℝ 4 (Function.uncurry A) :=
    periodThreeCutoffAmplitude_contDiff hf
  have hT : ContDiff ℝ 2 T := by
    rw [show T = fun u => partialDerivYY (Function.uncurry A)
        (u, 3 * y - 1) by
      funext u
      exact iteratedDeriv_two_slice_y_eq_partialDerivYY hA u (3 * y - 1)]
    exact (partialDerivYY_contDiff_two hA).comp
      (contDiff_id.prodMk contDiff_const)
  rw [← iteratedDeriv_two_slice_x_partialDerivYY_eq_partialDerivXXYY
    (periodThreeScaledCutoffAmplitude_contDiff hf) x y]
  have hYY (x' : ℝ) :
      partialDerivYY (periodThreeScaledCutoffAmplitude f) (x', y) =
        (3 : ℝ) ^ 2 • T (3 * x' - 1) := by
    rw [partialDerivYY_periodThreeScaledCutoffAmplitude hf]
  rw [show (fun x' => partialDerivYY
      (periodThreeScaledCutoffAmplitude f) (x', y)) =
      fun x' => (3 : ℝ) ^ 2 • T (3 * x' - 1) by
    funext x'
    exact hYY x']
  rw [iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_comp_three_sub_one 2 hT]

/-- The fixed loss from the cutoff's Leibniz rule and the period-three
coordinate change. -/
noncomputable def periodThreeC4DerivativeScale : ℝ :=
  1296 * periodThreeCutoffDerivativeBound ^ 2

theorem periodThreeC4DerivativeScale_nonneg :
    0 ≤ periodThreeC4DerivativeScale := by
  unfold periodThreeC4DerivativeScale
  positivity

theorem norm_periodThreeScaledCutoffAmplitude_derivatives_le
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (M : NNReal)
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖periodThreeScaledCutoffAmplitude f (x, y)‖ ≤
        periodThreeC4DerivativeScale * (M : ℝ) ∧
      ‖partialDerivXX (periodThreeScaledCutoffAmplitude f) (x, y)‖ ≤
        periodThreeC4DerivativeScale * (M : ℝ) ∧
      ‖partialDerivYY (periodThreeScaledCutoffAmplitude f) (x, y)‖ ≤
        periodThreeC4DerivativeScale * (M : ℝ) ∧
      ‖partialDerivXXYY (periodThreeScaledCutoffAmplitude f) (x, y)‖ ≤
        periodThreeC4DerivativeScale * (M : ℝ) := by
  have hu : 3 * x - 1 ∈ Icc (-1 : ℝ) 2 := by
    constructor <;> linarith [hx.1, hx.2]
  have hv : 3 * y - 1 ∈ Icc (-1 : ℝ) 2 := by
    constructor <;> linarith [hy.1, hy.2]
  have hK : 1 ≤ periodThreeCutoffDerivativeBound :=
    periodThreeCutoffDerivativeBound_one_le
  have hM : 0 ≤ (M : ℝ) := M.coe_nonneg
  have h0 := norm_periodThreeCutoffAmplitude_le hderiv hu hv
  have hxx := norm_iteratedDeriv_two_periodThreeCutoffAmplitude_x_le
    hf hderiv hu hv
  have hyy := norm_iteratedDeriv_two_periodThreeCutoffAmplitude_y_le
    hf hderiv hu hv
  have hxxyy := norm_iteratedDeriv_two_two_periodThreeCutoffAmplitude_le
    hf hderiv hu hv
  constructor
  · change ‖periodThreeCutoffAmplitude f (3 * x - 1) (3 * y - 1)‖ ≤ _
    unfold periodThreeC4DerivativeScale
    nlinarith
  constructor
  · rw [partialDerivXX_periodThreeScaledCutoffAmplitude hf, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ 2)]
    unfold periodThreeC4DerivativeScale
    nlinarith
  constructor
  · rw [partialDerivYY_periodThreeScaledCutoffAmplitude hf, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ 2)]
    unfold periodThreeC4DerivativeScale
    nlinarith
  · rw [partialDerivXXYY_periodThreeScaledCutoffAmplitude hf,
      norm_smul, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ 2)]
    unfold periodThreeC4DerivativeScale
    nlinarith

theorem mFourierCoeff_periodThreeTorusExtensionC
    (f : ℝ → ℝ → ℂ) (hf : ContDiff ℝ 4 (Function.uncurry f))
    (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (periodThreeTorusExtensionC f hf) n =
      iteratedFourierCoeffOn
        (fun x y => periodThreeCutoffAmplitude f (3 * x - 1) (3 * y - 1)) n := by
  rw [mFourierCoeff_finTwo_eq_iterated]
  let H : ℝ → ℝ → ℂ := fun x y =>
    periodThreeCutoffAmplitude f (3 * x - 1) (3 * y - 1)
  let K : ℝ → UnitAddCircle → ℂ := fun x => AddCircle.liftIco 1 0 (H x)
  have hslice (x : UnitAddCircle) :
      fourierCoeff
          (fun y : UnitAddCircle => periodThreeTorusExtensionC f hf
            (unitAddTorusPair x y)) (n 1) =
        AddCircle.liftIco 1 0 (fun r => fourierCoeff (K r) (n 1)) x := by
    change fourierCoeff (AddCircle.liftIco 1 0 K x) (n 1) =
      AddCircle.liftIco 1 0 (fun r => fourierCoeff (K r) (n 1)) x
    exact (AddCircle.liftIco_comp_apply (p := (1 : ℝ))
      (a := (0 : ℝ)) (f := K) (g := fun q => fourierCoeff q (n 1)) (x := x)).symm
  change fourierCoeff
      (fun x : UnitAddCircle => fourierCoeff
        (fun y : UnitAddCircle => periodThreeTorusExtensionC f hf
          (unitAddTorusPair x y)) (n 1)) (n 0) = _
  rw [show (fun x : UnitAddCircle => fourierCoeff
      (fun y : UnitAddCircle => periodThreeTorusExtensionC f hf
        (unitAddTorusPair x y)) (n 1)) =
      AddCircle.liftIco 1 0 (fun r => fourierCoeff (K r) (n 1)) by
    funext x
    exact hslice x]
  rw [fourierCoeff_liftIco_eq]
  unfold iteratedFourierCoeffOn
  simp only [K]
  simp_rw [fourierCoeff_liftIco_eq]
  simp only [H]
  congr
  · norm_num
  · funext x
    congr
    norm_num

theorem norm_mFourierCoeff_periodThreeTorusExtensionC_le_envelope
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 4 (Function.uncurry f))
    (M : NNReal)
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ))
    (n : Fin 2 → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (periodThreeTorusExtensionC f hf) n‖ ≤
      (periodThreeC4DerivativeScale * (M : ℝ)) *
        integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1) := by
  rw [mFourierCoeff_periodThreeTorusExtensionC]
  let g := periodThreeScaledCutoffAmplitude f
  have hbounds (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :=
    norm_periodThreeScaledCutoffAmplitude_derivatives_le hf M hderiv hx hy
  have h := norm_iteratedFourierCoeffOn_le_envelope
    (periodThreeScaledCutoffAmplitude_contDiff hf)
    (periodThreeScaledCutoffAmplitude_periodic_y f)
    (periodThreeScaledCutoffAmplitude_partialDerivY_periodic f)
    (periodThreeScaledCutoffAmplitude_periodic_x f)
    (periodThreeScaledCutoffAmplitude_partialDerivX_periodic f)
    (periodThreeScaledCutoffAmplitude_partialDerivYY_periodic_x f)
    (periodThreeScaledCutoffAmplitude_partialDerivXYY_periodic_x f)
    (mul_nonneg periodThreeC4DerivativeScale_nonneg M.coe_nonneg)
    (fun x hx y hy => (hbounds x hx y hy).1)
    (fun x hx y hy => (hbounds x hx y hy).2.1)
    (fun x hx y hy => (hbounds x hx y hy).2.2.1)
    (fun x hx y hy => (hbounds x hx y hy).2.2.2) n
  change ‖iteratedFourierCoeffOn
    (Function.curry (periodThreeScaledCutoffAmplitude f)) n‖ ≤ _
  exact h

/-- Total mass of the fixed product Fourier envelope on `ℤ²`. -/
noncomputable def periodThreeFourierEnvelopeMass : ℝ :=
  ∑' n : Fin 2 → ℤ,
    integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1)

theorem periodThreeFourierEnvelopeMass_nonneg :
    0 ≤ periodThreeFourierEnvelopeMass := by
  unfold periodThreeFourierEnvelopeMass
  exact tsum_nonneg fun n => mul_nonneg
    (integerFourierEnvelope_nonneg (n 0))
    (integerFourierEnvelope_nonneg (n 1))

/-- Universal constant for the fixed period-three `C⁴` extension. -/
noncomputable def periodThreeC4FourierL1Constant : NNReal :=
  ⟨1296 * periodThreeCutoffDerivativeBound ^ 2 *
      periodThreeFourierEnvelopeMass,
    mul_nonneg periodThreeC4DerivativeScale_nonneg
      periodThreeFourierEnvelopeMass_nonneg⟩

theorem periodThreeC4FourierL1Constant_coe :
    (periodThreeC4FourierL1Constant : ℝ) =
      periodThreeC4DerivativeScale * periodThreeFourierEnvelopeMass := by
  rfl

/-- A `C⁴` amplitude on the physical square has a fixed period-three torus
extension with absolutely summable Fourier coefficients and a quantitative
`ℓ1` bound. -/
theorem exists_periodThreeTorusExtension_with_mFourierCoeff_l1_bound
    (f : ℝ → ℝ → ℂ)
    (hf : ContDiff ℝ 4 (Function.uncurry f))
    (M : NNReal)
    (hderiv : ∀ (a b : ℕ), a + b ≤ 4 →
      ∀ {u v : ℝ}, u ∈ Icc (-1 : ℝ) 2 →
      v ∈ Icc (-1 : ℝ) 2 →
      ‖iteratedDeriv a (fun u' =>
          iteratedDeriv b (fun v' => f u' v') v) u‖ ≤ (M : ℝ)) :
    ∃ F : C(UnitAddTorus (Fin 2), ℂ),
      (∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
        v ∈ Icc (0 : ℝ) 1 →
        F (unitAddTorusPair (periodThreeTorusPoint u)
          (periodThreeTorusPoint v)) = f u v) ∧
      Summable (fun n : Fin 2 → ℤ =>
        ‖UnitAddTorus.mFourierCoeff F n‖) ∧
      Summable (UnitAddTorus.mFourierCoeff F) ∧
      (∑' n : Fin 2 → ℤ, ‖UnitAddTorus.mFourierCoeff F n‖) ≤
        (periodThreeC4FourierL1Constant : ℝ) * (M : ℝ) := by
  let F := periodThreeTorusExtensionC f hf
  have hcoeff : ∀ n : Fin 2 → ℤ,
      ‖UnitAddTorus.mFourierCoeff F n‖ ≤
        (periodThreeC4DerivativeScale * (M : ℝ)) *
          integerFourierEnvelope (n 0) * integerFourierEnvelope (n 1) := by
    intro n
    exact norm_mFourierCoeff_periodThreeTorusExtensionC_le_envelope
      hf M hderiv n
  have hsum := summable_and_tsum_norm_le_of_finTwo_envelope hcoeff
  refine ⟨F, ?_, hsum.1.norm, hsum.1, ?_⟩
  · intro u v hu hv
    exact periodThreeTorusExtensionC_apply_physical hf hu hv
  · calc
      (∑' n : Fin 2 → ℤ, ‖UnitAddTorus.mFourierCoeff F n‖) ≤
          (periodThreeC4DerivativeScale * (M : ℝ)) *
            periodThreeFourierEnvelopeMass := by
        simpa only [periodThreeFourierEnvelopeMass] using hsum.2
      _ = (periodThreeC4FourierL1Constant : ℝ) * (M : ℝ) := by
        rw [periodThreeC4FourierL1Constant_coe]
        ring

end

end MeyerGeneralProblem
