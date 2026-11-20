module

public import MeyerGeneralProblem.Cardinal.Adaptive.PhaseAvoidance
public import MeyerGeneralProblem.Distribution.DiscreteSupportCounting

@[expose] public section

/-!
# Translation of support counting measures

The counting measure has the same translation covariance as the
original distribution. A discrete support bound also gives a local
mass bound for the detector, irrespective of jet order or coefficients.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Metric Set
open scoped ENNReal Topology

private theorem isVanishingOn_translation_iff (a : ℝ) (T : TemperedDistribution ℝ ℂ)
    (O : Set ℝ) :
    IsVanishingOn (combDistributionTranslation a T) O ↔
      IsVanishingOn T ((fun x : ℝ => a + x) ⁻¹' O) := by
  constructor
  · intro h f hf
    have hS : tsupport (combSchwartzTranslation (-a) f) ⊆ O := by
      rw [translated_test_tsupport]
      intro x hx
      have hx' := hf hx
      change a + (-a + x) ∈ O at hx'
      simpa only [add_neg_cancel_left] using hx'
    have h₀ := h (combSchwartzTranslation (-a) f) hS
    change T (combSchwartzTranslation a (combSchwartzTranslation (-a) f)) = 0 at h₀
    have hInv : combSchwartzTranslation a (combSchwartzTranslation (-a) f) = f := by
      ext x
      rw [combSchwartzTranslation_apply, combSchwartzTranslation_apply, neg_add_cancel_left]
    simpa only [hInv] using h₀
  · intro h f hf
    change T (combSchwartzTranslation a f) = 0
    exact h _ (by rw [translated_test_tsupport]; exact preimage_mono hf)

/-- Original distributional support is pushed forward under translation. -/
theorem dsupport_combDistributionTranslation (a : ℝ) (T : TemperedDistribution ℝ ℂ) :
    dsupport (combDistributionTranslation a T) = (fun x : ℝ => a + x) '' dsupport T := by
  apply Set.ext
  intro x
  have hImage : x ∈ (fun y : ℝ => a + y) '' dsupport T ↔ -a + x ∈ dsupport T := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [neg_add_cancel_left]
    · intro hx
      exact ⟨-a + x, hx, add_neg_cancel_left a x⟩
  rw [hImage, ← not_iff_not,
    notMem_dsupport_iff x, notMem_dsupport_iff (-a + x)]
  constructor
  · rintro ⟨O, hVan, hO, hxO⟩
    refine ⟨_, (isVanishingOn_translation_iff a T O).mp hVan,
      hO.preimage (continuous_const.add continuous_id), ?_⟩
    change a + (-a + x) ∈ O
    rwa [add_neg_cancel_left]
  · rintro ⟨O, hVan, hO, hxO⟩
    refine ⟨(fun y : ℝ => -a + y) ⁻¹' O, ?_,
      hO.preimage (continuous_const.add continuous_id), hxO⟩
    apply (isVanishingOn_translation_iff a T _).mpr
    have hPre : (fun y : ℝ => a + y) ⁻¹' ((fun y : ℝ => -a + y) ⁻¹' O) = O := by
      ext y
      change -a + (a + y) ∈ O ↔ y ∈ O
      rw [neg_add_cancel_left]
    rwa [hPre]

/-- Counting each actual support site once commutes with translation. -/
theorem discreteSupportCount_combDistributionTranslation (a : ℝ)
    (T : TemperedDistribution ℝ ℂ) :
    discreteSupportCount (combDistributionTranslation a T) =
      Measure.map (fun x : ℝ => a + x) (discreteSupportCount T) := by
  let e := Homeomorph.addLeft a
  apply Measure.ext
  intro B hB
  change discreteSupportCount (combDistributionTranslation a T) B =
    Measure.map e (discreteSupportCount T) B
  have hMeas : Measurable e := e.continuous.measurable
  have hTS : dsupport (combDistributionTranslation a T) = e '' dsupport T :=
    dsupport_combDistributionTranslation a T
  rw [Measure.map_apply hMeas hB, discreteSupportCount, discreteSupportCount,
    Measure.restrict_apply hB, Measure.restrict_apply (hMeas hB), hTS]
  have hImage : MeasurableSet (e '' dsupport T) :=
    e.toMeasurableEquiv.measurableSet_image.mpr isClosed_dsupport.measurableSet
  rw [Measure.count_apply (hB.inter hImage),
    Measure.count_apply ((hMeas hB).inter isClosed_dsupport.measurableSet)]
  have he : e '' (e ⁻¹' B ∩ dsupport T) = B ∩ e '' dsupport T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.1, x, hx.2, rfl⟩
    · rintro ⟨hyB, x, hx, rfl⟩
      exact ⟨x, ⟨hyB, hx⟩, rfl⟩
  rw [← he, e.injective.encard_image]

/-- Any uniform original unit-window count bounds the detector mass
in each half-open unit window, including at collision parameters. -/
theorem discreteSupportCount_unit_window_le (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ t : ℝ, (S.carrier ∩ Ico t (t + 1)).ncard ≤ K) (t : ℝ) :
    discreteSupportCount T (Ico t (t + 1)) ≤ (K : ℝ≥0∞) := by
  have hSub := inter_subset_inter_left (Ico t (t + 1))
    (dsupport_subset_of_discrete_support S T hT)
  have hFinite := S.finite_inter_Ico t (t + 1)
  rw [discreteSupportCount_apply_of_finite T measurableSet_Ico (hFinite.subset hSub)]
  exact_mod_cast (Set.ncard_le_ncard hSub hFinite).trans (hCount t)

/-- A nonzero distribution on a locally finite carrier has a nonzero
counting measure of its actual support. -/
theorem discreteSupportCount_ne_zero (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    (hNonzero : T ≠ 0) : discreteSupportCount T ≠ 0 := by
  intro hMeasure
  have hEmpty : dsupport T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hOne : discreteSupportCount T {x} = 1 := by
      rw [discreteSupportCount, Measure.restrict_apply (measurableSet_singleton x),
        singleton_inter_of_mem hx]
      simp
    simp [hMeasure] at hOne
  apply hNonzero
  ext f
  have hCompact (n : ℕ) : T (compactSchwartzApproximation n f) = 0 := by
    have hSupp := distributionSupportedOn_dsupport_of_discrete_support S T hT
    rw [hEmpty] at hSupp
    exact hSupp _ (compactSchwartzApproximation_hasCompactSupport n f) (by simp)
  have hLim := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hZero : Tendsto (fun n : ℕ => T (compactSchwartzApproximation n f)) atTop (𝓝 0) := by
    simpa only [hCompact] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hLim hZero

end
end MeyerGeneralProblem
