module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPhaseDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Haar mean of the real Cayley phase density
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory MeasureTheory.Measure Set UnitAddTorus
open scoped ENNReal NNReal Topology

private theorem aemeasurable_prod_of_ae_continuous_sections
    {Θ E : Type*} [MeasurableSpace Θ] {μ : Measure Θ}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Θ → ℝ → E) (hCont : ∀ᵐ θ ∂μ, Continuous (f θ))
    (hMeas : ∀ x, AEMeasurable (fun θ => f θ x) μ) :
    AEMeasurable (fun p : Θ × ℝ => f p.1 p.2) (μ.prod volume) := by
  let hId : StronglyMeasurable (id : ℝ → ℝ) := stronglyMeasurable_id
  let c := hId.approx
  let g (n : ℕ) (p : Θ × ℝ) := f p.1 (c n p.2)
  have hProj : QuasiMeasurePreserving Prod.fst (μ.prod (volume : Measure ℝ)) μ := quasiMeasurePreserving_fst
  apply aemeasurable_of_tendsto_metrizable_ae' (f := g)
  · intro n
    let v (r : (c n).range) (θ : Θ) := (hMeas r).mk (fun θ => f θ r) θ
    have hV : Measurable (fun p : Θ × (c n).range => v p.2 p.1) :=
      measurable_from_prod_countable_left fun r => (hMeas r).measurable_mk
    have hVeq : ∀ᵐ θ ∂μ, ∀ r : (c n).range, f θ r = v r θ :=
      ae_all_iff.mpr fun r => (hMeas r).ae_eq_mk
    let r (x : ℝ) : (c n).range := ⟨c n x, SimpleFunc.mem_range_self _ _⟩
    have hr : Measurable r := (c n).measurable.subtype_mk
    refine (hV.comp (measurable_fst.prodMk (hr.comp measurable_snd))).aemeasurable.congr ?_
    have hVeqP : ∀ᵐ p : Θ × ℝ ∂μ.prod volume, ∀ r : (c n).range, f p.1 r = v r p.1 :=
      hProj.ae hVeq
    filter_upwards [hVeqP] with p hp
    exact (hp (r p.2)).symm
  · have hContP : ∀ᵐ p : Θ × ℝ ∂μ.prod volume, Continuous (f p.1) := hProj.ae hCont
    filter_upwards [hContP] with p hp
    exact (hp.tendsto p.2).comp (hId.tendsto_approx p.2)

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyPhaseMeanCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleyPhaseMeanCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section PhaseMean

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

include hAdvance in
/-- The real Cayley value at each fixed real point is Haar measurable up
to a null set, by transport of the coherent value at the origin. -/
theorem aemeasurable_torusPoissonCayleyExtendedLeaf_real (x : ℝ) :
    AEMeasurable (fun θ => torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (x : ℂ)) volume := by
  let hPres := measurePreserving_unitAddTorusFlow β x
  refine ((aemeasurable_torusPoissonCayleyBoundary β S T hT hCont hCount hAdvance).comp_quasiMeasurePreserving
    hPres.quasiMeasurePreserving).congr ?_
  filter_upwards [ae_torusPoissonCayleyExtendedLeaf_real_phaseAdvance β S T hT hCont hCount hAdvance x]
    with θ hθ
  simpa only [Complex.ofReal_zero, zero_add, torusPoissonCayleyExtendedLeaf_zero, Function.comp_apply]
    using hθ 0

include hAdvance in
/-- The actual real Cayley paths are jointly Haar–Lebesgue measurable
up to a product null set. -/
theorem aemeasurable_prod_torusPoissonCayleyExtendedLeaf_real :
    AEMeasurable (fun p : UnitAddTorus d × ℝ =>
      torusPoissonCayleyExtendedLeaf β S T hT hCont hCount p.1 (p.2 : ℂ))
      ((volume : Measure (UnitAddTorus d)).prod volume) := by
  refine aemeasurable_prod_of_ae_continuous_sections
    (μ := (volume : Measure (UnitAddTorus d)))
    (fun θ (x : ℝ) => torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (x : ℂ)) ?_ ?_
  · filter_upwards [ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance]
      with θ hθ
    exact continuous_iff_continuousAt.mpr fun x =>
      (hθ x).1.continuousAt.comp Complex.continuous_ofReal.continuousAt
  · exact aemeasurable_torusPoissonCayleyExtendedLeaf_real β S T hT hCont hCount hAdvance

include hAdvance in
/-- The real phase density is Haar measurable up to a null set at fixed
real coordinates and jointly Haar–Lebesgue measurable up to a null set. -/
theorem aemeasurable_torusPoissonCayleyPhaseDensity :
    (∀ x : ℝ, AEMeasurable (fun θ => torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x)
      volume) ∧
    AEMeasurable (fun p : UnitAddTorus d × ℝ =>
      torusPoissonCayleyPhaseDensity β S T hT hCont hCount p.1 p.2)
      ((volume : Measure (UnitAddTorus d)).prod volume) := by
  let F (θ : UnitAddTorus d) (x : ℝ) :=
    torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (x : ℂ)
  let D (θ : UnitAddTorus d) (x : ℝ) := deriv (F θ) x
  have hGood := ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance
  have hDer (θ : UnitAddTorus d) (hθ : ∀ x : ℝ,
      AnalyticAt ℂ (torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ) (x : ℂ))
      (x : ℝ) : HasDerivAt (F θ)
        (deriv (torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ) (x : ℂ)) x :=
    ((hθ x).differentiableAt.hasDerivAt).comp_ofReal
  have hContDer : ∀ᵐ θ ∂volume, Continuous (D θ) := by
    filter_upwards [hGood] with θ hθ
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hEq : D θ = fun x : ℝ =>
        deriv (torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ) (x : ℂ) :=
      funext fun x => (hDer θ (fun t => (hθ t).1) x).deriv
    rw [hEq]
    exact (hθ x).1.deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hMeas (x : ℝ) : AEMeasurable (fun θ => D θ x) volume := by
    apply aemeasurable_of_tendsto_metrizable_ae (𝓝[≠] (0 : ℝ))
      (f := fun r θ => r⁻¹ • (F θ (x + r) - F θ x))
    · intro r
      exact ((aemeasurable_torusPoissonCayleyExtendedLeaf_real β S T hT hCont hCount hAdvance (x + r)).sub
        (aemeasurable_torusPoissonCayleyExtendedLeaf_real β S T hT hCont hCount hAdvance x)).const_smul (r⁻¹ : ℝ)
    · filter_upwards [hGood] with θ hθ
      exact ((hDer θ (fun t => (hθ t).1) x).differentiableAt.hasDerivAt).tendsto_slope_zero
  exact ⟨fun x => (hMeas x).norm.div_const _,
    (aemeasurable_prod_of_ae_continuous_sections D hContDer hMeas).norm.div_const _⟩


/-- The Haar mean of the nonnegative real phase density at the origin. -/
def torusPoissonCayleyMeanPhaseDensity : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ 0)

include hAdvance in
/-- Haar invariance makes the expected real phase density independent
of the real coordinate. -/
theorem lintegral_torusPoissonCayleyPhaseDensity_eq_mean (x : ℝ) :
    (∫⁻ θ, ENNReal.ofReal (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x)) =
      torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount := by
  let f (x : ℝ) (θ : UnitAddTorus d) :=
    ENNReal.ofReal (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x)
  let hPres := measurePreserving_unitAddTorusFlow β x
  have hMeas : AEMeasurable (f 0) (Measure.map (unitAddTorusFlow β x) volume) := by
    rw [hPres.map_eq]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((aemeasurable_torusPoissonCayleyPhaseDensity β S T hT hCont hCount hAdvance).1 0)
  calc
    _ = ∫⁻ θ, f 0 (unitAddTorusFlow β x θ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_torusPoissonCayleyPhaseDensity_phaseAdvance β S T hT hCont hCount hAdvance x]
        with θ hθ
      have h := congrArg ENNReal.ofReal (hθ 0)
      simpa only [f, zero_add] using h.symm
    _ = _ := by
      have h := lintegral_map' hMeas hPres.measurable.aemeasurable
      rw [hPres.map_eq] at h
      exact h.symm

include hAdvance in
/-- The expected mass of the real phase density on a compact interval
is its length times the Haar mean. -/
theorem lintegral_interval_torusPoissonCayleyPhaseDensity (a b : ℝ) :
    (∫⁻ θ, ∫⁻ x in Icc a b,
      ENNReal.ofReal (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x)) =
      ENNReal.ofReal (b - a) * torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount := by
  let ν := (volume : Measure ℝ).restrict (Icc a b)
  let f (θ : UnitAddTorus d) (x : ℝ) :=
    ENNReal.ofReal (torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x)
  have hMeas : AEMeasurable (Function.uncurry f) ((volume : Measure (UnitAddTorus d)).prod ν) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_torusPoissonCayleyPhaseDensity β S T hT hCont hCount hAdvance).2).mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self)
  change (∫⁻ θ, ∫⁻ x, f θ x ∂ν) = _
  rw [lintegral_lintegral_swap hMeas]
  simp only [f, lintegral_torusPoissonCayleyPhaseDensity_eq_mean β S T hT hCont hCount hAdvance,
    lintegral_const, ν, Measure.restrict_apply_univ, Real.volume_Icc, mul_comm]


include hAdvance in
/-- Any almost-everywhere count cap on the actual support in one interval
gives a quantitative bound on the Haar-averaged mass of that interval. -/
theorem mul_torusPoissonCayleyMeanPhaseDensity_le_of_supportCount
    {a b : ℝ} (hab : a ≤ b) (C : ℕ)
    (hCap : ∀ᵐ θ ∂volume, (Distribution.dsupport (T θ) ∩ Ioo a b).ncard ≤ C) :
    ENNReal.ofReal (b - a) * torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount ≤
      (C : ℝ≥0∞) + 1 := by
  let f (θ : UnitAddTorus d) (x : ℝ) := torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ x
  have hMass : ∀ᵐ θ ∂volume, (∫⁻ x in Icc a b, ENNReal.ofReal (f θ x)) ≤
      (C : ℝ≥0∞) + 1 := by
    filter_upwards [ae_intervalIntegral_torusPoissonCayleyPhaseDensity_le β S T hT hCont hCount hAdvance,
      ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance, hCap]
      with θ hBound hAn hCnt
    let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ
    have hEq : (fun t : ℝ => deriv (fun x : ℝ => F (x : ℂ)) t) =
        fun t : ℝ => deriv F (t : ℂ) :=
      funext fun t => ((hAn t).1.differentiableAt.hasDerivAt.comp_ofReal).deriv
    have hDerCont : Continuous (fun t : ℝ => deriv F (t : ℂ)) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact (hAn t).1.deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt
    have hContF : Continuous (f θ) := by
      change Continuous (fun x : ℝ => ‖deriv (fun t : ℝ => F (t : ℂ)) x‖ / (2 * Real.pi))
      simp only [hEq]
      exact hDerCont.norm.div_const _
    have hInt : IntegrableOn (f θ) (Icc a b) :=
      hContF.continuousOn.integrableOn_compact isCompact_Icc
    have hNonneg (x : ℝ) : 0 ≤ f θ x := div_nonneg (norm_nonneg _) Real.two_pi_pos.le
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hNonneg),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have hRealCnt : ((Distribution.dsupport (T θ) ∩ Ioo a b).ncard : ℝ) ≤ C := by
      exact_mod_cast hCnt
    have hReal : (∫ x in a..b, f θ x) ≤ (C : ℝ) + 1 := by
      linarith only [hBound a b hab, hRealCnt]
    have h := ENNReal.ofReal_le_ofReal hReal
    rwa [ENNReal.ofReal_add (Nat.cast_nonneg C) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one] at h
  have h := lintegral_mono_ae hMass
  rwa [lintegral_interval_torusPoissonCayleyPhaseDensity β S T hT hCont hCount hAdvance,
    lintegral_const, measure_univ, mul_one] at h

include hAdvance in
/-- The Haar mean is finite, at most the uniform unit-cell support cap plus one. -/
theorem torusPoissonCayleyMeanPhaseDensity_le_unitCap :
    torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount ≤ (K : ℝ≥0∞) + 1 := by
  have hCap : ∀ᵐ θ ∂volume, (Distribution.dsupport (T θ) ∩ Ioo (0 : ℝ) 1).ncard ≤ K := by
    filter_upwards with θ
    have hSub : Distribution.dsupport (T θ) ∩ Ioo (0 : ℝ) 1 ⊆ (S θ).carrier ∩ Ico 0 1 :=
      fun _ h => ⟨dsupport_subset_of_discrete_support (S θ) (T θ) (hT θ) h.1, h.2.1.le, h.2.2⟩
    exact (Set.ncard_le_ncard hSub ((S θ).finite_inter_Ico 0 1)).trans (by simpa using hCount θ 0)
  have h := mul_torusPoissonCayleyMeanPhaseDensity_le_of_supportCount
    β S T hT hCont hCount hAdvance zero_le_one K hCap
  simpa only [sub_zero, ENNReal.ofReal_one, one_mul] using h


end PhaseMean

end
end MeyerGeneralProblem
