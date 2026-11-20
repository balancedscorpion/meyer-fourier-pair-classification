module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayley

@[expose] public section

/-!
# The exceptional value of the Cayley boundary has measure zero

Haar invariance makes the mean point mass independent of the point.
Arbitrarily many distinct tests in one unit interval then force that
mean to vanish under the common support-count cap.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal NNReal Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyBoundaryMeasureCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleyBoundaryMeasureCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem pointMass_supportCount_one {U : TemperedDistribution ℝ ℂ} {x : ℝ}
    (h : x ∈ Distribution.dsupport U) : discreteSupportCount U {x} = 1 := by
  rw [discreteSupportCount, Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_mem h]
  simp

private theorem pointMass_supportCount_zero {U : TemperedDistribution ℝ ℂ} {x : ℝ}
    (h : x ∉ Distribution.dsupport U) : discreteSupportCount U {x} = 0 := by
  rw [discreteSupportCount, Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_notMem h]
  simp

section ExceptionalValue

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

include β S hT hCont hCount hAdvance in
private theorem ae_origin_notMem_dsupport : ∀ᵐ θ ∂volume, 0 ∉ Distribution.dsupport (T θ) := by
  let η (θ : UnitAddTorus d) := discreteSupportCount (T θ)
  let f (x : ℝ) (θ : UnitAddTorus d) := (η θ {x}).toReal
  have hMeas (x : ℝ) : Measurable (f x) :=
    ((Measure.measurable_coe (measurableSet_singleton x)).comp
      (measurable_discreteSupportCount S T hT hCont)).ennreal_toReal
  have hInt (x : ℝ) : Integrable (f x) := by
    apply Integrable.of_bound (hMeas x).aestronglyMeasurable 1
    filter_upwards with θ
    by_cases h : x ∈ Distribution.dsupport (T θ)
    · simp [f, η, pointMass_supportCount_one h]
    · simp [f, η, pointMass_supportCount_zero h]
  have hEq (x : ℝ) (θ : UnitAddTorus d) : f 0 (unitAddTorusFlow β x θ) = f x θ := by
    have hPoint : 0 ∈ Distribution.dsupport (T (unitAddTorusFlow β x θ)) ↔ x ∈ Distribution.dsupport (T θ) := by
      rw [hAdvance, dsupport_combDistributionTranslation]
      constructor
      · rintro ⟨y, hy, he⟩
        have : y = x := by linarith
        simpa only [this] using hy
      · intro h
        exact ⟨x, h, neg_add_cancel _⟩
    by_cases hx : x ∈ Distribution.dsupport (T θ)
    · simp [f, η, pointMass_supportCount_one hx, pointMass_supportCount_one (hPoint.mpr hx)]
    · simp [f, η, pointMass_supportCount_zero hx, pointMass_supportCount_zero (fun h => hx (hPoint.mp h))]
  let P := ∫ θ, f 0 θ
  have hMean (x : ℝ) : (∫ θ, f x θ) = P := by
    have hPres := measurePreserving_unitAddTorusFlow β x
    have hMeasMap : AEStronglyMeasurable (f 0) (Measure.map (unitAddTorusFlow β x) volume) := by
      rw [hPres.map_eq]
      exact (hMeas 0).aestronglyMeasurable
    calc
      _ = ∫ θ, f 0 (unitAddTorusFlow β x θ) :=
        integral_congr_ae (ae_of_all _ fun θ => (hEq x θ).symm)
      _ = _ := by
        have h := integral_map hPres.measurable.aemeasurable hMeasMap
        rw [hPres.map_eq] at h
        exact h.symm
  have hCap (N : ℕ) : (N : ℝ) * P ≤ K := by
    let r (j : Fin N) : ℝ := (j : ℕ) / ((N : ℝ) + 1)
    have hPos : 0 < (N : ℝ) + 1 := by positivity
    have hInj : Function.Injective r := by
      intro i j hij
      change ((i : ℕ) : ℝ) / ((N : ℝ) + 1) = ((j : ℕ) : ℝ) / ((N : ℝ) + 1) at hij
      have h := congrArg (fun x : ℝ => x * ((N : ℝ) + 1)) hij
      simp only [div_mul_cancel₀ _ hPos.ne'] at h
      exact Fin.ext (by exact_mod_cast h)
    have hWin (j : Fin N) : r j ∈ Ico 0 1 := by
      refine ⟨by unfold r; positivity, ?_⟩
      change ((j : ℕ) : ℝ) / ((N : ℝ) + 1) < 1
      apply (div_lt_iff₀ hPos).mpr
      have h := (show ((j : ℕ) : ℝ) < (N : ℝ) by exact_mod_cast j.isLt)
      linarith
    have hBound (θ : UnitAddTorus d) : (∑ j : Fin N, f (r j) θ) ≤ (K : ℝ) := by
      have hDis : Pairwise (fun i j : Fin N => Disjoint ({r i} : Set ℝ) {r j}) :=
        fun _ _ h => Set.disjoint_singleton.mpr (fun he => h (hInj he))
      have hU : (η θ) (⋃ j : Fin N, ({r j} : Set ℝ)) =
          ∑ j : Fin N, (η θ) {r j} := by
        rw [measure_iUnion hDis (fun _ => measurableSet_singleton _), tsum_fintype]
      have hSub : (⋃ j : Fin N, ({r j} : Set ℝ)) ⊆ Ico (0 : ℝ) 1 :=
        iUnion_subset fun j => singleton_subset_iff.mpr (hWin j)
      have hLe : (η θ) (⋃ j : Fin N, ({r j} : Set ℝ)) ≤ (K : ℝ≥0∞) :=
        (measure_mono hSub).trans (by
          simpa only [η, zero_add] using discreteSupportCount_unit_window_le
            (S θ) (T θ) (hT θ) (hCount θ) 0)
      have hFinite (j : Fin N) : (η θ) {r j} ≠ ∞ := by
        by_cases h : r j ∈ Distribution.dsupport (T θ)
        · simp [η, pointMass_supportCount_one h]
        · simp [η, pointMass_supportCount_zero h]
      simp only [f]
      rw [← ENNReal.toReal_sum (fun j _ => hFinite j), ← hU]
      simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono (ENNReal.natCast_ne_top K) hLe
    have h := integral_mono
      (integrable_finsetSum Finset.univ (fun j _ => hInt (r j)))
      (integrable_const (K : ℝ)) hBound
    rw [integral_finsetSum _ (fun j _ => hInt (r j))] at h
    simp only [hMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
    exact h
  have hP0 : 0 ≤ P := integral_nonneg fun _ => ENNReal.toReal_nonneg
  have hZero : P = 0 := by
    by_contra h
    have hp : 0 < P := lt_of_le_of_ne hP0 (Ne.symm h)
    obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℝ) / P)
    exact (not_lt_of_ge (hCap N)) ((div_lt_iff₀ hp).mp hN)
  have hAE : f 0 =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hInt 0)).mp hZero
  filter_upwards [hAE] with θ hθ
  intro h
  simp [f, η, pointMass_supportCount_one h] at hθ

/-- The value one occurs on a Haar-null set of the coherent Cayley boundary. -/
theorem ae_ne_one_torusPoissonCayleyBoundaryL2 :
    ∀ᵐ θ ∂volume, torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance θ ≠ 1 := by
  have hCoe : torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance =ᵐ[volume]
      torusPoissonCayleyBoundary β S T hT hCont hCount := by
    unfold torusPoissonCayleyBoundaryL2
    exact MemLp.coeFn_toLp _
  filter_upwards [hCoe, ae_origin_notMem_dsupport β S T hT hCont hCount hAdvance,
    ae_re_torusPositivePoissonLeaf_real_of_notMem_dsupport β S T hT hCont hCount hAdvance]
    with θ hθ hNo hRe
  let w := torusPositivePoissonLeaf β S T hT hCont hCount θ 0
  have hReal : w.re = 0 := by simpa only [Complex.ofReal_zero] using hRe 0 hNo
  have hDen := supportPoissonCayley_denominator_ne_zero hReal.ge
  rw [hθ]
  simp only [torusPoissonCayleyBoundary, ite_eq_right hNo, supportPoissonCayley]
  intro h
  have he := (div_eq_iff hDen).mp h
  exact (show (2 : ℂ) ≠ 0 by norm_num) (by linear_combination -he)

end ExceptionalValue

end
end MeyerGeneralProblem
