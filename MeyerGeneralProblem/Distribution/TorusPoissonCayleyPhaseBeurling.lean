module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPhaseMean
public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusSupport
public import MeyerGeneralProblem.Carrier.UniformDensity
public import Mathlib.Data.Set.Card.Arithmetic

@[expose] public section

/-!
# The Haar phase density bound by the original Beurling density

The original fixed-length support cap passes to the weak phase family.
The expected phase mass is bounded by this cap plus one. Increasing
the length gives the exact normalized upper uniform density bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal FourierTransform NNReal Topology

private theorem exists_max_windowCount_of_unitCap (A : LocallyFiniteCarrier) {K : ℕ}
    (hA : ∀ r, windowCount A r 1 ≤ K) (L : ℝ) :
    ∃ r : ℝ, ∀ s : ℝ, windowCount A s L ≤ windowCount A r L := by
  obtain ⟨N, hN⟩ := exists_nat_gt L
  have hBound (r : ℝ) : windowCount A r L ≤ N * K := by
    let U (j : Fin N) := A.carrier ∩ Ico (r + (j : ℕ)) (r + (j : ℕ) + 1)
    have hF (j : Fin N) : (U j).Finite := A.finite_inter_Ico _ _
    have hSub : A.carrier ∩ Ico r (r + L) ⊆ ⋃ j, U j := by
      intro x hx
      have hPos : 0 ≤ x - r := sub_nonneg.mpr hx.2.1
      let j := Nat.floor (x - r)
      have hj : j < N := (Nat.floor_lt hPos).mpr (by linarith only [hN, hx.2.2])
      refine mem_iUnion.mpr ⟨⟨j, hj⟩, hx.1, ?_, ?_⟩
      · have h := Nat.floor_le hPos
        linarith only [h]
      · have h := Nat.lt_floor_add_one (x - r)
        linarith only [h]
    change (A.carrier ∩ Ico r (r + L)).ncard ≤ N * K
    refine (Set.ncard_le_ncard hSub (Set.finite_iUnion hF)).trans ?_
    refine (Set.ncard_iUnion_le_of_fintype U).trans ?_
    calc
      _ ≤ ∑ j : Fin N, K := Finset.sum_le_sum fun j _ => hA (r + (j : ℕ))
      _ = _ := by simp
  let W := Set.range fun r : ℝ => windowCount A r L
  have hW : BddAbove W := ⟨N * K, by rintro _ ⟨r, rfl⟩; exact hBound r⟩
  obtain ⟨r, hr⟩ := Nat.sSup_mem (range_nonempty _) hW
  change windowCount A r L = sSup W at hr
  exact ⟨r, fun s => (le_csSup hW (mem_range_self s)).trans_eq hr.symm⟩

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleySharpDensityCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

include hAdvance in
/-- An original all-length support cap gives the sharp Haar phase-density
bound by the physical upper uniform Beurling density. -/
theorem torusPoissonCayleyMeanPhaseDensity_le_upperUniformBeurlingDensity
    (A : LocallyFiniteCarrier) (hA : ∀ r, windowCount A r 1 ≤ K)
    (hWin : ∀ (L : ℝ), 0 < L → ∀ C : ℕ, (∀ r : ℝ, windowCount A r L ≤ C) →
      ∀ᵐ θ ∂volume, (Distribution.dsupport (T θ) ∩ Ioo 0 L).ncard ≤ C) :
    torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount ≤
      upperUniformBeurlingDensity A := by
  let D := torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount
  have hD : D ≠ ∞ :=
    (lt_of_le_of_lt (torusPoissonCayleyMeanPhaseDensity_le_unitCap β S T hT hCont hCount hAdvance)
      (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top K, ENNReal.one_lt_top⟩)).ne
  change D ≤ limsup (upperUniformDensityProfile A) atTop
  refine le_limsup_of_le (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩) ?_
  intro e he
  by_cases hTop : e = ∞
  · simp [hTop]
  by_contra! hlt
  have hRealLt : e.toReal < D.toReal := (ENNReal.toReal_lt_toReal hTop hD).mpr hlt
  have hDelta : 0 < D.toReal - e.toReal := sub_pos.mpr hRealLt
  have hLong : ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 / (D.toReal - e.toReal) < L :=
    (eventually_gt_atTop 0).and (eventually_gt_atTop _)
  obtain ⟨L, ⟨hPos, hLarge⟩, hLe⟩ := (hLong.and he).exists
  obtain ⟨r, hMax⟩ := exists_max_windowCount_of_unitCap A hA L
  let C := windowCount A r L
  have hMass := mul_torusPoissonCayleyMeanPhaseDensity_le_of_supportCount
    β S T hT hCont hCount hAdvance hPos.le C (hWin L hPos C hMax)
  have hMassR := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top C, ENNReal.one_ne_top⟩) hMass
  simp only [sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.le,
    ENNReal.toReal_add (ENNReal.natCast_ne_top C) ENNReal.one_ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_one] at hMassR
  change L * D.toReal ≤ (C : ℝ) + 1 at hMassR
  have hProfile : (C : ℝ≥0∞) / ENNReal.ofReal L ≤ e := by
    calc
      _ ≤ upperUniformDensityProfile A L := by
        rw [A.upperUniformDensityProfile_of_pos hPos]
        exact le_iSup (fun s => (windowCount A s L : ℝ≥0∞) / ENNReal.ofReal L) r
      _ ≤ e := hLe
  have hProfileM : (C : ℝ≥0∞) ≤ e * ENNReal.ofReal L :=
    (ENNReal.div_le_iff_le_mul (Or.inr hTop) (Or.inl ENNReal.ofReal_ne_top)).mp hProfile
  have hProfileR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hTop ENNReal.ofReal_ne_top) hProfileM
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.le] at hProfileR
  have hGap : 1 < L * (D.toReal - e.toReal) := (div_lt_iff₀ hDelta).mp hLarge
  nlinarith only [hMassR, hProfileR, hGap]

end

/-- On the actual original weak phase family the Haar boundary phase
density is bounded by the original physical upper Beurling density. -/
theorem exists_originalPhasePhysical_meanPhaseDensity_le_upperUniformBeurlingDensity
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ)
    {K : ℕ} (hA : ∀ r, windowCount A r 1 ≤ K) :
    let T := originalPhasePhysicalRecord B label N μ hν
    ∃ (S : UnitAddTorus d → LocallyFiniteCarrier)
      (hS : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
      (hK : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K),
      torusPoissonCayleyMeanPhaseDensity β S T hS
        (fun f _ => continuous_originalPhasePhysicalRecord_apply B label N μ hν f) hK ≤
        upperUniformBeurlingDensity A := by
  let T := originalPhasePhysicalRecord B label N μ hν
  obtain ⟨S, _, hS, hK⟩ :=
    exists_originalPhasePhysicalRecord_supportFamily A B label β hLabel hIndep N μ hν hμ hA
  refine ⟨S, hS, hK, ?_⟩
  have hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ) :=
    fun t θ => originalPhasePhysicalRecord_advance B label β hLabel N μ hν θ t
  apply torusPoissonCayleyMeanPhaseDensity_le_upperUniformBeurlingDensity
    β S T hS _ hK hAdvance A hA
  intro L _ C hCap
  filter_upwards with θ
  obtain ⟨hFin, hW⟩ := finite_and_ncard_originalPhasePhysical_support_window A B label β hLabel
    hIndep N μ hν hμ L C hCap θ 0
  simp only [zero_add] at hFin hW
  exact (Set.ncard_le_ncard (inter_subset_inter_right _ Ioo_subset_Ico_self) hFin).trans hW


end
end MeyerGeneralProblem
