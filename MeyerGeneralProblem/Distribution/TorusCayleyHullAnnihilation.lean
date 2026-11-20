module

public import MeyerGeneralProblem.Distribution.TorusCayleyHullVanishing
public import MeyerGeneralProblem.Distribution.TorusSchwartzOrbitConvolution
public import MeyerGeneralProblem.Distribution.IntrinsicJetAnnihilation

@[expose] public section

/-!
# Schwartz multiplication by the Cayley finite difference

The nonzero band difference is a temperate multiplier on each good
real orbit. The intrinsic zero jets annihilate the whole original
distribution when its Schwartz order is below the Cayley power.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Set UnitAddTorus

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- Use normalized Haar measure on each circle factor. -/
local instance hullAnnihilationCircleMeasureSpace : MeasureSpace UnitAddCircle :=
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

/-- Under the corresponding hull Schwartz-order bound, the extracted
nonzero Cayley finite difference annihilates the hull distributions
as a multiplier on the full Schwartz space. -/
theorem exists_torusCayleyFiniteDifference_annihilates_hull
    (E W : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) (hq : 0 < q) (hWidth : (q : ℝ) * E < W)
    (hOrder : ∀ᵐ θ ∂volume, HasSchwartzSeminormBound (T θ) 2 (q - 1)) :
    let e := (mFourierBasis (d := d)).repr
    let U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance : _ ≃ₗᵢ[ℂ] _)
    ∃ (W₀ : ℝ) (f : SeqL2(d → ℤ)) (G : UnitAddTorus d → ℂ) (R : UnitAddTorus d → ℂ → ℂ),
      0 ≤ W₀ ∧ f ≠ 0 ∧ ((U - 1) ^ q) f ≠ 0 ∧
      (∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W₀ →
        f n = 0 ∧ ((U - 1) ^ q) f n = 0) ∧
      Measurable G ∧ G =ᵐ[volume] e.symm (((U - 1) ^ q) f) ∧
      ∀ᵐ θ ∂volume, Differentiable ℂ (R θ) ∧
        (∀ᵐ x : ℝ ∂volume, R θ (x : ℂ) = G (unitAddTorusFlow β x θ)) ∧
        (fun x : ℝ => R θ (x : ℂ)).HasTemperateGrowth ∧
        TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => R θ (x : ℂ)) (T θ) = 0 := by
  intro e U
  obtain ⟨W₀, f, F, G, A, R, hW₀, hf, hNe, hBand, hF, hG, hFRep, hGRep, hHull⟩ :=
    exists_entire_torusCayleyFiniteDifference_vanishing_on_hull
      β S T hT hCont hCount hAdvance E W hE q hWidth
  let r := ((U - 1) ^ q) f
  let Rreal (θ : UnitAddTorus d) (x : ℝ) := R θ (x : ℂ)
  have hRBand (n : d → ℤ) (hn : torusDirectionalFrequency β n ∉ Icc 0 W₀) :
      mFourierCoeff (e.symm r) n = 0 := by
    rw [← mFourierBasis_repr]
    change e (e.symm r) n = 0
    rw [e.apply_symm_apply]
    exact (hBand n hn).2
  have hReal : ∀ᵐ θ ∂volume, Continuous (Rreal θ) ∧
      Rreal θ =ᵐ[volume] fun t => G (unitAddTorusFlow β t θ) := by
    filter_upwards [hHull] with θ hθ
    exact ⟨hθ.2.1.continuous.comp Complex.continuous_ofReal, hθ.2.2.2.1⟩
  have hGrow := ae_hasTemperateGrowth_of_continuous_torusOrbit_representative
    β W₀ (e.symm r) hRBand G hG hGRep Rreal hReal
  refine ⟨W₀, f, G, R, hW₀, hf, hNe, hBand, hG, hGRep, ?_⟩
  filter_upwards [hHull, hOrder, hGrow] with θ hθ hOrderθ hGrowθ
  refine ⟨hθ.2.1, hθ.2.2.2.1, hGrowθ, ?_⟩
  exact temperedDistribution_smulLeft_eq_zero_of_intrinsic_zero_jets
    (S θ) (T θ) (hT θ) 2 (q - 1) hOrderθ (Rreal θ) hGrowθ
    (fun a ha j hj => hθ.2.2.2.2.2 a ha j (by omega))

end
end
end MeyerGeneralProblem
