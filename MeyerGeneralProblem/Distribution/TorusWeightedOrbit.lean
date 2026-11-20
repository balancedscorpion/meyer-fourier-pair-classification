module

public import MeyerGeneralProblem.Distribution.TorusPoissonFourierMultiplier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Weighted square integrability along torus orbits

Haar invariance and Tonelli give the weighted mean square of an orbit.
This gives a measurable representative for band-limited torus data
with finite weighted orbit norm at almost every phase.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory UnitAddTorus
open scoped ENNReal

/-- Use normalized Haar measure on each circle factor of the torus. -/
local instance torusBandCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- Normalized Haar measure gives each circle factor total mass one. -/
local instance torusBandCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The weighted mean square of a torus orbit is the Haar mean square
times the mass of the weight. -/
theorem lintegral_weighted_torusOrbit_norm_sq {d : Type*} [Fintype d]
    (β : d → ℝ) (F : UnitAddTorus d → ℂ) (hF : Measurable F)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ θ, ∫⁻ x : ℝ, w x * ENNReal.ofReal (‖F (unitAddTorusFlow β x θ)‖ ^ 2)) =
      (∫⁻ x, w x) * (∫⁻ θ, ENNReal.ofReal (‖F θ‖ ^ 2)) := by
  let G (θ : UnitAddTorus d) := ENNReal.ofReal (‖F θ‖ ^ 2)
  let H (θ : UnitAddTorus d) (x : ℝ) := w x * G (unitAddTorusFlow β x θ)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hF.norm.pow_const 2)
  have hJoint : Measurable (Function.uncurry H) :=
    (hw.comp measurable_snd).mul (hG.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  have hInv (x : ℝ) :
      (∫⁻ θ, G (unitAddTorusFlow β x θ)) = ∫⁻ θ, G θ := by
    have hPres := measurePreserving_unitAddTorusFlow β x
    have h := lintegral_map (μ := (volume : Measure (UnitAddTorus d))) hG hPres.measurable
    rw [hPres.map_eq] at h
    exact h.symm
  have hInner (x : ℝ) :
      (∫⁻ θ, H θ x) = w x * ∫⁻ θ, G θ := by
    have hx := (measurePreserving_unitAddTorusFlow β x).measurable
    change (∫⁻ θ, w x * G (unitAddTorusFlow β x θ)) = _
    have h := lintegral_const_mul (μ := (volume : Measure (UnitAddTorus d))) (w x) (hG.comp hx)
    change (∫⁻ θ, w x * G (unitAddTorusFlow β x θ)) =
      w x * ∫⁻ θ, G (unitAddTorusFlow β x θ) at h
    rw [h, hInv]
  change (∫⁻ θ, ∫⁻ x, H θ x) = (∫⁻ x, w x) * ∫⁻ θ, G θ
  rw [lintegral_lintegral_swap hJoint.aemeasurable]
  simp_rw [hInner]
  exact lintegral_mul_const _ hw

/-- A square-integrable torus function has a finite weighted mean square
along almost every real phase orbit. -/
theorem ae_torusOrbit_weighted_norm_sq_lt_top {d : Type*} [Fintype d]
    (β : d → ℝ) (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hLp : MemLp F 2 volume) :
    ∀ᵐ θ, (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹) *
      ENNReal.ofReal (‖F (unitAddTorusFlow β x θ)‖ ^ 2)) < ∞ := by
  let w (x : ℝ) := ENNReal.ofReal ((1 + x ^ 2)⁻¹)
  let G (θ : UnitAddTorus d) := ENNReal.ofReal (‖F θ‖ ^ 2)
  let H (θ : UnitAddTorus d) (x : ℝ) := w x * G (unitAddTorusFlow β x θ)
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    ((measurable_const.add (measurable_id.pow_const 2)).inv)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hF.norm.pow_const 2)
  have hJoint : Measurable (Function.uncurry H) :=
    (hw.comp measurable_snd).mul (hG.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  change ∀ᵐ θ, (∫⁻ x, H θ x) < ∞
  apply ae_lt_top hJoint.lintegral_prod_right'
  have hwFin : (∫⁻ x, w x) < ∞ := by
    have h := integrable_inv_one_add_sq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_norm] at h
    have hEq : (fun x : ℝ => ENNReal.ofReal ‖(1 + x ^ 2)⁻¹‖) = w := by
      funext x
      exact congrArg ENNReal.ofReal (Real.norm_of_nonneg (by positivity))
    rwa [hEq] at h
  have hgFin : (∫⁻ θ, G θ) < ∞ := by
    have h := (hLp.integrable_norm_pow (p := 2) (by decide)).hasFiniteIntegral
    rw [hasFiniteIntegral_iff_norm] at h
    have hEq : (fun θ => ENNReal.ofReal ‖‖F θ‖ ^ 2‖) = G := by
      funext θ
      exact congrArg ENNReal.ofReal (Real.norm_of_nonneg (sq_nonneg _))
    rwa [hEq] at h
  have h := lintegral_weighted_torusOrbit_norm_sq β F hF w hw
  change (∫⁻ θ, ∫⁻ x, H θ x) = (∫⁻ x, w x) * ∫⁻ θ, G θ at h
  change (∫⁻ θ, ∫⁻ x, H θ x) ≠ ∞
  rw [h]
  exact (ENNReal.mul_lt_top hwFin hgFin).ne

/-- Changing the measurable Haar representative changes almost every orbit on
only a Lebesgue-null set. -/
theorem ae_torusOrbit_congr {d : Type*} [Fintype d] (β : d → ℝ)
    (F G : UnitAddTorus d → ℂ) (hF : Measurable F) (hG : Measurable G)
    (hEq : F =ᵐ[volume] G) :
    ∀ᵐ θ ∂volume, ∀ᵐ x ∂volume, F (unitAddTorusFlow β x θ) = G (unitAddTorusFlow β x θ) := by
  let A (p : UnitAddTorus d × ℝ) := unitAddTorusFlow β p.2 p.1
  have hA : Measurable A := (continuous_unitAddTorusFlow β).measurable.comp measurable_swap
  have hSet : MeasurableSet {p : UnitAddTorus d × ℝ | F (A p) = G (A p)} :=
    measurableSet_eq_fun (hF.comp hA) (hG.comp hA)
  apply (Measure.ae_ae_comm (μ := (volume : Measure (UnitAddTorus d))) (ν := (volume : Measure ℝ)) hSet).mpr
  exact Eventually.of_forall fun x => (measurePreserving_unitAddTorusFlow β x).quasiMeasurePreserving.ae hEq

/-- Each torus L² class has a measurable representative with finite
weighted orbit mean square for Haar-almost every phase. -/
theorem exists_torusLp_representative_with_weighted_orbits {d : Type*} [Fintype d]
    (β : d → ℝ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ∃ F : UnitAddTorus d → ℂ, Measurable F ∧ F =ᵐ[volume] f ∧
      ∀ᵐ θ, (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹) *
        ENNReal.ofReal (‖F (unitAddTorusFlow β x θ)‖ ^ 2)) < ∞ := by
  let hf := (Lp.aestronglyMeasurable f).aemeasurable
  let F := hf.mk (⇑f)
  have hF : Measurable F := hf.measurable_mk
  have hEq : F =ᵐ[volume] f := hf.ae_eq_mk.symm
  have hLp : MemLp F 2 volume := (memLp_congr_ae hEq.symm).mp (Lp.memLp f)
  exact ⟨F, hF, hEq, ae_torusOrbit_weighted_norm_sq_lt_top β F hF hLp⟩

end
end MeyerGeneralProblem
