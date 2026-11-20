module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Uniform bounds for compact interpolation families

A jointly continuous family of injective linear maps has one positive lower
bound on a compact parameter set when the domain has compact closed balls.
The proof minimizes the actual image norm on the parameter/unit-sphere
product. No inverse norm estimate is supplied as a hypothesis. Finite complex
coefficient spaces have the required properness. Applying this result to
grouped interpolation still requires the actual data map's continuity and
injectivity, including every allowed confluent boundary configuration.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Compactness and injectivity give a single positive lower bound for the
actual linear family. Empty parameter sets and zero-dimensional domains
require no separate nondegeneracy assumption. -/
theorem exists_uniform_lowerBound_of_compact_injective_family
    (K : Set P) (hK : IsCompact K) (T : P → E →ₗ[ℂ] F)
    (hcontinuous : Continuous (fun z : P × E => T z.1 z.2))
    (hinjective : ∀ p ∈ K, Function.Injective (T p)) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ K, ∀ x : E, A * ‖x‖ ≤ ‖T p x‖ := by
  have hcompact : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) :=
    hK.prod (isCompact_sphere 0 1)
  obtain ⟨A, hA, hlower⟩ := hcompact.exists_forall_le'
    hcontinuous.norm.continuousOn (a := (0 : ℝ)) (by
      rintro ⟨p, x⟩ ⟨hp, hx⟩
      apply norm_pos_iff.mpr
      intro hzero
      have hxzero : x = 0 := hinjective p hp (hzero.trans (map_zero (T p)).symm)
      simp [hxzero] at hx)
  refine ⟨A, hA, ?_⟩
  intro p hp x
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : E) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
    exact inv_mul_cancel₀ hnorm.ne'
  have h := hlower (p, ((‖x‖⁻¹ : ℝ) : ℂ) • x) ⟨hp, hunit⟩
  simp only [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg x)] at h
  exact (le_div_iff₀ hnorm).mp (by simpa only [div_eq_mul_inv, mul_comm] using h)

/-- The reciprocal lower bound controls the preimage norm uniformly; there
is no parameter-dependent inverse constant in the conclusion. -/
theorem exists_uniform_preimageNormBound_of_compact_injective_family
    (K : Set P) (hK : IsCompact K) (T : P → E →ₗ[ℂ] F)
    (hcontinuous : Continuous (fun z : P × E => T z.1 z.2))
    (hinjective : ∀ p ∈ K, Function.Injective (T p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ x : E, ‖x‖ ≤ C * ‖T p x‖ := by
  obtain ⟨A, hA, hlower⟩ := exists_uniform_lowerBound_of_compact_injective_family
    K hK T hcontinuous hinjective
  refine ⟨A⁻¹, inv_pos.mpr hA, ?_⟩
  intro p hp x
  have h := mul_le_mul_of_nonneg_left (hlower p hp x) (inv_nonneg.mpr hA.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using h

/-- A compact family of bijective actual interpolation maps has unique
interpolants with one common norm bound, even at confluent parameters. -/
theorem exists_uniform_interpolant_of_compact_bijective_family
    (K : Set P) (hK : IsCompact K) (T : P → E →ₗ[ℂ] F)
    (hcontinuous : Continuous (fun z : P × E => T z.1 z.2))
    (hbijective : ∀ p ∈ K, Function.Bijective (T p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ data : F,
      ∃! x : E, T p x = data ∧ ‖x‖ ≤ C * ‖data‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_preimageNormBound_of_compact_injective_family
    K hK T hcontinuous (fun p hp => (hbijective p hp).injective)
  refine ⟨C, hC, ?_⟩
  intro p hp data
  obtain ⟨x, hx⟩ := (hbijective p hp).surjective data
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · simpa only [hx] using hbound p hp x
  · intro y hy
    exact (hbijective p hp).injective (hy.1.trans hx.symm)

end

end MeyerGeneralProblem
