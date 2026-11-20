module

public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-!
# Literal half-line restrictions of an atomic tempered distribution

A smooth selector changes value only in the carrier gap just below the
cut. Its two multiplied distributions have the exact original cut
coefficients regardless of the total variation of the original record.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped ContDiff Topology

/-- The exact upper half-line carrier, including the cut if it is present. -/
def LocallyFiniteCarrier.upperCut (S : LocallyFiniteCarrier) (s : ℝ) : LocallyFiniteCarrier :=
  S.restrict (S.carrier ∩ Ici s) inter_subset_left

/-- The exact lower half-line carrier, excluding the cut. -/
def LocallyFiniteCarrier.lowerCut (S : LocallyFiniteCarrier) (s : ℝ) : LocallyFiniteCarrier :=
  S.restrict (S.carrier ∩ Iio s) inter_subset_left

theorem smoothTransition_hasTemperateGrowth :
    Function.HasTemperateGrowth Real.smoothTransition := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hsupport : HasCompactSupport (fderiv ℝ Real.smoothTransition) := by
    apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
    intro x hx
    have h : x < 0 ∨ 1 < x := by
      by_cases h₀ : x < 0
      · exact Or.inl h₀
      · exact Or.inr (lt_of_not_ge fun h₁ => hx ⟨le_of_not_gt h₀, h₁⟩)
    rcases h with h | h
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [he.fderiv_eq]
      simp
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [he.fderiv_eq]
      simp
  have hder : ContDiff ℝ ∞ (fderiv ℝ Real.smoothTransition) := hs.fderiv_right (by simp)
  apply Function.HasTemperateGrowth.of_fderiv (hsupport.hasTemperateGrowth hder)
    (hs.differentiable (by simp)) (k := 0) (C := 1)
  intro x
  rw [pow_zero, mul_one, Real.norm_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem atomicHalfCut_exists_gap (S : LocallyFiniteCarrier) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S.carrier, x < s → x ≤ s - δ := by
  let P := S.restrict (S.carrier \ ({s} : Set ℝ)) sdiff_subset
  have hn : s ∈ P.carrierᶜ := by simp [P, LocallyFiniteCarrier.restrict]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (P.carrier_isClosed.isOpen_compl.mem_nhds hn)
  refine ⟨δ, hδ, fun x hx hxs => le_of_not_gt fun hlt => ?_⟩
  have hb : x ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hxs)]
    linarith
  exact hball hb ⟨hx, by simpa using hxs.ne⟩

private theorem halfCut_multiplier_coeff (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth) (x : ℝ) :
    extendedAtomicCoefficient S (TemperedDistribution.smulLeftCLM ℂ χ T) x =
      χ x * extendedAtomicCoefficient S T x := by
  classical
  by_cases hx : x ∈ S.carrier
  · rw [extendedAtomicCoefficient, dite_eq_left hx, TemperedDistribution.smulLeftCLM_apply_apply]
    rw [atomic_action_singleton_values S T hT _ x]
    · rw [SchwartzMap.smulLeftCLM_apply_apply hχ, S.isolationSchwartz_self, smul_eq_mul, mul_one]
      exact mul_comm _ _
    · intro y hy hyx
      rw [SchwartzMap.smulLeftCLM_apply_apply hχ, S.isolationSchwartz_of_mem_of_ne _ hy hyx,
        smul_zero]
  · simp [extendedAtomicCoefficient, hx]

private theorem halfCut_multiplier_atomic (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (P : Set ℝ) (hP : P ⊆ S.carrier) (χ : ℝ → ℂ) (hχ : χ.HasTemperateGrowth)
    (hzero : ∀ x ∈ S.carrier, x ∉ P → χ x = 0) :
    AtomicOnCarrier (S.restrict P hP) (TemperedDistribution.smulLeftCLM ℂ χ T) := by
  intro f hf
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  apply hT
  intro x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
  by_cases hp : x ∈ P
  · rw [hf x hp, smul_zero]
  · rw [hzero x hx hp, zero_smul]

/-- A broad atomic tempered distribution splits at an arbitrary real cut
into actual atomic tempered half-lines with the original literal coefficients. -/
theorem exists_tempered_atomic_halfCut (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) (s : ℝ) :
    ∃ P N : TemperedDistribution ℝ ℂ, P + N = T ∧
      AtomicOnCarrier (S.upperCut s) P ∧ AtomicOnCarrier (S.lowerCut s) N ∧
      (∀ x : ℝ, extendedAtomicCoefficient S P x =
        if s ≤ x then extendedAtomicCoefficient S T x else 0) ∧
      ∀ x : ℝ, extendedAtomicCoefficient S N x =
        if x < s then extendedAtomicCoefficient S T x else 0 := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := atomicHalfCut_exists_gap S s
  let g (x : ℝ) := Real.smoothTransition ((x - (s - δ)) / δ)
  let χ (x : ℝ) : ℂ := g x
  let ψ (x : ℝ) : ℂ := 1 - χ x
  have hg : g.HasTemperateGrowth := by
    simp only [g, div_eq_mul_inv]
    exact smoothTransition_hasTemperateGrowth.comp
      ((Function.HasTemperateGrowth.id'.sub (.const (s - δ))).mul (.const δ⁻¹))
  have hχ : χ.HasTemperateGrowth := Complex.ofRealCLM.hasTemperateGrowth.comp hg
  have hψ : ψ.HasTemperateGrowth := (Function.HasTemperateGrowth.const _).sub hχ
  have hχ0 (x : ℝ) (hx : x ∈ S.carrier) (hxs : x < s) : χ x = 0 := by
    have h := hgap x hx hxs
    change (g x : ℂ) = 0
    dsimp [g]
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hδ.le)]
    norm_num
  have hχ1 (x : ℝ) (hxs : s ≤ x) : χ x = 1 := by
    change (g x : ℂ) = 1
    dsimp [g]
    rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith)]
    norm_num
  let P := TemperedDistribution.smulLeftCLM ℂ χ T
  let N := TemperedDistribution.smulLeftCLM ℂ ψ T
  have hadd : P + N = T := by
    ext f
    simp only [P, N, _root_.add_apply, TemperedDistribution.smulLeftCLM_apply_apply, ← map_add]
    congr 1
    ext x
    simp only [_root_.add_apply, SchwartzMap.smulLeftCLM_apply_apply hχ,
      SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul, ψ]
    ring
  have hP : AtomicOnCarrier (S.upperCut s) P :=
    halfCut_multiplier_atomic S T hT _ inter_subset_left χ hχ fun x hx h => by
      exact hχ0 x hx (lt_of_not_ge fun hs => h ⟨hx, hs⟩)
  have hN : AtomicOnCarrier (S.lowerCut s) N :=
    halfCut_multiplier_atomic S T hT _ inter_subset_left ψ hψ fun x hx h => by
      dsimp [ψ]
      rw [hχ1 x (le_of_not_gt fun hs => h ⟨hx, hs⟩), sub_self]
  refine ⟨P, N, hadd, hP, hN, ?_, ?_⟩
  · intro x
    rw [halfCut_multiplier_coeff S T hT χ hχ]
    by_cases hx : x ∈ S.carrier
    · by_cases hs : s ≤ x
      · rw [hχ1 x hs, ite_eq_left hs, one_mul]
      · rw [hχ0 x hx (lt_of_not_ge hs), ite_eq_right hs, zero_mul]
    · simp [extendedAtomicCoefficient, hx]
  · intro x
    rw [halfCut_multiplier_coeff S T hT ψ hψ]
    by_cases hx : x ∈ S.carrier
    · by_cases hs : x < s
      · simp [ψ, hχ0 x hx hs, hs]
      · simp [ψ, hχ1 x (le_of_not_gt hs), hs]
    · simp [extendedAtomicCoefficient, hx]

end

end MeyerGeneralProblem
