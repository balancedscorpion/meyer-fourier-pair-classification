module

public import MeyerGeneralProblem.Sampling.KNSGraphSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-!
# Exact L2 bounds for actual pointwise limits

Fatou's inequality derives the limit L2 membership and retains the exact
converging norm bound. No L2 membership of the limit is assumed.
-/

namespace MeyerGeneralProblem.L2LimitBound
noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- A pointwise almost-everywhere limit inherits a converging actual L2 norm bound. -/
theorem exists_memLp_norm_le_of_tendsto {u : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hu : ∀ n, MemLp (u n) 2) (hf : AEStronglyMeasurable f volume)
    {b : ℕ → ℝ} {B : ℝ} (hB : 0≤B)
    (hb : Tendsto b atTop (𝓝 B)) (hn : ∀ n, ‖(hu n).toLp‖ ≤ b n)
    (hlim : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ∃ hF : MemLp f 2, ‖hF.toLp‖ ≤ B := by
  have he (n : ℕ) : eLpNorm (u n) 2 volume ≤ ENNReal.ofReal (b n) := by
    rw [← Lp.enorm_toLp (hu n), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn n)
  have ht : Tendsto (fun n => ENNReal.ofReal (b n)) atTop (𝓝 (ENNReal.ofReal B)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  have hfB : eLpNorm f 2 volume ≤ ENNReal.ofReal B := by
    calc
      _ ≤ atTop.liminf (fun n => eLpNorm (u n) 2 volume) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hu n).aestronglyMeasurable) f hf hlim
      _ ≤ atTop.liminf (fun n => ENNReal.ofReal (b n)) :=
        liminf_le_liminf (Eventually.of_forall he)
      _ = _ := ht.liminf_eq
  have hF : MemLp f 2 := hfB.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hF, ?_⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfB).trans_eq (ENNReal.toReal_ofReal hB)

/-- Squared L2 estimates pass to the actual pointwise limit with the exact
constant and a converging input norm, not a bounded abstract surrogate. -/
theorem exists_memLp_sq_le_of_tendsto {u : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hu : ∀ n, MemLp (u n) 2) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0≤C) {b : ℕ → ℝ} {B : ℝ} (hB : 0≤B)
    (hb0 : ∀ n, 0≤b n) (hb : Tendsto b atTop (𝓝 B))
    (hn : ∀ n, ‖(hu n).toLp‖^2 ≤ C * (b n)^2)
    (hlim : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ∃ hF : MemLp f 2, ‖hF.toLp‖^2 ≤ C*B^2 := by
  have hn' (n : ℕ) : ‖(hu n).toLp‖ ≤ Real.sqrt C * b n := by
    have hs := Real.sq_sqrt hC
    have hp : 0≤Real.sqrt C * b n := mul_nonneg (Real.sqrt_nonneg C) (hb0 n)
    nlinarith [hn n, norm_nonneg (hu n).toLp, sq_nonneg (‖(hu n).toLp‖ + Real.sqrt C*b n)]
  obtain ⟨hF, hbF⟩ := exists_memLp_norm_le_of_tendsto hu hf
    (mul_nonneg (Real.sqrt_nonneg C) hB) (hb.const_mul (Real.sqrt C)) hn' hlim
  refine ⟨hF, ?_⟩
  calc
    _ ≤ (Real.sqrt C*B)^2 := pow_le_pow_left₀ (norm_nonneg _) hbF 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hC]
end
end MeyerGeneralProblem.L2LimitBound
