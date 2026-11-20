module

public import MeyerGeneralProblem.Sampling.KNSGaussianRateImprovement
public import MeyerGeneralProblem.Sampling.KNSWeightedRootSector
public import MeyerGeneralProblem.Sampling.KNSClaimThreeDecay

@[expose] public section

/-!
# A strict Gaussian-rate improvement from actual one-sided Claim 3

The sharp entire bound and the displayed angular dominance give genuine sector
growth for the weighted principal root. Actual zeros at nonnegative physical
nodes transfer to squared coordinates. Their ordered cofinal squared sequence
and eventual gap bound then give Claim 3 decay. Choosing epsilon equal to
`(d-a)*s` converts that decay to a strictly larger selected-ray Gaussian rate.

The geometric and angular compatibility inputs remain explicit. No weighted
decay, optimal-rate attainment, parity or uniqueness premise replaces them.
-/

namespace MeyerGeneralProblem

open Filter

/-- Actual sharp entire and selected-ray Gaussian bounds, numerical angular
dominance, and genuine squared-gap zeros imply a strictly improved global
Gaussian bound on the same selected physical ray. The two exceptional prefixes
remain independent. The weighted-root decay is derived, not assumed. -/
theorem exists_globalGaussian_improvement_of_sharpBounds_squaredGapZeros
    {E : ℂ → ℂ} {t : ℕ → ℝ} {sgn κ η Creal A ell d a α s : ℝ}
    (hE : Differentiable ℂ E) (hsgn : sgn = 1 ∨ sgn = -1)
    (hκ : 0 < κ) (hη : 0 < η) (hCreal : 0 ≤ Creal) (hA : 0 ≤ A)
    (hell : 0 < ell) (hd0 : 0 < d) (hdell : d < ell⁻¹)
    (ha0 : 0 ≤ a) (had : a < d)
    (hα0 : 0 < α) (hαhalf : α < Real.pi/2)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsSector : s*(Real.sin α+Real.cos α) < Real.sin α)
    (hreal : ∀ u : ℝ, 0 ≤ u →
      ‖E (((sgn*u : ℝ) : ℂ))‖ ≤ Creal*Real.exp (-2*Real.pi*κ*u^2))
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp ((Real.pi/(2*η))*z.im^2))
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*η) ≤ a*Real.sin α)
    (htmono : StrictMono (fun n => (t n)^2))
    (httop : Tendsto (fun n => (t n)^2) atTop atTop)
    (Ngap Nzero : ℕ)
    (hgap : ∀ n ≥ Ngap, (t (n+1))^2-(t n)^2 ≤ ell)
    (hzero : ∀ n ≥ Nzero, 0 ≤ t n ∧ E (((sgn*t n : ℝ) : ℂ)) = 0) :
    κ < κ+(d-a)*s/(2*Real.pi) ∧
      ∃ C₁ > 0, ∀ u : ℝ, 0 ≤ u →
        ‖E (((sgn*u : ℝ) : ℂ))‖ ≤
          C₁*Real.exp (-2*Real.pi*(κ+(d-a)*s/(2*Real.pi))*u^2) := by
  have hδ : 0 < (d-a)*s := mul_pos (sub_pos.mpr had) hs0
  refine ⟨lt_add_of_pos_right κ (div_pos hδ (by positivity)), ?_⟩
  have hGrowth := norm_knsWeightedPrincipalRoot_on_sector_le
    hE hsgn hη hCreal hA hα0 hαhalf ha0 hreal hsharp hdom ((d-a)*s) hδ
  have hZeros := knsWeightedPrincipalRoot_zero_tail sgn κ ((d-a)*s) E t Nzero hzero
  obtain ⟨X₀, hX₀, hdecay⟩ :=
    exists_eventual_exp_decay_of_sectorGrowth_eventualGapZeros
      (H := knsWeightedPrincipalRoot sgn κ ((d-a)*s) E)
      (z := fun n => (t n)^2) (M := max 1 (max Creal A)) (Rg := 0)
      hell hd0 hdell ha0 had hα0 hαhalf hs0 hs1 hsSector
      (le_max_left 1 _) (by norm_num)
      (analyticOnNhd_knsWeightedPrincipalRoot sgn κ ((d-a)*s) hE)
      (fun w hw _ => hGrowth w hw) htmono httop Ngap Nzero hgap hZeros
  apply exists_globalGaussian_improvement_of_weightedRoot_decay
    hκ hδ hCreal
    (mul_nonneg (zero_le_one.trans (le_max_left 1 _)) (Real.exp_pos _).le)
    hX₀ hreal
  intro x hx
  simpa only [mul_assoc] using hdecay x hx

end MeyerGeneralProblem
