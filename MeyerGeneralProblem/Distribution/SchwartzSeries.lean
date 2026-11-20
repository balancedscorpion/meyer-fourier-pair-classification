module

public import MeyerGeneralProblem.Distribution.IntegerComb
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Actual continuous Schwartz series with a common seminorm bound

A summable numerical majorant against one continuous Schwartz seminorm
constructs the continuous functional itself. Fourier and inverse Fourier
identities are proved on the actual test series, without interchanging
uncontrolled physical coefficient sums.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform NNReal

/-- A common seminorm and a summable coefficient bound imply absolute
summability of the actual scalar actions on every Schwartz test. -/
theorem summable_schwartzSeries_actions
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (b : ℕ → ℝ) (hb : Summable b)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n => T n f) :=
  Summable.of_norm_bounded (hb.mul_right (p f)) (fun n => hT n f)

/-- The actual scalar series is bounded by the summed numerical majorant
times the same seminorm; no varying seminorms are introduced. -/
theorem norm_schwartzSeries_sum_le
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (b : ℕ → ℝ) (hb : Summable b)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    ‖∑' n, T n f‖ ≤ (∑' n, b n)*p f := by
  have hs := summable_schwartzSeries_actions T p b hb hT f
  calc
    _ ≤ ∑' n, ‖T n f‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n, b n*p f := hs.norm.tsum_le_tsum (fun n => hT n f) (hb.mul_right _)
    _ = _ := tsum_mul_right

/-- The actual series as a bounded complex-linear Schwartz functional.
Continuity follows from the given continuous seminorm, reduced to finitely
many standard Schwartz seminorms by the proved topology theorem. -/
def schwartzSeriesCLM
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => ∑' n, T n f)
    (fun f g => by
      simp only [map_add]
      exact (summable_schwartzSeries_actions T p b hb hT f).tsum_add
        (summable_schwartzSeries_actions T p b hb hT g))
    (fun a f => by
      simp only [map_smul, RingHom.id_apply, smul_eq_mul]
      exact tsum_mul_left)
    (by
      obtain ⟨s,C,_,hC⟩ := Seminorm.bound_of_continuous
        (schwartz_withSeminorms ℂ ℝ ℂ) p hp
      have hsum : 0 ≤ ∑' n, b n := tsum_nonneg hb0
      refine ⟨s,(∑' n, b n)*(C:ℝ),mul_nonneg hsum C.coe_nonneg,fun f => ?_⟩
      apply (norm_schwartzSeries_sum_le T p b hb hT f).trans
      have h := mul_le_mul_of_nonneg_left (hC f) hsum
      simpa only [smul_apply,NNReal.smul_def,smul_eq_mul,mul_assoc] using h)

/-- A genuine tempered distribution defined by the convergent scalar
series, with continuity proved rather than assumed. -/
def schwartzSeries
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) : TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (SchwartzMap ℝ ℂ) ℂ (schwartzSeriesCLM T p hp b hb hb0 hT)

/-- Exact action of the constructed series on every Schwartz test. -/
theorem schwartzSeries_apply
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    schwartzSeries T p hp b hb hb0 hT f = ∑' n, T n f := rfl

/-- Fourier acts on the constructed series by the actual transformed
test; each scalar series is absolutely convergent. -/
theorem fourier_schwartzSeries_apply
    (T : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hT : ∀ n f, ‖T n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    𝓕 (schwartzSeries T p hp b hb hb0 hT) f = ∑' n, 𝓕 (T n) f := rfl

/-- Define the physical distribution from its proved continuous Fourier
series. This uses genuine inverse Fourier, equivalent to the third power. -/
def inverseFourierSchwartzSeries
    (Q : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hQ : ∀ n f, ‖Q n f‖ ≤ b n*p f) : TemperedDistribution ℝ ℂ :=
  𝓕⁻ (schwartzSeries Q p hp b hb hb0 hQ)

/-- The physical inverse has exactly the constructed spectral sum as
its Fourier transform, with no extra existence certificate. -/
theorem fourier_inverseFourierSchwartzSeries
    (Q : ℕ → TemperedDistribution ℝ ℂ) (p : Seminorm ℂ (SchwartzMap ℝ ℂ))
    (hp : Continuous p) (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hQ : ∀ n f, ‖Q n f‖ ≤ b n*p f) :
    𝓕 (inverseFourierSchwartzSeries Q p hp b hb hb0 hQ) =
      schwartzSeries Q p hp b hb hb0 hQ :=
  FourierTransform.fourier_fourierInv_eq _

/-- Genuine block Fourier identities identify the inverse distribution
with the actual physical scalar series on every Schwartz test. -/
theorem inverseFourierSchwartzSeries_apply
    (P Q : ℕ → TemperedDistribution ℝ ℂ) (hPQ : ∀ n, 𝓕 (P n)=Q n)
    (p : Seminorm ℂ (SchwartzMap ℝ ℂ)) (hp : Continuous p)
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hQ : ∀ n f, ‖Q n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    inverseFourierSchwartzSeries Q p hp b hb hb0 hQ f = ∑' n, P n f := by
  change (∑' n, Q n (𝓕⁻ f)) = _
  apply tsum_congr
  intro n
  rw [← hPQ n,TemperedDistribution.fourier_apply,FourierTransform.fourier_fourierInv_eq]

/-- Absolute summability of physical block actions follows from the
spectral majorant at the fixed inverse-Fourier test, not from absolute
summability of all individual physical atom moduli. -/
theorem summable_physical_actions_of_fourier_bound
    (P Q : ℕ → TemperedDistribution ℝ ℂ) (hPQ : ∀ n, 𝓕 (P n)=Q n)
    (p : Seminorm ℂ (SchwartzMap ℝ ℂ)) (b : ℕ → ℝ) (hb : Summable b)
    (hQ : ∀ n f, ‖Q n f‖ ≤ b n*p f) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n => P n f) := by
  have h := summable_schwartzSeries_actions Q p b hb hQ (𝓕⁻ f)
  simpa only [← hPQ,TemperedDistribution.fourier_apply,FourierTransform.fourier_fourierInv_eq] using h

/-- The deliberately non-sharp square scale loss remains summable against
the geometric coefficient ceiling, after any finite initial size shift. -/
theorem summable_square_geometric_shift (k : ℕ) :
    Summable (fun n : ℕ => (((n+k : ℕ) : ℝ)^2)*((2:ℝ)^(n+k))⁻¹) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := (2:ℝ)⁻¹) (by norm_num)
  simpa only [inv_pow] using (summable_nat_add_iff k).2 h

end

end MeyerGeneralProblem
