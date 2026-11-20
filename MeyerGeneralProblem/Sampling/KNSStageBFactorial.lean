module

public import MeyerGeneralProblem.Sampling.KNSStageBParameters

@[expose] public section

/-!
# Actual eventual factorial moment bound for KNS Fourier pairs

The proved localized one-row inequalities are coupled only after Stage A
has supplied finite moments. The cutoff width is square-root n. The base
depends solely on the strict reciprocal-gap margin; the finite deletions
and central geometry affect the starting order alone.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff

/-- The explicit factorial base is strictly positive throughout the
strict reciprocal-gap range. -/
theorem knsStageBFactorialBase_pos {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    0 < knsStageBFactorialBase ρ := by
  have hK := (knsStageB_parameters hρ hρhalf).1
  dsimp only [knsStageBFactorialBase]
  positivity

private theorem kns_factorial_numeric_bound {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hn : 1 ≤ n) :
    12*(K+1)^(2*n)*(n : ℝ)^n ≤
      (12*Real.exp 1*(K+1)^2)^n*(n.factorial : ℝ) := by
  have h12 : (12 : ℝ) ≤ 12^n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤12) hn
  have he := knsStageB_order_le_factorial n
  have hfirst := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 12*(K+1)^(2*n))
  have hsecond := mul_le_mul_of_nonneg_right h12
    (by positivity : 0 ≤ (K+1)^(2*n)*(Real.exp 1)^n*(n.factorial : ℝ))
  calc
    _ ≤ 12*(K+1)^(2*n)*((Real.exp 1)^n*(n.factorial : ℝ)) := hfirst
    _ ≤ 12^n*((K+1)^(2*n)*(Real.exp 1)^n*(n.factorial : ℝ)) := by nlinarith
    _ = _ := by simp only [mul_pow,← pow_mul]; ring

private theorem kns_ofReal_oneRow_to_real {X Y M c E : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (h : ENNReal.ofReal X ≤ ENNReal.ofReal c*ENNReal.ofReal Y +
      ENNReal.ofReal E*ENNReal.ofReal M) : X ≤ c*Y+E*M := by
  have he : ENNReal.ofReal (c*Y+E*M) =
      ENNReal.ofReal c*ENNReal.ofReal Y+ENNReal.ofReal E*ENNReal.ofReal M := by
    rw [ENNReal.ofReal_add (mul_nonneg hc hY) (mul_nonneg hE hM),
      ENNReal.ofReal_mul hc,ENNReal.ofReal_mul hE]
  rw [← he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hc hY) (mul_nonneg hE hM))).mp h

/-- The quantitative KNS bootstrap for an actual classical Fourier pair.
Its explicit factorial base depends only on rho. A common starting order
is selected before f; higher moments are obtained from Stage A, never
assumed in place of the localized recurrence. -/
theorem knsStageB_eventual_factorialMoments
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (Λ M : TwoSidedCarrier) (F J G L : Finset ℤ)
    (hgapΛ : ∀ j : ℤ, j ∉ J → max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ ρ)
    (hgapM : ∀ j : ℤ, j ∉ L → max |M j| |M (j+1)| * (M (j+1)-M j) ≤ ρ) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → ContDiff ℝ 1 (𝓕 f) →
      Integrable f → Integrable (𝓕 f) → MemLp f 2 →
      Integrable (fun x => x^2*‖f x‖^2) → Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2) →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → (∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) →
      ∀ n ≥ n0,
      (∫ x, x^(2*n)*‖f x‖^2) + (∫ ξ, ξ^(2*n)*‖𝓕 f ξ‖^2) ≤
        (knsStageBFactorialBase ρ)^n*(n.factorial : ℝ)*(∫ x, ‖f x‖^2) := by
  obtain ⟨hK,hσ,hmargin,hr0,hr1,_,_⟩ := knsStageB_parameters hρ hρhalf
  let K := knsStageBK ρ
  let σ := knsStageBSigma ρ
  let r := knsStageBR ρ
  have hσ0 : 0 < σ := by dsimp only [σ]; linarith
  have hgΛ : ∀ j : ℤ, j ∉ J → max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹ := by
    simpa only [σ,knsStageBSigma_reciprocal hρ] using hgapΛ
  have hgM : ∀ j : ℤ, j ∉ L → max |M j| |M (j+1)| * (M (j+1)-M j) ≤ (2*σ)⁻¹ := by
    simpa only [σ,knsStageBSigma_reciprocal hρ] using hgapM
  obtain ⟨R,hR,hΛ⟩ := exists_radius_knsStageB_oneRow Λ F J hσ0 hgΛ
  obtain ⟨S,hS,hM⟩ := exists_radius_knsStageB_oneRow M G L hσ0 hgM
  obtain ⟨n0,hn0,hstart⟩ := exists_knsStageB_starting_order hr0.le hr1 (max R S)
  refine ⟨n0,hn0,?_⟩
  intro f hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM n hn
  have hn2 : 2 ≤ n := hn0.trans hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu0,husq,hnsq⟩ := knsStageB_sqrt_order hn1
  obtain ⟨hwidth,hcontract⟩ := hstart n hn
  let u := Real.sqrt (n : ℝ)
  have hRu : R ≤ u := (le_max_left _ _).trans hwidth
  have hSu : S ≤ u := (le_max_right _ _).trans hwidth
  have hF2 := (memLp_fourier_norm_eq_of_integrable hf1 hf2).1
  have h1 := hΛ K hK hmargin n hn2 u hRu f hf hf1 hf2 hzΛ
  have h2 := hM K hK hmargin n hn2 u hSu (𝓕 f) hF hF1 hF2 hzM
  rw [knsPowerEnergy_fourier_fourier hf.continuous hf1 hF1,
    lintegral_knsFourier_squareMass hf1 hf2] at h2
  obtain ⟨hphys,hfreq⟩ := knsStageA_all_squareMoments Λ M F J G L hσ hgΛ hgM
    hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM n
  rw [knsPowerEnergy_eq_ofReal_integral n hphys,knsPowerEnergy_eq_ofReal_integral n hfreq,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp_complex hf2)
      (Eventually.of_forall (fun _ => sq_nonneg _))] at h1 h2
  let X := ∫ x, x^(2*n)*‖f x‖^2
  let Y := ∫ ξ, ξ^(2*n)*‖𝓕 f ξ‖^2
  let Z := ∫ x, ‖f x‖^2
  let c := 2*r^(2*n)
  let E := K^(2*n)*u^(2*n)+2*(K+1)^(2*n)*((n:ℝ)/u)^(2*n)
  let Q := (K+1)^(2*n)*(n:ℝ)^n
  have hK0 : 0 ≤ K := by dsimp only [K]; linarith
  have hX : 0 ≤ X := integral_nonneg (fun x => mul_nonneg
    (show 0 ≤ x^(2*n) by rw [pow_mul]; positivity) (sq_nonneg _))
  have hY : 0 ≤ Y := integral_nonneg (fun ξ => mul_nonneg
    (show 0 ≤ ξ^(2*n) by rw [pow_mul]; positivity) (sq_nonneg _))
  have hZ : 0 ≤ Z := integral_nonneg (fun _ => sq_nonneg _)
  have hc : 0 ≤ c := by dsimp only [c,r]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have h1r : X ≤ c*Y+E*Z := kns_ofReal_oneRow_to_real hY hZ hc hE h1
  have h2r : Y ≤ c*X+E*Z := kns_ofReal_oneRow_to_real hX hZ hc hE h2
  have hEbound : E ≤ 3*Q := by
    dsimp only [E,Q,u]
    rw [husq,hnsq]
    have hp := pow_le_pow_left₀ hK0 (show K ≤ K+1 by linarith) (2*n)
    have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (n:ℝ)^n)
    nlinarith
  have hsum : X+Y ≤ 12*Q*Z := by
    have hx := mul_le_mul_of_nonneg_right hcontract hX
    have hy := mul_le_mul_of_nonneg_right hcontract hY
    have he := mul_le_mul_of_nonneg_right hEbound hZ
    change c*X ≤ (1/2:ℝ)*X at hx
    change c*Y ≤ (1/2:ℝ)*Y at hy
    nlinarith
  have hfact := mul_le_mul_of_nonneg_right (kns_factorial_numeric_bound hK0 hn1) hZ
  change X+Y ≤ (knsStageBFactorialBase ρ)^n*(n.factorial : ℝ)*Z
  apply hsum.trans
  convert! hfact using 1
  dsimp only [Q,K,knsStageBFactorialBase]
  ring

end

end MeyerGeneralProblem
