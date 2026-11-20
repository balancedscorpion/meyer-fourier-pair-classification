module

public import MeyerGeneralProblem.Sampling.KNSStageBRecurrence

@[expose] public section

/-!
# Order-independent parameters for the quantitative KNS bootstrap

The geometric contraction depends only on the strict reciprocal-gap
margin. The cutoff width is the square root of the order; the central
radius affects only the starting order, never the factorial base.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

/-- The explicit exterior-to-cutoff ratio determined by the reciprocal
gap margin, before the function or central radius is chosen. -/
def knsStageBK (ρ : ℝ) : ℝ := 4/(1-2*ρ)

/-- The reciprocal-gap Poincare scale corresponding to rho. -/
def knsStageBSigma (ρ : ℝ) : ℝ := 1/(2*ρ)

/-- The exact moment contraction after the physical and frequency splits. -/
def knsStageBR (ρ : ℝ) : ℝ :=
  (knsStageBK ρ+1)/(knsStageBSigma ρ*(knsStageBK ρ-3))

/-- The explicit factorial base, fixed by rho alone. Its eventual moment
bound is established by composition, not by this definition. -/
def knsStageBFactorialBase (ρ : ℝ) : ℝ :=
  12*Real.exp 1*(knsStageBK ρ+1)^2

/-- The explicit choice has a strict contraction and the exact squared
margin. In particular the discarded frequency prefactor is at most one. -/
theorem knsStageB_parameters {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    4 < knsStageBK ρ ∧ 1 < knsStageBSigma ρ ∧
      knsStageBK ρ ≤ knsStageBSigma ρ*(knsStageBK ρ-3) ∧
      0 < knsStageBR ρ ∧ knsStageBR ρ < 1 ∧
      knsStageBR ρ = 2*ρ*(5-2*ρ)/(1+6*ρ) ∧
      1-knsStageBR ρ = (1-2*ρ)^2/(1+6*ρ) := by
  have hd : 0 < 1-2*ρ := by linarith
  have h2ρ : 0 < 2*ρ := by positivity
  have he : 0 < 1+6*ρ := by positivity
  have hK : 4 < knsStageBK ρ := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have hσ : 1 < knsStageBSigma ρ := by
    apply (lt_div_iff₀ h2ρ).mpr
    linarith
  have hden : 0 < knsStageBSigma ρ*(knsStageBK ρ-3) := mul_pos (by linarith) (by linarith)
  have hrform : knsStageBR ρ = 2*ρ*(5-2*ρ)/(1+6*ρ) := by
    have hKeq : knsStageBK ρ*(1-2*ρ)=4 := by dsimp only [knsStageBK]; field_simp
    have hσeq : knsStageBSigma ρ*(2*ρ)=1 := by dsimp only [knsStageBSigma]; field_simp
    apply (div_eq_div_iff hden.ne' he.ne').mpr
    calc
      (knsStageBK ρ+1)*(1+6*ρ) = (5-2*ρ)*(knsStageBK ρ-3) := by nlinarith [hKeq]
      _ = (knsStageBSigma ρ*(2*ρ))*((5-2*ρ)*(knsStageBK ρ-3)) := by rw [hσeq,one_mul]
      _ = _ := by ring
  have hmargin : 1-knsStageBR ρ = (1-2*ρ)^2/(1+6*ρ) := by
    rw [hrform]
    field_simp
    ring
  have hr0 : 0 < knsStageBR ρ := by
    rw [hrform]
    exact div_pos (mul_pos h2ρ (by linarith)) he
  have hr1 : knsStageBR ρ < 1 := by
    have hpos : 0 < (1-2*ρ)^2/(1+6*ρ) := div_pos (sq_pos_of_pos hd) he
    linarith
  have hKmargin : knsStageBK ρ ≤ knsStageBSigma ρ*(knsStageBK ρ-3) := by
    have h := (div_lt_one hden).mp hr1
    linarith
  exact ⟨hK,hσ,hKmargin,hr0,hr1,hrform,hmargin⟩

/-- The pointwise gap threshold becomes precisely rho under the chosen
sigma, with no hidden loss in the Fourier normalization. -/
theorem knsStageBSigma_reciprocal {ρ : ℝ} (hρ : 0 < ρ) :
    (2*knsStageBSigma ρ)⁻¹ = ρ := by
  dsimp only [knsStageBSigma]
  field_simp

/-- At cutoff width square-root n, both displayed order errors have
the identical n-to-the-n size. -/
theorem knsStageB_sqrt_order {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.sqrt (n : ℝ) ∧
      (Real.sqrt (n : ℝ))^(2*n)=(n : ℝ)^n ∧
      ((n : ℝ)/Real.sqrt (n : ℝ))^(2*n)=(n : ℝ)^n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq := Real.sq_sqrt hn0.le
  have he : (n : ℝ)/Real.sqrt (n : ℝ)=Real.sqrt (n : ℝ) := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith
  refine ⟨hs,?_,?_⟩
  · rw [pow_mul,hsq]
  · rw [he,pow_mul,hsq]

/-- The nth nonnegative term of the exponential series gives the exact
n-to-the-n versus factorial bound, including order zero. -/
theorem knsStageB_order_le_factorial (n : ℕ) :
    (n : ℝ)^n ≤ (Real.exp 1)^n*(n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
  simpa only [← Real.exp_nat_mul,mul_one] using h

/-- The geometric-series contraction and a given central radius hold
simultaneously from one starting order. The factorial base is unaffected. -/
theorem exists_knsStageB_starting_order {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (R : ℝ) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0, R ≤ Real.sqrt (n : ℝ) ∧ 2*r^(2*n) ≤ 1/2 := by
  have hr2 : r^2 < 1 := by nlinarith
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg r) hr2
  have hevent : ∀ᶠ n : ℕ in atTop, (r^2)^n < (1/4 : ℝ) :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  obtain ⟨L,hL⟩ := exists_nat_ge ((max R 0)^2)
  let n0 := max 2 (max N L)
  refine ⟨n0,le_max_left _ _,?_⟩
  intro n hn
  have hNn : N ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hLn : L ≤ n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  constructor
  · have hRn : (max R 0)^2 ≤ (n : ℝ) := hL.trans (by exact_mod_cast hLn)
    have hs : max R 0 ≤ Real.sqrt (n : ℝ) :=
      (Real.le_sqrt (le_max_right _ _) (Nat.cast_nonneg n)).mpr hRn
    exact (le_max_left _ _).trans hs
  · have h := hN n hNn
    rw [← pow_mul] at h
    linarith

end

end MeyerGeneralProblem
