module

public import MeyerGeneralProblem.Gram.GroupedMixedDerivativeBounds
public import MeyerGeneralProblem.Hermite.Exhaustion
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

@[expose] public section

/-!
# Higher Hermite jet estimates for grouped kernels

The exact Hermite ladder is used with squared spectral weights: each
physical derivative costs one unit of the squared spectral exponent,
not an entire Hermite order. This distinction is necessary for a
same-order weighted estimate after signed-square pullback.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- The actual iterated derivative of a normalized Hermite Schwartz map. -/
def groupedHermiteJet : ℕ → ℕ → SchwartzMap ℝ ℂ
  | 0, n => normalizedHermiteSchwartz n
  | i+1, n => SchwartzMap.derivCLM ℂ ℂ (groupedHermiteJet i n)

theorem groupedHermiteJet_apply (i n : ℕ) (x : ℝ) :
    groupedHermiteJet i n x = iteratedDeriv i (normalizedHermiteSchwartz n) x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [groupedHermiteJet, SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
    congr 1
    exact funext ih

/-- The original ladder commutes with every further Schwartz derivative. -/
theorem groupedHermiteJet_ladder (i n : ℕ) :
    groupedHermiteJet (i+1) n = hermiteDerivativeDown n • groupedHermiteJet i (n-1) -
      hermiteDerivativeUp n • groupedHermiteJet i (n+1) := by
  induction i with
  | zero => exact deriv_normalizedHermiteSchwartz n
  | succ i ih =>
    change SchwartzMap.derivCLM ℂ ℂ (groupedHermiteJet (i+1) n) = _
    rw [ih, map_sub, map_smul, map_smul]
    rfl

theorem norm_hermiteDerivativeDown_sq (n : ℕ) :
    ‖hermiteDerivativeDown n‖^2 = Real.pi*(n:ℝ) := by
  rw [hermiteDerivativeDown, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

theorem norm_hermiteDerivativeUp_sq (n : ℕ) :
    ‖hermiteDerivativeUp n‖^2 = Real.pi*((n:ℝ)+1) := by
  rw [hermiteDerivativeUp, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

theorem norm_groupedHermiteJet_succ_sq_le (i n : ℕ) (x : ℝ) :
    ‖groupedHermiteJet (i+1) n x‖^2 ≤ 2*Real.pi*
      ((n:ℝ)*‖groupedHermiteJet i (n-1) x‖^2 +
        ((n:ℝ)+1)*‖groupedHermiteJet i (n+1) x‖^2) := by
  rw [groupedHermiteJet_ladder]
  change ‖hermiteDerivativeDown n * groupedHermiteJet i (n-1) x -
    hermiteDerivativeUp n * groupedHermiteJet i (n+1) x‖^2 ≤ _
  have hnorm := norm_sub_le (hermiteDerivativeDown n * groupedHermiteJet i (n-1) x)
    (hermiteDerivativeUp n * groupedHermiteJet i (n+1) x)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have hdiff := sq_nonneg (‖hermiteDerivativeDown n * groupedHermiteJet i (n-1) x‖ -
    ‖hermiteDerivativeUp n * groupedHermiteJet i (n+1) x‖)
  have hA : ‖hermiteDerivativeDown n * groupedHermiteJet i (n-1) x‖^2 =
      Real.pi*(n:ℝ)*‖groupedHermiteJet i (n-1) x‖^2 := by
    rw [norm_mul, mul_pow, norm_hermiteDerivativeDown_sq]
  have hB : ‖hermiteDerivativeUp n * groupedHermiteJet i (n+1) x‖^2 =
      Real.pi*((n:ℝ)+1)*‖groupedHermiteJet i (n+1) x‖^2 := by
    rw [norm_mul, mul_pow, norm_hermiteDerivativeUp_sq]
  nlinarith

/-- Squared jet coefficients with integer squared-weight exponent `k`. -/
def groupedHermiteJetEnergyTerm (k i : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (((n:ℝ)+1)⁻¹)^k * ‖groupedHermiteJet i n x‖^2

theorem groupedHermiteJetEnergyTerm_nonneg (k i : ℕ) (x : ℝ) (n : ℕ) :
    0 ≤ groupedHermiteJetEnergyTerm k i x n := by
  unfold groupedHermiteJetEnergyTerm
  positivity

theorem grouped_hermite_weight_pred_bound (k n : ℕ) :
    (((n:ℝ)+1)⁻¹)^(k+1)*(n:ℝ) ≤ ((((n-1:ℕ):ℝ)+1)⁻¹)^k := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hbase : ((n:ℝ)+2)⁻¹ ≤ ((n:ℝ)+1)⁻¹ :=
      (inv_le_inv₀ (by positivity) hn).mpr (by linarith)
    have hsmall : ((n:ℝ)+2)⁻¹*((n:ℝ)+1) ≤ 1 := by
      apply (inv_mul_le_one₀ (by positivity)).mpr
      linarith
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring, pow_succ, mul_assoc]
    calc
      _ ≤ (((n:ℝ)+2)⁻¹)^k * 1 :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ _ := by rw [mul_one]; exact pow_le_pow_left₀ (by positivity) hbase k

theorem grouped_hermite_weight_succ_bound (k n : ℕ) :
    (((n:ℝ)+1)⁻¹)^(k+1)*((n:ℝ)+1) ≤
      (2:ℝ)^k * ((((n+1:ℕ):ℝ)+1)⁻¹)^k := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hbase : ((n:ℝ)+1)⁻¹ ≤ 2*((n:ℝ)+2)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hn (by positivity)).mpr
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [pow_succ, mul_assoc, inv_mul_cancel₀ hn.ne', mul_one]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hbase k

/-- Each differentiation loses exactly one squared spectral exponent,
with both spectral shifts kept explicit. -/
theorem groupedHermiteJetEnergyTerm_step_le (k i n : ℕ) (x : ℝ) :
    groupedHermiteJetEnergyTerm (k+1) (i+1) x n ≤
      2*Real.pi*(groupedHermiteJetEnergyTerm k i x (n-1) +
        (2:ℝ)^k*groupedHermiteJetEnergyTerm k i x (n+1)) := by
  have h := mul_le_mul_of_nonneg_left (norm_groupedHermiteJet_succ_sq_le i n x)
    (show 0 ≤ (((n:ℝ)+1)⁻¹)^(k+1) by positivity)
  unfold groupedHermiteJetEnergyTerm at *
  calc
    _ ≤ (((n:ℝ)+1)⁻¹)^(k+1) * (2*Real.pi*
        ((n:ℝ)*‖groupedHermiteJet i (n-1) x‖^2 +
          ((n:ℝ)+1)*‖groupedHermiteJet i (n+1) x‖^2)) := h
    _ = 2*Real.pi*(((((n:ℝ)+1)⁻¹)^(k+1)*(n:ℝ))*‖groupedHermiteJet i (n-1) x‖^2 +
        ((((n:ℝ)+1)⁻¹)^(k+1)*((n:ℝ)+1))*‖groupedHermiteJet i (n+1) x‖^2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (grouped_hermite_weight_pred_bound k n) (sq_nonneg _)
      · simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (grouped_hermite_weight_succ_bound k n) (sq_nonneg _)

/-- Total squared spectral energy of an actual Hermite jet. -/
def groupedHermiteJetEnergy (k i : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, groupedHermiteJetEnergyTerm k i x n

theorem groupedHermiteJetEnergy_nonneg (k i : ℕ) (x : ℝ) :
    0 ≤ groupedHermiteJetEnergy k i x :=
  tsum_nonneg (groupedHermiteJetEnergyTerm_nonneg k i x)

theorem groupedHermiteJetEnergyTerm_even_zero (m n : ℕ) (x : ℝ) :
    groupedHermiteJetEnergyTerm (2*m) 0 x n = ‖hermiteDiracCoefficients m x n‖^2 := by
  simp only [groupedHermiteJetEnergyTerm, groupedHermiteJet,
    hermiteDiracCoefficients, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    hermiteScaleWeight, zpow_neg, zpow_natCast, ← inv_pow,
    abs_of_nonneg (by positivity : 0 ≤ (((n:ℝ)+1)⁻¹)^m), mul_pow, ← pow_mul]
  rw [Nat.mul_comm m 2]

theorem groupedHermiteJetEnergy_even_zero (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    groupedHermiteJetEnergy (2*m) 0 x = ‖hermitePointMass m hm x‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal)
    (hermitePointMass m hm x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hermitePointMass_apply] at h
  unfold groupedHermiteJetEnergy
  simp_rw [groupedHermiteJetEnergyTerm_even_zero]
  exact h.symm

theorem summable_groupedHermiteJetEnergyTerm_zero (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    Summable (groupedHermiteJetEnergyTerm k 0 x) := by
  have hs : Summable (fun n => ‖hermiteDiracCoefficients 1 x n‖^2) := by
    have h := hermiteDiracCoefficients_memℓp 1 (by omega) x
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)] at h
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  apply hs.of_nonneg_of_le (groupedHermiteJetEnergyTerm_nonneg k 0 x)
  intro n
  rw [← groupedHermiteJetEnergyTerm_even_zero]
  unfold groupedHermiteJetEnergyTerm
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity
  have hb1 : ((n:ℝ)+1)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact pow_le_pow_of_le_one hb hb1 hk

theorem grouped_summable_pred {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n => f (n-1)) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_sub_cancel] using hf

theorem grouped_tsum_succ_le {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) :
    (∑' n : ℕ, f (n+1)) ≤ ∑' n : ℕ, f n := by
  have h := hf.tsum_eq_zero_add
  linarith [h0 0]

theorem grouped_tsum_pred_le {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) :
    (∑' n : ℕ, f (n-1)) ≤ 2 * ∑' n : ℕ, f n := by
  rw [(grouped_summable_pred hf).tsum_eq_zero_add]
  simp only [Nat.zero_sub, Nat.add_sub_cancel]
  have h := hf.le_tsum 0 (fun n hn => h0 n)
  linarith

/-- Summability and the total-energy step follow from the actual ladder,
with the predecessor's single repeated zero coordinate counted. -/
theorem groupedHermiteJetEnergy_step (k i : ℕ) (x : ℝ)
    (h : Summable (groupedHermiteJetEnergyTerm k i x)) :
    Summable (groupedHermiteJetEnergyTerm (k+1) (i+1) x) ∧
      groupedHermiteJetEnergy (k+1) (i+1) x ≤
        (2*Real.pi*(2+(2:ℝ)^k))*groupedHermiteJetEnergy k i x := by
  have hpred := grouped_summable_pred h
  have hsucc := (summable_nat_add_iff 1).mpr h
  have hB := (hpred.add (hsucc.mul_left ((2:ℝ)^k))).mul_left (2*Real.pi)
  have hnext := hB.of_nonneg_of_le (groupedHermiteJetEnergyTerm_nonneg (k+1) (i+1) x)
    (fun n => groupedHermiteJetEnergyTerm_step_le k i n x)
  refine ⟨hnext, ?_⟩
  unfold groupedHermiteJetEnergy
  calc
    _ ≤ ∑' n : ℕ, 2*Real.pi*(groupedHermiteJetEnergyTerm k i x (n-1) +
        (2:ℝ)^k*groupedHermiteJetEnergyTerm k i x (n+1)) :=
      hnext.tsum_le_tsum (fun n => groupedHermiteJetEnergyTerm_step_le k i n x) hB
    _ = 2*Real.pi*((∑' n : ℕ, groupedHermiteJetEnergyTerm k i x (n-1)) +
        (2:ℝ)^k*(∑' n : ℕ, groupedHermiteJetEnergyTerm k i x (n+1))) := by
      rw [tsum_mul_left, hpred.tsum_add (hsucc.mul_left _), tsum_mul_left]
    _ ≤ 2*Real.pi*(2*(∑' n : ℕ, groupedHermiteJetEnergyTerm k i x n) +
        (2:ℝ)^k*(∑' n : ℕ, groupedHermiteJetEnergyTerm k i x n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (grouped_tsum_pred_le h (groupedHermiteJetEnergyTerm_nonneg k i x))
        (mul_le_mul_of_nonneg_left (grouped_tsum_succ_le h
          (groupedHermiteJetEnergyTerm_nonneg k i x)) (by positivity))
    _ = _ := by ring

/-- Explicit constant accumulated by the squared-weight ladder. -/
def groupedHermiteJetLadderConstant (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | i+1 => (2*Real.pi*(2+(2:ℝ)^(k+i))) * groupedHermiteJetLadderConstant k i

theorem groupedHermiteJetLadderConstant_pos (k i : ℕ) :
    0 < groupedHermiteJetLadderConstant k i := by
  induction i with
  | zero => norm_num [groupedHermiteJetLadderConstant]
  | succ i ih => unfold groupedHermiteJetLadderConstant; positivity

/-- Arbitrarily many actual Hermite derivatives, with the sharp one-unit
squared-weight loss per derivative and an explicit finite ladder constant. -/
theorem groupedHermiteJetEnergy_ladder (k i : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    Summable (groupedHermiteJetEnergyTerm (k+i) i x) ∧
      groupedHermiteJetEnergy (k+i) i x ≤
        groupedHermiteJetLadderConstant k i * groupedHermiteJetEnergy k 0 x := by
  induction i with
  | zero =>
    refine ⟨by simpa using summable_groupedHermiteJetEnergyTerm_zero k hk x, ?_⟩
    simp [groupedHermiteJetLadderConstant]
  | succ i ih =>
    have hstep := groupedHermiteJetEnergy_step (k+i) i x ih.1
    refine ⟨by simpa only [Nat.add_assoc] using hstep.1, ?_⟩
    have h := hstep.2.trans (mul_le_mul_of_nonneg_left ih.2 (by positivity))
    simpa only [Nat.add_assoc, groupedHermiteJetLadderConstant, mul_assoc] using h

theorem grouped_norm_hermitePointMass_sq_le_scale
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    ‖hermitePointMass m hm x‖^2 ≤
      hermiteRawNormalizationConstant m * (hermiteDiagonalScale x)^hermiteResolventHalfShape m := by
  have h := norm_hermiteResolventKernel_le_diagonalScales m hm x x
  rw [← inner_hermitePointMass_eq_resolventKernel m hm,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at h
  simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, mul_one] at h
  convert h using 1
  rw [← sq, ← Real.rpow_natCast_mul (hermiteDiagonalScale_pos x).le]
  congr 2
  push_cast
  ring

/-- Exact scalar balancing inequality for the missing odd squared
spectral exponent. -/
theorem grouped_odd_weight_balance (m : ℕ) {w A : ℝ} (hw : 0 ≤ w) (hA : 0 < A) :
    w^(2*m+1) ≤ (A*w^(2*(m+1)) + A⁻¹*w^(2*m))/2 := by
  have hb : 2*w ≤ A*w^2+A⁻¹ := by
    have h : 0 ≤ (A*w-1)^2/A := by positivity
    have heq : (A*w-1)^2/A = A*w^2 + A⁻¹ - 2*w := by field_simp; ring
    rw [heq] at h
    linarith
  have h := mul_le_mul_of_nonneg_left hb (pow_nonneg hw (2*m))
  rw [show 2*(m+1) = 2*m+2 by omega, pow_add w (2*m) 2, pow_succ w (2*m)]
  nlinarith

theorem groupedHermiteJetEnergy_odd_balance
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    groupedHermiteJetEnergy (2*m+1) 0 x ≤
      (A*groupedHermiteJetEnergy (2*(m+1)) 0 x + A⁻¹*groupedHermiteJetEnergy (2*m) 0 x)/2 := by
  have hhi := (summable_groupedHermiteJetEnergyTerm_zero (2*(m+1)) (by omega) x).mul_left A
  have hlo := (summable_groupedHermiteJetEnergyTerm_zero (2*m) (by omega) x).mul_left A⁻¹
  have hodd := summable_groupedHermiteJetEnergyTerm_zero (2*m+1) (by omega) x
  unfold groupedHermiteJetEnergy
  calc
    _ ≤ ∑' n : ℕ, (A*groupedHermiteJetEnergyTerm (2*(m+1)) 0 x n +
        A⁻¹*groupedHermiteJetEnergyTerm (2*m) 0 x n)/2 := by
      apply hodd.tsum_le_tsum _ ((hhi.add hlo).div_const 2)
      intro n
      unfold groupedHermiteJetEnergyTerm
      have h := mul_le_mul_of_nonneg_right
        (grouped_odd_weight_balance m (show 0 ≤ ((n:ℝ)+1)⁻¹ by positivity) hA)
        (sq_nonneg ‖groupedHermiteJet 0 n x‖)
      convert h using 1
      ring
    _ = _ := by rw [tsum_div_const, hhi.tsum_add hlo, tsum_mul_left, tsum_mul_left]

theorem groupedHermiteJetEnergy_odd_le_scale
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    groupedHermiteJetEnergy (2*m+1) 0 x ≤
      ((hermiteRawNormalizationConstant (m+1) + hermiteRawNormalizationConstant m)/2) *
        (hermiteDiagonalScale x)^((2*m+1:ℕ)- (1/2:ℝ)) := by
  let T := hermiteDiagonalScale x
  have hT : 0 < T := hermiteDiagonalScale_pos x
  have h := groupedHermiteJetEnergy_odd_balance m hm x (A := T⁻¹) (inv_pos.mpr hT)
  rw [groupedHermiteJetEnergy_even_zero (m+1) (by omega), groupedHermiteJetEnergy_even_zero m hm] at h
  have h₁ : T⁻¹*T^hermiteResolventHalfShape (m+1) = T^((2*m+1:ℕ)-(1/2:ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hT]
    congr 1
    unfold hermiteResolventHalfShape
    push_cast
    ring
  have h₂ : T*T^hermiteResolventHalfShape m = T^((2*m+1:ℕ)-(1/2:ℝ)) := by
    calc
      _ = T^(1:ℝ)*T^hermiteResolventHalfShape m := by rw [Real.rpow_one]
      _ = _ := ?_
    rw [← Real.rpow_add hT]
    congr 1
    unfold hermiteResolventHalfShape
    push_cast
    ring
  refine h.trans ?_
  rw [inv_inv]
  calc
    _ ≤ (T⁻¹*(hermiteRawNormalizationConstant (m+1)*T^hermiteResolventHalfShape (m+1)) +
        T*(hermiteRawNormalizationConstant m*T^hermiteResolventHalfShape m))/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (grouped_norm_hermitePointMass_sq_le_scale (m+1) (by omega) x)
          (inv_nonneg.mpr hT.le))
        (mul_le_mul_of_nonneg_left (grouped_norm_hermitePointMass_sq_le_scale m hm x) hT.le)
    _ = _ := by
      rw [mul_left_comm T⁻¹, mul_left_comm T, h₁, h₂]
      ring

/-- Every integer squared spectral exponent at least two has its sharp
diagonal spatial power; odd exponents are genuinely interpolated. -/
theorem exists_groupedHermiteDiagonalEnergy_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      groupedHermiteJetEnergy k 0 x ≤ C*(hermiteDiagonalScale x)^((k:ℝ)-1/2) := by
  let m := k/2
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hrep : k = 2*m ∨ k = 2*m+1 := by
    dsimp [m]
    omega
  rcases hrep with h | h
  · refine ⟨hermiteRawNormalizationConstant m, hermiteRawNormalizationConstant_pos hm, ?_⟩
    intro x
    rw [h, groupedHermiteJetEnergy_even_zero m hm]
    simpa only [hermiteResolventHalfShape, Nat.cast_mul, Nat.cast_ofNat] using
      grouped_norm_hermitePointMass_sq_le_scale m hm x
  · refine ⟨(hermiteRawNormalizationConstant (m+1)+hermiteRawNormalizationConstant m)/2,
      div_pos (add_pos (hermiteRawNormalizationConstant_pos (m := m+1) (by omega))
        (hermiteRawNormalizationConstant_pos hm)) (by norm_num), ?_⟩
    intro x
    rw [h]
    exact groupedHermiteJetEnergy_odd_le_scale m hm x

/-- All physical derivative orders in the source's admissible range have
a genuine same-order squared-norm bound. -/
theorem exists_groupedHermiteJetEnergy_sameOrder_bound
    (m i : ℕ) (hi : i+2 ≤ 2*m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      groupedHermiteJetEnergy (2*m) i x ≤
        C*(1+|x|)^(2*i)*‖hermitePointMass m (by omega) x‖^2 := by
  let k := 2*m-i
  have hk : 2 ≤ k := by dsimp [k]; omega
  obtain ⟨B, hB, hbound⟩ := exists_groupedHermiteDiagonalEnergy_bound k hk
  let L := groupedHermiteJetLadderConstant k i
  have hL : 0 < L := groupedHermiteJetLadderConstant_pos k i
  have hF := hermiteDiagonalFloorConstant_pos m
  refine ⟨L*B/hermiteDiagonalFloorConstant m, by positivity, ?_⟩
  intro x
  let T := hermiteDiagonalScale x
  have hT : 0 < T := hermiteDiagonalScale_pos x
  have hpow : T^((k:ℝ)-1/2) = (1+x^2)^i*T^hermiteResolventHalfShape m := by
    have hexp : (k:ℝ)-1/2 = -(i:ℝ)+hermiteResolventHalfShape m := by
      dsimp [k, hermiteResolventHalfShape]
      rw [Nat.cast_sub (by omega : i ≤ 2*m)]
      push_cast
      ring
    rw [hexp, Real.rpow_add hT, Real.rpow_neg hT.le, Real.rpow_natCast]
    dsimp [T, hermiteDiagonalScale]
    rw [← inv_pow, inv_inv]
  have hspace : (1+x^2)^i ≤ (1+|x|)^(2*i) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_abs x, abs_nonneg x]
  have hfloor : T^hermiteResolventHalfShape m ≤
      ‖hermitePointMass m (by omega) x‖^2/hermiteDiagonalFloorConstant m := by
    apply (le_div_iff₀ hF).mpr
    have h := hermitePointMassDiagonalFloor_le_norm_sq m (by omega) x
    rw [hermitePointMassDiagonalFloor_eq_rpow m (by omega)] at h
    simpa only [mul_comm, T] using h
  have hjet := (groupedHermiteJetEnergy_ladder k i hk x).2
  have hki : k+i = 2*m := by dsimp [k]; omega
  rw [hki] at hjet
  calc
    _ ≤ L*(B*T^((k:ℝ)-1/2)) := hjet.trans (mul_le_mul_of_nonneg_left (hbound x) hL.le)
    _ = (L*B)*(1+x^2)^i*T^hermiteResolventHalfShape m := by rw [hpow]; ring
    _ ≤ (L*B)*(1+|x|)^(2*i)*
        (‖hermitePointMass m (by omega) x‖^2/hermiteDiagonalFloorConstant m) := by
      gcongr
    _ = _ := by ring

/-- Coordinates of the genuine physical derivative of a negative-scale Dirac vector. -/
def groupedHermiteJetCoefficients (m i : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  (((((n:ℝ)+1)⁻¹)^m : ℝ) : ℂ) * groupedHermiteJet i n x

theorem norm_groupedHermiteJetCoefficients_sq (m i n : ℕ) (x : ℝ) :
    ‖groupedHermiteJetCoefficients m i x n‖^2 = groupedHermiteJetEnergyTerm (2*m) i x n := by
  simp only [groupedHermiteJetCoefficients, groupedHermiteJetEnergyTerm, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (((n:ℝ)+1)⁻¹)^m), mul_pow, ← pow_mul]
  rw [Nat.mul_comm m 2]

theorem groupedHermiteJetCoefficients_memℓp
    (m i : ℕ) (hi : i+2 ≤ 2*m) (x : ℝ) :
    Memℓp (groupedHermiteJetCoefficients m i x) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_groupedHermiteJetCoefficients_sq]
  have h := (groupedHermiteJetEnergy_ladder (2*m-i) i (by omega) x).1
  simpa only [Nat.sub_add_cancel (by omega : i ≤ 2*m)] using h

/-- The actual square-summable Hermite jet vector, at the same Hermite order. -/
def groupedHermiteJetPointMass (m i : ℕ) (hi : i+2 ≤ 2*m) (x : ℝ) : HermiteScale (-(m:ℤ)) :=
  ⟨groupedHermiteJetCoefficients m i x, groupedHermiteJetCoefficients_memℓp m i hi x⟩

theorem norm_groupedHermiteJetPointMass_sq (m i : ℕ) (hi : i+2 ≤ 2*m) (x : ℝ) :
    ‖groupedHermiteJetPointMass m i hi x‖^2 = groupedHermiteJetEnergy (2*m) i x := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal)
    (groupedHermiteJetPointMass m i hi x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, groupedHermiteJetPointMass,
    norm_groupedHermiteJetCoefficients_sq, groupedHermiteJetEnergy] using h

theorem exists_groupedHermiteJetPointMass_sameOrder_bound
    (m i : ℕ) (hi : i+2 ≤ 2*m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖groupedHermiteJetPointMass m i hi x‖ ≤
        C*(1+|x|)^i*‖hermitePointMass m (by omega) x‖ := by
  obtain ⟨C,hC,h⟩ := exists_groupedHermiteJetEnergy_sameOrder_bound m i hi
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_groupedHermiteJetPointMass_sq, mul_pow, mul_pow, Real.sq_sqrt hC.le]
  simpa only [← pow_mul, Nat.mul_comm i 2] using h x

/-- The genuine mixed Hermite spectral jet term. -/
def groupedHermiteMixedJetTerm (m i j : ℕ) (x y : ℝ) (n : ℕ) : ℂ :=
  starRingEnd ℂ (groupedHermiteJetCoefficients m i x n) * groupedHermiteJetCoefficients m j y n

/-- The absolutely convergent mixed spectral jet kernel in the admissible range. -/
def groupedHermiteMixedJetKernel (m i j : ℕ) (x y : ℝ) : ℂ :=
  ∑' n : ℕ, groupedHermiteMixedJetTerm m i j x y n

theorem summable_groupedHermiteMixedJetTerm
    (m i j : ℕ) (hi : i+2 ≤ 2*m) (hj : j+2 ≤ 2*m) (x y : ℝ) :
    Summable (groupedHermiteMixedJetTerm m i j x y) := by
  have h := lp.summable_inner (𝕜 := ℂ)
    (groupedHermiteJetPointMass m i hi x) (groupedHermiteJetPointMass m j hj y)
  apply h.congr
  intro n
  simp only [RCLike.inner_apply, groupedHermiteJetPointMass,
    groupedHermiteMixedJetTerm, mul_comm]

theorem groupedHermiteMixedJetKernel_eq_inner
    (m i j : ℕ) (hi : i+2 ≤ 2*m) (hj : j+2 ≤ 2*m) (x y : ℝ) :
    groupedHermiteMixedJetKernel m i j x y =
      inner ℂ (groupedHermiteJetPointMass m i hi x) (groupedHermiteJetPointMass m j hj y) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [groupedHermiteMixedJetTerm, RCLike.inner_apply,
    groupedHermiteJetPointMass, mul_comm]

/-- Arbitrary physical mixed spectral jets satisfy a uniform same-order bound.
Actual iterated differentiation of the kernel is proved separately below. -/
theorem exists_groupedHermiteMixedJetKernel_sameOrder_bound
    (m i j : ℕ) (hi : i+2 ≤ 2*m) (hj : j+2 ≤ 2*m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖groupedHermiteMixedJetKernel m i j x y‖ ≤
        C*(1+|x|)^i*(1+|y|)^j*‖hermitePointMass m (by omega) x‖*
          ‖hermitePointMass m (by omega) y‖ := by
  obtain ⟨A,hA,hx⟩ := exists_groupedHermiteJetPointMass_sameOrder_bound m i hi
  obtain ⟨B,hB,hy⟩ := exists_groupedHermiteJetPointMass_sameOrder_bound m j hj
  refine ⟨A*B,mul_pos hA hB, ?_⟩
  intro x y
  rw [groupedHermiteMixedJetKernel_eq_inner m i j hi hj]
  calc
    _ ≤ ‖groupedHermiteJetPointMass m i hi x‖ * ‖groupedHermiteJetPointMass m j hj y‖ :=
      norm_inner_le_norm _ _
    _ ≤ (A*(1+|x|)^i*‖hermitePointMass m (by omega) x‖)*
        (B*(1+|y|)^j*‖hermitePointMass m (by omega) y‖) := by gcongr; exact hx x; exact hy y
    _ = _ := by ring

/-- Finite Schwartz seminorm envelope used only to justify differentiation
of the genuine series; it is not used for the sharp spatial bound. -/
def groupedHermiteJetEnvelope (q n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (q+1), normalizedHermiteSchwartzSeminorm 0 i n

theorem groupedHermiteJetEnvelope_nonneg (q n : ℕ) :
    0 ≤ groupedHermiteJetEnvelope q n := by
  apply Finset.sum_nonneg
  intro i hi
  exact apply_nonneg _ _

theorem groupedHermiteJetEnvelope_polynomiallyBounded (q : ℕ) :
    NatPolynomiallyBounded (groupedHermiteJetEnvelope q) := by
  induction q with
  | zero =>
    have heq : groupedHermiteJetEnvelope 0 = fun n => normalizedHermiteSchwartzSeminorm 0 0 n := by
      funext n
      simp [groupedHermiteJetEnvelope]
    rw [heq]
    exact normalizedHermiteSchwartzSeminorm_polynomiallyBounded 0 0
  | succ q ih =>
    have h := ih.add (normalizedHermiteSchwartzSeminorm_polynomiallyBounded 0 (q+1))
    have heq : groupedHermiteJetEnvelope (q+1) = fun n =>
        groupedHermiteJetEnvelope q n + normalizedHermiteSchwartzSeminorm 0 (q+1) n := by
      funext n
      exact Finset.sum_range_succ _ _
    rw [heq]
    exact h

theorem norm_groupedHermiteJet_le_envelope (q i n : ℕ) (hi : i ≤ q) (x : ℝ) :
    ‖groupedHermiteJet i n x‖ ≤ groupedHermiteJetEnvelope q n := by
  have h := SchwartzMap.le_seminorm' ℂ 0 i (normalizedHermiteSchwartz n) x
  simp only [pow_zero, one_mul, ← groupedHermiteJet_apply] at h
  exact h.trans (Finset.single_le_sum (fun j hj => apply_nonneg _ _)
    (Finset.mem_range.mpr (by omega)))

/-- A polynomial envelope constant, chosen from the proved Schwartz seminorm bound. -/
def groupedHermiteJetGrowthConstant (q : ℕ) : ℝ :=
  (groupedHermiteJetEnvelope_polynomiallyBounded q).choose

/-- A polynomial degree, chosen from the proved finite seminorm envelope. -/
def groupedHermiteJetGrowthDegree (q : ℕ) : ℕ :=
  (groupedHermiteJetEnvelope_polynomiallyBounded q).choose_spec.2.choose

theorem groupedHermiteJetGrowthConstant_nonneg (q : ℕ) :
    0 ≤ groupedHermiteJetGrowthConstant q :=
  (groupedHermiteJetEnvelope_polynomiallyBounded q).choose_spec.1

theorem groupedHermiteJetEnvelope_le_growth (q n : ℕ) :
    groupedHermiteJetEnvelope q n ≤
      groupedHermiteJetGrowthConstant q*((n:ℝ)+1)^groupedHermiteJetGrowthDegree q :=
  (groupedHermiteJetEnvelope_polynomiallyBounded q).choose_spec.2.choose_spec n

/-- A sufficient cofinal order for justified derivatives through order `q`.
The sharp energy bounds themselves do not require this extra regularity margin. -/
def groupedHermiteDifferentiationOrder (q : ℕ) : ℕ :=
  max (q+2) (groupedHermiteJetGrowthDegree (q+1)+1)

theorem grouped_weight_growth_bound (m d : ℕ) (hmd : d+1 ≤ m) (n : ℕ) :
    (((n:ℝ)+1)⁻¹)^(2*m)*(((n:ℝ)+1)^d)^2 ≤ (((n:ℝ)+1)⁻¹)^2 := by
  let a : ℝ := (n:ℝ)+1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpow : a^(2*d+2) ≤ a^(2*m) := pow_le_pow_right₀ ha1 (by omega)
  rw [← pow_mul, inv_pow, inv_pow, ← div_eq_inv_mul]
  rw [← one_div]
  apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos ha _)).mpr
  change a^(d*2)*a^2 ≤ 1*a^(2*m)
  simpa only [← pow_add, one_mul, Nat.mul_comm d 2] using hpow

theorem norm_groupedHermiteMixedJetTerm_le_summable_bound
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q+1) (hj : j ≤ q+1) (x y : ℝ) (n : ℕ) :
    ‖groupedHermiteMixedJetTerm m i j x y n‖ ≤
      (groupedHermiteJetGrowthConstant (q+1))^2 * (((n:ℝ)+1)⁻¹)^2 := by
  have hC := groupedHermiteJetGrowthConstant_nonneg (q+1)
  have hx := (norm_groupedHermiteJet_le_envelope (q+1) i n hi x).trans
    (groupedHermiteJetEnvelope_le_growth (q+1) n)
  have hy := (norm_groupedHermiteJet_le_envelope (q+1) j n hj y).trans
    (groupedHermiteJetEnvelope_le_growth (q+1) n)
  have hmd : groupedHermiteJetGrowthDegree (q+1)+1 ≤ m := (le_max_right _ _).trans hm
  simp only [groupedHermiteMixedJetTerm, groupedHermiteJetCoefficients,
    norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (((n:ℝ)+1)⁻¹)^m)]
  calc
    _ = (((n:ℝ)+1)⁻¹)^(2*m)*(‖groupedHermiteJet i n x‖*‖groupedHermiteJet j n y‖) := by
      rw [pow_mul, pow_two]; ring
    _ ≤ (((n:ℝ)+1)⁻¹)^(2*m)*
        ((groupedHermiteJetGrowthConstant (q+1)*((n:ℝ)+1)^groupedHermiteJetGrowthDegree (q+1))^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [pow_two]
      exact mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = (groupedHermiteJetGrowthConstant (q+1))^2 *
        ((((n:ℝ)+1)⁻¹)^(2*m)*(((n:ℝ)+1)^groupedHermiteJetGrowthDegree (q+1))^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (grouped_weight_growth_bound m _ hmd n) (sq_nonneg _)

theorem summable_groupedHermiteMixedJet_majorant (q : ℕ) :
    Summable (fun n : ℕ =>
      (groupedHermiteJetGrowthConstant (q+1))^2 * (((n:ℝ)+1)⁻¹)^2) := by
  have h := ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).mul_left
    ((groupedHermiteJetGrowthConstant (q+1))^2)
  apply h.congr
  intro n
  rw [abs_of_pos (by positivity : 0 < (n:ℝ)+1), Real.rpow_two, one_div, inv_pow]

theorem hasDerivAt_groupedHermiteJet (i n : ℕ) (x : ℝ) :
    HasDerivAt (groupedHermiteJet i n) (groupedHermiteJet (i+1) n x) x := by
  simpa only [groupedHermiteJet, SchwartzMap.derivCLM_apply] using
    (groupedHermiteJet i n).hasDerivAt x

theorem hasDerivAt_groupedHermiteJetCoefficients (m i n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => groupedHermiteJetCoefficients m i x n)
      (groupedHermiteJetCoefficients m (i+1) x n) x :=
  (hasDerivAt_groupedHermiteJet i n x).const_mul _

theorem hasDerivAt_groupedHermiteMixedJetTerm_left (m i j n : ℕ) (x y : ℝ) :
    HasDerivAt (fun x => groupedHermiteMixedJetTerm m i j x y n)
      (groupedHermiteMixedJetTerm m (i+1) j x y n) x := by
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_groupedHermiteJetCoefficients m i n x)).mul_const
      (groupedHermiteJetCoefficients m j y n)
  exact h

theorem hasDerivAt_groupedHermiteMixedJetTerm_right (m i j n : ℕ) (x y : ℝ) :
    HasDerivAt (fun y => groupedHermiteMixedJetTerm m i j x y n)
      (groupedHermiteMixedJetTerm m i (j+1) x y n) y :=
  (hasDerivAt_groupedHermiteJetCoefficients m j n y).const_mul _

/-- Genuine termwise differentiation, using a global summable Schwartz
seminorm majorant and pointwise convergence of the spectral kernel. -/
theorem hasDerivAt_groupedHermiteMixedJetKernel_left
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (x y : ℝ) :
    HasDerivAt (fun x => groupedHermiteMixedJetKernel m i j x y)
      (groupedHermiteMixedJetKernel m (i+1) j x y) x := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  exact hasDerivAt_tsum (summable_groupedHermiteMixedJet_majorant q)
    (fun n x => hasDerivAt_groupedHermiteMixedJetTerm_left m i j n x y)
    (fun n x => norm_groupedHermiteMixedJetTerm_le_summable_bound q m (i+1) j hm
      (by omega) (by omega) x y n)
    (summable_groupedHermiteMixedJetTerm m i j (by omega) (by omega) 0 y) x

theorem hasDerivAt_groupedHermiteMixedJetKernel_right
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (x y : ℝ) :
    HasDerivAt (fun y => groupedHermiteMixedJetKernel m i j x y)
      (groupedHermiteMixedJetKernel m i (j+1) x y) y := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  exact hasDerivAt_tsum (summable_groupedHermiteMixedJet_majorant q)
    (fun n y => hasDerivAt_groupedHermiteMixedJetTerm_right m i j n x y)
    (fun n y => norm_groupedHermiteMixedJetTerm_le_summable_bound q m i (j+1) hm
      (by omega) (by omega) x y n)
    (summable_groupedHermiteMixedJetTerm m i j (by omega) (by omega) x 0) y

theorem groupedHermiteJetCoefficients_zero (m n : ℕ) (x : ℝ) :
    groupedHermiteJetCoefficients m 0 x n = hermiteDiracCoefficients m x n := by
  simp only [groupedHermiteJetCoefficients, groupedHermiteJet,
    hermiteDiracCoefficients, hermiteScaleWeight, zpow_neg, zpow_natCast, inv_pow]

theorem groupedHermiteMixedJetKernel_zero (m : ℕ) (x y : ℝ) :
    groupedHermiteMixedJetKernel m 0 0 x y = hermiteResolventKernel m x y := by
  apply tsum_congr
  intro n
  rw [groupedHermiteMixedJetTerm, groupedHermiteJetCoefficients_zero,
    groupedHermiteJetCoefficients_zero]
  exact star_hermiteDiracCoefficients_mul_eq_resolventTerm m x y n

theorem iteratedDeriv_groupedHermiteMixedJetKernel_left
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (y : ℝ) :
    iteratedDeriv i (fun x => groupedHermiteMixedJetKernel m 0 j x y) =
      fun x => groupedHermiteMixedJetKernel m i j x y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext x
    exact (hasDerivAt_groupedHermiteMixedJetKernel_left q m i j hm (by omega) hj x y).deriv

theorem iteratedDeriv_groupedHermiteMixedJetKernel_right
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (x : ℝ) :
    iteratedDeriv j (fun y => groupedHermiteMixedJetKernel m i 0 x y) =
      fun y => groupedHermiteMixedJetKernel m i j x y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext y
    exact (hasDerivAt_groupedHermiteMixedJetKernel_right q m i j hm hi (by omega) x y).deriv

/-- Arbitrary actual mixed derivatives are the absolutely convergent
spectral jet kernel, under the proved sufficient cofinal order cutoff. -/
theorem iteratedDeriv_iteratedDeriv_hermiteResolventKernel_eq
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (x y : ℝ) :
    iteratedDeriv j (fun y => iteratedDeriv i (fun x => hermiteResolventKernel m x y) x) y =
      groupedHermiteMixedJetKernel m i j x y := by
  simp_rw [← groupedHermiteMixedJetKernel_zero,
    iteratedDeriv_groupedHermiteMixedJetKernel_left q m i 0 hm hi (by omega)]
  exact congrFun (iteratedDeriv_groupedHermiteMixedJetKernel_right q m i j hm hi hj x) y

theorem exists_norm_iteratedDeriv_iteratedDeriv_hermiteResolventKernel_le_weighted
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖iteratedDeriv j (fun y => iteratedDeriv i (fun x => hermiteResolventKernel m x y) x) y‖ ≤
        C*(1+|x|)^i*(1+|y|)^j*‖hermitePointMass m (by
          have := (le_max_left _ _).trans hm; omega) x‖*
          ‖hermitePointMass m (by have := (le_max_left _ _).trans hm; omega) y‖ := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  obtain ⟨C,hC,h⟩ := exists_groupedHermiteMixedJetKernel_sameOrder_bound m i j (by omega) (by omega)
  refine ⟨C,hC,fun x y => ?_⟩
  rw [iteratedDeriv_iteratedDeriv_hermiteResolventKernel_eq q m i j hm hi hj]
  exact h x y

theorem contDiff_groupedHermiteMixedJetKernel_left
    (q m j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hj : j ≤ q) (y : ℝ) :
    ContDiff ℝ q (fun x => groupedHermiteMixedJetKernel m 0 j x y) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro i hi
    rw [iteratedDeriv_groupedHermiteMixedJetKernel_left q m i j hm hi hj]
    exact Differentiable.continuous (fun x =>
      (hasDerivAt_groupedHermiteMixedJetKernel_left q m i j hm hi hj x y).differentiableAt)
  · intro i hi
    rw [iteratedDeriv_groupedHermiteMixedJetKernel_left q m i j hm hi.le hj]
    exact fun x => (hasDerivAt_groupedHermiteMixedJetKernel_left q m i j hm hi.le hj x y).differentiableAt

theorem contDiff_groupedHermiteMixedJetKernel_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (x : ℝ) :
    ContDiff ℝ q (fun y => groupedHermiteMixedJetKernel m i 0 x y) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j hj
    rw [iteratedDeriv_groupedHermiteMixedJetKernel_right q m i j hm hi hj]
    exact Differentiable.continuous (fun y =>
      (hasDerivAt_groupedHermiteMixedJetKernel_right q m i j hm hi hj x y).differentiableAt)
  · intro j hj
    rw [iteratedDeriv_groupedHermiteMixedJetKernel_right q m i j hm hi hj.le]
    exact fun y => (hasDerivAt_groupedHermiteMixedJetKernel_right q m i j hm hi hj.le x y).differentiableAt

/-- Falling-power coefficients of the square-root ray derivatives. -/
def groupedRayDerivativeCoefficient : ℕ → ℝ
  | 0 => 1
  | i+1 => groupedRayDerivativeCoefficient i * (1/2-(i:ℝ))

/-- Exact derivative model on either open signed-square ray. -/
def groupedRayDerivativeModel (ε : ℝ) (i : ℕ) (s : ℝ) : ℝ :=
  ε^(i+1)*groupedRayDerivativeCoefficient i*(ε*s)^(1/2-(i:ℝ))

theorem hasDerivAt_groupedRayDerivativeModel (ε : ℝ) (i : ℕ) (s : ℝ) (hs : 0 < ε*s) :
    HasDerivAt (groupedRayDerivativeModel ε i) (groupedRayDerivativeModel ε (i+1) s) s := by
  have h := (((Real.hasDerivAt_rpow_const (p := 1/2-(i:ℝ)) (Or.inl hs.ne')).comp s
    ((hasDerivAt_id s).const_mul ε)).const_mul (ε^(i+1)*groupedRayDerivativeCoefficient i))
  apply h.congr_deriv
  dsimp [groupedRayDerivativeModel, groupedRayDerivativeCoefficient]
  rw [show 1/2-((i+1:ℕ):ℝ) = (1/2-(i:ℝ))-1 by push_cast; ring]
  rw [pow_succ ε (i+1)]
  ring

theorem iteratedDeriv_groupedSignedSquareRayPoint (ε : ℝ) (i : ℕ) (s : ℝ) (hs : 0 < ε*s) :
    iteratedDeriv i (groupedSignedSquareRayPoint ε) s = groupedRayDerivativeModel ε i s := by
  induction i generalizing s with
  | zero => simp [groupedSignedSquareRayPoint, groupedRayDerivativeModel,
      groupedRayDerivativeCoefficient, Real.sqrt_eq_rpow]
  | succ i ih =>
    rw [iteratedDeriv_succ]
    have hnear : ∀ᶠ t in 𝓝 s, 0 < ε*t :=
      (continuous_const.mul continuous_id).continuousAt.eventually (lt_mem_nhds hs)
    have heq : iteratedDeriv i (groupedSignedSquareRayPoint ε) =ᶠ[𝓝 s]
        groupedRayDerivativeModel ε i := hnear.mono (fun t ht => ih t ht)
    rw [heq.deriv_eq]
    exact (hasDerivAt_groupedRayDerivativeModel ε i s hs).deriv

theorem contDiffAt_groupedSignedSquareRayPoint
    (ε s : ℝ) (q : ℕ) (hs : 0 < ε*s) :
    ContDiffAt ℝ q (groupedSignedSquareRayPoint ε) s := by
  exact contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_id).sqrt hs.ne')

/-- Every positive ray derivative has one uniform inverse-radius factor.
This weaker consequence of the exact derivative formula is sufficient for
every block in Faà di Bruno and avoids inverse node gaps entirely. -/
theorem abs_iteratedDeriv_groupedSignedSquareRayPoint_le
    (ε s : ℝ) (i : ℕ) (hε : ε^2=1) (hs : 1 ≤ ε*s) (hi : 1 ≤ i) :
    |iteratedDeriv i (groupedSignedSquareRayPoint ε) s| *
      (1+|groupedSignedSquareRayPoint ε s|) ≤ 2*|groupedRayDerivativeCoefficient i| := by
  have hpos : 0 < ε*s := by linarith
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hpow : (ε*s)^(1/2-(i:ℝ)) ≤ (ε*s)^(-(1/2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hs
    have hiR : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
    linarith
  have hroot : 1 ≤ Real.sqrt (ε*s) := (Real.one_le_sqrt).mpr hs
  have hid : (ε*s)^(-(1/2:ℝ))*Real.sqrt (ε*s)=1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
    norm_num
  rw [iteratedDeriv_groupedSignedSquareRayPoint ε i s hpos,
    groupedRayDerivativeModel, abs_mul, abs_mul, abs_pow, heps, one_pow, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hpos.le _), abs_groupedSignedSquareRayPoint hε s]
  calc
    _ ≤ |groupedRayDerivativeCoefficient i| * ((ε*s)^(-(1/2:ℝ))*(2*Real.sqrt (ε*s))) := by
      rw [mul_assoc]
      gcongr
      linarith
    _ = _ := by rw [mul_left_comm _ 2, hid]; ring

/-- Scalar ray factor for one ordered derivative partition. -/
def groupedRayPartitionCoefficient {i : ℕ} (ε s : ℝ) (c : OrderedFinpartition i) : ℝ :=
  ∏ r, iteratedDeriv (c.partSize r) (groupedSignedSquareRayPoint ε) s

/-- Uniform numerical bound for an ordered ray derivative partition. -/
def groupedRayPartitionBound {i : ℕ} (c : OrderedFinpartition i) : ℝ :=
  ∏ r, 2*|groupedRayDerivativeCoefficient (c.partSize r)|

theorem groupedRayPartitionBound_nonneg {i : ℕ} (c : OrderedFinpartition i) :
    0 ≤ groupedRayPartitionBound c := by
  apply Finset.prod_nonneg
  intro r hr
  positivity

theorem abs_groupedRayPartitionCoefficient_mul_weight_le
    {i : ℕ} (ε s : ℝ) (c : OrderedFinpartition i) (hε : ε^2=1) (hs : 1 ≤ ε*s) :
    |groupedRayPartitionCoefficient ε s c| *
        (1+|groupedSignedSquareRayPoint ε s|)^c.length ≤ groupedRayPartitionBound c := by
  rw [groupedRayPartitionCoefficient, Finset.abs_prod]
  have heq : (1+|groupedSignedSquareRayPoint ε s|)^c.length =
      ∏ _r : Fin c.length, (1+|groupedSignedSquareRayPoint ε s|) := by simp
  rw [heq, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro r hr
    positivity
  · intro r hr
    exact abs_iteratedDeriv_groupedSignedSquareRayPoint_le ε s (c.partSize r) hε hs
      (c.partSize_pos r)

theorem iteratedDeriv_groupedHermiteMixedJetKernel_ray_left
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε s y : ℝ) (hs : 0 < ε*s) :
    iteratedDeriv i (fun s => groupedHermiteMixedJetKernel m 0 j
      (groupedSignedSquareRayPoint ε s) y) s =
        ∑ c : OrderedFinpartition i, groupedRayPartitionCoefficient ε s c •
          groupedHermiteMixedJetKernel m c.length j (groupedSignedSquareRayPoint ε s) y := by
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (contDiff_groupedHermiteMixedJetKernel_left q m j hm hj y).contDiffAt
    (contDiffAt_groupedSignedSquareRayPoint ε s q hs) (by exact_mod_cast hi)
  simp only [Function.comp_def] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c hc
  rw [iteratedDeriv_groupedHermiteMixedJetKernel_left q m c.length j hm (c.length_le.trans hi) hj]
  rfl

theorem iteratedDeriv_groupedHermiteMixedJetKernel_ray_right
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (η t x : ℝ) (ht : 0 < η*t) :
    iteratedDeriv j (fun t => groupedHermiteMixedJetKernel m i 0 x
      (groupedSignedSquareRayPoint η t)) t =
        ∑ d : OrderedFinpartition j, groupedRayPartitionCoefficient η t d •
          groupedHermiteMixedJetKernel m i d.length x (groupedSignedSquareRayPoint η t) := by
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (contDiff_groupedHermiteMixedJetKernel_right q m i hm hi x).contDiffAt
    (contDiffAt_groupedSignedSquareRayPoint η t q ht) (by exact_mod_cast hj)
  simp only [Function.comp_def] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  rw [iteratedDeriv_groupedHermiteMixedJetKernel_right q m i d.length hm hi (d.length_le.trans hj)]
  rfl

/-- Exact arbitrary mixed derivative formula after either signed-square
ray pullback. All differentiation is justified before this finite expansion. -/
theorem iteratedDeriv_iteratedDeriv_hermiteResolventKernel_signedSquareRay_eq
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε η s t : ℝ) (hs : 0 < ε*s) (ht : 0 < η*t) :
    iteratedDeriv j (fun t => iteratedDeriv i (fun s => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η t)) s) t =
      ∑ c : OrderedFinpartition i, ∑ d : OrderedFinpartition j,
        (groupedRayPartitionCoefficient ε s c * groupedRayPartitionCoefficient η t d) •
          groupedHermiteMixedJetKernel m c.length d.length
            (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η t) := by
  simp_rw [← groupedHermiteMixedJetKernel_zero,
    iteratedDeriv_groupedHermiteMixedJetKernel_ray_left q m i 0 hm hi (by omega) ε s _ hs]
  have hsm (c : OrderedFinpartition i) : ContDiffAt ℝ j
      (fun t => groupedRayPartitionCoefficient ε s c • groupedHermiteMixedJetKernel m c.length 0
        (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η t)) t := by
    apply ContDiffAt.const_smul
    exact (((contDiff_groupedHermiteMixedJetKernel_right q m c.length hm
      (c.length_le.trans hi) (groupedSignedSquareRayPoint ε s)).contDiffAt).comp t
        (contDiffAt_groupedSignedSquareRayPoint η t q ht)).of_le (by exact_mod_cast hj)
  rw [iteratedDeriv_fun_sum (fun c hc => hsm c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_groupedHermiteMixedJetKernel_ray_right q m c.length j hm
      (c.length_le.trans hi) hj η t (groupedSignedSquareRayPoint ε s) ht,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [smul_smul]

/-- Arbitrary mixed derivatives of the actual same-order resolvent kernel
in signed-square coordinates, uniformly on all four pairs of tail rays.
The sufficient cofinal order cutoff is explicit and independent of nodes,
their separation, their coordinates, and the ray signs. -/
theorem exists_norm_iteratedDeriv_iteratedDeriv_hermiteResolventKernel_signedSquareRay_le_weighted
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 →
      ∀ s t : ℝ, 1 ≤ ε*s → 1 ≤ η*t →
      ‖iteratedDeriv j (fun t => iteratedDeriv i (fun s => hermiteResolventKernel m
        (groupedSignedSquareRayPoint ε s) (groupedSignedSquareRayPoint η t)) s) t‖ ≤
        C*‖hermitePointMass m (by have := (le_max_left _ _).trans hm; omega)
          (groupedSignedSquareRayPoint ε s)‖*
        ‖hermitePointMass m (by have := (le_max_left _ _).trans hm; omega)
          (groupedSignedSquareRayPoint η t)‖ := by
  classical
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  have hproof (c : OrderedFinpartition i) (d : OrderedFinpartition j) :
      c.length+2 ≤ 2*m ∧ d.length+2 ≤ 2*m := by
    have := c.length_le
    have := d.length_le
    omega
  choose C hC hbound using fun (c : OrderedFinpartition i) (d : OrderedFinpartition j) =>
    exists_groupedHermiteMixedJetKernel_sameOrder_bound m c.length d.length
      (hproof c d).1 (hproof c d).2
  let B : ℝ := ∑ c : OrderedFinpartition i, ∑ d : OrderedFinpartition j,
    C c d * groupedRayPartitionBound c * groupedRayPartitionBound d
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (mul_nonneg (hC c d).le (groupedRayPartitionBound_nonneg c))
      (groupedRayPartitionBound_nonneg d)
  refine ⟨B+1, by linarith, ?_⟩
  intro ε η hε hη s t hs ht
  let x := groupedSignedSquareRayPoint ε s
  let y := groupedSignedSquareRayPoint η t
  let U := ‖hermitePointMass m (by omega) x‖
  let V := ‖hermitePointMass m (by omega) y‖
  have hU : 0 ≤ U := norm_nonneg _
  have hV : 0 ≤ V := norm_nonneg _
  have hterm (c : OrderedFinpartition i) (d : OrderedFinpartition j) :
      ‖(groupedRayPartitionCoefficient ε s c * groupedRayPartitionCoefficient η t d) •
          groupedHermiteMixedJetKernel m c.length d.length x y‖ ≤
        C c d * groupedRayPartitionBound c * groupedRayPartitionBound d * U * V := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (|groupedRayPartitionCoefficient ε s c| * |groupedRayPartitionCoefficient η t d|) *
          (C c d*(1+|x|)^c.length*(1+|y|)^d.length*U*V) :=
        mul_le_mul_of_nonneg_left (hbound c d x y) (by positivity)
      _ = C c d * (|groupedRayPartitionCoefficient ε s c| * (1+|x|)^c.length) *
          (|groupedRayPartitionCoefficient η t d| * (1+|y|)^d.length) * U * V := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hV
        apply mul_le_mul_of_nonneg_right _ hU
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (abs_groupedRayPartitionCoefficient_mul_weight_le ε s c hε hs) (hC c d).le)
          (abs_groupedRayPartitionCoefficient_mul_weight_le η t d hη ht)
          (by positivity) (mul_nonneg (hC c d).le (groupedRayPartitionBound_nonneg c))
  rw [iteratedDeriv_iteratedDeriv_hermiteResolventKernel_signedSquareRay_eq
    q m i j hm hi hj ε η s t (by linarith) (by linarith)]
  calc
    _ ≤ ∑ c : OrderedFinpartition i, ∑ d : OrderedFinpartition j,
        ‖(groupedRayPartitionCoefficient ε s c * groupedRayPartitionCoefficient η t d) •
          groupedHermiteMixedJetKernel m c.length d.length x y‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      exact norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition i, ∑ d : OrderedFinpartition j,
        C c d * groupedRayPartitionBound c * groupedRayPartitionBound d * U * V := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      exact hterm c d
    _ = B*U*V := by simp only [B, Finset.sum_mul]
    _ ≤ (B+1)*U*V := by gcongr; linarith

end

end MeyerGeneralProblem
