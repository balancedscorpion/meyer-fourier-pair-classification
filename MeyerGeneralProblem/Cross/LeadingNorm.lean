module

public import MeyerGeneralProblem.Cross.AllRatioMehler
public import MeyerGeneralProblem.Cross.OperatorSchur
public import Mathlib.Data.Nat.Dist

@[expose] public section

/-!
# Fine-block leading envelope

This file records the exact algebraic `4⁻ᵐ` factor extracted from a pair of
logarithmic blocks. The remaining ratio factor is at most one and is symmetric
under interchange of the two scales.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Scale-ratio envelope of the normalized leading Mehler block. -/
def blockRatioEnvelope (m : ℕ) (R : ℝ) : ℝ :=
  R ^ m * Real.rpow R (1 / 4) / (1 + R) ^ (2 * m)

/-- The dimensionless ratio factor after extracting `4⁻ᵐ`. -/
def balancedRatioFactor (R : ℝ) : ℝ :=
  4 * R / (1 + R) ^ 2

/-- Exact elementary form of the block envelope. This is the version used in
place of introducing hyperbolic secant notation. -/
theorem blockRatioEnvelope_eq (m : ℕ) {R : ℝ} (hR : 0 < R) :
    blockRatioEnvelope m R =
      (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) * balancedRatioFactor R ^ m := by
  have hden : 1 + R ≠ 0 := by linarith
  rw [blockRatioEnvelope, balancedRatioFactor]
  rw [div_pow]
  field_simp
  rw [mul_pow]
  have hfour : (1 / 4 : ℝ) ^ m * 4 ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    R ^ m * Real.rpow R (1 / 4) * ((1 + R) ^ 2) ^ m =
        R ^ m * Real.rpow R (1 / 4) * ((1 + R) ^ 2) ^ m * 1 := by ring
    _ = R ^ m * Real.rpow R (1 / 4) * ((1 + R) ^ 2) ^ m *
        ((1 / 4 : ℝ) ^ m * 4 ^ m) := by rw [hfour]
    _ = Real.rpow R (1 / 4) * ((1 + R) ^ 2) ^ m * (1 / 4) ^ m *
        (4 ^ m * R ^ m) := by ring
    _ = Real.rpow R (1 / 4) * (1 + R) ^ (2 * m) * (1 / 4) ^ m *
        (4 ^ m * R ^ m) := by rw [pow_mul]

/-- The balanced ratio factor never exceeds one on positive scales. -/
theorem balancedRatioFactor_le_one {R : ℝ} (hR : 0 ≤ R) :
    balancedRatioFactor R ≤ 1 := by
  have hden : 0 < (1 + R) ^ 2 := sq_pos_of_pos (by linarith)
  rw [balancedRatioFactor, div_le_one hden]
  nlinarith [sq_nonneg (R - 1)]

theorem balancedRatioFactor_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ balancedRatioFactor R := by
  unfold balancedRatioFactor
  positivity

/-- On the large-ratio side, the balanced factor has the elementary decay
`4/R`. -/
theorem balancedRatioFactor_le_four_div {R : ℝ} (hR : 0 < R) :
    balancedRatioFactor R ≤ 4 / R := by
  have hden : 0 < (1 + R) ^ 2 := sq_pos_of_pos (by linarith)
  rw [balancedRatioFactor, div_le_div_iff₀ hden hR]
  nlinarith [sq_nonneg R, sq_nonneg (1 + R)]

/-- Interchanging the two block scales leaves the ratio factor unchanged. -/
theorem balancedRatioFactor_inv {R : ℝ} (hR : R ≠ 0) :
    balancedRatioFactor R⁻¹ = balancedRatioFactor R := by
  unfold balancedRatioFactor
  field_simp
  ring

/-- Ratio between logarithmic blocks whose indices differ by `k`, with
block width `1/m`. -/
def fineLogBlockRatio (m k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / (m : ℝ))

/-- Leading scalar envelope at logarithmic block distance `k`. -/
def fineLogBlockEnvelope (m k : ℕ) : ℝ :=
  blockRatioEnvelope m (fineLogBlockRatio m k)

theorem fineLogBlockRatio_pos (m k : ℕ) :
    0 < fineLogBlockRatio m k := by
  exact Real.exp_pos _

theorem fineLogBlockEnvelope_nonneg (m k : ℕ) :
    0 ≤ fineLogBlockEnvelope m k := by
  unfold fineLogBlockEnvelope blockRatioEnvelope
  have hR := (fineLogBlockRatio_pos m k).le
  exact div_nonneg
    (mul_nonneg (pow_nonneg hR m) (Real.rpow_nonneg hR _))
    (pow_nonneg (by linarith) (2 * m))

/-- Every near-ratio block costs only the common `4⁻ᵐ` factor and a
fixed numerical constant. -/
theorem fineLogBlockEnvelope_le_near
    {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    fineLogBlockEnvelope m k ≤
      Real.exp (1 / 4 : ℝ) * (4 : ℝ)⁻¹ ^ m := by
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hz₀ : 0 ≤ (k : ℝ) / (m : ℝ) := by positivity
  have hz₁ : (k : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm₀]
    exact_mod_cast hk
  let R := fineLogBlockRatio m k
  have hR : 0 < R := fineLogBlockRatio_pos m k
  have hbal₀ : 0 ≤ balancedRatioFactor R :=
    balancedRatioFactor_nonneg hR.le
  have hbal₁ : balancedRatioFactor R ≤ 1 :=
    balancedRatioFactor_le_one hR.le
  have hbalpow : balancedRatioFactor R ^ m ≤ 1 := by
    exact pow_le_one₀ hbal₀ hbal₁
  have hrpow : Real.rpow R (1 / 4 : ℝ) ≤ Real.exp (1 / 4 : ℝ) := by
    change R ^ (1 / 4 : ℝ) ≤ Real.exp (1 / 4 : ℝ)
    rw [Real.rpow_def_of_pos hR]
    change Real.exp
        (Real.log (Real.exp ((k : ℝ) / (m : ℝ))) * (1 / 4 : ℝ)) ≤ _
    rw [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [fineLogBlockEnvelope, show fineLogBlockRatio m k = R from rfl,
    blockRatioEnvelope_eq m hR]
  calc
    (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) *
          balancedRatioFactor R ^ m ≤
        (4 : ℝ)⁻¹ ^ m * Real.exp (1 / 4) * 1 := by
      gcongr
    _ = Real.exp (1 / 4 : ℝ) * (4 : ℝ)⁻¹ ^ m := by ring

/-- There are exactly `m+1` nonnegative block distances up to logarithmic
distance one, so the near-ratio Schur loss is explicitly linear. -/
theorem sum_fineLogBlockEnvelope_near_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (m + 1), fineLogBlockEnvelope m k ≤
      (m + 1 : ℝ) * Real.exp (1 / 4 : ℝ) * (4 : ℝ)⁻¹ ^ m := by
  calc
    ∑ k ∈ Finset.range (m + 1), fineLogBlockEnvelope m k ≤
        ∑ _k ∈ Finset.range (m + 1),
          Real.exp (1 / 4 : ℝ) * (4 : ℝ)⁻¹ ^ m := by
      apply Finset.sum_le_sum
      intro k hk
      exact fineLogBlockEnvelope_le_near hm (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk))
    _ = (m + 1 : ℝ) * Real.exp (1 / 4 : ℝ) * (4 : ℝ)⁻¹ ^ m := by
      simp
      ring

/-- Extending the near range to logarithmic distance four still costs only a
linear number of blocks.  This wider cutoff is convenient because the crude
far-tail exponential already beats `4⁻ᵐ` there. -/
theorem fineLogBlockEnvelope_le_moderate
    {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ 4 * m) :
    fineLogBlockEnvelope m k ≤
      Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hz₀ : 0 ≤ (k : ℝ) / (m : ℝ) := by positivity
  have hz₄ : (k : ℝ) / (m : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hm₀]
    exact_mod_cast hk
  let R := fineLogBlockRatio m k
  have hR : 0 < R := fineLogBlockRatio_pos m k
  have hbal₀ : 0 ≤ balancedRatioFactor R :=
    balancedRatioFactor_nonneg hR.le
  have hbal₁ : balancedRatioFactor R ≤ 1 :=
    balancedRatioFactor_le_one hR.le
  have hbalpow : balancedRatioFactor R ^ m ≤ 1 := by
    exact pow_le_one₀ hbal₀ hbal₁
  have hrpow : Real.rpow R (1 / 4 : ℝ) ≤ Real.exp 1 := by
    change R ^ (1 / 4 : ℝ) ≤ Real.exp 1
    rw [Real.rpow_def_of_pos hR]
    change Real.exp
        (Real.log (Real.exp ((k : ℝ) / (m : ℝ))) * (1 / 4 : ℝ)) ≤ _
    rw [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [fineLogBlockEnvelope, show fineLogBlockRatio m k = R from rfl,
    blockRatioEnvelope_eq m hR]
  calc
    (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) *
          balancedRatioFactor R ^ m ≤
        (4 : ℝ)⁻¹ ^ m * Real.exp 1 * 1 := by
      gcongr
    _ = Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by ring

/-- The block contribution through logarithmic distance four has precisely
the polynomial loss `(4m+1)` and the common exponential factor `4⁻ᵐ`. -/
theorem sum_fineLogBlockEnvelope_moderate_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (4 * m + 1), fineLogBlockEnvelope m k ≤
      (4 * m + 1 : ℝ) * Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
  calc
    ∑ k ∈ Finset.range (4 * m + 1), fineLogBlockEnvelope m k ≤
        ∑ _k ∈ Finset.range (4 * m + 1),
          Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
      apply Finset.sum_le_sum
      intro k hk
      exact fineLogBlockEnvelope_le_moderate hm (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk))
    _ = (4 * m + 1 : ℝ) * Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
      simp
      ring

/-- The non-overlapping finite head used in the final head-tail
decomposition. -/
theorem sum_fineLogBlockEnvelope_head_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (4 * m), fineLogBlockEnvelope m k ≤
      (4 * m : ℝ) * Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
  calc
    ∑ k ∈ Finset.range (4 * m), fineLogBlockEnvelope m k ≤
        ∑ _k ∈ Finset.range (4 * m),
          Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
      apply Finset.sum_le_sum
      intro k hk
      exact fineLogBlockEnvelope_le_moderate hm
        (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) (Nat.le_refl _))
    _ = (4 * m : ℝ) * Real.exp 1 * (4 : ℝ)⁻¹ ^ m := by
      simp
      ring

/-- Beyond logarithmic distance four, the exact leading envelope is bounded by
a fixed geometric tail.  This estimate is intentionally independent of `m`;
the missing `4⁻ᵐ` is recovered from the starting index of that tail. -/
theorem fineLogBlockEnvelope_le_far
    {m k : ℕ} (hm : 1 ≤ m) :
    fineLogBlockEnvelope m k ≤
      Real.exp (-(3 / 4 : ℝ) * (k : ℝ)) := by
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  let z : ℝ := (k : ℝ) / (m : ℝ)
  let R : ℝ := fineLogBlockRatio m k
  have hR : 0 < R := fineLogBlockRatio_pos m k
  have hbal₀ : 0 ≤ balancedRatioFactor R :=
    balancedRatioFactor_nonneg hR.le
  have hbal : balancedRatioFactor R ≤ 4 / R :=
    balancedRatioFactor_le_four_div hR
  have hfourdiv₀ : 0 ≤ 4 / R := by positivity
  have hfirst : fineLogBlockEnvelope m k ≤
      (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) * (4 / R) ^ m := by
    rw [fineLogBlockEnvelope, show fineLogBlockRatio m k = R from rfl,
      blockRatioEnvelope_eq m hR]
    have hcoef : 0 ≤ (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) :=
      mul_nonneg (pow_nonneg (by norm_num) m) (Real.rpow_nonneg hR.le _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbal₀ hbal m) hcoef
  have hsimplify :
      (4 : ℝ)⁻¹ ^ m * Real.rpow R (1 / 4) * (4 / R) ^ m =
        Real.rpow R (1 / 4) / R ^ m := by
    rw [div_pow]
    field_simp
    have hcancel : (1 / 4 : ℝ) ^ m * 4 ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      ((1 / 4 : ℝ) ^ m * Real.rpow R (1 / 4)) * 4 ^ m =
          Real.rpow R (1 / 4) * ((1 / 4 : ℝ) ^ m * 4 ^ m) := by ring
      _ = Real.rpow R (1 / 4) := by rw [hcancel, mul_one]
  have hrpow : Real.rpow R (1 / 4 : ℝ) = Real.exp (z / 4) := by
    change (Real.exp z) ^ (1 / 4 : ℝ) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos z), Real.log_exp]
    congr 1
    ring
  have hpow : R ^ m = Real.exp ((m : ℝ) * z) := by
    change Real.exp z ^ m = _
    rw [← Real.exp_nat_mul]
  have hmz : (m : ℝ) * z = (k : ℝ) := by
    dsimp [z]
    field_simp
  have hz_le_k : z ≤ (k : ℝ) := by
    dsimp [z]
    rw [div_le_iff₀ hm₀]
    have hk₀ : (0 : ℝ) ≤ k := by positivity
    have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hexp : Real.rpow R (1 / 4) / R ^ m ≤
      Real.exp (-(3 / 4 : ℝ) * (k : ℝ)) := by
    rw [hrpow, hpow, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    rw [hmz]
    nlinarith
  exact hfirst.trans (hsimplify.trans_le hexp)

/-- At the chosen cutoff, the geometric tail has already gained `4⁻ᵐ`.
The elementary inequality `4 < exp 3` is enough; no asymptotics enter. -/
theorem exp_neg_three_mul_le_four_inv_pow (m : ℕ) :
    Real.exp (-(3 : ℝ) * (m : ℝ)) ≤ (4 : ℝ)⁻¹ ^ m := by
  have hbase : Real.exp (-3) ≤ (4 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 4)).2
    have h := Real.add_one_le_exp (3 : ℝ)
    norm_num at h ⊢
    exact h
  rw [show -(3 : ℝ) * (m : ℝ) = (m : ℝ) * (-3 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos (-3)).le hbase m

/-- The entire far side of the logarithmic block decomposition is summable
with an explicit `m`-independent geometric constant and the exact `4⁻ᵐ`
gain. -/
theorem tsum_fineLogBlockEnvelope_far_le (m : ℕ) (hm : 1 ≤ m) :
    ∑' n : ℕ, fineLogBlockEnvelope m (4 * m + n) ≤
      (4 : ℝ)⁻¹ ^ m *
        (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := by
  let g : ℕ → ℝ := fun n ↦ Real.exp ((n : ℝ) * (-(3 / 4 : ℝ)))
  have hg : Summable g := by
    dsimp [g]
    exact Real.summable_exp_nat_mul_iff.mpr (by norm_num)
  have hright : Summable (fun n : ℕ ↦ (4 : ℝ)⁻¹ ^ m * g n) :=
    hg.mul_left _
  have hpoint : ∀ n : ℕ,
      fineLogBlockEnvelope m (4 * m + n) ≤ (4 : ℝ)⁻¹ ^ m * g n := by
    intro n
    calc
      fineLogBlockEnvelope m (4 * m + n) ≤
          Real.exp (-(3 / 4 : ℝ) * ((4 * m + n : ℕ) : ℝ)) :=
        fineLogBlockEnvelope_le_far hm
      _ = Real.exp (-(3 : ℝ) * (m : ℝ)) * g n := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ (4 : ℝ)⁻¹ ^ m * g n := by
        exact mul_le_mul_of_nonneg_right
          (exp_neg_three_mul_le_four_inv_pow m) (Real.exp_pos _).le
  have hleft : Summable (fun n : ℕ ↦
      fineLogBlockEnvelope m (4 * m + n)) :=
    hright.of_nonneg_of_le
      (fun n ↦ fineLogBlockEnvelope_nonneg m (4 * m + n)) hpoint
  calc
    ∑' n : ℕ, fineLogBlockEnvelope m (4 * m + n) ≤
        ∑' n : ℕ, (4 : ℝ)⁻¹ ^ m * g n :=
      hleft.tsum_le_tsum hpoint hright
    _ = (4 : ℝ)⁻¹ ^ m * ∑' n : ℕ, g n := by
      rw [tsum_mul_left]
    _ = (4 : ℝ)⁻¹ ^ m *
        (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := by
      congr 1
      dsimp [g]
      rw [tsum_congr (fun n ↦ Real.exp_nat_mul (-(3 / 4 : ℝ)) n),
        tsum_geometric_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (by norm_num))]

/-- The leading block envelope is summable at every positive Hermite order. -/
theorem summable_fineLogBlockEnvelope (m : ℕ) (hm : 1 ≤ m) :
    Summable (fineLogBlockEnvelope m) := by
  let g : ℕ → ℝ := fun k ↦ Real.exp ((k : ℝ) * (-(3 / 4 : ℝ)))
  have hg : Summable g := by
    dsimp [g]
    exact Real.summable_exp_nat_mul_iff.mpr (by norm_num)
  apply hg.of_nonneg_of_le (fineLogBlockEnvelope_nonneg m)
  intro k
  simpa [g, mul_comm] using fineLogBlockEnvelope_le_far (m := m) (k := k) hm

/-- All logarithmic ratios together have exactly a linear polynomial loss.
This is the explicit exponent `A = 1` required by the endpoint squeeze. -/
theorem tsum_fineLogBlockEnvelope_le_linear (m : ℕ) (hm : 1 ≤ m) :
    ∑' k : ℕ, fineLogBlockEnvelope m k ≤
      (m + 1 : ℝ) *
        (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
          (4 : ℝ)⁻¹ ^ m := by
  let q : ℝ := (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹
  have hexplt : Real.exp (-(3 / 4 : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have hq₀ : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsplit :=
    (summable_fineLogBlockEnvelope m hm).sum_add_tsum_nat_add (4 * m)
  have htail :
      ∑' n : ℕ, fineLogBlockEnvelope m (n + 4 * m) ≤
        (4 : ℝ)⁻¹ ^ m * q := by
    simpa [q, Nat.add_comm] using tsum_fineLogBlockEnvelope_far_le m hm
  rw [← hsplit]
  calc
    ∑ k ∈ Finset.range (4 * m), fineLogBlockEnvelope m k +
          ∑' n : ℕ, fineLogBlockEnvelope m (n + 4 * m) ≤
        (4 * m : ℝ) * Real.exp 1 * (4 : ℝ)⁻¹ ^ m +
          (4 : ℝ)⁻¹ ^ m * q :=
      add_le_add (sum_fineLogBlockEnvelope_head_le m hm) htail
    _ = ((4 * m : ℝ) * Real.exp 1 + q) * (4 : ℝ)⁻¹ ^ m := by ring
    _ ≤ (m + 1 : ℝ) * (4 * Real.exp 1 + q) * (4 : ℝ)⁻¹ ^ m := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) m)
      have hmcast₀ : (0 : ℝ) ≤ m := by positivity
      have hexp₀ : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith

/-- A finite family of logarithmic blocks has at most two members at each
`Nat.dist` from a fixed block.  Consequently every finite row or column costs
at most twice the one-sided envelope `tsum`. -/
theorem sum_fineLogBlockEnvelope_natDist_le_two_tsum
    (m p : ℕ) (U : Finset ℕ) (hm : 1 ≤ m) :
    ∑ q ∈ U, fineLogBlockEnvelope m (Nat.dist p q) ≤
      2 * ∑' k : ℕ, fineLogBlockEnvelope m k := by
  let Uleft := U.filter (fun q ↦ q ≤ p)
  let Uright := U.filter (fun q ↦ ¬ q ≤ p)
  have hinjLeft : Set.InjOn (fun q : ℕ ↦ p - q) Uleft := by
    intro a ha b hb hab
    have hap : a ≤ p := (Finset.mem_filter.mp ha).2
    have hbp : b ≤ p := (Finset.mem_filter.mp hb).2
    change p - a = p - b at hab
    omega
  have hinjRight : Set.InjOn (fun q : ℕ ↦ q - p) Uright := by
    intro a ha b hb hab
    have hpa : p < a := Nat.lt_of_not_ge (Finset.mem_filter.mp ha).2
    have hpb : p < b := Nat.lt_of_not_ge (Finset.mem_filter.mp hb).2
    change a - p = b - p at hab
    omega
  have hleft :
      ∑ q ∈ Uleft, fineLogBlockEnvelope m (Nat.dist p q) ≤
        ∑' k : ℕ, fineLogBlockEnvelope m k := by
    calc
      ∑ q ∈ Uleft, fineLogBlockEnvelope m (Nat.dist p q) =
          ∑ q ∈ Uleft, fineLogBlockEnvelope m (p - q) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hq).2]
      _ = ∑ k ∈ Uleft.image (fun q : ℕ ↦ p - q),
          fineLogBlockEnvelope m k := by
        symm
        exact Finset.sum_image hinjLeft
      _ ≤ ∑' k : ℕ, fineLogBlockEnvelope m k :=
        (summable_fineLogBlockEnvelope m hm).sum_le_tsum _
          (fun k _ ↦ fineLogBlockEnvelope_nonneg m k)
  have hright :
      ∑ q ∈ Uright, fineLogBlockEnvelope m (Nat.dist p q) ≤
        ∑' k : ℕ, fineLogBlockEnvelope m k := by
    calc
      ∑ q ∈ Uright, fineLogBlockEnvelope m (Nat.dist p q) =
          ∑ q ∈ Uright, fineLogBlockEnvelope m (q - p) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hpq : p ≤ q :=
          (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2).le
        rw [Nat.dist_eq_sub_of_le hpq]
      _ = ∑ k ∈ Uright.image (fun q : ℕ ↦ q - p),
          fineLogBlockEnvelope m k := by
        symm
        exact Finset.sum_image hinjRight
      _ ≤ ∑' k : ℕ, fineLogBlockEnvelope m k :=
        (summable_fineLogBlockEnvelope m hm).sum_le_tsum _
          (fun k _ ↦ fineLogBlockEnvelope_nonneg m k)
  calc
    ∑ q ∈ U, fineLogBlockEnvelope m (Nat.dist p q) =
        (∑ q ∈ Uleft, fineLogBlockEnvelope m (Nat.dist p q)) +
          ∑ q ∈ Uright, fineLogBlockEnvelope m (Nat.dist p q) := by
      simpa only [Uleft, Uright] using
        (Finset.sum_filter_add_sum_filter_not U (fun q ↦ q ≤ p)
          (fun q ↦ fineLogBlockEnvelope m (Nat.dist p q))).symm
    _ ≤ (∑' k : ℕ, fineLogBlockEnvelope m k) +
          ∑' k : ℕ, fineLogBlockEnvelope m k := add_le_add hleft hright
    _ = 2 * ∑' k : ℕ, fineLogBlockEnvelope m k := by ring

/-- Operator-valued finite-section form of the full leading cross ceiling.
Once each block row and column is bounded by `C` times the scalar all-ratio
envelope, coherent recombination is controlled with the same explicit linear
loss and no additional power of `m`. -/
theorem sum_norm_sq_le_linear_block_ceiling
    {iota kappa E F : Type*} [Fintype iota] [Fintype kappa]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : iota → kappa → E →L[ℂ] F) (x : kappa → E)
    (m : ℕ) (hm : 1 ≤ m) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤
      C * ∑' k : ℕ, fineLogBlockEnvelope m k)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤
      C * ∑' k : ℕ, fineLogBlockEnvelope m k) :
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
      (C * ((m + 1 : ℝ) *
        (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
          (4 : ℝ)⁻¹ ^ m)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  let L : ℝ := (m + 1 : ℝ) *
    (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
      (4 : ℝ)⁻¹ ^ m
  have hq₀ : 0 ≤ (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := by
    have hlt : Real.exp (-(3 / 4 : ℝ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    positivity
  have hL₀ : 0 ≤ L := by
    dsimp [L]
    positivity
  have henv : (∑' k : ℕ, fineLogBlockEnvelope m k) ≤ L := by
    simpa only [L] using tsum_fineLogBlockEnvelope_le_linear m hm
  have hbound : C * (∑' k : ℕ, fineLogBlockEnvelope m k) ≤ C * L :=
    mul_le_mul_of_nonneg_left henv hC
  have henergy := sum_norm_sq_operatorBlock_mulVec_le A x
    (fun i ↦ (hrow i).trans hbound) (fun j ↦ (hcol j).trans hbound)
    (mul_nonneg hC hL₀)
  simpa only [L, pow_two] using henergy

/-- Dependent-space form of the finite leading block ceiling.  This is the
version used by physical logarithmic blocks, whose finite coefficient types
vary with the block number. -/
theorem sum_norm_sq_le_linear_dependent_block_ceiling
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (E : kappa → Type*) (F : iota → Type*)
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (A : ∀ i j, E j →L[ℂ] F i) (x : ∀ j, E j)
    (m : ℕ) (hm : 1 ≤ m) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤
      C * ∑' k : ℕ, fineLogBlockEnvelope m k)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤
      C * ∑' k : ℕ, fineLogBlockEnvelope m k) :
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
      (C * ((m + 1 : ℝ) *
        (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
          (4 : ℝ)⁻¹ ^ m)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  let L : ℝ := (m + 1 : ℝ) *
    (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
      (4 : ℝ)⁻¹ ^ m
  have hq₀ : 0 ≤ (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := by
    have hlt : Real.exp (-(3 / 4 : ℝ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    positivity
  have hL₀ : 0 ≤ L := by
    dsimp [L]
    positivity
  have henv : (∑' k : ℕ, fineLogBlockEnvelope m k) ≤ L := by
    simpa only [L] using tsum_fineLogBlockEnvelope_le_linear m hm
  have hbound : C * (∑' k : ℕ, fineLogBlockEnvelope m k) ≤ C * L :=
    mul_le_mul_of_nonneg_left henv hC
  have henergy := sum_norm_sq_dependentOperatorBlock_mulVec_le E F A x
    (fun i ↦ (hrow i).trans hbound) (fun j ↦ (hcol j).trans hbound)
    (mul_nonneg hC hL₀) (mul_nonneg hC hL₀)
  simpa only [L, pow_two] using henergy

end

end MeyerGeneralProblem
