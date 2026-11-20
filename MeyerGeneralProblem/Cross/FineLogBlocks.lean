module

public import MeyerGeneralProblem.Carrier.SignedSquare
public import MeyerGeneralProblem.Cross.AmplitudeMultiplier
public import MeyerGeneralProblem.Cross.LeadingNorm
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Dist

@[expose] public section

/-!
# Concrete fine logarithmic carrier blocks

The blocks in this module are the actual squared-magnitude blocks of a
two-sided carrier.  A block may contain points from both physical rays.  The
signed-square tail gap implies physical separation even across the two rays,
so no sign decomposition is required.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped Matrix.Norms.L2Operator

/-- Lower squared-magnitude scale of logarithmic block `p`. -/
def fineLogBlockScale (m p : ℕ) : ℝ :=
  Real.exp ((p : ℝ) / (m : ℝ))

theorem fineLogBlockScale_pos (m p : ℕ) :
    0 < fineLogBlockScale m p := Real.exp_pos _

theorem one_le_fineLogBlockScale
    (m p : ℕ) (hm : 1 ≤ m) :
    1 ≤ fineLogBlockScale m p := by
  rw [fineLogBlockScale, Real.one_le_exp_iff]
  positivity

theorem fineLogBlockScale_mono
    (m : ℕ) (hm : 1 ≤ m) :
    Monotone (fineLogBlockScale m) := by
  intro p q hpq
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  rw [fineLogBlockScale, fineLogBlockScale, Real.exp_le_exp]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hpq) hmR.le

theorem fineLogBlockScale_succ
    (m p : ℕ) (hm : 1 ≤ m) :
    fineLogBlockScale m (p + 1) =
      fineLogBlockScale m p * Real.exp (1 / (m : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  unfold fineLogBlockScale
  rw [← Real.exp_add]
  congr 1
  push_cast
  field_simp [hmR]

theorem fineLogBlockScale_succ_le_exp_mul
    (m p : ℕ) (hm : 1 ≤ m) :
    fineLogBlockScale m (p + 1) ≤
      Real.exp 1 * fineLogBlockScale m p := by
  rw [fineLogBlockScale_succ m p hm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hexp : Real.exp (1 / (m : ℝ)) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp, div_le_one hmR]
    exact_mod_cast hm
  nlinarith [fineLogBlockScale_pos m p]

theorem fineLogBlockScale_div_eq_fineLogBlockRatio
    (m : ℕ) (hm : 1 ≤ m) {p q : ℕ} (hqp : q ≤ p) :
    fineLogBlockScale m p / fineLogBlockScale m q =
      fineLogBlockRatio m (p - q) := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  unfold fineLogBlockScale fineLogBlockRatio
  rw [← Real.exp_sub]
  congr 1
  rw [Nat.cast_sub hqp]
  field_simp [hmR]

/-- Exact carrier block in the half-open squared-magnitude interval
`[exp (p/m), exp ((p+1)/m))`. -/
def fineLogCarrierBlockSet
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) : Set ℤ :=
  {j | j ∉ F ∧
    fineLogBlockScale m p ≤ (Λ j) ^ 2 ∧
    (Λ j) ^ 2 < fineLogBlockScale m (p + 1)}

theorem fineLogCarrierBlockSet_finite
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) :
    (fineLogCarrierBlockSet Λ F m p).Finite := by
  let U := fineLogBlockScale m (p + 1)
  apply (Λ.finite_indices_in_Icc (-Real.sqrt U) (Real.sqrt U)).subset
  intro j hj
  change j ∉ F ∧ fineLogBlockScale m p ≤ (Λ j) ^ 2 ∧
    (Λ j) ^ 2 < U at hj
  have habs : |Λ j| ≤ Real.sqrt U := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hj.2.2.le
  exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩

/-- Finite carrier block cut out by `fineLogCarrierBlockSet`. -/
def fineLogCarrierBlock
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) : Finset ℤ :=
  (fineLogCarrierBlockSet_finite Λ F m p).toFinset

@[simp]
theorem mem_fineLogCarrierBlock
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    {m p : ℕ} {j : ℤ} :
    j ∈ fineLogCarrierBlock Λ F m p ↔
      j ∉ F ∧
      fineLogBlockScale m p ≤ (Λ j) ^ 2 ∧
      (Λ j) ^ 2 < fineLogBlockScale m (p + 1) := by
  exact (fineLogCarrierBlockSet_finite Λ F m p).mem_toFinset

/-- Finite index type of one logarithmic carrier block. -/
abbrev FineLogBlockIndex
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) :=
  fineLogCarrierBlock Λ F m p

/-- Physical carrier point associated to a fine-block index. -/
def fineLogBlockPoint
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) : FineLogBlockIndex Λ F m p → ℝ :=
  fun j => Λ j.1

/-- Unit logarithmic coordinate inside one fine block. -/
def fineLogBlockCoordinate
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p : ℕ) (j : FineLogBlockIndex Λ F m p) : ℝ :=
  (m : ℝ) * Real.log ((Λ j.1) ^ 2 / fineLogBlockScale m p)

theorem fineLogBlockCoordinate_mem_Icc
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (j : FineLogBlockIndex Λ F m p) :
    fineLogBlockCoordinate Λ F m p j ∈ Icc (0 : ℝ) 1 := by
  have hj := mem_fineLogCarrierBlock.mp j.property
  let S := (Λ j.1) ^ 2
  let M := fineLogBlockScale m p
  have hM : 0 < M := fineLogBlockScale_pos m p
  have hS : 0 < S := hM.trans_le hj.2.1
  have hratio : 1 ≤ S / M := (one_le_div₀ hM).2 hj.2.1
  have hupper : S / M < Real.exp (1 / (m : ℝ)) := by
    rw [div_lt_iff₀ hM]
    simpa only [S, M, fineLogBlockScale_succ m p hm, mul_comm] using hj.2.2
  have hlog0 : 0 ≤ Real.log (S / M) :=
    (Real.log_nonneg_iff (div_pos hS hM)).2 hratio
  have hlog1 : Real.log (S / M) < 1 / (m : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (div_pos hS hM)]
    exact hupper
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  change 0 ≤ (m : ℝ) * Real.log (S / M) ∧
    (m : ℝ) * Real.log (S / M) ≤ 1
  constructor
  · positivity
  · have hmul := (lt_div_iff₀ hmR).mp hlog1
    nlinarith

theorem fineLogBlockScale_mul_exp_coordinate
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (j : FineLogBlockIndex Λ F m p) :
    fineLogBlockScale m p *
        Real.exp (fineLogBlockCoordinate Λ F m p j / (m : ℝ)) =
      (Λ j.1) ^ 2 := by
  have hj := mem_fineLogCarrierBlock.mp j.property
  let S := (Λ j.1) ^ 2
  let M := fineLogBlockScale m p
  have hM : 0 < M := fineLogBlockScale_pos m p
  have hS : 0 < S := hM.trans_le hj.2.1
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hcoord : fineLogBlockCoordinate Λ F m p j / (m : ℝ) =
      Real.log (S / M) := by
    unfold fineLogBlockCoordinate
    dsimp only [S, M]
    field_simp [hmR]
  rw [hcoord, Real.exp_log (div_pos hS hM)]
  field_simp [hM.ne']
  dsimp only [S, M]

/-- Natural block number of a positive squared magnitude. -/
def fineLogBlockNumber (m : ℕ) (S : ℝ) : ℕ :=
  ⌊(m : ℝ) * Real.log S⌋₊

/-- The floor block number places every noncentral tail point in its declared
half-open logarithmic block. -/
theorem mem_fineLogCarrierBlock_blockNumber
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    {m : ℕ} (hm : 1 ≤ m) {j : ℤ}
    (hjF : j ∉ F) (hjSq : 1 < (Λ j) ^ 2) :
    j ∈ fineLogCarrierBlock Λ F m
      (fineLogBlockNumber m ((Λ j) ^ 2)) := by
  let S := (Λ j) ^ 2
  let x := (m : ℝ) * Real.log S
  let p := fineLogBlockNumber m S
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hS : 0 < S := zero_lt_one.trans hjSq
  have hlogS : 0 < Real.log S := Real.log_pos hjSq
  have hx : 0 ≤ x := (mul_pos hmR hlogS).le
  have hpLower : (p : ℝ) ≤ x := by
    exact Nat.floor_le hx
  have hpUpper : x < (p : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  have hlowerLog : (p : ℝ) / (m : ℝ) ≤ Real.log S := by
    dsimp only [x] at hpLower
    exact (div_le_iff₀ hmR).2 (by simpa [mul_comm] using hpLower)
  have hupperLog : Real.log S < ((p : ℝ) + 1) / (m : ℝ) := by
    dsimp only [x] at hpUpper
    exact (lt_div_iff₀ hmR).2 (by simpa [mul_comm] using hpUpper)
  apply mem_fineLogCarrierBlock.mpr
  refine ⟨hjF, ?_, ?_⟩
  · change Real.exp ((p : ℝ) / (m : ℝ)) ≤ S
    rw [← Real.exp_log hS]
    exact Real.exp_le_exp.mpr hlowerLog
  · change S < Real.exp (((p + 1 : ℕ) : ℝ) / (m : ℝ))
    rw [← Real.exp_log hS]
    apply Real.exp_lt_exp.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hupperLog

/-- The half-open fine logarithmic blocks are disjoint. -/
theorem fineLogCarrierBlock_index_unique
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    {m p q : ℕ} (hm : 1 ≤ m) {j : ℤ}
    (hjp : j ∈ fineLogCarrierBlock Λ F m p)
    (hjq : j ∈ fineLogCarrierBlock Λ F m q) :
    p = q := by
  have hp := mem_fineLogCarrierBlock.mp hjp
  have hq := mem_fineLogCarrierBlock.mp hjq
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hpSucc : p + 1 ≤ q := by omega
    have hscale := fineLogBlockScale_mono m hm hpSucc
    linarith
  · exact hpq
  · have hqSucc : q + 1 ≤ p := by omega
    have hscale := fineLogBlockScale_mono m hm hqSucc
    linarith

/-- Outside the central exceptional set, the natural fine logarithmic blocks
form an exact partition of the carrier indices. -/
theorem fineLogCarrierBlock_existsUnique
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    {m : ℕ} (hm : 1 ≤ m) {j : ℤ}
    (hjF : j ∉ F) (hjSq : 1 < (Λ j) ^ 2) :
    ∃! p : ℕ, j ∈ fineLogCarrierBlock Λ F m p := by
  refine ⟨fineLogBlockNumber m ((Λ j) ^ 2),
    mem_fineLogCarrierBlock_blockNumber hm hjF hjSq, ?_⟩
  intro q hjq
  exact fineLogCarrierBlock_index_unique hm hjq
    (mem_fineLogCarrierBlock_blockNumber hm hjF hjSq)

/-- Coarse physical radius enclosing the entire magnitude block. -/
def fineLogBlockRadius (m p : ℕ) : ℝ :=
  Real.sqrt (Real.exp 1 * fineLogBlockScale m p)

/-- Separation scale forced by unit signed-square gaps inside block `p`. -/
def fineLogBlockPhysicalSeparation (m p : ℕ) : ℝ :=
  (2 * fineLogBlockRadius m p)⁻¹

/-- Coarse physical diameter of fine block `p`. -/
def fineLogBlockPhysicalDiameter (m p : ℕ) : ℝ :=
  2 * fineLogBlockRadius m p

theorem fineLogBlockRadius_pos (m p : ℕ) :
    0 < fineLogBlockRadius m p := by
  unfold fineLogBlockRadius
  exact Real.sqrt_pos.2
    (mul_pos (Real.exp_pos 1) (fineLogBlockScale_pos m p))

theorem fineLogBlockRadius_sq (m p : ℕ) :
    fineLogBlockRadius m p ^ 2 =
      Real.exp 1 * fineLogBlockScale m p := by
  unfold fineLogBlockRadius
  rw [Real.sq_sqrt (mul_nonneg (Real.exp_pos 1).le
    (fineLogBlockScale_pos m p).le)]

theorem fineLogBlockRadius_mono
    (m : ℕ) (hm : 1 ≤ m) :
    Monotone (fineLogBlockRadius m) := by
  intro p q hpq
  unfold fineLogBlockRadius
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (fineLogBlockScale_mono m hm hpq)
    (Real.exp_pos 1).le

theorem fineLogBlockPoint_sq_le_radius_sq
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (j : FineLogBlockIndex Λ F m p) :
    (fineLogBlockPoint Λ F m p j) ^ 2 ≤
      fineLogBlockRadius m p ^ 2 := by
  rw [fineLogBlockRadius_sq]
  exact (mem_fineLogCarrierBlock.mp j.property).2.2.le.trans
    (fineLogBlockScale_succ_le_exp_mul m p hm)

theorem fineLogBlockPoint_abs_le_radius
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (j : FineLogBlockIndex Λ F m p) :
    |fineLogBlockPoint Λ F m p j| ≤ fineLogBlockRadius m p := by
  have hsq := fineLogBlockPoint_sq_le_radius_sq Λ F m hm p j
  have hR := fineLogBlockRadius_pos m p
  nlinarith [sq_abs (fineLogBlockPoint Λ F m p j)]

theorem fineLogBlockPoint_separated
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (i j : FineLogBlockIndex Λ F m p) (hij : i ≠ j) :
    fineLogBlockPhysicalSeparation m p ≤
      |fineLogBlockPoint Λ F m p i - fineLogBlockPoint Λ F m p j| := by
  have hi := mem_fineLogCarrierBlock.mp i.property
  have hj := mem_fineLogCarrierBlock.mp j.property
  have hidx : (i : ℤ) ≠ (j : ℤ) := Subtype.coe_injective.ne hij
  have hsigned := hsep i j hi.1 hj.1 hidx
  have hupper := abs_signedSquare_sub_le_abs_sub_mul_abs_add (Λ i) (Λ j)
  have hiR := fineLogBlockPoint_abs_le_radius Λ F m hm p i
  have hjR := fineLogBlockPoint_abs_le_radius Λ F m hm p j
  change |Λ i| ≤ fineLogBlockRadius m p at hiR
  change |Λ j| ≤ fineLogBlockRadius m p at hjR
  have hR : 0 < fineLogBlockRadius m p := fineLogBlockRadius_pos m p
  unfold fineLogBlockPhysicalSeparation
  rw [inv_le_iff_one_le_mul₀' (mul_pos two_pos hR)]
  calc
    1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)| := hsigned
    _ ≤ |Λ i - Λ j| * (|Λ i| + |Λ j|) := hupper
    _ ≤ |Λ i - Λ j| * (2 * fineLogBlockRadius m p) := by
      gcongr
      linarith
    _ = 2 * fineLogBlockRadius m p * |Λ i - Λ j| := by ring

theorem fineLogBlockPoint_diameter
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (i j : FineLogBlockIndex Λ F m p) :
    |fineLogBlockPoint Λ F m p i - fineLogBlockPoint Λ F m p j| ≤
      fineLogBlockPhysicalDiameter m p := by
  have hi := fineLogBlockPoint_abs_le_radius Λ F m hm p i
  have hj := fineLogBlockPoint_abs_le_radius Λ F m hm p j
  calc
    |fineLogBlockPoint Λ F m p i - fineLogBlockPoint Λ F m p j| ≤
        |fineLogBlockPoint Λ F m p i| +
          |fineLogBlockPoint Λ F m p j| := abs_sub _ _
    _ ≤ 2 * fineLogBlockRadius m p := by linarith
    _ = fineLogBlockPhysicalDiameter m p := rfl

/-- Absolute squared-norm constant for a fine-block Fourier rectangle. -/
def fineLogRectangleSqConstant : ℝ :=
  32 * fourierRectangleConstant * Real.exp 1

theorem fineLogRectangleSqConstant_pos :
    0 < fineLogRectangleSqConstant := by
  unfold fineLogRectangleSqConstant
  exact mul_pos
    (mul_pos (by norm_num) fourierRectangleConstant_pos)
    (Real.exp_pos 1)

/-- Geometric factor in the absorbed Fourier-rectangle estimate for blocks
`p` and `q`. -/
def fineLogRectangleGeometryFactor (m p q : ℕ) : ℝ :=
  ((fineLogBlockPhysicalSeparation m p)⁻¹ +
      fineLogBlockPhysicalSeparation m p *
        fineLogBlockPhysicalDiameter m q ^ 2) *
    (fineLogBlockPhysicalDiameter m p +
      (fineLogBlockPhysicalSeparation m q)⁻¹)

theorem fineLogRectangleGeometryFactor_le
    (m : ℕ) (hm : 1 ≤ m) {p q : ℕ} (hqp : q ≤ p) :
    fineLogRectangleGeometryFactor m p q ≤
      16 * Real.exp 1 * fineLogBlockScale m p := by
  let rp := fineLogBlockRadius m p
  let rq := fineLogBlockRadius m q
  have hrp : 0 < rp := fineLogBlockRadius_pos m p
  have hrq : 0 < rq := fineLogBlockRadius_pos m q
  have hrq_le : rq ≤ rp := fineLogBlockRadius_mono m hm hqp
  have hδp : fineLogBlockPhysicalSeparation m p = (2 * rp)⁻¹ := rfl
  have hδq : fineLogBlockPhysicalSeparation m q = (2 * rq)⁻¹ := rfl
  have hDp : fineLogBlockPhysicalDiameter m p = 2 * rp := rfl
  have hDq : fineLogBlockPhysicalDiameter m q = 2 * rq := rfl
  have hδpInv : (fineLogBlockPhysicalSeparation m p)⁻¹ = 2 * rp := by
    rw [hδp, inv_inv]
  have hδqInv : (fineLogBlockPhysicalSeparation m q)⁻¹ = 2 * rq := by
    rw [hδq, inv_inv]
  have hrqSq : rq ^ 2 ≤ rp ^ 2 := by nlinarith
  have hmixed : fineLogBlockPhysicalSeparation m p *
      fineLogBlockPhysicalDiameter m q ^ 2 ≤ 2 * rp := by
    rw [hδp, hDq]
    calc
      (2 * rp)⁻¹ * (2 * rq) ^ 2 ≤
          (2 * rp)⁻¹ * (2 * rp) ^ 2 := by
        gcongr
      _ = 2 * rp := by field_simp [hrp.ne']
  have hfirst : (fineLogBlockPhysicalSeparation m p)⁻¹ +
      fineLogBlockPhysicalSeparation m p *
        fineLogBlockPhysicalDiameter m q ^ 2 ≤ 4 * rp := by
    rw [hδpInv]
    linarith
  have hsecond : fineLogBlockPhysicalDiameter m p +
      (fineLogBlockPhysicalSeparation m q)⁻¹ ≤ 4 * rp := by
    rw [hDp, hδqInv]
    linarith
  have hfirst0 : 0 ≤ (fineLogBlockPhysicalSeparation m p)⁻¹ +
      fineLogBlockPhysicalSeparation m p *
        fineLogBlockPhysicalDiameter m q ^ 2 := by
    rw [hδpInv]
    exact add_nonneg (mul_nonneg (by norm_num) hrp.le)
      (mul_nonneg (inv_nonneg.mpr (mul_pos two_pos hrp).le) (sq_nonneg _))
  have hsecond0 : 0 ≤ fineLogBlockPhysicalDiameter m p +
      (fineLogBlockPhysicalSeparation m q)⁻¹ := by
    rw [hDp, hδqInv]
    positivity
  rw [fineLogRectangleGeometryFactor]
  calc
    ((fineLogBlockPhysicalSeparation m p)⁻¹ +
        fineLogBlockPhysicalSeparation m p *
          fineLogBlockPhysicalDiameter m q ^ 2) *
      (fineLogBlockPhysicalDiameter m p +
        (fineLogBlockPhysicalSeparation m q)⁻¹) ≤
        (4 * rp) * (4 * rp) :=
      mul_le_mul hfirst hsecond hsecond0 (by positivity)
    _ = 16 * rp ^ 2 := by ring
    _ = 16 * Real.exp 1 * fineLogBlockScale m p := by
      rw [show rp ^ 2 = Real.exp 1 * fineLogBlockScale m p by
        exact fineLogBlockRadius_sq m p]
      ring

theorem fineLogBlockPhysicalSeparation_le_diameter
    (m p : ℕ) (hm : 1 ≤ m) :
    fineLogBlockPhysicalSeparation m p ≤
      fineLogBlockPhysicalDiameter m p := by
  let r := fineLogBlockRadius m p
  have hr : 0 < r := fineLogBlockRadius_pos m p
  have hM := one_le_fineLogBlockScale m p hm
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hrsq : 1 ≤ r ^ 2 := by
    rw [show r ^ 2 = Real.exp 1 * fineLogBlockScale m p by
      exact fineLogBlockRadius_sq m p]
    nlinarith
  unfold fineLogBlockPhysicalSeparation fineLogBlockPhysicalDiameter
  rw [inv_le_iff_one_le_mul₀' (mul_pos two_pos hr)]
  nlinarith

theorem fineLogBlock_negativeRectangle_sq_le
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|)
    (m : ℕ) (hm : 1 ≤ m)
    {p q : ℕ} (hqp : q ≤ p) :
    ‖finiteNegativeFourierRectangle
        (fineLogBlockPoint Λ F m p)
        (fineLogBlockPoint Λ F m q)‖ ^ 2 ≤
      fineLogRectangleSqConstant * fineLogBlockScale m p := by
  have hδp : 0 < fineLogBlockPhysicalSeparation m p := by
    unfold fineLogBlockPhysicalSeparation
    exact inv_pos.mpr (mul_pos two_pos (fineLogBlockRadius_pos m p))
  have hδq : 0 < fineLogBlockPhysicalSeparation m q := by
    unfold fineLogBlockPhysicalSeparation
    exact inv_pos.mpr (mul_pos two_pos (fineLogBlockRadius_pos m q))
  have hrect := finiteSeparatedNegativeFourierRectangle_l2OpNorm_sq_le
    (fineLogBlockPoint Λ F m p) (fineLogBlockPoint Λ F m q)
    (δx := fineLogBlockPhysicalSeparation m p)
    (δy := fineLogBlockPhysicalSeparation m q)
    (Lx := fineLogBlockPhysicalDiameter m p)
    (Wy := fineLogBlockPhysicalDiameter m q)
    hδp hδq
    (mul_nonneg (by norm_num) (fineLogBlockRadius_pos m p).le)
    (mul_nonneg (by norm_num) (fineLogBlockRadius_pos m q).le)
    ((fineLogBlockPhysicalSeparation_le_diameter m p hm).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr hδq.le)))
    (fineLogBlockPoint_separated hsep m hm p)
    (fineLogBlockPoint_separated hsep m hm q)
    (fineLogBlockPoint_diameter Λ F m hm p)
    (fineLogBlockPoint_diameter Λ F m hm q)
  have hgeom := fineLogRectangleGeometryFactor_le m hm hqp
  calc
    ‖finiteNegativeFourierRectangle
        (fineLogBlockPoint Λ F m p)
        (fineLogBlockPoint Λ F m q)‖ ^ 2 ≤
      2 * fourierRectangleConstant *
        fineLogRectangleGeometryFactor m p q := by
      simpa only [fineLogRectangleGeometryFactor, mul_assoc] using hrect
    _ ≤ 2 * fourierRectangleConstant *
        (16 * Real.exp 1 * fineLogBlockScale m p) :=
      mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg (by norm_num) fourierRectangleConstant_pos.le)
    _ = fineLogRectangleSqConstant * fineLogBlockScale m p := by
      unfold fineLogRectangleSqConstant
      ring

theorem fineLogBlock_positiveRectangle_sq_le
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|)
    (m : ℕ) (hm : 1 ≤ m)
    {p q : ℕ} (hqp : q ≤ p) :
    ‖finiteFourierRectangle
        (fineLogBlockPoint Λ F m p)
        (fineLogBlockPoint Λ F m q)‖ ^ 2 ≤
      fineLogRectangleSqConstant * fineLogBlockScale m p := by
  have hδp : 0 < fineLogBlockPhysicalSeparation m p := by
    unfold fineLogBlockPhysicalSeparation
    exact inv_pos.mpr (mul_pos two_pos (fineLogBlockRadius_pos m p))
  have hδq : 0 < fineLogBlockPhysicalSeparation m q := by
    unfold fineLogBlockPhysicalSeparation
    exact inv_pos.mpr (mul_pos two_pos (fineLogBlockRadius_pos m q))
  have hrect := finiteSeparatedFourierRectangle_l2OpNorm_sq_le
    (fineLogBlockPoint Λ F m p) (fineLogBlockPoint Λ F m q)
    (δx := fineLogBlockPhysicalSeparation m p)
    (δy := fineLogBlockPhysicalSeparation m q)
    (Lx := fineLogBlockPhysicalDiameter m p)
    (Wy := fineLogBlockPhysicalDiameter m q)
    hδp hδq
    (mul_nonneg (by norm_num) (fineLogBlockRadius_pos m p).le)
    (mul_nonneg (by norm_num) (fineLogBlockRadius_pos m q).le)
    ((fineLogBlockPhysicalSeparation_le_diameter m p hm).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr hδq.le)))
    (fineLogBlockPoint_separated hsep m hm p)
    (fineLogBlockPoint_separated hsep m hm q)
    (fineLogBlockPoint_diameter Λ F m hm p)
    (fineLogBlockPoint_diameter Λ F m hm q)
  have hgeom := fineLogRectangleGeometryFactor_le m hm hqp
  calc
    ‖finiteFourierRectangle
        (fineLogBlockPoint Λ F m p)
        (fineLogBlockPoint Λ F m q)‖ ^ 2 ≤
      2 * fourierRectangleConstant *
        fineLogRectangleGeometryFactor m p q := by
      simpa only [fineLogRectangleGeometryFactor, mul_assoc] using hrect
    _ ≤ 2 * fourierRectangleConstant *
        (16 * Real.exp 1 * fineLogBlockScale m p) :=
      mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg (by norm_num) fourierRectangleConstant_pos.le)
    _ = fineLogRectangleSqConstant * fineLogBlockScale m p := by
      unfold fineLogRectangleSqConstant
      ring

@[simp]
theorem crossMehlerLeadingPhase_eq_gramPhase_neg (x y : ℝ) :
    crossMehlerLeadingPhase x y = gramPhase (-y) x := by
  unfold crossMehlerLeadingPhase gramPhase
  congr 1
  push_cast
  ring

@[simp]
theorem star_normalizedCrossBlockAmplitude
    (m : ℕ) (R u v : ℝ) :
    star (normalizedCrossBlockAmplitude m R u v) =
      normalizedCrossBlockAmplitude m R u v := by
  unfold normalizedCrossBlockAmplitude
  simp

/-- Symmetric spatial scale coefficient of a physical leading block. -/
def fineLogLeadingGeometricCoefficient (m p q : ℕ) : ℝ :=
  (fineLogBlockScale m p * fineLogBlockScale m q) ^
      ((m : ℝ) - 1 / 4) /
    (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m)

theorem fineLogLeadingGeometricCoefficient_comm (m p q : ℕ) :
    fineLogLeadingGeometricCoefficient m p q =
      fineLogLeadingGeometricCoefficient m q p := by
  unfold fineLogLeadingGeometricCoefficient
  rw [mul_comm (fineLogBlockScale m p) (fineLogBlockScale m q),
    add_comm (fineLogBlockScale m p) (fineLogBlockScale m q)]

/-- The actual physical leading kernel restricted to two full magnitude
blocks. -/
def fineLogLeadingBlockMatrix
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m p q : ℕ) :
    Matrix (FineLogBlockIndex Λ F m p)
      (FineLogBlockIndex Λ F m q) ℂ :=
  fun i j => normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)

theorem fineLogLeadingBlockMatrix_factorization
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) :
    fineLogLeadingBlockMatrix Λ F m p q =
      ((gramNormalization m * fineLogLeadingGeometricCoefficient m p q : ℝ) : ℂ) •
        amplitudeWeightedMatrix
          (fun i : FineLogBlockIndex Λ F m p =>
            fun j : FineLogBlockIndex Λ F m q =>
            normalizedCrossBlockAmplitude m
            (fineLogBlockScale m p / fineLogBlockScale m q)
            (fineLogBlockCoordinate Λ F m p i)
            (fineLogBlockCoordinate Λ F m q j))
          (finiteNegativeFourierRectangle
            (fineLogBlockPoint Λ F m p)
            (fineLogBlockPoint Λ F m q)) := by
  ext i j
  rw [fineLogLeadingBlockMatrix, normalizedCrossSpatialLeadingTerm]
  rw [← fineLogBlockScale_mul_exp_coordinate Λ F m hm p i,
    ← fineLogBlockScale_mul_exp_coordinate Λ F m hm q j]
  rw [gramNormalizedCrossLeadingTerm_logBlock_factorization m hm
    (fineLogBlockScale_pos m p) (fineLogBlockScale_pos m q)]
  unfold fineLogLeadingGeometricCoefficient
  change
    ((((gramNormalization m *
        (fineLogBlockScale m p * fineLogBlockScale m q) ^
          ((m : ℝ) - 1 / 4) /
        (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m) : ℝ) : ℂ) *
      normalizedCrossBlockAmplitude m
        (fineLogBlockScale m p / fineLogBlockScale m q)
        (fineLogBlockCoordinate Λ F m p i)
        (fineLogBlockCoordinate Λ F m q j)) *
      crossMehlerLeadingPhase (Λ i) (Λ j) =
    ((gramNormalization m *
        ((fineLogBlockScale m p * fineLogBlockScale m q) ^
          ((m : ℝ) - 1 / 4) /
        (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m)) : ℝ) : ℂ) *
      (normalizedCrossBlockAmplitude m
        (fineLogBlockScale m p / fineLogBlockScale m q)
        (fineLogBlockCoordinate Λ F m p i)
        (fineLogBlockCoordinate Λ F m q j) *
        gramPhase (-(Λ j)) (Λ i)))
  rw [crossMehlerLeadingPhase_eq_gramPhase_neg]
  ring_nf

/-- After adjoint swap, a column-larger leading block factors through the
positive Fourier rectangle and the reciprocal normalized amplitude. -/
theorem fineLogLeadingBlockMatrix_conjTranspose_factorization
    (Λ : TwoSidedCarrier) (F : Finset ℤ)
    (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) :
    Matrix.conjTranspose (fineLogLeadingBlockMatrix Λ F m p q) =
      ((gramNormalization m * fineLogLeadingGeometricCoefficient m p q : ℝ) : ℂ) •
        amplitudeWeightedMatrix
          (fun j : FineLogBlockIndex Λ F m q =>
            fun i : FineLogBlockIndex Λ F m p =>
            normalizedCrossBlockAmplitude m
            (fineLogBlockScale m q / fineLogBlockScale m p)
            (fineLogBlockCoordinate Λ F m q j)
            (fineLogBlockCoordinate Λ F m p i))
          (finiteFourierRectangle
            (fineLogBlockPoint Λ F m q)
            (fineLogBlockPoint Λ F m p)) := by
  ext j i
  rw [Matrix.conjTranspose_apply, fineLogLeadingBlockMatrix,
    normalizedCrossSpatialLeadingTerm]
  rw [← fineLogBlockScale_mul_exp_coordinate Λ F m hm p i,
    ← fineLogBlockScale_mul_exp_coordinate Λ F m hm q j]
  rw [gramNormalizedCrossLeadingTerm_logBlock_factorization m hm
    (fineLogBlockScale_pos m p) (fineLogBlockScale_pos m q)]
  have hratio : 0 < fineLogBlockScale m p / fineLogBlockScale m q :=
    div_pos (fineLogBlockScale_pos m p) (fineLogBlockScale_pos m q)
  have hamp := normalizedCrossBlockAmplitude_inv_swap m hratio
    (fineLogBlockCoordinate Λ F m p i)
    (fineLogBlockCoordinate Λ F m q j)
  unfold fineLogLeadingGeometricCoefficient
  change
    star ((((gramNormalization m *
        (fineLogBlockScale m p * fineLogBlockScale m q) ^
          ((m : ℝ) - 1 / 4) /
        (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m) : ℝ) : ℂ) *
      normalizedCrossBlockAmplitude m
        (fineLogBlockScale m p / fineLogBlockScale m q)
        (fineLogBlockCoordinate Λ F m p i)
        (fineLogBlockCoordinate Λ F m q j)) *
      crossMehlerLeadingPhase (Λ i) (Λ j)) =
    ((gramNormalization m *
        ((fineLogBlockScale m p * fineLogBlockScale m q) ^
          ((m : ℝ) - 1 / 4) /
        (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m)) : ℝ) : ℂ) *
      (normalizedCrossBlockAmplitude m
        (fineLogBlockScale m q / fineLogBlockScale m p)
        (fineLogBlockCoordinate Λ F m q j)
        (fineLogBlockCoordinate Λ F m p i) *
        gramPhase (Λ i) (Λ j))
  rw [star_mul', star_mul', star_normalizedCrossBlockAmplitude]
  have hreal :
      gramNormalization m *
          (fineLogBlockScale m p * fineLogBlockScale m q) ^
            ((m : ℝ) - 1 / 4) /
          (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m) =
        gramNormalization m *
          ((fineLogBlockScale m p * fineLogBlockScale m q) ^
              ((m : ℝ) - 1 / 4) /
            (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m)) := by
    exact mul_div_assoc _ _ _
  have hscalar : star (((gramNormalization m *
      (fineLogBlockScale m p * fineLogBlockScale m q) ^
        ((m : ℝ) - 1 / 4) /
      (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m) : ℝ) : ℂ)) =
      ((gramNormalization m *
      ((fineLogBlockScale m p * fineLogBlockScale m q) ^
        ((m : ℝ) - 1 / 4) /
      (fineLogBlockScale m p + fineLogBlockScale m q) ^ (2 * m)) : ℝ) : ℂ) := by
    rw [hreal]
    simp
  have hphase : star (crossMehlerLeadingPhase (Λ i) (Λ j)) =
      gramPhase (Λ i) (Λ j) := by
    unfold crossMehlerLeadingPhase gramPhase
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hscalar, hphase, hamp]
  have hinv : (fineLogBlockScale m p / fineLogBlockScale m q)⁻¹ =
      fineLogBlockScale m q / fineLogBlockScale m p := by
    field_simp [fineLogBlockScale_pos m p |>.ne',
      fineLogBlockScale_pos m q |>.ne']
  rw [hinv]
  ring

theorem leadingGeometricCoefficient_mul_sqrt_eq_blockRatioEnvelope
    (m : ℕ) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    (M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m) * Real.sqrt M =
      blockRatioEnvelope m (M / N) := by
  have hMN : 0 < M * N := mul_pos hM hN
  have hsum : 0 < M + N := add_pos hM hN
  have hR : 0 < M / N := div_pos hM hN
  have hpowSum : 0 < (M + N) ^ (2 * m) := pow_pos hsum _
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hrpowMN : 0 < (M * N) ^ ((m : ℝ) - 1 / 4) :=
    Real.rpow_pos_of_pos hMN _
  have hrpowR : 0 < Real.rpow (M / N) (1 / 4) :=
    Real.rpow_pos_of_pos hR _
  have hlhs : 0 < (M * N) ^ ((m : ℝ) - 1 / 4) /
      (M + N) ^ (2 * m) * Real.sqrt M :=
    mul_pos (div_pos hrpowMN hpowSum) hsqrt
  have hrhs : 0 < blockRatioEnvelope m (M / N) := by
    exact div_pos (mul_pos (pow_pos hR _) hrpowR)
      (pow_pos (by linarith : 0 < 1 + M / N) _)
  apply Real.strictMonoOn_log.injOn hlhs hrhs
  rw [Real.log_mul (div_ne_zero hrpowMN.ne' hpowSum.ne') hsqrt.ne',
    Real.log_div hrpowMN.ne' hpowSum.ne', Real.log_rpow hMN,
    Real.log_pow, Real.log_sqrt hM.le]
  unfold blockRatioEnvelope
  rw [Real.log_div
      (mul_ne_zero (pow_ne_zero _ hR.ne') hrpowR.ne')
      (pow_ne_zero _ (by linarith : 1 + M / N ≠ 0)),
    Real.log_mul (pow_ne_zero _ hR.ne') hrpowR.ne', Real.log_pow]
  have hlogRpow := Real.log_rpow hR (1 / 4)
  change Real.log (Real.rpow (M / N) (1 / 4)) =
    (1 / 4) * Real.log (M / N) at hlogRpow
  rw [hlogRpow, Real.log_pow,
    Real.log_mul hM.ne' hN.ne', Real.log_div hM.ne' hN.ne']
  have hsumEq : M + N = N * (1 + M / N) := by
    field_simp [hN.ne']
    ring
  rw [hsumEq, Real.log_mul hN.ne' (by positivity : 1 + M / N ≠ 0)]
  push_cast
  ring

theorem fineLogLeadingGeometricCoefficient_mul_sqrt_eq
    (m : ℕ) (p q : ℕ) :
    fineLogLeadingGeometricCoefficient m p q *
        Real.sqrt (fineLogBlockScale m p) =
      blockRatioEnvelope m
        (fineLogBlockScale m p / fineLogBlockScale m q) := by
  exact leadingGeometricCoefficient_mul_sqrt_eq_blockRatioEnvelope m
    (fineLogBlockScale_pos m p) (fineLogBlockScale_pos m q)

/-- Square-root extraction in the exact form used to combine the amplitude
multiplier bound with a Fourier-rectangle squared norm bound. -/
theorem leadingBlockNorm_le_sqrtGeometry_mul_envelope
    (m : ℕ) (hm : 1 ≤ m) {M N C K z : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hC : 0 ≤ C) (hK : 0 < K)
    (hz : 0 ≤ z)
    (hsq : z ^ 2 ≤
      ‖(((gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
        C ^ 2 * (K * M)) :
    z ≤ C * Real.sqrt K * gramNormalization m *
      blockRatioEnvelope m (M / N) := by
  have hg : 0 < gramNormalization m := gramNormalization_pos hm
  have hMN : 0 < M * N := mul_pos hM hN
  have hsum : 0 < M + N := add_pos hM hN
  have hgeo : 0 <
      (M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m) :=
    div_pos (Real.rpow_pos_of_pos hMN _) (pow_pos hsum _)
  have hright : 0 ≤ C * Real.sqrt K * gramNormalization m *
      blockRatioEnvelope m (M / N) := by
    have henv : 0 < blockRatioEnvelope m (M / N) := by
      unfold blockRatioEnvelope
      exact div_pos
        (mul_pos (pow_pos (div_pos hM hN) _)
          (Real.rpow_pos_of_pos (div_pos hM hN) _))
        (pow_pos (by positivity : 0 < 1 + M / N) _)
    positivity
  rw [← sq_le_sq₀ hz hright]
  calc
    z ^ 2 ≤
        ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) /
              (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
          C ^ 2 * (K * M) := hsq
    _ = (C * Real.sqrt K * gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) /
            (M + N) ^ (2 * m) * Real.sqrt M)) ^ 2 := by
      rw [Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg hg.le hgeo.le)]
      have hsqrtK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
      have hsqrtM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM.le
      rw [show
        (C * Real.sqrt K * gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) /
            (M + N) ^ (2 * m) * Real.sqrt M)) ^ 2 =
          C ^ 2 * Real.sqrt K ^ 2 * gramNormalization m ^ 2 *
            ((M * N) ^ ((m : ℝ) - 1 / 4) /
              (M + N) ^ (2 * m)) ^ 2 * Real.sqrt M ^ 2 by ring,
        hsqrtK, hsqrtM]
      ring
    _ = (C * Real.sqrt K * gramNormalization m *
          blockRatioEnvelope m (M / N)) ^ 2 := by
      rw [leadingGeometricCoefficient_mul_sqrt_eq_blockRatioEnvelope m hM hN]

/-- Uniform leading-block estimate when the row block has the larger
squared-magnitude scale. -/
theorem exists_uniform_fineLogLeadingBlock_norm_le_of_le
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ C : NNReal, ∀ (m : ℕ), 1 ≤ m → ∀ p q : ℕ, q ≤ p →
      ‖fineLogLeadingBlockMatrix Λ F m p q‖ ≤
        (C : ℝ) * gramNormalization m * fineLogBlockEnvelope m (p - q) := by
  obtain ⟨Camp, hamp⟩ :=
    exists_uniform_normalizedCrossBlockAmplitude_l2MultiplierBound
  let K : NNReal :=
    ⟨fineLogRectangleSqConstant, fineLogRectangleSqConstant_pos.le⟩
  refine ⟨Camp * NNReal.sqrt K, ?_⟩
  intro m hm p q hqp
  let M := fineLogBlockScale m p
  let N := fineLogBlockScale m q
  let A := finiteNegativeFourierRectangle
    (fineLogBlockPoint Λ F m p) (fineLogBlockPoint Λ F m q)
  let W := amplitudeWeightedMatrix
    (fun i : FineLogBlockIndex Λ F m p =>
      fun j : FineLogBlockIndex Λ F m q =>
      normalizedCrossBlockAmplitude m (M / N)
        (fineLogBlockCoordinate Λ F m p i)
        (fineLogBlockCoordinate Λ F m q j)) A
  have hM : 0 < M := fineLogBlockScale_pos m p
  have hN : 0 < N := fineLogBlockScale_pos m q
  have hMN : 0 < M * N := mul_pos hM hN
  have hsum : 0 < M + N := add_pos hM hN
  have hgeo : 0 <
      (M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m) :=
    div_pos (Real.rpow_pos_of_pos hMN _) (pow_pos hsum _)
  have hratio : 1 ≤ M / N := by
    apply (one_le_div₀ hN).2
    exact fineLogBlockScale_mono m hm hqp
  have hW : ‖W‖ ≤ (Camp : ℝ) * ‖A‖ := by
    exact hamp m hm hratio
      (fineLogBlockCoordinate Λ F m p)
      (fineLogBlockCoordinate Λ F m q)
      (fineLogBlockCoordinate_mem_Icc Λ F m hm p)
      (fineLogBlockCoordinate_mem_Icc Λ F m hm q) A
  have hA : ‖A‖ ^ 2 ≤ (K : ℝ) * M := by
    change ‖finiteNegativeFourierRectangle
        (fineLogBlockPoint Λ F m p)
        (fineLogBlockPoint Λ F m q)‖ ^ 2 ≤
      fineLogRectangleSqConstant * fineLogBlockScale m p
    simpa only using
      fineLogBlock_negativeRectangle_sq_le hsep m hm hqp
  have hWsquare : ‖W‖ ^ 2 ≤ ((Camp : ℝ) * ‖A‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg W)
      (mul_nonneg Camp.coe_nonneg (norm_nonneg A))).2 hW
  have hsq : ‖fineLogLeadingBlockMatrix Λ F m p q‖ ^ 2 ≤
      ‖(((gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
        (Camp : ℝ) ^ 2 * ((K : ℝ) * M) := by
    rw [fineLogLeadingBlockMatrix_factorization Λ F m hm p q]
    change ‖((((gramNormalization m *
        ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ)) • W)‖ ^ 2 ≤ _
    rw [norm_smul]
    calc
      (‖(((gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ *
          ‖W‖) ^ 2 =
          ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            ‖W‖ ^ 2 := by ring
      _ ≤ ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (((Camp : ℝ) * ‖A‖) ^ 2) := by
        gcongr
      _ = ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (Camp : ℝ) ^ 2 * ‖A‖ ^ 2 := by ring
      _ ≤ ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (Camp : ℝ) ^ 2 * ((K : ℝ) * M) := by
        gcongr
  have hbound := leadingBlockNorm_le_sqrtGeometry_mul_envelope m hm
    hM hN Camp.coe_nonneg (show 0 < (K : ℝ) from
      fineLogRectangleSqConstant_pos)
    (norm_nonneg (fineLogLeadingBlockMatrix Λ F m p q)) hsq
  rw [fineLogBlockScale_div_eq_fineLogBlockRatio m hm hqp,
    ← fineLogBlockEnvelope] at hbound
  rw [NNReal.coe_mul, Real.coe_sqrt]
  exact hbound

/-- Uniform leading-block estimate in the opposite orientation.  The adjoint
factorization is essential here: it turns the reciprocal normalized amplitude
into a large-ratio symbol and the kernel into the positive Fourier rectangle. -/
theorem exists_uniform_fineLogLeadingBlock_norm_le_of_ge
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ C : NNReal, ∀ (m : ℕ), 1 ≤ m → ∀ p q : ℕ, p ≤ q →
      ‖fineLogLeadingBlockMatrix Λ F m p q‖ ≤
        (C : ℝ) * gramNormalization m * fineLogBlockEnvelope m (q - p) := by
  obtain ⟨Camp, hamp⟩ :=
    exists_uniform_normalizedCrossBlockAmplitude_l2MultiplierBound
  let K : NNReal :=
    ⟨fineLogRectangleSqConstant, fineLogRectangleSqConstant_pos.le⟩
  refine ⟨Camp * NNReal.sqrt K, ?_⟩
  intro m hm p q hpq
  let M := fineLogBlockScale m q
  let N := fineLogBlockScale m p
  let A := finiteFourierRectangle
    (fineLogBlockPoint Λ F m q) (fineLogBlockPoint Λ F m p)
  let W := amplitudeWeightedMatrix
    (fun j : FineLogBlockIndex Λ F m q =>
      fun i : FineLogBlockIndex Λ F m p =>
      normalizedCrossBlockAmplitude m (M / N)
        (fineLogBlockCoordinate Λ F m q j)
        (fineLogBlockCoordinate Λ F m p i)) A
  have hM : 0 < M := fineLogBlockScale_pos m q
  have hN : 0 < N := fineLogBlockScale_pos m p
  have hMN : 0 < M * N := mul_pos hM hN
  have hsum : 0 < M + N := add_pos hM hN
  have hratio : 1 ≤ M / N := by
    apply (one_le_div₀ hN).2
    exact fineLogBlockScale_mono m hm hpq
  have hW : ‖W‖ ≤ (Camp : ℝ) * ‖A‖ := by
    exact hamp m hm hratio
      (fineLogBlockCoordinate Λ F m q)
      (fineLogBlockCoordinate Λ F m p)
      (fineLogBlockCoordinate_mem_Icc Λ F m hm q)
      (fineLogBlockCoordinate_mem_Icc Λ F m hm p) A
  have hA : ‖A‖ ^ 2 ≤ (K : ℝ) * M := by
    change ‖finiteFourierRectangle
        (fineLogBlockPoint Λ F m q)
        (fineLogBlockPoint Λ F m p)‖ ^ 2 ≤
      fineLogRectangleSqConstant * fineLogBlockScale m q
    simpa only using
      fineLogBlock_positiveRectangle_sq_le hsep m hm hpq
  have hWsquare : ‖W‖ ^ 2 ≤ ((Camp : ℝ) * ‖A‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg W)
      (mul_nonneg Camp.coe_nonneg (norm_nonneg A))).2 hW
  have hsq : ‖fineLogLeadingBlockMatrix Λ F m p q‖ ^ 2 ≤
      ‖(((gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
        (Camp : ℝ) ^ 2 * ((K : ℝ) * M) := by
    rw [← Matrix.l2_opNorm_conjTranspose,
      fineLogLeadingBlockMatrix_conjTranspose_factorization Λ F m hm p q,
      fineLogLeadingGeometricCoefficient_comm m p q]
    change ‖((((gramNormalization m *
        ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ)) • W)‖ ^ 2 ≤ _
    rw [norm_smul]
    calc
      (‖(((gramNormalization m *
          ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ *
          ‖W‖) ^ 2 =
          ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            ‖W‖ ^ 2 := by ring
      _ ≤ ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (((Camp : ℝ) * ‖A‖) ^ 2) := by
        gcongr
      _ = ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (Camp : ℝ) ^ 2 * ‖A‖ ^ 2 := by ring
      _ ≤ ‖(((gramNormalization m *
            ((M * N) ^ ((m : ℝ) - 1 / 4) / (M + N) ^ (2 * m)) : ℝ) : ℂ))‖ ^ 2 *
            (Camp : ℝ) ^ 2 * ((K : ℝ) * M) := by
        gcongr
  have hbound := leadingBlockNorm_le_sqrtGeometry_mul_envelope m hm
    hM hN Camp.coe_nonneg (show 0 < (K : ℝ) from
      fineLogRectangleSqConstant_pos)
    (norm_nonneg (fineLogLeadingBlockMatrix Λ F m p q)) hsq
  rw [fineLogBlockScale_div_eq_fineLogBlockRatio m hm hpq,
    ← fineLogBlockEnvelope] at hbound
  rw [NNReal.coe_mul, Real.coe_sqrt]
  exact hbound

/-- Uniform physical leading-block estimate in every block orientation. -/
theorem exists_uniform_fineLogLeadingBlock_norm_le
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ C : NNReal, ∀ (m : ℕ), 1 ≤ m → ∀ p q : ℕ,
      ‖fineLogLeadingBlockMatrix Λ F m p q‖ ≤
        (C : ℝ) * gramNormalization m *
          fineLogBlockEnvelope m (Nat.dist p q) := by
  obtain ⟨Cneg, hneg⟩ :=
    exists_uniform_fineLogLeadingBlock_norm_le_of_le hsep
  obtain ⟨Cpos, hpos⟩ :=
    exists_uniform_fineLogLeadingBlock_norm_le_of_ge hsep
  refine ⟨Cneg + Cpos, ?_⟩
  intro m hm p q
  rcases le_total q p with hqp | hpq
  · rw [Nat.dist_eq_sub_of_le_right hqp]
    exact (hneg m hm p q hqp).trans (by
      have hg : 0 ≤ gramNormalization m := (gramNormalization_pos hm).le
      have he := fineLogBlockEnvelope_nonneg m (p - q)
      push_cast
      nlinarith [Cneg.coe_nonneg, Cpos.coe_nonneg,
        mul_nonneg hg he])
  · rw [Nat.dist_eq_sub_of_le hpq]
    exact (hpos m hm p q hpq).trans (by
      have hg : 0 ≤ gramNormalization m := (gramNormalization_pos hm).le
      have he := fineLogBlockEnvelope_nonneg m (q - p)
      push_cast
      nlinarith [Cneg.coe_nonneg, Cpos.coe_nonneg,
        mul_nonneg hg he])

/-- Strict subcriticality alone supplies the exceptional set, noncentral
tail geometry, unit signed-square separation, and a uniform estimate for the
actual physical leading blocks. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_fineLogLeadingBlock_bound
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ (F : Finset ℤ) (CΛ : NNReal),
      (∀ j, j ∉ F → 1 < (Λ j) ^ 2) ∧
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ p q : ℕ,
        ‖fineLogLeadingBlockMatrix Λ F m p q‖ ≤
          (CΛ : ℝ) * gramNormalization m *
            fineLogBlockEnvelope m (Nat.dist p q) := by
  obtain ⟨F, hsep, houtside⟩ := hΛ.exists_unitSeparated_noncentral_tail
  obtain ⟨CΛ, hblock⟩ :=
    exists_uniform_fineLogLeadingBlock_norm_le hsep
  exact ⟨F, CΛ, houtside, hsep, hblock⟩

end

end MeyerGeneralProblem
