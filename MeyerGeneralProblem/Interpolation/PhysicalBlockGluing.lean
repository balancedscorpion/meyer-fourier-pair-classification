module

public import MeyerGeneralProblem.Interpolation.RayBlockEnergy

@[expose] public section

/-!
# Arbitrary-start physical central and exterior gluing

The carrier's actual tail threshold determines the central transition.
The two signed exterior families are not reflected into each other. Their
smooth ray selectors and the actual tail partition preserve point values.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- Exterior local data before the actual tail start are identically zero. -/
def tailBlockFunctions (start : ℕ) (h : ℕ → ℝ → ℂ) (b : ℕ) : ℝ → ℂ :=
  if start ≤ b then h b else fun _ => 0

/-- The actual one-ray tail beginning at an arbitrary source threshold. -/
def physicalRayBlockTail (B : ℝ) (start : ℕ) (ε : ℝ) (h : ℕ → ℝ → ℂ) : ℝ → ℂ :=
  exteriorRayBlockSum B ε (tailBlockFunctions start h)

/-- Truncating the index set preserves genuine smoothness of each local function. -/
theorem contDiff_tailBlockFunctions (start b : ℕ) (h : ℕ → ℝ → ℂ)
    {n : ℕ∞} (hh : ContDiff ℝ n (h b)) : ContDiff ℝ n (tailBlockFunctions start h b) := by
  unfold tailBlockFunctions
  split_ifs
  · exact hh
  · exact contDiff_const

/-- The arbitrary-start physical ray tail is smooth by local finiteness. -/
theorem contDiff_physicalRayBlockTail {B : ℝ} (hB : 0 < B) (start : ℕ) (ε : ℝ)
    (h : ℕ → ℝ → ℂ) {n : ℕ∞} (hh : ∀ b, ContDiff ℝ n (h b)) :
    ContDiff ℝ n (physicalRayBlockTail B start ε h) :=
  contDiff_exteriorRayBlockSum hB ε _ (fun b => contDiff_tailBlockFunctions start b h (hh b))

/-- Filtering all natural indices by the actual tail threshold has the
same proved partition sum as the shifted enumeration. -/
theorem hasSum_blockCutoff_atLeast (B s : ℝ) (start : ℕ) :
    HasSum (fun b : ℕ => if start ≤ b then blockCutoff B b s else 0)
      (blockTransition B start s) := by
  let g : ℕ → ℝ := fun b => if start ≤ b then blockCutoff B b s else 0
  have hf : Summable (fun b => blockCutoff B b s) := by
    simpa only [Nat.zero_add] using (hasSum_blockCutoff B 0 s).summable
  have hg : Summable g := hf.of_nonneg_of_le
    (fun b => by dsimp only [g]; split_ifs; exact (blockCutoff_mem_Icc B b s).1; exact le_rfl)
    (fun b => by dsimp only [g]; split_ifs; exact le_rfl; exact (blockCutoff_mem_Icc B b s).1)
  have hzero : ∑ b ∈ Finset.range start, g b = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    simp [g, Nat.not_le.mpr (Finset.mem_range.mp hb)]
  have htail : (fun n : ℕ => g (n+start)) = fun n => blockCutoff B (start+n) s := by
    funext n
    simp [g, Nat.add_comm]
  have heq : ∑' b : ℕ, g b = blockTransition B start s := by
    rw [← hg.sum_add_tsum_nat_add start, hzero, zero_add, htail,
      (hasSum_blockCutoff B start s).tsum_eq]
  exact heq ▸ hg.hasSum

/-- Arbitrary-start ray gluing preserves active local values with the
correct source-dependent central transition, not a fixed third block. -/
theorem physicalRayBlockTail_eq_of_active_values (B : ℝ) (start : ℕ)
    (hstart : 3 ≤ start) (ε : ℝ) (h : ℕ → ℝ → ℂ) (x : ℝ) (v : ℂ)
    (hactive : ∀ b, start ≤ b → blockCutoff B b (x^2) ≠ 0 → h b (x^2) = v) :
    physicalRayBlockTail B start ε h x =
      unitBlockTransition (ε*x) • (blockTransition B start (x^2) • v) := by
  have heq (b : ℕ) :
      quadraticBlockPiece B b (exteriorRayBlockFactor b ε (tailBlockFunctions start h b)) x =
      (if start ≤ b then blockCutoff B b (x^2) else 0) • (unitBlockTransition (ε*x) • v) := by
    by_cases hb : start ≤ b
    · have hb3 : 3 ≤ b := hstart.trans hb
      by_cases hz : blockCutoff B b (x^2)=0
      · simp [quadraticBlockPiece, exteriorRayBlockFactor, tailBlockFunctions, hb, hb3, hz]
      · simp [quadraticBlockPiece, exteriorRayBlockFactor, tailBlockFunctions, hb, hb3,
          hactive b hb hz]
    · simp [quadraticBlockPiece, exteriorRayBlockFactor, tailBlockFunctions, hb]
  simp only [physicalRayBlockTail, exteriorRayBlockSum, heq,
    ((hasSum_blockCutoff_atLeast B (x^2) start).smul_const (unitBlockTransition (ε*x) • v)).tsum_eq]
  simp only [smul_smul, mul_comm]

/-- The wrong ray of an actual exterior sum is identically zero. -/
theorem exteriorRayBlockSum_eq_zero_of_nonpos {B : ℝ} (hB : 1 ≤ B)
    {ε : ℝ} (hε : ε^2=1) (h : ℕ → ℝ → ℂ) {x : ℝ} (hx : ε*x ≤ 0) :
    exteriorRayBlockSum B ε h x = 0 := by
  unfold exteriorRayBlockSum
  have hz (b : ℕ) : quadraticBlockPiece B b (exteriorRayBlockFactor b ε (h b)) x = 0 := by
    rw [quadraticBlockPiece_exteriorRayBlockFactor]
    split_ifs with hb
    · have ht := iteratedDeriv_rayQuadraticBlockPiece hB (by omega : 2 ≤ b) hε (h b) 0 x
      simpa only [iteratedDeriv_zero, not_lt.mpr hx, ite_false] using ht
    · rfl
  simp only [hz, tsum_zero]

/-- The wrong ray remains zero for every actual tail threshold. -/
theorem physicalRayBlockTail_eq_zero_of_nonpos {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) {ε : ℝ} (hε : ε^2=1) (h : ℕ → ℝ → ℂ)
    {x : ℝ} (hx : ε*x ≤ 0) : physicalRayBlockTail B start ε h x = 0 :=
  exteriorRayBlockSum_eq_zero_of_nonpos hB hε _ hx

/-- The exterior transition vanishes throughout the physical unit interval,
uniformly over all source tail thresholds at least three. -/
theorem blockTransition_square_eq_zero_near_origin {B : ℝ} (hB : 1 ≤ B)
    {start : ℕ} (hstart : 3 ≤ start) {x : ℝ} (hx : |x| ≤ 1) :
    blockTransition B start (x^2) = 0 := by
  have hs : (3 : ℝ) ≤ start := by exact_mod_cast hstart
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hdiv : x^2/B ≤ 1 := (div_le_one (by linarith : 0 < B)).mpr (hx2.trans hB)
  apply unitBlockTransition_zero
  linarith

/-- On its positive ray the smooth selector acts as the identity on the
actual exterior transition, including the neighborhood of the origin. -/
theorem unitBlockTransition_mul_squareTransition {B : ℝ} (hB : 1 ≤ B)
    {start : ℕ} (hstart : 3 ≤ start) {ε : ℝ} (hε : ε^2=1)
    {x : ℝ} (hx : 0 < ε*x) :
    unitBlockTransition (ε*x)*blockTransition B start (x^2) = blockTransition B start (x^2) := by
  by_cases hsmall : |x| ≤ 1
  · simp [blockTransition_square_eq_zero_near_origin hB hstart hsmall]
  · have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
    have habs : |ε*x|=|x| := by rw [abs_mul, heps, one_mul]
    rw [abs_of_pos hx] at habs
    rw [unitBlockTransition_one (by linarith [lt_of_not_ge hsmall]), one_mul]

/-- The central physical piece and the two independent signed tail families. -/
def physicalBlockGluing (B : ℝ) (start : ℕ) (central : ℝ → ℂ)
    (positive negative : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  (1-blockTransition B start (x^2)) • central x +
    physicalRayBlockTail B start 1 positive x + physicalRayBlockTail B start (-1) negative x

/-- The actual physical gluing is smooth across the origin and the central
boundary for every source tail start. -/
theorem contDiff_physicalBlockGluing {B : ℝ} (hB : 0 < B) (start : ℕ)
    (central : ℝ → ℂ) (positive negative : ℕ → ℝ → ℂ) {n : ℕ∞}
    (hc : ContDiff ℝ n central) (hp : ∀ b, ContDiff ℝ n (positive b))
    (hn : ∀ b, ContDiff ℝ n (negative b)) :
    ContDiff ℝ n (physicalBlockGluing B start central positive negative) :=
  (((contDiff_const.sub ((contDiff_blockTransition B start).comp (by fun_prop))).smul hc).add
    (contDiff_physicalRayBlockTail hB start 1 positive hp)).add
    (contDiff_physicalRayBlockTail hB start (-1) negative hn)

/-- Actual point interpolation after central/two-ray composition. Local
values are required only on their active ray and actual cutoff supports. -/
theorem physicalBlockGluing_eq_of_active_values {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) (central : ℝ → ℂ)
    (positive negative : ℕ → ℝ → ℂ) (x : ℝ) (v : ℂ)
    (hc : 1-blockTransition B start (x^2) ≠ 0 → central x = v)
    (hp : 0 < x → ∀ b, start ≤ b → blockCutoff B b (x^2) ≠ 0 → positive b (x^2)=v)
    (hn : x < 0 → ∀ b, start ≤ b → blockCutoff B b (x^2) ≠ 0 → negative b (x^2)=v) :
    physicalBlockGluing B start central positive negative x = v := by
  have hc' : (1-blockTransition B start (x^2)) • central x =
      (1-blockTransition B start (x^2)) • v := by
    by_cases hz : 1-blockTransition B start (x^2)=0
    · simp [hz]
    · rw [hc hz]
  unfold physicalBlockGluing
  rw [hc']
  rcases lt_trichotomy 0 x with hx | hx | hx
  · rw [physicalRayBlockTail_eq_of_active_values B start hstart 1 positive x v (hp hx),
      physicalRayBlockTail_eq_zero_of_nonpos hB start (by norm_num : (-1:ℝ)^2=1) negative
        (by linarith : (-1:ℝ)*x ≤ 0), add_zero, smul_smul,
      unitBlockTransition_mul_squareTransition hB hstart (by norm_num : (1:ℝ)^2=1)
        (by simpa using hx), ← add_smul]
    simp
  · subst x
    rw [physicalRayBlockTail_eq_zero_of_nonpos hB start (by norm_num : (1:ℝ)^2=1) positive (by norm_num),
      physicalRayBlockTail_eq_zero_of_nonpos hB start (by norm_num : (-1:ℝ)^2=1) negative (by norm_num),
      blockTransition_square_eq_zero_near_origin hB hstart (by norm_num : |(0:ℝ)| ≤ 1)]
    simp
  · rw [physicalRayBlockTail_eq_zero_of_nonpos hB start (by norm_num : (1:ℝ)^2=1) positive
        (by linarith : (1:ℝ)*x ≤ 0), add_zero,
      physicalRayBlockTail_eq_of_active_values B start hstart (-1) negative x v (hn hx),
      smul_smul, unitBlockTransition_mul_squareTransition hB hstart
        (by norm_num : (-1:ℝ)^2=1) (by linarith : 0 < (-1:ℝ)*x), ← add_smul]
    simp

end

end MeyerGeneralProblem
