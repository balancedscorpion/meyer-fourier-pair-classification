module

public import MeyerGeneralProblem.Interpolation.BlockOverlap
public import MeyerGeneralProblem.Carrier.CanonicalClusterGeometry
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Actual triple-block incidence bounds

A group of diameter at most the block length can meet at most five triple
windows. The bound applies to the actual nodes and any anchor in that group.
It controls infinite nonnegative energy sums without assuming summability.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

/-- The three consecutive half-open blocks used for exterior interpolation. -/
def tripleBlockWindow (B : ℝ) (b : ℕ) : Set ℝ :=
  Ico (((b : ℝ) - 1) * B) (((b : ℝ) + 2) * B)

/-- Five possible triple-window indices around the actual anchor. -/
def tripleBlockIndices (B a : ℝ) : Finset ℕ :=
  Finset.Icc (⌊a / B⌋₊ - 2) (⌊a / B⌋₊ + 2)

/-- Natural-index truncation can only decrease the five-index bound. -/
theorem card_tripleBlockIndices_le (B a : ℝ) :
    (tripleBlockIndices B a).card ≤ 5 := by
  simp only [tripleBlockIndices, Nat.card_Icc]
  omega

/-- A genuine node within one block length of the anchor places every
touching triple window inside the explicit five-index set. -/
theorem mem_tripleBlockIndices_of_near_node {B a s : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (hnear : |s - a| ≤ B) {b : ℕ}
    (hs : s ∈ tripleBlockWindow B b) : b ∈ tripleBlockIndices B a := by
  have hfloor := Nat.floor_le (div_nonneg ha hB.le)
  have hceil := Nat.lt_floor_add_one (a / B)
  have hlo : (b : ℝ) - 2 ≤ a / B := (le_div_iff₀ hB).mpr (by
    rcases abs_le.mp hnear with ⟨h₁, h₂⟩
    have := hs.1
    nlinarith)
  have hhi : a / B < (b : ℝ) + 3 := (div_lt_iff₀ hB).mpr (by
    rcases abs_le.mp hnear with ⟨h₁, h₂⟩
    have := hs.2
    nlinarith)
  have h₁ : b ≤ ⌊a / B⌋₊ + 2 := by
    have : (b : ℝ) < (⌊a / B⌋₊ : ℝ) + 3 := by linarith
    have : b < ⌊a / B⌋₊ + 3 := by exact_mod_cast this
    omega
  have h₂ : ⌊a / B⌋₊ ≤ b + 2 := by
    have : (⌊a / B⌋₊ : ℝ) < (b : ℝ) + 3 := lt_of_le_of_lt hfloor hhi
    have : ⌊a / B⌋₊ < b + 3 := by exact_mod_cast this
    omega
  simp only [tripleBlockIndices, Finset.mem_Icc]
  omega

/-- Actual contact of a group with a triple window. No convex-hull or
chosen representative is substituted for a node. -/
def groupTouchesTripleBlock (B : ℝ) (nodes : Set ℝ) (b : ℕ) : Prop :=
  (nodes ∩ tripleBlockWindow B b).Nonempty

/-- The actual set of triple windows touched by a bounded-diameter group
is finite and has cardinality at most five. -/
theorem finite_ncard_groupTouchesTripleBlock {B a : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (nodes : Set ℝ) (hnear : ∀ s ∈ nodes, |s-a| ≤ B) :
    {b : ℕ | groupTouchesTripleBlock B nodes b}.Finite ∧
      {b : ℕ | groupTouchesTripleBlock B nodes b}.ncard ≤ 5 := by
  have hsub : {b : ℕ | groupTouchesTripleBlock B nodes b} ⊆
      (tripleBlockIndices B a : Set ℕ) := by
    rintro b ⟨s, hs, hb⟩
    exact mem_tripleBlockIndices_of_near_node hB ha (hnear s hs) hb
  have hfinite := (tripleBlockIndices B a).finite_toSet.subset hsub
  refine ⟨hfinite, (Set.ncard_le_ncard hsub (tripleBlockIndices B a).finite_toSet).trans ?_⟩
  simpa using card_tripleBlockIndices_le B a

/-- Every actual canonical cluster satisfies the five-window incidence
bound when its proved diameter q*d is at most the block length. -/
theorem BoundedClusterOrder.canonical_groupTouchesTripleBlock_bound
    {S : LocallyFiniteCarrier} {d B : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hB : 0 < B)
    (hsize : (q : ℝ)*d ≤ B) (C : CanonicalClusterIndex S d)
    (i : Fin (horder.clusterSize C)) (ha : 0 ≤ horder.realClusterNode C i) :
    {b : ℕ | groupTouchesTripleBlock B (Set.range (horder.realClusterNode C)) b}.Finite ∧
      {b : ℕ | groupTouchesTripleBlock B (Set.range (horder.realClusterNode C)) b}.ncard ≤ 5 := by
  apply finite_ncard_groupTouchesTripleBlock hB ha
  rintro s ⟨j, rfl⟩
  simpa only [Real.dist_eq] using (horder.realClusterNode_diameter hd C j i).trans hsize

/-- Exterior touching groups have anchors comparable to the block scale.
The harmless finite initial blocks are explicitly excluded. -/
theorem tripleBlock_scale_le_anchor {B a s : ℝ} (hB : 0 < B)
    (hnear : |s-a| ≤ B) {b : ℕ} (hb : 3 ≤ b)
    (hs : s ∈ tripleBlockWindow B b) : (b : ℝ)*B ≤ 3*a := by
  have hb' : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hnode := hs.1
  change ((b : ℝ)-1)*B ≤ s at hnode
  have hdiff := (abs_le.mp hnear).2
  nlinarith

/-- The actual nonnegative energy repeated over touching windows costs
only five, even when the value is infinite. -/
theorem tsum_groupTouchesTripleBlock_le {B a : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (nodes : Set ℝ) (hnear : ∀ s ∈ nodes, |s-a| ≤ B)
    (E : ℝ≥0∞) :
    (∑' b : ℕ, if groupTouchesTripleBlock B nodes b then E else 0) ≤ 5*E := by
  classical
  have hz (b : ℕ) (hb : b ∉ tripleBlockIndices B a) :
      (if groupTouchesTripleBlock B nodes b then E else 0) = 0 := by
    split_ifs with h
    · obtain ⟨s, hs, hwin⟩ := h
      exact False.elim (hb (mem_tripleBlockIndices_of_near_node hB ha (hnear s hs) hwin))
    · rfl
  rw [tsum_eq_sum hz]
  calc
    _ ≤ ∑ _b ∈ tripleBlockIndices B a, E := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs <;> simp
    _ = ((tripleBlockIndices B a).card : ℝ≥0∞)*E := by simp [nsmul_eq_mul]
    _ ≤ 5*E := mul_le_mul' (by exact_mod_cast card_tripleBlockIndices_le B a) le_rfl

/-- Summing actual local group energies over all windows preserves the
global energy bound with only the fixed incidence factor five. -/
theorem tsum_tripleBlock_groupEnergy_le {ι : Type*} (B : ℝ) (hB : 0 < B)
    (anchor : ι → ℝ) (ha : ∀ i, 0 ≤ anchor i) (nodes : ι → Set ℝ)
    (hnear : ∀ i s, s ∈ nodes i → |s-anchor i| ≤ B) (E : ι → ℝ≥0∞) :
    (∑' b : ℕ, ∑' i : ι, if groupTouchesTripleBlock B (nodes i) b then E i else 0) ≤
      5 * ∑' i : ι, E i := by
  classical
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun i => tsum_groupTouchesTripleBlock_le hB (ha i)
    (nodes i) (hnear i) (E i))

/-- The square-coordinate block energy has exactly the physical anchor
weight of order `2k-1`; no extra power of the anchor is lost. -/
theorem tripleBlock_rpow_le_physical_anchor_weight {B a s : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (hnear : |s-a| ≤ B) {b k : ℕ} (hb : 3 ≤ b) (hk : 1 ≤ k)
    (hs : s ∈ tripleBlockWindow B b) :
    ((b : ℝ)*B)^((k : ℝ)-1/2) ≤
      (3 : ℝ)^((k : ℝ)-1/2) * (1+Real.sqrt a)^(2*k-1) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 ≤ (k : ℝ)-1/2 := by linarith
  have hexp : (2 : ℝ)*((k : ℝ)-1/2) = ((2*k-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hweight : a^((k : ℝ)-1/2) ≤ (1+Real.sqrt a)^(2*k-1) := by
    calc
      _ = ((Real.sqrt a)^2)^((k : ℝ)-1/2) := by rw [Real.sq_sqrt ha]
      _ = (Real.sqrt a)^((2 : ℝ)*((k : ℝ)-1/2)) := by
        rw [Real.rpow_mul (Real.sqrt_nonneg a), Real.rpow_two]
      _ = (Real.sqrt a)^(2*k-1) := by rw [hexp, Real.rpow_natCast]
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg a) (by linarith) (2*k-1)
  calc
    _ ≤ (3*a)^((k : ℝ)-1/2) :=
      Real.rpow_le_rpow (by positivity) (tripleBlock_scale_le_anchor hB hnear hb hs) hp
    _ = (3 : ℝ)^((k : ℝ)-1/2)*a^((k : ℝ)-1/2) := Real.mul_rpow (by norm_num) ha
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg (by norm_num) _)

/-- The actual exterior-window energy reindexes into the canonical
physical anchor weight with a fixed five-window factor. Infinite data
energies remain visible; no summability hypothesis is smuggled in. -/
theorem tsum_tripleBlock_weighted_groupEnergy_le {ι : Type*} (B : ℝ) (hB : 0 < B)
    (anchor : ι → ℝ) (ha : ∀ i, 0 ≤ anchor i) (nodes : ι → Set ℝ)
    (hnear : ∀ i s, s ∈ nodes i → |s-anchor i| ≤ B)
    (k : ℕ) (hk : 1 ≤ k) (E : ι → ℝ≥0∞) :
    (∑' b : ℕ, ∑' i : ι,
      if 3 ≤ b ∧ groupTouchesTripleBlock B (nodes i) b
      then ENNReal.ofReal (((b : ℝ)*B)^((k : ℝ)-1/2)) * E i else 0) ≤
      5 * ENNReal.ofReal ((3 : ℝ)^((k : ℝ)-1/2)) *
        ∑' i : ι, ENNReal.ofReal ((1+Real.sqrt (anchor i))^(2*k-1)) * E i := by
  let W : ι → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ((3 : ℝ)^((k : ℝ)-1/2)) *
      (ENNReal.ofReal ((1+Real.sqrt (anchor i))^(2*k-1)) * E i)
  have hpoint (b : ℕ) (i : ι) :
      (if 3 ≤ b ∧ groupTouchesTripleBlock B (nodes i) b
       then ENNReal.ofReal (((b : ℝ)*B)^((k : ℝ)-1/2)) * E i else 0) ≤
      if groupTouchesTripleBlock B (nodes i) b then W i else 0 := by
    split_ifs with h htouch
    · obtain ⟨s, hs, hwin⟩ := h.2
      have hw := ENNReal.ofReal_le_ofReal
        (tripleBlock_rpow_le_physical_anchor_weight hB (ha i) (hnear i s hs) h.1 hk hwin)
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)] at hw
      exact (mul_le_mul' hw le_rfl).trans_eq (mul_assoc _ _ _)
    · exact False.elim (htouch h.2)
    · exact bot_le
    · exact le_rfl
  calc
    _ ≤ ∑' b : ℕ, ∑' i : ι, if groupTouchesTripleBlock B (nodes i) b then W i else 0 :=
      ENNReal.tsum_le_tsum (fun b => ENNReal.tsum_le_tsum (hpoint b))
    _ ≤ 5 * ∑' i : ι, W i := tsum_tripleBlock_groupEnergy_le B hB anchor ha nodes hnear W
    _ = _ := by simp only [W, ENNReal.tsum_mul_left, mul_assoc]

end

end MeyerGeneralProblem
