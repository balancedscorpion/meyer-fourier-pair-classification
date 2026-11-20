module

public import MeyerGeneralProblem.Carrier.ClusterDecomposition
public import MeyerGeneralProblem.Carrier.SeparatedDensity
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Centered counts of finite affine lattice unions

The indexed full lines may overlap and may include singletons. Bounding
the count of the actual union by the sum of its constituent counts
gives a linear bound at every radius at least one.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- The full affine integer line, including the zero-step singleton. -/
def affineLatticeLine (y w : ℝ) : Set ℝ :=
  Set.range (fun k : ℤ => y + (k : ℝ) * w)

@[simp]
theorem affineLatticeLine_zero (y : ℝ) : affineLatticeLine y 0 = {y} := by
  ext x
  simp [affineLatticeLine, eq_comm]

theorem affineLatticeLine_neg (y w : ℝ) : affineLatticeLine y (-w) = affineLatticeLine y w := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by push_cast; ring⟩

theorem affineLatticeLine_abs (y w : ℝ) : affineLatticeLine y |w| = affineLatticeLine y w := by
  by_cases h : 0 ≤ w
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), affineLatticeLine_neg]

private def latticeWindow (y w l r : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(l - y) / w⌉ ⌊(r - y) / w⌋

private theorem affineLatticeLine_inter_subset_window (y w l r : ℝ) (hw : 0 < w) :
    affineLatticeLine y w ∩ Icc l r ⊆
      (↑((latticeWindow y w l r).image fun k : ℤ => y + (k : ℝ) * w) : Set ℝ) := by
  classical
  rintro _ ⟨⟨k, rfl⟩, hlo, hhi⟩
  apply Finset.mem_image.mpr
  refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Int.ceil_le.mpr ((div_le_iff₀ hw).mpr (by linarith))
  · exact Int.le_floor.mpr ((le_div_iff₀ hw).mpr (by linarith))

/-- Each full affine lattice line is locally finite. -/
def affineLatticeLineCarrier (y w : ℝ) : LocallyFiniteCarrier where
  carrier := affineLatticeLine y w
  finite_inter_Icc l r := by
    by_cases he : w = 0
    · rw [he, affineLatticeLine_zero]
      exact (Set.finite_singleton y).subset inter_subset_left
    · rw [← affineLatticeLine_abs y w]
      exact (Finset.finite_toSet _).subset
        (affineLatticeLine_inter_subset_window y |w| l r (abs_pos.mpr he))

private theorem affineLatticeLine_centered_count_pos (y w R : ℝ) (hw : 0 < w)
    (hR : 0 ≤ R) :
    ((affineLatticeLine y w ∩ Icc (-R) R).ncard : ℝ) ≤ 2 * R / w + 1 := by
  classical
  let P := latticeWindow y w (-R) R
  let F := P.image (fun k : ℤ => y + (k : ℝ) * w)
  have hs : (affineLatticeLine y w ∩ Icc (-R) R).ncard ≤ P.card := calc
    _ ≤ (F : Set ℝ).ncard := Set.ncard_le_ncard
      (affineLatticeLine_inter_subset_window y w (-R) R hw) F.finite_toSet
    _ ≤ _ := by rw [Set.ncard_coe_finset]; exact Finset.card_image_le
  apply (Nat.cast_le.mpr hs).trans
  let l : ℤ := ⌈(-R - y) / w⌉
  let r : ℤ := ⌊(R - y) / w⌋
  change ((Finset.Icc l r).card : ℝ) ≤ _
  by_cases h : l ≤ r + 1
  · have hc := congrArg (fun x : ℤ => (x : ℝ)) (Int.card_Icc_of_le l r h)
    push_cast at hc
    rw [hc]
    have hlo : (-R - y) / w ≤ (l : ℝ) := Int.le_ceil _
    have hhi : (r : ℝ) ≤ (R - y) / w := Int.floor_le _
    linarith [show (R - y) / w - (-R - y) / w = 2 * R / w by ring]
  · have hz : r + 1 - l ≤ 0 := by omega
    rw [Int.card_Icc, Int.toNat_of_nonpos hz, Nat.cast_zero]
    positivity

/-- A uniform-in-the-origin linear count for a specified full line. -/
theorem affineLatticeLine_centered_count (y w R : ℝ) (hR : 1 ≤ R) :
    ((affineLatticeLine y w ∩ Icc (-R) R).ncard : ℝ) ≤
      (if w = 0 then 1 else 2 / |w| + 1) * R := by
  by_cases h : w = 0
  · rw [ite_eq_left h, one_mul, h, affineLatticeLine_zero]
    have hm : ({y} ∩ Icc (-R) R).ncard ≤ 1 := by
      simpa only [ncard_singleton] using
        Set.ncard_le_ncard (inter_subset_left : {y} ∩ Icc (-R) R ⊆ {y}) (Set.finite_singleton y)
    have hmR : (({y} ∩ Icc (-R) R).ncard : ℝ) ≤ 1 := by exact_mod_cast hm
    exact hmR.trans hR
  · rw [ite_eq_right h, ← affineLatticeLine_abs y w]
    refine (affineLatticeLine_centered_count_pos y |w| R (abs_pos.mpr h) (by linarith)).trans ?_
    linarith [show 2 * R / |w| = (2 / |w|) * R by ring]

/-- The true finite union of the specified affine integer lines. -/
def affineLatticeUnionCarrier (E : Finset (ℝ × ℝ)) : LocallyFiniteCarrier where
  carrier := ⋃ p : E, affineLatticeLine p.val.1 p.val.2
  finite_inter_Icc l r := by
    rw [iUnion_inter]
    exact finite_iUnion fun p => (affineLatticeLineCarrier p.val.1 p.val.2).finite_inter_Icc l r

theorem mem_affineLatticeUnionCarrier (E : Finset (ℝ × ℝ)) (x : ℝ) :
    x ∈ (affineLatticeUnionCarrier E).carrier ↔ ∃ p ∈ E, x ∈ affineLatticeLine p.1 p.2 := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact ⟨p, p.property, hp⟩
  · rintro ⟨p, hp, hx⟩
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩

/-- Every specified finite affine lattice union has a genuine linear
centered window count. Multiple representations of a site only reduce
the count of this union. -/
theorem exists_affineLatticeUnionCarrier_linear_count (E : Finset (ℝ × ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R →
      ((((affineLatticeUnionCarrier E).carrier ∩ Icc (-R) R).ncard : ℕ) : ℝ) ≤ B * R := by
  classical
  let c (p : E) : ℝ := if p.val.2 = 0 then 1 else 2 / |p.val.2| + 1
  refine ⟨∑ p : E, c p, Finset.sum_nonneg (fun p _ => by unfold c; split <;> positivity), ?_⟩
  intro R hR
  let F (p : E) := ((affineLatticeLineCarrier p.val.1 p.val.2).finite_inter_Icc (-R) R).toFinset
  let K := Finset.univ.biUnion F
  have hsub : (affineLatticeUnionCarrier E).carrier ∩ Icc (-R) R ⊆ (K : Set ℝ) := by
    rintro x ⟨hx, hw⟩
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, ((affineLatticeLineCarrier p.val.1 p.val.2).finite_inter_Icc (-R) R).mem_toFinset.mpr ⟨hp, hw⟩⟩
  calc
    _ ≤ (K.card : ℝ) := by
      exact_mod_cast (Set.ncard_le_ncard hsub K.finite_toSet).trans_eq (Set.ncard_coe_finset K)
    _ ≤ ∑ p : E, ((F p).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : K.card ≤ ∑ p : E, (F p).card)
    _ ≤ ∑ p : E, c p * R := by
      apply Finset.sum_le_sum
      intro p _
      have hf := Set.ncard_eq_toFinset_card _ ((affineLatticeLineCarrier p.val.1 p.val.2).finite_inter_Icc (-R) R)
      rw [← hf]
      exact affineLatticeLine_centered_count p.val.1 p.val.2 R hR
    _ = _ := (Finset.sum_mul _ _ _).symm


private theorem affineLatticeLine_separated (y w : ℝ) (hw : 0 < w) :
    ∀ x ∈ affineLatticeLine y w, ∀ z ∈ affineLatticeLine y w, x ≠ z → w ≤ |x - z| := by
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ hne
  have hkl : k ≠ l := fun h => hne (by rw [h])
  have hnonzero : k - l ≠ 0 := sub_ne_zero.mpr hkl
  have habs : (1 : ℤ) ≤ |k - l| := by
    have hp : 0 < |k - l| := abs_pos.mpr hnonzero
    omega
  rw [show y + (k : ℝ) * w - (y + (l : ℝ) * w) = ((k - l : ℤ) : ℝ) * w by
    push_cast; ring, abs_mul, abs_of_pos hw]
  have hone : (1 : ℝ) ≤ |((k - l : ℤ) : ℝ)| := by exact_mod_cast habs
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hw.le

/-- An explicit unit-cell cap for a finite union of positive-step lattices. -/
theorem unitCellBound_affineLatticeUnionCarrier (E : Finset (ℝ × ℝ))
    (hE : ∀ p ∈ E, 0 < p.2) :
    UnitCellBound (affineLatticeUnionCarrier E) (∑ p ∈ E, (⌊1 / p.2⌋₊ + 1)) := by
  classical
  intro n
  let L (p : E) := affineLatticeLineCarrier p.val.1 p.val.2
  let F (p : E) := ((L p).finite_window n 1).toFinset
  have hsub : (affineLatticeUnionCarrier E).carrier ∩ Ico (n : ℝ) ((n : ℝ) + 1) ⊆
      (↑(Finset.univ.biUnion F) : Set ℝ) := by
    rintro x ⟨hx, hn⟩
    obtain ⟨p, hp, hxp⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
    exact Finset.mem_biUnion.mpr
      ⟨⟨p, hp⟩, Finset.mem_univ _, ((L ⟨p, hp⟩).finite_window n 1).mem_toFinset.mpr ⟨hxp, hn⟩⟩
  unfold windowCount
  calc
    _ ≤ (Finset.univ.biUnion F).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ p : E, (F p).card := Finset.card_biUnion_le
    _ ≤ ∑ p : E, (⌊1 / p.val.2⌋₊ + 1) := by
      apply Finset.sum_le_sum
      intro p _
      rw [← (L p).windowCount_eq_toFinset_card]
      exact (L p).windowCount_le_natFloor_div_add_one_of_separated (hE p p.property)
        (affineLatticeLine_separated p.val.1 p.val.2 (hE p p.property)) zero_le_one
    _ = _ := Finset.sum_attach E (fun p => ⌊1 / p.2⌋₊ + 1)

end
end MeyerGeneralProblem
