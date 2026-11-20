module

public import MeyerGeneralProblem.Interpolation.CanonicalBlockInterpolation

@[expose] public section

/-!
# Exact finite selection of all canonical groups touching a block

The touching classes are exactly the quotient image of actual carrier points
in the oriented triple window. Local finiteness proves finiteness and the
actual point count bounds the number of classes. Thus uniform source block
counts supply the finite-pattern bound needed for local interpolation.
Original signed-node prefixes are never reordered on the negative ray.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

/-- Actual carrier points whose oriented coordinates lie in a half-open
interval. For the negative ray this gives the reflected half-open convention. -/
def orientedIntervalPoints (S : LocallyFiniteCarrier) (ε a u : ℝ) : Set S.subtype :=
  {x | ε * (x : ℝ) ∈ Ico a u}

/-- Local finiteness controls every oriented finite interval on either ray. -/
theorem finite_orientedIntervalPoints (S : LocallyFiniteCarrier) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (a u : ℝ) : (orientedIntervalPoints S ε a u).Finite := by
  rcases hε with rfl | rfl
  · have hf := Set.Finite.preimage (f := fun x : S.subtype => (x : ℝ))
      Subtype.val_injective.injOn (S.finite_inter_Icc a u)
    apply hf.subset
    intro x hx
    exact ⟨x.property, by simpa only [orientedIntervalPoints, mem_ofPred_eq, one_mul] using hx.1,
      by simpa only [orientedIntervalPoints, mem_ofPred_eq, one_mul] using hx.2.le⟩
  · have hf := Set.Finite.preimage (f := fun x : S.subtype => (x : ℝ))
      Subtype.val_injective.injOn (S.finite_inter_Icc (-u) (-a))
    apply hf.subset
    intro x hx
    change a ≤ -1 * (x : ℝ) ∧ -1 * (x : ℝ) < u at hx
    exact ⟨x.property, by linarith [hx.2], by linarith [hx.1]⟩

/-- Actual points of one source block, using integer indices to avoid
truncation at the predecessor block. -/
def orientedBlockPoints (S : LocallyFiniteCarrier) (B ε : ℝ) (j : ℤ) : Set S.subtype :=
  orientedIntervalPoints S ε ((j : ℝ) * B) (((j : ℝ) + 1) * B)

/-- Actual carrier points in the three-block interpolation window. -/
def orientedTripleBlockPoints (S : LocallyFiniteCarrier) (B ε : ℝ) (b : ℕ) : Set S.subtype :=
  orientedIntervalPoints S ε (((b : ℝ) - 1) * B) (((b : ℝ) + 2) * B)

/-- The actual triple-window point set is finite, with no density input. -/
theorem finite_orientedTripleBlockPoints (S : LocallyFiniteCarrier) (B : ℝ)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    (orientedTripleBlockPoints S B ε b).Finite :=
  finite_orientedIntervalPoints S hε _ _

/-- A triple window is exactly the union of its three half-open source
blocks, including every boundary point once. -/
theorem orientedTripleBlockPoints_eq_union (S : LocallyFiniteCarrier) (B ε : ℝ) (b : ℕ) :
    orientedTripleBlockPoints S B ε b =
      orientedBlockPoints S B ε ((b : ℤ) - 1) ∪
      orientedBlockPoints S B ε (b : ℤ) ∪
      orientedBlockPoints S B ε ((b : ℤ) + 1) := by
  ext x
  simp only [orientedTripleBlockPoints, orientedBlockPoints, orientedIntervalPoints,
    mem_ofPred_eq, mem_Ico, mem_union, Int.cast_sub, Int.cast_add,
    Int.cast_natCast, Int.cast_one]
  constructor
  · intro hx
    rcases lt_or_ge (ε * (x : ℝ)) ((b : ℝ) * B) with h | h
    · exact Or.inl (Or.inl ⟨hx.1, by nlinarith⟩)
    · rcases lt_or_ge (ε * (x : ℝ)) (((b : ℝ) + 1) * B) with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr ⟨h', by nlinarith [hx.2]⟩
  · rintro ((hx | hx) | hx) <;> constructor <;> nlinarith [hx.1, hx.2]

/-- Actual counts in the three source blocks bound the triple-window count. -/
theorem ncard_orientedTripleBlockPoints_le (S : LocallyFiniteCarrier) (B ε : ℝ) (b : ℕ) :
    (orientedTripleBlockPoints S B ε b).ncard ≤
      (orientedBlockPoints S B ε ((b : ℤ) - 1)).ncard +
      (orientedBlockPoints S B ε (b : ℤ)).ncard +
      (orientedBlockPoints S B ε ((b : ℤ) + 1)).ncard := by
  rw [orientedTripleBlockPoints_eq_union S B ε b]
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)

/-- All and only the actual canonical clusters with a node in the oriented
triple window; whole clusters are retained when they straddle a boundary. -/
def canonicalBlockClasses (B ε : ℝ) (b : ℕ) : Set (CanonicalClusterIndex S d) :=
  {C | groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b}

/-- Exact quotient-image description of all touching classes. This avoids
assuming a finite selection or bounding an arbitrarily chosen witness list. -/
theorem canonicalBlockClasses_eq_image (B ε : ℝ) (b : ℕ) :
    horder.canonicalBlockClasses B ε b =
      Quotient.mk (clusterSetoid S d) '' orientedTripleBlockPoints S B ε b := by
  ext C
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hs⟩
    exact ⟨horder.orderedClusterNode C i, hs, horder.orderedClusterNode_class C i⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨⟨C, i⟩, hi⟩ := horder.orderedClusterNode_bijective.2 x
    have hclass : Quotient.mk (clusterSetoid S d) x = C := by
      rw [← hi]
      exact horder.orderedClusterNode_class C i
    rw [hclass]
    refine ⟨ε * horder.realClusterNode C i, ⟨i, rfl⟩, ?_⟩
    change ε * (x : ℝ) ∈ tripleBlockWindow B b at hx
    simpa only [realClusterNode, hi] using hx

/-- All touching canonical classes form a finite set. -/
theorem finite_canonicalBlockClasses (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) : (horder.canonicalBlockClasses B ε b).Finite := by
  rw [horder.canonicalBlockClasses_eq_image]
  exact (finite_orientedTripleBlockPoints S B hε b).image _

/-- Each touching class contains an actual window point, so the class count
is at most the actual point count, even if full classes overhang the window. -/
theorem ncard_canonicalBlockClasses_le (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    (horder.canonicalBlockClasses B ε b).ncard ≤
      (orientedTripleBlockPoints S B ε b).ncard := by
  rw [horder.canonicalBlockClasses_eq_image]
  exact Set.ncard_image_le (finite_orientedTripleBlockPoints S B hε b)

/-- Uniform source block counts imply the required `3N` bound on the
actual complete set of touching classes, without a finite-choice premise. -/
theorem ncard_canonicalBlockClasses_le_three_mul (B : ℝ)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (N : ℕ) (b₀ : ℤ)
    (hcount : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N)
    (b : ℕ) (hb : b₀ + 1 ≤ (b : ℤ)) :
    (horder.canonicalBlockClasses B ε b).ncard ≤ 3 * N := by
  have h₁ := hcount ((b : ℤ) - 1) (by omega)
  have h₂ := hcount (b : ℤ) (by omega)
  have h₃ := hcount ((b : ℤ) + 1) (by omega)
  exact (horder.ncard_canonicalBlockClasses_le B hε b).trans
    ((ncard_orientedTripleBlockPoints_le S B ε b).trans (by omega))

/-- The finite set used for local interpolation is the entire proved set
of touching canonical classes, not an input selection. -/
def canonicalBlockFinset (B : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    Finset (CanonicalClusterIndex S d) :=
  (horder.finite_canonicalBlockClasses B hε b).toFinset

/-- Membership in the finite selection is exactly actual node contact. -/
@[simp] theorem mem_canonicalBlockFinset (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) (C : CanonicalClusterIndex S d) :
    C ∈ horder.canonicalBlockFinset B hε b ↔
      groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b := by
  simp only [canonicalBlockFinset, Set.Finite.mem_toFinset, canonicalBlockClasses, mem_ofPred_eq]

/-- An injective finite enumeration of every touching class. The internal
canonical node enumeration is unchanged by this exterior class enumeration. -/
def canonicalBlockEnum (B : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    Fin (horder.canonicalBlockFinset B hε b).card ↪ CanonicalClusterIndex S d :=
  (horder.canonicalBlockFinset B hε b).equivFin.symm.toEmbedding.trans
    (Function.Embedding.subtype _)

/-- Every enumerated class really touches the oriented window. -/
theorem canonicalBlockEnum_touches (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (g : Fin (horder.canonicalBlockFinset B hε b).card) :
    groupTouchesTripleBlock B
      (range (fun i => ε * horder.realClusterNode (horder.canonicalBlockEnum B hε b g) i)) b := by
  apply (horder.mem_canonicalBlockFinset B hε b _).mp
  exact ((horder.canonicalBlockFinset B hε b).equivFin.symm g).property

/-- The selected enumeration covers every touching canonical class. -/
theorem range_canonicalBlockEnum (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    range (horder.canonicalBlockEnum B hε b) = horder.canonicalBlockClasses B ε b := by
  ext C
  constructor
  · rintro ⟨g, rfl⟩
    exact horder.canonicalBlockEnum_touches B hε b g
  · intro hC
    let x : horder.canonicalBlockFinset B hε b :=
      ⟨C, (horder.mem_canonicalBlockFinset B hε b C).mpr hC⟩
    refine ⟨(horder.canonicalBlockFinset B hε b).equivFin x, ?_⟩
    simp [canonicalBlockEnum, x]

/-- The finite enumeration has the proved actual quotient-image count. -/
theorem card_canonicalBlockFinset (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    (horder.canonicalBlockFinset B hε b).card =
      (horder.canonicalBlockClasses B ε b).ncard := by
  exact (Set.ncard_eq_toFinset_card _ (horder.finite_canonicalBlockClasses B hε b)).symm

/-- Exact finite reindexing from the selected list to canonical classes.
No ordering or multiplicity is changed in a group's own coefficient vector. -/
theorem sum_canonicalBlockEnum {M : Type*} [AddCommMonoid M] (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) (E : CanonicalClusterIndex S d → M) :
    (∑ g, E (horder.canonicalBlockEnum B hε b g)) =
      ∑ C ∈ horder.canonicalBlockFinset B hε b, E C := by
  let F := horder.canonicalBlockFinset B hε b
  change (∑ g, E ((F.equivFin.symm g : F) : CanonicalClusterIndex S d)) = _
  exact (F.equivFin.symm.sum_comp (fun C : F => E C)).trans (Finset.sum_coe_sort F E)

/-- The finite selected energy equals the global canonical indicator sum,
even for infinite nonnegative coefficients. No summability premise is used. -/
theorem sum_canonicalBlockEnum_eq_tsum (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) (E : CanonicalClusterIndex S d → ℝ≥0∞) :
    (∑ g, E (horder.canonicalBlockEnum B hε b g)) =
      ∑' C : CanonicalClusterIndex S d,
        if groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b
        then E C else 0 := by
  rw [horder.sum_canonicalBlockEnum]
  rw [tsum_eq_sum (s := horder.canonicalBlockFinset B hε b) (by
    intro C hC
    have hn := mt (horder.mem_canonicalBlockFinset B hε b C).mpr hC
    exact ite_eq_right hn)]
  apply Finset.sum_congr rfl
  intro C hC
  exact (ite_eq_left ((horder.mem_canonicalBlockFinset B hε b C).mp hC)).symm

/-- Actual local coefficient energy, including every prefix of every whole
canonical cluster touching the window exactly once. -/
def canonicalBlockDataEnergy (B : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) : ℝ :=
  ∑ C ∈ horder.canonicalBlockFinset B hε b, ∑ j, ‖data C j‖ ^ 2

/-- The actual finite local data energy is nonnegative. -/
theorem canonicalBlockDataEnergy_nonneg (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    0 ≤ horder.canonicalBlockDataEnergy B hε b data :=
  Finset.sum_nonneg (fun C _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖data C j‖))

/-- The actual finite grouped coefficient sum is exactly the canonical
local energy, rather than a bound with an extra cluster multiplicity. -/
theorem sum_canonicalBlockEnum_data (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    (∑ g, ∑ j, ‖data (horder.canonicalBlockEnum B hε b g) j‖ ^ 2) =
      horder.canonicalBlockDataEnergy B hε b data :=
  horder.sum_canonicalBlockEnum B hε b (fun C => ∑ j : Fin (horder.clusterSize C), ‖data C j‖ ^ 2)

/-- The actual selected data sup norm is bounded by the square root of
the canonical local energy, including when the touching set is empty. -/
theorem norm_canonicalBlockEnum_data_le_sqrt (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    ‖fun g => data (horder.canonicalBlockEnum B hε b g)‖ ≤
      Real.sqrt (horder.canonicalBlockDataEnergy B hε b data) := by
  have h := groupedData_norm_sq_le_sum _ (fun g => data (horder.canonicalBlockEnum B hε b g))
  rw [horder.sum_canonicalBlockEnum_data B hε b data] at h
  nlinarith [Real.sq_sqrt (horder.canonicalBlockDataEnergy_nonneg B hε b data),
    Real.sqrt_nonneg (horder.canonicalBlockDataEnergy B hε b data),
    norm_nonneg (fun g => data (horder.canonicalBlockEnum B hε b g))]

/-- Matching canonical prefixes on all touching classes gives interpolation
at every actual carrier point in the oriented triple window. -/
theorem allTouching_values_of_prefix_eq (B ε : ℝ) (b : ℕ) (f h : ℝ → ℂ)
    (hprefix : ∀ C : CanonicalClusterIndex S d,
      groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
      ∀ i : Fin (horder.clusterSize C),
        analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
          (fun s => h (ε * s)) =
        analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i f)
    (x : S.subtype) (hx : x ∈ orientedTripleBlockPoints S B ε b) :
    h (ε * (x : ℝ)) = f (x : ℝ) := by
  obtain ⟨⟨C, i⟩, hi⟩ := horder.orderedClusterNode_bijective.2 x
  have ht : groupTouchesTripleBlock B
      (range (fun j => ε * horder.realClusterNode C j)) b := by
    refine ⟨ε * horder.realClusterNode C i, ⟨i, rfl⟩, ?_⟩
    change ε * (x : ℝ) ∈ tripleBlockWindow B b at hx
    simpa only [realClusterNode, hi] using hx
  simpa only [realClusterNode, hi] using
    horder.canonicalBlock_values_of_prefix_eq C f h ε (hprefix C ht) i

/-- Exact conversion of local real coefficient energy to the global
canonical nonnegative indicator sum. -/
theorem ofReal_canonicalBlockDataEnergy_eq_tsum (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    ENNReal.ofReal (horder.canonicalBlockDataEnergy B hε b data) =
      ∑' C : CanonicalClusterIndex S d,
        if groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b
        then ENNReal.ofReal (∑ j, ‖data C j‖ ^ 2) else 0 := by
  rw [← horder.sum_canonicalBlockEnum_eq_tsum B hε b]
  rw [horder.sum_canonicalBlockEnum B hε b
    (fun C => ENNReal.ofReal (∑ j : Fin (horder.clusterSize C), ‖data C j‖ ^ 2))]
  exact ENNReal.ofReal_sum_of_nonneg (fun C _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖data C j‖))

/-- On the exterior part of either ray, every actual node is within one
block length of the magnitude of any actual node chosen as its cluster anchor. -/
theorem canonicalBlock_node_near_abs_anchor {B : ℝ} (hd : 0 < d)
    (hdiam : (q : ℝ) * d ≤ B) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (C : CanonicalClusterIndex S d) (a : Fin (horder.clusterSize C)) {s : ℝ}
    (hs : s ∈ range (fun i => ε * horder.realClusterNode C i) ∩ Ici B) :
    |s - (|horder.realClusterNode C a|)| ≤ B := by
  obtain ⟨⟨i, rfl⟩, hs⟩ := hs
  have hraw : |horder.realClusterNode C i - horder.realClusterNode C a| ≤ B := by
    simpa only [Real.dist_eq] using (horder.realClusterNode_diameter hd C i a).trans hdiam
  have hnear : |ε * horder.realClusterNode C i - ε * horder.realClusterNode C a| ≤ B := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hraw
    · simpa only [neg_one_mul, neg_sub_neg, abs_sub_comm] using hraw
  have ha : 0 ≤ ε * horder.realClusterNode C a := by
    have hu := (abs_le.mp hnear).2
    change B ≤ ε * horder.realClusterNode C i at hs
    linarith
  have habs : |horder.realClusterNode C a| = ε * horder.realClusterNode C a := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using abs_of_nonneg (by simpa only [one_mul] using ha)
    · simpa only [neg_one_mul] using abs_of_nonpos (by simpa only [neg_one_mul, neg_nonneg] using ha)
  rw [habs]
  exact hnear

/-- Exterior windows see exactly the same clusters after restricting the
oriented node sets to their positive tail. No exterior constraint is discarded. -/
theorem canonicalBlock_touches_positive_tail_iff {B : ℝ} (hB : 0 < B)
    (ε : ℝ) {b : ℕ} (hb : 2 ≤ b) (C : CanonicalClusterIndex S d) :
    groupTouchesTripleBlock B
      (range (fun i => ε * horder.realClusterNode C i) ∩ Ici B) b ↔
    groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b := by
  constructor
  · rintro ⟨s, ⟨hs, _⟩, hw⟩
    exact ⟨s, hs, hw⟩
  · rintro ⟨s, hs, hw⟩
    refine ⟨s, ⟨hs, ?_⟩, hw⟩
    have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    change B ≤ s
    have hl := hw.1
    change ((b : ℝ) - 1) * B ≤ s at hl
    nlinarith

/-- Summing the selected local coefficient energies over all exterior
blocks costs only the proved five-window factor and the exact physical anchor
weight. The anchor is any actual node of each cluster; both ray signs work.
The global data may have infinite energy. -/
theorem tsum_canonicalBlockDataEnergy_weighted_le {B : ℝ} (hB : 0 < B)
    (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    (∑' b : ℕ, if 3 ≤ b then
      ENNReal.ofReal (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
        ENNReal.ofReal (horder.canonicalBlockDataEnergy B hε b data) else 0) ≤
      5 * ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) - 1 / 2)) *
        ∑' C : CanonicalClusterIndex S d,
          ENNReal.ofReal ((1 + Real.sqrt |horder.realClusterNode C (anchor C)|) ^ (2 * k - 1)) *
            ENNReal.ofReal (∑ j, ‖data C j‖ ^ 2) := by
  have h := tsum_tripleBlock_weighted_groupEnergy_le B hB
    (fun C => |horder.realClusterNode C (anchor C)|) (fun C => abs_nonneg _)
    (fun C => range (fun i => ε * horder.realClusterNode C i) ∩ Ici B)
    (fun C s hs => horder.canonicalBlock_node_near_abs_anchor hd hdiam hε C (anchor C) hs)
    k hk (fun C => ENNReal.ofReal (∑ j, ‖data C j‖ ^ 2))
  refine (le_of_eq ?_).trans h
  apply tsum_congr
  intro b
  by_cases hb : 3 ≤ b
  · rw [ite_eq_left hb, horder.ofReal_canonicalBlockDataEnergy_eq_tsum, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro C
    rw [horder.canonicalBlock_touches_positive_tail_iff hB ε (by omega) C]
    by_cases ht : groupTouchesTripleBlock B
        (range (fun i => ε * horder.realClusterNode C i)) b <;> simp [hb, ht]
  · simp [hb]

end BoundedClusterOrder

/-- Uniform source block counts construct a genuine interpolant on every
whole touching class. The selection, cardinal bound, and local energy bound
are proved outputs of the actual carrier geometry and polynomial construction. -/
theorem exists_uniform_allTouching_block_interpolant (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ,
      (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ b : ℕ, b₀ + 1 ≤ (b : ℤ) → 2 ≤ b →
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ,
        ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧
          (∀ C : CanonicalClusterIndex S d,
            groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
            ∀ i : Fin (horder.clusterSize C),
              analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
                (fun s => h (ε * s)) = data C i) ∧
          (∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
            ∀ j ≤ k, ‖iteratedDeriv j h x‖ ≤
              C * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data)) ∧
          let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
          MeasureTheory.Integrable (fun x => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
          MeasureTheory.Integrable (fun x => ‖iteratedDeriv k f x‖ ^ 2) ∧
          (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
              (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤
            C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
              horder.canonicalBlockDataEnergy B hε b data := by
  obtain ⟨CI, hCI, hinterp⟩ := exists_uniform_canonicalBlock_polynomialInterpolant (3 * N) q k hB hd hdiam
  obtain ⟨CE, hCE, henergy⟩ := exists_uniform_quadraticBlock_energy_bound k
  have hCI2 : 0 < CE * CI ^ 2 := mul_pos hCE (sq_pos_of_pos hCI)
  refine ⟨CI + CE * CI ^ 2, add_pos hCI hCI2, ?_⟩
  intro S horder ε hε b₀ hcount b hb₀ hb data
  have hcard : (horder.canonicalBlockFinset B hε b).card ≤ 3 * N := by
    rw [horder.card_canonicalBlockFinset]
    exact horder.ncard_canonicalBlockClasses_le_three_mul B hε N b₀ hcount b hb₀
  obtain ⟨p, hsmooth, hprefix, _hcoeff, hderiv⟩ := hinterp S horder _ hcard
    (horder.canonicalBlockEnum B hε b) (horder.canonicalBlockEnum B hε b).injective
    b ε hε (horder.canonicalBlockEnum_touches B hε b)
    (fun g => data (horder.canonicalBlockEnum B hε b g))
  have hderiv' : ∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
      ∀ j ≤ k, ‖iteratedDeriv j
        (fun t : ℝ => p.1.eval ((ε * t - ε * ((b : ℝ) * B) : ℝ) : ℂ)) x‖ ≤
          CI * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data) := by
    intro x hx j hj
    exact (hderiv x hx j hj).trans (mul_le_mul_of_nonneg_left
      (horder.norm_canonicalBlockEnum_data_le_sqrt B hε b data) hCI.le)
  have he := henergy B hB b hb _ hsmooth
    (CI * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data))
    (mul_nonneg hCI.le (Real.sqrt_nonneg _)) hderiv'
  refine ⟨_, hsmooth, ?_, ?_, he.1, he.2.1, ?_⟩
  · intro C ht i
    have ht' : C ∈ horder.canonicalBlockClasses B ε b := ht
    rw [← horder.range_canonicalBlockEnum B hε b] at ht'
    obtain ⟨g, rfl⟩ := ht'
    exact hprefix g i
  · intro x hx j hj
    exact (hderiv' x hx j hj).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hCI2.le) (Real.sqrt_nonneg _))
  · calc
      _ ≤ CE * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
          (CI * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data)) ^ 2 := he.2.2
      _ = (CE * CI ^ 2) * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
          horder.canonicalBlockDataEnergy B hε b data := by
        rw [mul_pow, Real.sq_sqrt (horder.canonicalBlockDataEnergy_nonneg B hε b data)]
        ring
      _ ≤ _ := by
        gcongr
        all_goals first
          | exact horder.canonicalBlockDataEnergy_nonneg B hε b data
          | exact le_add_of_nonneg_left hCI.le

/-- One family of actual smooth local interpolants is constructed for all
exterior blocks from the same global canonical data. The constants precede
the carrier and data. Inactive initial blocks are identically zero. This is a
local family; infinite physical sums and their ray restrictions are separate. -/
theorem exists_uniform_allTouching_interpolation_family (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ,
      (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ,
        ∃ h : ℕ → ℝ → ℂ, (∀ b, ContDiff ℝ ∞ (h b)) ∧
          (∀ b : ℕ, ¬(b₀ + 1 ≤ (b : ℤ) ∧ 2 ≤ b) → h b = 0) ∧
          ∀ b : ℕ, b₀ + 1 ≤ (b : ℤ) → 2 ≤ b →
          (∀ C : CanonicalClusterIndex S d,
            groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
            ∀ i : Fin (horder.clusterSize C),
              analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
                (fun s => h b (ε * s)) = data C i) ∧
          (∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
            ∀ j ≤ k, ‖iteratedDeriv j (h b) x‖ ≤
              C * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data)) ∧
          let f := quadraticBlockPiece B b (fun x : ℝ => h b (x ^ 2))
          MeasureTheory.Integrable (fun x => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
          MeasureTheory.Integrable (fun x => ‖iteratedDeriv k f x‖ ^ 2) ∧
          (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
              (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤
            C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
              horder.canonicalBlockDataEnergy B hε b data := by
  obtain ⟨C, hC, hlocal⟩ := exists_uniform_allTouching_block_interpolant N q k hB hd hdiam
  refine ⟨C, hC, ?_⟩
  intro S horder ε hε b₀ hcount data
  let Valid (b : ℕ) := b₀ + 1 ≤ (b : ℤ) ∧ 2 ≤ b
  have hex (b : ℕ) : ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧
      (¬Valid b → h = 0) ∧
      (Valid b →
        (∀ C : CanonicalClusterIndex S d,
          groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
          ∀ i : Fin (horder.clusterSize C),
            analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
              (fun s => h (ε * s)) = data C i) ∧
        (∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
          ∀ j ≤ k, ‖iteratedDeriv j h x‖ ≤
            C * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data)) ∧
        let f := quadraticBlockPiece B b (fun x : ℝ => h (x ^ 2))
        MeasureTheory.Integrable (fun x => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
        MeasureTheory.Integrable (fun x => ‖iteratedDeriv k f x‖ ^ 2) ∧
        (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
            (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤
          C * B * (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
            horder.canonicalBlockDataEnergy B hε b data) := by
    by_cases hb : Valid b
    · obtain ⟨h, hs, hp⟩ := hlocal S horder ε hε b₀ hcount b hb.1 hb.2 data
      exact ⟨h, hs, fun hn => False.elim (hn hb), fun _ => hp⟩
    · exact ⟨0, contDiff_const, fun _ => rfl, fun h => False.elim (hb h)⟩
  choose h hs hz hp using hex
  exact ⟨h, hs, hz, fun b hb₀ hb => hp b ⟨hb₀, hb⟩⟩

end

end MeyerGeneralProblem
