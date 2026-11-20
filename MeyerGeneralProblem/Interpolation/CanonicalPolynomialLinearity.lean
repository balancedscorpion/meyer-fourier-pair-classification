module

public import MeyerGeneralProblem.Interpolation.CanonicalBlockSelection
public import MeyerGeneralProblem.Interpolation.PhysicalBlockGluing

@[expose] public section

/-!
# Linear canonical local polynomial interpolation

The unique grouped polynomial inverse determines the actual local polynomial
as a complex-linear map. Existing uniform estimates transfer to this map by
unisolvence, so no data-dependent nonlinear choice remains. The original
signed-node prefix order is retained on both rays.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Polynomial
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q)

/-- Distinct canonical classes remain disjoint after a common translation.
There is no minimum separation requirement inside a class. -/
theorem centeredCanonicalNodes_disjoint (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre : ℝ) :
    GroupedNodeDisjoint (fun g => horder.clusterSize (clusters g))
      (fun g j => (finiteNodeSequence
        (fun i => horder.realClusterNode (clusters g) i - centre) j : ℂ)) := by
  intro g h hgh i hi j hj heq
  have hreal : horder.realClusterNode (clusters g) ⟨i, hi⟩ - centre =
      horder.realClusterNode (clusters h) ⟨j, hj⟩ - centre := by
    apply Complex.ofReal_injective
    simpa only [finiteNodeSequence, dite_eq_left hi, dite_eq_left hj] using heq
  have hn : horder.realClusterNode (clusters g) ⟨i, hi⟩ =
      horder.realClusterNode (clusters h) ⟨j, hj⟩ := by linarith
  have hgap := horder.realClusterNode_separated (hinj.ne hgh) ⟨i, hi⟩ ⟨j, hj⟩
  rw [hn, sub_self, abs_zero] at hgap
  exact (not_le_of_gt hd) hgap

/-- The actual centred polynomial inverse for a finite injective list of
canonical classes, as a linear map on their full prefix data. -/
def canonicalPolynomialMap (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre : ℝ) :
    ((g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ) →ₗ[ℂ]
      Polynomial.degreeLT ℂ (∑ g, horder.clusterSize (clusters g)) :=
  (groupedConfluentDataEquiv (fun g => horder.clusterSize (clusters g))
    (fun g j => (finiteNodeSequence
      (fun i => horder.realClusterNode (clusters g) i - centre) j : ℂ))
    (horder.centeredCanonicalNodes_disjoint hd clusters hinj centre)).symm.toLinearMap

/-- This actual linear inverse prescribes every original analytic prefix. -/
theorem canonicalPolynomialMap_prefix (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre : ℝ) (data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ)
    (g : Fin n) (i : Fin (horder.clusterSize (clusters g))) :
    analyticDividedDifference (finiteNodeSequence (horder.realClusterNode (clusters g))) i
      (fun t : ℝ => (horder.canonicalPolynomialMap hd clusters hinj centre data).1.eval
        ((t - centre : ℝ) : ℂ)) = data g i := by
  rw [analyticDividedDifference_finite_shiftedPolynomial]
  exact polynomialDividedDifference_groupedConfluentInterpolant
    (fun g => horder.clusterSize (clusters g))
    (fun g j => (finiteNodeSequence
      (fun i => horder.realClusterNode (clusters g) i - centre) j : ℂ))
    (horder.centeredCanonicalNodes_disjoint hd clusters hinj centre) data g i

/-- Any polynomial of the required degree with these full prefixes is the
same actual linear inverse. Bounds play no role in this uniqueness proof. -/
theorem eq_canonicalPolynomialMap_of_prefix (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre : ℝ) (data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ)
    (p : Polynomial.degreeLT ℂ (∑ g, horder.clusterSize (clusters g)))
    (hp : ∀ g, ∀ i : Fin (horder.clusterSize (clusters g)),
      analyticDividedDifference (finiteNodeSequence (horder.realClusterNode (clusters g))) i
        (fun t : ℝ => p.1.eval ((t - centre : ℝ) : ℂ)) = data g i) :
    p = horder.canonicalPolynomialMap hd clusters hinj centre data := by
  apply groupedConfluentData_injective _ _
    (horder.centeredCanonicalNodes_disjoint hd clusters hinj centre)
  funext g i
  change polynomialDividedDifference
    (fun j => (finiteNodeSequence (fun a => horder.realClusterNode (clusters g) a - centre) j : ℂ))
    i p.1 = polynomialDividedDifference
    (fun j => (finiteNodeSequence (fun a => horder.realClusterNode (clusters g) a - centre) j : ℂ))
    i (horder.canonicalPolynomialMap hd clusters hinj centre data).1
  rw [← analyticDividedDifference_finite_shiftedPolynomial,
    ← analyticDividedDifference_finite_shiftedPolynomial,
    hp g i, horder.canonicalPolynomialMap_prefix hd clusters hinj centre data g i]

/-- Evaluating the centred inverse in either oriented block coordinate is
still complex-linear in the supplied full grouped data. -/
def canonicalLocalFunctionMap (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre ε : ℝ) :
    ((g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun data t := (horder.canonicalPolynomialMap hd clusters hinj centre data).1.eval
    ((ε*t - centre : ℝ) : ℂ)
  map_add' a b := by ext t; simp
  map_smul' a b := by ext t; simp

/-- Every local function produced by the actual linear inverse is smooth. -/
theorem contDiff_canonicalLocalFunctionMap (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre ε : ℝ) (data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ) :
    ContDiff ℝ ∞ (horder.canonicalLocalFunctionMap hd clusters hinj centre ε data) := by
  have hp : ContDiff ℝ ∞ (fun z : ℂ =>
      (horder.canonicalPolynomialMap hd clusters hinj centre data).1.eval z) := by
    simpa using ((horder.canonicalPolynomialMap hd clusters hinj centre data).1.contDiff_aeval
      (𝕜 := ℂ) ∞).restrict_scalars ℝ
  exact hp.comp (Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- Reflection is only in the evaluation coordinate: all prefix data remain
in the original canonical order, including on the negative ray. -/
theorem canonicalLocalFunctionMap_prefix (hd : 0 < d) {n : ℕ}
    (clusters : Fin n → CanonicalClusterIndex S d) (hinj : Function.Injective clusters)
    (centre : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ)
    (g : Fin n) (i : Fin (horder.clusterSize (clusters g))) :
    analyticDividedDifference (finiteNodeSequence (horder.realClusterNode (clusters g))) i
      (fun s => horder.canonicalLocalFunctionMap hd clusters hinj centre ε data (ε*s)) =
        data g i := by
  change analyticDividedDifference _ _ (fun s : ℝ =>
    (horder.canonicalPolynomialMap hd clusters hinj centre data).1.eval
      ((ε*(ε*s)-centre : ℝ) : ℂ)) = _
  rcases hε with rfl | rfl <;>
    simpa only [one_mul, neg_one_mul, neg_neg] using
      horder.canonicalPolynomialMap_prefix hd clusters hinj centre data g i

end BoundedClusterOrder

/-- The previously proved uniform bounds hold for the actual local linear
map. Unisolvence identifies the bounded existence witness with this map. -/
theorem exists_uniform_canonicalLocalFunctionMap_bound (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ)*d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ n : ℕ, n ≤ N →
      ∀ clusters : Fin n → CanonicalClusterIndex S d,
        ∀ hinj : Function.Injective clusters, ∀ b : ℕ,
        ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        (∀ g, groupTouchesTripleBlock B
          (range (fun i => ε * horder.realClusterNode (clusters g) i)) b) →
        ∀ data : (g : Fin n) → Fin (horder.clusterSize (clusters g)) → ℂ,
          ‖Polynomial.degreeLTEquiv ℂ (∑ g, horder.clusterSize (clusters g))
            (horder.canonicalPolynomialMap hd clusters hinj (ε*((b:ℝ)*B)) data)‖ ≤ C*‖data‖ ∧
          ∀ x ∈ Icc ((b : ℝ)*B-B/8) (((b : ℝ)+1)*B+B/8), ∀ j ≤ k,
            ‖iteratedDeriv j
              (horder.canonicalLocalFunctionMap hd clusters hinj (ε*((b:ℝ)*B)) ε data) x‖ ≤
                C*‖data‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_canonicalBlock_polynomialInterpolant N q k hB hd hdiam
  refine ⟨C, hC, ?_⟩
  intro S horder n hn clusters hinj b ε hε htouch data
  obtain ⟨p, _hs, hp, hc, hh⟩ := hb S horder n hn clusters hinj b ε hε htouch data
  have hp' : p = horder.canonicalPolynomialMap hd clusters hinj (ε*((b:ℝ)*B)) data := by
    apply horder.eq_canonicalPolynomialMap_of_prefix hd clusters hinj _ data p
    intro g i
    have h := hp g i
    rcases hε with rfl | rfl <;>
      simpa only [one_mul, neg_one_mul, neg_neg] using h
  subst p
  exact ⟨hc, hh⟩

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q)

/-- The canonical all-touching local function, as one actual linear map
from the global original-prefix data. Only the finite selected rows are used. -/
def allTouchingLocalFunctionMap (hd : 0 < d) (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ) :
    ((C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun data := horder.canonicalLocalFunctionMap hd (horder.canonicalBlockEnum B hε b)
    (horder.canonicalBlockEnum B hε b).injective (ε*((b:ℝ)*B)) ε
    (fun g => data (horder.canonicalBlockEnum B hε b g))
  map_add' a b := by
    change (horder.canonicalLocalFunctionMap _ _ _ _ _) (_ + _) = _
    exact map_add _ _ _
  map_smul' a b := by
    change (horder.canonicalLocalFunctionMap _ _ _ _ _) (a • _) = _
    exact map_smul _ _ _

/-- The chosen all-touching local map is smooth for every input data vector,
even for blocks where no source count bound has been imposed. -/
theorem contDiff_allTouchingLocalFunctionMap (hd : 0 < d) (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    ContDiff ℝ ∞ (horder.allTouchingLocalFunctionMap hd B hε b data) :=
  horder.contDiff_canonicalLocalFunctionMap hd _ _ _ _ _

/-- Every whole canonical group touching the block receives all of its
original prefix data from the actual linear map. -/
theorem allTouchingLocalFunctionMap_prefix (hd : 0 < d) (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (b : ℕ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ)
    (C : CanonicalClusterIndex S d)
    (hC : groupTouchesTripleBlock B (range (fun i => ε*horder.realClusterNode C i)) b)
    (i : Fin (horder.clusterSize C)) :
    analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
      (fun s => horder.allTouchingLocalFunctionMap hd B hε b data (ε*s)) = data C i := by
  have hmem : C ∈ range (horder.canonicalBlockEnum B hε b) := by
    rw [horder.range_canonicalBlockEnum B hε b]
    exact hC
  obtain ⟨g, rfl⟩ := hmem
  exact horder.canonicalLocalFunctionMap_prefix hd _ _ _ hε _ g i

/-- All local polynomials are selected simultaneously by a single linear
map. Its construction is independent of source thresholds and of input data. -/
def canonicalLocalFamilyMap (hd : 0 < d) (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ((C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) →ₗ[ℂ]
      (ℕ → ℝ → ℂ) :=
  LinearMap.pi (fun b => horder.allTouchingLocalFunctionMap hd B hε b)

/-- The family map evaluates to the actual all-touching local map. -/
theorem canonicalLocalFamilyMap_apply (hd : 0 < d) (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) (b : ℕ) :
    horder.canonicalLocalFamilyMap hd B hε data b =
      horder.allTouchingLocalFunctionMap hd B hε b data := rfl

end BoundedClusterOrder

/-- Actual source block counts give one common derivative bound for the
entire explicit linear family. The constant precedes the carrier, source
threshold, ray, block, and input data; no conditioning estimate is assumed. -/
theorem exists_uniform_canonicalLocalFamilyMap_bound (N q k : ℕ)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ)*d ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ,
      (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ b : ℕ, b₀+1 ≤ (b : ℤ) →
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ,
      ∀ x ∈ Icc ((b : ℝ)*B-B/8) (((b : ℝ)+1)*B+B/8), ∀ j ≤ k,
        ‖iteratedDeriv j (horder.canonicalLocalFamilyMap hd B hε data b) x‖ ≤
          C*Real.sqrt (horder.canonicalBlockDataEnergy B hε b data) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_canonicalLocalFunctionMap_bound (3*N) q k hB hd hdiam
  refine ⟨C, hC, ?_⟩
  intro S horder ε hε b₀ hcount b hb₀ data x hx j hj
  have hcard : (horder.canonicalBlockFinset B hε b).card ≤ 3*N := by
    rw [horder.card_canonicalBlockFinset B hε b]
    exact horder.ncard_canonicalBlockClasses_le_three_mul B hε N b₀ hcount b hb₀
  have h := (hb S horder _ hcard (horder.canonicalBlockEnum B hε b)
    (horder.canonicalBlockEnum B hε b).injective b ε hε
    (horder.canonicalBlockEnum_touches B hε b)
    (fun g => data (horder.canonicalBlockEnum B hε b g))).2 x hx j hj
  exact h.trans (mul_le_mul_of_nonneg_left
    (horder.norm_canonicalBlockEnum_data_le_sqrt B hε b data) hC.le)

private theorem summable_physicalRayBlockTail_terms {B : ℝ} (hB : 0 < B)
    (start : ℕ) (ε : ℝ) (h : ℕ → ℝ → ℂ) (x : ℝ) :
    Summable (fun b => quadraticBlockPiece B b
      (exteriorRayBlockFactor b ε (tailBlockFunctions start h b)) x) := by
  have hs := summable_blockCutoff_smul hB 0
    (fun b _ => exteriorRayBlockFactor b ε (tailBlockFunctions start h b) x) (x^2)
  simpa only [Nat.zero_add, quadraticBlockPiece] using hs

/-- The actual locally finite physical tail is additive in its local
functions, with summability proved from the cutoff supports. -/
theorem physicalRayBlockTail_add {B : ℝ} (hB : 0 < B) (start : ℕ) (ε : ℝ)
    (h g : ℕ → ℝ → ℂ) :
    physicalRayBlockTail B start ε (h+g) =
      physicalRayBlockTail B start ε h + physicalRayBlockTail B start ε g := by
  funext x
  have hterm (b : ℕ) : quadraticBlockPiece B b
      (exteriorRayBlockFactor b ε (tailBlockFunctions start (h+g) b)) x =
      quadraticBlockPiece B b (exteriorRayBlockFactor b ε (tailBlockFunctions start h b)) x +
      quadraticBlockPiece B b (exteriorRayBlockFactor b ε (tailBlockFunctions start g b)) x := by
    simp only [quadraticBlockPiece, exteriorRayBlockFactor, tailBlockFunctions]
    split_ifs <;> simp [smul_add]
  simpa only [physicalRayBlockTail, exteriorRayBlockSum, hterm, Pi.add_apply] using
    (summable_physicalRayBlockTail_terms hB start ε h x).tsum_add
      (summable_physicalRayBlockTail_terms hB start ε g x)

/-- The actual physical tail respects complex scalar multiplication, not
only real changes of amplitude. -/
theorem physicalRayBlockTail_smul (B : ℝ) (start : ℕ) (ε : ℝ)
    (a : ℂ) (h : ℕ → ℝ → ℂ) :
    physicalRayBlockTail B start ε (a • h) = a • physicalRayBlockTail B start ε h := by
  funext x
  have hterm (b : ℕ) : quadraticBlockPiece B b
      (exteriorRayBlockFactor b ε (tailBlockFunctions start (a • h) b)) x =
      a • quadraticBlockPiece B b (exteriorRayBlockFactor b ε (tailBlockFunctions start h b)) x := by
    simp only [quadraticBlockPiece, exteriorRayBlockFactor, tailBlockFunctions]
    split_ifs <;> simp [mul_left_comm]
  simpa only [physicalRayBlockTail, exteriorRayBlockSum, hterm, Pi.smul_apply] using
    (tsum_const_smul'' (f := fun b => quadraticBlockPiece B b
      (exteriorRayBlockFactor b ε (tailBlockFunctions start h b)) x) a)

/-- The actual arbitrary-start physical tail as a linear map on all local
functions. Cutoff local finiteness, not growth or summability inputs, proves
its additivity. -/
def physicalRayBlockTailLinearMap {B : ℝ} (hB : 0 < B) (start : ℕ) (ε : ℝ) :
    (ℕ → ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun := physicalRayBlockTail B start ε
  map_add' := physicalRayBlockTail_add hB start ε
  map_smul' := physicalRayBlockTail_smul B start ε

/-- Composition of the actual canonical polynomial family and the actual
ray tail is a genuine global linear map of the original grouped data. -/
def BoundedClusterOrder.canonicalExteriorLinearMap
    {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)
    (hd : 0 < d) {B : ℝ} (hB : 0 < B) (start : ℕ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ((C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  (physicalRayBlockTailLinearMap hB start ε).comp (horder.canonicalLocalFamilyMap hd B hε)

end

end MeyerGeneralProblem
