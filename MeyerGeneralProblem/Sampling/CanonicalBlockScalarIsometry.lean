module

public import MeyerGeneralProblem.Sampling.CanonicalGraphData
public import MeyerGeneralProblem.Gram.CanonicalGroupedGram
public import MeyerGeneralProblem.Atomic.RieszSynthesis

@[expose] public section

/-!
# Canonical block-to-scalar isometry

This module flattens canonical finite cluster blocks to the exact dependent
scalar index.  Both directions preserve every coordinate definitionally; no
abstract Hilbert-space classification or arbitrary basis choice is used.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

abbrev CanonicalScalarIndex :=
  Σ C : CanonicalClusterIndex S.signedSquareImage d, Fin (horder.clusterSize C)

/-- Flatten the exact canonical cluster blocks to their scalar sigma coordinates. -/
def canonicalGraphDataFlatten (y : horder.CanonicalGraphData) :
    CoefficientSpace horder.CanonicalScalarIndex :=
  ⟨fun x => y x.1 x.2, by
    apply memℓp_gen
    have hy : Summable (fun C => ‖y C‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hblocks : Summable (fun C => ∑' i : Fin (horder.clusterSize C), ‖y C i‖ ^ 2) :=
      hy.congr fun C => by simp only [PiLp.norm_sq_eq_of_L2, tsum_fintype]
    have hflat : Summable
        (fun x : horder.CanonicalScalarIndex => ‖y x.1 x.2‖ ^ 2) :=
      (summable_sigma_of_nonneg
        (f := fun x : horder.CanonicalScalarIndex => ‖y x.1 x.2‖ ^ 2)
        (fun x => sq_nonneg ‖y x.1 x.2‖)).2
        ⟨fun _ => (hasSum_fintype _).summable, hblocks⟩
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hflat⟩

/-- Reassemble scalar sigma coordinates into their original finite canonical blocks. -/
def canonicalGraphDataUnflatten
    (x : CoefficientSpace horder.CanonicalScalarIndex) : horder.CanonicalGraphData :=
  ⟨fun C => WithLp.toLp 2 (fun i => x ⟨C, i⟩), by
    apply memℓp_gen
    have hx : Summable (fun z : horder.CanonicalScalarIndex => ‖x z‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hsigma :=
      (summable_sigma_of_nonneg
        (f := fun z : horder.CanonicalScalarIndex => ‖x z‖ ^ 2)
        (fun z => sq_nonneg ‖x z‖)).mp hx
    have hblocks : Summable
        (fun C => ‖WithLp.toLp 2 (fun i : Fin (horder.clusterSize C) => x ⟨C, i⟩)‖ ^ 2) :=
      hsigma.2.congr fun C => by simp only [PiLp.norm_sq_eq_of_L2, tsum_fintype]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hblocks⟩

theorem canonicalGraphDataFlatten_norm
    (y : horder.CanonicalGraphData) :
    ‖horder.canonicalGraphDataFlatten y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hflatnorm : ‖horder.canonicalGraphDataFlatten y‖ ^ 2 =
      ∑' z : horder.CanonicalScalarIndex, ‖horder.canonicalGraphDataFlatten y z‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
        (horder.canonicalGraphDataFlatten y)
  have hblocknorm : ‖y‖ ^ 2 = ∑' C, ‖y C‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  rw [hflatnorm, hblocknorm]
  change (∑' z : horder.CanonicalScalarIndex, ‖y z.1 z.2‖ ^ 2) =
    ∑' C, ‖y C‖ ^ 2
  have hsum : Summable (fun z : horder.CanonicalScalarIndex => ‖y z.1 z.2‖ ^ 2) := by
    have hy : Summable (fun C => ‖y C‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hblocks : Summable
        (fun C => ∑' i : Fin (horder.clusterSize C), ‖y C i‖ ^ 2) :=
      hy.congr fun C => by simp only [PiLp.norm_sq_eq_of_L2, tsum_fintype]
    exact (summable_sigma_of_nonneg
      (f := fun z : horder.CanonicalScalarIndex => ‖y z.1 z.2‖ ^ 2)
      (fun z => sq_nonneg ‖y z.1 z.2‖)).2
      ⟨fun _ => (hasSum_fintype _).summable, hblocks⟩
  rw [hsum.tsum_sigma]
  apply tsum_congr
  intro C
  simp only [PiLp.norm_sq_eq_of_L2, tsum_fintype]

/-- The coordinate-preserving complex-linear isometric equivalence between the
canonical block Hilbert sum and scalar `ℓ²` on the exact dependent index. -/
def canonicalGraphDataCoefficientEquiv :
    horder.CanonicalGraphData ≃ₗᵢ[ℂ] CoefficientSpace horder.signedGrouping.Index where
  toFun := horder.canonicalGraphDataFlatten
  invFun := horder.canonicalGraphDataUnflatten
  left_inv y := by
    apply Subtype.ext
    funext C
    apply PiLp.ext
    intro i
    rfl
  right_inv x := by
    apply Subtype.ext
    funext z
    rcases z with ⟨C, i⟩
    rfl
  map_add' y z := by
    apply Subtype.ext
    funext x
    rfl
  map_smul' a y := by
    apply Subtype.ext
    funext x
    rfl
  norm_map' := horder.canonicalGraphDataFlatten_norm

/-- The equivalence preserves each original block/scalar coordinate exactly. -/
@[simp] theorem canonicalGraphDataCoefficientEquiv_apply
    (y : horder.CanonicalGraphData) (C : CanonicalClusterIndex S.signedSquareImage d)
    (i : Fin (horder.clusterSize C)) :
    horder.canonicalGraphDataCoefficientEquiv y ⟨C, i⟩ = y C i := rfl

/-- The inverse equivalence restores each scalar coordinate in its original block. -/
@[simp] theorem canonicalGraphDataCoefficientEquiv_symm_apply
    (x : CoefficientSpace horder.signedGrouping.Index)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (i : Fin (horder.clusterSize C)) :
    (horder.canonicalGraphDataCoefficientEquiv.symm x) C i = x ⟨C, i⟩ := rfl

end BoundedClusterOrder

end

end MeyerGeneralProblem
