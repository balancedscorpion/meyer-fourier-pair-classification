module

public import MeyerGeneralProblem.Distribution.LatticeOrbitResidueRows
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

/-!
# Cyclotomic reduction of residue rows

After grouping phases by their common modulus powers, distinct
powered phases separate the constraints on an entire residue.
Inside each phase class the ratios are powers of one primitive root.
The corresponding matrix ranks can be taken in its generated field.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- Distinct phases give linearly independent bilateral power sequences. -/
theorem integerPowerSum_coefficients_eq_zero_of_injective
    {ι : Type*} [Fintype ι] (c z : ι → ℂ) (hz : Function.Injective z)
    (h : integerPowerSum c z = 0) : c = 0 := by
  let e := (Fintype.equivFin ι).symm
  let phase (j : Fin (Fintype.card ι)) := z (e j)
  let V := (Matrix.vandermonde phase).transpose
  have hinj : Function.Injective V.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det V).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp e.injective)
  have hzV : V.mulVec (c ∘ e) = 0 := by
    funext n
    change (∑ j, phase j ^ n.val * c (e j)) = 0
    calc
      _ = ∑ j, c (e j) * z (e j) ^ n.val := by
        simp only [phase, mul_comm]
      _ = ∑ i, c i * z i ^ n.val := e.sum_comp fun i => c i * z i ^ n.val
      _ = 0 := by simpa only [integerPowerSum, zpow_natCast, Pi.zero_apply] using congrFun h (n.val : ℤ)
  have hzero : c ∘ e = 0 := hinj (by simpa only [Matrix.mulVec_zero] using hzV)
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  exact congrFun hzero j

/-- The finite set of powered phases. -/
def latticePhaseClasses {ι : Type*} [Fintype ι] (z : ι → ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact Finset.univ.image fun i => z i ^ p

/-- The original frequencies in one powered-phase class. -/
abbrev LatticePhaseClass {ι : Type*} [Fintype ι] (z : ι → ℂ) (p : ℕ)
    (η : latticePhaseClasses z p) :=
  {i : ι // z i ^ p = η.val}

private theorem integerPowerSum_eq_grouped_phaseClasses
    {ι : Type*} [Fintype ι] (a z : ι → ℂ) (p : ℕ) :
    haveI := Classical.decEq ι
    haveI := Classical.propDecidable
    integerPowerSum a (fun i => z i ^ p) =
      integerPowerSum (fun η : latticePhaseClasses z p => ∑ i : LatticePhaseClass z p η, a i.val)
        Subtype.val := by
  classical
  let cl (i : ι) : latticePhaseClasses z p :=
    ⟨z i ^ p, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  funext n
  unfold integerPowerSum
  rw [← Finset.sum_fiberwise Finset.univ cl (fun i => a i * (z i ^ p) ^ n)]
  apply Finset.sum_congr rfl
  intro η _
  rw [Finset.sum_mul]
  have hmem (i : ι) : i ∈ Finset.univ.filter (fun j => cl j = η) ↔ z i ^ p = η.val := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext (show (cl i).val = η.val from h)⟩
  rw [Finset.sum_subtype _ hmem]
  exact Finset.sum_congr rfl fun i _ => by rw [show z i.val ^ p = η.val from i.property]

/-- The phase ratios within each powered-phase class are distinct powers
of one primitive root, provided the original phases are distinct. -/
theorem exists_cyclotomic_indices_of_latticePhaseClasses
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (hDistinct : Function.Injective z) (p : ℕ) (hp : 0 < p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ (rep : latticePhaseClasses z p → ι)
      (k : ∀ η : latticePhaseClasses z p, LatticePhaseClass z p η → Fin p),
      (∀ η, z (rep η) ^ p = η.val) ∧
      ∀ η, Function.Injective (k η) ∧
        ∀ i, z i.val = z (rep η) * ζ ^ (k η i).val := by
  classical
  let _ : NeZero p := ⟨hp.ne'⟩
  have hrep (η : latticePhaseClasses z p) : ∃ i, z i ^ p = η.val := by
    obtain ⟨i, _, h⟩ := Finset.mem_image.mp η.property
    exact ⟨i, h⟩
  choose rep hRep using hrep
  have hex (η : latticePhaseClasses z p) (i : LatticePhaseClass z p η) :
      ∃ m : Fin p, ζ ^ m.val = z i.val / z (rep η) := by
    have hroot : (z i.val / z (rep η)) ^ p = 1 := by
      rw [div_pow, hRep η, show z i.val ^ p = η.val from i.property, div_self]
      exact (hRep η) ▸ pow_ne_zero p (hz (rep η))
    obtain ⟨m, hm, he⟩ := hζ.eq_pow_of_pow_eq_one hroot
    exact ⟨⟨m, hm⟩, he⟩
  choose k hk using hex
  refine ⟨rep, k, hRep, fun η => ?_⟩
  have he (i : LatticePhaseClass z p η) : z i.val = z (rep η) * ζ ^ (k η i).val := by
    rw [hk η i]
    field_simp [hz (rep η)]
  refine ⟨?_, he⟩
  intro i j h
  apply Subtype.ext
  apply hDistinct
  rw [he i, he j, h]

/-- On one forbidden residue, the consecutive sample equations are
equivalent to the root-of-unity equations for each powered-phase class. -/
theorem backward_powerSum_residue_iff_cyclotomic_rows
    {ι : Type*} [Fintype ι] (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (p r : ℕ) (ζ : ℂ) (rep : latticePhaseClasses z p → ι)
    (k : ∀ η : latticePhaseClasses z p, LatticePhaseClass z p η → Fin p)
    (hrep : ∀ η (i : LatticePhaseClass z p η), z i.val = z (rep η) * ζ ^ (k η i).val) :
    haveI := Classical.propDecidable
    (∀ n : Fin (Fintype.card ι),
      integerPowerSum c z ((r : ℤ) - (n.val : ℤ) * (p : ℤ)) = 0) ↔
    ∀ η : latticePhaseClasses z p,
      (∑ i : LatticePhaseClass z p η, c i.val * ζ ^ ((k η i).val * r)) = 0 := by
  classical
  let a (i : ι) := c i * z i ^ r
  let node (i : ι) := z i ^ p
  have hEval (n : ℤ) : integerPowerSum c z ((r : ℤ) + n * (p : ℤ)) =
      integerPowerSum a node n := by
    unfold integerPowerSum
    apply Finset.sum_congr rfl
    intro i _
    rw [zpow_add₀ (hz i), mul_comm n (p : ℤ), zpow_mul, zpow_natCast, zpow_natCast]
    simp only [a, node, mul_assoc]
  have hSamples :
      (∀ n : Fin (Fintype.card ι),
        integerPowerSum c z ((r : ℤ) - (n.val : ℤ) * (p : ℤ)) = 0) ↔
      integerPowerSum a node = 0 := by
    constructor
    · intro h
      apply integerPowerSum_eq_zero_of_backward_samples a node (fun i => pow_ne_zero _ (hz i))
      intro n
      rw [← hEval, neg_mul, ← sub_eq_add_neg]
      exact h n
    · intro h n
      have he := congrFun h (-(n.val : ℤ))
      rw [← hEval, neg_mul, ← sub_eq_add_neg, Pi.zero_apply] at he
      exact he
  have hblock (η : latticePhaseClasses z p) :
      (∑ i : LatticePhaseClass z p η, a i.val) =
        z (rep η) ^ r * ∑ i : LatticePhaseClass z p η, c i.val * ζ ^ ((k η i).val * r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [a]
    rw [hrep η i, mul_pow, ← pow_mul]
    ring
  rw [hSamples]
  have hGroup := integerPowerSum_eq_grouped_phaseClasses a z p
  change integerPowerSum a node = _ at hGroup
  rw [hGroup]
  constructor
  · intro h η
    have he := congrFun (integerPowerSum_coefficients_eq_zero_of_injective _ _
      Subtype.val_injective h) η
    rw [Pi.zero_apply, hblock] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (hz (rep η)))
  · intro h
    funext n
    unfold integerPowerSum
    apply Finset.sum_eq_zero
    intro η _
    change (∑ i : LatticePhaseClass z p η, a i.val) * η.val ^ n = 0
    rw [hblock η, h η, mul_zero, zero_mul]

/-- Actual residue coordinates, after multiplying each column by the
nonzero character at its orbit origin, satisfy the cyclotomic equations. -/
theorem exists_latticeOrbitResidueRows_cyclotomic
    {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ) (origin : ι → ℝ)
    (modes : List ℝ) (p : ℕ) (hp : 0 < p)
    (hModes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    haveI := Classical.propDecidable
    let z (j : Fin modes.length) := combModulationCharacter (modes.get j) w
    let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
    ∃ k : ∀ η : latticePhaseClasses z p, LatticePhaseClass z p η → Fin p,
      (∀ η, Function.Injective (k η)) ∧
      ∀ c, c ∈ LinearMap.ker (latticeOrbitResidueRows A w origin modes p) ↔
        ∀ r : ForbiddenLatticeOrbitResidue A w origin p, ∀ η : latticePhaseClasses z p,
          (∑ j : LatticePhaseClass z p η,
            c r.val.1 j.val * combModulationCharacter (modes.get j.val) (origin r.val.1) *
              ζ ^ ((k η j).val * r.val.2.val)) = 0 := by
  classical
  let z (j : Fin modes.length) := combModulationCharacter (modes.get j) w
  let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hz (j : Fin modes.length) : z j ≠ 0 :=
    norm_pos_iff.mp (by rw [show z j = _ from rfl, norm_combModulationCharacter]; norm_num)
  have hNeg (j : Fin modes.length) : combModulationCharacter (-w) (modes.get j) = (z j)⁻¹ := by
    dsimp only [z]
    rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hDistinct : Function.Injective z := by
    intro i j hij
    have he : combModulationCharacter (-w) (modes.get i) =
        combModulationCharacter (-w) (modes.get j) := by rw [hNeg i, hNeg j, hij]
    rcases lt_trichotomy i j with hl | heq | hr
    · exact ((List.pairwise_iff_get.mp hModes i j hl) he).elim
    · exact heq
    · exact ((List.pairwise_iff_get.mp hModes j i hr) he.symm).elim
  obtain ⟨rep, k, _, hk⟩ := exists_cyclotomic_indices_of_latticePhaseClasses z hz hDistinct
    p hp ζ (Complex.isPrimitiveRoot_exp p hp.ne')
  refine ⟨k, fun η => (hk η).1, fun c => ?_⟩
  let a (i : ι) (j : Fin modes.length) := c i j * combModulationCharacter (modes.get j) (origin i)
  have hEval (r : ForbiddenLatticeOrbitResidue A w origin p) (n : Fin modes.length) :
      latticeOrbitResidueRows A w origin modes p c r n =
        integerPowerSum (a r.val.1) z ((r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ)) := by
    change (∑ j, c r.val.1 j * combModulationCharacter (modes.get j)
      (origin r.val.1 + (((r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ) : ℤ) : ℝ) * w)) = _
    simp only [combModulationCharacter_on_integer_affine, integerPowerSum, a, z, mul_assoc]
  have hBlock (r : ForbiddenLatticeOrbitResidue A w origin p) :=
    backward_powerSum_residue_iff_cyclotomic_rows (a r.val.1) z hz p r.val.2.val ζ rep k
      (fun η i => (hk η).2 i)
  constructor
  · intro hc r
    apply (hBlock r).mp
    intro n
    let j : Fin modes.length := ⟨n.val, by simpa only [Fintype.card_fin] using n.isLt⟩
    have hzero := congrFun (congrFun (LinearMap.mem_ker.mp hc) r) j
    rw [hEval, Pi.zero_apply, Pi.zero_apply] at hzero
    exact hzero
  · intro h
    apply LinearMap.mem_ker.mpr
    funext r n
    let j : Fin (Fintype.card (Fin modes.length)) := ⟨n.val, by
      simpa only [Fintype.card_fin] using n.isLt⟩
    have hz := (hBlock r).mpr (h r) j
    rw [hEval, Pi.zero_apply, Pi.zero_apply]
    exact hz

/-- Matrix rank is preserved under a field embedding. The factorization
through the original range has split factors, and both splittings
transport by the coefficient map. -/
theorem matrix_rank_map_fieldHom
    {K L m n : Type*} [Field K] [Field L] [Fintype m] [Fintype n]
    (f : K →+* L) (A : Matrix m n K) :
    (A.map f).rank = A.rank := by
  classical
  let W := LinearMap.range A.mulVecLin
  let d := A.rank
  let e : W ≃ₗ[K] (Fin d → K) := (Module.finBasis K W).equivFun
  let j : (Fin d → K) →ₗ[K] (m → K) := W.subtype.comp e.symm.toLinearMap
  let p : (n → K) →ₗ[K] (Fin d → K) := e.toLinearMap.comp A.mulVecLin.rangeRestrict
  have hj : Function.Injective j := W.subtype_injective.comp e.symm.injective
  have hp : Function.Surjective p := e.surjective.comp (LinearMap.surjective_rangeRestrict _)
  let B := LinearMap.toMatrix' j
  let C := LinearMap.toMatrix' p
  have hjp : j.comp p = A.mulVecLin := by
    apply LinearMap.ext
    intro v
    change ((e.symm (e (A.mulVecLin.rangeRestrict v)) : W) : m → K) = A.mulVecLin v
    rw [e.symm_apply_apply]
    rfl
  have hA : B * C = A := by
    rw [show B * C = LinearMap.toMatrix' j * LinearMap.toMatrix' p from rfl,
      ← LinearMap.toMatrix'_comp, hjp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  obtain ⟨g, hg⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let D := LinearMap.toMatrix' g
  have hD : D * B = 1 := by
    rw [show D * B = LinearMap.toMatrix' g * LinearMap.toMatrix' j from rfl,
      ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hC : Function.Surjective C.mulVec := by
    intro v
    obtain ⟨u, hu⟩ := hp v
    exact ⟨u, by simpa only [C, LinearMap.toMatrix'_mulVec] using hu⟩
  obtain ⟨H, hH⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hC
  have hMap : A.map f = B.map f * C.map f := by
    rw [← hA, Matrix.map_mul]
  have hSplit : (D.map f * A.map f) * H.map f = 1 := by
    calc
      _ = (D.map f * B.map f) * (C.map f * H.map f) := by rw [hMap]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← Matrix.map_mul, ← Matrix.map_mul, hD, hH,
          Matrix.map_one f (map_zero f) (map_one f), one_mul]
  have hLower : d ≤ (A.map f).rank := by
    have h := (Matrix.rank_mul_le_left (D.map f * A.map f) (H.map f)).trans
      (Matrix.rank_mul_le_right (D.map f) (A.map f))
    rw [hSplit, Matrix.rank_one, Fintype.card_fin] at h
    exact h
  have hUpper : (A.map f).rank ≤ d := by
    rw [hMap]
    exact (Matrix.rank_mul_le_left (B.map f) (C.map f)).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (B.map f))
  exact le_antisymm hUpper hLower


/-- The field generated by the chosen primitive root of unity. -/
def latticeCyclotomicField (ζ : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({ζ} : Set ℂ)

/-- The exact root-of-unity matrix over the cyclotomic field. -/
def latticeCyclotomicMatrix {R C : Type*} (ζ : ℂ) (exponent : R → C → ℕ) :
    Matrix R C (latticeCyclotomicField ζ) :=
  Matrix.of fun r c =>
    (⟨ζ, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)⟩ : latticeCyclotomicField ζ) ^
      exponent r c

/-- Its rank over the cyclotomic field is exactly the complex rank. -/
theorem latticeCyclotomicMatrix_rank {R C : Type*} [Fintype R] [Fintype C]
    (ζ : ℂ) (exponent : R → C → ℕ) :
    (latticeCyclotomicMatrix ζ exponent).rank =
      (Matrix.of (fun r c => ζ ^ exponent r c)).rank := by
  let K := latticeCyclotomicField ζ
  let f := K.toSubfield.subtype
  have he : (latticeCyclotomicMatrix ζ exponent).map f =
      (Matrix.of (fun r c => ζ ^ exponent r c)) := by
    ext r c
    change f ((⟨ζ, _⟩ : K) ^ exponent r c) = ζ ^ exponent r c
    rw [map_pow]
    rfl
  rw [← he]
  exact (matrix_rank_map_fieldHom f _).symm

private def phaseGroupingEquiv {I : Type*} [Fintype I] (z : I → ℂ) (p : ℕ) :
    (I → ℂ) ≃ₗ[ℂ] (η : latticePhaseClasses z p) → LatticePhaseClass z p η → ℂ := by
  classical
  let cl (i : I) : latticePhaseClasses z p :=
    ⟨z i ^ p, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  refine
    { toFun := fun a _ i => a i.val
      invFun := fun a i => a (cl i) ⟨i, rfl⟩
      left_inv := fun _ => rfl
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  intro a
  funext η i
  obtain ⟨i, hi⟩ := i
  have he : cl i = η := Subtype.ext (show (cl i).val = η.val from hi)
  subst η
  rfl

/-- The dimension of the literal residue kernel is the sum of the
cyclotomic nullities over all orbits and powered-phase classes. -/
theorem exists_latticeOrbitResidueRows_cyclotomic_finrank
    {ι : Type*} [Fintype ι] (A : LocallyFiniteCarrier) (w : ℝ) (origin : ι → ℝ)
    (modes : List ℝ) (p : ℕ) (hp : 0 < p)
    (hModes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t)) :
    haveI := Classical.propDecidable
    let z (j : Fin modes.length) := combModulationCharacter (modes.get j) w
    let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
    let R (i : ι) := {r : Fin p // origin i + (r.val : ℝ) * w ∉ A.carrier}
    ∃ k : ∀ η : latticePhaseClasses z p, LatticePhaseClass z p η → Fin p,
      (∀ η, Function.Injective (k η)) ∧
      (∀ c, c ∈ LinearMap.ker (latticeOrbitResidueRows A w origin modes p) ↔
        ∀ r : ForbiddenLatticeOrbitResidue A w origin p, ∀ η : latticePhaseClasses z p,
          (∑ j : LatticePhaseClass z p η,
            c r.val.1 j.val * combModulationCharacter (modes.get j.val) (origin r.val.1) *
              ζ ^ ((k η j).val * r.val.2.val)) = 0) ∧
      Module.finrank ℂ (LinearMap.ker (latticeOrbitResidueRows A w origin modes p)) =
        ∑ i : ι, ∑ η : latticePhaseClasses z p,
          (Fintype.card (LatticePhaseClass z p η) -
            (latticeCyclotomicMatrix ζ
              (fun (r : R i) j => (k η j).val * r.val.val)).rank) := by
  classical
  let z (j : Fin modes.length) := combModulationCharacter (modes.get j) w
  let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  let R (i : ι) := {r : Fin p // origin i + (r.val : ℝ) * w ∉ A.carrier}
  obtain ⟨k, hki, hRows⟩ := exists_latticeOrbitResidueRows_cyclotomic A w origin modes p hp hModes
  refine ⟨k, hki, hRows, ?_⟩
  let Phase (η : latticePhaseClasses z p) := LatticePhaseClass z p η
  let K := LinearMap.ker (latticeOrbitResidueRows A w origin modes p)
  let weight (i : ι) (j : Fin modes.length) := combModulationCharacter (modes.get j) (origin i)
  have hw (i : ι) (j : Fin modes.length) : weight i j ≠ 0 :=
    norm_pos_iff.mp (by rw [show weight i j = _ from rfl, norm_combModulationCharacter]; norm_num)
  let W : (ι → Fin modes.length → ℂ) ≃ₗ[ℂ] (ι → Fin modes.length → ℂ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.piCongrRight fun j =>
      LinearEquiv.smulOfUnit (M := ℂ) (Units.mk0 (weight i j) (hw i j))
  let f := W.trans (LinearEquiv.piCongrRight fun _ : ι => phaseGroupingEquiv z p)
  let exp (i : ι) (η : latticePhaseClasses z p) (r : R i) (j : Phase η) :=
    (k η j).val * r.val.val
  let M (i : ι) (η : latticePhaseClasses z p) : Matrix (R i) (Phase η) ℂ :=
    Matrix.of fun r j => ζ ^ exp i η r j
  let B (i : ι) (η : latticePhaseClasses z p) := LinearMap.ker (M i η).mulVecLin
  have hEntry (c : ι → Fin modes.length → ℂ) (i : ι) (η : latticePhaseClasses z p) (r : R i) :
      (M i η).mulVecLin (f c i η) r =
        ∑ j : Phase η, c i j.val * weight i j.val * ζ ^ exp i η r j := by
    change (∑ j : Phase η, ζ ^ exp i η r j * (weight i j.val * c i j.val)) = _
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hMem (c : ι → Fin modes.length → ℂ) : c ∈ K ↔
      ∀ i η, f c i η ∈ B i η := by
    change c ∈ LinearMap.ker (latticeOrbitResidueRows A w origin modes p) ↔ _
    rw [hRows c]
    constructor
    · intro h i η
      apply LinearMap.mem_ker.mpr
      funext r
      rw [hEntry, Pi.zero_apply]
      exact h ⟨(i, r.val), r.property⟩ η
    · intro h r η
      let t : R r.val.1 := ⟨r.val.2, r.property⟩
      have hzero := congrFun (LinearMap.mem_ker.mp (h r.val.1 η)) t
      rw [hEntry, Pi.zero_apply] at hzero
      exact hzero
  let e : K ≃ₗ[ℂ] ((i : ι) → (η : latticePhaseClasses z p) → B i η) :=
    { toFun := fun c i η => ⟨f c i η, (hMem c).mp c.property i η⟩
      invFun := fun c => ⟨f.symm (fun i η => (c i η).val), (hMem _).mpr fun i η => by
        rw [f.apply_symm_apply]
        exact (c i η).property⟩
      left_inv := fun c => Subtype.ext (f.symm_apply_apply c.val)
      right_inv := fun c => by
        funext i η
        apply Subtype.ext
        exact congrFun (congrFun (f.apply_symm_apply (fun i η => (c i η).val)) i) η
      map_add' := fun c d => by
        funext i η
        apply Subtype.ext
        exact congrFun (congrFun (map_add f c.val d.val) i) η
      map_smul' := fun t c => by
        funext i η
        apply Subtype.ext
        exact congrFun (congrFun (map_smul f t c.val) i) η }
  have hDim := e.finrank_eq
  rw [Module.finrank_pi_fintype] at hDim
  refine hDim.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun η _ => ?_
  have h := LinearMap.finrank_range_add_finrank_ker (M i η).mulVecLin
  rw [← Matrix.rank, Module.finrank_pi] at h
  have hRank : (latticeCyclotomicMatrix ζ (exp i η)).rank = (M i η).rank :=
    latticeCyclotomicMatrix_rank ζ (exp i η)
  exact Nat.eq_sub_of_add_eq (by rw [hRank, add_comm]; exact h)

end
end MeyerGeneralProblem
