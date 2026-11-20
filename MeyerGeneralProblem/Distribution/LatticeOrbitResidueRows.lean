module

public import MeyerGeneralProblem.Distribution.BilateralCombResidues
public import MeyerGeneralProblem.Distribution.LatticeOrbitPairSpace

@[expose] public section

/-!
# Finite residue matrices for lattice partners

The rational period relation bounds the number of physical orbits and
makes each orbit mask periodic. Consecutive samples on each forbidden
residue determine the entire forbidden progression by its recurrence.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- Full affine lattices of one step are invariant under its integer shifts. -/
theorem mem_latticeOrbitUnion_add_int_mul_iff {ι : Type*} [Fintype ι]
    (w : ℝ) (origin : ι → ℝ) (x : ℝ) (n : ℤ) :
    x + (n : ℝ) * w ∈ (latticeOrbitUnion w origin).carrier ↔
      x ∈ (latticeOrbitUnion w origin).carrier := by
  rw [mem_latticeOrbitUnion, mem_latticeOrbitUnion]
  constructor
  · rintro ⟨i, k, hk⟩
    refine ⟨i, k - n, ?_⟩
    change origin i + (k : ℝ) * w = x + (n : ℝ) * w at hk
    change origin i + ((k - n : ℤ) : ℝ) * w = x
    push_cast
    linear_combination hk
  · rintro ⟨i, k, hk⟩
    refine ⟨i, k + n, ?_⟩
    change origin i + (k : ℝ) * w = x at hk
    change origin i + ((k + n : ℤ) : ℝ) * w = x + (n : ℝ) * w
    push_cast
    linear_combination hk

/-- Under the rational period relation, physical membership along an
orbit depends only on the index modulo the numerator. -/
theorem mem_latticeOrbitUnion_at_reciprocalOrbit_periodic
    {ι : Type*} [Fintype ι] (a w y : ℝ) (origin : ι → ℝ) (p q k n : ℤ)
    (h : (q : ℝ) * a = (p : ℝ) * w) :
    y + ((k + n * p : ℤ) : ℝ) * w ∈ (latticeOrbitUnion a origin).carrier ↔
      y + (k : ℝ) * w ∈ (latticeOrbitUnion a origin).carrier := by
  rw [show y + ((k + n * p : ℤ) : ℝ) * w =
      (y + (k : ℝ) * w) + ((n * q : ℤ) : ℝ) * a by
    push_cast
    linear_combination -(n : ℝ) * h]
  exact mem_latticeOrbitUnion_add_int_mul_iff a origin _ (n * q)

/-- The reciprocal orbits meeting the physical class have disjoint
representatives among the first denominator-many sites of each coset. -/
theorem exists_disjoint_latticeOrbitCover_of_rational_step {ι : Type*} [Fintype ι]
    (a w : ℝ) (origin : ι → ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (h : (q : ℝ) * a = (p : ℝ) * w) :
    ∃ (κ : Type) (f : Fintype κ), letI := f
      ∃ y : κ → ℝ,
        (latticeOrbitUnion a origin).carrier ⊆ (latticeOrbitUnion w y).carrier ∧
        (Pairwise fun i j => Disjoint (affineLatticeLine (y i) w)
          (affineLatticeLine (y j) w)) ∧
        (∀ i, y i ∈ (latticeOrbitUnion a origin).carrier) ∧
        Fintype.card κ ≤ q * Fintype.card ι := by
  classical
  let site (i : ι × Fin q) := origin i.1 + (i.2.val : ℝ) * a
  let orbits : Finset (Set ℝ) := Finset.univ.image fun i => affineLatticeLine (site i) w
  have hrep (i : orbits) : ∃ j : ι × Fin q, affineLatticeLine (site j) w = i.val := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
    exact ⟨j, hj⟩
  choose rep hrep using hrep
  let y (i : orbits) := site (rep i)
  have hy (i : orbits) : affineLatticeLine (y i) w = i.val := hrep i
  refine ⟨orbits, inferInstance, y, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, n, rfl⟩ := (mem_latticeOrbitUnion a origin x).mp hx
    let _ : NeZero q := ⟨hq.ne'⟩
    let divMod := Int.divModEquiv q
    let r := (divMod n).2
    let m := (divMod n).1
    have hn : m * (q : ℤ) + (r.val : ℤ) = n := divMod.symm_apply_apply n
    let i : orbits := ⟨affineLatticeLine (site (j, r)) w,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    apply (mem_latticeOrbitUnion w y _).mpr
    refine ⟨i, ?_⟩
    rw [hy i]
    refine ⟨m * p, ?_⟩
    change site (j, r) + ((m * p : ℤ) : ℝ) * w = origin j + (n : ℝ) * a
    rw [← hn]
    dsimp only [site]
    push_cast
    linear_combination -(m : ℝ) * h
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hx'
    apply hij
    apply Subtype.ext
    rw [← hy i, ← hy j]
    exact (affineLatticeLine_eq_of_mem x (y i) w hx).symm.trans
      (affineLatticeLine_eq_of_mem x (y j) w hx')
  · intro i
    exact (mem_latticeOrbitUnion a origin _).mpr
      ⟨(rep i).1, ((rep i).2.val : ℤ), by simp [y, site]⟩
  · rw [Fintype.card_coe]
    calc
      orbits.card ≤ (Finset.univ : Finset (ι × Fin q)).card := Finset.card_image_le
      _ = q * Fintype.card ι := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- A forbidden residue of an orbit with periodic physical incidence. -/
def ForbiddenLatticeOrbitResidue {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (p : ℕ) :=
  {j : ι × Fin p // origin j.1 + (j.2.val : ℝ) * w ∉ A.carrier}

/-- On each forbidden residue, sample the backward consecutive values
of the character sum along the residue progression. -/
def latticeOrbitResidueRows {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (p : ℕ) :
    (ι → Fin modes.length → ℂ) →ₗ[ℂ]
      (ForbiddenLatticeOrbitResidue A w origin p → Fin modes.length → ℂ) where
  toFun c r n := ∑ j, c r.val.1 j * combModulationCharacter (modes.get j)
    (origin r.val.1 + (((r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ) : ℤ) : ℝ) * w)
  map_add' c d := by
    funext r n
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext r n
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Finset.mul_sum, RingHom.id_apply]

/-- Every forbidden site equation follows from a finite set of
samples, even when powers of several original phases coincide. -/
theorem ker_latticeOrbitResidueRows {ι : Type*} (A : LocallyFiniteCarrier) (w : ℝ)
    (origin : ι → ℝ) (modes : List ℝ) (p : ℕ) (hp : 0 < p)
    (hperiod : ∀ (i : ι) (k n : ℤ),
      origin i + ((k + n * (p : ℤ) : ℤ) : ℝ) * w ∈ A.carrier ↔
        origin i + (k : ℝ) * w ∈ A.carrier) :
    LinearMap.ker (latticeOrbitResidueRows A w origin modes p) =
      LinearMap.ker (latticeOrbitRestrictionRows A w origin modes) := by
  ext c
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    funext x
    let _ : NeZero p := ⟨hp.ne'⟩
    let divMod := Int.divModEquiv p
    let i := x.val.1
    let r := (divMod x.val.2).2
    let n := (divMod x.val.2).1
    have hdiv : (r.val : ℤ) + n * (p : ℤ) = x.val.2 := by
      rw [add_comm]
      exact divMod.symm_apply_apply x.val.2
    have hr : origin i + (r.val : ℝ) * w ∉ A.carrier := by
      intro hmem
      have hr' : origin i + ((r.val : ℤ) : ℝ) * w ∈ A.carrier := by exact_mod_cast hmem
      have he := (hperiod i (r.val : ℤ) n).mpr hr'
      rw [hdiv] at he
      exact x.property he
    let y := origin i + (r.val : ℝ) * w
    let a (j : Fin modes.length) := c i j * combModulationCharacter (modes.get j) y
    let z (j : Fin modes.length) := combModulationCharacter (modes.get j) ((p : ℝ) * w)
    have hz (j : Fin modes.length) : z j ≠ 0 :=
      norm_pos_iff.mp (by rw [show z j = _ from rfl, norm_combModulationCharacter]; norm_num)
    have hEval (k : ℤ) : integerPowerSum a z k = ∑ j, c i j * combModulationCharacter (modes.get j)
        (origin i + (((r.val : ℤ) + k * (p : ℤ) : ℤ) : ℝ) * w) := by
      rw [show origin i + (((r.val : ℤ) + k * (p : ℤ) : ℤ) : ℝ) * w =
          y + (k : ℝ) * ((p : ℝ) * w) by dsimp only [y]; push_cast; ring]
      simp only [integerPowerSum, combModulationCharacter_on_integer_affine, a, z, mul_assoc]
    let site : ForbiddenLatticeOrbitResidue A w origin p := ⟨(i, r), hr⟩
    have hsample (m : Fin modes.length) : integerPowerSum a z (-(m.val : ℤ)) = 0 := by
      rw [hEval, neg_mul, ← sub_eq_add_neg]
      exact congrFun (congrFun h site) m
    have hzero := congrFun (integerPowerSum_eq_zero_of_backward_samples a z hz
      (fun m => hsample ⟨m.val, by simpa only [Fintype.card_fin] using m.isLt⟩)) n
    rw [hEval, hdiv, Pi.zero_apply] at hzero
    rw [latticeOrbitRestrictionRows_apply, Pi.zero_apply]
    exact hzero
  · intro h
    funext r n
    let k := (r.val.2.val : ℤ) - (n.val : ℤ) * (p : ℤ)
    have hk : origin r.val.1 + (k : ℝ) * w ∉ A.carrier := by
      intro hmem
      have ht : k = (r.val.2.val : ℤ) + (-(n.val : ℤ)) * (p : ℤ) := by
        simp [k, sub_eq_add_neg]
      rw [ht] at hmem
      have hbase := (hperiod r.val.1 (r.val.2.val : ℤ) (-(n.val : ℤ))).mp hmem
      apply r.property
      exact_mod_cast hbase
    exact congrFun h (⟨(r.val.1, k), hk⟩ : ForbiddenLatticeOrbitSite A w origin)

/-- The dimension of the entire paired-class space is the number of
orbit coefficients minus the rank of the finite forbidden rows. -/
theorem latticeOrbitPair_finrank_add_residueRows_rank
    {ι : Type*} [Fintype ι] (A : LocallyFiniteCarrier) (w : ℝ) (hw : 0 < w)
    (origin : ι → ℝ) (hA : A.carrier ⊆ (latticeOrbitUnion w origin).carrier)
    (hdisj : Pairwise fun i j => Disjoint (affineLatticeLine (origin i) w)
      (affineLatticeLine (origin j) w))
    (modes : List ℝ)
    (hmodes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (p : ℕ) (hp : 0 < p) (hperiod : ∀ (i : ι) (k n : ℤ),
      origin i + ((k + n * (p : ℤ) : ℤ) : ℝ) * w ∈ A.carrier ↔
        origin i + (k : ℝ) * w ∈ A.carrier) :
    Module.finrank ℂ (DistributionalMeyerPairSpace A (latticeOrbitUnion w⁻¹ modes.get)) +
      Module.finrank ℂ (LinearMap.range (latticeOrbitResidueRows A w origin modes p)) =
        Fintype.card ι * modes.length := by
  obtain ⟨e, _⟩ := exists_latticeOrbitPairEquiv A w hw origin hA hdisj modes hmodes
  have h := LinearMap.finrank_range_add_finrank_ker (latticeOrbitResidueRows A w origin modes p)
  rw [ker_latticeOrbitResidueRows A w origin modes p hp hperiod, e.finrank_eq,
    Module.finrank_pi_fintype] at h
  simpa [Module.finrank_fin_fun, add_comm] using h

/-- A paired class with a rational period relation has its complete
finite residue matrix and a synthesis equivalence on the original records. -/
theorem exists_pairedLatticeClass_residueEquiv
    {ι : Type*} [Fintype ι] (a w : ℝ) (hw : 0 < w) (origin : ι → ℝ)
    (modes : List ℝ)
    (hmodes : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : (q : ℝ) * a = (p : ℝ) * w) :
    ∃ (κ : Type) (f : Fintype κ), letI := f
      ∃ y : κ → ℝ, Fintype.card κ ≤ q * Fintype.card ι ∧
        (∀ i, y i ∈ (latticeOrbitUnion a origin).carrier) ∧
        (latticeOrbitUnion a origin).carrier ⊆ (latticeOrbitUnion w y).carrier ∧
        (Pairwise fun i j => Disjoint (affineLatticeLine (y i) w)
          (affineLatticeLine (y j) w)) ∧
        ∃ e : LinearMap.ker (latticeOrbitResidueRows (latticeOrbitUnion a origin) w y modes p)
          ≃ₗ[ℂ] DistributionalMeyerPairSpace (latticeOrbitUnion a origin)
            (latticeOrbitUnion w⁻¹ modes.get),
          ∀ c, (e c : TemperedDistribution ℝ ℂ) = latticeOrbitSynthesis w hw y modes c := by
  obtain ⟨κ, f, y, hcover, hdisj, hCenter, hcard⟩ :=
    exists_disjoint_latticeOrbitCover_of_rational_step a w origin (p : ℤ) q hq (by exact_mod_cast h)
  let _ := f
  let A := latticeOrbitUnion a origin
  have hperiod (i : κ) (k n : ℤ) :
      y i + ((k + n * (p : ℤ) : ℤ) : ℝ) * w ∈ A.carrier ↔
        y i + (k : ℝ) * w ∈ A.carrier :=
    mem_latticeOrbitUnion_at_reciprocalOrbit_periodic a w (y i) origin (p : ℤ) (q : ℤ) k n
      (by exact_mod_cast h)
  obtain ⟨e, he⟩ := exists_latticeOrbitPairEquiv A w hw y hcover hdisj modes hmodes
  let eRows := LinearEquiv.ofEq _ _ (ker_latticeOrbitResidueRows A w y modes p hp hperiod)
  refine ⟨κ, f, y, hcard, hCenter, hcover, hdisj, eRows.trans e, fun c => ?_⟩
  change (e (eRows c) : TemperedDistribution ℝ ℂ) = _
  rw [he]
  rfl

end
end MeyerGeneralProblem
