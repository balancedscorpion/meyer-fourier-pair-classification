module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import MeyerGeneralProblem.Distribution.IntegerAffineCells

@[expose] public section

/-!
# Common integer coordinates for a rational span of quadrants

Clearing rational denominators embeds the original lattices in one
integer plane. A positive common multiple of the triangular lattice
determinants gives a sublattice with an exact lift into every source.
Neither extra atoms nor uniqueness between different sources is assumed.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators

/-- The additive map with the indicated columns on the integer plane. -/
def integerPlaneMap {G : Type*} [AddCommGroup G] (a b : G) : ℤ × ℤ →+ G where
  toFun p := p.1 • a + p.2 • b
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, add_zsmul]; abel

theorem integerPlaneMap_apply {G : Type*} [AddCommGroup G] (a b : G) (p : ℤ × ℤ) :
    integerPlaneMap a b p = p.1 • a + p.2 • b := rfl

theorem integerPlaneMap_real_apply (a b : ℝ) (p : ℤ × ℤ) :
    integerPlaneMap a b p = (p.1 : ℝ) * a + (p.2 : ℝ) * b := by
  rw [integerPlaneMap_apply, zsmul_eq_mul, zsmul_eq_mul]

private theorem integerPlaneMap_map_apply {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : G →+ H) (a b : G) (p : ℤ × ℤ) :
    L (integerPlaneMap a b p) = integerPlaneMap (L a) (L b) p := by
  rw [integerPlaneMap_apply, map_add, map_zsmul, map_zsmul, integerPlaneMap_apply]

/-- One common plane, the original lattice maps into it, and exact
integer lifts of a uniform finite-index sublattice into every source. -/
structure CommonQuadrantCoordinates {ι : Type*} (a : ι → ℝ) (w : ℝ) where
  /-- The map from common integer coordinates to real sites. -/
  grid : ℤ × ℤ →+ ℝ
  grid_injective : Function.Injective grid
  /-- The embedding of each source lattice into the common integer grid. -/
  source : ι → (ℤ × ℤ →+ ℤ × ℤ)
  source_injective : ∀ i, Function.Injective (source i)
  source_location : ∀ i p, grid (source i p) = integerPlaneMap (a i) w p
  /-- The common positive scale whose multiples lie in every source lattice. -/
  modulus : ℕ
  modulus_pos : 0 < modulus
  /-- The source coordinates lifting each point of the scaled common grid. -/
  lift : ι → (ℤ × ℤ →+ ℤ × ℤ)
  source_lift : ∀ i p, source i (lift i p) = (modulus : ℤ) • p

private theorem exists_integer_of_rat_den_dvd (N : ℕ) (r : ℚ) (h : r.den ∣ N) :
    ∃ u : ℤ, (u : ℝ) = (N : ℝ) * (r : ℝ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨r.num * (k : ℤ), ?_⟩
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [Rat.cast_def, hk]
  push_cast
  field_simp

private theorem triangular_lattice_injective (u v D : ℤ) (hu : u ≠ 0) (hD : D ≠ 0) :
    Function.Injective (integerPlaneMap (u, v) (0, D)) := by
  intro p q he
  have h₁ := congrArg Prod.fst he
  change p.1 * u + p.2 * 0 = q.1 * u + q.2 * 0 at h₁
  have hx : p.1 = q.1 := mul_right_cancel₀ hu (by simpa only [mul_zero, add_zero] using h₁)
  have h₂ := congrArg Prod.snd he
  change p.1 * v + p.2 * D = q.1 * v + q.2 * D at h₂
  rw [hx] at h₂
  exact Prod.ext hx (mul_right_cancel₀ hD (add_left_cancel h₂))

private theorem triangular_lattice_lift (u v D k M : ℤ) (hM : M = D * u * k)
    (p : ℤ × ℤ) :
    integerPlaneMap (u, v) (0, D)
      (integerPlaneMap (D * k, -v * k) (0, u * k) p) = M • p := by
  apply Prod.ext
  · change (p.1 * (D * k) + p.2 * 0) * u + (p.1 * (-v * k) + p.2 * (u * k)) * 0 =
      M * p.1
    rw [hM]
    ring
  · change (p.1 * (D * k) + p.2 * 0) * v + (p.1 * (-v * k) + p.2 * (u * k)) * D =
      M * p.2
    rw [hM]
    ring

/-- A finite family with the same rational span as the reference pair
admits common residue coordinates by clearing the actual denominators. -/
theorem nonempty_commonQuadrantCoordinates_of_rat_span {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (b w : ℝ)
    (hbw : Function.Injective (integerPlaneMap b w))
    (hspan : ∀ i, ∃ r t : ℚ, r ≠ 0 ∧ a i = (r : ℝ) * b + (t : ℝ) * w) :
    Nonempty (CommonQuadrantCoordinates a w) := by
  classical
  choose r t hr ht using hspan
  let D : ℕ := ∏ i, (r i).den * (t i).den
  have hD : 0 < D := Finset.prod_pos fun i _ => Nat.mul_pos (r i).den_pos (t i).den_pos
  have hDℤ : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDℝ : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hdiv (i : ι) : (r i).den * (t i).den ∣ D :=
    Finset.dvd_prod_of_mem (fun i => (r i).den * (t i).den) (Finset.mem_univ i)
  choose u hu using fun i =>
    exists_integer_of_rat_den_dvd D (r i) ((dvd_mul_right _ _).trans (hdiv i))
  choose v hv using fun i =>
    exists_integer_of_rat_den_dvd D (t i) ((dvd_mul_left _ _).trans (hdiv i))
  have hu₀ (i : ι) : u i ≠ 0 := by
    intro he
    have hrℝ : (r i : ℝ) ≠ 0 := by exact_mod_cast hr i
    exact (mul_ne_zero hDℝ hrℝ) ((hu i).symm.trans (by rw [he, Int.cast_zero]))
  let grid := integerPlaneMap (b / D) (w / D)
  have hgrid (p : ℤ × ℤ) : (D : ℝ) * grid p = integerPlaneMap b w p := by
    simp only [grid, integerPlaneMap_real_apply]
    field_simp
  have hgi : Function.Injective grid := by
    intro p q he
    apply hbw
    rw [← hgrid p, ← hgrid q, he]
  let source (i : ι) := integerPlaneMap (u i, v i) (0, (D : ℤ))
  have hsource (i : ι) (p : ℤ × ℤ) : grid (source i p) = integerPlaneMap (a i) w p := by
    have h₁ : grid (u i, v i) = a i := by
      simp only [grid, integerPlaneMap_real_apply, hu, hv, ht]
      field_simp
    have h₂ : grid (0, (D : ℤ)) = w := by
      simp only [grid, integerPlaneMap_real_apply, Int.cast_zero, zero_mul, zero_add, Int.cast_natCast]
      field_simp
    rw [show source i p = integerPlaneMap (u i, v i) (0, (D : ℤ)) p from rfl,
      integerPlaneMap_map_apply, h₁, h₂]
  let M : ℕ := ∏ i, ((D : ℤ) * u i).natAbs
  have hM : 0 < M := Finset.prod_pos fun i _ => Int.natAbs_pos.mpr (mul_ne_zero hDℤ (hu₀ i))
  have hmul (i : ι) : (D : ℤ) * u i ∣ (M : ℤ) :=
    Int.dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun j => ((D : ℤ) * u j).natAbs) (Finset.mem_univ i))
  choose k hk using hmul
  let lift (i : ι) := integerPlaneMap ((D : ℤ) * k i, -v i * k i) (0, u i * k i)
  refine ⟨⟨grid, hgi, source, fun i => triangular_lattice_injective _ _ _ (hu₀ i) hDℤ,
    hsource, M, hM, lift, ?_⟩⟩
  intro i p
  exact triangular_lattice_lift (u i) (v i) D (k i) M (hk i) p

/-- Lift of a residue-cell direction in the original physical coordinates. -/
theorem CommonQuadrantCoordinates.lift_location {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) (i : ι) (p : ℤ × ℤ) :
    integerPlaneMap (a i) w (C.lift i p) = C.grid ((C.modulus : ℤ) • p) := by
  rw [← C.source_location i, C.source_lift]

/-- The original physical lattice of each source still has unique indices. -/
theorem CommonQuadrantCoordinates.location_injective {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) (i : ι) :
    Function.Injective (integerPlaneMap (a i) w) := by
  intro p q he
  apply C.source_injective i
  exact C.grid_injective (by rw [C.source_location, C.source_location, he])

/-- The finite residue coordinates cover every point of the common grid. -/
theorem exists_integerPlane_residue (N : ℕ) (hN : 0 < N) (p : ℤ × ℤ) :
    ∃ r : Fin N × Fin N, ∃ k : ℤ × ℤ,
      p = ((r.1.val : ℤ), (r.2.val : ℤ)) + (N : ℤ) • k := by
  let _ : NeZero N := ⟨hN.ne'⟩
  let e := Int.divModEquiv N
  refine ⟨((e p.1).2, (e p.2).2), ((e p.1).1, (e p.2).1), ?_⟩
  have he (z : ℤ) : (e z).1 * (N : ℤ) + ((e z).2.val : ℤ) = z := e.symm_apply_apply z
  apply Prod.ext
  · change p.1 = ((e p.1).2.val : ℤ) + (N : ℤ) * (e p.1).1
    simpa only [add_comm, mul_comm] using (he p.1).symm
  · change p.2 = ((e p.2).2.val : ℤ) + (N : ℤ) * (e p.2).1
    simpa only [add_comm, mul_comm] using (he p.2).symm

/-- The physical direction homomorphism on a single residue coset. -/
def CommonQuadrantCoordinates.residueDirection {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) : ℤ × ℤ →+ ℝ where
  toFun p := C.grid ((C.modulus : ℤ) • p)
  map_zero' := by rw [smul_zero, map_zero]
  map_add' p q := by rw [smul_add, map_add]

theorem CommonQuadrantCoordinates.residueDirection_injective {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) : Function.Injective C.residueDirection := by
  intro p q he
  have heq : (C.modulus : ℤ) • p = (C.modulus : ℤ) • q := C.grid_injective he
  have hn : (C.modulus : ℤ) ≠ 0 := by exact_mod_cast C.modulus_pos.ne'
  apply Prod.ext
  · have hf := congrArg Prod.fst heq
    change (C.modulus : ℤ) * p.1 = (C.modulus : ℤ) * q.1 at hf
    exact mul_left_cancel₀ hn hf
  · have hs := congrArg Prod.snd heq
    change (C.modulus : ℤ) * p.2 = (C.modulus : ℤ) * q.2 at hs
    exact mul_left_cancel₀ hn hs

/-- One index in the original source at the residue origin determines
the exact affine integer indices at all sites of that residue. -/
theorem CommonQuadrantCoordinates.index_eq_add_lift {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) (i : ι) (y x : ℝ) (p₀ p k : ℤ × ℤ)
    (h₀ : y + integerPlaneMap (a i) w p₀ = x) :
    y + integerPlaneMap (a i) w p = x + C.residueDirection k ↔ p = p₀ + C.lift i k := by
  have he : y + integerPlaneMap (a i) w (p₀ + C.lift i k) = x + C.residueDirection k := by
    rw [map_add, C.lift_location, ← add_assoc, h₀]
    rfl
  rw [← he]
  exact ⟨fun h => C.location_injective i (add_left_cancel h), fun h => by rw [h]⟩

/-- Membership in an original lattice is constant throughout one
residue, including the case in which the whole residue is absent. -/
theorem CommonQuadrantCoordinates.exists_index_iff_at_origin {ι : Type*} {a : ι → ℝ} {w : ℝ}
    (C : CommonQuadrantCoordinates a w) (i : ι) (y x : ℝ) (k : ℤ × ℤ) :
    (∃ p, y + integerPlaneMap (a i) w p = x + C.residueDirection k) ↔
      ∃ p₀, y + integerPlaneMap (a i) w p₀ = x := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p - C.lift i k, ?_⟩
    rw [map_sub, C.lift_location, ← add_sub_assoc, hp]
    exact add_sub_cancel_right _ _
  · rintro ⟨p₀, h₀⟩
    exact ⟨p₀ + C.lift i k, (C.index_eq_add_lift i y x p₀ _ k h₀).mpr rfl⟩

/-- Adding denominators keeps the common physical grid inside the
rational span of every participating source. -/
theorem CommonQuadrantCoordinates.exists_rat_grid_coordinates {ι : Type*}
    {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w) (i : ι) (p : ℤ × ℤ) :
    ∃ r t : ℚ, C.grid p = (r : ℝ) * a i + (t : ℝ) * w := by
  have hM : (C.modulus : ℝ) ≠ 0 := by exact_mod_cast C.modulus_pos.ne'
  refine ⟨((C.lift i p).1 : ℚ) / C.modulus, ((C.lift i p).2 : ℚ) / C.modulus, ?_⟩
  have hl := C.lift_location i p
  rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast, integerPlaneMap_real_apply] at hl
  push_cast
  field_simp
  linarith only [hl]

/-- Every site of an affine common grid is represented by one of its
finite residue origins and an exact physical direction. -/
theorem CommonQuadrantCoordinates.exists_residue_location {ι : Type*}
    {a : ι → ℝ} {w : ℝ} (C : CommonQuadrantCoordinates a w) (y : ℝ) (p : ℤ × ℤ) :
    ∃ r : Fin C.modulus × Fin C.modulus, ∃ k : ℤ × ℤ,
      y + C.grid p = (y + C.grid ((r.1.val : ℤ), (r.2.val : ℤ))) + C.residueDirection k := by
  obtain ⟨r, k, hk⟩ := exists_integerPlane_residue C.modulus C.modulus_pos p
  refine ⟨r, k, ?_⟩
  rw [hk, map_add, ← add_assoc]
  rfl

end
end MeyerGeneralProblem
