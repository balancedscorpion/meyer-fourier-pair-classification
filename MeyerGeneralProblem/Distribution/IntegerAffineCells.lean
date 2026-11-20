module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-!
# Integer planar cells and their physical images

A strict common integer direction gives arbitrarily large square boxes
in the cell whose physical radius grows linearly in their side length.
Without such a direction, each feasible integer point belongs to one
of finitely many bounded-value fibers of a nonzero constraint.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- An integral linear form in the two coordinates of a residue lattice. -/
def integerPlaneForm (u : ℤ × ℤ) : ℤ × ℤ →+ ℤ where
  toFun x := u.1 * x.1 + u.2 * x.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring

theorem integerPlaneForm_apply (u x : ℤ × ℤ) :
    integerPlaneForm u x = u.1 * x.1 + u.2 * x.2 := rfl

/-- The lattice points satisfying the stated finite affine inequalities. -/
def integerAffineCell {ι : Type*} (u : ι → ℤ × ℤ) (c : ι → ℤ) : Set (ℤ × ℤ) :=
  {x | ∀ i, c i ≤ integerPlaneForm (u i) x}

private theorem integerPlaneForm_square_le (u : ℤ × ℤ) (n : ℕ) (p q : Fin n) :
    -(n : ℤ) * (|u.1| + |u.2|) ≤ integerPlaneForm u (p.val, q.val) := by
  have hlo (v : ℤ) (k : Fin n) : -|v| * (n : ℤ) ≤ v * (k.val : ℤ) := by
    calc
      _ ≤ -|v| * (k.val : ℤ) :=
        mul_le_mul_of_nonpos_left (by exact_mod_cast k.isLt.le) (neg_nonpos.mpr (abs_nonneg v))
      _ ≤ _ := mul_le_mul_of_nonneg_right (neg_abs_le v) (Int.natCast_nonneg _)
  rw [integerPlaneForm_apply]
  linarith [hlo u.1 p, hlo u.2 q]

private theorem abs_addHom_integerPlane_square_le (L : ℤ × ℤ →+ ℝ) (n : ℕ)
    (p q : Fin n) : |L (p.val, q.val)| ≤ (n : ℝ) * (|L (1, 0)| + |L (0, 1)|) := by
  have he : ((p.val : ℤ), (q.val : ℤ)) =
      (p.val : ℤ) • ((1, 0) : ℤ × ℤ) + (q.val : ℤ) • ((0, 1) : ℤ × ℤ) := by
    simp
  rw [he, map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  calc
    _ ≤ |((p.val : ℤ) : ℝ) * L (1, 0)| + |((q.val : ℤ) : ℝ) * L (0, 1)| :=
      abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by exact_mod_cast p.isLt.le) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast q.isLt.le) (abs_nonneg _))

/-- A strict common direction gives square boxes of all positive sizes
inside the affine cell, in centered physical intervals of linear radius. -/
theorem exists_integer_square_in_affineCell {ι : Type*} [Fintype ι]
    (u : ι → ℤ × ℤ) (c : ι → ℤ) (d : ℤ × ℤ) (hd : ∀ i, 0 < integerPlaneForm (u i) d)
    (L : ℤ × ℤ →+ ℝ) (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ o : ℤ × ℤ, ∀ p q : Fin n,
      (o.1 + (p.val : ℤ), o.2 + (q.val : ℤ)) ∈ integerAffineCell u c ∧
        |y + L (o.1 + (p.val : ℤ), o.2 + (q.val : ℤ))| ≤ C * (n : ℝ) := by
  let K : ℤ := 1 + ∑ i, (|((u i).1)| + |((u i).2)| + |c i|)
  let v : ℤ × ℤ := K • d
  let C := 1 + |y| + |L v| + |L (1, 0)| + |L (0, 1)|
  have hK : 0 ≤ K := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
      add_nonneg (add_nonneg (abs_nonneg ((u i).1)) (abs_nonneg ((u i).2))) (abs_nonneg (c i)))
    dsimp [K]
    omega
  have hKi (i : ι) : |((u i).1)| + |((u i).2)| + |c i| ≤ K := by
    have h := Finset.single_le_sum (f := fun i => |((u i).1)| + |((u i).2)| + |c i|)
      (fun j _ => by positivity) (Finset.mem_univ i)
    dsimp [K]
    omega
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn
  let o : ℤ × ℤ := (n : ℤ) • v
  have hn₀ : 0 ≤ (n : ℤ) := Int.natCast_nonneg _
  have hn₁ : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  refine ⟨o, fun p q => ?_⟩
  change o + ((p.val : ℤ), (q.val : ℤ)) ∈ integerAffineCell u c ∧
    |y + L (o + ((p.val : ℤ), (q.val : ℤ)))| ≤ C * n
  constructor
  · intro i
    rw [map_add, show integerPlaneForm (u i) o =
      (n : ℤ) * K * integerPlaneForm (u i) d by
        dsimp only [o, v]
        rw [map_zsmul, map_zsmul]
        change (n : ℤ) * (K * integerPlaneForm (u i) d) =
          (n : ℤ) * K * integerPlaneForm (u i) d
        ring]
    have hdir : 1 ≤ integerPlaneForm (u i) d := hd i
    have hstep := mul_le_mul_of_nonneg_left hdir (mul_nonneg hn₀ hK)
    have hs := integerPlaneForm_square_le (u i) n p q
    have hconst : c i ≤ (n : ℤ) * |c i| := (le_abs_self _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn₁ (abs_nonneg (c i)))
    nlinarith [mul_le_mul_of_nonneg_left (hKi i) hn₀]
  · rw [map_add, show L o = (n : ℝ) * L v by
      dsimp only [o]
      rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast]]
    have h := abs_addHom_integerPlane_square_le L n p q
    have hy : |y| ≤ (n : ℝ) * |y| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ n by exact_mod_cast hn) (abs_nonneg y)
    calc
      _ ≤ |y| + |(n : ℝ) * L v| + |L ((p.val : ℤ), (q.val : ℤ))| := by
        rw [← add_assoc]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
        dsimp [C]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- In the absence of a strict direction, each feasible lattice point
has at least one bounded constraint value. -/
theorem mem_boundedForm_fiber_of_not_exists_strict_direction {ι : Type*}
    (u : ι → ℤ × ℤ) (c : ι → ℤ) (h : ¬ ∃ d, ∀ i, 0 < integerPlaneForm (u i) d)
    {x : ℤ × ℤ} (hx : x ∈ integerAffineCell u c) :
    ∃ i, integerPlaneForm (u i) x ∈ Icc (c i) 0 := by
  have hn : ¬ ∀ i, 0 < integerPlaneForm (u i) x := fun hd => h ⟨x, hd⟩
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact ⟨i, hx i, hi⟩

/-- Each nonempty fiber of a nonzero integer planar form is an affine
translate of a cyclic subgroup of the original integer coordinates. -/
theorem exists_affineCyclic_integerPlaneForm_fiber (u : ℤ × ℤ) (hu : u ≠ 0)
    (k : ℤ) (x₀ : ℤ × ℤ) (hx₀ : integerPlaneForm u x₀ = k) :
    ∃ d : ℤ × ℤ, ∀ x, integerPlaneForm u x = k ↔ ∃ t : ℤ, x = x₀ + t • d := by
  let H := (integerPlaneForm u).ker
  have hcyc : IsAddCyclic H := by
    let C : ℤ × ℤ →+ ℤ := if u.1 = 0 then AddMonoidHom.fst ℤ ℤ else AddMonoidHom.snd ℤ ℤ
    apply isAddCyclic_of_injective (C.comp H.subtype)
    intro x y he
    apply Subtype.ext
    have hx : integerPlaneForm u (x : ℤ × ℤ) = 0 := x.property
    have hy : integerPlaneForm u (y : ℤ × ℤ) = 0 := y.property
    rw [integerPlaneForm_apply] at hx hy
    change C (x : ℤ × ℤ) = C (y : ℤ × ℤ) at he
    by_cases h : u.1 = 0
    · have hu₂ : u.2 ≠ 0 := fun h₂ => hu (Prod.ext h h₂)
      simp only [C, h, ite_true] at he
      change (x : ℤ × ℤ).1 = (y : ℤ × ℤ).1 at he
      refine Prod.ext he (mul_left_cancel₀ hu₂ ?_)
      simpa only [h, zero_mul, zero_add] using hx.trans hy.symm
    · simp only [C, h, ite_false] at he
      change (x : ℤ × ℤ).2 = (y : ℤ × ℤ).2 at he
      refine Prod.ext (mul_left_cancel₀ h ?_) he
      rw [he] at hx
      exact add_right_cancel (hx.trans hy.symm)
  let _ : IsAddCyclic H := hcyc
  obtain ⟨d, hd⟩ := exists_zsmul_surjective H
  refine ⟨d, fun x => ?_⟩
  constructor
  · intro hx
    have hdiff : x - x₀ ∈ H := by
      change integerPlaneForm u (x - x₀) = 0
      rw [map_sub, hx, hx₀, sub_self]
    obtain ⟨t, ht⟩ := hd ⟨x - x₀, hdiff⟩
    have he := congrArg (fun z : H => (z : ℤ × ℤ)) ht
    change t • (d : ℤ × ℤ) = x - x₀ at he
    exact ⟨t, by rw [he]; abel⟩
  · rintro ⟨t, rfl⟩
    have hz : integerPlaneForm u (d : ℤ × ℤ) = 0 := d.property
    rw [map_add, map_zsmul, hx₀, hz, smul_zero, add_zero]

/-- The integer points of a cell with no strict direction lie in finitely
many affine cyclic lines of its original coordinate lattice. -/
theorem exists_finite_affineCyclic_cover_of_no_strict_direction {ι : Type*} [Fintype ι]
    (u : ι → ℤ × ℤ) (c : ι → ℤ) (hu : ∀ i, u i ≠ 0)
    (h : ¬ ∃ d, ∀ i, 0 < integerPlaneForm (u i) d) :
    ∃ E : Finset ((ℤ × ℤ) × (ℤ × ℤ)), ∀ x ∈ integerAffineCell u c,
      ∃ p ∈ E, ∃ t : ℤ, x = p.1 + t • p.2 := by
  classical
  have hline (p : ι × ℤ) : ∃ a d : ℤ × ℤ, ∀ x, integerPlaneForm (u p.1) x = p.2 →
      ∃ t : ℤ, x = a + t • d := by
    by_cases hp : ∃ a, integerPlaneForm (u p.1) a = p.2
    · obtain ⟨a, ha⟩ := hp
      obtain ⟨d, hd⟩ := exists_affineCyclic_integerPlaneForm_fiber (u p.1) (hu p.1) p.2 a ha
      exact ⟨a, d, fun x hx => (hd x).mp hx⟩
    · exact ⟨0, 0, fun x hx => (hp ⟨x, hx⟩).elim⟩
  choose a d hline using hline
  let S := Finset.univ.biUnion fun i : ι => (Finset.Icc (c i) 0).image (Prod.mk i)
  refine ⟨S.image (fun p => (a p, d p)), ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_boundedForm_fiber_of_not_exists_strict_direction u c h hx
  let p : ι × ℤ := (i, integerPlaneForm (u i) x)
  have hp : p ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨p.2, Finset.mem_Icc.mpr hi, rfl⟩⟩
  exact ⟨(a p, d p), Finset.mem_image_of_mem _ hp, hline p x rfl⟩

end
end MeyerGeneralProblem
