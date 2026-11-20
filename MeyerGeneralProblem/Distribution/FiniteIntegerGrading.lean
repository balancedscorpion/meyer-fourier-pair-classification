module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Finite sign preservation by an integral grading

A basis of a finitely generated torsion-free frequency module permits
rounding a large multiple of the real weights. A finite set of strict
inequalities survives because each label has a fixed total rounding error.
-/

namespace MeyerGeneralProblem

/-- Any finite set of strictly positive frequencies remains strictly
positive under some integral grading of a finite-rank free group. -/
theorem exists_integralGrading_positive_on_finite_set
    {G : Type*} [AddCommGroup G] [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (S : Finset G) (hS : ∀ m ∈ S, 0 < L m) :
    ∃ ν : G →+ ℤ, ∀ m ∈ S, 0 < ν m := by
  classical
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := G)
  let A (m : G) := ∑ i : Fin d, |((b.repr m i : ℤ) : ℝ)|
  let B (m : G) := (A m + 1) / L m
  let t := 1 + ∑ m ∈ S, B m
  have hA (m : G) : 0 ≤ A m := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB (m : G) (hm : m ∈ S) : 0 ≤ B m := div_nonneg (by linarith [hA m]) (hS m hm).le
  let e (i : Fin d) := t * L (b i)
  let a (i : Fin d) := ⌊e i⌋
  let ν : G →ₗ[ℤ] ℤ := b.constr ℤ a
  refine ⟨ν.toAddMonoidHom, fun m hm => ?_⟩
  change 0 < ν m
  have hlarge : A m < t * L m := by
    have hle : B m ≤ t := (Finset.single_le_sum hB hm).trans (le_add_of_nonneg_left zero_le_one)
    have hh : A m + 1 ≤ t * L m := (div_le_iff₀ (hS m hm)).mp hle
    linarith
  have hs (m : G) : L m = ∑ i : Fin d, (b.repr m i : ℝ) * L (b i) := by
    have h := congrArg L (b.sum_repr m)
    rw [map_sum] at h
    simpa only [map_zsmul, zsmul_eq_mul] using h.symm
  have hν (m : G) : (ν m : ℝ) = ∑ i : Fin d, (b.repr m i : ℝ) * (a i : ℝ) := by
    change (((b.constr ℤ a) m : ℤ) : ℝ) = _
    rw [b.constr_apply_fintype ℤ a m, Int.cast_sum]
    simp only [Module.Basis.equivFun_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_id]
  have hround (i : Fin d) : |e i - (a i : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le (e i)))]
    linarith [Int.lt_floor_add_one (e i)]
  have herr : t * L m - (ν m : ℝ) ≤ A m := by
    calc
      _ = ∑ i : Fin d, (b.repr m i : ℝ) * (e i - (a i : ℝ)) := by
        rw [hν, hs m, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [e]
        ring
      _ ≤ ∑ i : Fin d, |(b.repr m i : ℝ) * (e i - (a i : ℝ))| :=
        Finset.sum_le_sum fun _ _ => le_abs_self _
      _ ≤ A m := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hround i)
  have hpos : (0 : ℝ) < (ν m : ℝ) := by linarith
  exact_mod_cast hpos


/-- A common strict extremum and a weak numerator cut are preserved on
the same integral grading of a finite frequency module. -/
theorem exists_integralGrading_preserving_extreme
    {G : Type*} [AddCommGroup G] [Module.Finite ℤ G] [Module.IsTorsionFree ℤ G]
    (L : G →+ ℝ) (hL : Function.Injective L) (P R : Finset G) (m : G)
    (hmin : ∀ x ∈ P, x ≠ m → L m < L x) (hR : ∀ x ∈ R, L m ≤ L x) :
    ∃ ν : G →+ ℤ, (∀ x ∈ P, x ≠ m → ν m < ν x) ∧ ∀ x ∈ R, ν m ≤ ν x := by
  classical
  let S := ((P ∪ R).erase m).image fun x => x - m
  have hS (d : G) (hd : d ∈ S) : 0 < L d := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hx
    have hlt : L m < L x := (Finset.mem_union.mp hm).elim
      (fun h => hmin x h hne)
      (fun h => lt_of_le_of_ne (hR x h) (fun eq => hne (hL eq.symm)))
    rw [map_sub]
    exact sub_pos.mpr hlt
  obtain ⟨ν, hν⟩ := exists_integralGrading_positive_on_finite_set L S hS
  have hcmp (x : G) (hx : x ∈ P ∪ R) (hne : x ≠ m) : ν m < ν x := by
    have h := hν (x - m) (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hne, hx⟩))
    rwa [map_sub, sub_pos] at h
  refine ⟨ν, fun x hx => hcmp x (Finset.mem_union_left _ hx), fun x hx => ?_⟩
  by_cases h : x = m
  · rw [h]
  · exact (hcmp x (Finset.mem_union_right _ hx) h).le

/-- The grading exists in the original finitely generated real spectral subgroup. -/
theorem exists_integralGrading_positive_on_finite_spectral_set
    (Γ : AddSubgroup ℝ) (hΓ : Γ.FG) (D : Finset Γ) (hD : ∀ m ∈ D, 0 < (m : ℝ)) :
    ∃ ν : Γ →+ ℤ, ∀ m ∈ D, 0 < ν m := by
  let _ : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr
    ((AddGroup.fg_iff_addSubgroup_fg Γ).mpr hΓ)
  exact exists_integralGrading_positive_on_finite_set Γ.subtype D hD

end MeyerGeneralProblem
