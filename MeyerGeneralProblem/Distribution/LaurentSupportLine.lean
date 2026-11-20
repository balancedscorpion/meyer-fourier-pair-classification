module

public import MeyerGeneralProblem.Distribution.LaurentMonomialLocalization
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

/-!
# Detecting noncollinear Laurent support

The two-coordinate witness in the quadratic obstruction detects every
support that cannot be placed in an affine cyclic subgroup. The proof
uses an injective integral coordinate on a subgroup of collinear
differences.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G ι : Type*} [AddCommGroup G]

/-- The exact two-coordinate witness required for the quadratic
Laurent-prime obstruction. -/
def LaurentHasNoncollinearSupport (p : AddMonoidAlgebra ℂ G) : Prop :=
  ∃ (e f : G →+ ℂ) (n₀ n₁ n₂ : G),
    p.coeff n₀ ≠ 0 ∧ p.coeff n₁ ≠ 0 ∧ p.coeff n₂ ≠ 0 ∧
      (e n₁ - e n₀) * (f n₂ - f n₀) - (e n₂ - e n₀) * (f n₁ - f n₀) ≠ 0

/-- If no two-coordinate witness exists, all occupied exponents lie in
one affine translate of a cyclic subgroup of the exact original module. -/
theorem exists_affineCyclic_support_of_not_noncollinear
    (b : Module.Basis ι ℤ G) (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0)
    (hline : ¬ LaurentHasNoncollinearSupport p) :
    ∃ a d : G, ∀ n ∈ p.coeff.support, ∃ k : ℤ, n = a + k • d := by
  classical
  have hp' : p.coeff ≠ 0 := fun h => hp (AddMonoidAlgebra.coeff_injective (by simpa using h))
  obtain ⟨n₀, h₀⟩ := Finsupp.support_nonempty_iff.mpr hp'
  by_cases h : ∃ n₁ ∈ p.coeff.support, n₁ ≠ n₀
  · obtain ⟨n₁, h₁, hne⟩ := h
    let z := n₁ - n₀
    have hz : z ≠ 0 := sub_ne_zero.mpr hne
    have hrepr : b.repr z ≠ 0 := fun hh => hz (b.repr.injective (by simpa using hh))
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
    let C := (b.coord i).toAddMonoidHom
    let t := C z
    have ht : t ≠ 0 := Finsupp.mem_support_iff.mp hi
    let H : AddSubgroup G :=
      { carrier := {v | C v • z = t • v}
        zero_mem' := by simp
        add_mem' := by
          intro u v hu hv
          change C u • z = t • u at hu
          change C v • z = t • v at hv
          change C (u + v) • z = t • (u + v)
          rw [map_add, add_zsmul, zsmul_add, hu, hv]
        neg_mem' := by
          intro v hv
          change C v • z = t • v at hv
          change C (-v) • z = t • (-v)
          rw [map_neg, neg_zsmul, zsmul_neg, hv] }
    let D : H →+ ℤ := C.comp H.subtype
    have hD : Function.Injective D := by
      intro u v he
      apply Subtype.ext
      apply b.repr.injective
      ext j
      have hu : C (u : G) • z = t • (u : G) := u.property
      have hv : C (v : G) • z = t • (v : G) := v.property
      have hu' := congrArg (fun x => b.repr x j) hu
      have hv' := congrArg (fun x => b.repr x j) hv
      change C (u : G) = C (v : G) at he
      simp only [map_smul, Finsupp.smul_apply, zsmul_eq_mul] at hu' hv'
      exact mul_left_cancel₀ ht (hu'.symm.trans (he.symm ▸ hv'))
    let _ : IsAddCyclic H := isAddCyclic_of_injective D hD
    obtain ⟨d, hd⟩ := exists_zsmul_surjective H
    refine ⟨n₀, d, fun n hn => ?_⟩
    let v := n - n₀
    have hv : v ∈ H := by
      let E (j : ι) : G →+ ℂ := (Int.castAddHom ℂ).comp (b.coord j).toAddMonoidHom
      have hdet (j : ι) :
          (E i n₁ - E i n₀) * (E j n - E j n₀) -
            (E i n - E i n₀) * (E j n₁ - E j n₀) = 0 := by
        by_contra hh
        exact hline ⟨E i, E j, n₀, n₁, n, Finsupp.mem_support_iff.mp h₀,
          Finsupp.mem_support_iff.mp h₁, Finsupp.mem_support_iff.mp hn, hh⟩
      change C v • z = t • v
      apply b.repr.injective
      ext j
      have he := hdet j
      rw [← map_sub, ← map_sub, ← map_sub, ← map_sub] at he
      change ((b.repr z i : ℤ) : ℂ) * ((b.repr v j : ℤ) : ℂ) -
        ((b.repr v i : ℤ) : ℂ) * ((b.repr z j : ℤ) : ℂ) = 0 at he
      have he' : b.repr z i * b.repr v j - b.repr v i * b.repr z j = 0 := by
        exact_mod_cast he
      simp only [map_smul, Finsupp.smul_apply, zsmul_eq_mul]
      exact (sub_eq_zero.mp he').symm
    obtain ⟨k, hk⟩ := hd ⟨v, hv⟩
    have he := congrArg (fun x : H => (x : G)) hk
    change k • (d : G) = n - n₀ at he
    exact ⟨k, by rw [he]; abel⟩
  · refine ⟨n₀, 0, fun n hn => ⟨0, ?_⟩⟩
    have he : n = n₀ := by
      by_contra hn'
      exact h ⟨n, hn, hn'⟩
    simp [he]

end

end MeyerGeneralProblem
