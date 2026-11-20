module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Simultaneous avoidance of countably many cancellation equations

The argument takes place in a finite complex coefficient space, not in an
unspecified topology on a space of measures. The row index can encode both
physical and Fourier atoms. The empty family and identically zero rows are
handled explicitly by `exists_generic_linearCombination`.
-/

namespace MeyerGeneralProblem.UniformDiscrete

open scoped BigOperators Topology

noncomputable section

/-- A countable family of nonzero linear forms on a finite complex
coordinate space has a simultaneous nonzero value. -/
theorem exists_nonzero_rows {I J : Type*} [Countable I] [Fintype J]
    (row : I → (J → ℂ) →ₗ[ℂ] ℂ) (hne : ∀ i, row i ≠ 0) :
    ∃ t : J → ℂ, ∀ i, row i t ≠ 0 := by
  classical
  let U : I → Set (J → ℂ) := fun i => (LinearMap.ker (row i) : Set (J → ℂ))ᶜ
  have ho : ∀ i, IsOpen (U i) := by
    intro i
    change IsOpen {t : J → ℂ | row i t ≠ 0}
    exact isOpen_ne_fun (row i).continuous_of_finiteDimensional continuous_const
  have hd : ∀ i, Dense (U i) := by
    intro i
    apply interior_eq_empty_iff_dense_compl.mp
    by_contra h
    have ht : LinearMap.ker (row i) = ⊤ :=
      Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr h)
    apply hne i
    apply LinearMap.ext
    intro t
    have hm : t ∈ LinearMap.ker (row i) := by rw [ht]; trivial
    exact hm
  obtain ⟨t, ht⟩ := (dense_iInter_of_isOpen ho hd).nonempty
  refine ⟨t, fun i => ?_⟩
  exact Set.mem_iInter.mp ht i

/-- A linear combination whose coefficients are the coordinates of a
finite function space. -/
def finiteCombination {J V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℂ V] (v : J → V) : (J → ℂ) →ₗ[ℂ] V where
  toFun t := ∑ j, t j • v j
  map_add' := by
    intro s t
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c t
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- A single finite linear combination has exactly the union of the
nonzero row coordinates of the given family. Taking a disjoint union of
physical and spectral row indices gives simultaneous support preservation.
No linear independence of the family is needed. -/
theorem exists_generic_linearCombination {I J V : Type*}
    [Countable I] [Fintype J] [AddCommGroup V] [Module ℂ V]
    (row : I → V →ₗ[ℂ] ℂ) (v : J → V) :
    ∃ t : J → ℂ, ∀ i,
      row i (finiteCombination v t) ≠ 0 ↔ ∃ j, row i (v j) ≠ 0 := by
  classical
  let A : Set I := {i | ∃ j, row i (v j) ≠ 0}
  let r : A → (J → ℂ) →ₗ[ℂ] ℂ := fun i => (row i).comp (finiteCombination v)
  have hr : ∀ i, r i ≠ 0 := by
    intro i hzero
    obtain ⟨j, hj⟩ := i.property
    apply hj
    have h := congrArg (fun L : (J → ℂ) →ₗ[ℂ] ℂ => L (Pi.single j 1)) hzero
    simpa [r, finiteCombination] using h
  obtain ⟨t, ht⟩ := exists_nonzero_rows r hr
  refine ⟨t, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    by_contra h
    have hz : ∀ j, row i (v j) = 0 := by simpa only [not_exists, not_not] using h
    apply hi
    change row i (∑ j, t j • v j) = 0
    simp only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero]
  · intro hi
    exact ht ⟨i, hi⟩

end

end MeyerGeneralProblem.UniformDiscrete
