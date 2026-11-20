module

public import MeyerGeneralProblem.Sampling.CanonicalGroupedRiesz

@[expose] public section

/-!
# Exact finitely supported canonical grouped Riesz inequalities

Each finite coefficient vector is zero-filled on every prefix coordinate of
its touched whole groups. The finite group enumeration is injective, and both
coefficient energy and grouped exponential synthesis are unchanged.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Finset

/-- Completing touched groups by zero coefficients does not change any
finitely supported sum whose summand vanishes at coefficient zero. -/
theorem finsupp_sum_eq_sum_touched_groups {κ M : Type*} [DecidableEq κ]
    [AddCommMonoid M] (size : κ → ℕ) (c : (Σ C, Fin (size C)) →₀ ℂ)
    (f : (Σ C, Fin (size C)) → ℂ → M) (hf : ∀ x, f x 0=0) :
    c.sum f = ∑ C ∈ c.support.image Sigma.fst, ∑ j, f ⟨C,j⟩ (c ⟨C,j⟩) := by
  classical
  let U := (c.support.image Sigma.fst).sigma (fun C => (univ : Finset (Fin (size C))))
  have hsub : c.support ⊆ U := by
    intro x hx
    exact mem_sigma.mpr ⟨mem_image_of_mem _ hx,mem_univ _⟩
  calc
    c.sum f = ∑ x ∈ U, f x (c x) := by
      apply sum_subset hsub
      intro x _hx hnot
      rw [Finsupp.notMem_support_iff.mp hnot,hf]
    _ = _ := by simp only [U,sum_sigma]

/-- The genuine canonical Riesz bounds apply to every finitely supported
dependent coordinate vector, without an unspoken finite-block condition. -/
theorem canonicalGrouping_groupedExponential_finsupp_riesz
    (S : LocallyFiniteCarrier) {q : ℕ} {d W : ℝ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2*W)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ c : (Σ C : CanonicalClusterIndex S d, Fin (horder.clusterSize C)) →₀ ℂ,
        A*(c.sum fun _ z => ‖z‖^2) ≤
          ∫ t : ℝ in Set.Icc (-W) W,
            ‖c.sum (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t)‖^2 ∧
        (∫ t : ℝ in Set.Icc (-W) W,
            ‖c.sum (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t)‖^2) ≤
          B*(c.sum fun _ z => ‖z‖^2) := by
  classical
  obtain ⟨A,B,hA,hB,hbounds⟩ := groupedExponential_isRieszSequence S horder hd hW hS
  refine ⟨A,B,hA,hB,?_⟩
  intro c
  let groups := c.support.image Sigma.fst
  let e := (Fintype.equivFin groups).symm
  let emb : Fin (Fintype.card groups) ↪ CanonicalClusterIndex S d :=
    ⟨fun g => (e g).val,Subtype.val_injective.comp e.injective⟩
  have hsum {M : Type} [AddCommMonoid M]
      (f : (Σ C : CanonicalClusterIndex S d, Fin (horder.clusterSize C)) → ℂ → M)
      (hf : ∀ x, f x 0=0) :
      c.sum f = ∑ g, ∑ j, f ⟨emb g,j⟩ (c ⟨emb g,j⟩) := by
    rw [finsupp_sum_eq_sum_touched_groups _ c f hf]
    change (∑ C ∈ groups, ∑ j, f ⟨C,j⟩ (c ⟨C,j⟩)) = _
    rw [← Finset.sum_coe_sort groups]
    exact (e.sum_comp (fun C : groups => ∑ j, f ⟨C.val,j⟩ (c ⟨C.val,j⟩))).symm
  have henergy := hsum (fun _ z => ‖z‖^2) (by intro x; simp)
  have hpoly (t : ℝ) := hsum
    (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t) (by intro x; simp)
  simp_rw [henergy,hpoly]
  exact hbounds _ emb (fun g j => c ⟨emb g,j⟩)

/-- Weakest downstream canonical lower interface, with its positive constant
chosen before the arbitrary finite coefficient support and internal gaps. -/
theorem canonicalGrouping_groupedExponential_finsupp_lower
    (S : LocallyFiniteCarrier) {q : ℕ} {d W : ℝ}
    (horder : BoundedClusterOrder S d q) (hd : 0 < d) (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2*W)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ c : (Σ C : CanonicalClusterIndex S d, Fin (horder.clusterSize C)) →₀ ℂ,
        A*(c.sum fun _ z => ‖z‖^2) ≤
          ∫ t : ℝ in Set.Icc (-W) W,
            ‖c.sum (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t)‖^2 := by
  obtain ⟨A,B,hA,_hB,hbounds⟩ := canonicalGrouping_groupedExponential_finsupp_riesz S horder hd hW hS
  exact ⟨A,hA,fun c => (hbounds c).1⟩

end

end MeyerGeneralProblem
