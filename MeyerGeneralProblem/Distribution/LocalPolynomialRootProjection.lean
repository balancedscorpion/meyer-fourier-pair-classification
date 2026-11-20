module

public import MeyerGeneralProblem.Carrier.EntireRootFreeApproximation

@[expose] public section

/-!
# Local projection of contained zero sets

An isolated zero of an entire fiber persists somewhere in a fixed
nearby disk. If the local zero set is contained in that of another
function, all nearby parameter fibers then have a common zero.
-/

namespace MeyerGeneralProblem

noncomputable section

open Metric Set
open scoped Topology

/-- A nontrivial entire fiber's zero has nearby zeros in every sufficiently
close fiber of a jointly continuous entire family. -/
theorem exists_parameter_neighborhood_with_root
    {X : Type*} [TopologicalSpace X] (P : X → ℂ → ℂ)
    (hP : Continuous (fun v : X × ℂ => P v.1 v.2))
    (hentire : ∀ x, AnalyticOnNhd ℂ (P x) univ)
    (x₀ : X) (c : ℂ) (hzero : P x₀ c = 0) (hnz : ∃ z, P x₀ z ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, ∃ z ∈ closedBall c r, P x z = 0 := by
  have hb : ∃ ε > 0, ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c r) ∧
    (∀ z ∈ closedBall c r, g z ≠ 0) ∧ ∀ z ∈ closedBall c r, ‖g z - P x₀ z‖ < ε := by
    by_contra h
    push Not at h
    exact entire_ne_zero_at_of_closedBall_approximation (P x₀) (hentire x₀)
      hnz c r hr h hzero
  obtain ⟨ε, hε, hbad⟩ := hb
  let V := {v : X × ℂ | ‖P v.1 v.2 - P x₀ v.2‖ < ε}
  have hcx : Continuous (fun v : X × ℂ => P x₀ v.2) :=
    hP.comp (continuous_const.prodMk continuous_snd)
  have hV : IsOpen V := isOpen_lt (hP.sub hcx).norm continuous_const
  have hv₀ : ({x₀} : Set X) ×ˢ closedBall c r ⊆ V := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    change x = x₀ at hx
    subst x
    simpa [V] using hε
  obtain ⟨S, T, hS, _, hS₀, hT₀, hST⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall c r) hV hv₀
  refine ⟨S, hS, hS₀ (mem_singleton x₀), ?_⟩
  intro x hx
  by_contra h
  push Not at h
  exact hbad ⟨P x, (hentire x).mono (subset_univ _), h,
    fun z hz => hST (show (x, z) ∈ S ×ˢ T from ⟨hx, hT₀ hz⟩)⟩

/-- Local containment of one zero set in another forces the projection
of their common zero set to contain a whole parameter neighborhood. -/
theorem exists_parameter_neighborhood_with_common_root
    {X : Type*} [TopologicalSpace X] (P Q : X → ℂ → ℂ)
    (hP : Continuous (fun v : X × ℂ => P v.1 v.2))
    (hentire : ∀ x, AnalyticOnNhd ℂ (P x) univ)
    (x₀ : X) (c : ℂ) (hzero : P x₀ c = 0) (hnz : ∃ z, P x₀ z ≠ 0)
    (W : Set (X × ℂ)) (hW : IsOpen W) (h₀ : (x₀, c) ∈ W)
    (hcontained : ∀ x z, (x, z) ∈ W → P x z = 0 → Q x z = 0) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      ∀ x ∈ V, ∃ z, (x, z) ∈ W ∧ P x z = 0 ∧ Q x z = 0 := by
  have hsub : ({x₀} : Set X) ×ˢ ({c} : Set ℂ) ⊆ W := by
    simpa only [Set.singleton_prod_singleton, Set.singleton_subset_iff] using h₀
  obtain ⟨S, T, hS, hT, hS₀, hT₀, hST⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_singleton hW hsub
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (hT₀ (mem_singleton c)))
  have hclosed : closedBall c (r / 2) ⊆ T :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
  obtain ⟨V, hV, hV₀, hroots⟩ := exists_parameter_neighborhood_with_root
    P hP hentire x₀ c hzero hnz (r / 2) (by positivity)
  refine ⟨V ∩ S, hV.inter hS, ⟨hV₀, hS₀ (mem_singleton x₀)⟩, ?_⟩
  rintro x ⟨hxV, hxS⟩
  obtain ⟨z, hz, he⟩ := hroots x hxV
  have hxz : (x, z) ∈ W := hST ⟨hxS, hclosed hz⟩
  exact ⟨z, hxz, he, hcontained x z hxz he⟩

/-- Any certificate expressing a parameter-only obstruction as a
combination of the two functions must vanish throughout the projected
neighborhood of local common roots. -/
theorem parameter_obstruction_eq_zero_on_neighborhood
    {X : Type*} [TopologicalSpace X] (P Q : X → ℂ → ℂ)
    (hP : Continuous (fun v : X × ℂ => P v.1 v.2))
    (hentire : ∀ x, AnalyticOnNhd ℂ (P x) univ)
    (x₀ : X) (c : ℂ) (hzero : P x₀ c = 0) (hnz : ∃ z, P x₀ z ≠ 0)
    (W : Set (X × ℂ)) (hW : IsOpen W) (h₀ : (x₀, c) ∈ W)
    (hcontained : ∀ x z, (x, z) ∈ W → P x z = 0 → Q x z = 0)
    (D : X → ℂ) (E F : X → ℂ → ℂ)
    (hD : ∀ x z, D x = E x z * P x z + F x z * Q x z) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∀ x ∈ V, D x = 0 := by
  obtain ⟨V, hV, hV₀, hroots⟩ :=
    exists_parameter_neighborhood_with_common_root P Q hP hentire x₀ c hzero hnz W hW h₀ hcontained
  refine ⟨V, hV, hV₀, fun x hx => ?_⟩
  obtain ⟨z, _, hp, hq⟩ := hroots x hx
  rw [hD x z, hp, hq, mul_zero, mul_zero, add_zero]

end

end MeyerGeneralProblem
