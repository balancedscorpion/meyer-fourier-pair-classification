module

public import MeyerGeneralProblem.Carrier.FoldedSquaredGap
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Ring
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-!
# Actual folded squared tails of a two-sided carrier

Independent anchors put both physical tails strictly on their respective rays
and beyond the finite node and gap exceptions. Reflecting the negative tail
reverses its index direction. Its adjacent gap therefore starts at the original
index one below the current node, not at the current node itself.

The larger-endpoint weighted gap yields a squared-gap bound with exact factor
two on both tails. No function, zero transport, analytic estimate, or symmetry of the
carrier enters this geometric construction.
-/

namespace MeyerGeneralProblem
namespace TwoSidedCarrier

open Filter

/-- Cofinality and finite boundedness give independent signed anchors, including
the preceding gap index needed by the reflected negative tail. -/
private theorem exists_foldedTail_anchors (Λ : TwoSidedCarrier)
    (Fzero Fgap : Finset ℤ) :
    ∃ Kpos Kneg : ℤ,
      (∀ n : ℕ, 0 < Λ (Kpos + (n : ℤ)) ∧
        Kpos + (n : ℤ) ∉ Fzero ∧ Kpos + (n : ℤ) ∉ Fgap) ∧
      (∀ n : ℕ, 0 < -Λ (Kneg - (n : ℤ)) ∧
        Kneg - (n : ℤ) ∉ Fzero ∧ Kneg - (n : ℤ) - 1 ∉ Fgap) := by
  obtain ⟨P, hP⟩ := eventually_atTop.mp (Λ.eventually_point_ge 1)
  obtain ⟨Q, hQ⟩ := eventually_atBot.mp (Λ.eventually_point_le (-1))
  obtain ⟨U, hU⟩ := (Fzero ∪ Fgap).bddAbove
  obtain ⟨L, hL⟩ := (Fzero ∪ Fgap).bddBelow
  have above_outside {j : ℤ} (hj : U < j) : j ∉ Fzero ∧ j ∉ Fgap := by
    constructor
    · intro hz
      have hu := hU (Finset.mem_union_left Fgap hz)
      omega
    · intro hg
      have hu := hU (Finset.mem_union_right Fzero hg)
      omega
  have below_outside {j : ℤ} (hj : j < L) : j ∉ Fzero ∧ j ∉ Fgap := by
    constructor
    · intro hz
      have hl := hL (Finset.mem_union_left Fgap hz)
      omega
    · intro hg
      have hl := hL (Finset.mem_union_right Fzero hg)
      omega
  refine ⟨max P (U + 1), min Q (L - 1), ?_, ?_⟩
  · intro n
    have hp := hP (max P (U + 1) + (n : ℤ)) (by omega)
    exact ⟨by linarith, above_outside (by omega)⟩
  · intro n
    have hq := hQ (min Q (L - 1) - (n : ℤ)) (by omega)
    exact ⟨by linarith, (below_outside (by omega)).1,
      (below_outside (by omega)).2⟩

/-- The genuine positive and reflected negative squared tails are strictly
increasing, cofinal, avoid independently supplied finite exceptions, and have
adjacent gaps at most `2 * ρ`. The displayed bounds `0 < ρ < 1 / 2`
are retained for the intended application; this pure geometric construction
itself does not need either of those two numerical restrictions. -/
theorem exists_foldedSquaredTails (Λ : TwoSidedCarrier) {ρ : ℝ}
    (_hρ0 : 0 < ρ) (_hρhalf : ρ < 1 / 2) (Fzero Fgap : Finset ℤ)
    (hgap : ∀ j, j ∉ Fgap →
      max |Λ j| |Λ (j + 1)| * (Λ (j + 1) - Λ j) ≤ ρ) :
    ∃ Kpos Kneg : ℤ,
      let tpos : ℕ → ℝ := fun n => Λ (Kpos + (n : ℤ))
      let tneg : ℕ → ℝ := fun n => -Λ (Kneg - (n : ℤ))
      (∀ n, 0 < tpos n ∧ Kpos + (n : ℤ) ∉ Fzero ∧ Kpos + (n : ℤ) ∉ Fgap) ∧
      (∀ n, 0 < tneg n ∧ Kneg - (n : ℤ) ∉ Fzero ∧
        Kneg - (n : ℤ) - 1 ∉ Fgap) ∧
      StrictMono (fun n => (tpos n) ^ 2) ∧
      Tendsto (fun n => (tpos n) ^ 2) atTop atTop ∧
      (∀ n, (tpos (n + 1)) ^ 2 - (tpos n) ^ 2 ≤ 2 * ρ) ∧
      StrictMono (fun n => (tneg n) ^ 2) ∧
      Tendsto (fun n => (tneg n) ^ 2) atTop atTop ∧
      (∀ n, (tneg (n + 1)) ^ 2 - (tneg n) ^ 2 ≤ 2 * ρ) := by
  obtain ⟨Kpos, Kneg, hp, hn⟩ := exists_foldedTail_anchors Λ Fzero Fgap
  have hcast : Tendsto (fun n : ℕ => (n : ℤ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hip : Tendsto (fun n : ℕ => Kpos + (n : ℤ)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hcast.eventually (eventually_ge_atTop (b - Kpos))] with n hnb
    omega
  have hin : Tendsto (fun n : ℕ => Kneg - (n : ℤ)) atTop atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    filter_upwards [hcast.eventually (eventually_ge_atTop (Kneg - b))] with n hnb
    omega
  have htp : Tendsto (fun n : ℕ => Λ (Kpos + (n : ℤ))) atTop atTop :=
    Λ.tendsto_atTop.comp hip
  have htn : Tendsto (fun n : ℕ => -Λ (Kneg - (n : ℤ))) atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Λ.tendsto_atBot.comp hin)
  refine ⟨Kpos, Kneg, hp, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    have hlt := Λ.point_lt_point (show Kpos + (m : ℤ) < Kpos + (n : ℤ) by omega)
    have hpos := (hp m).1
    change (Λ (Kpos + (m : ℤ))) ^ 2 < (Λ (Kpos + (n : ℤ))) ^ 2
    nlinarith
  · exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp htp
  · intro n
    have he : Kpos + ((n + 1 : ℕ) : ℤ) = Kpos + (n : ℤ) + 1 := by omega
    have hinc := signedSquare_sub_le_twice_of_weightedGap
      (Λ.point_le_point (show Kpos + (n : ℤ) ≤ Kpos + (n : ℤ) + 1 by omega))
      (Or.inr (hp n).1.le) (hgap _ (hp n).2.2)
    rw [← he, signedSquare_of_nonneg (hp (n + 1)).1.le,
      signedSquare_of_nonneg (hp n).1.le] at hinc
    exact hinc
  · intro m n hmn
    have hlt := Λ.point_lt_point (show Kneg - (n : ℤ) < Kneg - (m : ℤ) by omega)
    have hpos := (hn m).1
    change (-Λ (Kneg - (m : ℤ))) ^ 2 < (-Λ (Kneg - (n : ℤ))) ^ 2
    nlinarith
  · exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp htn
  · intro n
    have he : Kneg - ((n + 1 : ℕ) : ℤ) = Kneg - (n : ℤ) - 1 := by omega
    have hy : Λ (Kneg - (n : ℤ)) ≤ 0 := by linarith [(hn n).1]
    have hx : Λ (Kneg - ((n + 1 : ℕ) : ℤ)) ≤ 0 := by
      linarith [(hn (n + 1)).1]
    have hinc := signedSquare_sub_le_twice_of_weightedGap
      (Λ.point_le_point (show Kneg - (n : ℤ) - 1 ≤ Kneg - (n : ℤ) by omega))
      (Or.inl hy)
      (by simpa only [sub_add_cancel] using hgap _ (hn n).2.2)
    rw [← he, signedSquare_of_nonpos hy, signedSquare_of_nonpos hx] at hinc
    simpa only [neg_sq, neg_sub_neg] using hinc

end TwoSidedCarrier
end MeyerGeneralProblem
