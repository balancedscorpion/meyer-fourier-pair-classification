module

public import MeyerGeneralProblem.Carrier.SignedSquare
public import MeyerGeneralProblem.Sampling.CosineIngham
public import MeyerGeneralProblem.Sampling.WindowChoice

@[expose] public section

/-!
# Strict-subcritical carrier Ingham window

This low-level bridge combines signed-square carrier separation with the
cosine-window parameter choice.  Keeping it below both the Gram model and the
endpoint assembly prevents an inverted dependency between those two layers.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A strict-subcritical carrier supplies, after a finite deletion, both a
signed-square separation constant and a valid Ingham window. -/
theorem strictSubcritical_exists_separated_ingham_window
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ d > 1, ∃ F : Finset ℤ,
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∃ a : ℝ, 0 < a ∧ 1 / (2 * d) < a ∧ a < 1 / 2 ∧
        0 < inghamFloorFactor a d := by
  rcases strictSubcritical_signedSquare_separated hΛ with
    ⟨d, hd, F, hsep⟩
  exact ⟨d, hd, F, hsep, exists_subcritical_ingham_window hd⟩

end


end MeyerGeneralProblem
