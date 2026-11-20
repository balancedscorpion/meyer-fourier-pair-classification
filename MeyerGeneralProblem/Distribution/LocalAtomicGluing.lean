module

public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Local verification of order-zero carrier support

A finite smooth partition over the support of a compact test reduces
annihilation to the actual local Schwartz tests. Expanding cutoffs then
give annihilation of the full Schwartz vanishing ideal.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped ContDiff Manifold SchwartzMap Topology

/-- Local annihilation of tests vanishing on a carrier implies the global
intrinsic order-zero condition on that carrier. -/
theorem atomicOnCarrier_of_locally_annihilates
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hlocal : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ φ : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) → SchwartzVanishesOn S φ → T φ = 0) :
    AtomicOnCarrier S T := by
  classical
  choose δ hδ haction using hlocal
  have hcomp (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) (hv : SchwartzVanishesOn S f) :
      T f = 0 := by
    let K := tsupport f
    let U (a : ℝ) := Metric.ball a (δ a)
    have hK : IsCompact K := hf
    have hU (a : ℝ) : IsOpen (U a) := Metric.isOpen_ball
    have hcover : K ⊆ ⋃ a : ℝ, U a := by
      intro x _
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hδ x)⟩
    obtain ⟨E, hE⟩ := hK.elim_finite_subcover U hU hcover
    have hcoverE : K ⊆ ⋃ a : E, U a := by
      intro x hx
      have h := hE hx
      simp only [mem_iUnion] at h ⊢
      obtain ⟨a, ha, hx⟩ := h
      exact ⟨⟨a, ha⟩, hx⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ))
      (isClosed_tsupport f) (fun a : E => U a) (fun a => hU a) hcoverE
    let g (a : E) : ℝ → ℂ := fun x => (ρ a x : ℂ) * f x
    have hgC (a : E) : HasCompactSupport (g a) := hf.mul_left
    have hgs (a : E) : ContDiff ℝ ∞ (g a) :=
      (Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp (ρ a).contMDiff)).mul f.smooth'
    let φ (a : E) : SchwartzMap ℝ ℂ := (hgC a).toSchwartzMap (hgs a)
    have hval (a : E) (x : ℝ) : φ a x = (ρ a x : ℂ) * f x := rfl
    have hsum : f = ∑ a : E, φ a := by
      ext x
      simp only [_root_.sum_apply, hval, ← Finset.sum_mul]
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hx : x ∈ K := subset_tsupport f hfx
        have heq := ρ.sum_eq_one hx
        rw [finsum_eq_sum_of_fintype] at heq
        rw [← Complex.ofReal_sum, heq, Complex.ofReal_one, one_mul]
    have hzero (a : E) : T (φ a) = 0 := by
      apply haction a (φ a) _ (fun x hx => by rw [hval, hv x hx, mul_zero])
      intro x hx
      have hxρ : ρ a x ≠ 0 := by
        intro he
        exact hx (by rw [hval, he, Complex.ofReal_zero, zero_mul])
      have hb : x ∈ U a := hρ a (subset_tsupport (ρ a) hxρ)
      exact le_of_lt (by simpa only [U, Metric.mem_ball, Real.dist_eq] using hb)
    rw [hsum, map_sum, Finset.sum_eq_zero (fun a _ => hzero a)]
  intro f hf
  have hzero (n : ℕ) : T (compactSchwartzApproximation n f) = 0 :=
    hcomp _ (compactSchwartzApproximation_hasCompactSupport n f)
      (compactSchwartzApproximation_preserves_vanishing S n f hf)
  have hlim := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzlim : Tendsto (fun n => T (compactSchwartzApproximation n f)) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzlim

end

end MeyerGeneralProblem
