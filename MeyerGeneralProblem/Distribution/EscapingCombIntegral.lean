module

public import MeyerGeneralProblem.Distribution.FinitePhaseCombKernel
public import MeyerGeneralProblem.Distribution.WeightedQuadrant

@[expose] public section

/-!
# The escaping integral of an affine comb

The forward and backward halves escape in opposite directions, with the
coefficients determined by the positive physical pushforward convention.
Their difference identity is proved against every Schwartz test by
splitting off the first row of absolutely convergent quadrant sums.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap

private theorem tsum_split_equiv {A B C : Type*} (e : A ⊕ B ≃ C) (g : C → ℂ)
    (hg : Summable g) :
    (∑' p : C, g p) =
      (∑' a : A, g (e (Sum.inl a))) + (∑' b : B, g (e (Sum.inr b))) := by
  rw [← e.tsum_eq g]
  have ha : Summable ((g ∘ e) ∘ Sum.inl) :=
    hg.comp_injective (e.injective.comp Sum.inl_injective)
  have hb : Summable ((g ∘ e) ∘ Sum.inr) :=
    hg.comp_injective (e.injective.comp Sum.inr_injective)
  exact Summable.tsum_sum ha hb

private def quadrantFirstRowEquiv : ℕ ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun
    | .inl n => (n, 0)
    | .inr (n, m) => (n, m + 1)
  invFun
    | (n, 0) => .inl n
    | (n, m + 1) => .inr (n, m)
  left_inv := by rintro (n | ⟨n, m⟩) <;> rfl
  right_inv := by rintro ⟨n, m | m⟩ <;> rfl

private theorem tsum_quadrant_firstRow (g : ℕ × ℕ → ℂ) (hg : Summable g) :
    (∑' p, g p) = (∑' n, g (n, 0)) + (∑' p : ℕ × ℕ, g (p.1, p.2 + 1)) :=
  tsum_split_equiv quadrantFirstRowEquiv g hg

def affinePhaseQuadrant (y d a b : ℝ) (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) : TemperedDistribution ℝ ℂ :=
  combDistributionTranslation y
    (weightedQuadrant d a b hd ha hb (fun p => u p.1 * ω ^ p.2) M hM
      (fun p => by simpa only [norm_mul, norm_pow, hω, one_pow, mul_one] using hu p.1))

private theorem affinePhaseQuadrant_apply (y d a b : ℝ)
    (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) (f : SchwartzMap ℝ ℂ) :
    affinePhaseQuadrant y d a b hd ha hb u M hM hu ω hω f =
      ∑' p : ℕ × ℕ, (u p.1 * ω ^ p.2) * f (y + quadrantNode d a b p) := by
  simp only [affinePhaseQuadrant, combDistributionTranslation_apply, weightedQuadrant_apply,
    combSchwartzTranslation_apply]

private theorem summable_affinePhaseQuadrant (y d a b : ℝ) (hd : |d| = 1)
    (ha : 0 < a) (hb : 0 < b) (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) (f : SchwartzMap ℝ ℂ) :
    Summable (fun p : ℕ × ℕ => (u p.1 * ω ^ p.2) * f (y + quadrantNode d a b p)) := by
  simpa only [combSchwartzTranslation_apply] using
    summable_weightedQuadrant_samples d a b hd ha hb (fun p => u p.1 * ω ^ p.2) M hM
      (fun p => by simpa only [norm_mul, norm_pow, hω, one_pow, mul_one] using hu p.1)
      (combSchwartzTranslation y f)

private theorem affinePhaseQuadrant_atomicOnCarrier (y d a b : ℝ)
    (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) :
    AtomicOnCarrier ((quadrantCarrier d a b hd ha hb).translate y)
      (affinePhaseQuadrant y d a b hd ha hb u M hM hu ω hω) :=
  atomicOnCarrier_combDistributionTranslation _ _
    (weightedQuadrant_atomicOnCarrier d a b hd ha hb _ M hM _) y

theorem phase_norm_inv (ω : ℂ) (hω : ‖ω‖ = 1) : ‖ω⁻¹‖ = 1 := by rw [norm_inv, hω, inv_one]

private theorem forwardQuadrant_boundary (y a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) (f : SchwartzMap ℝ ℂ) :
    let P := affinePhaseQuadrant y 1 a w (abs_one) ha hw u M hM hu ω⁻¹ (phase_norm_inv ω hω)
    P f = (∑' n : ℕ, u n * f (y + a * (n : ℝ))) + ω⁻¹ * P (combSchwartzTranslation w f) := by
  dsimp only
  rw [affinePhaseQuadrant_apply, affinePhaseQuadrant_apply, ← tsum_mul_left]
  rw [tsum_quadrant_firstRow _ (summable_affinePhaseQuadrant y 1 a w abs_one ha hw u M hM hu
    ω⁻¹ (phase_norm_inv ω hω) f)]
  congr 1
  · apply tsum_congr
    intro n
    simp [quadrantNode]
  · apply tsum_congr
    intro p
    rw [pow_succ, combSchwartzTranslation_apply]
    have h : y + quadrantNode 1 a w (p.1, p.2 + 1) =
        w + (y + quadrantNode 1 a w p) := by simp only [quadrantNode, Nat.cast_add, Nat.cast_one]; ring
    rw [h]
    ring

private theorem backwardQuadrant_boundary (y a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (ω : ℂ) (hω : ‖ω‖ = 1) (f : SchwartzMap ℝ ℂ) :
    let N := affinePhaseQuadrant (y - a - w) (-1) a w (by norm_num) ha hw u M hM hu ω hω
    N (combSchwartzTranslation w f) =
      (∑' n : ℕ, u n * f (y - a * ((n : ℝ) + 1))) + ω * N f := by
  dsimp only
  rw [affinePhaseQuadrant_apply, affinePhaseQuadrant_apply, ← tsum_mul_left]
  rw [tsum_quadrant_firstRow _
    (summable_affinePhaseQuadrant (y - a - w) (-1) a w (by norm_num) ha hw u M hM hu
      ω hω (combSchwartzTranslation w f))]
  congr 1
  · apply tsum_congr
    intro n
    rw [pow_zero, mul_one, combSchwartzTranslation_apply]
    congr 2
    simp only [quadrantNode, Nat.cast_zero, mul_zero]
    ring
  · apply tsum_congr
    intro p
    rw [pow_succ, combSchwartzTranslation_apply]
    have h : w + (y - a - w + quadrantNode (-1) a w (p.1, p.2 + 1)) =
        y - a - w + quadrantNode (-1) a w p := by
      simp only [quadrantNode, Nat.cast_add, Nat.cast_one]
      ring
    rw [h]
    ring

/-- The coefficient of a comb summand at its integer index for the given step. -/
def AffineCombTerm.weight (q : AffineCombTerm) (a : ℝ) (k : ℤ) : ℂ :=
  q.coefficient * combModulationCharacter q.frequency (q.origin + (k : ℝ) * a)

theorem norm_affineCombTerm_weight (q : AffineCombTerm) (a : ℝ) (k : ℤ) :
    ‖q.weight a k‖ = ‖q.coefficient‖ := by
  simp only [AffineCombTerm.weight, norm_mul, norm_combModulationCharacter, mul_one]

private theorem affineCombTerm_split_action (q : AffineCombTerm) (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap ℝ ℂ) :
    q.distribution a ha f =
      (∑' n : ℕ, q.weight a (Int.ofNat n) * f (q.origin + a * (n : ℝ))) +
      (∑' n : ℕ, q.weight a (Int.negSucc n) * f (q.origin - a * ((n : ℝ) + 1))) := by
  simp only [AffineCombTerm.distribution, smul_apply, smul_eq_mul, modulatedAffineDiracComb_apply,
    ← tsum_mul_left, ← mul_assoc]
  let g (k : ℤ) := q.weight a k * f (q.origin + (k : ℝ) * a)
  have hg : Summable g := by
    simpa only [g, combSchwartzDilation_apply, combSchwartzTranslation_apply,
      mul_comm a] using summable_weightedInteger_samples (q.weight a)
        (norm_nonneg q.coefficient) (fun k => (norm_affineCombTerm_weight q a k).le)
        (combSchwartzDilation a ha.ne' (combSchwartzTranslation q.origin f))
  change (∑' k, g k) = _
  rw [tsum_split_equiv Equiv.intEquivNatSumNat.symm g hg]
  congr 1
  · apply tsum_congr
    intro n
    simp only [g, Equiv.intEquivNatSumNat, Equiv.coe_fn_symm_mk, Sum.elim_inl,
      Int.ofNat_eq_natCast, Int.cast_natCast, mul_comm a]
  · apply tsum_congr
    intro n
    simp only [g, Equiv.intEquivNatSumNat, Equiv.coe_fn_symm_mk, Sum.elim_inr, Int.cast_negSucc,
      Nat.cast_add, Nat.cast_one]
    congr 2
    ring

def escapingCombForward (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (ω : ℂ) (hω : ‖ω‖ = 1) : TemperedDistribution ℝ ℂ :=
  affinePhaseQuadrant q.origin 1 a w abs_one ha hw (fun n => q.weight a (Int.ofNat n))
    ‖q.coefficient‖ (norm_nonneg _) (fun _ => (norm_affineCombTerm_weight q a _).le) ω⁻¹ (phase_norm_inv ω hω)

def escapingCombBackward (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (ω : ℂ) (hω : ‖ω‖ = 1) : TemperedDistribution ℝ ℂ :=
  affinePhaseQuadrant (q.origin - a - w) (-1) a w (by norm_num) ha hw
    (fun n => q.weight a (Int.negSucc n)) ‖q.coefficient‖ (norm_nonneg _)
    (fun _ => (norm_affineCombTerm_weight q a _).le) ω hω

/-- The two actual outgoing quadrant records for one comb, using the
positive physical pushforward and its corresponding negative character. -/
def escapingCombIntegral (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (s : ℝ) : TemperedDistribution ℝ ℂ :=
  let ω := combModulationCharacter (-w) s
  let hω := norm_combModulationCharacter (-w) s
  (-ω⁻¹) • escapingCombForward q a w ha hw ω hω + escapingCombBackward q a w ha hw ω hω

/-- Its physical carrier is the union of the two actual closed quadrants.
The backward origin records the strict negative index of both steps. -/
def escapingCombIntegralCarrier (y a w : ℝ) (ha : 0 < a) (hw : 0 < w) : LocallyFiniteCarrier :=
  ((quadrantCarrier 1 a w abs_one ha hw).translate y).union
    ((quadrantCarrier (-1) a w (by norm_num) ha hw).translate (y - a - w))

theorem escapingCombIntegral_atomicOnCarrier (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) :
    AtomicOnCarrier (escapingCombIntegralCarrier q.origin a w ha hw)
      (escapingCombIntegral q a w ha hw s) := by
  intro f hf
  simp only [escapingCombIntegral, escapingCombForward, escapingCombBackward, add_apply,
    smul_apply, smul_eq_mul]
  have hf₁ : SchwartzVanishesOn ((quadrantCarrier 1 a w abs_one ha hw).translate q.origin) f :=
    fun x hx => hf x (Or.inl hx)
  have hf₂ : SchwartzVanishesOn
      ((quadrantCarrier (-1) a w (by norm_num) ha hw).translate (q.origin - a - w)) f :=
    fun x hx => hf x (Or.inr hx)
  rw [affinePhaseQuadrant_atomicOnCarrier _ _ _ _ _ _ _ _ _ _ _ _ _ f hf₁,
    affinePhaseQuadrant_atomicOnCarrier _ _ _ _ _ _ _ _ _ _ _ _ _ f hf₂, mul_zero, add_zero]

/-- Every Schwartz pairing retains the original quadrant weights and
indices, including all collisions between distinct indices. -/
theorem escapingCombIntegral_apply (q : AffineCombTerm) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    let ω := combModulationCharacter (-w) s
    escapingCombIntegral q a w ha hw s f =
      (-ω⁻¹) * (∑' p : ℕ × ℕ, (q.weight a (Int.ofNat p.1) * (ω⁻¹) ^ p.2) *
        f (q.origin + quadrantNode 1 a w p)) +
      (∑' p : ℕ × ℕ, (q.weight a (Int.negSucc p.1) * ω ^ p.2) *
        f (q.origin - a - w + quadrantNode (-1) a w p)) := by
  simp only [escapingCombIntegral, escapingCombForward, escapingCombBackward, add_apply,
    smul_apply, smul_eq_mul, affinePhaseQuadrant_apply]

/-- The two outgoing quadrant index sets with the original affine coordinates. -/
theorem mem_escapingCombIntegralCarrier (y a w : ℝ) (ha : 0 < a) (hw : 0 < w) (x : ℝ) :
    x ∈ (escapingCombIntegralCarrier y a w ha hw).carrier ↔
      (∃ p : ℕ × ℕ, x = y + a * (p.1 : ℝ) + w * (p.2 : ℝ)) ∨
      (∃ p : ℕ × ℕ, x = y - a * ((p.1 : ℝ) + 1) - w * ((p.2 : ℝ) + 1)) := by
  rw [escapingCombIntegralCarrier, LocallyFiniteCarrier.union_carrier, Set.mem_union,
    LocallyFiniteCarrier.mem_translate, LocallyFiniteCarrier.mem_translate]
  constructor
  · rintro (⟨_, ⟨p, rfl⟩, rfl⟩ | ⟨_, ⟨p, rfl⟩, rfl⟩)
    · exact Or.inl ⟨p, by unfold quadrantNode; ring⟩
    · exact Or.inr ⟨p, by unfold quadrantNode; ring⟩
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact Or.inl ⟨_, ⟨p, rfl⟩, by unfold quadrantNode; ring⟩
    · exact Or.inr ⟨_, ⟨p, rfl⟩, by unfold quadrantNode; ring⟩

/-- A single translation factor applied to the actual escaping integral
returns the original comb as a tempered distribution. -/
theorem combTranslationFactor_escapingCombIntegral (q : AffineCombTerm) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) (s : ℝ) :
    combTranslationFactor w s (escapingCombIntegral q a w ha hw s) = q.distribution a ha := by
  let ω := combModulationCharacter (-w) s
  let hω := norm_combModulationCharacter (-w) s
  have hne : ω ≠ 0 := by
    intro he
    have hn : ‖ω‖ = 1 := hω
    rw [he, norm_zero] at hn
    norm_num at hn
  let P := escapingCombForward q a w ha hw ω hω
  let N := escapingCombBackward q a w ha hw ω hω
  ext f
  have hp := forwardQuadrant_boundary q.origin a w ha hw
    (fun n => q.weight a (Int.ofNat n)) ‖q.coefficient‖ (norm_nonneg _)
    (fun _ => (norm_affineCombTerm_weight q a _).le) ω hω f
  have hn := backwardQuadrant_boundary q.origin a w ha hw
    (fun n => q.weight a (Int.negSucc n)) ‖q.coefficient‖ (norm_nonneg _)
    (fun _ => (norm_affineCombTerm_weight q a _).le) ω hω f
  let plus := ∑' n : ℕ, q.weight a (Int.ofNat n) * f (q.origin + a * (n : ℝ))
  let minus := ∑' n : ℕ, q.weight a (Int.negSucc n) * f (q.origin - a * ((n : ℝ) + 1))
  change P f = plus + ω⁻¹ * P (combSchwartzTranslation w f) at hp
  change N (combSchwartzTranslation w f) = minus + ω * N f at hn
  rw [affineCombTerm_split_action q a ha f, combTranslationFactor_apply]
  change (combDistributionTranslation w ((-ω⁻¹) • P + N) - ω • ((-ω⁻¹) • P + N)) f =
    plus + minus
  simp only [sub_apply, smul_apply, add_apply, smul_eq_mul, combDistributionTranslation_apply]
  rw [hp, hn]
  linear_combination (plus + ω⁻¹ * P (combSchwartzTranslation w f)) * (mul_inv_cancel₀ hne)

end
end MeyerGeneralProblem
