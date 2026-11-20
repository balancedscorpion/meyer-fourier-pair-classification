module

public import MeyerGeneralProblem.Gram.GroupedGramKernel
public import MeyerGeneralProblem.Gram.CarrierUniversalCompactness
public import MeyerGeneralProblem.Gram.GroupedSchurCompactness

@[expose] public section

/-!
# Gap-independent grouped Gram remainder estimates

Actual barycentric divided differences are bounded using the proved local
HG theorem. Near-band smallness and off-diagonal decay are kept distinct.
The one-anchor normalization in the actual grouped Gram is tracked separately
from the divided differences of the point-normalized kernel.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped Topology
open Finset

/-- A nonnegative HG bound can discard reciprocal factorials without
introducing a node-gap constant. -/
theorem grouped_div_factorials_le (M : ℝ) (hM : 0 ≤ M) (i j : ℕ) :
    (M/(j.factorial:ℝ))/(i.factorial:ℝ) ≤ M := by
  exact (div_le_self (by positivity) (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos i)))).trans
    (div_le_self hM (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos j))))

/-- Uniform near-band smallness of genuine grouped divided differences
of the normalized Hermite-minus-universal remainder. The finite lists can
have arbitrarily small internal gaps; their common diameter bound is fixed. -/
theorem groupedDoubleDividedDifference_hermiteRemainder_uniform_small
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (ε : ℝ) (hε : ε^2=1) (i j : ℕ) (hi : i ≤ q) (hj : j ≤ q)
    (D L : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∀ δ > 0, ∃ T ≥ 1, ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      T ≤ r → T ≤ t → |t-r| ≤ L →
      (∀ x, nodes x ∈ Set.Icc r (r+D)) → (∀ y, other y ∈ Set.Icc t (t+D)) →
      ‖groupedDoubleDividedDifference nodes other a b
        (groupedMagnitudeHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε)‖ ≤ δ := by
  intro δ hδ
  obtain ⟨T,hT,hsmall⟩ := groupedMagnitudeHermiteRemainder_mixedDeriv_vanishesOnBands q m i j hm hi hj ε hε
    (L+2*D) (by positivity) δ hδ
  refine ⟨T,hT,?_⟩
  intro n k nodes other hnodes hother a b ha hb r t hr ht hrt hn ho
  have hle := norm_groupedDoubleDividedDifference_le_positive nodes other hnodes hother a b
    (groupedMagnitudeHermiteRemainder m _ ε)
    (fun x y hx _hy => (contDiffAt_groupedMagnitudeHermiteRemainder_left (q+1) m hm ε x y hε hx).of_le
      (by exact_mod_cast (show a.val ≤ q+1 by omega)))
    (fun x y hx hy => (contDiffAt_iteratedDeriv_groupedMagnitudeHermiteRemainder_right (q+1) m a.val hm
      (by omega) ε x y hε hx hy).of_le (by exact_mod_cast (show b.val ≤ q+1 by omega)))
    (hT.trans hr) (hT.trans ht) hn ho (M := δ) (fun x hx y hy => ?_)
  · exact hle.trans (grouped_div_factorials_le δ hδ.le _ _)
  · have hdist : |y-x| ≤ L+2*D := by
      have htri := abs_add_three (y-t) (t-r) (r-x)
      have hyt : |y-t| ≤ D := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
      have hrx : |r-x| ≤ D := abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
      rw [show (y-t)+(t-r)+(r-x)=y-x by ring] at htri
      linarith
    simpa only [ha,hb] using hsmall x y (hr.trans hx.1) (ht.trans hy.1) hdist

/-- Genuine grouped remainder entries have a summable exponential
envelope in the distance between group anchors. The constant depends on
the diameter and fixed derivative orders, never on an internal gap. -/
theorem exists_groupedDoubleDividedDifference_hermiteRemainder_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ε^2=1 →
      ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      1 ≤ r → 1 ≤ t → (∀ x, nodes x ∈ Set.Icc r (r+D)) →
      (∀ y, other y ∈ Set.Icc t (t+D)) →
      ‖groupedDoubleDividedDifference nodes other a b
        (groupedMagnitudeHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε)‖ ≤
        C*Real.exp (-c*|t-r|) := by
  obtain ⟨C,hC,c,hc,hdec⟩ := exists_norm_mixedDeriv_groupedMagnitudeHermiteRemainder_le_exponential q m i j hm hi hj
  refine ⟨C*Real.exp (2*c*D),by positivity,c,hc,?_⟩
  intro ε hε n k nodes other hnodes hother a b ha hb r t hr ht hn ho
  have hM : 0 ≤ (C*Real.exp (2*c*D))*Real.exp (-c*|t-r|) := by positivity
  have hle := norm_groupedDoubleDividedDifference_le_positive nodes other hnodes hother a b
    (groupedMagnitudeHermiteRemainder m _ ε)
    (fun x y hx _hy => (contDiffAt_groupedMagnitudeHermiteRemainder_left (q+1) m hm ε x y hε hx).of_le
      (by exact_mod_cast (show a.val ≤ q+1 by omega)))
    (fun x y hx hy => (contDiffAt_iteratedDeriv_groupedMagnitudeHermiteRemainder_right (q+1) m a.val hm
      (by omega) ε x y hε hx hy).of_le (by exact_mod_cast (show b.val ≤ q+1 by omega))) hr ht hn ho
    (M := (C*Real.exp (2*c*D))*Real.exp (-c*|t-r|)) (fun x hx y hy => ?_)
  · exact hle.trans (grouped_div_factorials_le _ hM _ _)
  · have htri := abs_add_three (t-y) (y-x) (x-r)
    have hty : |t-y| ≤ D := abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
    have hxr : |x-r| ≤ D := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [show (t-y)+(y-x)+(x-r)=t-r by ring] at htri
    have hlow : |t-r|-2*D ≤ |y-x| := by linarith
    have h := hdec ε hε x y (hr.trans hx.1) (ht.trans hy.1)
    rw [ha,hb]
    refine h.trans ?_
    rw [mul_assoc,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith

/-- Uniform tail smallness with two genuine lower anchor parameters and
bounded group hulls. This records limits of actual kernels, not compactness. -/
def GroupedAnchorVanishesOnBands (F : ℝ → ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ D ≥ 0, ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 1, ∀ a b s t : ℝ,
    T ≤ a → T ≤ b → s ∈ Set.Icc a (a+D) → t ∈ Set.Icc b (b+D) →
    |t-s| ≤ L → ‖F a b s t‖ ≤ δ

theorem groupedAnchorHermiteRemainder_vanishesOnBands
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : ε^2=1) :
    GroupedAnchorVanishesOnBands (groupedAnchorHermiteRemainder m hm ε) := by
  intro D hD L hL δ hδ
  obtain ⟨T,hT,hsmall⟩ := groupedMagnitudeHermiteRemainder_vanishesOnBands m hm ε hε L hL (δ/2) (by positivity)
  let N := groupedNormalizerDerivativeConstant m 1
  have hN : 0 < N := groupedNormalizerDerivativeConstant_pos m hm 1
  refine ⟨max T (1+4*N*D/δ),hT.trans (le_max_left _ _),?_⟩
  intro a b s t ha hb hs ht hst
  have haT : T ≤ a := (le_max_left _ _).trans ha
  have hbT : T ≤ b := (le_max_left _ _).trans hb
  have ha1 : 1 ≤ a := hT.trans haT
  have hb1 : 1 ≤ b := hT.trans hbT
  have hcorr (x : ℝ) (hx : max T (1+4*N*D/δ) ≤ x) : (N/x)*D ≤ δ/4 := by
    have hx1 : 1 ≤ x := hT.trans ((le_max_left _ _).trans hx)
    have hxδ : 4*N*D/δ ≤ x := by linarith [(le_max_right T (1+4*N*D/δ)).trans hx]
    have hmul : 4*N*D ≤ x*δ := (div_le_iff₀ hδ).mp hxδ
    have heq : (N/x)*D=N*D/x := by ring
    rw [heq]
    apply (div_le_iff₀ (by linarith : 0 < x)).mpr
    nlinarith
  have h := norm_groupedAnchorHermiteRemainder_le m hm ε a b s t D hε ha1 hb1 hs ht
  have hsml := hsmall s t (haT.trans hs.1) (hbT.trans ht.1) hst
  have ha' := hcorr a ha
  have hb' := hcorr b hb
  dsimp [N] at ha' hb'
  linarith

/-- The actual Taylor interpolation step, uniformly in both anchors.
Increasing the allowed hull diameter by one keeps the interpolation
interval inside the domain without any minimum gap hypothesis. -/
theorem GroupedAnchorVanishesOnBands.deriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedAnchorVanishesOnBands F)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ 2 (fun u => F a b u t) s)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ‖iteratedDeriv 2 (fun u => F a b u t) s‖ ≤ B) :
    GroupedAnchorVanishesOnBands (fun a b s t => deriv (fun u => F a b u t) s) := by
  intro D hD L hL δ hδ
  let h := min 1 (δ/(4*(B+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhδ : h ≤ δ/(4*(B+1)) := min_le_right _ _
  have hBh : B*h ≤ δ/4 := by
    have hh' : h*(4*(B+1)) ≤ δ := (le_div_iff₀ (by positivity)).mp hhδ
    nlinarith
  obtain ⟨T,hT,hsmall⟩ := hF (D+1) (by linarith) (L+1) (by linarith) (δ*h/8) (by positivity)
  refine ⟨T,hT,?_⟩
  intro a b s t ha hb hs ht hst
  have hlocal (u : ℝ) (hu : u ∈ Set.Icc s (s+h)) :
      u ∈ Set.Icc a (a+(D+1)) ∧ |t-u| ≤ L+1 := by
    constructor
    · exact ⟨hs.1.trans hu.1,by linarith [hs.2,hu.2]⟩
    · have htri := abs_add_le (t-s) (s-u)
      rw [show (t-s)+(s-u)=t-u by ring] at htri
      have hsu : |s-u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.2],by linarith [hu.1]⟩
      linarith
  have hres := grouped_norm_deriv_le_value_secondDerivative (fun u => F a b u t) s h (δ*h/8) B hh
    (fun u hu => hreg a b u t (hT.trans ha) (hT.trans hb) (hs.1.trans hu.1) ht.1)
    (fun u hu => hsmall a b u t ha hb (hlocal u hu).1 ⟨ht.1,by linarith [ht.2]⟩ (hlocal u hu).2)
    (fun u hu => hbound a b u t (hT.trans ha) (hT.trans hb) (hs.1.trans hu.1) ht.1)
  have hquot : 2*(δ*h/8)/h=δ/4 := by field_simp; norm_num
  rw [hquot] at hres
  linarith

theorem GroupedAnchorVanishesOnBands.iteratedDeriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedAnchorVanishesOnBands F) (q : ℕ)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ (q+1) (fun u => F a b u t) s)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t → ‖iteratedDeriv k (fun u => F a b u t) s‖ ≤ B) :
    ∀ i ≤ q, GroupedAnchorVanishesOnBands (fun a b s t => iteratedDeriv i (fun u => F a b u t) s) := by
  intro i
  induction i with
  | zero => intro _; simpa only [iteratedDeriv_zero] using hF
  | succ i ih =>
    intro hi
    obtain ⟨B,hB,hmajor⟩ := hbound (i+2) (by omega)
    have h := (ih (by omega)).deriv_left (fun a b s t ha hb has hbt =>
      grouped_contDiffAt_iteratedDeriv (fun u => F a b u t) 2 i s
        ((hreg a b s t ha hb has hbt).of_le (by exact_mod_cast (show 2+i ≤ q+1 by omega)))) B hB
      (fun a b s t ha hb has hbt => by
        rw [grouped_iteratedDeriv_iteratedDeriv]
        simpa only [Nat.add_comm] using hmajor a b s t ha hb has hbt)
    simpa only [iteratedDeriv_succ] using h

theorem GroupedAnchorVanishesOnBands.swap
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedAnchorVanishesOnBands F) :
    GroupedAnchorVanishesOnBands (fun a b s t => F b a t s) := by
  intro D hD L hL δ hδ
  obtain ⟨T,hT,h⟩ := hF D hD L hL δ hδ
  exact ⟨T,hT,fun a b s t ha hb hs ht hst => h b a t s hb ha ht hs (by simpa only [abs_sub_comm] using hst)⟩

theorem GroupedAnchorVanishesOnBands.iteratedDeriv_right
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedAnchorVanishesOnBands F) (q : ℕ)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ (q+1) (F a b s) t)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t → ‖iteratedDeriv k (F a b s) t‖ ≤ B) :
    ∀ j ≤ q, GroupedAnchorVanishesOnBands (fun a b s t => iteratedDeriv j (F a b s) t) := by
  intro j hj
  have h := hF.swap.iteratedDeriv_left q
    (fun a b s t ha hb has hbt => hreg b a t s hb ha hbt has)
    (fun k hk => by
      obtain ⟨B,hB,hmajor⟩ := hbound k hk
      exact ⟨B,hB,fun a b s t ha hb has hbt => hmajor b a t s hb ha hbt has⟩) j hj
  exact h.swap

/-- Arbitrary mixed derivatives of the actual two-anchor-normalized
remainder are uniformly small on bounded-diameter tail groups. -/
theorem groupedAnchorHermiteRemainder_mixedDeriv_vanishesOnBands
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1) :
    GroupedAnchorVanishesOnBands (fun a b s t => iteratedDeriv j (fun v => iteratedDeriv i (fun u =>
      groupedAnchorHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε a b u v) s) t) := by
  have hbound (a b : ℕ) (ha : a ≤ q+1) (hb : b ≤ q+1) :=
    exists_norm_mixedDeriv_groupedAnchorHermiteRemainder_le (q+1) m a b hm ha hb
  have hleft := (groupedAnchorHermiteRemainder_vanishesOnBands m _ ε hε).iteratedDeriv_left q
    (fun a b s t ha _hb has _hbt => contDiffAt_groupedAnchorHermiteRemainder_left (q+1) m hm ε a b s t hε (by linarith))
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound k 0 hk (by omega)
      exact ⟨B,hB,by simpa only [iteratedDeriv_zero] using hb ε hε⟩) i hi
  exact hleft.iteratedDeriv_right q
    (fun a b s t ha hb has hbt => contDiffAt_iteratedDeriv_groupedAnchorHermiteRemainder_right
      (q+1) m i hm (by omega) ε a b s t hε (by linarith) (by linarith))
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound i k (by omega) hk
      exact ⟨B,hB,hb ε hε⟩) j hj

/-- Exponential localization uniformly in the two group anchors. -/
def GroupedAnchorExponentialDecay (ε η : ℝ) (F : ℝ → ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ a b s t : ℝ,
    1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t → ‖F a b s t‖ ≤ C*Real.exp (-c*|η*t-ε*s|)

theorem GroupedAnchorExponentialDecay.deriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} {ε η : ℝ} (hF : GroupedAnchorExponentialDecay ε η F) (hε : ε^2=1)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ 2 (fun u => F a b u t) s)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ‖iteratedDeriv 2 (fun u => F a b u t) s‖ ≤ B) :
    GroupedAnchorExponentialDecay ε η (fun a b s t => deriv (fun u => F a b u t) s) := by
  obtain ⟨A,hA,c,hc,hdec⟩ := hF
  refine ⟨2*(A*Real.exp c)+B,by positivity,c/2,by positivity,?_⟩
  intro a b s t ha hb has hbt
  have heps : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  have hd (u : ℝ) (hu : u ∈ Set.Icc s (s+1)) : |η*t-ε*s|-1 ≤ |η*t-ε*u| := by
    have hlocal : |u-s| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have htri := abs_add_le (η*t-ε*u) (ε*(u-s))
    rw [show (η*t-ε*u)+ε*(u-s)=η*t-ε*s by ring,abs_mul,heps,one_mul] at htri
    linarith
  have h := grouped_norm_deriv_le_exponential_of_secondDerivative (fun u => F a b u t) s
    (A*Real.exp c) B c |η*t-ε*s| hc.le (abs_nonneg _)
    (fun u hu => hreg a b u t ha hb (has.trans hu.1) hbt)
    (fun u hu => ?_) (fun u hu => hbound a b u t ha hb (has.trans hu.1) hbt)
  · convert h using 1
    congr 2
    ring
  · refine (hdec a b u t ha hb (has.trans hu.1) hbt).trans ?_
    rw [mul_assoc,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.exp_le_exp.mpr (by nlinarith [hd u hu])

theorem GroupedAnchorExponentialDecay.iteratedDeriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} {ε η : ℝ} (hF : GroupedAnchorExponentialDecay ε η F)
    (hε : ε^2=1) (q : ℕ)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ (q+1) (fun u => F a b u t) s)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t → ‖iteratedDeriv k (fun u => F a b u t) s‖ ≤ B) :
    ∀ i ≤ q, GroupedAnchorExponentialDecay ε η (fun a b s t => iteratedDeriv i (fun u => F a b u t) s) := by
  intro i
  induction i with
  | zero => intro _; simpa only [iteratedDeriv_zero] using hF
  | succ i ih =>
    intro hi
    obtain ⟨B,hB,hmajor⟩ := hbound (i+2) (by omega)
    have h := (ih (by omega)).deriv_left hε (fun a b s t ha hb has hbt =>
      grouped_contDiffAt_iteratedDeriv (fun u => F a b u t) 2 i s
        ((hreg a b s t ha hb has hbt).of_le (by exact_mod_cast (show 2+i ≤ q+1 by omega)))) B hB
      (fun a b s t ha hb has hbt => by
        rw [grouped_iteratedDeriv_iteratedDeriv]
        simpa only [Nat.add_comm] using hmajor a b s t ha hb has hbt)
    simpa only [iteratedDeriv_succ] using h

theorem GroupedAnchorExponentialDecay.swap
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} {ε η : ℝ} (hF : GroupedAnchorExponentialDecay ε η F) :
    GroupedAnchorExponentialDecay η ε (fun a b s t => F b a t s) := by
  obtain ⟨C,hC,c,hc,h⟩ := hF
  exact ⟨C,hC,c,hc,fun a b s t ha hb has hbt => by simpa only [abs_sub_comm] using h b a t s hb ha hbt has⟩

theorem GroupedAnchorExponentialDecay.iteratedDeriv_right
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} {ε η : ℝ} (hF : GroupedAnchorExponentialDecay ε η F)
    (hη : η^2=1) (q : ℕ)
    (hreg : ∀ a b s t : ℝ, 1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t →
      ContDiffAt ℝ (q+1) (F a b s) t)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ a b s t : ℝ,
      1 ≤ a → 1 ≤ b → a ≤ s → b ≤ t → ‖iteratedDeriv k (F a b s) t‖ ≤ B) :
    ∀ j ≤ q, GroupedAnchorExponentialDecay ε η (fun a b s t => iteratedDeriv j (F a b s) t) := by
  intro j hj
  have h := hF.swap.iteratedDeriv_left hη q
    (fun a b s t ha hb has hbt => hreg b a t s hb ha hbt has)
    (fun k hk => by
      obtain ⟨B,hB,hmajor⟩ := hbound k hk
      exact ⟨B,hB,fun a b s t ha hb has hbt => hmajor b a t s hb ha hbt has⟩) j hj
  exact h.swap

theorem groupedAnchorNormalizedKernel_mixedDeriv_exponentialDecay
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    GroupedAnchorExponentialDecay ε η (fun a b s t => iteratedDeriv j (fun v => iteratedDeriv i (fun u =>
      groupedAnchorNormalizedKernel m (by have := (le_max_left _ _).trans hm; omega) ε η a b u v) s) t) := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  have hzero : GroupedAnchorExponentialDecay ε η (groupedAnchorNormalizedKernel m hp ε η) := by
    refine ⟨hermiteNormalizedGramGaussianConstant m,hermiteNormalizedGramGaussianConstant_pos hp,
      Real.pi/2,by positivity,?_⟩
    intro a b s t ha hb has hbt
    rw [groupedAnchorNormalizedKernel_eq_ratios m hp ε η a b s t hε hη,norm_smul,
      Real.norm_of_nonneg (by positivity [groupedNormalizerRatio_pos m hp a s,groupedNormalizerRatio_pos m hp b t])]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      (norm_groupedMagnitudeNormalizedKernel_le_exponential m hp ε η s t hε hη (by linarith) (by linarith))
    exact (mul_le_of_le_one_right (groupedNormalizerRatio_pos m hp a s).le
      (groupedNormalizerRatio_le_one m hp (by linarith) hbt)).trans
      (groupedNormalizerRatio_le_one m hp (by linarith) has)
  have hbound (a b : ℕ) (ha : a ≤ q+1) (hb : b ≤ q+1) :=
    exists_norm_mixedDeriv_groupedAnchorNormalizedKernel_le (q+1) m a b hm ha hb
  have hleft := hzero.iteratedDeriv_left hε q
    (fun a b s t ha _hb has _hbt => contDiffAt_groupedAnchorNormalizedKernel_left (q+1) m hm ε η a b s t
      hε hη (by linarith))
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound k 0 hk (by omega)
      exact ⟨B,hB.le,by simpa only [iteratedDeriv_zero] using hb ε η hε hη⟩) i hi
  exact hleft.iteratedDeriv_right hη q
    (fun a b s t ha hb has hbt => contDiffAt_iteratedDeriv_groupedAnchorNormalizedKernel_right
      (q+1) m i hm (by omega) ε η a b s t hε hη (by linarith) (by linarith))
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound i k (by omega) hk
      exact ⟨B,hB.le,hb ε η hε hη⟩) j hj

theorem groupedAnchorHermiteRemainder_mixedDeriv_exponentialDecay
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1) :
    GroupedAnchorExponentialDecay ε ε (fun a b s t => iteratedDeriv j (fun v => iteratedDeriv i (fun u =>
      groupedAnchorHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε a b u v) s) t) := by
  obtain ⟨A,hA,a,ha,hactual⟩ := groupedAnchorNormalizedKernel_mixedDeriv_exponentialDecay q m i j hm hi hj ε ε hε hε
  obtain ⟨B,hB,b,hb,hmodel⟩ := exists_norm_iteratedDeriv_universalGramKernel_le_exponential_grouped q m i j hm hi hj
  refine ⟨A+B,by positivity,min a b,lt_min ha hb,?_⟩
  intro x y s t hx hy hxs hyt
  dsimp only
  rw [mixedDeriv_groupedAnchorHermiteRemainder_eq (q+1) m i j hm (by omega) (by omega) ε x y s t hε
    (by linarith) (by linarith)]
  have hεabs : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  have hd : |ε*t-ε*s|=|t-s| := by rw [← mul_sub,abs_mul,hεabs,one_mul]
  have hK := hactual x y s t hx hy hxs hyt
  dsimp only at hK
  rw [hd] at hK ⊢
  have hU : ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) s) t‖ ≤
      B*Real.exp (-b*|t-s|) := by
    rw [norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j ε s t hε]
    exact hmodel ε hε _
  refine (norm_sub_le _ _).trans ((add_le_add hK hU).trans ?_)
  rw [add_mul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_left a b,abs_nonneg (t-s)])
  · apply mul_le_mul_of_nonneg_left _ hB.le
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_right a b,abs_nonneg (t-s)])

/-- Uniform smallness of actual double divided differences of the
source-normalized anchor remainder on nearby tail groups. -/
theorem groupedDoubleDividedDifference_anchorRemainder_uniform_small
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1)
    (D L : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∀ δ > 0, ∃ T ≥ 1, ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      T ≤ r → T ≤ t → |t-r| ≤ L →
      (∀ x, nodes x ∈ Set.Icc r (r+D)) → (∀ y, other y ∈ Set.Icc t (t+D)) →
      ‖groupedDoubleDividedDifference nodes other a b
        (groupedAnchorHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε r t)‖ ≤ δ := by
  intro δ hδ
  obtain ⟨T,hT,hsmall⟩ := groupedAnchorHermiteRemainder_mixedDeriv_vanishesOnBands q m i j hm hi hj ε hε
    D hD (L+2*D) (by positivity) δ hδ
  refine ⟨T,hT,?_⟩
  intro n k nodes other hnodes hother a b ha hb r t hr ht hrt hn ho
  have hle := norm_groupedDoubleDividedDifference_le_positive nodes other hnodes hother a b
    (groupedAnchorHermiteRemainder m _ ε r t)
    (fun x y hx _hy => (contDiffAt_groupedAnchorHermiteRemainder_left (q+1) m hm ε r t x y hε hx).of_le
      (by exact_mod_cast (show a.val ≤ q+1 by omega)))
    (fun x y hx hy => (contDiffAt_iteratedDeriv_groupedAnchorHermiteRemainder_right (q+1) m a.val hm
      (by omega) ε r t x y hε hx hy).of_le (by exact_mod_cast (show b.val ≤ q+1 by omega)))
    (hT.trans hr) (hT.trans ht) hn ho (M := δ) (fun x hx y hy => ?_)
  · exact hle.trans (grouped_div_factorials_le δ hδ.le _ _)
  · have htri := abs_add_three (y-t) (t-r) (r-x)
    have hyt : |y-t| ≤ D := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hrx : |r-x| ≤ D := abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
    rw [show (y-t)+(t-r)+(r-x)=y-x by ring] at htri
    simpa only [ha,hb] using hsmall r t x y hr ht hx hy (by linarith)

/-- Uniform exponential envelope for actual source-normalized grouped
remainder entries, independent of the internal node gaps. -/
theorem exists_groupedDoubleDividedDifference_anchorRemainder_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      1 ≤ r → 1 ≤ t → (∀ x, nodes x ∈ Set.Icc r (r+D)) →
      (∀ y, other y ∈ Set.Icc t (t+D)) →
      ‖groupedDoubleDividedDifference nodes other a b
        (groupedAnchorHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε r t)‖ ≤
        C*Real.exp (-c*|t-r|) := by
  obtain ⟨C,hC,c,hc,hdec⟩ := groupedAnchorHermiteRemainder_mixedDeriv_exponentialDecay q m i j hm hi hj ε hε
  refine ⟨C*Real.exp (2*c*D),by positivity,c,hc,?_⟩
  intro n k nodes other hnodes hother a b ha hb r t hr ht hn ho
  have hM : 0 ≤ (C*Real.exp (2*c*D))*Real.exp (-c*|t-r|) := by positivity
  have hle := norm_groupedDoubleDividedDifference_le_positive nodes other hnodes hother a b
    (groupedAnchorHermiteRemainder m _ ε r t)
    (fun x y hx _hy => (contDiffAt_groupedAnchorHermiteRemainder_left (q+1) m hm ε r t x y hε hx).of_le
      (by exact_mod_cast (show a.val ≤ q+1 by omega)))
    (fun x y hx hy => (contDiffAt_iteratedDeriv_groupedAnchorHermiteRemainder_right (q+1) m a.val hm
      (by omega) ε r t x y hε hx hy).of_le (by exact_mod_cast (show b.val ≤ q+1 by omega))) hr ht hn ho
    (M := (C*Real.exp (2*c*D))*Real.exp (-c*|t-r|)) (fun x hx y hy => ?_)
  · exact hle.trans (grouped_div_factorials_le _ hM _ _)
  · have htri := abs_add_three (t-y) (y-x) (x-r)
    have hty : |t-y| ≤ D := abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
    have hxr : |x-r| ≤ D := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [show (t-y)+(y-x)+(x-r)=t-r by ring] at htri
    have hlow : |t-r|-2*D ≤ |y-x| := by linarith
    have h := hdec r t x y hr ht hx.1 hy.1
    have heps : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
    rw [← mul_sub,abs_mul,heps,one_mul] at h
    rw [ha,hb]
    refine h.trans ?_
    rw [mul_assoc,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem contDiffAt_iteratedDeriv_universalTwoRay_right (m q i : ℕ)
    (hi : q+i+2 ≤ 2*m) (ε η s t : ℝ) (hε : ε^2=1) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => universalGramKernel m (η*v-ε*u)) s) t := by
  have heq (v : ℝ) : iteratedDeriv i (fun u => universalGramKernel m (η*v-ε*u)) s =
      ε^i • iteratedDeriv i (fun z => universalGramKernel m (η*v-z)) (ε*s) :=
    grouped_iteratedDeriv_comp_sign (fun z => universalGramKernel m (η*v-z)) i ε s hε
  simp_rw [heq,iteratedDeriv_comp_const_sub]
  have hreg := grouped_contDiffAt_iteratedDeriv (universalGramKernel m) q i (η*t-ε*s)
    (contDiff_grouped_universalGramKernel m (q+i) hi).contDiffAt
  exact ((hreg.comp t ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)).const_smul
    ((-1:ℝ)^i)).const_smul (ε^i)

theorem norm_mixedDeriv_universalTwoRay (m i j : ℕ) (ε η s t : ℝ)
    (hε : ε^2=1) (hη : η^2=1) :
    ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (η*v-ε*u)) s) t‖ =
      ‖iteratedDeriv (j+i) (universalGramKernel m) (η*t-ε*s)‖ := by
  rw [grouped_norm_mixedDeriv_comp_signs (fun u v => universalGramKernel m (v-u)) i j ε η s t hε hη]
  simpa only [one_mul] using norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j 1
    (ε*s) (η*t) (by norm_num)

/-- Local HG transfers a proved mixed exponential estimate to genuine
double divided differences on two independent rays. -/
theorem norm_groupedDoubleDividedDifference_le_twoRay_exponential {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (K : ℝ → ℝ → ℂ)
    (hleft : ∀ x y, 0 < x → 0 < y → ContDiffAt ℝ i.val (fun z => K z y) x)
    (hright : ∀ x y, 0 < x → 0 < y →
      ContDiffAt ℝ j.val (fun v => iteratedDeriv i.val (fun u => K u v) x) y)
    (ε η r t D A c : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hD : 0 ≤ D) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hn : ∀ x, nodes x ∈ Set.Icc r (r+D)) (ho : ∀ y, other y ∈ Set.Icc t (t+D))
    (hdec : ∀ x ∈ Set.Icc r (r+D), ∀ y ∈ Set.Icc t (t+D),
      ‖iteratedDeriv j.val (fun v => iteratedDeriv i.val (fun u => K u v) x) y‖ ≤
        A*Real.exp (-c*|η*y-ε*x|)) :
    ‖groupedDoubleDividedDifference nodes other i j K‖ ≤
      (A*Real.exp (2*c*D))*Real.exp (-c*|η*t-ε*r|) := by
  have hM : 0 ≤ (A*Real.exp (2*c*D))*Real.exp (-c*|η*t-ε*r|) := by positivity
  apply (norm_groupedDoubleDividedDifference_le_positive nodes other hnodes hother i j K
    hleft hright hr ht hn ho (M := (A*Real.exp (2*c*D))*Real.exp (-c*|η*t-ε*r|)) ?_).trans
      (grouped_div_factorials_le _ hM _ _)
  intro x hx y hy
  have he : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  have het : |η|=1 := by nlinarith [sq_abs η,abs_nonneg η]
  have htri := abs_add_three (η*(t-y)) (η*y-ε*x) (ε*(x-r))
  rw [show η*(t-y)+(η*y-ε*x)+ε*(x-r)=η*t-ε*r by ring,
    abs_mul,abs_mul,he,het,one_mul,one_mul] at htri
  have hty : |t-y| ≤ D := abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have hxr : |x-r| ≤ D := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  refine (hdec x hx y hy).trans ?_
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hA
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Actual raw-anchor-minus-universal divided differences on all ray pairs
have a common off-diagonal envelope in signed-square anchor distance. -/
theorem exists_groupedDoubleDividedDifference_twoRayRemainder_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      1 ≤ r → 1 ≤ t → (∀ x, nodes x ∈ Set.Icc r (r+D)) →
      (∀ y, other y ∈ Set.Icc t (t+D)) →
      ‖groupedDoubleDividedDifference nodes other a b (fun s u =>
        groupedAnchorNormalizedKernel m (by have := (le_max_left _ _).trans hm; omega) ε η r t s u -
          universalGramKernel m (η*u-ε*s))‖ ≤ C*Real.exp (-c*|η*t-ε*r|) := by
  have hq : q+1+2 ≤ m := (le_max_left _ _).trans hm
  obtain ⟨A,hA,c,hc,hactual⟩ := groupedAnchorNormalizedKernel_mixedDeriv_exponentialDecay q m i j hm hi hj ε η hε hη
  obtain ⟨B,hB,d,hd,hmodel⟩ := exists_norm_iteratedDeriv_universalGramKernel_le_exponential_grouped q m i j hm hi hj
  refine ⟨A*Real.exp (2*c*D)+B*Real.exp (2*d*D),by positivity,min c d,lt_min hc hd,?_⟩
  intro n k nodes other hnodes hother a b ha hb r t hr ht hn ho
  rw [groupedDoubleDividedDifference_sub]
  have hK := norm_groupedDoubleDividedDifference_le_twoRay_exponential nodes other hnodes hother a b
    (groupedAnchorNormalizedKernel m _ ε η r t)
    (fun x y hx _hy => (contDiffAt_groupedAnchorNormalizedKernel_left (q+1) m hm ε η r t x y hε hη hx).of_le
      (by exact_mod_cast (show a.val ≤ q+1 by omega)))
    (fun x y hx hy => (contDiffAt_iteratedDeriv_groupedAnchorNormalizedKernel_right (q+1) m a.val hm
      (by omega) ε η r t x y hε hη hx hy).of_le (by exact_mod_cast (show b.val ≤ q+1 by omega)))
    ε η r t D A c hε hη hr ht hD hA.le hc.le hn ho (fun x hx y hy => by
      simpa only [ha,hb] using hactual r t x y hr ht hx.1 hy.1)
  have hU := norm_groupedDoubleDividedDifference_le_twoRay_exponential nodes other hnodes hother a b
    (fun x y => universalGramKernel m (η*y-ε*x))
    (fun x y _hx _hy => (contDiff_grouped_universalGramKernel m a.val (by omega)).contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)))
    (fun x y _hx _hy => contDiffAt_iteratedDeriv_universalTwoRay_right m b.val a.val (by omega) ε η x y hε)
    ε η r t D B d hε hη hr ht hD hB.le hd.le hn ho (fun x _hx y _hy => by
      rw [norm_mixedDeriv_universalTwoRay m a.val b.val ε η x y hε hη,ha,hb]
      simpa only [one_mul] using hmodel 1 (by norm_num) (η*y-ε*x))
  refine (norm_sub_le _ _).trans ((add_le_add hK hU).trans ?_)
  rw [add_mul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_left c d,abs_nonneg (η*t-ε*r)])
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_right c d,abs_nonneg (η*t-ε*r)])

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- Near-tail smallness of the actual grouped atom Gram minus the actual
universal grouped `L²` Gram. The threshold is uniform over all allowed prefix
orders and all node collisions inside the two bounded-diameter groups. -/
theorem gramRemainder_uniform_small (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (ε : ℝ) (hε : ε^2=1) (D L : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∀ δ > 0, ∃ T ≥ 1, ∀ (C E : κ) (i : Fin (G.size C)) (j : Fin (G.size E)),
      i.val ≤ q → j.val ≤ q → T ≤ G.anchorMagnitude ε C → T ≤ G.anchorMagnitude ε E →
      |G.anchorMagnitude ε E-G.anchorMagnitude ε C| ≤ L →
      (∀ a, G.magnitudeNodes ε C a ∈ Set.Icc (G.anchorMagnitude ε C) (G.anchorMagnitude ε C+D)) →
      (∀ b, G.magnitudeNodes ε E b ∈ Set.Icc (G.anchorMagnitude ε E) (G.anchorMagnitude ε E+D)) →
      ‖G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩ -
        G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩‖ ≤ δ := by
  intro δ hδ
  choose T hT hnear using fun p : Fin (q+1) × Fin (q+1) =>
    groupedDoubleDividedDifference_anchorRemainder_uniform_small q m p.1.val p.2.val hm
      (by omega) (by omega) ε hε D L hD hL δ hδ
  obtain ⟨p,hp⟩ := Finite.exists_max T
  refine ⟨T p,hT p,?_⟩
  intro C E i j hi hj hC hE hdist hnodes hother
  let k : Fin (q+1) × Fin (q+1) := (⟨i.val,by omega⟩,⟨j.val,by omega⟩)
  have hC0 : ∀ a, 0 ≤ G.magnitudeNodes ε C a := fun a => by linarith [(hnodes a).1,hT p]
  have hE0 : ∀ b, 0 ≤ G.magnitudeNodes ε E b := fun b => by linarith [(hother b).1,hT p]
  rw [G.norm_gramRemainder_eq_magnitude_DD m _ ε hε C E i j hC0 hE0]
  exact hnear k _ _ (G.magnitudeNodes_injective ε hε C) (G.magnitudeNodes_injective ε hε E)
    i j rfl rfl _ _ ((hp k).trans hC) ((hp k).trans hE) hdist hnodes hother

/-- A common summable off-diagonal envelope for the actual grouped atom
remainder on either fixed ray, with all prefix orders bounded by `q`. -/
theorem exists_gramRemainder_exponential (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (ε : ℝ) (hε : ε^2=1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (C E : κ) (i : Fin (G.size C)) (j : Fin (G.size E)),
      i.val ≤ q → j.val ≤ q → 1 ≤ G.anchorMagnitude ε C → 1 ≤ G.anchorMagnitude ε E →
      (∀ a, G.magnitudeNodes ε C a ∈ Set.Icc (G.anchorMagnitude ε C) (G.anchorMagnitude ε C+D)) →
      (∀ b, G.magnitudeNodes ε E b ∈ Set.Icc (G.anchorMagnitude ε E) (G.anchorMagnitude ε E+D)) →
      ‖G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩ -
        G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩‖ ≤
        A*Real.exp (-c*|G.anchorMagnitude ε E-G.anchorMagnitude ε C|) := by
  choose A hA c hc hdec using fun p : Fin (q+1) × Fin (q+1) =>
    exists_groupedDoubleDividedDifference_anchorRemainder_exponential q m p.1.val p.2.val hm
      (by omega) (by omega) ε hε D hD
  obtain ⟨p,hp⟩ := Finite.exists_max A
  obtain ⟨r,hr⟩ := Finite.exists_min c
  refine ⟨A p,hA p,c r,hc r,?_⟩
  intro C E i j hi hj hC hE hnodes hother
  let k : Fin (q+1) × Fin (q+1) := (⟨i.val,by omega⟩,⟨j.val,by omega⟩)
  have hC0 : ∀ a, 0 ≤ G.magnitudeNodes ε C a := fun a => by linarith [(hnodes a).1]
  have hE0 : ∀ b, 0 ≤ G.magnitudeNodes ε E b := fun b => by linarith [(hother b).1]
  rw [G.norm_gramRemainder_eq_magnitude_DD m _ ε hε C E i j hC0 hE0]
  refine (hdec k _ _ (G.magnitudeNodes_injective ε hε C) (G.magnitudeNodes_injective ε hε E)
    i j rfl rfl _ _ hC hE hnodes hother).trans ?_
  exact mul_le_mul (hp k)
    (Real.exp_le_exp.mpr (by nlinarith [hr k,abs_nonneg (G.anchorMagnitude ε E-G.anchorMagnitude ε C)]))
    (Real.exp_pos _).le (hA p).le

/-- The actual grouped remainder has one off-diagonal exponential envelope
for all four ray pairs and every allowed prefix order. -/
theorem exists_gramRemainder_twoRay_exponential (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (ε η : ℝ), ε^2=1 → η^2=1 →
      ∀ (C E : κ) (i : Fin (G.size C)) (j : Fin (G.size E)),
      i.val ≤ q → j.val ≤ q → 1 ≤ G.anchorMagnitude ε C → 1 ≤ G.anchorMagnitude η E →
      (∀ a, G.magnitudeNodes ε C a ∈ Set.Icc (G.anchorMagnitude ε C) (G.anchorMagnitude ε C+D)) →
      (∀ b, G.magnitudeNodes η E b ∈ Set.Icc (G.anchorMagnitude η E) (G.anchorMagnitude η E+D)) →
      ‖G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩ -
        G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩‖ ≤
        A*Real.exp (-c*|η*G.anchorMagnitude η E-ε*G.anchorMagnitude ε C|) := by
  let sign : Bool → ℝ := fun b => if b then 1 else -1
  have hsign (b : Bool) : (sign b)^2=1 := by cases b <;> norm_num [sign]
  choose A hA c hc hdec using fun p : (Bool × Bool) × (Fin (q+1) × Fin (q+1)) =>
    exists_groupedDoubleDividedDifference_twoRayRemainder_exponential q m p.2.1.val p.2.2.val hm
      (by omega) (by omega) (sign p.1.1) (sign p.1.2) (hsign _) (hsign _) D hD
  obtain ⟨p,hp⟩ := Finite.exists_max A
  obtain ⟨r,hr⟩ := Finite.exists_min c
  refine ⟨A p,hA p,c r,hc r,?_⟩
  intro ε η hε hη C E i j hi hj hC hE hnodes hother
  have hsrep (σ : ℝ) (hσ : σ^2=1) : ∃ b : Bool, sign b=σ := by
    rcases sq_eq_one_iff.mp hσ with rfl | rfl
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  obtain ⟨e,he⟩ := hsrep ε hε
  obtain ⟨f,hf⟩ := hsrep η hη
  let k : (Bool × Bool) × (Fin (q+1) × Fin (q+1)) := ((e,f),(⟨i.val,by omega⟩,⟨j.val,by omega⟩))
  have hC0 : ∀ a, 0 ≤ G.magnitudeNodes ε C a := fun a => by linarith [(hnodes a).1]
  have hE0 : ∀ b, 0 ≤ G.magnitudeNodes η E b := fun b => by linarith [(hother b).1]
  rw [G.norm_gramRemainder_eq_twoRay_DD m _ ε η hε hη C E i j hC0 hE0]
  have hentry := hdec k (G.magnitudeNodes ε C) (G.magnitudeNodes η E)
    (G.magnitudeNodes_injective ε hε C) (G.magnitudeNodes_injective η hη E)
    i j rfl rfl _ _ hC hE hnodes hother
  dsimp only [k] at hentry
  rw [he,hf] at hentry
  refine hentry.trans ?_
  exact mul_le_mul (hp k)
    (Real.exp_le_exp.mpr (by nlinarith [hr k,abs_nonneg (η*G.anchorMagnitude η E-ε*G.anchorMagnitude ε C)]))
    (Real.exp_pos _).le (hA p).le

/-- Uniform near-tail smallness in signed anchor distance. Opposite rays
cannot enter a fixed near band once both anchor magnitudes exceed its width. -/
theorem gramRemainder_twoRay_uniform_small (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (D L : ℝ) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∀ δ > 0, ∃ T ≥ 1, ∀ (ε η : ℝ), ε^2=1 → η^2=1 →
      ∀ (C E : κ) (i : Fin (G.size C)) (j : Fin (G.size E)),
      i.val ≤ q → j.val ≤ q → T ≤ G.anchorMagnitude ε C → T ≤ G.anchorMagnitude η E →
      |η*G.anchorMagnitude η E-ε*G.anchorMagnitude ε C| ≤ L →
      (∀ a, G.magnitudeNodes ε C a ∈ Set.Icc (G.anchorMagnitude ε C) (G.anchorMagnitude ε C+D)) →
      (∀ b, G.magnitudeNodes η E b ∈ Set.Icc (G.anchorMagnitude η E) (G.anchorMagnitude η E+D)) →
      ‖G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩ -
        G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨C,i⟩ ⟨E,j⟩‖ ≤ δ := by
  intro δ hδ
  obtain ⟨T,hT,hplus⟩ := G.gramRemainder_uniform_small q m hm 1 (by norm_num) D L hD hL δ hδ
  obtain ⟨U,hU,hminus⟩ := G.gramRemainder_uniform_small q m hm (-1) (by norm_num) D L hD hL δ hδ
  refine ⟨max (max T U) (L+1),le_trans hT ((le_max_left T U).trans (le_max_left _ _)),?_⟩
  intro ε η hε hη C E i j hi hj hC hE hdist hn ho
  have hCT : T ≤ G.anchorMagnitude ε C := ((le_max_left T U).trans (le_max_left _ _)).trans hC
  have hET : T ≤ G.anchorMagnitude η E := ((le_max_left T U).trans (le_max_left _ _)).trans hE
  have hCU : U ≤ G.anchorMagnitude ε C := ((le_max_right T U).trans (le_max_left _ _)).trans hC
  have hEU : U ≤ G.anchorMagnitude η E := ((le_max_right T U).trans (le_max_left _ _)).trans hE
  have hCL : L+1 ≤ G.anchorMagnitude ε C := (le_max_right _ _).trans hC
  have hEL : L+1 ≤ G.anchorMagnitude η E := (le_max_right _ _).trans hE
  rcases sq_eq_one_iff.mp hε with rfl | rfl <;> rcases sq_eq_one_iff.mp hη with rfl | rfl
  · exact hplus C E i j hi hj hCT hET (by simpa only [one_mul] using hdist) hn ho
  · simp only [one_mul,neg_one_mul] at hdist
    have ha := (abs_le.mp hdist).1
    linarith
  · simp only [one_mul,neg_one_mul,sub_neg_eq_add] at hdist
    have ha := (abs_le.mp hdist).2
    linarith
  · apply hminus C E i j hi hj hCU hEU _ hn ho
    simpa only [neg_one_mul,neg_sub_neg,abs_sub_comm] using hdist

/-- The genuine grouped Gram remainder on selected tail clusters is a
compact self-adjoint coefficient operator. Every hypothesis is finite cluster
geometry: no kernel estimate, Bessel bound or compactness is assumed. The
central complement is deliberately not forced through a square-root chart. -/
theorem exists_compact_gramRemainder_on_tail (P : κ → Prop)
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (ray : {C : κ // P C} → ℝ) (hray : ∀ C, (ray C)^2=1)
    (D d : ℝ) (hD : 0 ≤ D) (hd : 0 < d)
    (hsize : ∀ C : {C : κ // P C}, G.size C.val ≤ q)
    (hanchor : ∀ C : {C : κ // P C}, 1 ≤ G.anchorMagnitude (ray C) C.val)
    (hdiam : ∀ (C : {C : κ // P C}) a, G.magnitudeNodes (ray C) C.val a ∈
      Set.Icc (G.anchorMagnitude (ray C) C.val) (G.anchorMagnitude (ray C) C.val+D))
    (hsep : ∀ C E : {C : κ // P C}, C ≠ E →
      d ≤ |G.realNodes C.val (G.anchor C.val)-G.realNodes E.val (G.anchor E.val)|) :
    ∃ A : CoefficientSpace (Σ C : {C : κ // P C}, Fin (G.size C.val)) →L[ℂ]
        CoefficientSpace (Σ C : {C : κ // P C}, Fin (G.size C.val)),
      IsSelfAdjoint A ∧ IsCompactOperator A ∧ ∀ i j,
        inner ℂ (coefficientAtom i) (A (coefficientAtom j)) =
          G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩ -
          G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩ := by
  classical
  let size := fun C : {C : κ // P C} => G.size C.val
  let s := fun C : {C : κ // P C} => G.realNodes C.val (G.anchor C.val)
  let K := fun i j : Σ C : {C : κ // P C}, Fin (size C) =>
    G.gramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩ -
    G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) ⟨i.1.val,i.2⟩ ⟨j.1.val,j.2⟩
  have hs (C : {C : κ // P C}) : ray C*G.anchorMagnitude (ray C) C.val=s C :=
    (congrFun (G.realNodes_eq_sign_magnitudeNodes (ray C) (hray C) C.val) (G.anchor C.val)).symm
  have hsabs (C : {C : κ // P C}) : |s C|=G.anchorMagnitude (ray C) C.val := by
    rw [← hs C,abs_mul,abs_of_nonneg (show 0 ≤ G.anchorMagnitude (ray C) C.val by linarith [hanchor C])]
    have he : |ray C|=1 := by nlinarith [sq_abs (ray C),abs_nonneg (ray C),hray C]
    rw [he,one_mul]
  obtain ⟨B,hB,c,hc,hbound⟩ := G.exists_gramRemainder_twoRay_exponential q m hm D hD
  have hherm (i j : Σ C : {C : κ // P C}, Fin (size C)) : starRingEnd ℂ (K j i)=K i j := by
    simp only [K,gramKernel,universalGroupedGramKernel,map_sub,inner_conj_symm]
  have hdec (i j : Σ C : {C : κ // P C}, Fin (size C)) :
      ‖K i j‖ ≤ B*Real.exp (-c*|s j.1-s i.1|) := by
    have hi : size i.1 ≤ q := hsize i.1
    have hj : size j.1 ≤ q := hsize j.1
    have h := hbound (ray i.1) (ray j.1) (hray i.1) (hray j.1) i.1.val j.1.val i.2 j.2
      (by have := i.2.isLt; omega) (by have := j.2.isLt; omega) (hanchor i.1) (hanchor j.1)
      (hdiam i.1) (hdiam j.1)
    simpa only [hs] using h
  have hnear : ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 0, ∀ i j : Σ C : {C : κ // P C}, Fin (size C),
      T ≤ |s i.1| → T ≤ |s j.1| → |s j.1-s i.1| ≤ L → ‖K i j‖ ≤ δ := by
    intro L hL δ hδ
    obtain ⟨T,hT,hsmall⟩ := G.gramRemainder_twoRay_uniform_small q m hm D L hD hL δ hδ
    refine ⟨T,by linarith,?_⟩
    intro i j hiT hjT hij
    have hi : size i.1 ≤ q := hsize i.1
    have hj : size j.1 ≤ q := hsize j.1
    apply hsmall (ray i.1) (ray j.1) (hray i.1) (hray j.1) i.1.val j.1.val i.2 j.2
      (by have := i.2.isLt; omega) (by have := j.2.isLt; omega)
      (by simpa only [hsabs] using hiT) (by simpa only [hsabs] using hjT)
      (by simpa only [hs] using hij) (hdiam i.1) (hdiam j.1)
  obtain ⟨A,hA,hcompact,_hnorm,hentry⟩ := exists_compact_grouped_coefficientOperator size hsize s hd hB hc
    hsep K hherm hdec hnear
  exact ⟨A,hA,hcompact,hentry⟩

end OrderedCarrierGrouping

end

end MeyerGeneralProblem
