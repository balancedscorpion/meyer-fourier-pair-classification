module

public import MeyerGeneralProblem.Distribution.GaussianHeatInitialValue

@[expose] public section

/-!
# Local heat evolution with an advanced compact part

The compact restriction starts at time `τ`, while the exterior density
starts at time zero. Inside the clipping interval the latter has zero
initial value. Both sides of the evolution have explicit limits as the
parameters approach zero.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The compact part of the heat flow can start at an earlier time
relative to the exterior part. -/
def localizedGaussianEvolution (l r : ℝ) (f : ℝ → ℝ) (τ t y : ℝ) : ℝ :=
  realGaussianSmoothing (t + τ) ((Icc l r).indicator f) y +
    realGaussianSmoothing t ((Icc l r)ᶜ.indicator f) y

/-- The integral formula evaluates to zero at heat parameter zero. -/
@[simp]
theorem realGaussianSmoothing_zero (f : ℝ → ℝ) (y : ℝ) : realGaussianSmoothing 0 f y = 0 := by
  simp [realGaussianSmoothing]

private theorem continuousAt_realGaussianSmoothing_pos {f : ℝ → ℝ}
    (hf : Integrable f) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => realGaussianSmoothing q.1 f q.2) p := by
  have hp' : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  exact (continuousOn_realGaussianSmoothing_of_integrable hf p hp').continuousAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp')

private theorem continuousWithinAt_realGaussianSmoothing_zero_of_ae_zero_near
    {f : ℝ → ℝ} (hf : Integrable f) {δ : ℝ} (hδ : 0 < δ) (y : ℝ)
    (hZero : ∀ᵐ x : ℝ ∂volume, |x - y| < δ → f x = 0) :
    ContinuousWithinAt (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)) (0, y) := by
  let S₀ : Set (ℝ × ℝ) := {(0 : ℝ)} ×ˢ (univ : Set ℝ)
  let Spos : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
  have hEq : Ici (0 : ℝ) ×ˢ (univ : Set ℝ) = S₀ ∪ Spos := by
    ext p
    simp only [S₀, Spos, mem_union, mem_prod, mem_Ici, mem_Ioi, mem_singleton_iff, mem_univ, and_true]
    constructor
    · intro h
      exact (lt_or_eq_of_le h).elim Or.inr (fun he => Or.inl he.symm)
    · rintro (he | h)
      · rw [he]
      · exact h.le
  have hAtZero : Tendsto (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
      (𝓝[S₀] (0, y)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin (s := S₀)] with p hp
    rw [show p.1 = 0 from hp.1, realGaussianSmoothing_zero]
  change Tendsto (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
    (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set ℝ)] (0, y)) (𝓝 (realGaussianSmoothing 0 f y))
  rw [hEq, nhdsWithin_union, realGaussianSmoothing_zero]
  exact hAtZero.sup (tendsto_realGaussianSmoothing_zero_of_ae_zero_near hf hδ y hZero)

/-- The advanced compact part and the exterior heat flow are jointly
continuous down to time zero on the interior of the clipping interval. -/
theorem continuousOn_localizedGaussianEvolution {f : ℝ → ℝ} (hf : Integrable f)
    (l r : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ContinuousOn (fun p : ℝ × ℝ => localizedGaussianEvolution l r f τ p.1 p.2)
      (Ici (0 : ℝ) ×ˢ Ioo l r) := by
  let g := (Icc l r).indicator f
  let h := (Icc l r)ᶜ.indicator f
  have hg : Integrable g := hf.indicator measurableSet_Icc
  have hh : Integrable h := hf.indicator measurableSet_Icc.compl
  intro p hp
  have ht : 0 ≤ p.1 := hp.1
  have hy : p.2 ∈ Ioo l r := hp.2
  have hG : ContinuousAt (fun q : ℝ × ℝ => realGaussianSmoothing (q.1 + τ) g q.2) p := by
    let A (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + τ, q.2)
    have hA : Continuous A := by unfold A; fun_prop
    have hPos : 0 < (A p).1 := add_pos_of_nonneg_of_pos ht hτ
    have hK : ContinuousAt (fun q : ℝ × ℝ => realGaussianSmoothing q.1 g q.2) (A p) :=
      continuousAt_realGaussianSmoothing_pos hg hPos
    exact hK.comp (hA.continuousAt (x := p))
  have hH : ContinuousWithinAt (fun q : ℝ × ℝ => realGaussianSmoothing q.1 h q.2)
      (Ici (0 : ℝ) ×ˢ Ioo l r) p := by
    rcases ht.eq_or_lt with htZero | htPos
    · have hpEq : p = (0, p.2) := Prod.ext htZero.symm rfl
      rw [hpEq]
      obtain ⟨δ, hδ, hB⟩ := Metric.isOpen_iff.mp isOpen_Ioo p.2 hy
      have hZero : ∀ᵐ x : ℝ ∂volume, |x - p.2| < δ → h x = 0 := by
        filter_upwards with x hx
        have hxB : x ∈ Metric.ball p.2 δ := by
          simpa only [Metric.mem_ball, Real.dist_eq] using hx
        exact indicator_of_notMem (show x ∉ (Icc l r)ᶜ from fun hn =>
          hn (Ioo_subset_Icc_self (hB hxB))) _
      exact (continuousWithinAt_realGaussianSmoothing_zero_of_ae_zero_near hh hδ p.2 hZero).mono
        (prod_mono subset_rfl (subset_univ _))
    · exact (continuousAt_realGaussianSmoothing_pos hh htPos).continuousWithinAt
  exact hG.continuousWithinAt.add hH

/-- The localized evolution satisfies the heat equation at every
positive time for nonnegative advancement of the compact part. -/
theorem hasDerivAt_localizedGaussianEvolution_time {f : ℝ → ℝ} (hf : Integrable f)
    (l r : ℝ) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => localizedGaussianEvolution l r f τ s y)
      (deriv (deriv (localizedGaussianEvolution l r f τ t)) y / 4) t :=
  hasDerivAt_add_realGaussianSmoothing_shift_time (hf.indicator measurableSet_Icc)
    (hf.indicator measurableSet_Icc.compl) τ ht (add_pos_of_pos_of_nonneg ht hτ) y

/-- At any fixed positive time the localized evolution converges to the
original heat flow as the advancement of the compact part tends to zero. -/
theorem tendsto_localizedGaussianEvolution_of_integrable {f : ℝ → ℝ} (hf : Integrable f)
    (l r : ℝ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Tendsto (fun τ => localizedGaussianEvolution l r f τ t y) (𝓝 0)
      (𝓝 (realGaussianSmoothing t f y)) := by
  let g := (Icc l r).indicator f
  let h := (Icc l r)ᶜ.indicator f
  have hg : Integrable g := hf.indicator measurableSet_Icc
  have hh : Integrable h := hf.indicator measurableSet_Icc.compl
  have hgCont : ContinuousAt (fun τ : ℝ => realGaussianSmoothing (t + τ) g y) 0 := by
    let A (τ : ℝ) : ℝ × ℝ := (t + τ, y)
    have hA : Continuous A := by unfold A; fun_prop
    have hPos : 0 < (A 0).1 := by dsimp [A]; linarith
    have hK : ContinuousAt (fun q : ℝ × ℝ => realGaussianSmoothing q.1 g q.2) (A 0) :=
      continuousAt_realGaussianSmoothing_pos hg hPos
    exact hK.comp (hA.continuousAt (x := 0))
  have hS : (fun x => g x + h x) = f := by
    funext x
    by_cases hx : x ∈ Icc l r
    · rw [show g x = f x from indicator_of_mem hx _,
        show h x = 0 from indicator_of_notMem (show x ∉ (Icc l r)ᶜ from fun hn => hn hx) _, add_zero]
    · rw [show g x = 0 from indicator_of_notMem hx _,
        show h x = f x from indicator_of_mem (show x ∈ (Icc l r)ᶜ from hx) _, zero_add]
  have hEq : realGaussianSmoothing t g y + realGaussianSmoothing t h y =
      realGaussianSmoothing t f y := by rw [← realGaussianSmoothing_fun_add hg hh ht, hS]
  have hT := hgCont.tendsto.add_const (realGaussianSmoothing t h y)
  simpa only [localizedGaussianEvolution, g, h, add_zero, hEq] using hT

private theorem tendsto_realGaussianSmoothing_initial_time {f : ℝ → ℝ} (hf : Integrable f)
    (y : ℝ) (hy : ContinuousAt f y) :
    Tendsto (fun t => realGaussianSmoothing t f y) (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  have hPos : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  have hEmbed : Tendsto (fun t : ℝ => (t, y)) (𝓝[>] (0 : ℝ))
      (𝓝[Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)] (0, y)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hPos.mono fun t ht => ⟨ht, mem_univ _⟩⟩
    exact (tendsto_id.prodMk_nhds tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  exact (tendsto_realGaussianSmoothing_initial_of_integrable hf y hy).comp hEmbed

private theorem exists_pos_lt_of_eventually_nhdsGT {P : ℝ → Prop}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ ε > 0, ∀ t, 0 < t → t < ε → P t := by
  obtain ⟨V, hV, hSub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ε, hε, fun t ht he => hSub ⟨hBall ?_, ht⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using he

/-- At a nonzero continuity point strictly inside the clipping interval,
the localized evolution keeps the original sign uniformly for all
nonnegative times and positive advancements whose sum is sufficiently small. -/
theorem exists_time_bound_localizedGaussianEvolution_sign
    {f : ℝ → ℝ} (hf : Integrable f) {l r y : ℝ} (hy : y ∈ Ioo l r)
    (hCont : ContinuousAt f y) (hNonzero : f y ≠ 0) :
    ∃ ε > 0, ∀ t τ, 0 ≤ t → 0 < τ → t + τ < ε →
      0 < f y * localizedGaussianEvolution l r f τ t y := by
  let g := (Icc l r).indicator f
  let h := (Icc l r)ᶜ.indicator f
  have hg : Integrable g := hf.indicator measurableSet_Icc
  have hh : Integrable h := hf.indicator measurableSet_Icc.compl
  have hgEq : g =ᶠ[𝓝 y] f := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx
    exact indicator_of_mem (Ioo_subset_Icc_self hx) _
  have hhEq : h =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx
    exact indicator_of_notMem (show x ∉ (Icc l r)ᶜ from fun hn => hn (Ioo_subset_Icc_self hx)) _
  have hG := tendsto_realGaussianSmoothing_initial_time hg y (hCont.congr_of_eventuallyEq hgEq)
  have hH := tendsto_realGaussianSmoothing_initial_time hh y
    (continuousAt_const.congr_of_eventuallyEq hhEq)
  rw [hgEq.eq_of_nhds] at hG
  rw [show h y = 0 from hhEq.eq_of_nhds] at hH
  let d := |f y| / 3
  have hd : 0 < d := div_pos (abs_pos.mpr hNonzero) (by norm_num)
  obtain ⟨εg, hεg, hGClose⟩ := exists_pos_lt_of_eventually_nhdsGT
    (hG.eventually (Metric.ball_mem_nhds _ hd))
  obtain ⟨εh, hεh, hHClose⟩ := exists_pos_lt_of_eventually_nhdsGT
    (hH.eventually (Metric.ball_mem_nhds _ hd))
  refine ⟨min εg εh, lt_min hεg hεh, fun t τ ht hτ hTime => ?_⟩
  have hPos : 0 < t + τ := add_pos_of_nonneg_of_pos ht hτ
  have hGDiff : |realGaussianSmoothing (t + τ) g y - f y| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hGClose _ hPos (hTime.trans_le (min_le_left _ _))
  have hHAbs : |realGaussianSmoothing t h y| < d := by
    rcases ht.eq_or_lt with htZero | htPos
    · simpa only [← htZero, realGaussianSmoothing_zero, abs_zero] using hd
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
        hHClose t htPos ((lt_add_of_pos_right t hτ).trans (hTime.trans_le (min_le_right _ _)))
  have hDiff : |localizedGaussianEvolution l r f τ t y - f y| < |f y| := by
    change |realGaussianSmoothing (t + τ) g y + realGaussianSmoothing t h y - f y| < _
    rw [add_sub_right_comm]
    exact (abs_add_le _ _).trans_lt (by
      dsimp [d] at hGDiff hHAbs
      linarith [abs_pos.mpr hNonzero])
  rcases lt_or_gt_of_ne hNonzero with hn | hp
  · rw [abs_of_neg hn] at hDiff
    exact mul_pos_of_neg_of_neg hn (by linarith [(abs_lt.mp hDiff).2])
  · rw [abs_of_pos hp] at hDiff
    exact mul_pos hp (by linarith [(abs_lt.mp hDiff).1])

/-- Clipping an observation interval at two collars of constant strict
sign preserves every witnessed alternation count. -/
theorem hasSignAlternations_on_Icc_of_same_sign_collars {f : ℝ → ℝ}
    {l a b r : ℝ} (hab : a ≤ b)
    (hLeft : ∀ x ∈ Icc l a, 0 < f a * f x)
    (hRight : ∀ x ∈ Icc b r, 0 < f b * f x) {n : ℕ}
    (h : HasSignAlternations f (Icc l r) n) :
    HasSignAlternations f (Icc a b) n := by
  obtain ⟨x, hx, hMem, hSigns⟩ := h
  let clip (t : ℝ) := max a (min b t)
  have hRange (t : ℝ) : clip t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hMono : Monotone clip := fun _ _ hle => max_le_max le_rfl (min_le_min le_rfl hle)
  have hKeep {t : ℝ} (ht : t ∈ Icc l r) (hNonzero : f t ≠ 0) :
      0 < f (clip t) * f t := by
    by_cases hLo : t ≤ a
    · have hEq : clip t = a := max_eq_left ((min_le_right b t).trans hLo)
      rw [hEq]
      exact hLeft t ⟨ht.1, hLo⟩
    by_cases hHi : b ≤ t
    · have hEq : clip t = b := by dsimp only [clip]; rw [min_eq_left hHi, max_eq_right hab]
      rw [hEq]
      exact hRight t ⟨hHi, ht.2⟩
    have hEq : clip t = t := by
      dsimp only [clip]
      rw [min_eq_right (le_of_not_ge hHi), max_eq_right (le_of_not_ge hLo)]
    rw [hEq]
    exact mul_self_pos.mpr hNonzero
  have hAlt (i : Fin n) : f (clip (x i.castSucc)) * f (clip (x i.succ)) < 0 := by
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp (ne_of_lt (hSigns i))
    have hProd := mul_pos (hKeep (hMem i.castSucc) ha) (hKeep (hMem i.succ) hb)
    rw [mul_mul_mul_comm] at hProd
    exact ((mul_pos_iff.mp hProd).resolve_left (fun hpos => (hSigns i).not_gt hpos.2)).1
  refine ⟨fun i => clip (x i), Fin.strictMono_iff_lt_succ.mpr fun i => ?_,
    fun i => hRange (x i), hAlt⟩
  refine lt_of_le_of_ne (hMono (hx.monotone Fin.castSucc_lt_succ.le)) fun he => ?_
  have hm := hAlt i
  rw [he] at hm
  exact (not_lt_of_ge (mul_self_nonneg _)) hm

/-- Nonzero endpoints at continuity points allow enlarging an interval
on both sides while preserving every witnessed sign count on the original
interval. -/
theorem exists_extended_Icc_same_signAlternations {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (ha₀ : f a ≠ 0) (hb₀ : f b ≠ 0) :
    ∃ l r, l < a ∧ b < r ∧
      ∀ n, HasSignAlternations f (Icc l r) n → HasSignAlternations f (Icc a b) n := by
  have haCont : ContinuousAt (fun x => f a * f x) a := continuousAt_const.mul ha
  have hbCont : ContinuousAt (fun x => f b * f x) b := continuousAt_const.mul hb
  obtain ⟨δa, hδa, hA⟩ := Metric.mem_nhds_iff.mp
    (haCont.tendsto.eventually (Ioi_mem_nhds (mul_self_pos.mpr ha₀)))
  obtain ⟨δb, hδb, hB⟩ := Metric.mem_nhds_iff.mp
    (hbCont.tendsto.eventually (Ioi_mem_nhds (mul_self_pos.mpr hb₀)))
  let l := a - δa / 2
  let r := b + δb / 2
  have hL (x : ℝ) (hx : x ∈ Icc l a) : 0 < f a * f x := by
    apply hA
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    have hxl : a - δa / 2 ≤ x := hx.1
    linarith
  have hR (x : ℝ) (hx : x ∈ Icc b r) : 0 < f b * f x := by
    apply hB
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have hxr : x ≤ b + δb / 2 := hx.2
    linarith
  refine ⟨l, r, ?_, ?_, fun n hn => hasSignAlternations_on_Icc_of_same_sign_collars hab hL hR hn⟩
  · dsimp [l]
    linarith
  · dsimp [r]
    linarith

/-- The ordered sign comparison for a classical heat solution on a
rectangle with nonzero fixed lateral signs. The allowed loss is four
sign alternations. -/
def HeatRectangleSignAlternationComparison : Prop :=
  ∀ (u : ℝ → ℝ → ℝ) (a b T : ℝ), a < b → 0 < T →
    ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 T ×ˢ Icc a b) →
    (∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b,
      DifferentiableAt ℝ (u t) x ∧ DifferentiableAt ℝ (deriv (u t)) x ∧
        HasDerivAt (fun s => u s x) (deriv (deriv (u t)) x / 4) t) →
    (∃ A B : ℝ, ∀ t ∈ Icc 0 T, 0 < A * u t a ∧ 0 < B * u t b) →
    ∀ n, HasSignAlternations (u T) (Icc a b) (n + 4) → HasSignAlternations (u 0) (Icc a b) n

private theorem differentiableAt_localizedGaussianEvolution_space
    {f : ℝ → ℝ} (hf : Integrable f) (l r : ℝ) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 < t)
    (x : ℝ) :
    DifferentiableAt ℝ (localizedGaussianEvolution l r f τ t) x ∧
      DifferentiableAt ℝ (deriv (localizedGaussianEvolution l r f τ t)) x := by
  let G := realGaussianSmoothing (t + τ) ((Icc l r).indicator f)
  let H := realGaussianSmoothing t ((Icc l r)ᶜ.indicator f)
  have hG (y : ℝ) : DifferentiableAt ℝ G y ∧ DifferentiableAt ℝ (deriv G) y :=
    differentiableAt_realGaussianSmoothing_twice (hf.indicator measurableSet_Icc)
      (add_pos_of_pos_of_nonneg ht hτ) y
  have hH (y : ℝ) : DifferentiableAt ℝ H y ∧ DifferentiableAt ℝ (deriv H) y :=
    differentiableAt_realGaussianSmoothing_twice (hf.indicator measurableSet_Icc.compl) ht y
  have hEq : deriv (localizedGaussianEvolution l r f τ t) = deriv G + deriv H :=
    funext fun y => deriv_add (hG y).1 (hH y).1
  refine ⟨(hG x).1.add (hH x).1, ?_⟩
  rw [hEq]
  exact (hG x).2.add (hH x).2

/-- The ordered rectangle comparison implies the local sign-change
bound for the full Gaussian evolution at two nonzero continuity points.
The clipping, continuity, boundary signs and passage to untruncated
heat flow are obtained from the original integrable density. -/
theorem eventually_local_gaussian_signAlternations_of_rectangle_comparison
    (hRect : HeatRectangleSignAlternationComparison)
    {f : ℝ → ℝ} (hf : Integrable f) {a b : ℝ} (hab : a < b)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (ha₀ : f a ≠ 0) (hb₀ : f b ≠ 0) :
    ∃ T > 0, ∀ t ∈ Ioo 0 T, ∀ n,
      HasSignAlternations (realGaussianSmoothing t f) (Icc a b) (n + 4) →
        HasSignAlternations f (Icc a b) n := by
  obtain ⟨l, r, hl, hr, hClip⟩ := exists_extended_Icc_same_signAlternations hab.le ha hb ha₀ hb₀
  have hla : a ∈ Ioo l r := ⟨hl, hab.trans hr⟩
  have hlb : b ∈ Ioo l r := ⟨hl.trans hab, hr⟩
  obtain ⟨εa, hεa, hASign⟩ := exists_time_bound_localizedGaussianEvolution_sign hf hla ha ha₀
  obtain ⟨εb, hεb, hBSign⟩ := exists_time_bound_localizedGaussianEvolution_sign hf hlb hb hb₀
  let T := min εa εb / 2
  have hT : 0 < T := half_pos (lt_min hεa hεb)
  refine ⟨T, hT, fun t ht n hAlt => ?_⟩
  have hAlt' : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      HasSignAlternations (localizedGaussianEvolution l r f τ t) (Icc a b) (n + 4) :=
    hAlt.eventually_of_pointwise_tendsto fun x _ =>
      (tendsto_localizedGaussianEvolution_of_integrable hf l r ht.1 x).mono_left nhdsWithin_le_nhds
  have hτRange : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioo 0 T := by
    have hp : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    have hq : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Iio T := nhdsWithin_le_nhds (Iio_mem_nhds hT)
    filter_upwards [hp, hq] with τ hp hq
    exact ⟨hp, hq⟩
  obtain ⟨τ, hτAlt, hτ⟩ := (hAlt'.and hτRange).exists
  let U := localizedGaussianEvolution l r f τ
  have hCont : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 t ×ˢ Icc a b) :=
    (continuousOn_localizedGaussianEvolution hf l r hτ.1).mono fun p hp =>
      ⟨hp.1.1, ⟨hl.trans_le hp.2.1, hp.2.2.trans_lt hr⟩⟩
  have hEq (s : ℝ) (hs : s ∈ Ioc 0 t) (x : ℝ) (_ : x ∈ Ioo a b) :
      DifferentiableAt ℝ (U s) x ∧ DifferentiableAt ℝ (deriv (U s)) x ∧
        HasDerivAt (fun w => U w x) (deriv (deriv (U s)) x / 4) s := by
    obtain ⟨h₁, h₂⟩ := differentiableAt_localizedGaussianEvolution_space hf l r hτ.1.le hs.1 x
    exact ⟨h₁, h₂, hasDerivAt_localizedGaussianEvolution_time hf l r hτ.1.le hs.1 x⟩
  have hSides : ∃ A B : ℝ, ∀ s ∈ Icc 0 t, 0 < A * U s a ∧ 0 < B * U s b := by
    refine ⟨f a, f b, fun s hs => ?_⟩
    have hsTime : s + τ < min εa εb := by
      have hs' : s < T := hs.2.trans_lt ht.2
      have hτ' : τ < T := hτ.2
      dsimp only [T] at hs' hτ'
      linarith
    exact ⟨hASign s τ hs.1 hτ.1 (hsTime.trans_le (min_le_left _ _)),
      hBSign s τ hs.1 hτ.1 (hsTime.trans_le (min_le_right _ _))⟩
  have hInitial : HasSignAlternations (U 0) (Icc a b) n :=
    hRect U a b t hab ht.1 hCont hEq hSides n hτAlt
  have hInitial' : HasSignAlternations (realGaussianSmoothing τ ((Icc l r).indicator f)) univ n := by
    have hEq₀ : U 0 = realGaussianSmoothing τ ((Icc l r).indicator f) := by
      funext x
      simp [U, localizedGaussianEvolution]
    rw [hEq₀] at hInitial
    exact hInitial.mono (subset_univ _)
  exact hClip n (hasSignAlternations_on_Icc_of_realGaussianSmoothing_indicator
    hτ.1 (hl.le.trans (hab.le.trans hr.le)) hf.integrableOn hInitial')

end
end MeyerGeneralProblem
