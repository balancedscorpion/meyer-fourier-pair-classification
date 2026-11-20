module

public import MeyerGeneralProblem.Distribution.HeatedRayOscillation
public import MeyerGeneralProblem.Distribution.HeatRectangleSignPaths

@[expose] public section

/-!
# Heat transfer across a terminal zero interval

If the original density has finite variation of sign on compact
intervals, the first nonzero values after a cutoff have one weak sign
on a small collar. An endpoint there permits the local heat comparison.
Returning to the cutoff costs at most one alternation.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform Topology

private theorem hasSignAlternations_of_both_signs_near_right
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hBoth : ∀ v > a, (∃ x ∈ Ioo a v, f x < 0) ∧ (∃ x ∈ Ioo a v, 0 < f x))
    (n : ℕ) : HasSignAlternations f (Ioo a b) n := by
  have hSeq : ∃ x : Fin (n + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ Ioo a b) ∧
      f (x 0) ≠ 0 ∧ ∀ i : Fin n, f (x i.castSucc) * f (x i.succ) < 0 := by
    induction n with
    | zero =>
      obtain ⟨x, hx, hf⟩ := (hBoth b hab).1
      refine ⟨fun _ => x, ?_, fun _ => hx, hf.ne, fun i => Fin.elim0 i⟩
      intro i j hij
      exact (hij.ne (Subsingleton.elim (α := Fin 1) i j)).elim
    | succ n ih =>
      obtain ⟨x, hMono, hMem, hFirst, hAlt⟩ := ih
      obtain ⟨y, hy, hSign⟩ : ∃ y ∈ Ioo a (x 0), f y * f (x 0) < 0 := by
        rcases lt_or_gt_of_ne hFirst with hNeg | hPos
        · obtain ⟨y, hy, hyPos⟩ := (hBoth (x 0) (hMem 0).1).2
          exact ⟨y, hy, mul_neg_of_pos_of_neg hyPos hNeg⟩
        · obtain ⟨y, hy, hyNeg⟩ := (hBoth (x 0) (hMem 0).1).1
          exact ⟨y, hy, mul_neg_of_neg_of_pos hyNeg hPos⟩
      refine ⟨Fin.cons y x, Fin.strictMono_cons.mpr
        ⟨fun i => hy.2.trans_le (hMono.monotone (Fin.zero_le i)), hMono⟩, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using (show y ∈ Ioo a b from ⟨hy.1, hy.2.trans (hMem 0).2⟩)
        · simpa only [Fin.cons_succ] using hMem j
      · intro he
        simp only [Fin.cons_zero] at he
        exact hSign.ne (by simp only [he, zero_mul])
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hSign
        · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hAlt j
  obtain ⟨x, hMono, hMem, _, hSign⟩ := hSeq
  exact ⟨x, hMono, hMem, hSign⟩

private theorem exists_nonzero_endpoint_with_weak_sign_collar
    {f : ℝ → ℝ} (hf : Continuous f) (hSupport : ∀ r : ℝ, ∃ x > r, f x ≠ 0)
    (hFinite : ∀ r : ℝ, ∃ n : ℕ, ¬ HasSignAlternations f (Icc 0 r) n)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ b > r, f b ≠ 0 ∧
      ((∀ x ∈ Ioc r b, 0 ≤ f x) ∨ (∀ x ∈ Ioc r b, f x ≤ 0)) := by
  let S := {x : ℝ | r < x ∧ f x ≠ 0}
  have hS : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := hSupport r
    exact ⟨x, hx, hfx⟩
  have hBound : BddBelow S := ⟨r, fun _ hy => hy.1.le⟩
  let a := sInf S
  have hInf : IsGLB S a := isGLB_csInf hS hBound
  have hra : r ≤ a := le_csInf hS fun _ hy => hy.1.le
  have ha : a ∉ S := by
    intro ha
    have hOpen : IsOpen S := isOpen_Ioi.inter (isClosed_eq hf continuous_const).isOpen_compl
    have hNear : ∀ᶠ y in 𝓝[<] a, y ∈ S ∧ y < a := by
      filter_upwards [nhdsWithin_le_nhds (hOpen.mem_nhds ha), self_mem_nhdsWithin]
        with y hy (hya : y < a)
      exact ⟨hy, hya⟩
    obtain ⟨y, hy, hya⟩ := hNear.exists
    exact hya.not_ge (hInf.1 hy)
  have hZero (x : ℝ) (hx : r < x) (hxa : x ≤ a) : f x = 0 := by
    by_contra! he
    have hXS : x ∈ S := ⟨hx, he⟩
    have hEq : x = a := le_antisymm hxa (hInf.1 hXS)
    exact ha (hEq ▸ hXS)
  have hCollar : ∃ u > a, (∀ x ∈ Ioo a u, 0 ≤ f x) ∨ (∀ x ∈ Ioo a u, f x ≤ 0) := by
    by_contra he
    push Not at he
    obtain ⟨N, hN⟩ := hFinite (a + 1)
    have hAlt := hasSignAlternations_of_both_signs_near_right (lt_add_one a) he N
    exact hN (hAlt.mono fun _ hx => ⟨hr.trans (hra.trans hx.1.le), hx.2.le⟩)
  obtain ⟨u, hu, hCollar⟩ := hCollar
  obtain ⟨b, hb, hbu⟩ := exists_lt_of_csInf_lt hS hu
  have hab : a < b := lt_of_le_of_ne (hInf.1 hb) (fun he => ha (he.symm ▸ hb))
  refine ⟨b, hb.1, hb.2, ?_⟩
  rcases hCollar with hPos | hNeg
  · left
    intro x hx
    by_cases hax : a < x
    · exact hPos x ⟨hax, hx.2.trans_lt hbu⟩
    · rw [hZero x hx.1 (le_of_not_gt hax)]
  · right
    intro x hx
    by_cases hax : a < x
    · exact hNeg x ⟨hax, hx.2.trans_lt hbu⟩
    · rw [hZero x hx.1 (le_of_not_gt hax)]

private theorem HasSignAlternations.trim_final_weak_sign
    {f : ℝ → ℝ} {a r b : ℝ} {n : ℕ}
    (h : HasSignAlternations f (Icc a b) (n + 1))
    (hSign : (∀ x ∈ Ioc r b, 0 ≤ f x) ∨ (∀ x ∈ Ioc r b, f x ≤ 0)) :
    HasSignAlternations f (Icc a r) n := by
  obtain ⟨x, hMono, hMem, hAlt⟩ := h
  let i := Fin.last n
  have hi : x i.castSucc ≤ r := by
    by_contra! hi
    have hp := (Fin.strictMono_iff_lt_succ.mp hMono) i
    have hL : x i.castSucc ∈ Ioc r b := ⟨hi, (hMem _).2⟩
    have hR : x i.succ ∈ Ioc r b := ⟨hi.trans hp, (hMem _).2⟩
    have hNonneg : 0 ≤ f (x i.castSucc) * f (x i.succ) := by
      rcases hSign with hPos | hNeg
      · exact mul_nonneg (hPos _ hL) (hPos _ hR)
      · exact mul_nonneg_of_nonpos_of_nonpos (hNeg _ hL) (hNeg _ hR)
    exact (hAlt i).not_ge hNonneg
  refine ⟨x ∘ Fin.castSucc, hMono.comp Fin.strictMono_castSucc, ?_, ?_⟩
  · intro j
    exact ⟨(hMem _).1, (hMono.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))).trans hi⟩
  · intro j
    simpa only [Function.comp_apply, Fin.castSucc_succ] using hAlt j.castSucc

/-- Transfer the uniform heated count to the original positive ray.
An interval ending in a zero gap is extended through a collar of weak
constant sign and then trimmed. -/
theorem eventually_original_positive_ray_signAlternations_of_unbounded_nonzero
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 < s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s))
    (hSupport : ∀ r : ℝ, ∃ x > r, f x ≠ 0)
    {c : ℝ} (hc : c < 2 * s) :
    ∀ᶠ r : ℝ in atTop, ∃ n : ℕ, c * r ≤ (n : ℝ) ∧ HasSignAlternations f (Icc 0 r) n := by
  by_cases hFinite : ∀ b : ℝ, ∃ n : ℕ, ¬ HasSignAlternations f (Icc 0 b) n
  · obtain ⟨d, hd, hds⟩ := exists_between (max_lt (show (0 : ℝ) < 2 * s by positivity) hc)
    have hdPos : 0 < d := (le_max_left _ _).trans_lt hd
    have hcd : c < d := (le_max_right _ _).trans_lt hd
    obtain ⟨κ, hκ, R₁, hHeat⟩ :=
      exists_eventually_heatSignAlternations_positive_ray_of_gap hf hfCont hf₀ hs hGap hds
    obtain ⟨a, ha, hfa⟩ := hSupport 0
    filter_upwards [eventually_ge_atTop R₁, eventually_ge_atTop (a + 1),
      eventually_ge_atTop (a / κ), eventually_ge_atTop (5 / d), eventually_ge_atTop (5 / (d - c))]
      with r hR₁ hRa hRκ hRd hRloss
    have har : a < r := (lt_add_one a).trans_le hRa
    obtain ⟨b, hb, hfb, hSign⟩ :=
      exists_nonzero_endpoint_with_weak_sign_collar hfCont hSupport hFinite (ha.trans har).le
    obtain ⟨T, hT, hComp⟩ := eventually_local_gaussian_signAlternations hf (har.trans hb)
      hfCont.continuousAt hfCont.continuousAt hfa hfb
    have hSmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 T := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hT)]
        with t (ht : 0 < t) (htT : t < T)
      exact ⟨ht, htT⟩
    obtain ⟨t, ht, hHeated⟩ := (hSmall.and hHeat).exists
    obtain ⟨N, hN, hNA⟩ := hHeated r hR₁
    have hLeft : a ≤ κ * r := by
      simpa only [mul_comm r κ] using (div_le_iff₀ hκ).mp hRκ
    have hFive : 5 ≤ (N : ℝ) :=
      ((div_le_iff₀ hdPos).mp hRd).trans (by simpa only [mul_comm r d] using hN)
    have hFiveNat : 5 ≤ N := by exact_mod_cast hFive
    let m := N - 5
    have hm : m + 1 + 4 = N := by dsimp only [m]; omega
    have hPre : HasSignAlternations (realGaussianSmoothing t f) (Icc a b) (m + 1 + 4) := by
      rw [hm]
      exact hNA.mono (Icc_subset_Icc hLeft hb.le)
    have hOrig := hComp t ht (m + 1) hPre
    have hMLoss := (div_le_iff₀ (sub_pos.mpr hcd)).mp hRloss
    have hMCast : (m : ℝ) + 5 = (N : ℝ) := by exact_mod_cast (show m + 5 = N by omega)
    have hRate : c * r ≤ (m : ℝ) := by linarith only [hN, hMLoss, hMCast]
    exact ⟨m, hRate, (hOrig.trim_final_weak_sign hSign).mono (Icc_subset_Icc ha.le le_rfl)⟩
  · push Not at hFinite
    obtain ⟨b, hb⟩ := hFinite
    filter_upwards [eventually_ge_atTop b] with r hr
    let n := ⌈c * r⌉₊
    exact ⟨n, Nat.le_ceil _, (hb n).mono (Icc_subset_Icc le_rfl hr)⟩

end
end MeyerGeneralProblem
