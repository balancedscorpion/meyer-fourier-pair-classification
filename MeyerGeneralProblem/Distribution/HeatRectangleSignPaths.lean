module

public import MeyerGeneralProblem.Distribution.HorizontalStripCrossing
public import MeyerGeneralProblem.Distribution.SignAlternationCut
public import MeyerGeneralProblem.Distribution.ParabolicMinimumPrinciple
public import MeyerGeneralProblem.Distribution.LocalGaussianHeat
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-!
# Order of sign paths across a heat rectangle

The crossing theorem orders bottom endpoints of opposite-sign paths
and transfers top sign alternations to the initial time.
-/

namespace MeyerGeneralProblem

open Filter Set
open scoped Convex unitInterval Topology

/-- A bottom-to-top path whose entire image has the strict sign of its
top point. Time is the imaginary coordinate and position the real one. -/
def HasBottomSignPath (u : ℝ → ℝ → ℝ) (a b T x : ℝ) : Prop :=
  ∃ p : I → ℂ, Continuous p ∧ (p 0).im = 0 ∧ (p 1).im = T ∧
    (p 1).re = x ∧ (p 0).re ∈ Icc a b ∧
    (∀ s : I, s ≠ 0 → s ≠ 1 → 0 < (p s).im ∧ (p s).im < T) ∧
    ∀ s : I, 0 < u T x * u (p s).im (p s).re

/-- Bottom-to-top paths with the sign of their top points transport an
alternation witness to the bottom. Opposite-sign paths are disjoint,
so consecutive bottom samples retain their order by the strip crossing
theorem. -/
theorem hasSignAlternations_bottom_of_top_of_signPaths
    (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hPath : ∀ x ∈ Icc a b, u T x ≠ 0 → HasBottomSignPath u a b T x)
    {n : ℕ} (hAlt : HasSignAlternations (u T) (Icc a b) n) :
    HasSignAlternations (u 0) (Icc a b) n := by
  cases n with
  | zero => exact hasSignAlternations_zero_of_nonempty ⟨a, le_rfl, hab⟩
  | succ n =>
    obtain ⟨x, hx, hxMem, hxAlt⟩ := hAlt
    have hxNonzero (i : Fin (n + 2)) : u T (x i) ≠ 0 := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (mul_ne_zero_iff.mp (ne_of_lt (hxAlt 0))).1
      · exact (mul_ne_zero_iff.mp (ne_of_lt (hxAlt j))).2
    choose p hC hZero hOne hTop hBottom hInside hSign using
      fun i => hPath (x i) (hxMem i) (hxNonzero i)
    let y (i : Fin (n + 2)) := (p i 0).re
    have hStartSign (i : Fin (n + 2)) : 0 < u T (x i) * u 0 (y i) := by
      simpa only [y, hZero] using hSign i 0
    have hYAlt (i : Fin (n + 1)) : u 0 (y i.castSucc) * u 0 (y i.succ) < 0 := by
      have h := mul_pos (hStartSign i.castSucc) (hStartSign i.succ)
      rw [mul_mul_mul_comm] at h
      exact ((mul_pos_iff.mp h).resolve_left (fun hp => (hxAlt i).not_gt hp.1)).2
    have hDisjoint (i : Fin (n + 1)) (s t : I) : p i.castSucc s ≠ p i.succ t := by
      intro he
      have h := hSign i.succ t
      rw [← he] at h
      replace h := mul_pos (hSign i.castSucc s) h
      rw [mul_mul_mul_comm] at h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (hxAlt i).le (mul_self_nonneg _))) h
    refine ⟨y, Fin.strictMono_iff_lt_succ.mpr fun i => ?_, hBottom, hYAlt⟩
    by_contra! hRev
    rcases lt_or_eq_of_le hRev with hStrict | he
    · have hTopOrder : (p i.castSucc 1).re < (p i.succ 1).re := by
        rw [hTop, hTop]
        exact hx Fin.castSucc_lt_succ
      obtain ⟨s, t, he⟩ := exists_eq_of_reversed_paths_across_horizontal_strip
        (p i.castSucc) (p i.succ) (hC _) (hC _) hT (hZero _) (hZero _)
        (hOne _) (hOne _) (hInside _) (hInside _) hStrict hTopOrder
      exact hDisjoint i s t he
    · have hs := hYAlt i
      rw [he] at hs
      exact (not_lt_of_ge (mul_self_nonneg _)) hs

private def IsInteriorTimePath {p q : ℝ × ℝ} (γ : Path p q) (T : ℝ) : Prop :=
  ∀ s : I, (s ≠ 0 → 0 < (γ s).1) ∧ (s ≠ 1 → (γ s).1 < T)

private theorem interiorTimePath_segment {p q : ℝ × ℝ} {T : ℝ}
    (hp₀ : 0 ≤ p.1) (hpT : p.1 < T) (hq₀ : 0 < q.1) (hqT : q.1 ≤ T) :
    IsInteriorTimePath (Path.segment p q) T := by
  intro s
  have he : (Path.segment p q s).1 = (1 - (s : ℝ)) * p.1 + (s : ℝ) * q.1 := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  rw [he]
  constructor
  · intro hs
    have hsPos : 0 < (s : ℝ) :=
      lt_of_le_of_ne s.property.1 (fun he => hs (Subtype.ext he.symm))
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr s.property.2) hp₀) (mul_pos hsPos hq₀)
  · intro hs
    have hsLt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (fun he => hs (Subtype.ext he))
    have h := add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hsLt) (sub_pos.mpr hpT))
      (mul_nonneg s.property.1 (sub_nonneg.mpr hqT))
    linarith

private theorem interiorTimePath_trans {p q r : ℝ × ℝ} {T : ℝ}
    {γ : Path p q} {η : Path q r}
    (hγ : IsInteriorTimePath γ T) (hη : IsInteriorTimePath η T) (hq : q.1 ∈ Ioo 0 T) :
    IsInteriorTimePath (γ.trans η) T := by
  intro s
  rw [Path.trans_apply]
  split_ifs with hs
  · let t : I := ⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.property.1, hs⟩⟩
    change (s ≠ 0 → 0 < (γ t).1) ∧ (s ≠ 1 → (γ t).1 < T)
    refine ⟨fun hs₀ => (hγ t).1 ?_, fun _ => ?_⟩
    · intro ht₀
      apply hs₀
      apply Subtype.ext
      have hV : 2 * (s : ℝ) = 0 := congrArg Subtype.val ht₀
      change (s : ℝ) = 0
      linarith
    · by_cases ht₁ : t = 1
      · simpa only [ht₁, Path.target] using hq.2
      · exact (hγ t).2 ht₁
  · let t : I := ⟨2 * (s : ℝ) - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs).le, s.property.2⟩⟩
    change (s ≠ 0 → 0 < (η t).1) ∧ (s ≠ 1 → (η t).1 < T)
    refine ⟨fun _ => ?_, fun hs₁ => (hη t).2 ?_⟩
    · by_cases ht₀ : t = 0
      · simpa only [ht₀, Path.source] using hq.1
      · exact (hη t).1 ht₀
    · intro ht₁
      apply hs₁
      apply Subtype.ext
      have hV : 2 * (s : ℝ) - 1 = 1 := congrArg Subtype.val ht₁
      change (s : ℝ) = 1
      linarith

private theorem path_trans_property {X : Type*} [TopologicalSpace X] {P : X → Prop}
    {x y z : X} {γ : Path x y} {η : Path y z}
    (hγ : ∀ s : I, P (γ s)) (hη : ∀ s : I, P (η s)) :
    ∀ s : I, P ((γ.trans η) s) := by
  intro s
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · exact hη _

private theorem sameSign_pos_trans {a b c : ℝ} (hab : 0 < a * b) (hbc : 0 < b * c) :
    0 < a * c := by
  have h := mul_pos hab hbc
  rw [show a * b * (b * c) = (a * c) * (b * b) by ring] at h
  exact ((mul_pos_iff.mp h).resolve_right fun hn => (not_lt_of_ge (mul_self_nonneg b)) hn.2).1

private theorem rectSignPath_of_realPath {u : ℝ → ℝ → ℝ} {a b T x y : ℝ}
    (hy : y ∈ Icc a b) (γ : Path ((0 : ℝ), y) (T, x)) (hγ : IsInteriorTimePath γ T)
    (hSign : ∀ s : I, 0 < u T x * u (γ s).1 (γ s).2) :
    HasBottomSignPath u a b T x := by
  let E (p : ℝ × ℝ) : ℂ := Complex.equivRealProdCLM.symm p.swap
  have hE : Continuous E := Complex.equivRealProdCLM.symm.continuous.comp continuous_swap
  refine ⟨fun s => E (γ s), hE.comp γ.continuous, ?_, ?_, ?_, ?_, ?_, hSign⟩
  · change (γ 0).1 = 0
    rw [Path.source]
  · change (γ 1).1 = T
    rw [Path.target]
  · change (γ 1).2 = x
    rw [Path.target]
  · change (γ 0).2 ∈ Icc a b
    rwa [Path.source]
  · exact fun s h₀ h₁ => ⟨(hγ s).1 h₀, (hγ s).2 h₁⟩

private theorem path_segment_mem_of_convex {S : Set (ℝ × ℝ)} (hS : Convex ℝ S)
    {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S) (s : I) : Path.segment p q s ∈ S := by
  apply hS.segment_subset hp hq
  rw [← Path.range_segment]
  exact mem_range_self s

private theorem hasBottomSignPath_of_heat_rectangle
    (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (hCont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 T ×ˢ Icc a b))
    (hHeat : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b,
      HasDerivAt (fun s => u s x) (deriv (deriv (u t)) x / 4) t)
    (hSides : ∃ A B : ℝ, ∀ t ∈ Icc 0 T, 0 < A * u t a ∧ 0 < B * u t b)
    (x : ℝ) (hx : x ∈ Icc a b) (hxNZ : u T x ≠ 0) :
    HasBottomSignPath u a b T x := by
  obtain ⟨A, B, hSides⟩ := hSides
  have hLateral {z s t : ℝ} (hz : z = a ∨ z = b) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      0 < u s z * u t z := by
    rcases hz with rfl | rfl
    · exact sameSign_pos_trans (by rw [mul_comm]; exact (hSides s hs).1) (hSides t ht).1
    · exact sameSign_pos_trans (by rw [mul_comm]; exact (hSides s hs).2) (hSides t ht).2
  have hVertical (z t : ℝ) (ht : t ∈ Icc 0 T) (s : I) :
      Path.segment ((0 : ℝ), z) (t, z) s ∈ Icc 0 T ×ˢ ({z} : Set ℝ) :=
    path_segment_mem_of_convex ((convex_Icc 0 T).prod (convex_singleton z))
      ⟨⟨le_rfl, hT.le⟩, mem_singleton z⟩ ⟨ht, mem_singleton z⟩ s
  by_cases hEdge : x = a ∨ x = b
  · have hγ := interiorTimePath_segment (p := ((0 : ℝ), x)) (q := (T, x))
      le_rfl hT hT le_rfl
    refine rectSignPath_of_realPath hx _ hγ (fun s => ?_)
    obtain ⟨hs, hsx⟩ := hVertical x T ⟨hT.le, le_rfl⟩ s
    rw [mem_singleton_iff.mp hsx]
    exact hLateral hEdge ⟨hT.le, le_rfl⟩ hs
  have hxInt : x ∈ Ioo a b := by
    push Not at hEdge
    exact ⟨lt_of_le_of_ne hx.1 hEdge.1.symm, lt_of_le_of_ne hx.2 hEdge.2⟩
  let D : Set (ℝ × ℝ) := Ioo 0 T ×ˢ Ioo a b
  let K : Set (ℝ × ℝ) := Icc 0 T ×ˢ Icc a b
  let v (s y : ℝ) := -(u T x) * u s y
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hDK : D ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hK : Convex ℝ K := (convex_Icc 0 T).prod (convex_Icc a b)
  have hCl : closure D = K := by
    dsimp [D, K]
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_Ioo hab.ne]
  have hDb : Bornology.IsBounded D := (isCompact_Icc.prod isCompact_Icc).isBounded.subset hDK
  have hvCont : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) K := continuousOn_const.mul hCont
  have hvHeat (p : ℝ × ℝ) (hp : p ∈ D) :
      ∃ d : ℝ, HasDerivAt (fun t => v t p.2) d p.1 ∧
        (1 / 4 : ℝ) * deriv (deriv (v p.1)) p.2 ≤ d := by
    have hD := (hHeat p.1 ⟨hp.1.1, hp.1.2.le⟩ p.2 hp.2).const_mul (-(u T x))
    refine ⟨_, hD, le_of_eq ?_⟩
    dsimp [v]
    rw [deriv_const_mul_field', deriv_const_mul_field]
    ring
  have hLocal (p : ℝ × ℝ) (hp : p ∈ K) (hn : v p.1 p.2 < 0) :
      ∃ δ > 0, ∀ q ∈ Metric.ball p δ ∩ K, v q.1 q.2 < 0 := by
    have hE : ∀ᶠ q in 𝓝[K] p, v q.1 q.2 < 0 :=
      (hvCont p hp).tendsto.eventually (Iio_mem_nhds hn)
    obtain ⟨W, hW, hSub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hE
    obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hW
    exact ⟨δ, hδ, fun q hq => hSub ⟨hBall hq.1, hq.2⟩⟩
  let p : ℝ × ℝ := (T, x)
  have hpK : p ∈ K := ⟨⟨hT.le, le_rfl⟩, hx⟩
  have hpNeg : v p.1 p.2 < 0 := by
    exact mul_neg_iff.mpr (by
      rcases lt_or_gt_of_ne hxNZ with h | h
      · exact Or.inl ⟨neg_pos.mpr h, h⟩
      · exact Or.inr ⟨neg_neg_of_pos h, h⟩)
  obtain ⟨δ, hδ, hNearP⟩ := hLocal p hpK hpNeg
  let e := min δ T / 2
  have he : 0 < e := half_pos (lt_min hδ hT)
  have heT : e < T := by dsimp [e]; linarith [min_le_right δ T]
  have heδ : e < δ := by dsimp [e]; linarith [min_le_left δ T]
  let p' : ℝ × ℝ := (T - e, x)
  have hp'D : p' ∈ D := ⟨⟨sub_pos.mpr heT, sub_lt_self _ he⟩, hxInt⟩
  have hp'Ball : p' ∈ Metric.ball p δ := by
    change dist (T - e, x) (T, x) < δ
    simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
    rw [show T - e - T = -e by ring, abs_neg, abs_of_pos he]
    exact max_lt heδ hδ
  have hp'Neg : v p'.1 p'.2 < 0 := hNearP p' ⟨hp'Ball, hDK hp'D⟩
  obtain ⟨q, hqF, hqT, hqNeg, hqC⟩ := exists_negative_boundary_in_closure_heat_component
    D hD hDb (by norm_num : 0 ≤ (1 / 4 : ℝ)) (prod_mono subset_rfl (subset_univ _)) v
    (hCl.symm ▸ hvCont) hvHeat p' hp'D hp'Neg
  let O := D ∩ {z : ℝ × ℝ | v z.1 z.2 < 0}
  let C := connectedComponentIn O p'
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hDz : D ∈ 𝓝 z := hD.mem_nhds hz.1
    have hVz : ContinuousAt (fun q : ℝ × ℝ => v q.1 q.2) z :=
      (hvCont.mono hDK z hz.1).continuousAt hDz
    exact inter_mem hDz (hVz (Iio_mem_nhds hz.2))
  have hp'O : p' ∈ O := ⟨hp'D, hp'Neg⟩
  have hp'C : p' ∈ C := mem_connectedComponentIn hp'O
  have hCO : C ⊆ O := connectedComponentIn_subset O p'
  have hCPath : IsPathConnected C :=
    hO.connectedComponentIn.isConnected_iff_isPathConnected.mp
      (isConnected_connectedComponentIn_iff.mpr hp'O)
  have hqK : q ∈ K := hCl ▸ hqF.1
  obtain ⟨ε, hε, hNearQ⟩ := hLocal q hqK hqNeg
  obtain ⟨q', hq'Ball, hq'C⟩ := (mem_closure_iff_nhds.mp hqC) (Metric.ball q ε)
    (Metric.ball_mem_nhds _ hε)
  have hq'D : q' ∈ D := (hCO hq'C).1
  obtain ⟨γ, hγ⟩ := hCPath.joinedIn q' hq'C p' hp'C
  have hγTime (s : I) : (γ s).1 ∈ Ioo 0 T := (hCO (hγ s)).1.1
  let H := ((Path.segment q q').trans γ).trans (Path.segment p' p)
  have hHtime : IsInteriorTimePath H T :=
    interiorTimePath_trans
      (interiorTimePath_trans (interiorTimePath_segment hqK.1.1 hqT hq'D.1.1 hq'D.1.2.le)
        (fun s => ⟨fun _ => (hγTime s).1, fun _ => (hγTime s).2⟩) hq'D.1)
      (interiorTimePath_segment hp'D.1.1.le hp'D.1.2 hT le_rfl) hp'D.1
  have hHNeg (s : I) : v (H s).1 (H s).2 < 0 :=
    path_trans_property
      (path_trans_property (fun t => hNearQ _ (path_segment_mem_of_convex
        ((convex_ball _ _).inter hK) ⟨Metric.mem_ball_self hε, hqK⟩
        ⟨hq'Ball, hDK hq'D⟩ t)) (fun t => (hCO (hγ t)).2))
      (fun t => hNearP _ (path_segment_mem_of_convex
        ((convex_ball _ _).inter hK) ⟨hp'Ball, hDK hp'D⟩
        ⟨Metric.mem_ball_self hδ, hpK⟩ t)) s
  have hHsign (s : I) : 0 < u T x * u (H s).1 (H s).2 := by
    have h := hHNeg s
    dsimp only [v] at h
    linarith
  rcases eq_or_lt_of_le hqK.1.1 with hqZero | hqPos
  · have he : ((0 : ℝ), q.2) = q := Prod.ext hqZero rfl
    exact rectSignPath_of_realPath hqK.2 (H.cast he rfl) hHtime hHsign
  · have hqEdge : q.2 = a ∨ q.2 = b := by
      by_contra! hn
      have hqD : q ∈ D := ⟨⟨hqPos, hqT⟩,
        ⟨lt_of_le_of_ne hqK.2.1 hn.1.symm, lt_of_le_of_ne hqK.2.2 hn.2⟩⟩
      exact hqF.2 (hD.interior_eq.symm ▸ hqD)
    let V := Path.segment ((0 : ℝ), q.2) q
    have hVtime : IsInteriorTimePath V T := interiorTimePath_segment le_rfl hT hqPos hqT.le
    have hVSign (s : I) : 0 < u T x * u (V s).1 (V s).2 := by
      obtain ⟨hts, hxs⟩ := hVertical q.2 q.1 hqK.1 s
      have hQSign : 0 < u T x * u q.1 q.2 := by dsimp [v] at hqNeg; linarith
      have he : (V s).2 = q.2 := hxs
      rw [he]
      exact sameSign_pos_trans hQSign (hLateral hqEdge hqK.1 hts)
    exact rectSignPath_of_realPath hqK.2 (V.trans H)
      (interiorTimePath_trans hVtime hHtime ⟨hqPos, hqT⟩)
      (path_trans_property (P := fun z : ℝ × ℝ => 0 < u T x * u z.1 z.2) hVSign hHsign)

/-- The top sign-alternation count of a heat solution with fixed
nonzero lateral signs is witnessed at the initial time. -/
theorem hasSignAlternations_initial_of_heat_rectangle
    (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (hCont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 T ×ˢ Icc a b))
    (hHeat : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ioo a b,
      HasDerivAt (fun s => u s x) (deriv (deriv (u t)) x / 4) t)
    (hSides : ∃ A B : ℝ, ∀ t ∈ Icc 0 T, 0 < A * u t a ∧ 0 < B * u t b)
    {n : ℕ} (hAlt : HasSignAlternations (u T) (Icc a b) n) :
    HasSignAlternations (u 0) (Icc a b) n :=
  hasSignAlternations_bottom_of_top_of_signPaths u hab.le hT
    (hasBottomSignPath_of_heat_rectangle u hab hT hCont hHeat hSides) hAlt

/-- The ordered rectangle comparison used in the local Gaussian argument. -/
theorem heatRectangleSignAlternationComparison : HeatRectangleSignAlternationComparison := by
  intro u a b T hab hT hCont hHeat hSides n hAlt
  have h := hasSignAlternations_initial_of_heat_rectangle u hab hT hCont
    (fun t ht x hx => (hHeat t ht x hx).2.2) hSides hAlt
  exact h.drop_first.drop_first.drop_first.drop_first

/-- On an interval with two nonzero continuity endpoints, sufficiently
short untruncated Gaussian flow satisfies the local alternation bound. -/
theorem eventually_local_gaussian_signAlternations
    {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) {a b : ℝ} (hab : a < b)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b)
    (ha₀ : f a ≠ 0) (hb₀ : f b ≠ 0) :
    ∃ T > 0, ∀ t ∈ Ioo 0 T, ∀ n,
      HasSignAlternations (realGaussianSmoothing t f) (Icc a b) (n + 4) →
        HasSignAlternations f (Icc a b) n :=
  eventually_local_gaussian_signAlternations_of_rectangle_comparison
    heatRectangleSignAlternationComparison hf hab ha hb ha₀ hb₀

end MeyerGeneralProblem
