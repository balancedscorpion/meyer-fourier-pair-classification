module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-!
# The parabolic minimum principle on a bounded region

At a negative minimum, the time derivative has the sign imposed by
earlier times and the second spatial derivative has the opposite sign.
A positive affine perturbation in time makes the inequality strict.
-/

namespace MeyerGeneralProblem

open Filter Set
open scoped Topology

private theorem second_deriv_nonneg_of_local_min
    {f : ℝ → ℝ} {x : ℝ} (hMin : IsLocalMin f x) (hCont : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hNeg
  have hMax := isLocalMax_of_deriv_deriv_neg hNeg hMin.deriv_eq_zero hCont
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hMin, hMax] with y hmy hMy
    exact le_antisymm hMy hmy
  have hZero : deriv (deriv f) x = 0 := by simpa using he.deriv.deriv_eq
  linarith

private theorem deriv_nonpos_of_left_min
    {f : ℝ → ℝ} {t d : ℝ} (hD : HasDerivAt f d t)
    (hMin : ∀ᶠ s in 𝓝[<] t, f t ≤ f s) : d ≤ 0 := by
  have hSlope := (hasDerivAt_iff_tendsto_slope_left_right.mp hD).1
  apply le_of_tendsto hSlope
  filter_upwards [hMin, self_mem_nhdsWithin (s := Iio t)] with s hs hst
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) (sub_nonpos.mpr hst.le)

/-- A continuous supersolution on a compact time-space region is
nonnegative if every point where it could be negative admits an open
spatial slice, an earlier-time neighborhood, and the differential
inequality. This allows a top time slice without prescribed values. -/
theorem nonneg_on_compact_of_heat_inequality
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u : ℝ → ℝ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hCont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) K)
    (hTime : ∀ p ∈ K, 0 ≤ p.1)
    (hInterior : ∀ p ∈ K, u p.1 p.2 < 0 →
      (∀ᶠ x in 𝓝 p.2, (p.1, x) ∈ K) ∧
      (∀ᶠ t in 𝓝[<] p.1, (t, p.2) ∈ K) ∧
      ∃ d : ℝ, HasDerivAt (fun t => u t p.2) d p.1 ∧ κ * deriv (deriv (u p.1)) p.2 ≤ d) :
    ∀ p ∈ K, 0 ≤ u p.1 p.2 := by
  intro p hp
  by_contra! hpNeg
  let e := -(u p.1 p.2) / (2 * (p.1 + 1))
  have hpTime : 0 < p.1 + 1 := by linarith [hTime p hp]
  have he : 0 < e := div_pos (neg_pos.mpr hpNeg) (by positivity)
  let v (q : ℝ × ℝ) := u q.1 q.2 + e * (q.1 + 1)
  have hPerturb : Continuous (fun q : ℝ × ℝ => e * (q.1 + 1)) :=
    continuous_const.mul (continuous_fst.add continuous_const)
  obtain ⟨q, hq, hMin⟩ := hK.exists_isMinOn ⟨p, hp⟩ (hCont.add hPerturb.continuousOn)
  have hpV : v p < 0 := by
    have hEq : e * (p.1 + 1) = -(u p.1 p.2) / 2 := by
      dsimp only [e]
      field_simp [hpTime.ne']
    change u p.1 p.2 + e * (p.1 + 1) < 0
    rw [hEq]
    linarith
  have hqV := lt_of_le_of_lt (hMin hp) hpV
  have hqU : u q.1 q.2 < 0 := by
    have hqPerturb : 0 ≤ e * (q.1 + 1) := mul_nonneg he.le (by linarith [hTime q hq])
    exact (le_add_of_nonneg_right hqPerturb).trans_lt hqV
  obtain ⟨hSpace, hBack, d, hDeriv, hHeat⟩ := hInterior q hq hqU
  have hMinSpace : IsLocalMin (u q.1) q.2 := by
    filter_upwards [hSpace] with x hx
    have hCompare : v q ≤ v (q.1, x) := hMin hx
    change u q.1 q.2 + e * (q.1 + 1) ≤ u q.1 x + e * (q.1 + 1) at hCompare
    exact le_of_add_le_add_right hCompare
  have hSpaceMap : Tendsto (fun x : ℝ => (q.1, x)) (𝓝 q.2) (𝓝[K] q) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds tendsto_id, hSpace⟩
  have hSpaceCont : ContinuousAt (u q.1) q.2 := (hCont q hq).tendsto.comp hSpaceMap
  have hSecond := second_deriv_nonneg_of_local_min hMinSpace hSpaceCont
  have hTimeDeriv : HasDerivAt (fun t => v (t, q.2)) (d + e) q.1 := by
    change HasDerivAt ((fun t : ℝ => u t q.2) + (fun t : ℝ => e * (t + 1))) (d + e) q.1
    simpa only [id_eq, mul_one] using
      hDeriv.add (((hasDerivAt_id q.1).add_const (1 : ℝ)).const_mul e)
  have hTimeMin : ∀ᶠ t in 𝓝[<] q.1, v (q.1, q.2) ≤ v (t, q.2) :=
    hBack.mono fun _ ht => hMin ht
  have hTimeLe := deriv_nonpos_of_left_min hTimeDeriv hTimeMin
  linarith [mul_nonneg hκ hSecond]

/-- A continuous heat supersolution on a bounded open time-space region
below time `T` is nonnegative throughout if its boundary values below
`T` are nonnegative. -/
theorem nonneg_on_bounded_open_of_heat_inequality
    (D : Set (ℝ × ℝ)) (hD : IsOpen D) (hBound : Bornology.IsBounded D)
    {T κ : ℝ} (hκ : 0 ≤ κ) (hStrip : D ⊆ Ioo 0 T ×ˢ univ)
    (u : ℝ → ℝ → ℝ) (hCont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (closure D))
    (hBoundary : ∀ p ∈ frontier D, p.1 < T → 0 ≤ u p.1 p.2)
    (hHeat : ∀ p ∈ D, ∃ d : ℝ,
      HasDerivAt (fun t => u t p.2) d p.1 ∧ κ * deriv (deriv (u p.1)) p.2 ≤ d) :
    ∀ p ∈ D, 0 ≤ u p.1 p.2 := by
  intro p hp
  let K := closure D ∩ {q : ℝ × ℝ | q.1 ≤ p.1}
  have hK : IsCompact K := hBound.isCompact_closure.inter_right (isClosed_le continuous_fst continuous_const)
  have hDTime : closure D ⊆ {q : ℝ × ℝ | 0 ≤ q.1} :=
    closure_minimal (fun q hq => (hStrip hq).1.1.le) (isClosed_le continuous_const continuous_fst)
  refine nonneg_on_compact_of_heat_inequality K hK u hκ (hCont.mono inter_subset_left)
    (fun q hq => hDTime hq.1) ?_ p ⟨subset_closure hp, show p.1 ≤ p.1 from le_rfl⟩
  intro q hq hNeg
  have hqD : q ∈ D := by
    by_contra hn
    have hF : q ∈ frontier D := by
      rw [frontier, hD.interior_eq]
      exact ⟨hq.1, hn⟩
    exact (not_lt_of_ge (hBoundary q hF (hq.2.trans_lt (hStrip hp).1.2))) hNeg
  have hU : D ∈ 𝓝 q := hD.mem_nhds hqD
  have hSpatial : Tendsto (fun x : ℝ => (q.1, x)) (𝓝 q.2) (𝓝 q) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hVertical : Tendsto (fun t : ℝ => (t, q.2)) (𝓝 q.1) (𝓝 q) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  refine ⟨(hSpatial.eventually hU).mono fun _ hx => ⟨subset_closure hx, hq.2⟩, ?_, hHeat q hqD⟩
  filter_upwards [(hVertical.eventually hU).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin (s := Iio q.1)] with t htD ht
  refine ⟨subset_closure htD, ?_⟩
  show t ≤ p.1
  exact (show t < q.1 from ht).le.trans hq.2

/-- The closure of a negative component reaches a negative boundary
point below the top time. Continuity and the minimum principle exclude
an interior boundary point of the component with that sign. -/
theorem exists_negative_boundary_in_closure_heat_component
    (D : Set (ℝ × ℝ)) (hD : IsOpen D) (hBound : Bornology.IsBounded D)
    {T κ : ℝ} (hκ : 0 ≤ κ) (hStrip : D ⊆ Ioo 0 T ×ˢ univ)
    (u : ℝ → ℝ → ℝ) (hCont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (closure D))
    (hHeat : ∀ p ∈ D, ∃ d : ℝ,
      HasDerivAt (fun t => u t p.2) d p.1 ∧ κ * deriv (deriv (u p.1)) p.2 ≤ d)
    (p : ℝ × ℝ) (hp : p ∈ D) (hNeg : u p.1 p.2 < 0) :
    ∃ q ∈ frontier D, q.1 < T ∧ u q.1 q.2 < 0 ∧
      q ∈ closure (connectedComponentIn (D ∩ {z : ℝ × ℝ | u z.1 z.2 < 0}) p) := by
  let O := D ∩ {z : ℝ × ℝ | u z.1 z.2 < 0}
  let C := connectedComponentIn O p
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hqD : D ∈ 𝓝 q := hD.mem_nhds hq.1
    have hqU : ContinuousAt (fun z : ℝ × ℝ => u z.1 z.2) q :=
      (hCont.mono subset_closure q hq.1).continuousAt hqD
    exact inter_mem hqD (hqU (Iio_mem_nhds hq.2))
  have hCopen : IsOpen C := hO.connectedComponentIn
  have hCD : C ⊆ D := (connectedComponentIn_subset O p).trans inter_subset_left
  have hpC : p ∈ C := mem_connectedComponentIn ⟨hp, hNeg⟩
  have hExists : ∃ q ∈ frontier C, q.1 < T ∧ u q.1 q.2 < 0 := by
    by_contra! hBoundary
    exact hNeg.not_ge (nonneg_on_bounded_open_of_heat_inequality C hCopen
      (hBound.subset hCD) hκ (hCD.trans hStrip) u (hCont.mono (closure_mono hCD))
      hBoundary (fun q hq => hHeat q (hCD hq)) p hpC)
  obtain ⟨q, hqF, hqT, hqNeg⟩ := hExists
  have hqCl : q ∈ closure C := hqF.1
  have hqNot : q ∉ C := by
    have h : q ∉ interior C := hqF.2
    simpa only [hCopen.interior_eq] using h
  have hqND : q ∉ D := by
    intro hqD
    obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hO q ⟨hqD, hqNeg⟩
    have hCenter : q ∈ Metric.ball q ε := Metric.mem_ball_self hε
    obtain ⟨x, hxB, hxC⟩ := (mem_closure_iff_nhds.mp hqCl) (Metric.ball q ε)
      (Metric.ball_mem_nhds _ hε)
    have hBallC := (convex_ball q ε).isPreconnected.subset_connectedComponentIn hxB hBall
    have hEq : connectedComponentIn O p = connectedComponentIn O x := connectedComponentIn_eq hxC
    apply hqNot
    change q ∈ connectedComponentIn O p
    rw [hEq]
    exact hBallC hCenter
  have hqFD : q ∈ frontier D := by
    rw [frontier, hD.interior_eq]
    exact ⟨closure_mono hCD hqCl, hqND⟩
  exact ⟨q, hqFD, hqT, hqNeg, hqCl⟩

end MeyerGeneralProblem
