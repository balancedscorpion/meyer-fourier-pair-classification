module

public import MeyerGeneralProblem.Distribution.LatticeSlabPhaseAverages

@[expose] public section

/-!
# Exact qualitative limits for closed real lattice slabs

Integral horizontal coordinates range over symmetric boxes. The last
coordinate is counted by a closed integer interval. Injectivity gives an
exact frequency count, and the phase average gives the limit and the
strict deficit for a fixed enlargement of the narrower slab.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Classical Topology

/-- The frequency with horizontal integral coordinates and one
unrestricted last integral coordinate. -/
def slabLatticeFrequency {d : Type*} [Fintype d]
    (β : d → ℝ) (p : ℝ) (u : (d → ℤ) × ℤ) : ℝ :=
  (∑ i, (u.1 i : ℝ) * β i) + (u.2 : ℝ) * p

/-- The original closed lattice slab, with a symmetric integer box on
every horizontal coordinate. -/
def latticeSlabFrequencies {d : Type*} [Fintype d]
    (β : d → ℝ) (p L : ℝ) (N : ℕ) : Set ℝ :=
  {x | ∃ u : (d → ℤ) × ℤ, (∀ i, |u.1 i| ≤ (N : ℤ)) ∧
    slabLatticeFrequency β p u = x ∧ |x| ≤ L}

private def slabSlant {d : Type*} [Fintype d] (β : d → ℝ) (u : d → ℤ) : ℝ :=
  ∑ i, (u i : ℝ) * β i

private def slabHorizontalCoordinates {d : Type*} (M N : ℕ)
    (u : d → Fin (M + 1)) : d → ℤ :=
  fun i => (u i : ℕ) - (N : ℤ)

private theorem slabHorizontalCoordinates_injective {d : Type*} (M N : ℕ) :
    Function.Injective (@slabHorizontalCoordinates d M N) := by
  intro f g h
  funext i
  apply Fin.ext
  have he := congrFun h i
  change (f i : ℕ) - (N : ℤ) = (g i : ℕ) - (N : ℤ) at he
  omega

private theorem slabHorizontalCoordinates_mem_box {d : Type*} (N : ℕ)
    (f : d → Fin (2 * N + 1)) (i : d) :
    |slabHorizontalCoordinates (2 * N) N f i| ≤ (N : ℤ) := by
  apply abs_le.mpr
  have hi := (f i).isLt
  change -(N : ℤ) ≤ (f i : ℕ) - (N : ℤ) ∧ (f i : ℕ) - (N : ℤ) ≤ N
  omega

private theorem slabHorizontalCoordinates_surj_box {d : Type*} (N : ℕ) (u : d → ℤ)
    (hu : ∀ i, |u i| ≤ (N : ℤ)) :
    ∃ f : d → Fin (2 * N + 1), slabHorizontalCoordinates (2 * N) N f = u := by
  have hb (i : d) := abs_le.mp (hu i)
  let f (i : d) : Fin (2 * N + 1) := ⟨(u i + (N : ℤ)).toNat, by
    have h := hb i
    omega⟩
  refine ⟨f, funext fun i => ?_⟩
  change ((u i + (N : ℤ)).toNat : ℤ) - (N : ℤ) = u i
  have h := hb i
  omega

private def latticeSlabFiberIndices {d : Type*} [Fintype d]
    (β : d → ℝ) (p L : ℝ) (M N : ℕ) (f : d → Fin (M + 1)) : Finset ℤ :=
  let S := slabSlant β (slabHorizontalCoordinates M N f)
  Finset.Icc ⌈(-L - S) / p⌉ ⌊(L - S) / p⌋

private theorem mem_latticeSlabFiberIndices_iff {d : Type*} [Fintype d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) (L : ℝ) (M N : ℕ)
    (f : d → Fin (M + 1)) (k : ℤ) :
    k ∈ latticeSlabFiberIndices β p L M N f ↔
      |slabLatticeFrequency β p (slabHorizontalCoordinates M N f, k)| ≤ L := by
  rw [latticeSlabFiberIndices, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
    div_le_iff₀ hp, le_div_iff₀ hp, abs_le]
  change -L - slabSlant β (slabHorizontalCoordinates M N f) ≤ (k : ℝ) * p ∧
    (k : ℝ) * p ≤ L - slabSlant β (slabHorizontalCoordinates M N f) ↔
    -L ≤ slabSlant β (slabHorizontalCoordinates M N f) + (k : ℝ) * p ∧
    slabSlant β (slabHorizontalCoordinates M N f) + (k : ℝ) * p ≤ L
  constructor <;> rintro ⟨hlo, hhi⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Every horizontal index in the symmetric integer box contributes its
exact closed interval count. Injectivity retains each frequency once. -/
private theorem finite_and_ncard_latticeSlabFrequencies {d : Type*} [Fintype d] [DecidableEq d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) (L : ℝ) (N : ℕ)
    (hβ : Function.Injective (slabLatticeFrequency β p)) :
    (latticeSlabFrequencies β p L N).Finite ∧
    (latticeSlabFrequencies β p L N).ncard =
      ∑ f : d → Fin (2 * N + 1), (latticeSlabFiberIndices β p L (2 * N) N f).card := by
  classical
  let D := Σ f : d → Fin (2 * N + 1), ↥(latticeSlabFiberIndices β p L (2 * N) N f)
  let A : Finset D := Finset.univ
  let g (z : D) := slabLatticeFrequency β p (slabHorizontalCoordinates (2 * N) N z.1, z.2)
  have hg : Function.Injective g := by
    rintro ⟨f, k⟩ ⟨f', k'⟩ hh
    have he := hβ hh
    have hf : f = f' := slabHorizontalCoordinates_injective _ _ (congrArg Prod.fst he)
    subst f'
    have hk : k = k' := Subtype.ext (congrArg Prod.snd he)
    subst k'
    rfl
  have hE : (latticeSlabFrequencies β p L N) = (A.image g : Set ℝ) := by
    ext x
    change (∃ u : (d → ℤ) × ℤ, (∀ i, |u.1 i| ≤ (N : ℤ)) ∧ _ ∧ _) ↔ _
    simp only [Finset.mem_coe, Finset.mem_image, A, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨u, k⟩, hu, hx, hLx⟩
      obtain ⟨f, hf⟩ := slabHorizontalCoordinates_surj_box N u hu
      have hk : k ∈ latticeSlabFiberIndices β p L (2 * N) N f := by
        rw [mem_latticeSlabFiberIndices_iff β hp, hf, hx]
        exact hLx
      refine ⟨⟨f, ⟨k, hk⟩⟩, ?_⟩
      change slabLatticeFrequency β p (slabHorizontalCoordinates (2 * N) N f, k) = _
      rw [hf, hx]
    · rintro ⟨⟨f, k⟩, rfl⟩
      exact ⟨(slabHorizontalCoordinates (2 * N) N f, k), slabHorizontalCoordinates_mem_box N f,
        rfl, (mem_latticeSlabFiberIndices_iff β hp _ _ _ _ _).mp k.property⟩
  rw [hE]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hg, Finset.card_univ]
  simp only [D, Fintype.card_sigma, Fintype.card_coe]

private theorem slabFourierMode_detects {d : Type*} [Fintype d] [DecidableEq d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) (hβ : Function.Injective (slabLatticeFrequency β p))
    (i : d) (m : ℤ) (hm : m ≠ 0) :
    fourier m (((β i / p : ℝ)) : UnitAddCircle) ≠ 1 := by
  intro he
  rw [fourier_coe_apply] at he
  have ht : Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * (β i / p) : ℝ) : ℂ)) = 1 := by
    convert he using 2
    push_cast
    ring
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp ht
  have hpI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have harg : (((m : ℝ) * (β i / p) : ℝ) : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ hpI
    simpa [mul_comm, mul_left_comm, mul_assoc] using hk
  have he' : (m : ℝ) * (β i / p) = (k : ℝ) := by exact_mod_cast harg
  have hzero : slabLatticeFrequency β p (Pi.single i m, -k) = slabLatticeFrequency β p (0, 0) := by
    simp only [slabLatticeFrequency, Pi.single_apply, Int.cast_ite, Int.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Int.cast_neg, Pi.zero_apply, Finset.sum_const_zero,
      add_zero]
    have eq := (div_eq_iff hp.ne').mp (by simpa [mul_div_assoc] using he' : (m : ℝ) * β i / p = (k : ℝ))
    linarith
  apply hm
  simpa using congrFun (congrArg Prod.fst (hβ hzero)) i

/-- The closed lattice slab is finite for every horizontal box. -/
theorem finite_latticeSlabFrequencies {d : Type*} [Fintype d] [DecidableEq d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) (L : ℝ) (N : ℕ)
    (hβ : Function.Injective (slabLatticeFrequency β p)) :
    (latticeSlabFrequencies β p L N).Finite :=
  (finite_and_ncard_latticeSlabFrequencies β hp L N hβ).1

/-- The exact slab limit for rationally independent real frequencies, in
closed slabs and symmetric integer boxes. -/
theorem tendsto_ncard_latticeSlabFrequencies {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) {L : ℝ} (hL : 0 ≤ L)
    (hβ : Function.Injective (slabLatticeFrequency β p)) :
    Tendsto (fun N : ℕ => ((latticeSlabFrequencies β p L N).ncard : ℝ) /
      ((2 * N + 1 : ℕ) : ℝ) ^ Fintype.card d) atTop (𝓝 (2 * L / p)) := by
  classical
  let a (i : d) : UnitAddCircle := ((β i / p : ℝ) : UnitAddCircle)
  let t (n : ℕ) : ℝ := (L - ∑ i, ((n / 2 : ℕ) : ℝ) * β i) / p
  let c (n : ℕ) : UnitAddCircle := (t n : UnitAddCircle)
  let v (n : ℕ) (f : d → Fin (n + 1)) : ℝ :=
    (-L - slabSlant β (slabHorizontalCoordinates n (n / 2) f)) / p
  have hMode (m : ℤ) (hm : m ≠ 0) : ∃ i, fourier m (a i) ≠ 1 := by
    obtain ⟨i⟩ := ‹Nonempty d›
    exact ⟨i, slabFourierMode_detects β hp hβ i m hm⟩
  have hPhase (n : ℕ) (f : d → Fin (n + 1)) :
      ((-v n f : ℝ) : UnitAddCircle) = c n + ∑ j, (f j : ℕ) • a j := by
    let Q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    change Q (-v n f) = Q (t n) + ∑ j, (f j : ℕ) • Q (β j / p)
    have he : -v n f = t n + ∑ j, (f j : ℕ) • (β j / p) := by
      simp only [v, t, slabSlant, slabHorizontalCoordinates, Int.cast_sub, Int.cast_natCast,
        sub_mul, Finset.sum_sub_distrib, nsmul_eq_mul]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, ← add_div, ← neg_div]
      congr 1
      ring
    rw [he, map_add, map_sum]
    simp only [map_nsmul]
  have hMean := tendsto_closedIntegerIntervalCount_box_mean a c hMode v hPhase (2 * L / p) (by positivity)
  have hT : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  apply (hMean.comp hT).congr
  intro n
  have hn : 2 * n / 2 = n := by omega
  have hCard := (finite_and_ncard_latticeSlabFrequencies β hp L n hβ).2
  change ((∑ f : d → Fin (2 * n + 1), closedIntegerIntervalCount
    (v (2 * n) f) (v (2 * n) f + 2 * L / p)) : ℝ) / _ = _
  rw [hCard, ← Nat.cast_sum]
  apply congrArg (fun k : ℝ => k / ((2 * n + 1 : ℕ) : ℝ) ^ Fintype.card d)
  apply congrArg (fun k : ℕ => (k : ℝ))
  apply Finset.sum_congr rfl
  intro f _
  rw [closedIntegerIntervalCount, latticeSlabFiberIndices]
  have hv : v (2 * n) f =
      (-L - slabSlant β (slabHorizontalCoordinates (2 * n) n f)) / p := by
    dsimp [v]
    rw [hn]
  rw [hv]
  congr 3
  ring

/-- Enlarging the horizontal radius by a fixed amount preserves the
ratio limit between two positive-width slabs. -/
theorem tendsto_ncard_latticeSlabFrequencies_ratio {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) {J L : ℝ} (hJ : 0 < J) (hL : 0 < L)
    (H : ℕ) (hβ : Function.Injective (slabLatticeFrequency β p)) :
    Tendsto (fun N : ℕ => ((latticeSlabFrequencies β p J (N + H)).ncard : ℝ) /
      ((latticeSlabFrequencies β p L N).ncard : ℝ)) atTop (𝓝 (J / L)) := by
  let m (N : ℕ) : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let r := Fintype.card d
  let A (N : ℕ) : ℝ := (latticeSlabFrequencies β p J N).ncard
  let B (N : ℕ) : ℝ := (latticeSlabFrequencies β p L N).ncard
  have ha : Tendsto (fun N => A (N + H) / m (N + H) ^ r) atTop (𝓝 (2 * J / p)) :=
    (tendsto_ncard_latticeSlabFrequencies β hp hJ.le hβ).comp (tendsto_add_atTop_nat H)
  have hb : Tendsto (fun N => B N / m N ^ r) atTop (𝓝 (2 * L / p)) :=
    tendsto_ncard_latticeSlabFrequencies β hp hL.le hβ
  have hm : Tendsto m atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop.2
    intro n
    exact eventually_atTop.2 ⟨n, fun x hx => by omega⟩
  have hmpos (N : ℕ) : 0 < m N := by dsimp [m]; positivity
  have he (N : ℕ) : m (N + H) / m N = 1 + (2 * (H : ℝ)) / m N := by
    have hx : m (N + H) = m N + 2 * H := by simp [m]; ring
    rw [hx, add_div, div_self (hmpos N).ne']
  have hscale : Tendsto (fun N => (m (N + H) / m N) ^ r) atTop (𝓝 1) := by
    simp_rw [he]
    have ht : Tendsto (fun N => (2 * (H : ℝ)) / m N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hm
    simpa using (ht.const_add (1 : ℝ)).pow r
  have hBlim : 2 * L / p ≠ 0 := by positivity
  have hlim := (ha.div hb hBlim).mul hscale
  have hlimval : (2 * J / p) / (2 * L / p) * 1 = J / L := by
    field_simp
  rw [hlimval] at hlim
  apply hlim.congr'
  filter_upwards [hb.eventually_const_lt (show 0 < 2 * L / p by positivity)] with N hN
  have hB : B N ≠ 0 := by
    intro h
    rw [h, zero_div] at hN
    exact (lt_irrefl (0 : ℝ)) hN
  change (A (N + H) / m (N + H) ^ r) / (B N / m N ^ r) * (m (N + H) / m N) ^ r = A (N + H) / B N
  rw [div_pow]
  field_simp [(hmpos N).ne', (hmpos (N + H)).ne', hB]

/-- The strict row-to-column deficit applies for every sufficiently
large horizontal box whenever the output slab is narrower. -/
theorem eventually_ncard_latticeSlabFrequencies_lt {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (β : d → ℝ) {p : ℝ} (hp : 0 < p) {J L : ℝ} (hJ : 0 < J) (hJL : J < L)
    (H : ℕ) (hβ : Function.Injective (slabLatticeFrequency β p)) :
    ∀ᶠ N : ℕ in atTop,
      (latticeSlabFrequencies β p J (N + H)).ncard < (latticeSlabFrequencies β p L N).ncard := by
  have hL := hJ.trans hJL
  have hCount := tendsto_ncard_latticeSlabFrequencies β hp hL.le hβ
  have hRatio := tendsto_ncard_latticeSlabFrequencies_ratio β hp hJ hL H hβ
  filter_upwards [hCount.eventually_const_lt (show 0 < 2 * L / p by positivity),
    hRatio.eventually_lt_const ((div_lt_one hL).mpr hJL)] with N hpos hlt
  have hn : (0 : ℝ) < (latticeSlabFrequencies β p L N).ncard :=
    (div_pos_iff_of_pos_right (by positivity)).mp hpos
  have hc := (div_lt_one hn).mp hlt
  exact_mod_cast hc

end
end MeyerGeneralProblem
