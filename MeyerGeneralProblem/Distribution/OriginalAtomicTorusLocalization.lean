module

public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusRectangle
public import MeyerGeneralProblem.Distribution.OriginalGapOscillation

@[expose] public section

/-!
# Lattice localization and the original clustered gap finish

A wider input band contains enough shifts by rounding the pivot
coordinate. Each output shell face has one fewer free integral
coordinate. The finite multiplier from the rank comparison gives
an actual Fourier gap on the original atomic record.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UniformDiscrete UnitAddTorus
open scoped ENNReal FourierTransform Topology

/-- Integer choices in a fixed-width spectral section have a uniform
finite code, regardless of the contribution of the other coordinates. -/
theorem exists_integer_slab_coordinate_code
    (a b c : ℝ) (hc : c ≠ 0) :
    ∃ (M : ℕ) (code : ℝ → ℤ → ℕ),
      (∀ (t : ℝ) (m : ℤ), t + (m : ℝ) * c ∈ Ioo a b → code t m < M) ∧
      ∀ (t : ℝ) (m n : ℤ), t + (m : ℝ) * c ∈ Ioo a b →
        t + (n : ℝ) * c ∈ Ioo a b → code t m = code t n → m = n := by
  let e (m : ℤ) := if 0 ≤ c then m else -m
  have he (m : ℤ) : (e m : ℝ) * |c| = (m : ℝ) * c := by
    unfold e
    split
    · next h => rw [abs_of_nonneg h]
    · next h => rw [Int.cast_neg, abs_of_neg (lt_of_not_ge h)]; ring
  have hpos := abs_pos.mpr hc
  let l (t : ℝ) := ⌊(a - t) / |c|⌋
  let code (t : ℝ) (m : ℤ) := (e m - l t).toNat
  obtain ⟨M, hM⟩ := exists_nat_gt ((b - a) / |c| + 1)
  have hRange (t : ℝ) (m : ℤ) (hm : t + (m : ℝ) * c ∈ Ioo a b) :
      0 ≤ e m - l t ∧ ((e m - l t : ℤ) : ℝ) < (b - a) / |c| + 1 := by
    have h₀ : ((l t : ℤ) : ℝ) ≤ (a - t) / |c| := Int.floor_le _
    have h₁ : (a - t) / |c| < (l t : ℝ) + 1 := Int.lt_floor_add_one _
    have hb : (a - t) / |c| < (e m : ℝ) ∧ (e m : ℝ) < (b - t) / |c| := by
      constructor
      · apply (div_lt_iff₀ hpos).mpr
        rw [he]
        linarith [hm.1]
      · apply (lt_div_iff₀ hpos).mpr
        rw [he]
        linarith [hm.2]
    refine ⟨?_, ?_⟩
    · have hle : (l t : ℝ) ≤ (e m : ℝ) := h₀.trans hb.1.le
      exact sub_nonneg.mpr (by exact_mod_cast hle)
    · rw [Int.cast_sub]
      simp only [sub_div] at h₁ hb ⊢
      linarith [hb.2]
  refine ⟨M, code, ?_, ?_⟩
  · intro t m hm
    have h := hRange t m hm
    have hCast : (code t m : ℝ) = ((e m - l t : ℤ) : ℝ) := by
      rw [← Int.cast_natCast]
      exact congrArg (fun v : ℤ => (v : ℝ)) (Int.toNat_of_nonneg h.1)
    exact_mod_cast (hCast ▸ h.2).trans hM
  · intro t m n hm hn hEq
    have hh := congrArg (fun i : ℕ => (i : ℤ)) hEq
    change ((e m - l t).toNat : ℤ) = ((e n - l t).toNat : ℤ) at hh
    rw [Int.toNat_of_nonneg (hRange t m hm).1, Int.toNat_of_nonneg (hRange t n hn).1] at hh
    have hh' : e m = e n := sub_left_inj.mp hh
    by_cases hs : 0 ≤ c <;> simpa [e, hs] using hh'

/-- A bounded spectral slab meets the fixed-width integral coordinate
shell in at most a constant times the number of free two-face tuples. -/
theorem exists_ncard_slab_shell_le {d : Type*} [Fintype d]
    (L : (d → ℤ) →+ ℝ) (β : d → ℝ) (hL : ∀ x, L x = torusDirectionalFrequency β x)
    (hβ : ∀ i, β i ≠ 0) (hRank : 2 ≤ Fintype.card d)
    (a b : ℝ) (R : ℕ) :
    ∃ C : ℕ, ∀ N : ℕ, ({k | L k ∈ Ioo a b} ∩
      (integerCoordinateCube ((N : ℤ) + R) \ integerCoordinateCube ((N : ℤ) - R - 1))).ncard ≤
        C * (2 * (N + R) + 1) ^ (Fintype.card d - 2) := by
  classical
  have : Nontrivial d := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  choose p hp using (fun i : d => exists_ne i)
  choose M code hCode hCodeInj using (fun i : d => exists_integer_slab_coordinate_code a b (β i) (hβ i))
  let C := (2 * (2 * R + 1)) * ∑ i : d, M (p i)
  refine ⟨C, fun N => ?_⟩
  let O : ℤ := (N : ℤ) + R
  let I : ℤ := (N : ℤ) - R
  let J := {k | L k ∈ Ioo a b} ∩ (integerCoordinateCube O \ integerCoordinateCube (I - 1))
  have hJ : J.Finite := (integerCoordinateCube_finite O).subset (fun n hn => hn.2.1)
  let : Fintype J := hJ.fintype
  let F := Icc I O ∪ Icc (-O) (-I)
  let U := Icc (-O) O
  let : Fintype F := ((finite_Icc I O).union (finite_Icc (-O) (-I))).fintype
  let : Fintype U := (finite_Icc (-O) O).fintype
  have hIcc (x y : ℤ) : (Icc x y).ncard = (y + 1 - x).toNat := by
    rw [← Set.fintypeCard_eq_ncard, Fintype.card_Icc, Int.card_Icc]
  have hF : Fintype.card F ≤ 2 * (2 * R + 1) := by
    rw [Set.fintypeCard_eq_ncard]
    change (Icc I O ∪ Icc (-O) (-I)).ncard ≤ _
    calc
      _ ≤ (Icc I O).ncard + (Icc (-O) (-I)).ncard := Set.ncard_union_le _ _
      _ = _ := by rw [hIcc, hIcc]; dsimp [I, O]; omega
  have hU : Fintype.card U = 2 * (N + R) + 1 := by
    rw [Set.fintypeCard_eq_ncard]
    change (Icc (-O) O).ncard = _
    rw [hIcc]
    dsimp [O]
    omega
  have heach (n : J) : ∃ i : d, I ≤ |n.1 i| := by
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, |n.1 i| ≤ I - 1 from n.2.2.2)
    exact ⟨i, by omega⟩
  choose face hFace using heach
  have hnU (n : J) (i : d) : n.1 i ∈ U := by
    change -O ≤ n.1 i ∧ n.1 i ≤ O
    exact abs_le.mp (n.2.2.1 i)
  have hnF (n : J) (i : d) (hi : face n = i) : n.1 i ∈ F := by
    have hLower : I ≤ |n.1 i| := hi ▸ hFace n
    obtain ⟨hl, hu⟩ := hnU n i
    by_cases hn : 0 ≤ n.1 i
    · rw [abs_of_nonneg hn] at hLower
      exact Or.inl ⟨hLower, hu⟩
    · rw [abs_of_neg (lt_of_not_ge hn)] at hLower
      exact Or.inr ⟨hl, by omega⟩
  let t (j : d) (n : d → ℤ) :=
    ∑ i ∈ (Finset.univ : Finset d).erase j, (n i : ℝ) * β i
  have ht (j : d) (n : d → ℤ) : t j n + (n j : ℝ) * β j = L n := by
    rw [hL, torusDirectionalFrequency]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have hFib (i : d) :
      Fintype.card {n : J // face n = i} ≤
      (2 * (2 * R + 1)) * (2 * (N + R) + 1) ^ (Fintype.card d - 2) * M (p i) := by
    let j := p i
    let D : Finset d := {i, j}
    let V := {x : d // x ∉ D}
    have hD : D.card = 2 := by
      simp [D, j, Ne.symm (hp i)]
    have hV : Fintype.card V = Fintype.card d - 2 := by
      change Fintype.card {x : d // ¬ x ∈ D} = _
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_coe, hD]
    let enc (n : {n : J // face n = i}) : F × ((x : V) → U) × Fin (M j) :=
      (⟨n.1.1 i, hnF n.1 i n.2⟩,
        (fun x => ⟨n.1.1 x.1, hnU n.1 x.1⟩),
        ⟨code j (t j n.1.1) (n.1.1 j), hCode j _ _ (by rw [ht]; exact n.1.2.1)⟩)
    have hEnc : Function.Injective enc := by
      intro n m he
      have hi : n.1.1 i = m.1.1 i := congrArg (fun a : F × ((x : V) → U) × Fin (M j) =>
        a.1.val) he
      have hOther (x : d) (hx : x ≠ j) : n.1.1 x = m.1.1 x := by
        by_cases heq : x = i
        · simpa only [heq] using hi
        · have hVx : x ∉ D := by simp [D, heq, hx]
          exact congrArg (fun a : F × ((x : V) → U) × Fin (M j) => (a.2.1 ⟨x, hVx⟩).val) he
      have htEq : t j n.1.1 = t j m.1.1 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hOther x (Finset.ne_of_mem_erase hx)]
      have hEq : code j (t j n.1.1) (n.1.1 j) = code j (t j m.1.1) (m.1.1 j) :=
        congrArg (fun a : F × ((x : V) → U) × Fin (M j) => a.2.2.val) he
      have hj : n.1.1 j = m.1.1 j := by
        apply hCodeInj j (t j n.1.1)
        · rw [ht]
          exact n.1.2.1
        · rw [htEq, ht]
          exact m.1.2.1
        · simpa only [htEq] using hEq
      apply Subtype.ext
      apply Subtype.ext
      funext x
      by_cases hx : x = j
      · simpa only [hx] using hj
      · exact hOther x hx
    calc
      _ ≤ Fintype.card (F × ((x : V) → U) × Fin (M j)) := Fintype.card_le_of_injective enc hEnc
      _ = Fintype.card F * ((2 * (N + R) + 1) ^ (Fintype.card d - 2) * M j) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hU, hV]
      _ ≤ _ := by
        rw [mul_assoc]
        gcongr
  change J.ncard ≤ _
  rw [← Set.fintypeCard_eq_ncard, ← Fintype.card_congr (Equiv.sigmaFiberEquiv face), Fintype.card_sigma]
  calc
    _ ≤ ∑ i : d, (2 * (2 * R + 1)) * (2 * (N + R) + 1) ^ (Fintype.card d - 2) * M (p i) :=
      Finset.sum_le_sum fun i _ => hFib i
    _ = _ := by
      rw [← Finset.mul_sum]
      dsimp [C]
      ac_rfl

/-- A band at least the width of a nonzero pivot frequency contains one
lift of each free coordinate tuple, with a linear coordinate bound. -/
theorem exists_bounded_slab_shift_embedding {d : Type*} [Fintype d]
    (L : (d → ℤ) →+ ℝ) (β : d → ℝ) (hL : ∀ x, L x = torusDirectionalFrequency β x)
    (p : d) (hp : β p ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      ∃ γ : ((i : {i : d // i ≠ p}) → Fin n) ↪ (d → ℤ),
        (∀ x, L (γ x) ∈ Ico 0 |β p|) ∧
        ∀ x i, |((γ x i : ℤ) : ℝ)| ≤ A * (n + 1) := by
  classical
  let c := β p
  have hc : 0 < |c| := abs_pos.mpr hp
  let B := ∑ i : d, |β i|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  let A := B / |c| + 1
  refine ⟨A, by dsimp [A]; positivity, fun n => ?_⟩
  let z (x : (i : {i : d // i ≠ p}) → Fin n) (i : d) : ℤ :=
    if hi : i ≠ p then (x ⟨i, hi⟩).val else 0
  have hz (x) (i : d) : |((z x i : ℤ) : ℝ)| ≤ n := by
    unfold z
    split
    · next h =>
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (x ⟨i, h⟩).isLt.le
    · simp
  have hzp (x) : z x p = 0 := by simp [z]
  have hzL (x) : |L (z x)| ≤ (n : ℝ) * B := by
    rw [hL, torusDirectionalFrequency, Finset.mul_sum]
    calc
      _ ≤ ∑ i : d, |((z x i : ℤ) : ℝ) * β i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hz x i) (abs_nonneg _))
  let f (x : (i : {i : d // i ≠ p}) → Fin n) : ℤ := ⌊L (z x) / |c|⌋
  let m (x : (i : {i : d // i ≠ p}) → Fin n) : ℤ := if 0 ≤ c then -f x else f x
  have hMc (x) : ((m x : ℤ) : ℝ) * c = -(f x : ℝ) * |c| := by
    dsimp [m]
    split
    · next h => rw [Int.cast_neg, abs_of_nonneg h]
    · next h => rw [abs_of_neg (lt_of_not_ge h)]; ring
  let γ (x : (i : {i : d // i ≠ p}) → Fin n) := z x + Pi.single p (m x)
  have hγ (x) : L (γ x) = L (z x) + (m x : ℝ) * c := by
    rw [show L (γ x) = L (z x) + L (Pi.single p (m x)) from L.map_add _ _, hL (Pi.single p (m x))]
    simp only [torusDirectionalFrequency, Pi.single_apply, Int.cast_ite, Int.cast_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, c]
  have hSlab (x) : L (γ x) ∈ Ico 0 |c| := by
    have h₀ : (f x : ℝ) * |c| ≤ L (z x) := (le_div_iff₀ hc).mp (Int.floor_le _)
    have h₁ : L (z x) < ((f x : ℝ) + 1) * |c| := (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)
    rw [hγ, hMc]
    exact ⟨by linarith, by linarith⟩
  have hInjective : Function.Injective γ := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i.val
    simp only [γ, Pi.add_apply, Pi.single_eq_of_ne i.property, add_zero, z, dite_eq_left i.property] at hi
    apply Fin.ext
    exact_mod_cast hi
  refine ⟨⟨γ, hInjective⟩, hSlab, fun x i => ?_⟩
  by_cases hi : i = p
  · subst i
    have hP : γ x p = m x := by simp [γ, hzp]
    have hMul : |(m x : ℝ)| * |c| ≤ (n : ℝ) * B + |c| := by
      rw [← abs_mul, show (m x : ℝ) * c = L (γ x) - L (z x) by linarith [hγ x]]
      calc
        _ ≤ |L (γ x)| + |L (z x)| := by
          simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (L (γ x)) 0 (L (z x)))
        _ ≤ _ := by
          rw [abs_of_nonneg (hSlab x).1]
          linarith [(hSlab x).2, hzL x]
    change |(γ x p : ℝ)| ≤ A * (n + 1)
    rw [hP]
    refine ((le_div_iff₀ hc).mpr hMul).trans ?_
    rw [add_div, mul_div_assoc, div_self hc.ne']
    dsimp [A]
    nlinarith [div_nonneg hB hc.le, Nat.cast_nonneg (α := ℝ) n]
  · change |(γ x i : ℝ)| ≤ A * (n + 1)
    rw [show γ x i = z x i by simp [γ, Pi.single_eq_of_ne hi]]
    exact (hz x i).trans (by
      dsimp [A]
      nlinarith [div_nonneg hB hc.le, Nat.cast_nonneg (α := ℝ) n])


local notation "SeqL2(" G ")" => lp (fun _ : G => ℂ) 2

private theorem exists_finite_band_solution_of_subsingleton {d : Type*} [Fintype d] [Subsingleton d]
    (L : (d → ℤ) →+ ℝ) (β : d → ℝ) (hL : ∀ x, L x = torusDirectionalFrequency β x)
    (hβ : ∀ i, β i ≠ 0) (u : (d → ℤ) → ℂ) (W₀ : ℝ) (r : SeqL2(d → ℤ)) (hr : r ≠ 0)
    (hBand : ∀ j : d → ℤ, r j ≠ 0 → L j ∈ Icc 0 W₀)
    (hRows : ∀ k : d → ℤ, (∑' j : d → ℤ, r j * u (k - j)) = 0) :
    ∃ p : (d → ℤ) →₀ ℂ, p ≠ 0 ∧ ∀ k : d → ℤ, annihilatorArrayConvolution p u k = 0 := by
  classical
  choose R hR using (fun i : d => exists_nat_gt (W₀ / |β i|))
  have hS : (Function.support (⇑r : (d → ℤ) → ℂ)).Finite := by
    apply (Set.Finite.pi' (fun i : d => finite_Icc (-(R i : ℤ)) (R i : ℤ))).subset
    intro j hj i
    have hb := hBand j hj
    have hSingle : L j = (j i : ℝ) * β i := by
      rw [hL, torusDirectionalFrequency]
      exact Finset.sum_eq_single i (fun x _ hx => (hx (Subsingleton.elim _ _)).elim) (by simp)
    have hMul : |(j i : ℝ)| * |β i| ≤ W₀ := by
      rw [← abs_mul, ← hSingle, abs_of_nonneg hb.1]
      exact hb.2
    have hAbs : |(j i : ℝ)| ≤ R i :=
      ((le_div_iff₀ (abs_pos.mpr (hβ i))).mpr hMul).trans (hR i).le
    change j i ∈ Icc (-(R i : ℤ)) (R i : ℤ)
    have hInt : |j i| ≤ (R i : ℤ) := by exact_mod_cast hAbs
    exact abs_le.mp hInt
  let p := Finsupp.onFinset hS.toFinset (⇑r)
    (fun j hj => hS.mem_toFinset.mpr hj)
  have hp (j : d → ℤ) : p j = r j := Finsupp.onFinset_apply
  refine ⟨p, ?_, fun k => ?_⟩
  · intro h
    apply hr
    ext j
    have hj := hp j
    rw [h, Finsupp.zero_apply] at hj
    exact hj.symm
  · unfold annihilatorArrayConvolution
    have hS : (∑' j : d → ℤ, p j * u (k - j)) = ∑ j ∈ p.support, p j * u (k - j) :=
      tsum_eq_sum fun j hj => by rw [Finsupp.notMem_support_iff.mp hj, zero_mul]
    rw [← hS]
    simpa only [hp] using hRows k

/-- A nonzero bounded-band solution of all original rows yields a nonzero
finite solution on any fixed bounded open output interval. The input
band can be widened by one pivot frequency to place the shift columns. -/
theorem exists_finite_band_convolution_solution_of_global_rows {d : Type*} [Fintype d]
    (L : (d → ℤ) →+ ℝ) (β : d → ℝ) (hL : ∀ x, L x = torusDirectionalFrequency β x)
    (hβ : ∀ i, β i ≠ 0)
    (u : (d → ℤ) → ℂ) (hu : FrequencyLocallyFinite L u)
    (W₀ : ℝ) (r : SeqL2(d → ℤ)) (hr : r ≠ 0)
    (hBand : ∀ j : d → ℤ, r j ≠ 0 → L j ∈ Icc 0 W₀)
    (hRows : ∀ k : d → ℤ, (∑' j : d → ℤ, r j * u (k - j)) = 0)
    (a b : ℝ) :
    ∃ p : (d → ℤ) →₀ ℂ, p ≠ 0 ∧
      ∀ k : d → ℤ, L k ∈ Ioo a b → annihilatorArrayConvolution p u k = 0 := by
  classical
  by_cases hRank : 2 ≤ Fintype.card d
  swap
  · have : Subsingleton d := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨p, hp, hRow⟩ :=
      exists_finite_band_solution_of_subsingleton L β hL hβ u W₀ r hr hBand hRows
    exact ⟨p, hp, fun k _ => hRow k⟩
  have : Nonempty d := Fintype.card_pos_iff.mp (by omega)
  let i₀ : d := Classical.choice ‹Nonempty d›
  let W := W₀ + |β i₀|
  let D := originalConvolutionWindow L u hu W a b
  let R := D.sup (fun m => (Finset.univ : Finset d).sup (fun i => (m i).natAbs))
  have hWindow : ∀ m ∈ D, m ∈ integerCoordinateCube (R : ℤ) := by
    intro m hm i
    have h1 : (m i).natAbs ≤ (Finset.univ : Finset d).sup (fun j => (m j).natAbs) :=
      Finset.le_sup (f := fun j : d => (m j).natAbs) (Finset.mem_univ i)
    have h2 : (Finset.univ : Finset d).sup (fun j => (m j).natAbs) ≤ R :=
      Finset.le_sup (f := fun v : d → ℤ => (Finset.univ : Finset d).sup (fun j => (v j).natAbs)) hm
    rw [← Int.natCast_natAbs]
    exact_mod_cast (h1.trans h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n : d → ℤ, r n ≠ 0 := by
    by_contra h
    apply hr
    ext n
    exact not_ne_iff.mp (fun hn => h ⟨n, hn⟩)
  have hValue : 0 < ‖r n₀‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hn₀)
  obtain ⟨C, hShell⟩ := exists_ncard_slab_shell_le L β hL hβ hRank a b R
  obtain ⟨A, hA, hShifts⟩ := exists_bounded_slab_shift_embedding L β hL i₀ (hβ i₀)
  let B := ∑ i : d, |(n₀ i : ℝ)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Q, hQ⟩ := exists_nat_gt (A + B)
  let P := 4 * Q + 2 * R + 1
  let k := Fintype.card d - 2
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((C : ℝ) * (P : ℝ) ^ k * ‖r‖ ^ 2 / ‖r n₀‖ ^ 2))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hnLarge : (C : ℝ) * (P : ℝ) ^ k * ‖r‖ ^ 2 < (n : ℝ) * ‖r n₀‖ ^ 2 :=
    (div_lt_iff₀ hValue).mp ((le_max_right _ _).trans_lt hn)
  let N := Q * (n + 1)
  obtain ⟨γ, hγ, hγBound⟩ := hShifts n
  have hCenter (v) : n₀ + γ v ∈ integerCoordinateCube (N : ℤ) := by
    intro i
    have hb : |(n₀ i : ℝ)| ≤ B := Finset.single_le_sum
      (f := fun j : d => |(n₀ j : ℝ)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hInt : |((n₀ i + γ v i : ℤ) : ℝ)| ≤ N := by
      rw [Int.cast_add]
      calc
        _ ≤ |(n₀ i : ℝ)| + |(γ v i : ℝ)| := abs_add_le _ _
        _ ≤ B + A * (n + 1) := add_le_add hb (hγBound v i)
        _ ≤ _ := by
          dsimp [N]
          push_cast
          nlinarith [mul_nonneg hB hn0.le, mul_nonneg (sub_nonneg.mpr hQ.le) (show 0 ≤ (n : ℝ) + 1 by positivity)]
    exact_mod_cast hInt
  have hΓ (v) : L (γ v) ∈ Icc 0 (W - W₀) := by
    have h := hγ v
    exact ⟨h.1, by dsimp [W]; linarith [h.2]⟩
  have hP : (2 * (N + R) + 1 : ℕ) ≤ P * n := by
    have hPReal : ((2 * (N + R) + 1 : ℕ) : ℝ) ≤ ((P * n : ℕ) : ℝ) := by
      dsimp [P, N]
      push_cast
      have h1 : 0 ≤ (Q : ℝ) * ((n : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hn1.le)
      have h2 : 0 ≤ (R : ℝ) * ((n : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hn1.le)
      nlinarith
    exact_mod_cast hPReal
  let J := {j | L j ∈ Ioo a b} ∩
    (integerCoordinateCube ((N : ℤ) + R) \ integerCoordinateCube ((N : ℤ) - R - 1))
  have hCard : (J.ncard : ℝ) ≤ (C : ℝ) * ((P : ℝ) * n) ^ k := by
    have h : J.ncard ≤ C * (P * n) ^ k :=
      (hShell N).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP _))
    exact_mod_cast h
  have hRest : Fintype.card {i : d // i ≠ i₀} = Fintype.card d - 1 := by
    rw [Fintype.card_subtype_compl (fun i : d => i = i₀), Fintype.card_subtype_eq]
  have hInput : (Fintype.card ((i : {i : d // i ≠ i₀}) → Fin n) : ℝ) = (n : ℝ) ^ (k + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, hRest, Nat.cast_pow]
    have h : Fintype.card d - 1 = k + 1 := by dsimp [k]; omega
    rw [h]
  have hSize : (J.ncard : ℝ) * ‖r‖ ^ 2 <
      (Fintype.card ((i : {i : d // i ≠ i₀}) → Fin n) : ℝ) * ‖r n₀‖ ^ 2 := by
    calc
      _ ≤ ((C : ℝ) * ((P : ℝ) * n) ^ k) * ‖r‖ ^ 2 := mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
      _ = ((C : ℝ) * (P : ℝ) ^ k * ‖r‖ ^ 2) * (n : ℝ) ^ k := by rw [mul_pow]; ring
      _ < ((n : ℝ) * ‖r n₀‖ ^ 2) * (n : ℝ) ^ k := mul_lt_mul_of_pos_right hnLarge (pow_pos hn0 _)
      _ = _ := by rw [hInput, pow_succ]; ring
  obtain ⟨p, hp, _, hRows⟩ := exists_finite_band_convolution_solution_of_card_shell_lt
    L u hu W₀ W a b r hBand hRows (N : ℤ) (R : ℤ) (Int.natCast_nonneg R) hWindow n₀ γ hCenter hΓ hSize
  exact ⟨p, hp, hRows⟩

/-- Strictly above the physical upper uniform Beurling density, the
actual atomic Fourier gap forces the whole distribution to vanish. -/
theorem spectralGapUniqueness_of_upperUniformBeurlingDensity_lt
    (A : LocallyFiniteCarrier) (R : ℝ) (hR : 0 < R)
    (hDensity : upperUniformBeurlingDensity A < ENNReal.ofReal (2 * R)) :
    SpectralGapUniqueness A R := by
  obtain ⟨ε, hε, L₀, hL₀, hBound⟩ :=
    (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt A (by positivity : 0 ≤ 2 * R)).mpr hDensity
  intro T hAt hGap
  by_contra hNe
  let c := 2 * R - ε / 2
  let B := 2 * R - ε
  have hc : c < 2 * R := by dsimp [c]; linarith
  have hAtomic := (atomicOnCarrier_iff_hasLocallyAtomicAction A T).mpr hAt
  have hLow : ∀ᶠ r : ℝ in atTop, c * r ≤ (originalRayCount A true r : ℝ) :=
    atomicFourierGapRayLowerBound A T R hR hNe hAtomic hGap true c hc
  let M := max 1 (max L₀ ((|B| + 1) / (ε / 2)))
  obtain ⟨r, hLo, hr⟩ := (hLow.and (eventually_ge_atTop M)).exists
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrL : L₀ ≤ r + 1 := by
    have h := ((le_max_left L₀ _).trans (le_max_right 1 _)).trans hr
    linarith
  have hrMass : |B| + 1 ≤ (ε / 2) * r := by
    have hn := ((le_max_right L₀ _).trans (le_max_right 1 _)).trans hr
    have h := (div_le_iff₀ (show 0 < ε / 2 by positivity)).mp hn
    simpa only [mul_comm] using h
  have hCount : originalRayCount A true r ≤ windowCount A 0 (r + 1) := by
    unfold originalRayCount originalRayWindow windowCount
    simp only [ite_true, zero_add]
    have hFinite : (A.carrier ∩ Ico 0 (r + 1)).Finite := by
      simpa only [zero_add] using A.finite_window 0 (r + 1)
    apply Set.ncard_le_ncard _ hFinite
    rintro x ⟨hx, hlo, hhi⟩
    exact ⟨hx, hlo, by linarith⟩
  have hUpper : (originalRayCount A true r : ℝ) ≤ B * (r + 1) :=
    (by exact_mod_cast hCount : (originalRayCount A true r : ℝ) ≤ windowCount A 0 (r + 1)).trans
      (hBound (r + 1) hrL 0)
  dsimp [B, c] at hUpper hLo hrMass
  nlinarith [le_abs_self (2 * R - ε)]

/-- A uniform real unit-window cap gives a positive strict Beurling gap radius. -/
theorem exists_strict_upperDensity_radius_of_unit_window_bound (A : LocallyFiniteCarrier)
    (K : ℕ) (hK : ∀ r, windowCount A r 1 ≤ K) :
    ∃ R : ℝ, 0 < R ∧ upperUniformBeurlingDensity A < ENNReal.ofReal (2 * R) := by
  let R : ℝ := K + 2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt A (by positivity)).mp ?_⟩
  have hNat (n : ℕ) (x : ℝ) : windowCount A x (n : ℝ) ≤ K * n := by
    induction n with
    | zero => simp [windowCount]
    | succ n ih =>
        rw [Nat.cast_succ, A.windowCount_add x n 1 (Nat.cast_nonneg n) zero_le_one, Nat.mul_succ]
        exact Nat.add_le_add ih (hK _)
  refine ⟨1, zero_lt_one, 1, zero_lt_one, fun L hL x => ?_⟩
  let n := ⌈L⌉₊
  have hLen : L ≤ n := Nat.le_ceil _
  have htle : (n : ℝ) ≤ 2 * L := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
    exact h.le.trans (by linarith)
  have hs := (A.windowCount_mono_length (a := x) hLen).trans (hNat n x)
  have hsReal : (windowCount A x L : ℝ) ≤ (K : ℝ) * n := by exact_mod_cast hs
  calc
    _ ≤ (K : ℝ) * n := hsReal
    _ ≤ (K : ℝ) * (2 * L) := mul_le_mul_of_nonneg_left htle (Nat.cast_nonneg K)
    _ ≤ _ := by dsimp [R]; nlinarith

/-- Zero original rows on an interval containing the closed test window
give an actual distributional Fourier gap of the finite product. -/
theorem finiteExponentialMultiplication_eq_zero_of_original_window_rows
    {G : Type*} [AddCommGroup G] (L : G →+ ℝ) (B A : LocallyFiniteCarrier)
    (label : B.subtype → G) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (T : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (R : ℝ) (hGap : SpectralGapUniqueness A R) (p : G →₀ ℂ)
    (hRows : ∀ n, L n ∈ Icc (-R) R → annihilatorArrayConvolution p (originalFourierArray L B T) n = 0) :
    finiteExponentialMultiplication (fun i : p.support => L i.1) (fun i : p.support => p i.1) T = 0 := by
  classical
  let a (i : p.support) := L i.1
  let c (i : p.support) := p i.1
  apply hGap
  · apply atomicOnCarrier_hasLocallyAtomicAction
    intro f hf
    rw [finiteExponentialMultiplication_apply]
    apply hA
    intro x hx
    rw [finiteCombSchwartzSymbol_apply, hf x hx, mul_zero]
  · rw [fourier_finiteExponentialMultiplication]
    apply vanishesOnInterval_finiteCombConvolution_of_windowMap_eq_zero B _ hB
    ext x
    change (∑ i : p.support, c i * extendedAtomicCoefficient B (𝓕 T) ((x : ℝ) - a i)) = 0
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property.1
    obtain ⟨b, hb, he⟩ := (B.mem_translate (a i) x).mp hi
    let n := i.1 + label ⟨b, hb⟩
    have hn : L n = (x : ℝ) := by rw [map_add, hLabel]; exact he
    change (∑ j : p.support, p j.1 * extendedAtomicCoefficient B (𝓕 T) ((x : ℝ) - L j.1)) = 0
    rw [p.support.sum_coe_sort (fun j : G => p j * extendedAtomicCoefficient B (𝓕 T) ((x : ℝ) - L j)), ← hn]
    have hrow := hRows n (hn.symm ▸ x.property.2)
    simpa only [annihilatorArrayConvolution, originalFourierArray, map_sub] using hrow


/-- Use the original normalized phase Haar measure. -/
local instance originalLocalizationCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance originalLocalizationCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A finite polynomial in the original spectral module contains every
active physical atom, assuming the weighted spectrum and common
translated Schwartz bound used to construct the original hull. -/
theorem exists_originalModule_finite_annihilator_of_translated_schwartz_bound
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : LocallyFiniteCarrier) (β : d → ℝ) (L : (d → ℤ) →+ ℝ)
    (hL : Function.Injective L) (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hA : AtomicOnCarrier A μ) (hB : AtomicOnCarrier B (𝓕 μ))
    (hActual : ∀ x : A.subtype, μ (A.isolationSchwartz x) ≠ 0)
    {K : ℕ} (hCount : ∀ x, windowCount A x 1 ≤ K)
    (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 ≤ D)
    (hUniform : ∀ (t : ℝ) (g : SchwartzMap ℝ ℂ),
      ‖combDistributionTranslation (-t) μ g‖ ≤
        D * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) g) :
    ∃ p : (d → ℤ) →₀ ℂ, p ≠ 0 ∧
      (∃ y : ℝ, annihilatorExponentialSymbol L p y ≠ 0) ∧
      (∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) ∧
      finiteExponentialMultiplication (fun i : p.support => L i.1) (fun i : p.support => p i.1) μ = 0 := by
  classical
  have hSupp : DistributionSupportedOn A.carrier μ := by
    intro f _ hf
    exact hA f fun x hx => (hf x hx).eq_of_nhds
  have hβ (i : d) : β i ≠ 0 := by
    intro h
    let j : d → ℤ := Pi.single i 1
    have hj : L j = L 0 := by
      rw [map_zero, hLfreq, torusDirectionalFrequency]
      simp [j, Pi.single_apply, ite_mul, Finset.sum_ite_eq', h]
    have he : j i = (0 : d → ℤ) i := congrFun (hL hj) i
    simp [j] at he
  obtain ⟨R, hR, hρ⟩ := exists_strict_upperDensity_radius_of_unit_window_bound A K hCount
  obtain ⟨W, f, _, hf, hBand, hRows⟩ :=
    exists_bounded_band_originalFourierArray_annihilator_of_translated_schwartz_bound
      A B β L hL hLfreq label hLabel N μ hν hSupp hCount q hq D hD hUniform
  let e := (mFourierBasis (d := d)).repr
  let r := e f
  have hr : r ≠ 0 := fun h => hf (e.injective (h.trans e.map_zero.symm))
  have hrDef (n : d → ℤ) : r n = mFourierCoeff f n := mFourierBasis_repr f n
  have hrBand (n : d → ℤ) (hn : r n ≠ 0) : L n ∈ Icc 0 W := by
    by_contra h
    exact hn ((hrDef n).trans (hBand n h))
  have hrRows (k : d → ℤ) : (∑' j : d → ℤ, r j * originalFourierArray L B μ (k - j)) = 0 := by
    simp only [hrDef, hRows]
  obtain ⟨p, hp, hpRows⟩ := exists_finite_band_convolution_solution_of_global_rows
    L β hLfreq hβ (originalFourierArray L B μ) (originalFourierArray_frequencyLocallyFinite L hL B μ)
    W r hr hrBand hrRows (-R - 1) (R + 1)
  have hAζ := finiteExponentialMultiplication_eq_zero_of_original_window_rows L B A label hLabel μ hA hB
    R (spectralGapUniqueness_of_upperUniformBeurlingDensity_lt A R hR hρ) p (fun n hn =>
      hpRows n ⟨by linarith [hn.1], by linarith [hn.2]⟩)
  have hCoeff : (fun i : p.support => p i.1) ≠ 0 := by
    intro h
    apply hp
    ext n
    by_cases hn : n ∈ p.support
    · exact congrFun h ⟨n, hn⟩
    · exact Finsupp.notMem_support_iff.mp hn
  have hFreq : Function.Injective (fun i : p.support => L i.1) :=
    hL.comp Subtype.val_injective
  have hSymbol (x : ℝ) : (∑ j : p.support, p j.1 * combModulationCharacter (L j.1) x) =
      annihilatorExponentialSymbol L p x :=
    p.support.sum_coe_sort (fun j => p j * combModulationCharacter (L j) x)
  refine ⟨p, hp, ?_, ?_, hAζ⟩
  · obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero
      (fun i : p.support => L i.1) hFreq (fun i : p.support => p i.1) hCoeff
    exact ⟨y, fun h => hy ((hSymbol y).trans h)⟩
  · intro x hx
    rw [← hSymbol]
    exact finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom A μ hA _ _ hAζ ⟨x, hx⟩ (hActual ⟨x, hx⟩)

end
end MeyerGeneralProblem
