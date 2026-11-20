import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Classical in

/- English proof (translation)
Establish `hPP : (P * P).Monic` using `hP.mul hP`. Establish `hcard : Fintype.card (Fin (N - 2 * j) → K) = Fintype.card K ^ (N - 2 * j)` using `by simp`. Rewrite using `[← hcard, ← Finset.card_univ]`. Apply `Finset.card_le_card_of_injOn (fun c => fun i : Fin (N - 2 * j) => ((monicOf c) /ₘ (P * P)).coeff i)` to reduce the goal to its premises. Introduce `c _`.

Conclude with `Finset.mem_coe.mpr (Finset.mem_univ _)`. Establish `key : ∀ c : Fin N → K, P * P ∣ monicOf c → ((monicOf c) /ₘ (P * P)).Monic ∧ ((monicOf c) /ₘ (P * P)).natDegree = N - 2 * j ∧ monicOf c = P * P * ((monicOf c) /ₘ (P * P))`. Introduce `c hc`. Take `⟨g, hg⟩` from `hc`. Establish `hdiv : (monicOf c) /ₘ (P * P) = g`.

Rewrite using `[hg]`. Conclude with `mul_divByMonic_cancel_left g hPP`. Establish `hgm : g.Monic` using `hPP.of_mul_monic_left (hg ▸ monicOf_monic c)`. Establish `hdeg : (monicOf c).natDegree = (P * P).natDegree + g.natDegree`. Rewrite using `[hg]`.

Conclude with `hPP.natDegree_mul hgm`. Rewrite `hdeg` using `[monicOf_natDegree, hP.natDegree_mul hP, hj]`. Rewrite using `[hdiv]`. Conclude with `⟨hgm, by omega, hg⟩`. Introduce `c hc c' hc' h`.

Take `⟨h1, h2, h3⟩` from `key c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2`. Take `⟨h1', h2', h3'⟩` from `key c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2`. Apply `monicOf_injective` to reduce the goal to its premises. Rewrite using `[h3, h3', ← monicOf_coeffs h1 h2, ← monicOf_coeffs h1' h2']`. Conclude with `congrArg (fun v => P * P * monicOf v) h`.
-/
theorem card_mult_le {K : Type} [Field K] [Fintype K] (N j : ℕ) (P : K[X]) (hP : P.Monic)
    (hj : P.natDegree = j) :
    ((Finset.univ : Finset (Fin N → K)).filter (fun c => P * P ∣ monicOf c)).card
      ≤ Fintype.card K ^ (N - 2 * j) := by
  have hPP : (P * P).Monic := hP.mul hP
  have hcard : Fintype.card (Fin (N - 2 * j) → K) = Fintype.card K ^ (N - 2 * j) := by simp
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn
    (fun c => fun i : Fin (N - 2 * j) => ((monicOf c) /ₘ (P * P)).coeff i)
  · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · have key : ∀ c : Fin N → K, P * P ∣ monicOf c →
        ((monicOf c) /ₘ (P * P)).Monic ∧ ((monicOf c) /ₘ (P * P)).natDegree = N - 2 * j ∧
        monicOf c = P * P * ((monicOf c) /ₘ (P * P)) := by
      intro c hc
      obtain ⟨g, hg⟩ := hc
      have hdiv : (monicOf c) /ₘ (P * P) = g := by
        rw [hg]; exact mul_divByMonic_cancel_left g hPP
      have hgm : g.Monic := hPP.of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P * P).natDegree + g.natDegree := by
        rw [hg]; exact hPP.natDegree_mul hgm
      rw [monicOf_natDegree, hP.natDegree_mul hP, hj] at hdeg
      rw [hdiv]
      exact ⟨hgm, by omega, hg⟩
    intro c hc c' hc' h
    obtain ⟨h1, h2, h3⟩ := key c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    obtain ⟨h1', h2', h3'⟩ := key c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
    apply monicOf_injective
    rw [h3, h3', ← monicOf_coeffs h1 h2, ← monicOf_coeffs h1' h2']
    exact congrArg (fun v => P * P * monicOf v) h

/- English proof (translation)
Establish `key : ∀ m, 1 ≤ m → m ≤ N → (∑ j ∈ Finset.Icc 2 m, q ^ (N - j)) * (q - 1) + q ^ (N - m) = q ^ (N - 1)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro h`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ m ih`. Introduce `h1 h2`. Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_Icc_succ_top (by omega), add_mul, add_assoc]`. Establish `e : q ^ (N - (m + 1)) * (q - 1) + q ^ (N - (m + 1)) = q ^ (N - m)`. Establish `h3 : N - m = (N - (m + 1)) + 1` using `by omega`. Rewrite using `[h3, pow_succ, ← Nat.mul_succ]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `ih hm (by omega)`. Distinguish the cases in `hm1 : 1 ≤ m`. Establish `h` using `key m hm1 hm`.

Establish `hN1 : q ^ (N - 1) = q ^ (N - 2) * q`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Take `⟨p, hp⟩ : ∃ p, q = p + 2` from `⟨q - 2, by omega⟩`.

Substitute `hp` using the available equality. Establish `hq1 : p + 2 - 1 = p + 1` using `by omega`. Rewrite `h` using `[hq1, hN1]`. Use `set S := ∑ j ∈ Finset.Icc 2 m, (p + 2) ^ (N - j)`. Use `set Q := (p + 2) ^ (N - 2)`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4` using `Nat.mul_le_mul_right (p + 1) (show 2 * Q + 1 ≤ S by omega)`. Use `clear_value S Q`. Use `ring_nf at h h4`.

Use polynomial arithmetic with `[Nat.zero_le (p * Q), Nat.zero_le ((2 + p) ^ (N - m))]`. Establish `: m = 0` using `by omega`. Substitute `this` using the available equality. Simplify using the standard rewrite rules.
-/
theorem geom_tail (q N m : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) (hm : m ≤ N) :
    ∑ j ∈ Finset.Icc 2 m, q ^ (N - j) ≤ 2 * q ^ (N - 2) := by
  have key : ∀ m, 1 ≤ m → m ≤ N →
      (∑ j ∈ Finset.Icc 2 m, q ^ (N - j)) * (q - 1) + q ^ (N - m) = q ^ (N - 1) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · rw [Finset.sum_Icc_succ_top (by omega), add_mul, add_assoc]
        have e : q ^ (N - (m + 1)) * (q - 1) + q ^ (N - (m + 1)) = q ^ (N - m) := by
          have h3 : N - m = (N - (m + 1)) + 1 := by omega
          rw [h3, pow_succ, ← Nat.mul_succ]
          congr 1
          omega
        rw [e]
        exact ih hm (by omega)
  by_cases hm1 : 1 ≤ m
  · have h := key m hm1 hm
    have hN1 : q ^ (N - 1) = q ^ (N - 2) * q := by
      rw [← pow_succ]; congr 1; omega
    obtain ⟨p, hp⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    subst hp
    have hq1 : p + 2 - 1 = p + 1 := by omega
    rw [hq1, hN1] at h
    set S := ∑ j ∈ Finset.Icc 2 m, (p + 2) ^ (N - j)
    set Q := (p + 2) ^ (N - 2)
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_right (p + 1) (show 2 * Q + 1 ≤ S by omega)
    clear_value S Q
    ring_nf at h h4
    nlinarith [Nat.zero_le (p * Q), Nat.zero_le ((2 + p) ^ (N - m))]
  · have : m = 0 := by omega
    subst this
    simp

/- English proof (translation)
Introduce `K _ _ N hN`. Use `set q := Fintype.card K with hq`. Establish `hq2 : 2 ≤ q` using `Fintype.one_lt_card`. Use `set Ω := (Finset.univ : Finset (Fin N → K)) with hΩ`. Use `set Good := Ω.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hGood`.

Use `set Bad0 := Ω.filter (fun c => (monicOf c).coeff 0 = 0) with hBad0`. Use `set BadS := Ω.filter (fun c => ¬ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hBadS`. Establish `hΩcard : Ω.card = q ^ N` using `by simp [hΩ, hq]`. Establish `hcover : Ω ⊆ Good ∪ (Bad0 ∪ BadS)`. Introduce `c hc`.

Simplify using `only [hGood, hBad0, hBadS, Finset.mem_union, Finset.mem_filter]`. Distinguish the cases in `h0 : (monicOf c).coeff 0 = 0`. Conclude with `Or.inr (Or.inl ⟨hc, h0⟩)`. Distinguish the cases in `hs : Squarefree (monicOf c)`. Conclude with `Or.inl ⟨hc, hs, h0⟩`.

Conclude with `Or.inr (Or.inr ⟨hc, hs, h0⟩)`. Establish `hB0 : Bad0.card ≤ q ^ (N - 1)`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Establish `hcard : Fintype.card (Fin M → K) = q ^ (M + 1 - 1)` using `by simp [hq]`. Rewrite using `[← hcard, ← Finset.card_univ]`.

Apply `Finset.card_le_card_of_injOn (fun c => Fin.tail c)` to reduce the goal to its premises. Introduce `c _`. Conclude with `Finset.mem_coe.mpr (Finset.mem_univ _)`. Introduce `c hc c' hc' h`. Establish `h0 : c 0 = 0`.

Use `(Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2` as an intermediate fact. Rewrite using `[← monicOf_coeff c 0]` and apply the resulting hypothesis. Establish `h0' : c' 0 = 0`. Use `(Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2` as an intermediate fact. Rewrite using `[← monicOf_coeff c' 0]` and apply the resulting hypothesis.

Rewrite using `[← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, h0']`. Conclude with `congrArg (Fin.cons 0) h`. Use `set I : ℕ → ℕ := fun j => ((Finset.univ : Finset (Fin j → K)).filter (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).card with hI`. Establish `hBS : BadS.card ≤ ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j)`. Establish `hsub : BadS ⊆ (Finset.Icc 1 (N / 2)).biUnion (fun j => ((Finset.univ : Finset (Fin j → K)).filter (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).biUnion (fun p => Ω.filter (fun c => monicOf p * monicOf p ∣ monicOf c)))`.

Introduce `c hc`. Take `⟨_, hns, h0⟩` from `Finset.mem_filter.mp hc`. Establish `hne : monicOf c ≠ 0` using `(monicOf_monic c).ne_zero`. Rewrite `hns` using `[squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hne]`. Use `push Not at hns`.

Take `⟨P, hPirr, hPdvd⟩` from `hns`. Use `set P' := normalize P with hP'`. Establish `hass : Associated P' P` using `normalize_associated P`. Establish `hP'irr : Irreducible P'` using `hass.symm.irreducible hPirr`. Establish `hP'mon : P'.Monic` using `monic_normalize hPirr.ne_zero`.

Establish `hP'dvd : P' * P' ∣ monicOf c` using `(mul_dvd_mul hass.dvd hass.dvd).trans hPdvd`. Take `⟨g, hg⟩` from `hP'dvd`. Establish `hgm : g.Monic` using `(hP'mon.mul hP'mon).of_mul_monic_left (hg ▸ monicOf_monic c)`. Establish `hdeg : (monicOf c).natDegree = (P' * P').natDegree + g.natDegree`. Rewrite using `[hg]`.

Conclude with `(hP'mon.mul hP'mon).natDegree_mul hgm`. Rewrite `hdeg` using `[monicOf_natDegree, hP'mon.natDegree_mul hP'mon]`. Establish `hj1 : 1 ≤ P'.natDegree` using `hP'irr.natDegree_pos`. Establish `hc0 : P'.coeff 0 ≠ 0`. Introduce `hz`.

Apply `h0` to reduce the goal to its premises. Rewrite using `[hg, mul_coeff_zero, mul_coeff_zero, hz]`. Simplify using the standard rewrite rules. Use `Finset.mem_biUnion.mpr ⟨P'.natDegree, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, ?_⟩` and prove the remaining obligations. Use `Finset.mem_biUnion.mpr ⟨fun i => P'.coeff i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_filter, monicOf_coeffs hP'mon rfl]`. Conclude with `⟨Finset.mem_univ _, hP'irr, hc0⟩`. Rewrite using `[Finset.mem_filter, monicOf_coeffs hP'mon rfl]`. Conclude with `⟨Finset.mem_univ _, ⟨g, hg⟩⟩`. Use `(Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)` and prove the remaining obligations.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j _`. Use `Finset.card_biUnion_le.trans ?_` and prove the remaining obligations. Rewrite using `[hI]`. Simplify using `only`.

Rewrite using `[← smul_eq_mul, ← Finset.sum_const]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p _`. Conclude with `card_mult_le N j (monicOf p) (monicOf_monic p) (monicOf_natDegree p)`. Establish `hI1 : I 1 ≤ q - 1`.

Establish `hsub : ((Finset.univ : Finset (Fin 1 → K)).filter (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)) ⊆ (Finset.univ : Finset (Fin 1 → K)).erase 0`. Introduce `p hp`. Use `Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `(Finset.mem_filter.mp hp).2.2` as an intermediate fact.

Apply `this` to reduce the goal to its premises. Establish `h` using `monicOf_coeff (0 : Fin 1 → K) 0`. Simplify using `using h`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`.

Simplify `this` using `[hI, hq]`. Establish `hI2 : ∀ j, 2 ≤ j → 2 * I j ≤ q ^ j`. Introduce `j hj`. Establish `h1` using `irreducible_count_upper K j (by omega)`. Establish `h2 : I j ≤ ((Finset.univ : Finset (Fin j → K)).filter (fun c => Irreducible (monicOf c))).card`.

Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `p hp`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) ≤ q ^ (N - 1)`.

Break down `Nat.lt_or_ge N 2 with hlt | hge` into its components or cases. Establish `: N / 2 = 0` using `by omega`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hm1 : 1 ≤ N / 2` using `by omega`.

Rewrite using `[← Finset.add_sum_Ioc_eq_sum_Icc hm1]`. Establish `hIoc : Finset.Ioc 1 (N / 2) = Finset.Icc 2 (N / 2)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioc, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hIoc]`. Establish `h2 : 2 * ∑ j ∈ Finset.Icc 2 (N / 2), I j * q ^ (N - 2 * j) ≤ 2 * q ^ (N - 2)`. Rewrite using `[Finset.mul_sum]`. Use `le_trans (Finset.sum_le_sum (fun j hj => ?_)) (geom_tail q N (N / 2) hq2 hge (Nat.div_le_self _ _))` and prove the remaining obligations. Take `⟨hj2, hjm⟩` from `Finset.mem_Icc.mp hj`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : I 1 * q ^ (N - 2 * 1) ≤ (q - 1) * q ^ (N - 2)` using `Nat.mul_le_mul_right _ hI1`. Establish `h4 : q ^ (N - 1) = (q - 1) * q ^ (N - 2) + q ^ (N - 2)`. Establish `: N - 1 = (N - 2) + 1` using `by omega`. Rewrite using `[this, pow_succ]`.

Take `⟨r, hr⟩ : ∃ r, q = r + 1` from `⟨q - 1, by omega⟩`. Rewrite using `[hr]`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `Finset.card_le_card hcover`. Establish `h2` using `Finset.card_union_le Good (Bad0 ∪ BadS)`. Establish `h3` using `Finset.card_union_le Bad0 BadS`. Rewrite `h1` using `[hΩcard]`. Establish `h5` using `hBS.trans hsum`.

Use linear arithmetic over natural numbers and integers.
-/
theorem squarefree_count : SquarefreeCount := by
  classical
  intro K _ _ N hN
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set Ω := (Finset.univ : Finset (Fin N → K)) with hΩ
  set Good := Ω.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hGood
  set Bad0 := Ω.filter (fun c => (monicOf c).coeff 0 = 0) with hBad0
  set BadS := Ω.filter (fun c => ¬ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hBadS
  have hΩcard : Ω.card = q ^ N := by simp [hΩ, hq]
  have hcover : Ω ⊆ Good ∪ (Bad0 ∪ BadS) := by
    intro c hc
    simp only [hGood, hBad0, hBadS, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : (monicOf c).coeff 0 = 0
    · exact Or.inr (Or.inl ⟨hc, h0⟩)
    · by_cases hs : Squarefree (monicOf c)
      · exact Or.inl ⟨hc, hs, h0⟩
      · exact Or.inr (Or.inr ⟨hc, hs, h0⟩)
  have hB0 : Bad0.card ≤ q ^ (N - 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcard : Fintype.card (Fin M → K) = q ^ (M + 1 - 1) := by simp [hq]
    rw [← hcard, ← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun c => Fin.tail c)
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' h
      have h0 : c 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        rwa [← monicOf_coeff c 0]
      have h0' : c' 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
        rwa [← monicOf_coeff c' 0]
      rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, h0']
      exact congrArg (Fin.cons 0) h
  set I : ℕ → ℕ := fun j => ((Finset.univ : Finset (Fin j → K)).filter
      (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).card with hI
  have hBS : BadS.card ≤ ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) := by
    have hsub : BadS ⊆ (Finset.Icc 1 (N / 2)).biUnion (fun j =>
        ((Finset.univ : Finset (Fin j → K)).filter
          (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).biUnion (fun p =>
            Ω.filter (fun c => monicOf p * monicOf p ∣ monicOf c))) := by
      intro c hc
      obtain ⟨_, hns, h0⟩ := Finset.mem_filter.mp hc
      have hne : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hne] at hns
      push Not at hns
      obtain ⟨P, hPirr, hPdvd⟩ := hns
      set P' := normalize P with hP'
      have hass : Associated P' P := normalize_associated P
      have hP'irr : Irreducible P' := hass.symm.irreducible hPirr
      have hP'mon : P'.Monic := monic_normalize hPirr.ne_zero
      have hP'dvd : P' * P' ∣ monicOf c :=
        (mul_dvd_mul hass.dvd hass.dvd).trans hPdvd
      obtain ⟨g, hg⟩ := hP'dvd
      have hgm : g.Monic := (hP'mon.mul hP'mon).of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P' * P').natDegree + g.natDegree := by
        rw [hg]; exact (hP'mon.mul hP'mon).natDegree_mul hgm
      rw [monicOf_natDegree, hP'mon.natDegree_mul hP'mon] at hdeg
      have hj1 : 1 ≤ P'.natDegree := hP'irr.natDegree_pos
      have hc0 : P'.coeff 0 ≠ 0 := by
        intro hz
        apply h0
        rw [hg, mul_coeff_zero, mul_coeff_zero, hz]
        simp
      refine Finset.mem_biUnion.mpr ⟨P'.natDegree, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨fun i => P'.coeff i, ?_, ?_⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, hP'irr, hc0⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, ⟨g, hg⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    apply Finset.sum_le_sum
    intro j _
    refine Finset.card_biUnion_le.trans ?_
    rw [hI]
    simp only
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p _
    exact card_mult_le N j (monicOf p) (monicOf_monic p) (monicOf_natDegree p)
  have hI1 : I 1 ≤ q - 1 := by
    have hsub : ((Finset.univ : Finset (Fin 1 → K)).filter
        (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)) ⊆
        (Finset.univ : Finset (Fin 1 → K)).erase 0 := by
      intro p hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      have := (Finset.mem_filter.mp hp).2.2
      apply this
      have h := monicOf_coeff (0 : Fin 1 → K) 0
      simpa using h
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simpa [hI, hq] using this
  have hI2 : ∀ j, 2 ≤ j → 2 * I j ≤ q ^ j := by
    intro j hj
    have h1 := irreducible_count_upper K j (by omega)
    have h2 : I j ≤ ((Finset.univ : Finset (Fin j → K)).filter
        (fun c => Irreducible (monicOf c))).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
    calc 2 * I j ≤ j * I j := Nat.mul_le_mul_right _ hj
      _ ≤ j * _ := Nat.mul_le_mul_left _ h2
      _ ≤ q ^ j := h1
  have hsum : ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) ≤ q ^ (N - 1) := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · have : N / 2 = 0 := by omega
      rw [this]; simp
    · have hm1 : 1 ≤ N / 2 := by omega
      rw [← Finset.add_sum_Ioc_eq_sum_Icc hm1]
      have hIoc : Finset.Ioc 1 (N / 2) = Finset.Icc 2 (N / 2) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hIoc]
      have h2 : 2 * ∑ j ∈ Finset.Icc 2 (N / 2), I j * q ^ (N - 2 * j) ≤ 2 * q ^ (N - 2) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) (geom_tail q N (N / 2) hq2 hge
          (Nat.div_le_self _ _))
        obtain ⟨hj2, hjm⟩ := Finset.mem_Icc.mp hj
        calc 2 * (I j * q ^ (N - 2 * j)) = (2 * I j) * q ^ (N - 2 * j) := by ring
          _ ≤ q ^ j * q ^ (N - 2 * j) := Nat.mul_le_mul_right _ (hI2 j hj2)
          _ = q ^ (N - j) := by rw [← pow_add]; congr 1; omega
      have h3 : I 1 * q ^ (N - 2 * 1) ≤ (q - 1) * q ^ (N - 2) := Nat.mul_le_mul_right _ hI1
      have h4 : q ^ (N - 1) = (q - 1) * q ^ (N - 2) + q ^ (N - 2) := by
        have : N - 1 = (N - 2) + 1 := by omega
        rw [this, pow_succ]
        obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        rw [hr]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le Good (Bad0 ∪ BadS)
  have h3 := Finset.card_union_le Bad0 BadS
  rw [hΩcard] at h1
  have h5 := hBS.trans hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
