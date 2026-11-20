import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.Proof.different_power_unramified_iff

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `: Module.Free ℤ R` using `Module.free_of_finite_type_torsion_free'`. Establish `hsmul : (p : ℤ_[p]) • z = 0`. Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`. Conclude with `hz`.

Break down `smul_eq_zero.mp hsmul with h | h` into its components or cases. Conclude with `absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)`. Conclude with `h`.
-/
private lemma eq_zero_of_natCast_mul_eq_zero_op (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [Module.Finite ℤ R] (z : Op p R) (hz : (p : Op p R) * z = 0) :
    z = 0 := by
  have hp := (Fact.out : p.Prime)
  have : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hsmul : (p : ℤ_[p]) • z = 0 := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    exact hz
  rcases smul_eq_zero.mp hsmul with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
  · exact h

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hy : (p : Op p R) * y ∈ Ideal.span {1 - w.e}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]`. Conclude with `hx`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hy`.

Establish `hey : w.e * y = 0`. Apply `eq_zero_of_natCast_mul_eq_zero_op p R` to reduce the goal to its premises. Establish `hee : w.e * w.e = w.e` using `w.idem`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Conclude with `⟨y, by rw [mul_sub, mul_one, mul_comm y, hey, sub_zero]⟩`.
-/
theorem ow_p_torsionFree (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] (w : Place p R) (x : w.Ow) (hx : (p : w.Ow) * x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : (p : Op p R) * y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
  have hey : w.e * y = 0 := by
    apply eq_zero_of_natCast_mul_eq_zero_op p R
    have hee : w.e * w.e = w.e := w.idem
    calc (p : Op p R) * (w.e * y) = w.e * ((p : Op p R) * y) := by ring
      _ = w.e * (a * (1 - w.e)) := by rw [ha]
      _ = a * (w.e - w.e * w.e) := by ring
      _ = 0 := by rw [hee, sub_self, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by rw [mul_sub, mul_one, mul_comm y, hey, sub_zero]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hQM⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hQ' : Q ≤ M.comap f` using `Ideal.map_le_iff_le_comap.mp hQM`. Establish `hprime : (M.comap f).IsPrime` using `Ideal.comap_isPrime f M`. Establish `hbot : M.comap f ≠ ⊥` using `fun h => hQ (eq_bot_iff.mpr (h ▸ hQ'))`.

Establish `hmax : (M.comap f).IsMaximal` using `hprime.isMaximal hbot`. Distinguish the cases in `hPeq : M.comap f = P`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[← hPQ]`. Conclude with `(sup_eq_left.mpr (hPeq ▸ hQ')).symm`.

Apply `hM.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← h _ hmax hPeq]`. Conclude with `Ideal.map_comap_le`.
-/
theorem map_eq_top_of_coprime {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) (P : Ideal R) (hP : P.IsMaximal)
    (h : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map f = ⊤) (Q : Ideal R) (hQ : Q ≠ ⊥)
    (hPQ : P ⊔ Q = ⊤) : Q.map f = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal _ hne
  have hQ' : Q ≤ M.comap f := Ideal.map_le_iff_le_comap.mp hQM
  have hprime : (M.comap f).IsPrime := Ideal.comap_isPrime f M
  have hbot : M.comap f ≠ ⊥ := fun h => hQ (eq_bot_iff.mpr (h ▸ hQ'))
  have hmax : (M.comap f).IsMaximal := hprime.isMaximal hbot
  by_cases hPeq : M.comap f = P
  · apply hP.ne_top
    rw [← hPQ]
    exact (sup_eq_left.mpr (hPeq ▸ hQ')).symm
  · apply hM.ne_top
    rw [eq_top_iff, ← h _ hmax hPeq]
    exact Ideal.map_comap_le

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective g`. Establish `hee : w.e * w.e = w.e` using `w.idem`. Establish `hyy : y * y - y ∈ Ideal.span {1 - w.e}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]`. Conclude with `sub_eq_zero.mpr hg`.

Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hyy`. Establish `hey : w.e * (y * y) = w.e * y`. Establish `: w.e * (y * y - y) = 0`. Rewrite using `[← ha]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `this` using `[mul_sub]`. Conclude with `sub_eq_zero.mp this`. Establish `hf : IsIdempotentElem (w.e * y)` using `by show w.e * y * (w.e * y) = w.e * y`. Combine the equalities or inequalities in the displayed calculation. Establish `hfe : w.e * y * w.e = w.e * y`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmk : (Ideal.Quotient.mk (Ideal.span {1 - w.e}) y) = Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * y)`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨y, by ring⟩`. Rewrite using `[hmk]`.

Break down `w.primitive _ hf hfe with h | h` into its components or cases. Use `left`. Rewrite using `[h, map_zero]`. Use `right`. Rewrite using `[h, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - w.e})), Ideal.Quotient.eq, Ideal.mem_span_singleton']`.

Conclude with `⟨-1, by ring⟩`.
-/
private lemma isIdempotentElem_Ow_eq_zero_or_one {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]
    (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE) (g : w.Ow) (hg : IsIdempotentElem g) : g = 0 ∨ g = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hee : w.e * w.e = w.e := w.idem
  have hyy : y * y - y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
    exact sub_eq_zero.mpr hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyy
  have hey : w.e * (y * y) = w.e * y := by
    have : w.e * (y * y - y) = 0 := by
      rw [← ha]
      calc w.e * (a * (1 - w.e)) = a * (w.e - w.e * w.e) := by ring
        _ = 0 := by rw [hee, sub_self, mul_zero]
    rw [mul_sub] at this
    exact sub_eq_zero.mp this
  have hf : IsIdempotentElem (w.e * y) := by
    show w.e * y * (w.e * y) = w.e * y
    calc w.e * y * (w.e * y) = (w.e * w.e) * (y * y) := by ring
      _ = w.e * y := by rw [hee, hey]
  have hfe : w.e * y * w.e = w.e * y := by
    calc w.e * y * w.e = (w.e * w.e) * y := by ring
      _ = w.e * y := by rw [hee]
  have hmk : (Ideal.Quotient.mk (Ideal.span {1 - w.e}) y) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * y) := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨y, by ring⟩
  rw [hmk]
  rcases w.primitive _ hf hfe with h | h
  · left
    rw [h, map_zero]
  · right
    rw [h, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - w.e})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-1, by ring⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hDne : differentIdeal ℤ R ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hPtop : P.map w.toOw ≠ ⊤` using `hm.ne_top`. Establish `hpR : (p : R) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hIne : Ideal.span {(p : R)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hpR`. Establish `hIP : Ideal.span {(p : R)} ≤ P`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hpP`.

Take `⟨J, hPJ, hIJ⟩` from `Ideal.eq_prime_pow_mul_coprime hIne P`. Use `set c := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)})) with hc`. Establish `hJne : J ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hIJ` using `[Ideal.mul_bot]`.

Conclude with `hIne hIJ`. Establish `hpOw : Ideal.span {(p : w.Ow)} = P.map w.toOw ^ c`. Establish `hsp : Ideal.span {(p : w.Ow)} = (Ideal.span {(p : R)}).map w.toOw`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Rewrite using `[hsp, hIJ, Ideal.map_mul, Ideal.map_pow, map_eq_top_of_coprime w.toOw P hP hQ J hJne hPJ, Ideal.mul_top]`.

Establish `hcpos : 0 < c`. Break down `Nat.eq_zero_or_pos c with h0 | h0` into its components or cases. It suffices to derive a contradiction. Rewrite `hIJ` using `[h0, pow_zero, Ideal.one_eq_top, Ideal.top_mul]`. Rewrite `hIP` using `[hIJ]`.

Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[← hPJ]`. Conclude with `(sup_eq_left.mpr hIP).symm`. Conclude with `h0`. Take `⟨J', hPJ', hDJ'⟩` from `Ideal.eq_prime_pow_mul_coprime hDne P`.

Use `set k := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R)) with hk`. Establish `hJ'ne : J' ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hDJ'` using `[Ideal.mul_bot]`. Conclude with `hDne hDJ'`.

Establish `hDmap : (differentIdeal ℤ R).map w.toOw = P.map w.toOw ^ k`. Rewrite using `[hDJ', Ideal.map_mul, Ideal.map_pow, map_eq_top_of_coprime w.toOw P hP hQ J' hJ'ne hPJ', Ideal.mul_top]`. Use `⟨⟨k, c, hcpos, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hDmap, ← pow_mul, Nat.mul_comm k c, pow_mul, ← hpOw, Ideal.span_singleton_pow]`. Establish `hUnr : w.IsUnramified ↔ c = 1` using `by show (Ideal.span {(p : w.Ow)}).IsMaximal ↔ c = 1`.

Rewrite using `[hpOw]`. Prove the components needed by the constructor for the conclusion. Introduce `hmax`. Assume the negation of the conclusion as `hc1`. Establish `hc2 : 2 ≤ c` using `by omega`.

Establish `heq : P.map w.toOw ^ c = P.map w.toOw` using `hmax.eq_of_le hPtop (Ideal.pow_le_self hcpos.ne')`. Establish `hidem : IsIdempotentElem (P.map w.toOw)` using `by show P.map w.toOw * P.map w.toOw = P.map w.toOw`. Apply `le_antisymm Ideal.mul_le_right` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hfg : (P.map w.toOw).FG` using `Ideal.FG.map (IsNoetherian.noetherian P) w.toOw`.

Take `⟨g, hg, hgspan⟩` from `(Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem`. Establish `hpmem : (p : w.Ow) ∈ P.map w.toOw`. Rewrite using `[← map_natCast w.toOw p]`. Conclude with `Ideal.mem_map_of_mem _ hpP`. Break down `isIdempotentElem_Ow_eq_zero_or_one w g hg with rfl | rfl` into its components or cases.

Rewrite `hpmem` using `[hgspan]`. Establish `hp0 : (p : w.Ow) = 0` using `by simpa using hpmem`. Establish `h10 : (1 : w.Ow) = 0` using `ow_p_torsionFree p R w 1 (by rw [mul_one]; exact hp0)`. Apply `hPtop` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, h10]`.

Conclude with `zero_mem _`. Apply `hPtop` to reduce the goal to its premises. Rewrite using `[hgspan]`. Conclude with `Ideal.span_singleton_one`. Introduce `h1`.

Rewrite using `[h1, pow_one]`. Conclude with `hm`. Establish `hDtop : (differentIdeal ℤ R).map w.toOw = ⊤ ↔ ¬ P ∣ differentIdeal ℤ R`. Prove the components needed by the constructor for the conclusion. Introduce `h hdvd`.

Apply `hPtop` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← h]`. Conclude with `Ideal.map_mono (Ideal.le_of_dvd hdvd)`. Introduce `h`. Apply `map_eq_top_of_coprime w.toOw P hP hQ _ hDne` to reduce the goal to its premises.

Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le, hP.eq_of_le hne le_sup_left]`. Conclude with `le_sup_right`. Establish `hunder : P.under ℤ = Ideal.span {(p : ℤ)}`.

Establish `hpZ : (Ideal.span {(p : ℤ)}).IsMaximal`. Establish `hpr : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)`. Conclude with `hpr.isMaximal (by`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero)` after adjusting the coercions.

Use `symm`. Apply `hpZ.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ R (p : ℤ) ∈ P`. Rewrite using `[map_natCast]`.

Conclude with `hpP`. Establish `: P.IsPrime` using `hP.isPrime`. Establish `: P.LiesOver (Ideal.span {(p : ℤ)})` using `⟨hunder.symm⟩`. Establish `hspZ : Ideal.span {(p : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hmapZ : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(p : R)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hram : (Ideal.span {(p : ℤ)}).ramificationIdx' P = c`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises.

Rewrite using `[hmapZ, hIJ]`. Conclude with `le_trans (Ideal.mul_mono_right le_top) (le_of_eq (Ideal.mul_top _))`. Rewrite using `[hmapZ]`. Introduce `hle`. Establish `hdvd : P ^ c * P ∣ P ^ c * J`.

Rewrite using `[← pow_succ, ← hIJ, Ideal.dvd_iff_le]`. Conclude with `hle`. Establish `hPc : P ^ c ≠ 0` using `pow_ne_zero _ (by`. Introduce `h0`. Conclude with `hP.ne_top (by`.

Rewrite `h0` using `[Ideal.zero_eq_bot]`. Rewrite `hIP` using `[h0]`. Conclude with `absurd (le_bot_iff.mp hIP) hIne))`. Establish `hPJdvd : P ∣ J` using `(mul_dvd_mul_iff_left hPc).mp hdvd`. Apply `hP.ne_top` to reduce the goal to its premises.

Rewrite using `[← hPJ]`. Conclude with `(sup_eq_left.mpr (Ideal.le_of_dvd hPJdvd)).symm`. Rewrite using `[hDtop, hUnr, not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain, ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hspZ, hram]`.
-/
theorem different_pow_and_unramified_iff (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R)
    (P : Ideal R) (hP : P.IsMaximal) (hpP : (p : R) ∈ P) (hm : (P.map w.toOw).IsMaximal)
    (hQ : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) :
    (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧
      (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by
  have hp := (Fact.out : p.Prime)
  have hDne : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have hPtop : P.map w.toOw ≠ ⊤ := hm.ne_top
  have hpR : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hIne : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpR
  have hIP : Ideal.span {(p : R)} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpP
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hIne P
  set c := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)}))
    with hc
  have hJne : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hIJ
    exact hIne hIJ
  have hpOw : Ideal.span {(p : w.Ow)} = P.map w.toOw ^ c := by
    have hsp : Ideal.span {(p : w.Ow)} = (Ideal.span {(p : R)}).map w.toOw := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [hsp, hIJ, Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J hJne hPJ, Ideal.mul_top]
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      rw [h0, pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hIJ
      rw [hIJ] at hIP
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr hIP).symm
    · exact h0
  obtain ⟨J', hPJ', hDJ'⟩ := Ideal.eq_prime_pow_mul_coprime hDne P
  set k := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R))
    with hk
  have hJ'ne : J' ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hDJ'
    exact hDne hDJ'
  have hDmap : (differentIdeal ℤ R).map w.toOw = P.map w.toOw ^ k := by
    rw [hDJ', Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J' hJ'ne hPJ', Ideal.mul_top]
  refine ⟨⟨k, c, hcpos, ?_⟩, ?_⟩
  · rw [hDmap, ← pow_mul, Nat.mul_comm k c, pow_mul, ← hpOw, Ideal.span_singleton_pow]
  have hUnr : w.IsUnramified ↔ c = 1 := by
    show (Ideal.span {(p : w.Ow)}).IsMaximal ↔ c = 1
    rw [hpOw]
    constructor
    · intro hmax
      by_contra hc1
      have hc2 : 2 ≤ c := by omega
      have heq : P.map w.toOw ^ c = P.map w.toOw :=
        hmax.eq_of_le hPtop (Ideal.pow_le_self hcpos.ne')
      have hidem : IsIdempotentElem (P.map w.toOw) := by
        show P.map w.toOw * P.map w.toOw = P.map w.toOw
        apply le_antisymm Ideal.mul_le_right
        calc P.map w.toOw = P.map w.toOw ^ c := heq.symm
          _ ≤ P.map w.toOw ^ 2 := Ideal.pow_le_pow_right hc2
          _ = P.map w.toOw * P.map w.toOw := sq _
      have hfg : (P.map w.toOw).FG := Ideal.FG.map (IsNoetherian.noetherian P) w.toOw
      obtain ⟨g, hg, hgspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
      have hpmem : (p : w.Ow) ∈ P.map w.toOw := by
        rw [← map_natCast w.toOw p]
        exact Ideal.mem_map_of_mem _ hpP
      rcases isIdempotentElem_Ow_eq_zero_or_one w g hg with rfl | rfl
      · rw [hgspan] at hpmem
        have hp0 : (p : w.Ow) = 0 := by simpa using hpmem
        have h10 : (1 : w.Ow) = 0 := ow_p_torsionFree p R w 1 (by rw [mul_one]; exact hp0)
        apply hPtop
        rw [Ideal.eq_top_iff_one, h10]
        exact zero_mem _
      · apply hPtop
        rw [hgspan]
        exact Ideal.span_singleton_one
    · intro h1
      rw [h1, pow_one]
      exact hm
  have hDtop : (differentIdeal ℤ R).map w.toOw = ⊤ ↔ ¬ P ∣ differentIdeal ℤ R := by
    constructor
    · intro h hdvd
      apply hPtop
      rw [eq_top_iff, ← h]
      exact Ideal.map_mono (Ideal.le_of_dvd hdvd)
    · intro h
      apply map_eq_top_of_coprime w.toOw P hP hQ _ hDne
      by_contra hne
      apply h
      rw [Ideal.dvd_iff_le, hP.eq_of_le hne le_sup_left]
      exact le_sup_right
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpZ : (Ideal.span {(p : ℤ)}).IsMaximal := by
      have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      exact hpr.isMaximal (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero)
    symm
    apply hpZ.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ R (p : ℤ) ∈ P
    rw [map_natCast]
    exact hpP
  have : P.IsPrime := hP.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hunder.symm⟩
  have hspZ : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmapZ : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hram : (Ideal.span {(p : ℤ)}).ramificationIdx' P = c := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmapZ, hIJ]
      exact le_trans (Ideal.mul_mono_right le_top) (le_of_eq (Ideal.mul_top _))
    · rw [hmapZ]
      intro hle
      have hdvd : P ^ c * P ∣ P ^ c * J := by
        rw [← pow_succ, ← hIJ, Ideal.dvd_iff_le]
        exact hle
      have hPc : P ^ c ≠ 0 := pow_ne_zero _ (by
        intro h0
        exact hP.ne_top (by
          rw [Ideal.zero_eq_bot] at h0
          rw [h0] at hIP
          exact absurd (le_bot_iff.mp hIP) hIne))
      have hPJdvd : P ∣ J := (mul_dvd_mul_iff_left hPc).mp hdvd
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr (Ideal.le_of_dvd hPJdvd)).symm
  rw [hDtop, hUnr, not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hspZ, hram]

end GlobalTheory.Proof.different_power_unramified_iff
