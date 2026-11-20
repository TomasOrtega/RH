import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

section Factor

variable {R : Type} [CommRing R] {e : R}

local notation "Q" e:max => Ideal.Quotient.mk (Ideal.span {1 - e})

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Take the linear combination `e * hc - c * he.eq`. Introduce `h`.

Conclude with `⟨a - b, by linear_combination h⟩`.
-/
private theorem mk_eq_iff (he : IsIdempotentElem e) (a b : R) :
    (Q e) a = (Q e) b ↔ e * a = e * b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    linear_combination e * hc - c * he.eq
  · intro h
    exact ⟨a - b, by linear_combination h⟩

/- English proof (translation)
Rewrite using `[← map_one (Q e), mk_eq_iff he, mul_one, he.eq]`.
-/
private theorem mk_self (he : IsIdempotentElem e) : (Q e) e = 1 := by
  rw [← map_one (Q e), mk_eq_iff he, mul_one, he.eq]

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Rewrite `hc` using `[← map_mul, mk_eq_iff he]`. Conclude with `⟨e * c, by linear_combination hc⟩`.
-/
private theorem dvd_of_mk_dvd (he : IsIdempotentElem e) {a b : R} (h : (Q e) a ∣ (Q e) b) : a ∣ e * b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, mk_eq_iff he] at hc
  exact ⟨e * c, by linear_combination hc⟩

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
private theorem mem_pow_iff {S : Type} [CommRing S] (a x : S) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule S S) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Establish `hep : e ^ p = e`. Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hp.ne'`. Conclude with `he.pow_succ_eq k`. Establish `hb` using `PerfectRing.bijective_frobenius (R := R) (p := p)`. Use `⟨⟨fun x y h => ?_, fun x => ?_⟩⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `h' : (Q e) (a ^ p) = (Q e) (b ^ p)` using `by simpa only [map_pow] using h`. Rewrite `h'`, the goal using `[mk_eq_iff he]`. Apply `hb.1` to reduce the goal to its premises.

Use `show (e * a) ^ p = (e * b) ^ p`. Rewrite using `[mul_pow, mul_pow, hep, h']`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, hb'⟩` from `hb.2 a`. Conclude with `⟨(Q e) b, by rw [← hb']; simp only [map_pow]⟩`.
-/
private theorem perfect_quot (he : IsIdempotentElem e) {p : ℕ} (hp : 0 < p) [PerfectRing R p] :
    PerfectRing (R ⧸ Ideal.span {1 - e}) p := by
  have hep : e ^ p = e := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    exact he.pow_succ_eq k
  have hb := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h' : (Q e) (a ^ p) = (Q e) (b ^ p) := by simpa only [map_pow] using h
    rw [mk_eq_iff he] at h' ⊢
    apply hb.1
    show (e * a) ^ p = (e * b) ^ p
    rw [mul_pow, mul_pow, hep, h']
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb'⟩ := hb.2 a
    exact ⟨(Q e) b, by rw [← hb']; simp only [map_pow]⟩

/- English proof (translation)
Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[← map_mul, ← map_zero (Q e), mk_eq_iff he, mul_zero]`. Rewrite using `[← map_zero (Q e), mk_eq_iff he, mul_zero]`.

Rewrite `h` using `[mem_nonZeroDivisors_iff_right]`. Conclude with `h _ (by linear_combination hx)`.
-/
private theorem nzd_quot (he : IsIdempotentElem e) {π : R} (h : π ∈ nonZeroDivisors R) :
    (Q e) π ∈ nonZeroDivisors (R ⧸ Ideal.span {1 - e}) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, ← map_zero (Q e), mk_eq_iff he, mul_zero] at hx
  rw [← map_zero (Q e), mk_eq_iff he, mul_zero]
  rw [mem_nonZeroDivisors_iff_right] at h
  exact h _ (by linear_combination hx)

/- English proof (translation)
Establish `hH` using `h.toIsHausdorff`. Establish `hP` using `h.toIsPrecomplete`. Use `{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[← map_zero (Q e), mk_eq_iff he, mul_zero]`.

Use `hH.haus' _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, mem_pow_iff]`. Use `(hx n)` as an intermediate fact. Rewrite `this` using `[SModEq.zero, mem_pow_iff, ← map_pow]`. Conclude with `dvd_of_mk_dvd he this`.

Use `choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)`. Take `⟨L, hL⟩` from `hP.prec' (fun n => e * g n) (fun {m n} hmn => by`. Use `hf hmn` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, mem_pow_iff, ← map_pow, ← hg m, ← hg n, ← map_sub]`. Rewrite using `[SModEq.sub_mem, mem_pow_iff]`.

Establish `h2` using `dvd_of_mk_dvd he this`. Rewrite using `[mul_sub] at h2)` and apply the resulting hypothesis. Use `⟨(Q e) L, fun n => ?_⟩` and prove the remaining obligations. Use `hL n` as an intermediate fact. Rewrite `this`, the goal using `[SModEq.sub_mem, mem_pow_iff]`.

Establish `h3` using `map_dvd (Q e) this`. Rewrite `h3` using `[map_pow, map_sub, map_mul, mk_self he, one_mul, hg n]`. Conclude with `h3`.
-/
private theorem complete_quot (he : IsIdempotentElem e) {π : R} (h : IsAdicComplete (Ideal.span {π}) R) :
    IsAdicComplete (Ideal.span {(Q e) π}) (R ⧸ Ideal.span {1 - e}) := by
  have hH := h.toIsHausdorff
  have hP := h.toIsPrecomplete
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_zero (Q e), mk_eq_iff he, mul_zero]
    refine hH.haus' _ fun n => ?_
    rw [SModEq.zero, mem_pow_iff]
    have := (hx n)
    rw [SModEq.zero, mem_pow_iff, ← map_pow] at this
    exact dvd_of_mk_dvd he this
  · choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    obtain ⟨L, hL⟩ := hP.prec' (fun n => e * g n) (fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_pow_iff, ← map_pow, ← hg m, ← hg n, ← map_sub] at this
      rw [SModEq.sub_mem, mem_pow_iff]
      have h2 := dvd_of_mk_dvd he this
      rwa [mul_sub] at h2)
    refine ⟨(Q e) L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, mem_pow_iff] at this ⊢
    have h3 := map_dvd (Q e) this
    rw [map_pow, map_sub, map_mul, mk_self he, one_mul, hg n] at h3
    exact h3

/- English proof (translation)
Introduce `P hP hd`. Establish `hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I)` using `(Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P)`. Take `⟨q, rfl, hdeg, hq⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hP`. Take `⟨x, hx⟩` from `h q hq (hdeg ▸ hd)`. Conclude with `⟨_, hx.map⟩`.
-/
private theorem aic_quot (I : Ideal R) (h : ∀ P : R[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x) :
    ∀ P : (R ⧸ I)[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := by
  intro P hP hd
  have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P)
  obtain ⟨q, rfl, hdeg, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  obtain ⟨x, hx⟩ := h q hq (hdeg ▸ hd)
  exact ⟨_, hx.map⟩

/- English proof (translation)
Introduce `f g ⟨N, hN⟩`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective f`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective g`. Take `⟨c', d', hcd⟩` from `Ideal.mem_span_pair.1 hN`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c'`.

Take `⟨d, rfl⟩` from `Ideal.Quotient.mk_surjective d'`. Establish `hE : e * (c * a + d * b) = e * π ^ N`. Rewrite using `[← mk_eq_iff he]`. Simplify `hcd` using `only [map_add, map_mul, map_pow]`. Take `⟨u, hu, h1, h2⟩` from `h (a * e + (1 - e)) (b * e) ⟨N, Ideal.mem_span_pair.2 ⟨c * e + π ^ N * (1 - e), d, by`.

Take the linear combination `hE + (c * a - c - π ^ N * a + π ^ N) * he.eq⟩⟩`. Establish `hm : (Q e) (1 - e) = 0` using `by rw [map_sub, map_one, mk_self he, sub_self]`. Establish `ha : (Q e) (a * e + (1 - e)) = (Q e) a`. Rewrite using `[map_add, map_mul, mk_self he, hm, mul_one, add_zero]`. Establish `hb : (Q e) (b * e) = (Q e) b` using `by rw [map_mul, mk_self he, mul_one]`.

Rewrite `h1`, `h2` using `[Ideal.mem_span_singleton]`. Use `⟨(Q e) u, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (Q e) u * (Q e) u = (Q e) u`. Rewrite using `[← map_mul, hu.eq]`. Rewrite using `[Ideal.mem_span_singleton]`.

Use `map_dvd (Q e) h1` as an intermediate fact. Rewrite `this` using `[hb, map_mul, ha]`. Then use the resulting hypothesis. Rewrite using `[Ideal.mem_span_singleton]`. Use `map_dvd (Q e) h2` as an intermediate fact. Rewrite `this` using `[ha, map_mul, hb, map_sub, map_one]`. Then use the resulting hypothesis.
-/
private theorem val_quot (he : IsIdempotentElem e) {π : R}
    (h : ∀ f g : R, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f}) :
    ∀ f g : R ⧸ Ideal.span {1 - e}, (∃ N : ℕ, (Q e) π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R ⧸ Ideal.span {1 - e}, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f} := by
  intro f g ⟨N, hN⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨c', d', hcd⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  have hE : e * (c * a + d * b) = e * π ^ N := by
    rw [← mk_eq_iff he]
    simpa only [map_add, map_mul, map_pow] using hcd
  obtain ⟨u, hu, h1, h2⟩ := h (a * e + (1 - e)) (b * e) ⟨N, Ideal.mem_span_pair.2
    ⟨c * e + π ^ N * (1 - e), d, by
      linear_combination hE + (c * a - c - π ^ N * a + π ^ N) * he.eq⟩⟩
  have hm : (Q e) (1 - e) = 0 := by rw [map_sub, map_one, mk_self he, sub_self]
  have ha : (Q e) (a * e + (1 - e)) = (Q e) a := by
    rw [map_add, map_mul, mk_self he, hm, mul_one, add_zero]
  have hb : (Q e) (b * e) = (Q e) b := by rw [map_mul, mk_self he, mul_one]
  rw [Ideal.mem_span_singleton] at h1 h2
  refine ⟨(Q e) u, ?_, ?_, ?_⟩
  · show (Q e) u * (Q e) u = (Q e) u
    rw [← map_mul, hu.eq]
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (Q e) h1
    rwa [hb, map_mul, ha] at this
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (Q e) h2
    rwa [ha, map_mul, hb, map_sub, map_one] at this

end Factor

variable {l : ℕ} [Fact l.Prime]

private def factor (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : PAlg l where
  A := A.A ⧸ Ideal.span {1 - e}
  s := (Ideal.Quotient.mk _).comp A.s
  perf := perfect_quot he (Fact.out : l.Prime).pos
  compl := complete_quot he A.compl
  tf := nzd_quot he A.tf

/- English proof (translation)
Assemble the required witnesses or components as `⟨aic_quot _ h.1, val_quot he h.2⟩`.
-/
private theorem factor_isTest (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) (h : A.IsTest) :
    (factor A he).IsTest :=
  ⟨aic_quot _ h.1, val_quot he h.2⟩

/- English proof (translation)
Introduce `l _ A ι _ e he`. Use `⟨fun i => ⟨factor A.obj (he.idem i), factor_isTest _ _ A.property⟩, fun i => ObjectProperty.homMk ⟨Ideal.Quotient.mk _, rfl⟩, ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `he.bijective_pi`. Conclude with `mk_self (he.idem i)`.
-/
theorem decEx : DecEx := by
  intro l _ A ι _ e he
  refine ⟨fun i => ⟨factor A.obj (he.idem i), factor_isTest _ _ A.property⟩,
    fun i => ObjectProperty.homMk ⟨Ideal.Quotient.mk _, rfl⟩, ?_, fun i => ?_⟩
  · exact he.bijective_pi
  · exact mk_self (he.idem i)

end UpperTheory.Ru.crystallineComparison
