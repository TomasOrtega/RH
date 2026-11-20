import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open GlobalTheory.PELU GlobalTheory.UPel.HT

namespace UpperTheory.Gal.W2

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Take `⟨q, hq, hqa⟩` from `Nat.exists_prime_and_dvd ha`. Establish `hqb : ¬ q ∣ b` using `fun hqb => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab hqa hqb)`. Establish `hex : ∃ k, ¬ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t`. Use `⟨(Y t₀).natAbs, fun hall => h0 ?_⟩` and prove the remaining obligations.

Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hall t₀) ?_` and prove the remaining obligations. Rewrite using `[Int.natAbs_natCast]`. Conclude with `Nat.lt_pow_self hq.one_lt`. Establish `hk0 : Nat.find hex ≠ 0`. Introduce `h`.

Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this (fun t => by simp)`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero hk0`. Establish `hmY : ∀ t, ((q ^ m : ℕ) : ℤ) ∣ Y t`.

Assume the negation of the conclusion as `hc`. Conclude with `Nat.find_min hex (by omega) hc`. Establish `hcop : IsCoprime ((q ^ (m + 1) : ℕ) : ℤ) (b : ℤ)` using `Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))`. Establish `hX : ∀ t, ((q ^ (m + 1) : ℕ) : ℤ) ∣ X t`. Introduce `t`.

Use `hcop.dvd_of_dvd_mul_left ?_` and prove the remaining obligations. Rewrite using `[h t, pow_succ, Nat.cast_mul, mul_comm (a : ℤ)]`. Conclude with `mul_dvd_mul (hmY t) (Int.natCast_dvd_natCast.mpr hqa)`. Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[hm]`.

Conclude with `this ((hP q (m + 1) hq).mp hX)`.
-/
private lemma power_free {T : Type} (X Y : T → ℤ) (a b : ℕ) (hab : a.Coprime b)
    (h : ∀ t, (b : ℤ) * X t = a * Y t)
    (hP : ∀ q k : ℕ, q.Prime → ((∀ t, ((q ^ k : ℕ) : ℤ) ∣ X t) ↔ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t))
    (t₀ : T) (h0 : Y t₀ ≠ 0) : a = 1 := by
  classical
  by_contra ha
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha
  have hqb : ¬ q ∣ b := fun hqb => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab hqa hqb)
  have hex : ∃ k, ¬ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t := by
    refine ⟨(Y t₀).natAbs, fun hall => h0 ?_⟩
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hall t₀) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hq.one_lt
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this (fun t => by simp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmY : ∀ t, ((q ^ m : ℕ) : ℤ) ∣ Y t := by
    by_contra hc
    exact Nat.find_min hex (by omega) hc
  have hcop : IsCoprime ((q ^ (m + 1) : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))
  have hX : ∀ t, ((q ^ (m + 1) : ℕ) : ℤ) ∣ X t := by
    intro t
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [h t, pow_succ, Nat.cast_mul, mul_comm (a : ℤ)]
    exact mul_dvd_mul (hmY t) (Int.natCast_dvd_natCast.mpr hqa)
  have := Nat.find_spec hex
  rw [hm] at this
  exact this ((hP q (m + 1) hq).mp hX)

/- English proof (translation)
Take `⟨f, ν, -, -, H⟩` from `h`. Take `⟨hν, -, -, honto, hsim⟩` from `H n hn hc`. Prove the components needed by the constructor for the conclusion. Introduce `hd a a'`. Establish `h1 : (n : ℤ) ∣ ν n * D₀.EF a a'` using `(dvd_sub_right (hd _ _)).1 (hsim a a')`.

Conclude with `hν.symm.dvd_of_dvd_mul_left h1`. Introduce `hd x y`. Take `⟨a, e, rfl⟩` from `honto x`. Take `⟨a', e', rfl⟩` from `honto y`. Establish `h1 : (n : ℤ) ∣ D'.EF (f n a) (f n a')`.

Establish `h2` using `hsim a a'`. Establish `h3 : (n : ℤ) ∣ ν n * D₀.EF a a'` using `Dvd.dvd.mul_left (hd a a') _`. Conclude with `(dvd_sub_left h3).1 h2`. Simplify using `only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Conclude with `dvd_add (dvd_add h1 (Dvd.intro _ rfl)) (Dvd.intro _ rfl)`.
-/
private lemma genus_dvd {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (h : Genus p N D₀ D' t) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (∀ x y, (n : ℤ) ∣ D'.EF x y) ↔ ∀ a a', (n : ℤ) ∣ D₀.EF a a' := by
  obtain ⟨f, ν, -, -, H⟩ := h
  obtain ⟨hν, -, -, honto, hsim⟩ := H n hn hc
  constructor
  · intro hd a a'
    have h1 : (n : ℤ) ∣ ν n * D₀.EF a a' := (dvd_sub_right (hd _ _)).1 (hsim a a')
    exact hν.symm.dvd_of_dvd_mul_left h1
  · intro hd x y
    obtain ⟨a, e, rfl⟩ := honto x
    obtain ⟨a', e', rfl⟩ := honto y
    have h1 : (n : ℤ) ∣ D'.EF (f n a) (f n a') := by
      have h2 := hsim a a'
      have h3 : (n : ℤ) ∣ ν n * D₀.EF a a' := Dvd.dvd.mul_left (hd a a') _
      exact (dvd_sub_left h3).1 h2
    simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add (dvd_add h1 (Dvd.intro _ rfl)) (Dvd.intro _ rfl)

/- English proof (translation)
Take `⟨E₁, hE, e, he, hx⟩` from `h`. Set `b` to `Module.Free.chooseBasis ℤ D'.La`. Take `⟨i⟩` from `b.index_nonempty`. Take `⟨x, hx⟩` from `hx (b.coord i)`. Use `⟨E₁, e, x, b i, hE, he, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
private lemma half_value {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] :
    ∃ (E₁ : LinearMap.BilinForm ℤ D'.La) (e : ℕ) (x y : D'.La), D'.EF = (2 : ℤ) • E₁ ∧ e.Coprime p ∧ E₁ x y = e := by
  obtain ⟨E₁, hE, e, he, hx⟩ := h
  let b := Module.Free.chooseBasis ℤ D'.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨x, hx⟩ := hx (b.coord i)
  refine ⟨E₁, e, x, b i, hE, he, ?_⟩
  rw [hx]
  simp

/- English proof (translation)
Take `⟨E₁, e, x, y, hE, he, hxy⟩` from `half_value h`. Prove the components needed by the constructor for the conclusion. Introduce `hall`. Establish `h1` using `hall x y`. Rewrite `h1` using `[hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]`.

Establish `hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (e : ℤ)` using `Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ he.symm)`. Conclude with `hcop.dvd_of_dvd_mul_right h1`. Introduce `h2 x' y'`. Rewrite using `[hE, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `dvd_mul_of_dvd_left h2 _`.
-/
private lemma half_dvd {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] (k : ℕ) :
    (∀ x y, ((p ^ k : ℕ) : ℤ) ∣ D'.EF x y) ↔ ((p ^ k : ℕ) : ℤ) ∣ 2 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  constructor
  · intro hall
    have h1 := hall x y
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul] at h1
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (e : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ he.symm)
    exact hcop.dvd_of_dvd_mul_right h1
  · intro h2 x' y'
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left h2 _

/- English proof (translation)
Take `⟨E₁, e, x, y, hE, he, hxy⟩` from `half_value h`. Use `⟨x, y, ?_⟩` and prove the remaining obligations. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp he)`.

Rewrite using `[hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]`. Conclude with `mul_ne_zero two_ne_zero (by exact_mod_cast he0)`.
-/
private lemma half_ne {O : Type} [Ring O] {bar : O → O} {p : ℕ} (hp : p.Prime) {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] : ∃ x y, D'.EF x y ≠ 0 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  refine ⟨x, y, ?_⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp he)
  rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]
  exact mul_ne_zero two_ne_zero (by exact_mod_cast he0)

/- English proof (translation)
Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Take `⟨f, ν, -, -, hf⟩` from `h`. Establish `hn : 0 < 1 + p` using `by omega`. Establish `hc : (1 + p).Coprime p` using `Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)`.

Take `⟨-, -, hdiv, -, -⟩` from `hf (1 + p) hn hc`. Set `b` to `Module.Free.chooseBasis ℤ D₀.La`. Take `⟨i⟩` from `b.index_nonempty`. Take `⟨e, he⟩` from `(hdiv (b i)).mp ⟨0, Subsingleton.elim _ _⟩`. Establish `h1` using `congrArg (b.coord i) he`.

Simplify using `only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h1`. Establish `h2` using `Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private lemma genus_nontrivial {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (hp : p.Prime) (h : Genus p N D₀ D' t) [Nontrivial D₀.La] : Nontrivial D'.La := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨f, ν, -, -, hf⟩ := h
  have hn : 0 < 1 + p := by omega
  have hc : (1 + p).Coprime p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
  obtain ⟨-, -, hdiv, -, -⟩ := hf (1 + p) hn hc
  let b := Module.Free.chooseBasis ℤ D₀.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨e, he⟩ := (hdiv (b i)).mp ⟨0, Subsingleton.elim _ _⟩
  have h1 := congrArg (b.coord i) he
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul,
    Finsupp.smul_apply, nsmul_eq_mul] at h1
  have h2 := Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm
  have := hp.two_le
  omega

/- English proof (translation)
Introduce `p _ D N N' D' t D'' t'' hD' hD'' w r hr hEF`. Establish `hp : p.Prime` using `Fact.out`. Use `haveI : Nontrivial D.plat.La := by show Nontrivial D.La`. Use `Module.nontrivial_of_finrank_pos (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[D.rankLa]`.

Establish `h1` using `D.m_pos`. Establish `h2` using `D.n_pos`. Establish `h3 : 0 < Module.finrank ℚ D.F` using `Module.finrank_pos`. Check the signs of the components of the expression. Use `haveI : Nontrivial D'.La := genus_nontrivial hp hD'.1`.

Use `haveI : Nontrivial D''.La := genus_nontrivial hp hD''.1`. Set `X : D''.La × D''.La → ℤ` to `fun u => D'.EF (w u.1) (w u.2)`. Set `Y : D''.La × D''.La → ℤ` to `fun u => D''.EF u.1 u.2`. Establish `hXall : ∀ m : ℤ, (∀ u, m ∣ X u) ↔ ∀ x y, m ∣ D'.EF x y` using `fun m => ⟨fun h x y => by simpa [X] using h (w.symm x, w.symm y), fun h u => h _ _⟩`. Establish `hYall : ∀ m : ℤ, (∀ u, m ∣ Y u) ↔ ∀ x y, m ∣ D''.EF x y` using `fun m => ⟨fun h x y => h (x, y), fun h u => h _ _⟩`.

Establish `hP : ∀ q k : ℕ, q.Prime → ((∀ u, ((q ^ k : ℕ) : ℤ) ∣ X u) ↔ ∀ u, ((q ^ k : ℕ) : ℤ) ∣ Y u)`. Introduce `q k hq`. Rewrite using `[hXall, hYall]`. Distinguish the cases in `hqp : q = p`. Substitute `hqp` using the available equality.

Rewrite using `[half_dvd hD'.2, half_dvd hD''.2]`. Establish `hpos : 0 < q ^ k` using `pow_pos hq.pos k`. Establish `hcop : (q ^ k).Coprime p` using `Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)`. Rewrite using `[genus_dvd hD'.1 _ hpos hcop, genus_dvd hD''.1 _ hpos hcop]`. Establish `hnum : 0 < r.num` using `Rat.num_pos.mpr hr`.

Establish `hkey : ∀ u, (r.den : ℤ) * X u = (r.num.natAbs : ℤ) * Y u`. Introduce `u`. Rewrite using `[Int.natAbs_of_nonneg hnum.le]`. Establish `h1` using `hEF u.1 u.2`. Establish `h2 : ((r.den : ℤ) * X u : ℚ) = (r.num * Y u : ℚ)`.

Use `push_cast`. Rewrite using `[show (X u : ℚ) = ((D'.EF (w u.1) (w u.2) : ℤ) : ℚ) from rfl, h1, ← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h2` after adjusting the coercions. Take `⟨x₀, y₀, h0⟩` from `half_ne hp hD''.2`.

Take `⟨x₁, y₁, h1⟩` from `half_ne hp hD'.2`. Establish `ha : r.num.natAbs = 1` using `power_free X Y r.num.natAbs r.den r.reduced hkey hP (x₀, y₀) h0`. Establish `hb : r.den = 1` using `power_free Y X r.den r.num.natAbs r.reduced.symm (fun u => (hkey u).symm) (fun q k hq => (hP q k hq).symm) (w.symm x₁, w.symm y₁) (by simpa [X] using h1)`. Establish `hn1 : r.num = 1` using `by omega`. Rewrite using `[← Rat.num_div_den r, hn1, hb]`.

Evaluate the numerical expressions.
-/
theorem clsScalar_of : ClsScalar := by
  intro p _ D N N' D' t D'' t'' hD' hD'' w r hr hEF
  have hp : p.Prime := Fact.out
  haveI : Nontrivial D.plat.La := by
    show Nontrivial D.La
    refine Module.nontrivial_of_finrank_pos (R := ℤ) ?_
    rw [D.rankLa]
    have h1 := D.m_pos
    have h2 := D.n_pos
    have h3 : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    positivity
  haveI : Nontrivial D'.La := genus_nontrivial hp hD'.1
  haveI : Nontrivial D''.La := genus_nontrivial hp hD''.1
  let X : D''.La × D''.La → ℤ := fun u => D'.EF (w u.1) (w u.2)
  let Y : D''.La × D''.La → ℤ := fun u => D''.EF u.1 u.2
  have hXall : ∀ m : ℤ, (∀ u, m ∣ X u) ↔ ∀ x y, m ∣ D'.EF x y := fun m =>
    ⟨fun h x y => by simpa [X] using h (w.symm x, w.symm y), fun h u => h _ _⟩
  have hYall : ∀ m : ℤ, (∀ u, m ∣ Y u) ↔ ∀ x y, m ∣ D''.EF x y := fun m =>
    ⟨fun h x y => h (x, y), fun h u => h _ _⟩
  have hP : ∀ q k : ℕ, q.Prime → ((∀ u, ((q ^ k : ℕ) : ℤ) ∣ X u) ↔ ∀ u, ((q ^ k : ℕ) : ℤ) ∣ Y u) := by
    intro q k hq
    rw [hXall, hYall]
    by_cases hqp : q = p
    · subst hqp
      rw [half_dvd hD'.2, half_dvd hD''.2]
    · have hpos : 0 < q ^ k := pow_pos hq.pos k
      have hcop : (q ^ k).Coprime p := Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)
      rw [genus_dvd hD'.1 _ hpos hcop, genus_dvd hD''.1 _ hpos hcop]
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hkey : ∀ u, (r.den : ℤ) * X u = (r.num.natAbs : ℤ) * Y u := by
    intro u
    rw [Int.natAbs_of_nonneg hnum.le]
    have h1 := hEF u.1 u.2
    have h2 : ((r.den : ℤ) * X u : ℚ) = (r.num * Y u : ℚ) := by
      push_cast
      rw [show (X u : ℚ) = ((D'.EF (w u.1) (w u.2) : ℤ) : ℚ) from rfl, h1, ← Rat.mul_den_eq_num]
      ring
    exact_mod_cast h2
  obtain ⟨x₀, y₀, h0⟩ := half_ne hp hD''.2
  obtain ⟨x₁, y₁, h1⟩ := half_ne hp hD'.2
  have ha : r.num.natAbs = 1 :=
    power_free X Y r.num.natAbs r.den r.reduced hkey hP (x₀, y₀) h0
  have hb : r.den = 1 :=
    power_free Y X r.den r.num.natAbs r.reduced.symm (fun u => (hkey u).symm)
      (fun q k hq => (hP q k hq).symm) (w.symm x₁, w.symm y₁) (by simpa [X] using h1)
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hb]
  norm_num

end UpperTheory.Gal.W2
