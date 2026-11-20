import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.IdemObj

section Ring

variable {R : Type} [CommRing R] {e : R}

abbrev Q (e : R) : Type := R ⧸ Ideal.span {1 - e}

/- English proof (translation)
Establish `h : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite `h` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem mk_e : Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

/- English proof (translation)
Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `: e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Rewrite using `[mul_left_comm, this, mul_zero]`.
-/
theorem mul_eq_zero_of_mem (he : IsIdempotentElem e) {x : R} (hx : x ∈ Ideal.span {1 - e}) : e * x = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rw [mul_left_comm, this, mul_zero]

/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton'.2 ⟨x, by rw [mul_comm, sub_mul, one_mul, hx, sub_zero]⟩`.
-/
theorem mem_of_mul_eq_zero {x : R} (hx : e * x = 0) : x ∈ Ideal.span {1 - e} :=
  Ideal.mem_span_singleton'.2 ⟨x, by rw [mul_comm, sub_mul, one_mul, hx, sub_zero]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => mul_eq_zero_of_mem he (Ideal.Quotient.eq_zero_iff_mem.1 h), fun h => Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_mul_eq_zero h)⟩`.
-/
theorem mk_eq_zero_iff (he : IsIdempotentElem e) (x : R) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) x = 0 ↔ e * x = 0 :=
  ⟨fun h => mul_eq_zero_of_mem he (Ideal.Quotient.eq_zero_iff_mem.1 h),
    fun h => Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_mul_eq_zero h)⟩

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, mk_eq_zero_iff he, mul_sub, sub_eq_zero]`.
-/
theorem mk_eq_iff (he : IsIdempotentElem e) (x y : R) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) x = Ideal.Quotient.mk (Ideal.span {1 - e}) y ↔ e * x = e * y := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff he, mul_sub, sub_eq_zero]

/- English proof (translation)
Establish `hb : Function.Bijective (fun x : R => x ^ l)` using `PerfectRing.bijective_frobenius`. Establish `hp : e ^ l = e`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hl`. Rewrite using `[hk]`. Conclude with `he.pow_succ_eq k`.

Use `⟨⟨fun x y hxy => ?_, fun y => ?_⟩⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `h : Ideal.Quotient.mk (Ideal.span {1 - e}) (x ^ l) = Ideal.Quotient.mk (Ideal.span {1 - e}) (y ^ l)`. Rewrite using `[map_pow, map_pow]`.

Conclude with `hxy`. Rewrite `h` using `[mk_eq_iff he]`. Use `(mk_eq_iff he x y).2 (hb.1 ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e * x) ^ l = (e * y) ^ l`. Rewrite using `[mul_pow, mul_pow, hp, h]`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨x, rfl⟩` from `hb.2 y`. Conclude with `⟨Ideal.Quotient.mk _ x, (map_pow (Ideal.Quotient.mk _) x l).symm⟩`.
-/
theorem perfect_quot (he : IsIdempotentElem e) (l : ℕ) (hl : l ≠ 0) [PerfectRing R l] : PerfectRing (Q e) l := by
  have hb : Function.Bijective (fun x : R => x ^ l) := PerfectRing.bijective_frobenius
  have hp : e ^ l = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [hk]; exact he.pow_succ_eq k
  refine ⟨⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h : Ideal.Quotient.mk (Ideal.span {1 - e}) (x ^ l) = Ideal.Quotient.mk (Ideal.span {1 - e}) (y ^ l) := by
      rw [map_pow, map_pow]; exact hxy
    rw [mk_eq_iff he] at h
    refine (mk_eq_iff he x y).2 (hb.1 ?_)
    change (e * x) ^ l = (e * y) ^ l
    rw [mul_pow, mul_pow, hp, h]
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := hb.2 y
    exact ⟨Ideal.Quotient.mk _ x, (map_pow (Ideal.Quotient.mk _) x l).symm⟩

/- English proof (translation)
Use `mem_nonZeroDivisors_iff_left.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[← map_mul, mk_eq_zero_iff he]`. Rewrite using `[mk_eq_zero_iff he]`. Establish `: π * (e * x) = 0` using `by rw [mul_left_comm]; exact hx`.

Conclude with `(mem_nonZeroDivisors_iff_left.1 h) _ this`.
-/
theorem tf_quot (he : IsIdempotentElem e) {π : R} (h : π ∈ nonZeroDivisors R) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) π ∈ nonZeroDivisors (Q e) := by
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, mk_eq_zero_iff he] at hx
  rw [mk_eq_zero_iff he]
  have : π * (e * x) = 0 := by rw [mul_left_comm]; exact hx
  exact (mem_nonZeroDivisors_iff_left.1 h) _ this

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem smod_iff {S : Type} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {a}) ^ n • (⊤ : Submodule S S)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Rewrite `hc` using `[← map_pow, ← map_mul, mk_eq_iff he]`. Conclude with `⟨e * c, by rw [hc]; ring⟩`.
-/
theorem dvd_of_mk_dvd (he : IsIdempotentElem e) {a x : R} (n : ℕ)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) a ^ n ∣ Ideal.Quotient.mk (Ideal.span {1 - e}) x) :
    a ^ n ∣ e * x := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_pow, ← map_mul, mk_eq_iff he] at hc
  exact ⟨e * c, by rw [hc]; ring⟩

/- English proof (translation)
Establish `hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) π}) (Q e)` using `⟨fun x hx => by`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `(mk_eq_zero_iff he x).2 (hc.toIsHausdorff.haus' _ fun n => ?_)` and prove the remaining obligations. Use `(smod_iff _ _ _ n).1 (hx n)` as an intermediate fact. Rewrite `this` using `[sub_zero]`.

Conclude with `(smod_iff _ _ _ n).2 (by rw [sub_zero]; exact dvd_of_mk_dvd he n this)⟩`. Establish `hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) π}) (Q e)` using `⟨fun f hf => by choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)`. Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec' (fun n => e * g n) fun {m n} hmn => (smod_iff _ _ _ m).2 (by`. Use `(smod_iff _ _ _ m).1 (hf hmn)` as an intermediate fact. Rewrite `this` using `[← hg m, ← hg n, ← map_sub]`.

Rewrite using `[← mul_sub]`. Conclude with `dvd_of_mk_dvd he m this)`. Use `⟨Ideal.Quotient.mk _ L, fun n => (smod_iff _ _ _ n).2 ?_⟩` and prove the remaining obligations. Establish `h1` using `map_dvd (Ideal.Quotient.mk (Ideal.span {1 - e})) ((smod_iff _ _ _ n).1 (hL n))`. Rewrite `h1` using `[map_pow, map_sub, map_mul, mk_e, one_mul, hg n]`.

Conclude with `h1⟩`. Conclude with `{ hH, hP with }`.
-/
theorem complete_quot (he : IsIdempotentElem e) {π : R} (hc : IsAdicComplete (Ideal.span {π}) R) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) π}) (Q e) := by
  have hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) π}) (Q e) := ⟨fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine (mk_eq_zero_iff he x).2 (hc.toIsHausdorff.haus' _ fun n => ?_)
    have := (smod_iff _ _ _ n).1 (hx n)
    rw [sub_zero] at this
    exact (smod_iff _ _ _ n).2 (by rw [sub_zero]; exact dvd_of_mk_dvd he n this)⟩
  have hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) π}) (Q e) := ⟨fun f hf => by
    choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' (fun n => e * g n) fun {m n} hmn => (smod_iff _ _ _ m).2 (by
      have := (smod_iff _ _ _ m).1 (hf hmn)
      rw [← hg m, ← hg n, ← map_sub] at this
      rw [← mul_sub]
      exact dvd_of_mk_dvd he m this)
    refine ⟨Ideal.Quotient.mk _ L, fun n => (smod_iff _ _ _ n).2 ?_⟩
    have h1 := map_dvd (Ideal.Quotient.mk (Ideal.span {1 - e})) ((smod_iff _ _ _ n).1 (hL n))
    rw [map_pow, map_sub, map_mul, mk_e, one_mul, hg n] at h1
    exact h1⟩
  exact { hH, hP with }

/- English proof (translation)
Establish `: Nontrivial (Q e)`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Rewrite `hd` using `[Subsingleton.elim P 0, Polynomial.natDegree_zero]`. Conclude with `lt_irrefl _ hd`.

Establish `hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk (Ideal.span {1 - e}))` using `(Polynomial.lifts_iff_coeff_lifts _).2 fun n => Ideal.Quotient.mk_surjective _`. Take `⟨q, rfl, hq, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hm`. Establish `hn : q.natDegree = (q.map (Ideal.Quotient.mk (Ideal.span {1 - e}))).natDegree` using `Polynomial.natDegree_eq_of_degree_eq hq`. Take `⟨x, hx⟩` from `h q hqm (hn ▸ hd)`. Establish `hx' : q.eval x = 0` using `hx`.

Conclude with `⟨Ideal.Quotient.mk _ x, by`. Rewrite using `[Polynomial.IsRoot.def, Polynomial.eval_map_apply, hx', map_zero]⟩`.
-/
theorem aic_quot (h : ∀ P : Polynomial R, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x)
    (P : Polynomial (Q e)) (hm : P.Monic) (hd : 0 < P.natDegree) : ∃ x, P.IsRoot x := by
  have : Nontrivial (Q e) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
    exact lt_irrefl _ hd
  have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk (Ideal.span {1 - e})) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun n => Ideal.Quotient.mk_surjective _
  obtain ⟨q, rfl, hq, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
  have hn : q.natDegree = (q.map (Ideal.Quotient.mk (Ideal.span {1 - e}))).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq hq
  obtain ⟨x, hx⟩ := h q hqm (hn ▸ hd)
  have hx' : q.eval x = 0 := hx
  exact ⟨Ideal.Quotient.mk _ x, by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_apply, hx', map_zero]⟩

/- English proof (translation)
Establish `h1 : WittVector.map (Ideal.Quotient.mk (Ideal.span {1 - e})) (WittVector.teichmuller l e * x) = 0`. Rewrite using `[map_mul, hx, mul_zero]`. Establish `h2 : WittVector.map (Ideal.Quotient.mk (Ideal.span {e})) (WittVector.teichmuller l e * x) = 0`. Establish `: Ideal.Quotient.mk (Ideal.span {e}) e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite using `[map_mul, WittVector.map_teichmuller, this, WittVector.teichmuller_zero, zero_mul]`.

Use extensionality with `i`. Establish `c1` using `congrArg (fun w => WittVector.coeff w i) h1`. Establish `c2` using `congrArg (fun w => WittVector.coeff w i) h2`. Simplify using `only [WittVector.map_coeff, WittVector.zero_coeff] at c1 c2`. Rewrite using `[WittVector.zero_coeff]`.

Establish `a1` using `(mk_eq_zero_iff he _).1 c1`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 c2)`. Rewrite `a1` using `[← hc, mul_left_comm, he.eq, mul_comm]`. Rewrite using `[← hc, mul_comm c e, a1]`.
-/
theorem teich_mul_eq_zero {l : ℕ} [Fact l.Prime] (he : IsIdempotentElem e) (x : WittVector l R)
    (hx : WittVector.map (Ideal.Quotient.mk (Ideal.span {1 - e})) x = 0) :
    WittVector.teichmuller l e * x = 0 := by
  have h1 : WittVector.map (Ideal.Quotient.mk (Ideal.span {1 - e})) (WittVector.teichmuller l e * x) = 0 := by
    rw [map_mul, hx, mul_zero]
  have h2 : WittVector.map (Ideal.Quotient.mk (Ideal.span {e})) (WittVector.teichmuller l e * x) = 0 := by
    have : Ideal.Quotient.mk (Ideal.span {e}) e = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [map_mul, WittVector.map_teichmuller, this, WittVector.teichmuller_zero, zero_mul]
  ext i
  have c1 := congrArg (fun w => WittVector.coeff w i) h1
  have c2 := congrArg (fun w => WittVector.coeff w i) h2
  simp only [WittVector.map_coeff, WittVector.zero_coeff] at c1 c2
  rw [WittVector.zero_coeff]
  have a1 := (mk_eq_zero_iff he _).1 c1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 c2)
  rw [← hc, mul_left_comm, he.eq, mul_comm] at a1
  rw [← hc, mul_comm c e, a1]

end Ring

end GlobalTheory.CompanionTheory.IdemObj

namespace GlobalTheory.CompanionTheory.IdemObj

section Obj

variable {l : ℕ} [Fact l.Prime]

def obj (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : PAlg l where
  A := Q e
  s := (Ideal.Quotient.mk (Ideal.span {1 - e})).comp A.s
  perf := perfect_quot he l (Fact.out : l.Prime).ne_zero
  compl := complete_quot he A.compl
  tf := tf_quot he A.tf

def proj (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : A ⟶ obj A he :=
  ⟨Ideal.Quotient.mk (Ideal.span {1 - e}), rfl⟩

/- English proof (translation)
Introduce `f g ⟨N, hN⟩`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective f`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective g`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 hN`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `hpi : (obj A he).pi = Ideal.Quotient.mk (Ideal.span {1 - e}) A.pi` using `rfl`. Rewrite `hab` using `[hpi]`. Establish `hab' : Ideal.Quotient.mk (Ideal.span {1 - e}) (a * f + b * g) = Ideal.Quotient.mk (Ideal.span {1 - e}) (A.pi ^ N)`. Rewrite using `[map_add, map_mul, map_mul, map_pow]`.

Conclude with `hab`. Rewrite `hab'` using `[mk_eq_iff he]`. Establish `hmem : A.pi ^ N ∈ Ideal.span {e * f + (1 - e), e * g}`. Use `Ideal.mem_span_pair.2 ⟨e * a + (1 - e) * A.pi ^ N, b, ?_⟩` and prove the remaining obligations. Establish `e2 : e * e = e` using `he.eq`.

Establish `: (e * a + (1 - e) * A.pi ^ N) * (e * f + (1 - e)) + b * (e * g) = e * (a * f + b * g) + (e * e - e) * (a * f) + (e - e * e) * (a + A.pi ^ N * f) + (1 - 2 * e + e * e) * A.pi ^ N` using `by ring`. Rewrite using `[this, hab', e2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, hu, h1, h2⟩` from `h _ _ ⟨N, hmem⟩`. Use `⟨Ideal.Quotient.mk _ u, hu.map (Ideal.Quotient.mk _), ?_, ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 h1`. Use `Ideal.mem_span_singleton.2 ⟨Ideal.Quotient.mk _ c, ?_⟩` and prove the remaining obligations. Use `congrArg (Ideal.Quotient.mk (Ideal.span {1 - e})) hc` as an intermediate fact. Simplify `this` using `only [map_mul, map_add, map_sub, map_one, mk_e, sub_self, add_zero, one_mul]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 h2`.

Use `Ideal.mem_span_singleton.2 ⟨Ideal.Quotient.mk _ c, ?_⟩` and prove the remaining obligations. Use `congrArg (Ideal.Quotient.mk (Ideal.span {1 - e})) hc` as an intermediate fact. Simplify `this` using `only [map_mul, map_add, map_sub, map_one, mk_e, sub_self, add_zero, one_mul]`.
-/
theorem val_quot (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) (h : A.VAL) : (obj A he).VAL := by
  intro f g ⟨N, hN⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hpi : (obj A he).pi = Ideal.Quotient.mk (Ideal.span {1 - e}) A.pi := rfl
  rw [hpi] at hab
  have hab' : Ideal.Quotient.mk (Ideal.span {1 - e}) (a * f + b * g) = Ideal.Quotient.mk (Ideal.span {1 - e}) (A.pi ^ N) := by
    rw [map_add, map_mul, map_mul, map_pow]; exact hab
  rw [mk_eq_iff he] at hab'
  have hmem : A.pi ^ N ∈ Ideal.span {e * f + (1 - e), e * g} := by
    refine Ideal.mem_span_pair.2 ⟨e * a + (1 - e) * A.pi ^ N, b, ?_⟩
    have e2 : e * e = e := he.eq
    have : (e * a + (1 - e) * A.pi ^ N) * (e * f + (1 - e)) + b * (e * g)
        = e * (a * f + b * g) + (e * e - e) * (a * f) + (e - e * e) * (a + A.pi ^ N * f) + (1 - 2 * e + e * e) * A.pi ^ N := by ring
    rw [this, hab', e2]; ring
  obtain ⟨u, hu, h1, h2⟩ := h _ _ ⟨N, hmem⟩
  refine ⟨Ideal.Quotient.mk _ u, hu.map (Ideal.Quotient.mk _), ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h1
    refine Ideal.mem_span_singleton.2 ⟨Ideal.Quotient.mk _ c, ?_⟩
    have := congrArg (Ideal.Quotient.mk (Ideal.span {1 - e})) hc
    simpa only [map_mul, map_add, map_sub, map_one, mk_e, sub_self, add_zero, one_mul] using this
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h2
    refine Ideal.mem_span_singleton.2 ⟨Ideal.Quotient.mk _ c, ?_⟩
    have := congrArg (Ideal.Quotient.mk (Ideal.span {1 - e})) hc
    simpa only [map_mul, map_add, map_sub, map_one, mk_e, sub_self, add_zero, one_mul] using this

variable {A B : PAlg l}

/- English proof (translation)
Establish `key : ∀ y ∈ B.Acr0, ∃ z : A.Acr0, awayW (Hom.f f) z.1 = y`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`.

Conclude with `⟨A.dxi0 k, (awayW_dpw (Hom.f f) k (A.isUnit_natCast k.factorial_ne_zero) A.xi).trans (congrArg (dpw k) (mapW_xi f))⟩`. Consider the case `algebraMap x`. Take `⟨w, rfl⟩` from `WittVector.map_surjective (Hom.f f) hs x`. Conclude with `⟨algebraMap A.W A.Acr0 w, awayW_algebraMap (Hom.f f) w⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, map_mul _ _ _⟩`. Introduce `y`. Take `⟨z, hz⟩` from `key y.1 y.2`. Conclude with `⟨z, Subtype.ext hz⟩`.
-/
theorem acrisZero_surjective_of_surjective (f : A ⟶ B) (hs : Function.Surjective (Hom.f f)) :
    Function.Surjective (pdOk_hom f).acr0 := by
  have key : ∀ y ∈ B.Acr0, ∃ z : A.Acr0, awayW (Hom.f f) z.1 = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨A.dxi0 k, (awayW_dpw (Hom.f f) k (A.isUnit_natCast k.factorial_ne_zero) A.xi).trans
        (congrArg (dpw k) (mapW_xi f))⟩
    | algebraMap x =>
      obtain ⟨w, rfl⟩ := WittVector.map_surjective (Hom.f f) hs x
      exact ⟨algebraMap A.W A.Acr0 w, awayW_algebraMap (Hom.f f) w⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  intro y
  obtain ⟨z, hz⟩ := key y.1 y.2
  exact ⟨z, Subtype.ext hz⟩

/- English proof (translation)
Introduce `x` and use `by obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x obtain ⟨z, rfl⟩ := acrisZero_surjective_of_surjective f hs y exact ⟨A.mkAcr n z, rfl⟩`.
-/
theorem mapAcr_surjective (f : A ⟶ B) (hs : Function.Surjective (Hom.f f)) (n : ℕ) :
    Function.Surjective (mapAcr f n) := fun x => by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, rfl⟩ := acrisZero_surjective_of_surjective f hs y
  exact ⟨A.mkAcr n z, rfl⟩

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `h0 : B.mkAcr n ((pdOk_hom f).acr0 y) = 0` using `hx`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Take `⟨y₁, rfl⟩` from `acrisZero_surjective_of_surjective f hs c`. Establish `hz : (pdOk_hom f).acr0 (y - y₁ * (l : A.Acr0) ^ n) = 0`.

Rewrite using `[map_sub, map_mul, map_pow, map_natCast, hc, sub_self]`. Establish `hz' : awayW (Hom.f f) (y - y₁ * (l : A.Acr0) ^ n).1 = 0` using `congrArg Subtype.val hz`. Take `⟨⟨w, s⟩, hw⟩` from `IsLocalization.surj (Submonoid.powers (l : A.W)) (y - y₁ * (l : A.Acr0) ^ n).1`. Establish `hw0 : WittVector.map (Hom.f f) w = 0`. Apply `B.algebraMap_WL_injective` to reduce the goal to its premises.

Establish `hw' : (y - y₁ * (l : A.Acr0) ^ n).1 * algebraMap A.W (WL l A.A) s = algebraMap A.W (WL l A.A) w` using `hw`. Rewrite using `[map_zero, ← awayW_algebraMap, ← hw', map_mul, hz', zero_mul]`. Establish `hEz : algebraMap A.W (WL l A.A) E * (y - y₁ * (l : A.Acr0) ^ n).1 = 0`. Establish `hu : IsUnit (algebraMap A.W (WL l A.A) s)` using `IsLocalization.map_units _ s`. Apply `hu.mul_right_cancel` to reduce the goal to its premises.

Establish `hw' : (y - y₁ * (l : A.Acr0) ^ n).1 * algebraMap A.W (WL l A.A) s = algebraMap A.W (WL l A.A) w` using `hw`. Rewrite using `[zero_mul, mul_assoc, hw', ← map_mul, hE w hw0, map_zero]`. Establish `hEz' : algebraMap A.W A.Acr0 E * (y - y₁ * (l : A.Acr0) ^ n) = 0` using `Subtype.ext hEz`. Establish `hfin : algebraMap A.W A.Acr0 E * y = (algebraMap A.W A.Acr0 E * y₁) * (l : A.Acr0) ^ n`. Rewrite `hEz'` using `[mul_sub, sub_eq_zero]`.

Rewrite using `[hEz', mul_assoc]`. Express the relevant statement in the definitionally equal form `A.mkAcr n (algebraMap A.W A.Acr0 E) * A.mkAcr n y = 0`. Rewrite using `[← map_mul, hfin]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem mul_mapAcr_eq_zero (f : A ⟶ B) (hs : Function.Surjective (Hom.f f)) (E : A.W)
    (hE : ∀ w : A.W, WittVector.map (Hom.f f) w = 0 → E * w = 0) (n : ℕ) (x : A.Acr n)
    (hx : mapAcr f n x = 0) : A.toAcr n E * x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h0 : B.mkAcr n ((pdOk_hom f).acr0 y) = 0 := hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  obtain ⟨y₁, rfl⟩ := acrisZero_surjective_of_surjective f hs c
  have hz : (pdOk_hom f).acr0 (y - y₁ * (l : A.Acr0) ^ n) = 0 := by
    rw [map_sub, map_mul, map_pow, map_natCast, hc, sub_self]
  have hz' : awayW (Hom.f f) (y - y₁ * (l : A.Acr0) ^ n).1 = 0 := congrArg Subtype.val hz
  obtain ⟨⟨w, s⟩, hw⟩ := IsLocalization.surj (Submonoid.powers (l : A.W)) (y - y₁ * (l : A.Acr0) ^ n).1
  have hw0 : WittVector.map (Hom.f f) w = 0 := by
    apply B.algebraMap_WL_injective
    have hw' : (y - y₁ * (l : A.Acr0) ^ n).1 * algebraMap A.W (WL l A.A) s = algebraMap A.W (WL l A.A) w := hw
    rw [map_zero, ← awayW_algebraMap, ← hw', map_mul, hz', zero_mul]
  have hEz : algebraMap A.W (WL l A.A) E * (y - y₁ * (l : A.Acr0) ^ n).1 = 0 := by
    have hu : IsUnit (algebraMap A.W (WL l A.A) s) := IsLocalization.map_units _ s
    apply hu.mul_right_cancel
    have hw' : (y - y₁ * (l : A.Acr0) ^ n).1 * algebraMap A.W (WL l A.A) s = algebraMap A.W (WL l A.A) w := hw
    rw [zero_mul, mul_assoc, hw', ← map_mul, hE w hw0, map_zero]
  have hEz' : algebraMap A.W A.Acr0 E * (y - y₁ * (l : A.Acr0) ^ n) = 0 := Subtype.ext hEz
  have hfin : algebraMap A.W A.Acr0 E * y = (algebraMap A.W A.Acr0 E * y₁) * (l : A.Acr0) ^ n := by
    rw [mul_sub, sub_eq_zero] at hEz'
    rw [hEz', mul_assoc]
  change A.mkAcr n (algebraMap A.W A.Acr0 E) * A.mkAcr n y = 0
  rw [← map_mul, hfin]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Obj

/- English proof (translation)
Introduce `l _ A e he`. Establish `hs : Function.Surjective (Hom.f (proj A he))` using `Ideal.Quotient.mk_surjective`. Use `⟨obj A he, proj A he, fun h => ⟨aic_quot h.1, val_quot A he h.2⟩, mk_e, ?_, fun n => ⟨mapAcr_surjective _ hs n, mul_mapAcr_eq_zero _ hs _ (fun w hw => teich_mul_eq_zero he w hw) n⟩⟩` and prove the remaining obligations. Introduce `B ψ hψ`. Establish `hk : ∀ a ∈ Ideal.span {1 - e}, Hom.f ψ a = 0`.

Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul, map_sub, map_one, hψ, sub_self, mul_zero]`. Establish `hcomm : (Ideal.Quotient.lift _ (Hom.f ψ) hk).comp (obj A he).s = B.s`. Use `Hom.comm ψ` as an intermediate fact.

Conclude with `this`. Use `⟨⟨Ideal.Quotient.lift _ (Hom.f ψ) hk, hcomm⟩, Hom.ext (RingHom.ext fun x => rfl), fun χ hχ => Hom.ext ?_⟩` and prove the remaining obligations. Use `Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Conclude with `RingHom.congr_fun (congrArg Hom.f hχ) x`.
-/
theorem directFactor : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A), IsIdempotentElem e → ∃ (A' : PAlg l) (lam : A ⟶ A'), (A.IsTest → A'.IsTest) ∧ PAlg.Hom.f lam e = 1 ∧ (∀ (B : PAlg l) (ψ : A ⟶ B), PAlg.Hom.f ψ e = 1 → ∃! χ : A' ⟶ B, lam ≫ χ = ψ) ∧ ∀ n, Function.Surjective (mapAcr lam n) ∧ ∀ x, mapAcr lam n x = 0 → A.toAcr n (WittVector.teichmuller l e) * x = 0 := by
  intro l _ A e he
  have hs : Function.Surjective (Hom.f (proj A he)) := Ideal.Quotient.mk_surjective
  refine ⟨obj A he, proj A he, fun h => ⟨aic_quot h.1, val_quot A he h.2⟩, mk_e, ?_, fun n =>
    ⟨mapAcr_surjective _ hs n, mul_mapAcr_eq_zero _ hs _ (fun w hw => teich_mul_eq_zero he w hw) n⟩⟩
  intro B ψ hψ
  have hk : ∀ a ∈ Ideal.span {1 - e}, Hom.f ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, map_one, hψ, sub_self, mul_zero]
  have hcomm : (Ideal.Quotient.lift _ (Hom.f ψ) hk).comp (obj A he).s = B.s := by
    have := Hom.comm ψ
    exact this
  refine ⟨⟨Ideal.Quotient.lift _ (Hom.f ψ) hk, hcomm⟩, Hom.ext (RingHom.ext fun x => rfl), fun χ hχ => Hom.ext ?_⟩
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  exact RingHom.congr_fun (congrArg Hom.f hχ) x

end GlobalTheory.CompanionTheory.IdemObj
