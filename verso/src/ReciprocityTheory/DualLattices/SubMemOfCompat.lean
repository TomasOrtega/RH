import ReciprocityTheory.DualLattices.AinfTower
import ReciprocityTheory.DualLattices.HtLinStatement

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

def r'Alg (n : ℕ) : R'n p O ε (n + 1) →ₐ[R0 p O ε] R'n p O ε n :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (R0 p O ε) _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rRing (n : ℕ) : Rn p O (n + 1) →+* Rn p O n :=
  Ideal.Quotient.lift (span {(p : O) ^ (n + 1 + 1)})
    (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rAlg (n : ℕ) : (LR p O hv ε hε (n + 1) : Type) →ₐ[R0 p O ε] (LR p O hv ε hε n : Type) :=
  { toRingHom := rRing p O n
    commutes' := fun _ => rfl }

/- English proof (translation)
Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`.
-/
lemma r'Alg_surj (n : ℕ) : Function.Surjective (r'Alg p O ε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/- English proof (translation)
Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`.
-/
lemma rAlg_surj (n : ℕ) : Function.Surjective (rAlg p O hv ε hε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/- English proof (translation)
Introduce `m k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1 : f (m + k + 1) - f (m + k) ∈ span {(p : O) ^ m}`.

Establish `h` using `hf (m + k)`. Rewrite `h`, the goal using `[Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `h`. Conclude with `⟨a * p ^ (k + 1), by rw [← ha, mul_assoc, ← pow_add]; ring_nf⟩`. Establish `: f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m)`.

Rewrite using `[← add_assoc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ h1 ih`.
-/
lemma sub_mem_of_compat (f : ℕ → O)
    (hf : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)}) :
    ∀ m k, f (m + k) - f m ∈ span {(p : O) ^ m} := by
  intro m k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : f (m + k + 1) - f (m + k) ∈ span {(p : O) ^ m} := by
      have h := hf (m + k)
      rw [Ideal.mem_span_singleton'] at h ⊢
      obtain ⟨a, ha⟩ := h
      exact ⟨a * p ^ (k + 1), by rw [← ha, mul_assoc, ← pow_add]; ring_nf⟩
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]
    exact Ideal.add_mem _ h1 ih

/- English proof (translation)
Use `choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)`. Establish `hc : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)}`. Introduce `n`. Establish `h` using `hx n`. Rewrite `h` using `[← hf (n + 1), ← hf n, rRing, Ideal.Quotient.lift_mk, Ideal.Quotient.eq]`.

Conclude with `h`. Establish `hsm : ∀ m, (span {(p : O)} ^ m • ⊤ : Submodule O O) = span {(p : O) ^ m}`. Introduce `m`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := span {(p : O)}) (M := O) inferInstance (f := f) (fun {m n} hmn => by`.

Rewrite using `[SModEq.sub_mem, hsm]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Use `sub_mem_of_compat p O f hc m k` as an intermediate fact. Rewrite using `[← neg_sub]`. Conclude with `(Ideal.neg_mem_iff _).2 this)`.

Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf n, Ideal.Quotient.eq]`. Establish `h1` using `hL (n + 1)`. Rewrite `h1` using `[SModEq.sub_mem, hsm]`. Establish `h2` using `hc n`.

Establish `: L - f n = (f (n + 1) - f n) - (f (n + 1) - L)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ h2 h1`.
-/
lemma complete_O (x : ∀ n, (Rn p O n)) (hx : ∀ n, rRing p O n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hc : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)} := by
    intro n
    have h := hx n
    rw [← hf (n + 1), ← hf n, rRing, Ideal.Quotient.lift_mk, Ideal.Quotient.eq] at h
    exact h
  have hsm : ∀ m, (span {(p : O)} ^ m • ⊤ : Submodule O O) = span {(p : O) ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {(p : O)}) (M := O) inferInstance
    (f := f) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have := sub_mem_of_compat p O f hc m k
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
  refine ⟨L, fun n => ?_⟩
  rw [← hf n, Ideal.Quotient.eq]
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := hc n
  have : L - f n = (f (n + 1) - f n) - (f (n + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

def ainfTowerL : ATowerL (R0 p O ε) p where
  toATower := ainfTower p O hv ε hε
  r' n := ⟨r'Alg p O ε n, TowerExample.isLocalHom_of_surj _ (r'Alg_surj p O ε n)⟩
  r n := ⟨rAlg p O hv ε hε n, TowerExample.isLocalHom_of_surj _ (rAlg_surj p O hv ε hε n)⟩
  r_π n x := by
    obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x0
    rfl
  r_q n x := rfl
  r'_ξ n := rfl
  complete x hx := complete_O p O x hx

/- English proof (translation)
Use `show ((frobeniusEquiv (PreTilt O p) p).symm^[k + 1] ε) ^ p = _`. Rewrite using `[Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]`. Both sides reduce to the same expression.
-/
lemma root_succ_pow (k : ℕ) : root p O ε (k + 1) ^ p = root p O ε k := by
  show ((frobeniusEquiv (PreTilt O p) p).symm^[k + 1] ε) ^ p = _
  rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_mul, root_succ_pow, ih]`.
-/
lemma root_pow_one (n : ℕ) : root p O ε (n + 1) ^ p ^ n = root p O ε 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, root_succ_pow, ih]

/- English proof (translation)
Rewrite using `[zetaV, zetaV, ← map_pow, ← map_pow, root_succ_pow]`.
-/
theorem zeta_succ_pow (n : ℕ) : zetaV p O ε (n + 1) ^ p = zetaV p O ε n := by
  rw [zetaV, zetaV, ← map_pow, ← map_pow, root_succ_pow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma zeta_val (n : ℕ) :
    (((ainfTower p O hv ε hε).ζ n : ((ainfTower p O hv ε hε).O : Type)ˣ) :
      ((ainfTower p O hv ε hε).O : Type)) = zetaV p O ε n := rfl

include hv hε in

/- English proof (translation)
Establish `hz1 : zetaV p O ε n ^ p ^ (n + 1) = 1`. Rewrite using `[zetaV, ← map_pow, ← map_pow, root_pow, fontaineTheta_teichmuller, untilt_eps p O hv ε hε]`. Establish `hzn : zetaV p O ε n ^ p ^ n ≠ 1`. Rewrite using `[zetaV, ← map_pow, ← map_pow, root_pow_one, fontaineTheta_teichmuller]`. Conclude with `hε.ne_one hp.out.one_lt`.

Establish `hord : orderOf (zetaV p O ε n) ∣ p ^ (n + 1)` using `orderOf_dvd_of_pow_eq_one hz1`. Take `⟨j, hj, hj'⟩` from `(Nat.dvd_prime_pow hp.out).1 hord`. Establish `hjn : j = n + 1`. Assume the negation of the conclusion as `hne`. Establish `hle : j ≤ n` using `by omega`.

Apply `hzn` to reduce the goal to its premises. Establish `: orderOf (zetaV p O ε n) ∣ p ^ n` using `by rw [hj']; exact pow_dvd_pow p hle`. Conclude with `orderOf_dvd_iff_pow_eq_one.1 this`. Rewrite using `[← hjn, ← hj']`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem zeta_primitive (n : ℕ) : IsPrimitiveRoot (zetaV p O ε n) (p ^ (n + 1)) := by
  have hz1 : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow, fontaineTheta_teichmuller,
      untilt_eps p O hv ε hε]
  have hzn : zetaV p O ε n ^ p ^ n ≠ 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow_one, fontaineTheta_teichmuller]
    exact hε.ne_one hp.out.one_lt
  have hord : orderOf (zetaV p O ε n) ∣ p ^ (n + 1) := orderOf_dvd_of_pow_eq_one hz1
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hord
  have hjn : j = n + 1 := by
    by_contra hne
    have hle : j ≤ n := by omega
    apply hzn
    have : orderOf (zetaV p O ε n) ∣ p ^ n := by rw [hj']; exact pow_dvd_pow p hle
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [← hjn, ← hj']
  exact IsPrimitiveRoot.orderOf _

include hv hε in

/- English proof (translation)
Take `⟨-, -, -, hX, -, -⟩` from `a0 p C v O hv`. Conclude with `(hX ε hv hε).2.2.1`.
-/
theorem c_val : v (algebraMap O C (fontaineTheta O p (nu p O ε))) ^ (p - 1) = v (p : C) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  exact (hX ε hv hε).2.2.1

include hv hε in

/- English proof (translation)
Apply `hv.dvd_of_le` to reduce the goal to its premises. Rewrite `h` using `[← c_val p O hv ε hε]`. Establish `hp1 : p - 1 ≠ 0` using `by have := hp.out.two_le; omega`. Conclude with `(pow_le_pow_iff_left₀ zero_le zero_le hp1).1 h`.
-/
theorem c_dvd (c' : O) (h : v (algebraMap O C c') ^ (p - 1) ≤ v (p : C)) :
    fontaineTheta O p (nu p O ε) ∣ c' := by
  apply hv.dvd_of_le
  rw [← c_val p O hv ε hε] at h
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact (pow_le_pow_iff_left₀ zero_le zero_le hp1).1 h

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma c_eq : (ainfTower p O hv ε hε).c = fontaineTheta O p (nu p O ε) := rfl

end Ainf

end ReciprocityTheory.PGsh
