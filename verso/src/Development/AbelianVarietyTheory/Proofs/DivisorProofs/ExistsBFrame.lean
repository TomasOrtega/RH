import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfEqZero

set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]
  {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

/- English proof (translation)
Use `haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `dvd_of_eq_zero (ε := ε) 0 y (by rw [map_zero, zero_add]; exact h)` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_add, sq]`.

Conclude with `(mul_dvd_mul_iff_left (mu_ne hv hε)).1 this`. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[map_mul, ← p_τ]`. Take the linear combination `(↑p * a ε z) * τ_sq ε`.
-/
theorem tau_mul (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (y : Ainf p O) :
    τ ε * a ε y = 0 ↔ mu ε ∣ y := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  constructor
  · intro h
    have := dvd_of_eq_zero (ε := ε) 0 y (by rw [map_zero, zero_add]; exact h)
    rw [mul_zero, zero_add, sq] at this
    exact (mul_dvd_mul_iff_left (mu_ne hv hε)).1 this
  · rintro ⟨z, rfl⟩
    rw [map_mul, ← p_τ]
    linear_combination (↑p * a ε z) * τ_sq ε

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`. Take `⟨u, w, rfl⟩` from `gen ε b`. Establish `h` using `dvd_of_eq_zero (ε := ε) x (-u) (by`. Rewrite using `[hb, map_neg]`.

Take the linear combination `(a ε w) * τ_sq ε)`. Conclude with `mu_dvd hv hε x (by`. Establish `h2 : mu ε ∣ mu ε * -u` using `dvd_mul_right _ _`. Establish `h3` using `(dvd_pow_self (mu ε) two_ne_zero).trans h`. Simplify using `using (dvd_add_left h2).1 h3)`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨p * a ε c, by rw [map_mul, ← p_τ]; ring⟩`.
-/
theorem tau_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    τ ε ∣ a ε x ↔ mu ε ∣ x := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨u, w, rfl⟩ := gen ε b
    have h := dvd_of_eq_zero (ε := ε) x (-u) (by
      rw [hb, map_neg]; linear_combination (a ε w) * τ_sq ε)
    exact mu_dvd hv hε x (by
      have h2 : mu ε ∣ mu ε * -u := dvd_mul_right _ _
      have h3 := (dvd_pow_self (mu ε) two_ne_zero).trans h
      simpa using (dvd_add_left h2).1 h3)
  · rintro ⟨c, rfl⟩
    exact ⟨p * a ε c, by rw [map_mul, ← p_τ]; ring⟩

/- English proof (translation)
Establish `hp : (p : O) ≠ 0` using `fun h0 => by`. Use `congrArg (algebraMap O C) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this`. Use `haveI : IsDomain O := (algebraMap O C).domain_nontrivial |> fun _ => Function.Injective.isDomain (algebraMap O C) hv.hom_inj`.

Conclude with `(mul_eq_zero.1 h).resolve_left hp`.
-/
theorem sat (hv : v.Integers O) (b : O) (h : (p : O) * b = 0) : b = 0 := by
  have hp : (p : O) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap O C) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  haveI : IsDomain O := (algebraMap O C).domain_nontrivial |> fun _ =>
    Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  exact (mul_eq_zero.1 h).resolve_left hp

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]`.
-/
theorem smod_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {q}) ^ n • (⊤ : Submodule R R)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {(p : Ainf p O)}) (fun N => u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) (by`. Introduce `m n hmn`. Rewrite using `[smod_iff, ← dvd_neg, neg_sub]`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[Finset.sum_range_succ, show ∀ s t w : Ainf p O, u0 + (s + t) - w = (u0 + s - w) + t from fun _ _ _ => by ring]`. Conclude with `dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _))`. Conclude with `⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩`.
-/
theorem lim_series (u0 : Ainf p O) (u : ℕ → Ainf p O) : ∃ L : Ainf p O, ∀ n,
    (p : Ainf p O) ^ n ∣ (u0 + ∑ k ∈ Finset.range n, (p : Ainf p O) ^ k * u k) - L := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : Ainf p O)})
    (fun N => u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) (by
      intro m n hmn
      rw [smod_iff, ← dvd_neg, neg_sub]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [Finset.sum_range_succ, show ∀ s t w : Ainf p O, u0 + (s + t) - w = (u0 + s - w) + t
          from fun _ _ _ => by ring]
        exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _))
  exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩

/- English proof (translation)
Use `haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : ∀ n, (p : BR ε) ^ n ∣ x` using `fun n => by simpa using (smod_iff _ n x 0).1 (hx n)`. Take `⟨u, w, rfl⟩` from `gen ε x`.

Use `eq_zero_of_dvd hv hε u w (GlobalTheory.MuDivides.dvd_of_step (p : Ainf p O) (mu ε ^ 2) (fun z => ∀ n, ∃ s t, z = (p : Ainf p O) ^ n * s + mu ε ^ 2 * t) ?_ _ ?_)` and prove the remaining obligations. Introduce `z hz`. Take `⟨s, t, hst⟩` from `hz 1`. Use `⟨t, s, by rw [hst]; ring, fun n => ?_⟩` and prove the remaining obligations. Take `⟨s', t', hst'⟩` from `hz (n + 1)`.

Take `⟨e, he⟩` from `mu_sq_dvd hv hε (s - p ^ n * s') ⟨t' - t, by`. Take the linear combination `hst' - hst⟩`. Conclude with `⟨s', e, by linear_combination he⟩`. Introduce `n`. Take `⟨c, hc⟩` from `hx' n`.

Take `⟨s', t', rfl⟩` from `gen ε c`. Take `⟨e, he⟩` from `dvd_of_eq_zero (ε := ε) (u - p ^ n * s') (w - p ^ n * t') (by`. Simplify using `only [map_sub, map_mul, map_pow, map_natCast]`. Take the linear combination `hc)`. Conclude with `⟨p * s' + mu ε * t', e, by linear_combination he⟩`.

Introduce `f hf`. Establish `hstep : ∀ n, ∃ c, f (n + 1) - f n = (p : BR ε) ^ n * c` using `fun n => by`. Take `⟨c, hc⟩` from `(smod_iff _ n (f n) (f (n + 1))).1 (hf (Nat.le_succ n))`. Conclude with `⟨-c, by linear_combination -hc⟩`. Use `choose c hc using hstep`.

Use `choose u w huw using fun n => gen ε (c n)`. Take `⟨u0, w0, h0⟩` from `gen ε (f 0)`. Take `⟨LX, hX⟩` from `lim_series u0 u`. Take `⟨LY, hY⟩` from `lim_series w0 w`. Establish `hf' : ∀ N, f N = a ε (u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) + τ ε * a ε (w0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * w k)`.

Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simpa using h0`. Consider the case `succ N ih`. Use `hc N` as an intermediate fact.

Rewrite `this` using `[huw N]`. Simplify using `only [Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast] at ih ⊢`. Take the linear combination `this + ih`. Use `⟨a ε LX + τ ε * a ε LY, fun n => (smod_iff _ _ _ _).2 ?_⟩` and prove the remaining obligations. Take `⟨e1, he1⟩` from `hX n`.

Take `⟨e2, he2⟩` from `hY n`. Use `⟨a ε e1 + τ ε * a ε e2, ?_⟩` and prove the remaining obligations. Rewrite using `[hf' n]`. Establish `h1` using `congrArg (a ε) he1`. Establish `h2` using `congrArg (a ε) he2`.

Simplify using `only [map_sub, map_mul, map_pow, map_natCast, map_add] at h1 h2 ⊢`. Take the linear combination `h1 + τ ε * h2`.
-/
theorem complete (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    IsAdicComplete (Ideal.span {(p : BR ε)}) (BR ε) := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n, (p : BR ε) ^ n ∣ x := fun n => by simpa using (smod_iff _ n x 0).1 (hx n)
    obtain ⟨u, w, rfl⟩ := gen ε x
    refine eq_zero_of_dvd hv hε u w (GlobalTheory.MuDivides.dvd_of_step (p : Ainf p O) (mu ε ^ 2)
      (fun z => ∀ n, ∃ s t, z = (p : Ainf p O) ^ n * s + mu ε ^ 2 * t) ?_ _ ?_)
    · intro z hz
      obtain ⟨s, t, hst⟩ := hz 1
      refine ⟨t, s, by rw [hst]; ring, fun n => ?_⟩
      obtain ⟨s', t', hst'⟩ := hz (n + 1)
      obtain ⟨e, he⟩ := mu_sq_dvd hv hε (s - p ^ n * s') ⟨t' - t, by
        linear_combination hst' - hst⟩
      exact ⟨s', e, by linear_combination he⟩
    · intro n
      obtain ⟨c, hc⟩ := hx' n
      obtain ⟨s', t', rfl⟩ := gen ε c
      obtain ⟨e, he⟩ := dvd_of_eq_zero (ε := ε) (u - p ^ n * s') (w - p ^ n * t') (by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hc)
      exact ⟨p * s' + mu ε * t', e, by linear_combination he⟩
  · intro f hf
    have hstep : ∀ n, ∃ c, f (n + 1) - f n = (p : BR ε) ^ n * c := fun n => by
      obtain ⟨c, hc⟩ := (smod_iff _ n (f n) (f (n + 1))).1 (hf (Nat.le_succ n))
      exact ⟨-c, by linear_combination -hc⟩
    choose c hc using hstep
    choose u w huw using fun n => gen ε (c n)
    obtain ⟨u0, w0, h0⟩ := gen ε (f 0)
    obtain ⟨LX, hX⟩ := lim_series u0 u
    obtain ⟨LY, hY⟩ := lim_series w0 w
    have hf' : ∀ N, f N = a ε (u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) +
        τ ε * a ε (w0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * w k) := by
      intro N
      induction N with
      | zero => simpa using h0
      | succ N ih =>
        have := hc N
        rw [huw N] at this
        simp only [Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast] at ih ⊢
        linear_combination this + ih
    refine ⟨a ε LX + τ ε * a ε LY, fun n => (smod_iff _ _ _ _).2 ?_⟩
    obtain ⟨e1, he1⟩ := hX n
    obtain ⟨e2, he2⟩ := hY n
    refine ⟨a ε e1 + τ ε * a ε e2, ?_⟩
    rw [hf' n]
    have h1 := congrArg (a ε) he1
    have h2 := congrArg (a ε) he2
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add] at h1 h2 ⊢
    linear_combination h1 + τ ε * h2

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih]`. Use `push_cast`.

Take the linear combination `((n + 1 : R) * s ^ n) * ht`.
-/
theorem sqz_pow {R : Type} [CommRing R] (s t : R) (ht : t * t = 0) (n : ℕ) :
    (s + t) ^ (n + 1) = s ^ (n + 1) + (n + 1) * s ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((n + 1 : R) * s ^ n) * ht

/- English proof (translation)
Establish `hsq : (τ ε * a ε y) * (τ ε * a ε y) = 0`. Take the linear combination `(a ε y * a ε y) * τ_sq ε`. Establish `h` using `sqz_pow (a ε x) (τ ε * a ε y) hsq (p - 1)`. Establish `h1 : p - 1 + 1 = p` using `Nat.sub_add_cancel (Fact.out : p.Prime).one_le`. Establish `h2 : ((p - 1 : ℕ) : BR ε) + 1 = p` using `by rw [← Nat.cast_add_one, h1]`.

Rewrite `h` using `[h1, h2]`. Then use the resulting hypothesis.
-/
theorem pow_gen (x y : Ainf p O) : (a ε x + τ ε * a ε y) ^ p =
    a ε x ^ p + p * a ε x ^ (p - 1) * (τ ε * a ε y) := by
  have hsq : (τ ε * a ε y) * (τ ε * a ε y) = 0 := by
    linear_combination (a ε y * a ε y) * τ_sq ε
  have h := sqz_pow (a ε x) (τ ε * a ε y) hsq (p - 1)
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have h2 : ((p - 1 : ℕ) : BR ε) + 1 = p := by rw [← Nat.cast_add_one, h1]
  rwa [h1, h2] at h

/- English proof (translation)
Take `⟨x, y, rfl⟩` from `gen ε b`. Take `⟨z, hz⟩` from `frob_congr x`. Take `⟨d, hd⟩` from `frob_xi ε`. Rewrite using `[pow_gen, map_add, map_mul, σ_a, σ_a, σ_τ, hz, hd]`. Use `⟨a ε z + τ ε * a ε (frobenius y) - a ε x ^ (p - 1) * (τ ε * a ε y), ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Take the linear combination `(-(τ ε * a ε d * a ε (frobenius y))) * p_τ ε + ((p : BR ε) * a ε d * a ε (frobenius y)) * τ_sq ε`.
-/
theorem σ_pow (b : BR ε) : (p : BR ε) ∣ σ ε b - b ^ p := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  obtain ⟨z, hz⟩ := frob_congr x
  obtain ⟨d, hd⟩ := frob_xi ε
  rw [pow_gen, map_add, map_mul, σ_a, σ_a, σ_τ, hz, hd]
  refine ⟨a ε z + τ ε * a ε (frobenius y) - a ε x ^ (p - 1) * (τ ε * a ε y), ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast]
  linear_combination (-(τ ε * a ε d * a ε (frobenius y))) * p_τ ε +
    ((p : BR ε) * a ε d * a ε (frobenius y)) * τ_sq ε

/- English proof (translation)
It suffices to establish `h : (p : BR ε) ∣ x ^ p by`. Take `⟨y, hy⟩` from `h`. Use `⟨y, sat (p := p) hv _ ?_, hy⟩` and prove the remaining obligations. Use `congrArg (θ hε) hy` as an intermediate fact. Rewrite `this` using `[map_pow, hx, zero_pow (Fact.out : p.Prime).ne_zero, map_mul, map_natCast]`.

Conclude with `this.symm`. Take `⟨u, w, rfl⟩` from `gen ε x`. Establish `hu : fontaineTheta O p u = 0`. Rewrite `hx` using `[map_add, map_mul, θ_a, θ_a, θ_τ, zero_mul, add_zero]`. Conclude with `hx`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 (by rw [← GlobalTheory.AinfXi.ker_theta hv ε (prim hε)]; exact hu)`. Take `⟨z, hz⟩` from `frob_congr (xi ε)`. Take `⟨d, hd⟩` from `frob_xi ε`. Establish `hxi : a ε (xi ε) ^ p = p + p * τ ε * a ε d - p * a ε z`. Rewrite using `[← map_pow, show xi ε ^ p = frobenius (xi ε) - p * z by rw [hz]; ring, hd]`.

Simplify using `only [map_add, map_sub, map_mul, map_natCast]`. Rewrite using `[← p_τ]`. Rewrite using `[pow_gen]`. Use `⟨a ε c ^ p * (1 + τ ε * a ε d - a ε z) + a ε (c * xi ε) ^ (p - 1) * (τ ε * a ε w), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_pow, hxi]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : BR ε) (hx : θ hε x = 0) :
    ∃ y, θ hε y = 0 ∧ x ^ p = p * y := by
  suffices h : (p : BR ε) ∣ x ^ p by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, sat (p := p) hv _ ?_, hy⟩
    have := congrArg (θ hε) hy
    rw [map_pow, hx, zero_pow (Fact.out : p.Prime).ne_zero, map_mul, map_natCast] at this
    exact this.symm
  obtain ⟨u, w, rfl⟩ := gen ε x
  have hu : fontaineTheta O p u = 0 := by
    rw [map_add, map_mul, θ_a, θ_a, θ_τ, zero_mul, add_zero] at hx; exact hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1
    (by rw [← GlobalTheory.AinfXi.ker_theta hv ε (prim hε)]; exact hu)
  obtain ⟨z, hz⟩ := frob_congr (xi ε)
  obtain ⟨d, hd⟩ := frob_xi ε
  have hxi : a ε (xi ε) ^ p = p + p * τ ε * a ε d - p * a ε z := by
    rw [← map_pow, show xi ε ^ p = frobenius (xi ε) - p * z by rw [hz]; ring, hd]
    simp only [map_add, map_sub, map_mul, map_natCast]
    rw [← p_τ]
  rw [pow_gen]
  refine ⟨a ε c ^ p * (1 + τ ε * a ε d - a ε z) + a ε (c * xi ε) ^ (p - 1) * (τ ε * a ε w), ?_⟩
  rw [map_mul, mul_pow, hxi]
  ring

/- English proof (translation)
Rewrite using `[← a_natCast ε]`. Use `IsUnit.map _ (GlobalTheory.AinfXi.witt_isUnit _ ?_)` and prove the remaining obligations. Rewrite using `[map_natCast]`. Establish `hu : IsUnit (n : ZMod p)`. Use `(ZMod.unitOfCoprime n h).isUnit` as an intermediate fact.

Rewrite `this` using `[ZMod.coe_unitOfCoprime]`. Then use the resulting hypothesis. Simplify using `using hu.map (ZMod.castHom (dvd_refl p) (PreTilt O p))`.
-/
theorem unit_coprime (n : ℕ) (h : Nat.Coprime n p) : IsUnit (n : BR ε) := by
  rw [← a_natCast ε]
  refine IsUnit.map _ (GlobalTheory.AinfXi.witt_isUnit _ ?_)
  rw [map_natCast]
  have hu : IsUnit (n : ZMod p) := by
    have := (ZMod.unitOfCoprime n h).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  simpa using hu.map (ZMod.castHom (dvd_refl p) (PreTilt O p))

/- English proof (translation)
Take `⟨x, rfl⟩` from `(GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε (prim hε)).2.2.2.1 y`. Conclude with `⟨a ε x, θ_a hε x⟩`. Use `inj := IsLocalization.injective (M := Submonoid.powers (p : BR ε)) _ (Submonoid.powers_le.2 (mem_nonZeroDivisors_iff.2 ⟨fun x hx => torsion_free hv hε x hx, fun x hx => torsion_free hv hε x (by rw [mul_comm]; exact hx)⟩))`. Use `denom q := by`. Take `⟨⟨b, ⟨_, k, rfl⟩⟩, hq⟩` from `IsLocalization.surj (Submonoid.powers (p : BR ε)) q`.

Conclude with `⟨k, b, by rw [← hq, map_pow, map_natCast, mul_comm]⟩`. Use `unit_p := by`. Use `IsLocalization.Away.algebraMap_isUnit (S := BQ ε) (p : BR ε)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `unit_coprime := unit_coprime`.

Use `pd := pd hv hε`. Use `sat := sat hv`. Use `complete := complete hv hε`.
-/
theorem isFrame (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : QLog.IsFrame p (BQ ε) (θ hε) where
  surj y := by
    obtain ⟨x, rfl⟩ := (GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε (prim hε)).2.2.2.1 y
    exact ⟨a ε x, θ_a hε x⟩
  inj := IsLocalization.injective (M := Submonoid.powers (p : BR ε)) _ (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff.2 ⟨fun x hx => torsion_free hv hε x hx,
      fun x hx => torsion_free hv hε x (by rw [mul_comm]; exact hx)⟩))
  denom q := by
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (p : BR ε)) q
    exact ⟨k, b, by rw [← hq, map_pow, map_natCast, mul_comm]⟩
  unit_p := by
    have := IsLocalization.Away.algebraMap_isUnit (S := BQ ε) (p : BR ε)
    rwa [map_natCast] at this
  unit_coprime := unit_coprime
  pd := pd hv hε
  sat := sat hv
  complete := complete hv hε

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε`. Conclude with `⟨QLog.BFrame.mk (BR ε) (BQ ε) (a ε) (θ hε) (σ ε) (s ε) (τ ε) (isFrame hv hε) (θ_a hε) (σ_a ε) (s_alg ε) σ_pow (p_τ ε) (τ_sq ε) (gen ε) (tau_mul hv hε) (tau_dvd hv hε)⟩`.
-/
theorem exists_bFrame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (QLog.BFrame ε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  exact ⟨QLog.BFrame.mk (BR ε) (BQ ε) (a ε) (θ hε) (σ ε) (s ε) (τ ε) (isFrame hv hε) (θ_a hε)
    (σ_a ε) (s_alg ε) σ_pow (p_τ ε) (τ_sq ε) (gen ε) (tau_mul hv hε) (tau_dvd hv hε)⟩

end GlobalTheory.BRing
