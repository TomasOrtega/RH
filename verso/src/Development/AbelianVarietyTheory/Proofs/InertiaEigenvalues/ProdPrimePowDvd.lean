import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

open PowerSeries in

/- English proof (translation)
Establish `hres : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) = PowerSeries.X`. Establish `hx0 : IsLocalRing.residue O x = 0` using `(IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)`. Rewrite using `[map_sub, PowerSeries.map_X, PowerSeries.map_C, hx0, map_zero, sub_zero]`. Establish `hne : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) ≠ 0`. Rewrite using `[hres]`.

Conclude with `PowerSeries.X_ne_zero`. Take `⟨q, r, hdeg, heq⟩` from `a.exists_isWeierstrassDivision hne`. Express the relevant statement in the definitionally equal form `r.degree < ((PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O)).order.toNat at hdeg`. Rewrite `hdeg` using `[hres, PowerSeries.order_X]`. Establish `hr : r = Polynomial.C (r.coeff 0)`.

Establish `h1 : r.degree < 0 + 1` using `by simpa using hdeg`. Conclude with `Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ h1)`. Use `⟨q, r.coeff 0, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, hr, Polynomial.coe_C, Polynomial.coeff_C_zero]`.
-/
theorem exists_div_X_sub_C {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : O) (hx : ¬ IsUnit x) (a : PowerSeries O) :
    ∃ (b : PowerSeries O) (c : O), a = (PowerSeries.X - PowerSeries.C x) * b + PowerSeries.C c := by
  have hres : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) =
      PowerSeries.X := by
    have hx0 : IsLocalRing.residue O x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, hx0, map_zero, sub_zero]
  have hne : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [hres]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg, heq⟩ := a.exists_isWeierstrassDivision hne
  change r.degree < ((PowerSeries.X - PowerSeries.C x : PowerSeries O).map
      (IsLocalRing.residue O)).order.toNat at hdeg
  rw [hres, PowerSeries.order_X] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) := by
    have h1 : r.degree < 0 + 1 := by simpa using hdeg
    exact Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ h1)
  refine ⟨q, r.coeff 0, ?_⟩
  rw [heq, hr, Polynomial.coe_C, Polynomial.coeff_C_zero]

section
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]

/- English proof (translation)
Simplify `ev.commutes c` using `[PowerSeries.algebraMap_apply]`.
-/
theorem ev_C (ev : PowerSeries O →ₐ[O] PowerSeries L) (c : O) :
    ev (PowerSeries.C c) = PowerSeries.C (algebraMap O L c) := by
  simpa [PowerSeries.algebraMap_apply] using ev.commutes c

/- English proof (translation)
Establish `hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w`. Rewrite using `[map_sub, hev, ev_C]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨b, c, rfl⟩` from `exists_div_X_sub_C x hx a`. Rewrite `h` using `[map_add, map_mul, hXev, ev_C]`. Establish `h2 : PowerSeries.X ∣ PowerSeries.C (algebraMap O L c)` using `(dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).1 h`. Rewrite `h2` using `[PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C]`. Establish `hc : c = 0` using `hinj (by rw [h2, map_zero])`.

Substitute `hc` using the available equality. Rewrite using `[map_zero, add_zero]`. Conclude with `dvd_mul_right _ _`. Introduce and unpack `⟨b, rfl⟩`. Rewrite using `[map_mul, hXev, mul_assoc]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem X_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (a : PowerSeries O) :
    PowerSeries.X ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  constructor
  · intro h
    obtain ⟨b, c, rfl⟩ := exists_div_X_sub_C x hx a
    rw [map_add, map_mul, hXev, ev_C] at h
    have h2 : PowerSeries.X ∣ PowerSeries.C (algebraMap O L c) :=
      (dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).1 h
    rw [PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C] at h2
    have hc : c = 0 := hinj (by rw [h2, map_zero])
    subst hc
    rw [map_zero, add_zero]
    exact dvd_mul_right _ _
  · rintro ⟨b, rfl⟩
    rw [map_mul, hXev, mul_assoc]
    exact dvd_mul_right _ _

/- English proof (translation)
Establish `hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w`. Rewrite using `[map_sub, hev, ev_C]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `m generalizing a with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : PowerSeries.X ∣ ev a` using `(dvd_pow_self _ (Nat.succ_ne_zero m)).trans h`. Take `⟨b, rfl⟩` from `(X_dvd_ev_iff hinj hx ev hev a).1 h1`.

Rewrite `h` using `[map_mul, hXev, pow_succ', mul_assoc]`. Establish `h2 : PowerSeries.X ^ m ∣ w * ev b` using `(mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 h`. Establish `h3 : PowerSeries.X ^ m ∣ ev b` using `(IsUnit.dvd_mul_left hw).1 h2`. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ ((ih b).1 h3)`.

Introduce and unpack `⟨b, rfl⟩`. Rewrite using `[pow_succ' (PowerSeries.X - PowerSeries.C x), mul_assoc, map_mul, hXev, pow_succ' (PowerSeries.X : PowerSeries L), mul_assoc]`. Conclude with `mul_dvd_mul_left _ (dvd_mul_of_dvd_right ((ih _).2 (dvd_mul_right _ _)) _)`.
-/
theorem X_pow_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (m : ℕ) (a : PowerSeries O) :
    PowerSeries.X ^ m ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ^ m ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    constructor
    · intro h
      have h1 : PowerSeries.X ∣ ev a := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans h
      obtain ⟨b, rfl⟩ := (X_dvd_ev_iff hinj hx ev hev a).1 h1
      rw [map_mul, hXev, pow_succ', mul_assoc] at h
      have h2 : PowerSeries.X ^ m ∣ w * ev b := (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 h
      have h3 : PowerSeries.X ^ m ∣ ev b := (IsUnit.dvd_mul_left hw).1 h2
      rw [pow_succ']
      exact mul_dvd_mul_left _ ((ih b).1 h3)
    · rintro ⟨b, rfl⟩
      rw [pow_succ' (PowerSeries.X - PowerSeries.C x), mul_assoc, map_mul, hXev,
        pow_succ' (PowerSeries.X : PowerSeries L), mul_assoc]
      exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right ((ih _).2 (dvd_mul_right _ _)) _)

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `congrArg (PowerSeries.coeff 1) h`. Simplify using `at h1`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`.

Simplify using `using hx`. Introduce `a b h`. Rewrite `h` using `[← X_dvd_ev_iff hinj hx ev hev, map_mul]`. Rewrite using `[← X_dvd_ev_iff hinj hx ev hev a, ← X_dvd_ev_iff hinj hx ev hev b]`. Conclude with `PowerSeries.X_prime.2.2 _ _ h`.
-/
theorem prime_X_sub_C (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) :
    Prime (PowerSeries.X - PowerSeries.C x : PowerSeries O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp at h1
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hx
  · intro a b h
    rw [← X_dvd_ev_iff hinj hx ev hev, map_mul] at h
    rw [← X_dvd_ev_iff hinj hx ev hev a, ← X_dvd_ev_iff hinj hx ev hev b]
    exact PowerSeries.X_prime.2.2 _ _ h

end

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi]`. Take `⟨t, ht⟩` from `ih`.

Establish `hnd : ¬ p i ∣ ∏ k ∈ s, p k ^ m k`. Introduce `hd`. Take `⟨k, hk, hdk⟩` from `((hp i).dvd_finsetProd_iff _).1 hd`. Establish `hik` using `hne i k ((hp i).dvd_of_dvd_pow hdk)`. Substitute `hik` using the available equality.

Conclude with `hi hk`. Establish `hdt : p i ^ m i ∣ t` using `(hp i).pow_dvd_of_dvd_mul_left _ hnd (by rw [← ht]; exact h i)`. Rewrite using `[ht, mul_comm _ t]`. Conclude with `mul_dvd_mul_right hdt _`.
-/
theorem prod_prime_pow_dvd {R ι : Type} [CommRing R] [IsDomain R] (p : ι → R) (m : ι → ℕ)
    (hp : ∀ k, Prime (p k)) (hne : ∀ j k, p j ∣ p k → j = k) (a : R)
    (h : ∀ k, p k ^ m k ∣ a) (s : Finset ι) : (∏ k ∈ s, p k ^ m k) ∣ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    obtain ⟨t, ht⟩ := ih
    have hnd : ¬ p i ∣ ∏ k ∈ s, p k ^ m k := by
      intro hd
      obtain ⟨k, hk, hdk⟩ := ((hp i).dvd_finsetProd_iff _).1 hd
      have hik := hne i k ((hp i).dvd_of_dvd_pow hdk)
      subst hik
      exact hi hk
    have hdt : p i ^ m i ∣ t :=
      (hp i).pow_dvd_of_dvd_mul_left _ hnd (by rw [← ht]; exact h i)
    rw [ht, mul_comm _ t]
    exact mul_dvd_mul_right hdt _

/- English proof (translation)
Introduce `O _ _ _ _ LL _ _ _ ι _ x m hxinj hxu ev hev a`. Establish `hinj : Function.Injective (algebraMap O LL)` using `IsFractionRing.injective O LL`. Establish `key : ∀ k, PowerSeries.X ^ m k ∣ ev k a ↔ (PowerSeries.X - PowerSeries.C (x k)) ^ m k ∣ a`. Introduce `k`. Take `⟨w, hw, hwk⟩` from `hev k`.

Conclude with `X_pow_dvd_ev_iff hinj (hxu k) (ev k) hw hwk (m k) a`. Repeatedly rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `prod_prime_pow_dvd (fun k => PowerSeries.X - PowerSeries.C (x k)) m ?_ ?_ a h Finset.univ` and prove the remaining obligations.

Introduce `k`. Take `⟨w, -, hwk⟩` from `hev k`. Conclude with `prime_X_sub_C hinj (hxu k) (ev k) hwk`. Introduce `j k hjk`. Take `⟨w, -, hwj⟩` from `hev j`.

Establish `h1` using `(X_dvd_ev_iff hinj (hxu j) (ev j) hwj _).2 hjk`. Rewrite `h1` using `[map_sub, hwj, ev_C, PowerSeries.X_dvd_iff]`. Establish `h2 : algebraMap O LL (x j) = algebraMap O LL (x k)`. Simplify `h1` using `[sub_eq_zero]`. Conclude with `hxinj (hinj h2)`.

Introduce `h k`. Conclude with `(Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans h`.
-/
theorem weierstrass_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O], ∀ (LL : Type) [Field LL] [Algebra O LL] [IsFractionRing O LL] (ι : Type) [Fintype ι] (x : ι → O) (m : ι → ℕ), Function.Injective x → (∀ k, ¬ IsUnit (x k)) → ∀ (ev : ι → (PowerSeries O →ₐ[O] PowerSeries LL)), (∀ k, ∃ w : PowerSeries LL, IsUnit w ∧ ev k PowerSeries.X = PowerSeries.C (algebraMap O LL (x k)) + PowerSeries.X * w) → ∀ a : PowerSeries O, (∀ k, PowerSeries.X ^ m k ∣ ev k a) ↔ (∏ k, (PowerSeries.X - PowerSeries.C (x k)) ^ m k) ∣ a := by
  intro O _ _ _ _ LL _ _ _ ι _ x m hxinj hxu ev hev a
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have key : ∀ k, PowerSeries.X ^ m k ∣ ev k a ↔
      (PowerSeries.X - PowerSeries.C (x k)) ^ m k ∣ a := by
    intro k
    obtain ⟨w, hw, hwk⟩ := hev k
    exact X_pow_dvd_ev_iff hinj (hxu k) (ev k) hw hwk (m k) a
  simp_rw [key]
  constructor
  · intro h
    refine prod_prime_pow_dvd (fun k => PowerSeries.X - PowerSeries.C (x k)) m ?_ ?_ a h
      Finset.univ
    · intro k
      obtain ⟨w, -, hwk⟩ := hev k
      exact prime_X_sub_C hinj (hxu k) (ev k) hwk
    · intro j k hjk
      obtain ⟨w, -, hwj⟩ := hev j
      have h1 := (X_dvd_ev_iff hinj (hxu j) (ev j) hwj _).2 hjk
      rw [map_sub, hwj, ev_C, PowerSeries.X_dvd_iff] at h1
      have h2 : algebraMap O LL (x j) = algebraMap O LL (x k) := by
        simpa [sub_eq_zero] using h1
      exact hxinj (hinj h2)
  · intro h k
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans h

end GlobalTheory.Per
