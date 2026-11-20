import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

structure IsDer {A : Type*} [CommRing A] (δ : A → A) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x

namespace IsDer

variable {A : Type*} [CommRing A] {δ : A → A}

/- English proof (translation)
Establish `e` using `h.add 0 0`. Rewrite `e` using `[add_zero]`. Take the linear combination `-e`.
-/
theorem der_zero (h : IsDer δ) : δ 0 = 0 := by
  have e := h.add 0 0
  rw [add_zero] at e
  linear_combination -e

/- English proof (translation)
Establish `e` using `h.mul 1 1`. Simplify using `only [one_mul] at e`. Take the linear combination `-e`.
-/
theorem der_one (h : IsDer δ) : δ 1 = 0 := by
  have e := h.mul 1 1
  simp only [one_mul] at e
  linear_combination -e

/- English proof (translation)
Establish `e` using `h.add x (-x)`. Rewrite `e` using `[add_neg_cancel, h.der_zero]`. Take the linear combination `-e`.
-/
theorem der_neg (h : IsDer δ) (x : A) : δ (-x) = -δ x := by
  have e := h.add x (-x)
  rw [add_neg_cancel, h.der_zero] at e
  linear_combination -e

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]`.
-/
theorem der_sub (h : IsDer δ) (x y : A) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ x (n + 1), h.mul, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_pow_succ (h : IsDer δ) (x : A) (n : ℕ) : δ (x ^ (n + 1)) = (n + 1 : A) * x ^ n * δ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), h.mul, ih]
    push_cast
    ring

/- English proof (translation)
Consider the cases of `r with`. Consider the case `zero => simp [h.der_one]`. Consider the case `succ n`. Rewrite using `[h.der_pow_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_map_pow (h : IsDer δ) (z : A) (r : ℕ) : z * δ (z ^ r) = (r : A) * z ^ r * δ z := by
  cases r with
  | zero => simp [h.der_one]
  | succ n =>
    rw [h.der_pow_succ]
    push_cast
    ring

/- English proof (translation)
Conclude with `map_sum (AddMonoidHom.mk' δ h.add) f s`.
-/
theorem der_sum (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  exact map_sum (AddMonoidHom.mk' δ h.add) f s

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro r hr`. Simplify using `using hr`. Consider the case `succ m ih`.

Introduce `r hr`. Establish `hwJ : δ y * δ (y ^ (m + 1) * δ y ^ r) ∈ I` using `I.mul_mem_left _ (hI _ hr)`. Establish `e` using `h.mul_map_pow (δ y) r`. Establish `key : δ y * δ (y ^ (m + 1) * δ y ^ r) = (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) + ((m : A) + 1) * (y ^ m * δ y ^ (r + 2))`. Rewrite using `[h.mul, h.der_pow_succ]`.

Take the linear combination `y ^ (m + 1) * e`. Establish `h2 : ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) ∈ I`. Establish `h3 : (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) ∈ I` using `I.mul_mem_left _ hr`. Establish `h5` using `I.sub_mem hwJ h3`. Rewrite `h5` using `[key, add_sub_cancel_left]`. Then use the resulting hypothesis.

Establish `hu1` using `hu (m + 1) (Nat.succ_pos m)`. Move the coercions through the operations in `at hu1`. Establish `h4 : y ^ m * δ y ^ (r + 2) ∈ I` using `(Ideal.unit_mul_mem_iff_mem I hu1).mp h2`. Establish `h6` using `ih (r + 2) h4`. Rewrite `h6` using `[show r + 2 + 2 * m = r + 2 * (m + 1) by ring]`. Then use the resulting hypothesis.
-/
theorem pow_map_mem_of_pow_mul_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    (y : A) : ∀ m r : ℕ, y ^ m * δ y ^ r ∈ I → δ y ^ (r + 2 * m) ∈ I := by
  intro m
  induction m with
  | zero => intro r hr; simpa using hr
  | succ m ih =>
    intro r hr
    have hwJ : δ y * δ (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ (hI _ hr)
    have e := h.mul_map_pow (δ y) r
    have key : δ y * δ (y ^ (m + 1) * δ y ^ r) =
        (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) + ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) := by
      rw [h.mul, h.der_pow_succ]
      linear_combination y ^ (m + 1) * e
    have h2 : ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) ∈ I := by
      have h3 : (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ hr
      have h5 := I.sub_mem hwJ h3
      rwa [key, add_sub_cancel_left] at h5
    have hu1 := hu (m + 1) (Nat.succ_pos m)
    push_cast at hu1
    have h4 : y ^ m * δ y ^ (r + 2) ∈ I := (Ideal.unit_mul_mem_iff_mem I hu1).mp h2
    have h6 := ih (r + 2) h4
    rwa [show r + 2 + 2 * m = r + 2 * (m + 1) by ring] at h6

/- English proof (translation)
Establish `e` using `h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)`. Simplify using `using e`.
-/
theorem pow_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by
  have e := h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)
  simpa using e

/- English proof (translation)
Establish `hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx`. Establish `hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x)`. Take `⟨k, hk⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m))`.

Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]` and apply the resulting hypothesis. Use `Ideal.pow_mem_pow hj k` as an intermediate fact. Rewrite `this` using `[hk, Ideal.zero_eq_bot, Ideal.mem_bot]`. Then use the resulting hypothesis. Take `⟨n, hn⟩` from `hnil`. Rewrite `hn` using `[← map_pow]`.

Take `⟨⟨s, hs⟩, hsx⟩` from `(IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn`. Establish `hs' : s ∉ m` using `hs`. Establish `hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A)`. Rewrite using `[Ideal.mem_bot]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A)`. Introduce `z hz`. Rewrite `hz`, the goal using `[Ideal.mem_bot]`. Rewrite using `[hz, h.der_zero]`. Establish `hd` using `h.pow_mem ⊥ hb hu hsx0`.

Rewrite `hd` using `[Ideal.mem_bot]`. Establish `hdm : δ (s * x) ∈ m` using `hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)`. Rewrite `hdm` using `[h.mul]`. Establish `hxs : x * δ s ∈ m` using `m.mul_mem_right _ hx`. Establish `hsd : s * δ x ∈ m`.

Use `m.sub_mem hdm hxs` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `(hm.isPrime.mem_or_mem hsd).resolve_left hs'`.
-/
theorem mem_max [IsArtinianRing A] (h : IsDer δ) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A)) (m : Ideal A)
    [hm : m.IsMaximal] {x : A} (hx : x ∈ m) : δ x ∈ m := by

  have hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x) := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)
    refine ⟨k, ?_⟩
    have hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m)) := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    have := Ideal.pow_mem_pow hj k
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn
  have hs' : s ∉ m := hs

  have hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A) := by
    rw [Ideal.mem_bot]
    calc (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by ring
      _ = 0 := by simp only at hsx; rw [hsx, mul_zero]
  have hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A) := by
    intro z hz
    rw [Ideal.mem_bot] at hz ⊢
    rw [hz, h.der_zero]
  have hd := h.pow_mem ⊥ hb hu hsx0
  rw [Ideal.mem_bot] at hd
  have hdm : δ (s * x) ∈ m := hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)
  rw [h.mul] at hdm
  have hxs : x * δ s ∈ m := m.mul_mem_right _ hx
  have hsd : s * δ x ∈ m := by
    have := m.sub_mem hdm hxs
    rwa [add_sub_cancel_right] at this
  exact (hm.isPrime.mem_or_mem hsd).resolve_left hs'

/- English proof (translation)
Set `s` to `Function.surjInv (Ideal.Quotient.mk_surjective (I := I))`. Establish `hs : ∀ q, Ideal.Quotient.mk I (s q) = q` using `Function.surjInv_eq _`. Establish `key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x)`. Introduce `x`. Rewrite using `[Ideal.Quotient.eq, ← h.der_sub]`.

Conclude with `hI _ (Ideal.Quotient.eq.mp (hs _))`. Use `⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite using `[← map_add, key, key, key, h.add, map_add]`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite using `[← map_mul, key, key, key, h.mul, map_add, map_mul, map_mul]`.
-/
theorem quot (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) :
    ∃ δ' : A ⧸ I → A ⧸ I, IsDer δ' ∧ ∀ x, δ' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (δ x) := by
  classical
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  have key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x) := by
    intro x
    rw [Ideal.Quotient.eq, ← h.der_sub]
    exact hI _ (Ideal.Quotient.eq.mp (hs _))
  refine ⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add, key, key, key, h.add, map_add]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, key, key, h.mul, map_add, map_mul, map_mul]

/- English proof (translation)
Establish `d1 : d 1 = 0`. Establish `e` using `hmul 1 1`. Simplify using `only [mul_one, map_one, one_mul] at e`. Take the linear combination `-e`. Establish `d0 : d 0 = 0`.

Establish `e` using `hadd 0 0`. Simplify using `only [add_zero] at e`. Take the linear combination `-e`. Apply the tactic sequence `let ψ : A →+* TrivSqZeroExt B B := { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a) map_one' := by ext <;> simp [d1] map_mul' := fun x y => by`. Use `ext`.

Simplify using the standard rewrite rules. Simplify using `[hmul, TrivSqZeroExt.snd_mul]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `map_zero' := by ext <;> simp [d0]`. Use the proof step `map_add' := fun x y => by`.

Use `ext`. Simplify using the standard rewrite rules. Simplify using `[hadd] }`. Establish `hψ : ∀ s : S, IsUnit (ψ s)`. Introduce `s`.

Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify `IsLocalization.map_units B s` using `[ψ]`. Set `φ : B →+* TrivSqZeroExt B B` to `IsLocalization.lift hψ`. Establish `hφ : ∀ a, φ (algebraMap A B a) = ψ a` using `IsLocalization.lift_eq hψ`. Set `fst : TrivSqZeroExt B B →+* B` to `{ toFun := TrivSqZeroExt.fst map_one' := rfl map_mul' := fun x y => TrivSqZeroExt.fst_mul x y map_zero' := rfl map_add' := fun x y => rfl }`.

Establish `hfst : ∀ x, (φ x).fst = x`. Establish `e : fst.comp φ = RingHom.id B`. Apply `IsLocalization.ringHom_ext S` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply, hφ]`.

Use `show TrivSqZeroExt.fst (ψ a) = _`. Simplify using `[ψ]`. Introduce `x`. Conclude with `congrArg (fun f : B →+* B => f x) e`. Use `⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩` and prove the remaining obligations.

Simplify using `only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ofLoc {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by
  have d1 : d 1 = 0 := by
    have e := hmul 1 1
    simp only [mul_one, map_one, one_mul] at e
    linear_combination -e
  have d0 : d 0 = 0 := by
    have e := hadd 0 0
    simp only [add_zero] at e
    linear_combination -e

  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a)
      map_one' := by ext <;> simp [d1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul, TrivSqZeroExt.snd_mul]; ring
      map_zero' := by ext <;> simp [d0]
      map_add' := fun x y => by
        ext
        · simp
        · simp [hadd] }
  have hψ : ∀ s : S, IsUnit (ψ s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [ψ] using IsLocalization.map_units B s
  let φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hψ
  have hφ : ∀ a, φ (algebraMap A B a) = ψ a := IsLocalization.lift_eq hψ
  let fst : TrivSqZeroExt B B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun x y => TrivSqZeroExt.fst_mul x y
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hfst : ∀ x, (φ x).fst = x := by
    have e : fst.comp φ = RingHom.id B := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ]
      show TrivSqZeroExt.fst (ψ a) = _
      simp [ψ]
    intro x
    exact congrArg (fun f : B →+* B => f x) e
  refine ⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩
  simp only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]
  ring

end IsDer

end Formalism.L2.Pj.GenericSectionMinimum
