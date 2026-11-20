import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV

open Polynomial

namespace GlobalTheory.FrobOrbit

/- English proof (translation)
Establish `hd` using `FiniteField.X_pow_card_sub_X_natDegree_eq k hn`. Establish `hne : (X ^ n - X : k[X]) ≠ 0`. Introduce `h0`. Rewrite `hd` using `[h0, natDegree_zero]`. Use linear arithmetic over natural numbers and integers.

Use `card_le_degree_of_subset_roots (p := (X ^ n - X : k[X])) (Z := Z) (by` as an intermediate fact. Introduce `x hx`. Rewrite using `[mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hZ x hx, sub_self])`. Rewrite `this` using `[hd]`. Then use the resulting hypothesis.
-/
theorem card_le_of_pow_eq_self {k : Type} [Field k] {n : ℕ} (hn : 1 < n) (Z : Finset k)
    (hZ : ∀ x ∈ Z, x ^ n = x) : Z.card ≤ n := by
  have hd := FiniteField.X_pow_card_sub_X_natDegree_eq k hn
  have hne : (X ^ n - X : k[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd
    omega
  have := card_le_degree_of_subset_roots (p := (X ^ n - X : k[X])) (Z := Z) (by
    intro x hx
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hZ x hx, sub_self])
  rwa [hd] at this

/- English proof (translation)
Establish `h1 : 1 < p` using `hp.out.one_lt`. Establish `hfix : ∀ a, f a ^ p ^ h = f a` using `fun a => by`. Rewrite using `[← map_pow, ← hc, FiniteField.pow_card]`. Establish `himg : (Finset.univ.image f).card = p ^ h`. Rewrite using `[Finset.card_image_of_injective _ f.injective, Finset.card_univ, hc]`.

Establish `hlt : ∀ s t : ℕ, s < t → t < h → ¬ ∀ a, f a ^ p ^ s = f a ^ p ^ t`. Introduce `s t hst hth H`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hst`. Establish `hle` using `card_le_of_pow_eq_self (k := k) (n := p ^ (d + 1)) (Nat.one_lt_pow (Nat.succ_ne_zero d) h1) (Finset.univ.image f) (by`. Introduce `x hx`.

Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 hx`. Apply `(iterateFrobenius k p s).injective` to reduce the goal to its premises. Rewrite using `[iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, H a]`. Use `congr 2`. Use the proof step `omega)`.

Rewrite `hle` using `[himg]`. Use `(Nat.pow_le_pow_iff_right h1).1 hle` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hinj : ∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t`. Introduce `s t hs ht H`.

Break down `lt_trichotomy s t with hst | hst | hst` into its components or cases. Conclude with `absurd H (hlt s t hst ht)`. Conclude with `hst`. Conclude with `absurd (fun a => (H a).symm) (hlt t s hst hs)`. Use `⟨hfix, ?_, hinj, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `hx' : x ∉ Finset.univ.image f`. Introduce `hm`. Take `⟨a, -, ha⟩` from `Finset.mem_image.1 hm`.

Conclude with `hne ⟨a, ha⟩`. Establish `hle` using `card_le_of_pow_eq_self (k := k) (n := p ^ h) (Nat.one_lt_pow hh.ne' h1) (insert x (Finset.univ.image f)) (by`. Introduce `y hy`. Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Conclude with `hx`.

Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `hfix a)`. Rewrite `hle` using `[Finset.card_insert_of_notMem hx', himg]`. Use linear arithmetic over natural numbers and integers. Introduce `g haveI : CharP K p := RingHom.charP f f.injective p`.

Use `letI : Algebra (ZMod p) K := ZMod.algebra K p`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Set `toAlg : (K →+* k) → (K →ₐ[ZMod p] k)` to `fun φ => { φ with commutes' := fun r => congrArg (fun ψ : ZMod p →+* k => ψ r) (Subsingleton.elim (φ.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) k)) }`. Establish `toAlg_apply : ∀ φ a, toAlg φ a = φ a` using `fun _ _ => rfl`. Establish `hrank : Module.finrank (ZMod p) K = h`.

Use `Module.card_eq_pow_finrank (K := ZMod p) (V := K)` as an intermediate fact. Rewrite `this` using `[ZMod.card, hc]`. Conclude with `(Nat.pow_right_injective h1 this).symm`. Set `F : Fin h → (K →ₐ[ZMod p] k)` to `fun s => toAlg ((iterateFrobenius k p s.val).comp f)`. Establish `hF : ∀ s a, F s a = f a ^ p ^ s.val` using `fun s a => rfl`.

Establish `hFinj : Function.Injective F`. Introduce `s t hst`. Apply `Fin.ext` to reduce the goal to its premises. Apply `hinj _ _ s.2 t.2` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[← hF, ← hF, hst]`. Establish `hbij` using `hFinj.bijective_of_nat_card_le (by`. Use `card_algHom_le_finrank (ZMod p) K k` as an intermediate fact. Rewrite `this` using `[hrank]`. Simplify using `using this)`.

Take `⟨s, hs⟩` from `hbij.2 (toAlg g)`. Conclude with `⟨s.val, s.2, fun a => by rw [← hF, hs, toAlg_apply]⟩`.
-/
theorem field_case (K k : Type) [Field K] [Fintype K] [Field k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (f : K →+* k) (h : ℕ) (hh : 0 < h) (hc : Fintype.card K = p ^ h) :
    (∀ a, f a ^ p ^ h = f a) ∧ (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
    (∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t) ∧
    ∀ g : K →+* k, ∃ s : ℕ, s < h ∧ ∀ a, g a = f a ^ p ^ s := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  have hfix : ∀ a, f a ^ p ^ h = f a := fun a => by
    rw [← map_pow, ← hc, FiniteField.pow_card]
  have himg : (Finset.univ.image f).card = p ^ h := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, hc]
  have hlt : ∀ s t : ℕ, s < t → t < h → ¬ ∀ a, f a ^ p ^ s = f a ^ p ^ t := by
    intro s t hst hth H
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hst
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ (d + 1))
      (Nat.one_lt_pow (Nat.succ_ne_zero d) h1) (Finset.univ.image f) (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        apply (iterateFrobenius k p s).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, H a]
        congr 2
        omega)
    rw [himg] at hle
    have := (Nat.pow_le_pow_iff_right h1).1 hle
    omega
  have hinj : ∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t := by
    intro s t hs ht H
    rcases lt_trichotomy s t with hst | hst | hst
    · exact absurd H (hlt s t hst ht)
    · exact hst
    · exact absurd (fun a => (H a).symm) (hlt t s hst hs)
  refine ⟨hfix, ?_, hinj, ?_⟩
  · intro x hx
    by_contra hne
    have hx' : x ∉ Finset.univ.image f := by
      intro hm
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hm
      exact hne ⟨a, ha⟩
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ h)
      (Nat.one_lt_pow hh.ne' h1) (insert x (Finset.univ.image f)) (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
          exact hfix a)
    rw [Finset.card_insert_of_notMem hx', himg] at hle
    omega
  · intro g
    haveI : CharP K p := RingHom.charP f f.injective p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    let toAlg : (K →+* k) → (K →ₐ[ZMod p] k) := fun φ =>
      { φ with
        commutes' := fun r =>
          congrArg (fun ψ : ZMod p →+* k => ψ r)
            (Subsingleton.elim (φ.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) k)) }
    have toAlg_apply : ∀ φ a, toAlg φ a = φ a := fun _ _ => rfl
    have hrank : Module.finrank (ZMod p) K = h := by
      have := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
      rw [ZMod.card, hc] at this
      exact (Nat.pow_right_injective h1 this).symm
    let F : Fin h → (K →ₐ[ZMod p] k) := fun s => toAlg ((iterateFrobenius k p s.val).comp f)
    have hF : ∀ s a, F s a = f a ^ p ^ s.val := fun s a => rfl
    have hFinj : Function.Injective F := by
      intro s t hst
      apply Fin.ext
      apply hinj _ _ s.2 t.2
      intro a
      rw [← hF, ← hF, hst]
    have hbij := hFinj.bijective_of_nat_card_le (by
      have := card_algHom_le_finrank (ZMod p) K k
      rw [hrank] at this
      simpa using this)
    obtain ⟨s, hs⟩ := hbij.2 (toAlg g)
    exact ⟨s.val, s.2, fun a => by rw [← hF, hs, toAlg_apply]⟩

/- English proof (translation)
Introduce `R k _ _ p hp _ f h hh hc`. Use `haveI : NeZero h := ⟨hh.ne'⟩`. Use `haveI : Finite (R ⧸ RingHom.ker f) := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)`. Use `haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f`. Use `haveI : (RingHom.ker f).IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField _)`.

Use `letI : Field (R ⧸ RingHom.ker f) := Ideal.Quotient.field _`. Use `letI : Fintype (R ⧸ RingHom.ker f) := Fintype.ofFinite _`. Take `⟨hfix, hsurj, hinj, hall⟩` from `field_case (R ⧸ RingHom.ker f) k p (RingHom.kerLift f) h hh (by rw [← Nat.card_eq_fintype_card, hc])`. Establish `hmk : ∀ a, RingHom.kerLift f (Ideal.Quotient.mk _ a) = f a` using `RingHom.kerLift_mk f`. Establish `hfix' : ∀ a, f a ^ p ^ h = f a` using `fun a => by`.

Use `hfix (Ideal.Quotient.mk _ a)` as an intermediate fact. Conclude with `this`. Establish `hmod : ∀ (a : R) (n : ℕ), f a ^ p ^ (n % h) = f a ^ p ^ n`. Introduce `a n`. Establish `hm : ∀ m : ℕ, f a ^ p ^ (h * m) = f a`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix']`. Use `conv_rhs => rw [← Nat.div_add_mod n h, pow_add, pow_mul, hm]`.

Use `⟨fun x hx => ?_, fun s => (iterateFrobenius k p s.val).comp f, fun s a => rfl, fun s a => ?_, fun s t hst => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsurj x hx`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Conclude with `⟨b, ha⟩`. Express the relevant statement in the definitionally equal form `f a ^ p ^ (s + 1).val = (f a ^ p ^ s.val) ^ p`.

Establish `hv : (s + 1).val = (s.val + 1) % h`. Rewrite using `[ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]`. Rewrite using `[hv, hmod, pow_succ, pow_mul]`. Apply `ZMod.val_injective h` to reduce the goal to its premises. Apply `hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t)` to reduce the goal to its premises.

Introduce `a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Conclude with `congrArg (fun φ : R →+* k => φ b) hst`. Take `⟨s, hs, hgs⟩` from `hall (Ideal.Quotient.lift (RingHom.ker f) g (fun a ha => by rw [← hg] at ha; exact ha))`. Use `⟨(s : ZMod h), RingHom.ext fun a => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `f a ^ p ^ ((s : ZMod h)).val = g a`. Rewrite using `[ZMod.val_cast_of_lt hs]`. Conclude with `(hgs (Ideal.Quotient.mk _ a)).symm`. Introduce and unpack `⟨s, rfl⟩`. Use extensionality with `a`.

Rewrite using `[RingHom.mem_ker, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `f a ^ p ^ s.val = 0 ↔ f a = 0`. Conclude with `pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)`.
-/
theorem ringHom_ker_eq_iff_frobenius_twist :
    ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ),
      0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h →
      (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
      ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧
        (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧
        ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  intro R k _ _ p hp _ f h hh hc
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI : Finite (R ⧸ RingHom.ker f) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Fintype (R ⧸ RingHom.ker f) := Fintype.ofFinite _
  obtain ⟨hfix, hsurj, hinj, hall⟩ := field_case (R ⧸ RingHom.ker f) k p (RingHom.kerLift f) h hh
    (by rw [← Nat.card_eq_fintype_card, hc])
  have hmk : ∀ a, RingHom.kerLift f (Ideal.Quotient.mk _ a) = f a := RingHom.kerLift_mk f
  have hfix' : ∀ a, f a ^ p ^ h = f a := fun a => by
    have := hfix (Ideal.Quotient.mk _ a)
    exact this
  have hmod : ∀ (a : R) (n : ℕ), f a ^ p ^ (n % h) = f a ^ p ^ n := by
    intro a n
    have hm : ∀ m : ℕ, f a ^ p ^ (h * m) = f a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix']
    conv_rhs => rw [← Nat.div_add_mod n h, pow_add, pow_mul, hm]
  refine ⟨fun x hx => ?_, fun s => (iterateFrobenius k p s.val).comp f, fun s a => rfl,
    fun s a => ?_, fun s t hst => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := hsurj x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, ha⟩
  · change f a ^ p ^ (s + 1).val = (f a ^ p ^ s.val) ^ p
    have hv : (s + 1).val = (s.val + 1) % h := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [hv, hmod, pow_succ, pow_mul]
  · apply ZMod.val_injective h
    apply hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t)
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun φ : R →+* k => φ b) hst
  · obtain ⟨s, hs, hgs⟩ := hall (Ideal.Quotient.lift (RingHom.ker f) g
      (fun a ha => by rw [← hg] at ha; exact ha))
    refine ⟨(s : ZMod h), RingHom.ext fun a => ?_⟩
    change f a ^ p ^ ((s : ZMod h)).val = g a
    rw [ZMod.val_cast_of_lt hs]
    exact (hgs (Ideal.Quotient.mk _ a)).symm
  · rintro ⟨s, rfl⟩
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change f a ^ p ^ s.val = 0 ↔ f a = 0
    exact pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)

end GlobalTheory.FrobOrbit
