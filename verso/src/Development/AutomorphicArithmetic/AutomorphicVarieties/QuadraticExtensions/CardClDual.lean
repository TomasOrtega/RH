import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Use `⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩` and prove the remaining obligations. Use `show Nat.card (Module.Dual (ZMod l) V) ≤ _`. Rewrite using `[Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]`.
-/
private theorem cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
    [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
  refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
  show Nat.card (Module.Dual (ZMod l) V) ≤ _
  rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

/- English proof (translation)
Establish `hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c`. Introduce `p c n`. Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hm p 1 1`.

Rewrite `h` using `[mul_one]`. Simplify using `using h`. Consider the case `succ n ih => rw [pow_succ, hm, ih, succ_nsmul]`. Establish `h1 : ∀ p, θ p 1 = 0` using `fun p => by simpa using hpow p 1 0`. Establish `hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0`.

Introduce `v`. Express the relevant statement in the definitionally equal form `(Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1`. Take `⟨a, ha⟩` from `QuotientGroup.mk_surjective (Additive.toMul v)`. Rewrite using `[← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `⟨a, rfl⟩`.

Set `φ : P → A →* Multiplicative (ZMod l)` to `fun p => { toFun := fun a => Multiplicative.ofAdd (θ p a) map_one' := by show Multiplicative.ofAdd (θ p 1) = 1`. Rewrite using `[h1]`. Both sides reduce to the same expression. Use the proof step `map_mul' := fun a b => by show Multiplicative.ofAdd (θ p (a * b)) = _`. Rewrite using `[hm]`.

Use `rfl }`. Set `ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l)` to `fun p => QuotientGroup.lift _ (φ p) (by`. Introduce and unpack `_ ⟨c, rfl⟩`. Use `show Multiplicative.ofAdd (θ p (c ^ l)) = 1`. Rewrite using `[hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]`.

Use the proof step `rfl)`. Set `Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l)` to `fun p => AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _`. Rewrite using `[map_mul]`. Use the proof step `rfl)`. Establish `hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a` using `fun p a => rfl`.

Establish `hinj : Function.Injective Φ`. Introduce `p q h`. Apply `hθ` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Rewrite using `[← hΦ p a, ← hΦ q a, h]`.

Use `letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV`. Conclude with `CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _ ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range)) (M₁ := ZMod l)).comp hinj)`.
-/
private theorem cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
    (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
    CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
  have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
    intro p c n
    induction n with
    | zero =>
      have h := hm p 1 1
      rw [mul_one] at h
      simpa using h
    | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
  have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
  have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
    intro v
    change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  let φ : P → A →* Multiplicative (ZMod l) := fun p =>
    { toFun := fun a => Multiplicative.ofAdd (θ p a)
      map_one' := by
        show Multiplicative.ofAdd (θ p 1) = 1
        rw [h1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (θ p (a * b)) = _
        rw [hm]
        rfl }
  let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
    QuotientGroup.lift _ (φ p) (by
      rintro _ ⟨c, rfl⟩
      show Multiplicative.ofAdd (θ p (c ^ l)) = 1
      rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl)
  let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
      show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
      rw [map_mul]
      rfl)
  have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
  have hinj : Function.Injective Φ := by
    intro p q h
    apply hθ
    funext a
    rw [← hΦ p a, ← hΦ q a, h]
  letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
  exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
    ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
      (M₁ := ZMod l)).comp hinj)

/- English proof (translation)
Introduce `K _ _ l _ N`. Conclude with `cardLe_hom (ClassGroup (𝓞 K)) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1`.
-/
theorem UpperTheory.V.Two.cardClDual :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (N : ℕ), CardLe (ClDual K N (ZMod l) (ZMod l)) (Nat.card (ClassGroup (𝓞 K) ⧸ (powMonoidHom l : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)) := by
  intro K _ _ l _ N
  exact cardLe_hom (ClassGroup (𝓞 K)) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
