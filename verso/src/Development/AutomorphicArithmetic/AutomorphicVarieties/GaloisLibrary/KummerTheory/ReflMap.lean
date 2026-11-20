import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadXDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Set `f : E →* B ⧸ P` to `(QuotientGroup.mk' P).comp E.subtype`. Establish `hk : f.ker = P.subgroupOf E`. Use extensionality with `x`. Simplify using `[f, Subgroup.mem_subgroupOf]`. Establish `h1 : Nat.card (E ⧸ P.subgroupOf E) = Nat.card f.range`.

Rewrite using `[← hk]`. Conclude with `Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv`. Establish `hm : ∀ x, j x ∈ f.range`. Introduce `x`. Take `⟨b, hb, h⟩` from `hE x`.

Take `⟨e, he, p, hp, rfl⟩` from `Subgroup.mem_sup.1 hb`. Use `⟨⟨e, he⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hp, mul_one]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Conclude with `Subgroup.card_dvd_of_injective (j.codRestrict f.range hm) fun x y h => hj (congrArg Subtype.val h)`.
-/
private theorem card_parity_sign_length_of_eq {A B : Type} [Group A] [CommGroup B] (E P : Subgroup B) (j : A →* B ⧸ P)
    (hj : Function.Injective j) (hE : ∀ x, ∃ b ∈ E ⊔ P, j x = QuotientGroup.mk b) :
    Nat.card A ∣ Nat.card (E ⧸ P.subgroupOf E) := by
  let f : E →* B ⧸ P := (QuotientGroup.mk' P).comp E.subtype
  have hk : f.ker = P.subgroupOf E := by
    ext x
    simp [f, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (E ⧸ P.subgroupOf E) = Nat.card f.range := by
    rw [← hk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hm : ∀ x, j x ∈ f.range := by
    intro x
    obtain ⟨b, hb, h⟩ := hE x
    obtain ⟨e, he, p, hp, rfl⟩ := Subgroup.mem_sup.1 hb
    refine ⟨⟨e, he⟩, ?_⟩
    rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hp, mul_one]
    rfl
  rw [h1]
  exact Subgroup.card_dvd_of_injective (j.codRestrict f.range hm)
    fun x y h => hj (congrArg Subtype.val h)

/- English proof (translation)
Rewrite using `[ZMod.val_add, ← pow_add]`. Use `conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) n, pow_add, pow_mul, hζ, one_pow, mul_one]`.
-/
private theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (hζ : ζ ^ n = 1) (x y : ZMod n) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) n, pow_add, pow_mul, hζ, one_pow, mul_one]

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ hU hζ`. Take `⟨hex, huniq⟩` from `radXDual F Ω K U n N ζ hU hζ`. Establish `hn : n ≠ 0` using `NeZero.ne n`. Take `⟨hmul, -, hpow⟩` from `radClMul K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn`. Establish `hker` using `radClKer K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn`.

Establish `hbot : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥` using `by simp [clSub]`. Establish `hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n` using `hζ.map_of_injective (algebraMap K Ω).injective`. Establish `hex' : ∀ φ : XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β ∧ β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n` using `fun φ => hex φ.1 φ.2`. Use `choose β a hrad hβ hsel using hex'`. Establish `hwd : ∀ (φ : XDual N U (ZMod n) (ZMod n)) (β' : Ω) (a' : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β' → β' ^ n = algebraMap K Ω a' → ∃ c : Kˣ, a' = a φ * c ^ n`.

Introduce `φ β' a' h1 h2`. Take `⟨c, hc⟩` from `huniq φ.1 (β φ) β' (hrad φ) h1`. Use `⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩` and prove the remaining obligations. Rewrite using `[← h2, hc, mul_pow, hβ]`. Simplify using `[mul_comm]`.

Establish `hadd : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), ∃ c : Kˣ, a φ * a ψ = a (φ + ψ) * c ^ n`. Introduce `φ ψ`. Use `hwd (φ + ψ) (β φ * β ψ) _ ⟨mul_ne_zero (hrad φ).1 (hrad ψ).1, fun u => ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[map_mul, (hrad φ).2 u, (hrad ψ).2 u]`. Express the relevant statement in the definitionally equal form `_ = algebraMap K Ω ζ ^ (φ.1 u + ψ.1 u).val * _`.

Rewrite using `[pow_val_add hζ'.pow_eq_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_pow, hβ, hβ]`. Simplify using the standard rewrite rules. Establish `hmul' : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), radCl n (a (φ + ψ)) = radCl n (a φ) * radCl n (a ψ)`.

Introduce `φ ψ`. Take `⟨c, hc⟩` from `hadd φ ψ`. Establish `h` using `hmul _ (hsel φ) _ (hsel ψ)`. Rewrite `h` using `[← QuotientGroup.mk_mul, QuotientGroup.eq, hbot, Subgroup.mem_bot, inv_mul_eq_one, hc, hpow]`. Conclude with `h`.

Set `κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K))` to `AddMonoidHom.mk' (fun φ => Additive.ofMul (radCl n (a φ))) fun φ ψ => by rw [hmul']; rfl`. Establish `hκ : ∀ φ, κ φ = Additive.ofMul (radCl n (a φ))` using `fun _ => rfl`. Use `⟨κ, fun φ β' a' h1 h2 => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hwd φ β' a' h1 h2`. Rewrite using `[hκ, hpow]`.

Set `j : Multiplicative κ.ker →* Kˣ ⧸ powK K n` to `MonoidHom.mk' (fun x => QuotientGroup.mk (a (Multiplicative.toAdd x).1)) fun x y => by`. Take `⟨c, hc⟩` from `hadd (Multiplicative.toAdd x).1 (Multiplicative.toAdd y).1`. Establish `hc1 : (QuotientGroup.mk (c ^ n) : Kˣ ⧸ powK K n) = 1` using `(QuotientGroup.eq_one_iff _).2 ⟨c, rfl⟩`. Rewrite using `[← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul, hc1, mul_one]`. Both sides reduce to the same expression.

Establish `hj : ∀ x, j x = QuotientGroup.mk (a (Multiplicative.toAdd x).1)` using `fun _ => rfl`. Use `card_parity_sign_length_of_eq (A := Multiplicative κ.ker) _ _ j ?_ ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_one]`. Introduce `x hx`. Rewrite `hx` using `[hj, QuotientGroup.eq_one_iff]`.

Take `⟨c, hc⟩` from `hx`. Use `set φ := (Multiplicative.toAdd x).1 with hφ`. Establish `hc' : c ^ n = a φ` using `hc`. Establish `hc0 : algebraMap K Ω c ≠ 0` using `by simp`. Establish `h1 : (β φ / algebraMap K Ω c) ^ n = 1`.

Rewrite using `[div_pow, hβ, ← hc', Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hc0)]`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one h1`. Establish `h2 : β φ = algebraMap K Ω (ζ ^ i * c)`. Rewrite using `[map_mul, map_pow, hi, div_mul_cancel₀ _ hc0]`. Establish `h0 : φ = 0`.

Use `Subtype.ext (funext fun u => ?_)` and prove the remaining obligations. Establish `hu : u.1 ∈ galOf F K Ω` using `hU ▸ u.2`. Establish `h3 : u.1 (β φ) = β φ` using `by rw [h2]; exact hu _`. Rewrite `h3` using `[(hrad φ).2 u, mul_eq_right₀ (hrad φ).1]`. Establish `h4` using `hζ'.dvd_of_pow_eq_one _ h3`.

Conclude with `(ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h4 (ZMod.val_lt _))`. Conclude with `Multiplicative.toAdd.injective (Subtype.ext h0)`. Introduce `x`. Use `⟨_, (hker _ (hsel (Multiplicative.toAdd x).1)).1 ?_, hj x⟩` and prove the remaining obligations. Rewrite using `[hbot, Subgroup.mem_bot]`.

Conclude with `(Multiplicative.toAdd x).2`.
-/
theorem UpperTheory.V.Kum.reflMap :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K), U = galOf F K Ω → IsPrimitiveRoot ζ n → ∃ κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)),
    (∀ (φ : XDual N U (ZMod n) (ZMod n)) (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β → β ^ n = algebraMap K Ω a → κ φ = Additive.ofMul (radCl n a)) ∧
    Nat.card κ.ker ∣ Nat.card ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ⧸ (powK K n).subgroupOf ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ hU hζ
  obtain ⟨hex, huniq⟩ := radXDual F Ω K U n N ζ hU hζ
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨hmul, -, hpow⟩ := radClMul K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn
  have hker := radClKer K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn
  have hbot : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hex' : ∀ φ : XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β ∧
      β ^ n = algebraMap K Ω a ∧ a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := fun φ => hex φ.1 φ.2
  choose β a hrad hβ hsel using hex'
  have hwd : ∀ (φ : XDual N U (ZMod n) (ZMod n)) (β' : Ω) (a' : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1 β' →
      β' ^ n = algebraMap K Ω a' → ∃ c : Kˣ, a' = a φ * c ^ n := by
    intro φ β' a' h1 h2
    obtain ⟨c, hc⟩ := huniq φ.1 (β φ) β' (hrad φ) h1
    refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
    rw [← h2, hc, mul_pow, hβ]
    simp [mul_comm]
  have hadd : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), ∃ c : Kˣ, a φ * a ψ = a (φ + ψ) * c ^ n := by
    intro φ ψ
    refine hwd (φ + ψ) (β φ * β ψ) _ ⟨mul_ne_zero (hrad φ).1 (hrad ψ).1, fun u => ?_⟩ ?_
    · rw [map_mul, (hrad φ).2 u, (hrad ψ).2 u]
      change _ = algebraMap K Ω ζ ^ (φ.1 u + ψ.1 u).val * _
      rw [pow_val_add hζ'.pow_eq_one]
      ring
    · rw [mul_pow, hβ, hβ]
      simp
  have hmul' : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), radCl n (a (φ + ψ)) = radCl n (a φ) * radCl n (a ψ) := by
    intro φ ψ
    obtain ⟨c, hc⟩ := hadd φ ψ
    have h := hmul _ (hsel φ) _ (hsel ψ)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hbot, Subgroup.mem_bot, inv_mul_eq_one, hc, hpow] at h
    exact h
  let κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)) :=
    AddMonoidHom.mk' (fun φ => Additive.ofMul (radCl n (a φ))) fun φ ψ => by rw [hmul']; rfl
  have hκ : ∀ φ, κ φ = Additive.ofMul (radCl n (a φ)) := fun _ => rfl
  refine ⟨κ, fun φ β' a' h1 h2 => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hwd φ β' a' h1 h2
    rw [hκ, hpow]
  · let j : Multiplicative κ.ker →* Kˣ ⧸ powK K n :=
      MonoidHom.mk' (fun x => QuotientGroup.mk (a (Multiplicative.toAdd x).1)) fun x y => by
        obtain ⟨c, hc⟩ := hadd (Multiplicative.toAdd x).1 (Multiplicative.toAdd y).1
        have hc1 : (QuotientGroup.mk (c ^ n) : Kˣ ⧸ powK K n) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨c, rfl⟩
        rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul, hc1, mul_one]
        rfl
    have hj : ∀ x, j x = QuotientGroup.mk (a (Multiplicative.toAdd x).1) := fun _ => rfl
    refine card_parity_sign_length_of_eq (A := Multiplicative κ.ker) _ _ j ?_ ?_
    · rw [injective_iff_map_eq_one]
      intro x hx
      rw [hj, QuotientGroup.eq_one_iff] at hx
      obtain ⟨c, hc⟩ := hx
      set φ := (Multiplicative.toAdd x).1 with hφ
      have hc' : c ^ n = a φ := hc
      have hc0 : algebraMap K Ω c ≠ 0 := by simp
      have h1 : (β φ / algebraMap K Ω c) ^ n = 1 := by
        rw [div_pow, hβ, ← hc', Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hc0)]
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
      have h2 : β φ = algebraMap K Ω (ζ ^ i * c) := by
        rw [map_mul, map_pow, hi, div_mul_cancel₀ _ hc0]
      have h0 : φ = 0 := by
        refine Subtype.ext (funext fun u => ?_)
        have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
        have h3 : u.1 (β φ) = β φ := by rw [h2]; exact hu _
        rw [(hrad φ).2 u, mul_eq_right₀ (hrad φ).1] at h3
        have h4 := hζ'.dvd_of_pow_eq_one _ h3
        exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h4 (ZMod.val_lt _))
      exact Multiplicative.toAdd.injective (Subtype.ext h0)
    · intro x
      refine ⟨_, (hker _ (hsel (Multiplicative.toAdd x).1)).1 ?_, hj x⟩
      rw [hbot, Subgroup.mem_bot]
      exact (Multiplicative.toAdd x).2
