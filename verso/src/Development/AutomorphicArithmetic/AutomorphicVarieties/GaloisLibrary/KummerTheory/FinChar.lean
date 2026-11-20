import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Set `f : 𝓞 K →+* Ω` to `(algebraMap K Ω).comp (algebraMap (𝓞 K) K)`. Establish `hf : Function.Injective f` using `(algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)`. Set `e : 𝓞 K ≃+* f.range` to `RingEquiv.ofBijective f.rangeRestrict ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩`. Set `I : Ideal f.range` to `v.asIdeal.map e`. Establish `hI : I ≠ ⊤` using `by haveI : (v.asIdeal.map e).IsPrime := Ideal.map_isPrime_of_equiv e`.

Conclude with `Ideal.IsPrime.ne_top this`. Take `⟨V, hRV, hV⟩` from `Ideal.image_subset_nonunits_valuationSubring I hI`. Establish `hlt : ∀ y ∈ v.asIdeal, V.valuation (f y) < 1`. Introduce `y hy`. Establish `h1 : f y ∈ V.nonunits` using `hV ⟨e y, Ideal.mem_map_of_mem e hy, rfl⟩`.

Conclude with `(ValuationSubring.mem_nonunits_iff V).1 h1`. Establish `hle : ∀ y : 𝓞 K, V.valuation (f y) ≤ 1`. Introduce `y`. Conclude with `(ValuationSubring.valuation_le_one_iff V _).2 (hRV (RingHom.mem_range_self f y))`. Use `⟨V, fun x => ⟨fun hx => ?_, fun hx => hlt x hx⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hxv`. Take `⟨r, y, hy, hry⟩` from `v.isMaximal.exists_inv hxv`. Establish `h2 : V.valuation (f (r * x)) < 1`. Rewrite using `[map_mul, Valuation.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle r)) hx`.

Establish `h3 : V.valuation (f (r * x + y)) < 1`. Rewrite using `[map_add]`. Conclude with `Valuation.map_add_lt _ h2 (hlt y hy)`. Rewrite `h3` using `[hry, map_one, Valuation.map_one]`. Conclude with `lt_irrefl _ h3`.
-/
private theorem exists_valuationSubring_isPlaceOver (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ A : ValuationSubring Ω, IsPlaceOver A v := by
  let f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let e : 𝓞 K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := v.asIdeal.map e
  have hI : I ≠ ⊤ := by
    haveI : (v.asIdeal.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    exact Ideal.IsPrime.ne_top this
  obtain ⟨V, hRV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hlt : ∀ y ∈ v.asIdeal, V.valuation (f y) < 1 := by
    intro y hy
    have h1 : f y ∈ V.nonunits := hV ⟨e y, Ideal.mem_map_of_mem e hy, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).1 h1
  have hle : ∀ y : 𝓞 K, V.valuation (f y) ≤ 1 := by
    intro y
    exact (ValuationSubring.valuation_le_one_iff V _).2 (hRV (RingHom.mem_range_self f y))
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hlt x hx⟩⟩
  by_contra hxv
  obtain ⟨r, y, hy, hry⟩ := v.isMaximal.exists_inv hxv
  have h2 : V.valuation (f (r * x)) < 1 := by
    rw [map_mul, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle r)) hx
  have h3 : V.valuation (f (r * x + y)) < 1 := by
    rw [map_add]
    exact Valuation.map_add_lt _ h2 (hlt y hy)
  rw [hry, map_one, Valuation.map_one] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Establish `h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN` after adjusting the coercions. Use `(Ideal.finite_factors h0).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Conclude with `Ideal.dvd_span_singleton.2 hv`.
-/
private theorem finite_above_of_ne_zero (K : Type) [Field K] [NumberField K] (N : ℕ) (hN : N ≠ 0) :
    (Above K N).Finite := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ n N ζ hn hN hζ`. Use `haveI : NeZero n := ⟨hn⟩`. Set `ζΩ` to `algebraMap K Ω ζ`. Establish `hζΩ : IsPrimitiveRoot ζΩ n` using `hζ.map_of_injective (algebraMap K Ω).injective`. Establish `hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x` using `fun g x => AlgEquiv.commutes g x`.

Establish `hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val`. Introduce `g`. Rewrite using `[hfix g ζ]`. Break down `Nat.lt_or_ge 1 n with h1 | h1` into its components or cases. Rewrite using `[ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]`.

Establish `hn1 : n = 1` using `by omega`. Substitute `hn1` using the available equality. Establish `: ζΩ = 1` using `IsPrimitiveRoot.one_right_iff.1 hζΩ`. Use `show ζΩ = ζΩ ^ _`. Rewrite using `[this, one_pow]`.

Establish `key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F` using `K) A, φ g = 0}, ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above K N) n ∧ β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by`. Introduce and unpack `φ ⟨hlc, hadd, hine⟩`. Take `⟨β, a, hβ, hg⟩` from `radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc (fun g h => by rw [hadd, one_mul])`. Use `⟨β, a, ?_, hβ, hg⟩` and prove the remaining obligations. Introduce `v hv`.

Take `⟨A, hA⟩` from `exists_valuationSubring_isPlaceOver K Ω v`. Establish `hnot : ¬ A.valuation (N : Ω) < 1` using `fun h => hv (((placeDict K Ω).2.2.2 A v N hA).1 h)`. Conclude with `dvdOfIne K Ω n A v β a hA hβ (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])`. Use `choose! β a ha hβ hg using key`. Use `haveI hQ : Finite (↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) := by`.

Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[cardSel K _ n hn, cardSUnit K _ n (finite_above_of_ne_zero K N hN)]`. Establish `h1 : Nat.card ↥(rootsOfUnity n K) ≠ 0` using `Nat.card_pos.ne'`. Establish `h2 : Nat.card {c : ClS (Above K N) // c ^ n = 1} ≠ 0` using `by haveI : Nonempty {c : ClS (Above K N) // c ^ n = 1} := ⟨⟨1, one_pow _⟩⟩`. Conclude with `Nat.card_pos.ne'`.

Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) h1) h2`. Rewrite using `[← Set.finite_coe_iff]`. Use `Finite.of_injective (β := ↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_` and prove the remaining obligations. Introduce and unpack `⟨φ, hφ⟩ ⟨ψ, hψ⟩ h`. Simplify using `only at h`.

Rewrite `h` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Take `⟨c, hc⟩` from `h`. Simplify using `only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc`. Establish `hcu : a φ * c ^ n = a ψ` using `by rw [hc, mul_inv_cancel_left]`. Establish `hne : ∀ θ ∈ _, β θ ≠ 0` using `fun θ hθ h0 => by`.

Use `hβ θ hθ` as an intermediate fact. Rewrite `this` using `[h0, zero_pow hn]`. Conclude with `(Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `hφ0` using `hne φ hφ`.

Establish `hcΩ : algebraMap K Ω (c : K) ≠ 0`. Rewrite using `[Ne, map_eq_zero]`. Conclude with `c.ne_zero`. Use `set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef`. Establish `hωn : ω ^ n = 1`.

Rewrite using `[hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]`. Use `push_cast`. Conclude with `div_self (by simp)`. Take `⟨i, -, hi⟩` from `hζΩ.eq_pow_of_pow_eq_one hωn`. Establish `hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K))`.

Rewrite using `[hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]`. Establish `hgω : g ω = ω`. Rewrite using `[← hi, map_pow]`. Conclude with `congrArg (· ^ i) (hfix g ζ)`. Establish `hω0 : ω ≠ 0`.

Rewrite using `[← hi]`. Conclude with `pow_ne_zero _ (hζΩ.ne_zero hn)`. Establish `e1` using `hg ψ hψ g`. Rewrite `e1` using `[hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix]`. Establish `e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val`.

Establish `h3` using `mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ)`. Apply `mul_right_cancel₀ h3` to reduce the goal to its premises. Take the linear combination `e1`. Conclude with `ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)`.
-/
theorem UpperTheory.V.Kum.finChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n N : ℕ) (ζ : K), n ≠ 0 → N ≠ 0 → IsPrimitiveRoot ζ n → {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}.Finite := by
  intro K Ω _ _ _ _ _ n N ζ hn hN hζ
  haveI : NeZero n := ⟨hn⟩
  let ζΩ := algebraMap K Ω ζ
  have hζΩ : IsPrimitiveRoot ζΩ n := hζ.map_of_injective (algebraMap K Ω).injective
  have hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x :=
    fun g x => AlgEquiv.commutes g x
  have hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val := by
    intro g
    rw [hfix g ζ]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
    · have hn1 : n = 1 := by omega
      subst hn1
      have : ζΩ = 1 := IsPrimitiveRoot.one_right_iff.1 hζΩ
      show ζΩ = ζΩ ^ _
      rw [this, one_pow]
  have key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0},
      ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above K N) n ∧ β ^ n = algebraMap K Ω a ∧
        ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by
    rintro φ ⟨hlc, hadd, hine⟩
    obtain ⟨β, a, hβ, hg⟩ := radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc
      (fun g h => by rw [hadd, one_mul])
    refine ⟨β, a, ?_, hβ, hg⟩
    intro v hv
    obtain ⟨A, hA⟩ := exists_valuationSubring_isPlaceOver K Ω v
    have hnot : ¬ A.valuation (N : Ω) < 1 := fun h => hv (((placeDict K Ω).2.2.2 A v N hA).1 h)
    exact dvdOfIne K Ω n A v β a hA hβ
      (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])
  choose! β a ha hβ hg using key
  haveI hQ : Finite (↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) := by
    apply Nat.finite_of_card_ne_zero
    rw [cardSel K _ n hn, cardSUnit K _ n (finite_above_of_ne_zero K N hN)]
    have h1 : Nat.card ↥(rootsOfUnity n K) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card {c : ClS (Above K N) // c ^ n = 1} ≠ 0 := by
      haveI : Nonempty {c : ClS (Above K N) // c ^ n = 1} := ⟨⟨1, one_pow _⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) h1) h2
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := ↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n))
    (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
  simp only at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hcu : a φ * c ^ n = a ψ := by rw [hc, mul_inv_cancel_left]
  have hne : ∀ θ ∈ _, β θ ≠ 0 := fun θ hθ h0 => by
    have := hβ θ hθ
    rw [h0, zero_pow hn] at this
    exact (Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))
  refine Subtype.ext (funext fun g => ?_)
  have hφ0 := hne φ hφ
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact c.ne_zero
  set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef
  have hωn : ω ^ n = 1 := by
    rw [hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]
    push_cast
    exact div_self (by simp)
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hωn
  have hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K)) := by
    rw [hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]
  have hgω : g ω = ω := by
    rw [← hi, map_pow]
    exact congrArg (· ^ i) (hfix g ζ)
  have hω0 : ω ≠ 0 := by
    rw [← hi]
    exact pow_ne_zero _ (hζΩ.ne_zero hn)
  have e1 := hg ψ hψ g
  rw [hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix] at e1
  have e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val := by
    have h3 := mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ)
    apply mul_right_cancel₀ h3
    linear_combination e1
  exact ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)
