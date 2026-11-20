import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Establish `hn : l.Prime` using `hl.out`. Establish `hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hn.ne_zero` after adjusting the coercions. Establish `hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal` using `inferInstance`.

Establish `hm : ∀ p : Above F l, p.1.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F)`. Introduce and unpack `⟨p, hp⟩`. Establish `hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal` using `hp`. Rewrite using `[IsDedekindDomain.mem_primesOverFinset_iff hp0]`. Use `p.isPrime` as an intermediate fact.

Use `⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `hp'`. Set `f : Above F l → IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F)` to `fun p => ⟨_, hm p⟩`. Establish `hf : Function.Injective f` using `fun p q h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))`.

Use `⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_coe]`. Conclude with `Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0`.
-/
private theorem above_card (F : Type) [Field F] [NumberField F] (l : ℕ) [hl : Fact l.Prime] :
    (Above F l).Finite ∧ Nat.card (Above F l) ≤ Module.finrank ℚ F := by
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  have hm : ∀ p : Above F l, p.1.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F) := by
    rintro ⟨p, hp⟩
    have hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal := hp
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  let f : Above F l → IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F) := fun p => ⟨_, hm p⟩
  have hf : Function.Injective f := fun p q h =>
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0

/- English proof (translation)
Introduce `E _ _ l hl`. Establish `hn : l.Prime` using `hl.out`. Use `haveI : NeZero l := ⟨hn.ne_zero⟩`. Take `⟨hfin, hcard⟩` from `above_card E l`. Establish `h` using `cardSel E (Above E l) l hn.ne_zero`.

Rewrite `h` using `[cardSUnit E (Above E l) l hfin]`. Establish `hsurj : Function.Surjective (QuotientGroup.mk : ClassGroup (𝓞 E) → ClS (Above E l))` using `QuotientGroup.mk_surjective`. Use `haveI : Finite (ClS (Above E l)) := Finite.of_surjective _ hsurj`. Use `haveI : Nonempty {c : ClS (Above E l) // c ^ l = 1} := ⟨⟨1, one_pow _⟩⟩`. Establish `h1 : Nat.card {c : ClS (Above E l) // c ^ l = 1} ≤ classNumber E`.

Use `(Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_` and prove the remaining obligations. Use `(Nat.card_le_card_of_surjective _ hsurj).trans ?_` and prove the remaining obligations. Rewrite using `[classNumber, Nat.card_eq_fintype_card]`. Establish `h2 : Nat.card (rootsOfUnity l E) ≤ l` using `card_rootsOfUnity E l`. Establish `h3` using `InfinitePlace.card_add_two_mul_card_eq_rank E`.

Establish `h4 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Use `⟨Nat.finite_of_card_ne_zero ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn.ne_zero) Nat.card_pos.ne') Nat.card_pos.ne'`. Rewrite using `[h]`.

Use `Nat.mul_le_mul ?_ h1` and prove the remaining obligations. Use `(Nat.mul_le_mul_left _ h2).trans ?_` and prove the remaining obligations. Rewrite using `[← pow_succ]`. Conclude with `Nat.pow_le_pow_right hn.pos (by omega)`.
-/
theorem UpperTheory.V.Odd.selCard :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Finite (SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l)) ∧ Nat.card (SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l)) ≤ l ^ (2 * Module.finrank ℚ E) * classNumber E := by
  intro E _ _ l hl
  have hn : l.Prime := hl.out
  haveI : NeZero l := ⟨hn.ne_zero⟩
  obtain ⟨hfin, hcard⟩ := above_card E l
  have h := cardSel E (Above E l) l hn.ne_zero
  rw [cardSUnit E (Above E l) l hfin] at h
  have hsurj : Function.Surjective (QuotientGroup.mk : ClassGroup (𝓞 E) → ClS (Above E l)) :=
    QuotientGroup.mk_surjective
  haveI : Finite (ClS (Above E l)) := Finite.of_surjective _ hsurj
  haveI : Nonempty {c : ClS (Above E l) // c ^ l = 1} := ⟨⟨1, one_pow _⟩⟩
  have h1 : Nat.card {c : ClS (Above E l) // c ^ l = 1} ≤ classNumber E := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_
    refine (Nat.card_le_card_of_surjective _ hsurj).trans ?_
    rw [classNumber, Nat.card_eq_fintype_card]
  have h2 : Nat.card (rootsOfUnity l E) ≤ l := card_rootsOfUnity E l
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h4 : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn.ne_zero) Nat.card_pos.ne') Nat.card_pos.ne'
  · rw [h]
    refine Nat.mul_le_mul ?_ h1
    refine (Nat.mul_le_mul_left _ h2).trans ?_
    rw [← pow_succ]
    exact Nat.pow_le_pow_right hn.pos (by omega)
