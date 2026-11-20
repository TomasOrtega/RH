import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.PartBOfDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.R

namespace Cc2

/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Use `letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _`. Establish `: Finite (𝓞 K ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)`. Rewrite using `[show normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) from Nat.card_eq_fintype_card]`.

Assume the negation of the conclusion as `hlt`. Use `FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `Ideal.Quotient.eq.2 (h x)` as an intermediate fact. Rewrite `this` using `[map_pow]`.

Rewrite using `[eval_sub, eval_pow, eval_X, ← this, sub_self]`. Rewrite using `[FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]`. Conclude with `not_le.1 hlt`.
-/
theorem norm_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  rw [show normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) from Nat.card_eq_fintype_card]
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]
    exact not_le.1 hlt

/- English proof (translation)
Establish `hi : IsIntegral ℤ (algebraMap M Ω x)` using `x.isIntegral_coe.algebraMap`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))`. Rewrite using `[A.valuation_le_one_iff, ← hy]`. Conclude with `y.2`.
-/
theorem int_le {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] (A : ValuationSubring Ω) (x : 𝓞 M) :
    A.valuation (algebraMap M Ω x) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap M Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `h (AlgEquiv.ext fun x => ?_)` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 M) x`. Rewrite using `[map_div₀]`.

Conclude with `congrArg₂ (· / ·) (hn a) (hn b)`.
-/
theorem moved {K M : Type} [Field K] [Field M] [NumberField M] [Algebra K M] (τ : M ≃ₐ[K] M) (h : τ ≠ 1) :
    ∃ θ : 𝓞 M, τ θ ≠ θ := by
  by_contra hn
  push Not at hn
  refine h (AlgEquiv.ext fun x => ?_)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  rw [map_div₀]
  exact congrArg₂ (· / ·) (hn a) (hn b)

end Cc2

open Cc2

/- English proof (translation)
Introduce `K M _ _ _ _ _ _ _ _ hl`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Use `haveI := Fact.mk hl`. Use `haveI : NeZero (Module.finrank K M) := ⟨hl.ne_zero⟩`. Take `⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`.

Set `Ω` to `AlgebraicClosure M`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩`. Take `⟨art, ha⟩` from `GlobalTheory.globalArtinReciprocity_holds K Ω`. Set `r : G K Ω →* (M ≃ₐ[K] M)` to `AlgEquiv.restrictNormalHom M`. Establish `hr : ∀ s (x : M), algebraMap M Ω (r s x) = s (algebraMap M Ω x)` using `fun s x => AlgEquiv.restrictNormal_commutes s M x`.

Set `e : (M ≃ₐ[K] M) ≃* rootsOfUnity (Module.finrank K M) (Qbar 2)` to `mulEquivOfPrimeCardEq (IsGalois.card_aut_eq_finrank K M) (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _)`. Set `δ : G K Ω →* (Qbar 2)ˣ` to `((rootsOfUnity _ _).subtype.comp e.toMonoidHom).comp r`. Establish `hδ : ∀ s, δ s = 1 ↔ r s = 1` using `fun s => ⟨fun h => e.injective (Subtype.ext (h.trans (by rw [map_one]; rfl))), fun h => by simp [δ, h]⟩`. Use `choose θ hθ using fun τ : {τ : M ≃ₐ[K] M // τ ≠ 1} => moved τ.1 τ.2`. Establish `hc : Continuous δ`.

Use `continuous_of_isOpen_ker' δ (Subgroup.isOpen_mono (H₁ := ⨅ τ, MulAction.stabilizer (G K Ω) (algebraMap M Ω (θ τ))) (fun s hs => (hδ s).2 ?_) ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hθ ⟨r s, h⟩ ((algebraMap M Ω).injective ((hr s _).trans (Subgroup.mem_iInf.1 hs ⟨r s, h⟩)))`. Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite fun τ => stabilizer_isOpen_of_isIntegral _`.

Take `⟨η, ⟨ho, hL⟩, -⟩` from `exists_unique_hchar_of_finite_order ha ι δ hc hl.pos (MonoidHom.ext fun s => (e (r s)).2)`. Establish `hv1 : ∀ v, η.val v ^ Module.finrank K M = 1` using `fun v => by`. Rewrite using `[← Pb2.val_pow, show η ^ Module.finrank K M = 1 from ho]`. Both sides reduce to the same expression. Establish `ev : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ τ : {τ : M ≃ₐ[K] M // τ ≠ 1}, RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ ∉ w.asIdeal` using `Filter.eventually_all.2 fun τ => by`.

Establish `h0 : Ideal.span {RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_eq_zero]`. Conclude with `fun h => hθ τ (congrArg (fun x : 𝓞 M => (x : M)) h)`. Conclude with `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (not_not.1 hv)`. Establish `key : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, η.UnrAt (w.under (𝓞 K)) ∧ (η.val (w.under (𝓞 K)) = 1 ↔ normV w = normV (w.under (𝓞 K))) ∧ (normV w = normV (w.under (𝓞 K)) ∨ normV w = normV (w.under (𝓞 K)) ^ Module.finrank K M)` using `by filter_upwards [ev, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (decomp K M hl)] with w hw hd`.

Establish `hd'` using `hd.imp (fun h => h.2 w rfl) fun h => h.2 w rfl`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hv : IsPlaceOver A (w.under (𝓞 K))` using `fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K M Ω]`. Conclude with `hA (algebraMap (𝓞 K) (𝓞 M) x)`.

Establish `hur : ∀ s ∈ Ine (F` using `K) A, δ s = 1 := fun s hs => (hδ s).2 (by`. Assume the negation of the conclusion as `h`. Use `hw ⟨r s, h⟩ ((hA _).1 ?_)` and prove the remaining obligations. Use `hs.2 _ (int_le A (θ ⟨r s, h⟩))` as an intermediate fact. Rewrite `this` using `[← hr, ← map_sub]`.

Conclude with `this)`. Take `⟨φ, hφ⟩` from `exists_isFrob hv`. Establish `hu` using `(hL.unr_iff ha (Or.inr rfl) hv).1 hur`. Establish `h3` using `hL.frob_unr ha (Or.inr rfl) hu hv hφ`. Establish `h4 : η.val (w.under (𝓞 K)) = 1 ↔ δ φ = 1`.

Rewrite using `[← Units.val_eq_one, ← Units.val_eq_one (a := δ φ), h3, inv_eq_one, map_eq_one_iff _ ι.symm.injective]`. Establish `hq : 1 < normV (w.under (𝓞 K))` using `NumberField.HeightOneSpectrum.one_lt_absNorm _`. Use `⟨hu, h4.trans ⟨fun h => ?_, fun h => ?_⟩, hd'⟩` and prove the remaining obligations. Use `hd'.resolve_right fun h' => ?_` and prove the remaining obligations. Establish `hle : normV w ≤ normV (w.under (𝓞 K))` using `norm_le w hq fun x => by`.

Establish `h2` using `hφ.2 _ (int_le A x)`. Rewrite `h2` using `[← hr, (hδ φ).1 h]`. Rewrite using `[← hA]`. Simplify using `using h2`. Use `Nat.pow_lt_pow_right hq hl.one_lt` as an intermediate fact.

Rewrite `this` using `[pow_one, ← h']`. Use linear arithmetic over natural numbers and integers. Take `⟨ψ, hψ⟩` from `exists_isFrob hA`. Establish `hψ' : IsFrob (F` using `K) A (normV (w.under (𝓞 K))) (res K Ω M ψ) := by`. Rewrite using `[← h]`.

Conclude with `⟨hψ.1, hψ.2⟩`. Establish `h1` using `hur _ (inv_mul_mem_Ine_of_isFrob hφ hψ')`. Establish `h2 : δ (res K Ω M ψ) = 1` using `(hδ _).2 (AlgEquiv.ext fun x => (algebraMap M Ω).injective ((hr _ x).trans (ψ.commutes x)))`. Rewrite `h1` using `[map_mul, h2, mul_one, map_inv, inv_eq_one]`. Then use the resulting hypothesis. Use `⟨η, ⟨?_, ho, ?_⟩, key.mono fun w hw => ⟨hw.1, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `rfl haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (IsGalois.card_aut_eq_finrank K M ▸ hl.one_lt)`. Take `⟨τ, hτ⟩` from `exists_ne (1 : M ≃ₐ[K] M)`. Take `⟨s, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective Ω τ`. Use `hτ ((hδ s).1 (Units.ext ?_))` and prove the remaining obligations. Take `⟨x, hx⟩` from `ha.quot.surjective (toAb K Ω s)`.

Rewrite using `[hL x s hx, infPow_zero, lPow_zero]`. Simplify using the standard rewrite rules. Use `filter_upwards [key] with w hw f hf`. Break down `hw.2.2 with h | h` into its components or cases. Rewrite using `[hw.2.1.2 h, one_pow]`.

Rewrite using `[show f = Module.finrank K M from Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm _) (hf.symm.trans h), hv1]`. Distinguish the cases in `h : η.val (w.under (𝓞 K)) = 1`. Conclude with `Or.inl (hw.2.1.1 h)`. Use `Or.inr ?_` and prove the remaining obligations. Rewrite using `[← orderOf_eq_prime (hv1 _) h]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem classChar2 : ClassChar := by
  intro K M _ _ _ _ _ _ _ _ hl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fact.mk hl
  haveI : NeZero (Module.finrank K M) := ⟨hl.ne_zero⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  let Ω := AlgebraicClosure M
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  let r : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hr : ∀ s (x : M), algebraMap M Ω (r s x) = s (algebraMap M Ω x) := fun s x => AlgEquiv.restrictNormal_commutes s M x
  let e : (M ≃ₐ[K] M) ≃* rootsOfUnity (Module.finrank K M) (Qbar 2) :=
    mulEquivOfPrimeCardEq (IsGalois.card_aut_eq_finrank K M) (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _)
  let δ : G K Ω →* (Qbar 2)ˣ := ((rootsOfUnity _ _).subtype.comp e.toMonoidHom).comp r
  have hδ : ∀ s, δ s = 1 ↔ r s = 1 := fun s =>
    ⟨fun h => e.injective (Subtype.ext (h.trans (by rw [map_one]; rfl))), fun h => by simp [δ, h]⟩
  choose θ hθ using fun τ : {τ : M ≃ₐ[K] M // τ ≠ 1} => moved τ.1 τ.2
  have hc : Continuous δ := by
    refine continuous_of_isOpen_ker' δ (Subgroup.isOpen_mono
      (H₁ := ⨅ τ, MulAction.stabilizer (G K Ω) (algebraMap M Ω (θ τ))) (fun s hs => (hδ s).2 ?_) ?_)
    · by_contra h
      exact hθ ⟨r s, h⟩ ((algebraMap M Ω).injective ((hr s _).trans (Subgroup.mem_iInf.1 hs ⟨r s, h⟩)))
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun τ => stabilizer_isOpen_of_isIntegral _
  obtain ⟨η, ⟨ho, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι δ hc hl.pos (MonoidHom.ext fun s => (e (r s)).2)
  have hv1 : ∀ v, η.val v ^ Module.finrank K M = 1 := fun v => by
    rw [← Pb2.val_pow, show η ^ Module.finrank K M = 1 from ho]; rfl
  have ev : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      ∀ τ : {τ : M ≃ₐ[K] M // τ ≠ 1}, RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ ∉ w.asIdeal :=
    Filter.eventually_all.2 fun τ => by
      have h0 : Ideal.span {RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_eq_zero]
        exact fun h => hθ τ (congrArg (fun x : 𝓞 M => (x : M)) h)
      exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (not_not.1 hv)
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, η.UnrAt (w.under (𝓞 K)) ∧
      (η.val (w.under (𝓞 K)) = 1 ↔ normV w = normV (w.under (𝓞 K))) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ normV w = normV (w.under (𝓞 K)) ^ Module.finrank K M) := by
    filter_upwards [ev, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (decomp K M hl)] with w hw hd
    have hd' := hd.imp (fun h => h.2 w rfl) fun h => h.2 w rfl
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hur : ∀ s ∈ Ine (F := K) A, δ s = 1 := fun s hs => (hδ s).2 (by
      by_contra h
      refine hw ⟨r s, h⟩ ((hA _).1 ?_)
      have := hs.2 _ (int_le A (θ ⟨r s, h⟩))
      rw [← hr, ← map_sub] at this
      exact this)
    obtain ⟨φ, hφ⟩ := exists_isFrob hv
    have hu := (hL.unr_iff ha (Or.inr rfl) hv).1 hur
    have h3 := hL.frob_unr ha (Or.inr rfl) hu hv hφ
    have h4 : η.val (w.under (𝓞 K)) = 1 ↔ δ φ = 1 := by
      rw [← Units.val_eq_one, ← Units.val_eq_one (a := δ φ), h3, inv_eq_one, map_eq_one_iff _ ι.symm.injective]
    have hq : 1 < normV (w.under (𝓞 K)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
    refine ⟨hu, h4.trans ⟨fun h => ?_, fun h => ?_⟩, hd'⟩
    · refine hd'.resolve_right fun h' => ?_
      have hle : normV w ≤ normV (w.under (𝓞 K)) := norm_le w hq fun x => by
        have h2 := hφ.2 _ (int_le A x)
        rw [← hr, (hδ φ).1 h] at h2
        rw [← hA]
        simpa using h2
      have := Nat.pow_lt_pow_right hq hl.one_lt
      rw [pow_one, ← h'] at this
      omega
    · obtain ⟨ψ, hψ⟩ := exists_isFrob hA
      have hψ' : IsFrob (F := K) A (normV (w.under (𝓞 K))) (res K Ω M ψ) := by
        rw [← h]
        exact ⟨hψ.1, hψ.2⟩
      have h1 := hur _ (inv_mul_mem_Ine_of_isFrob hφ hψ')
      have h2 : δ (res K Ω M ψ) = 1 := (hδ _).2 (AlgEquiv.ext fun x => (algebraMap M Ω).injective ((hr _ x).trans (ψ.commutes x)))
      rwa [map_mul, h2, mul_one, map_inv, inv_eq_one] at h1
  refine ⟨η, ⟨?_, ho, ?_⟩, key.mono fun w hw => ⟨hw.1, ?_⟩⟩
  · rintro rfl
    haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (IsGalois.card_aut_eq_finrank K M ▸ hl.one_lt)
    obtain ⟨τ, hτ⟩ := exists_ne (1 : M ≃ₐ[K] M)
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
    refine hτ ((hδ s).1 (Units.ext ?_))
    obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω s)
    rw [hL x s hx, infPow_zero, lPow_zero]
    simp
  · filter_upwards [key] with w hw f hf
    rcases hw.2.2 with h | h
    · rw [hw.2.1.2 h, one_pow]
    · rw [show f = Module.finrank K M from
        Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm _) (hf.symm.trans h), hv1]
  · by_cases h : η.val (w.under (𝓞 K)) = 1
    · exact Or.inl (hw.2.1.1 h)
    · refine Or.inr ?_
      rw [← orderOf_eq_prime (hv1 _) h]
      exact IsPrimitiveRoot.orderOf _

end UpperTheory.ConvolutionTheory.R
