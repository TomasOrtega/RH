import Mathlib

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ A t hN ht hp hfr`. Use `set p : Ideal A := Ideal.span {t} with hpdef`. Use `haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by`. Take `⟨a, ha, b, hb, hb0, h⟩` from `hfr z`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, by show z = a / b`.

Rewrite using `[← h, mul_div_cancel_right₀ _ hb0]⟩`. Set `V0 : Subalgebra A L` to `Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors`. Use `haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _`. Use `haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p`. Use `haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN`.

Establish `hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]`. Establish `ht0 : algebraMap A V0 t ≠ 0` using `fun h => ht (congrArg Subtype.val h)`. Establish `hnf : ¬ IsField V0`. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]`.

Conclude with `ht0`. Establish `hdvr : IsDiscreteValuationRing V0` using `((IsDiscreteValuationRing.TFAE V0 hnf).out 0 4).2 (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)`. Use `haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by`. Take `⟨a, ha, b, hb, hb0, h⟩` from `hfr z`. Conclude with `⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by show z = a / b`.

Rewrite using `[← h, mul_div_cancel_right₀ _ hb0]⟩`. Set `V : ValuationSubring L` to `{ V0.toSubring with mem_or_inv_mem' := fun x => by`. Break down `ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases. Conclude with `Or.inl (hy ▸ y.2)`. Conclude with `Or.inr (hy ▸ y.2) }`.

Establish `hA : ∀ a ∈ A, a ∈ V` using `fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)`. Use `⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax`. Introduce `s hs`. Conclude with `IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)`.

Introduce `f`. Take `⟨⟨x, y⟩, hxy⟩` from `IsLocalization.mk'_surjective p.primeCompl (show V0 from f)`. Use `⟨x, y, y.2, ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)` as an intermediate fact. Establish `hxy' : IsLocalization.mk' V0 x y = (show V0 from f)` using `hxy`.

Rewrite `this` using `[hxy', map_mul]`. Conclude with `this`. Establish `h` using `(RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2 (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)`. Conclude with `h`.
-/
theorem dvr_loc_principal_prime : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  intro L _ A t hN ht hp hfr
  set p : Ideal A := Ideal.span {t} with hpdef
  haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V0 : Subalgebra A L := Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _
  haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p
  haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN
  have hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A V0 t ≠ 0 := fun h => ht (congrArg Subtype.val h)
  have hnf : ¬ IsField V0 := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact ht0
  have hdvr : IsDiscreteValuationRing V0 :=
    ((IsDiscreteValuationRing.TFAE V0 hnf).out 0 4).2
      (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)
  haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V : ValuationSubring L :=
    { V0.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hA : ∀ a ∈ A, a ∈ V := fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)
  refine ⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  · intro s hs
    exact IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)
  · intro f
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective p.primeCompl (show V0 from f)
    refine ⟨x, y, y.2, ?_⟩
    have := congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)
    have hxy' : IsLocalization.mk' V0 x y = (show V0 from f) := hxy
    rw [hxy', map_mul] at this
    exact this
  · have h := (RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2
      (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)
    exact h

end GlobalTheory
