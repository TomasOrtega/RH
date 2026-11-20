import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `x` and use `by rw [IsScalarTower.algebraMap_apply ℚ F Ω] exact hA (algebraMap _ _ x)`.
-/
private theorem under_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {t : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A t) :
    IsPlaceOver A (t.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ F Ω]
  exact hA (algebraMap _ _ x)

/- English proof (translation)
The claim follows from `GlobalTheory.AboveL.mem_dec_congr A _ g fun _ => rfl`.
-/
private theorem res_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ g ∈ Dec (F := F) A :=
  GlobalTheory.AboveL.mem_dec_congr A _ g fun _ => rfl

/- English proof (translation)
Rewrite using `[mem_Ine, mem_Ine]`. Conclude with `Iff.rfl`.
-/
private theorem res_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Ine (F := ℚ) A ↔ g ∈ Ine (F := F) A := by
  rw [mem_Ine, mem_Ine]
  exact Iff.rfl

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Use `haveI hM : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible`. Establish `hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal`. Establish `h` using `Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv.symm (p := Ideal.span {(p : ℤ)})`. Rewrite `h` using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Then use the resulting hypothesis.

Establish `key : ∀ c : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ c.asIdeal → c.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)}` using `fun c hc => (hmax.eq_of_le c.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hc)).symm`. Conclude with `HeightOneSpectrum.ext ((key a ha).trans (key b hb).symm)`.
-/
private theorem eq_of_natCast_mem {p : ℕ} (hp : p.Prime) {a b : HeightOneSpectrum (𝓞 ℚ)}
    (ha : ((p : ℕ) : 𝓞 ℚ) ∈ a.asIdeal) (hb : ((p : ℕ) : 𝓞 ℚ) ∈ b.asIdeal) : a = b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal := by
    have h := Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv.symm (p := Ideal.span {(p : ℤ)})
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
  have key : ∀ c : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ c.asIdeal →
      c.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := fun c hc =>
    (hmax.eq_of_le c.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hc)).symm
  exact HeightOneSpectrum.ext ((key a ha).trans (key b hb).symm)

/- English proof (translation)
Establish `hne : Nat.card (𝓞 ℚ ⧸ u.asIdeal) ≠ 0`. Establish `h0` using `h.ne_zero`. Unfold `normV at h0`. Conclude with `h0`. Use `haveI : Finite (𝓞 ℚ ⧸ u.asIdeal) := Nat.finite_of_card_ne_zero hne`.

Use `haveI := Fintype.ofFinite (𝓞 ℚ ⧸ u.asIdeal)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Unfold `normV`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`.
-/
private theorem natCast_normV_mem (u : HeightOneSpectrum (𝓞 ℚ)) (h : (normV u).Prime) :
    ((normV u : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
  have hne : Nat.card (𝓞 ℚ ⧸ u.asIdeal) ≠ 0 := by
    have h0 := h.ne_zero
    unfold normV at h0
    exact h0
  haveI : Finite (𝓞 ℚ ⧸ u.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 ℚ ⧸ u.asIdeal)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold normV
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω`. Use `haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩`. Set `res : G F Ω →* G ℚ Ω` to `AlgEquiv.restrictScalarsHom ℚ`. Establish `hres_inj : Function.Injective res` using `fun g h hgh => AlgEquiv.ext fun x => by`. Establish `e` using `congrArg (fun σ : G ℚ Ω => σ x) hgh`.

Conclude with `e`. Establish `hVo : IsOpen ((V.map res : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))` using `GlobalTheory.KLift.isOpen_map_restrictScalars V hV`. Take `⟨ψ₀, hG₀, hpow₀, hT₀, u₀, hu₀T, hp, hu₀, hram⟩` from `hFC ℚ Ω (V.map res) hVo ((fun t : HeightOneSpectrum (𝓞 F) => t.under (𝓞 ℚ)) '' T) (hT.image _) n hn`. Establish `decV : ∀ A : ValuationSubring Ω, IsPlaceOver A u₀ → Dec (F` using `F) A ≤ V := by`. Introduce `A hA g hg`.

Take `⟨h, hhV, hh⟩` from `(hu₀ A hA).1 ((res_dec A g).2 hg)`. Rewrite `hhV` using `[hres_inj hh]`. Then use the resulting hypothesis. Take `⟨A₀, hA₀⟩` from `exists_isPlaceOver Ω u₀`. Take `⟨u, hu⟩` from `GlobalTheory.AbOverSubfield.exists_place_between (F := ℚ) (K := F) hA₀`. Establish `eu : u.under (𝓞 ℚ) = u₀` using `eq_of_isPlaceOver (under_place hu) hA₀`.

Establish `hunder : ∀ A : ValuationSubring Ω, IsPlaceOver A u → IsPlaceOver A u₀`. Introduce `A hA`. Rewrite using `[← eu]`. Conclude with `under_place hA`. Use `⟨ψ₀.comp res, ?_, ?_, ?_, ?_, u, ?_, ?_⟩` and prove the remaining obligations.

Use `⟨hG₀.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω), Abelianization.commutator_subset_ker _, fun j c hc => ?_⟩` and prove the remaining obligations. Conclude with `hG₀.real j (res c) hc`. Introduce `t A hA`. Distinguish the cases in `hpt : ((normV u₀ : ℕ) : 𝓞 ℚ) ∈ (t.under (𝓞 ℚ)).asIdeal`. Use `right`.

Establish `e : t.under (𝓞 ℚ) = u₀` using `eq_of_natCast_mem hp hpt (natCast_normV_mem u₀ hp)`. Apply `decV` to reduce the goal to its premises. Rewrite using `[← e]`. Conclude with `under_place hA`. Use `left`.

Introduce `g hg`. Conclude with `hram _ A (under_place hA) hpt _ ((res_ine A g).2 hg)`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hpow₀, MonoidHom.one_apply, MonoidHom.one_apply]`. Introduce `t ht A hA g hg`.

Conclude with `hT₀ _ ⟨t, ht, rfl⟩ A (under_place hA) _ ((res_dec A g).2 hg)`. Introduce `huT`. Conclude with `hu₀T ⟨u, huT, eu⟩`. Introduce `A hA`. Use `⟨decV A (hunder A hA), ?_⟩` and prove the remaining obligations.

Take `⟨τ₀, hτ₀, ho⟩` from `(hu₀ A (hunder A hA)).2`. Take `⟨h, -, hh⟩` from `(hu₀ A (hunder A hA)).1 (Ine_le_Dec A hτ₀)`. Use `⟨h, (res_ine A h).1 (by rw [show res h = τ₀ from hh]; exact hτ₀), ?_⟩` and prove the remaining obligations. Use `show orderOf (ψ₀ (res h)) = n`. Rewrite using `[show res h = τ₀ from hh]`.

Conclude with `ho`.
-/
private theorem core {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (hFC : FreshChar) (V : Subgroup (G F Ω)) (hV : IsOpen (V : Set (G F Ω)))
    (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (n : ℕ) (hn : 0 < n) :
    ∃ ψ : G F Ω →* ℂˣ, Good ψ.ker ∧
      (∀ (t : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A t →
        Ine (F := F) A ≤ ψ.ker ∨ Dec (F := F) A ≤ V) ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ V ∧
        ∃ τ ∈ Ine (F := F) A, orderOf (ψ τ) = n := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let res : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ
  have hres_inj : Function.Injective res := fun g h hgh => AlgEquiv.ext fun x => by
    have e := congrArg (fun σ : G ℚ Ω => σ x) hgh
    exact e
  have hVo : IsOpen ((V.map res : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) :=
    GlobalTheory.KLift.isOpen_map_restrictScalars V hV
  obtain ⟨ψ₀, hG₀, hpow₀, hT₀, u₀, hu₀T, hp, hu₀, hram⟩ := hFC ℚ Ω (V.map res) hVo
    ((fun t : HeightOneSpectrum (𝓞 F) => t.under (𝓞 ℚ)) '' T) (hT.image _) n hn
  have decV : ∀ A : ValuationSubring Ω, IsPlaceOver A u₀ → Dec (F := F) A ≤ V := by
    intro A hA g hg
    obtain ⟨h, hhV, hh⟩ := (hu₀ A hA).1 ((res_dec A g).2 hg)
    rwa [hres_inj hh] at hhV
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω u₀
  obtain ⟨u, hu⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := ℚ) (K := F) hA₀
  have eu : u.under (𝓞 ℚ) = u₀ := eq_of_isPlaceOver (under_place hu) hA₀
  have hunder : ∀ A : ValuationSubring Ω, IsPlaceOver A u → IsPlaceOver A u₀ := by
    intro A hA
    rw [← eu]
    exact under_place hA
  refine ⟨ψ₀.comp res, ?_, ?_, ?_, ?_, u, ?_, ?_⟩
  · refine ⟨hG₀.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω),
      Abelianization.commutator_subset_ker _, fun j c hc => ?_⟩
    exact hG₀.real j (res c) hc
  · intro t A hA
    by_cases hpt : ((normV u₀ : ℕ) : 𝓞 ℚ) ∈ (t.under (𝓞 ℚ)).asIdeal
    · right
      have e : t.under (𝓞 ℚ) = u₀ := eq_of_natCast_mem hp hpt (natCast_normV_mem u₀ hp)
      apply decV
      rw [← e]
      exact under_place hA
    · left
      intro g hg
      exact hram _ A (under_place hA) hpt _ ((res_ine A g).2 hg)
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hpow₀,
      MonoidHom.one_apply, MonoidHom.one_apply]
  · intro t ht A hA g hg
    exact hT₀ _ ⟨t, ht, rfl⟩ A (under_place hA) _ ((res_dec A g).2 hg)
  · intro huT
    exact hu₀T ⟨u, huT, eu⟩
  · intro A hA
    refine ⟨decV A (hunder A hA), ?_⟩
    obtain ⟨τ₀, hτ₀, ho⟩ := (hu₀ A (hunder A hA)).2
    obtain ⟨h, -, hh⟩ := (hu₀ A (hunder A hA)).1 (Ine_le_Dec A hτ₀)
    refine ⟨h, (res_ine A h).1 (by rw [show res h = τ₀ from hh]; exact hτ₀), ?_⟩
    show orderOf (ψ₀ (res h)) = n
    rw [show res h = τ₀ from hh]
    exact ho

/- English proof (translation)
Introduce `hFC E Ω _ _ _ _ _ _ U hU T hT n hn`. Use `haveI := isAlgClosure_plus (E := E) (Ω := Ω)`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Take `⟨ψ, h1, h2, h3, h4, u, hu, h5⟩` from `core hFC (U ⊓ fixGrp (maximalRealSubfield E) Ω E) (hU.inter (isOpen_fixGrp _ Ω E)) T hT n hn`. Conclude with `⟨ψ, h1, fun t A hA => (h2 t A hA).imp_right fun h g hg => (h hg).2, h3, h4, u, hu, fun A hA => ⟨fun g hg => ((h5 A hA).1 hg).1, (h5 A hA).2⟩⟩`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshSplit :
    FreshChar → FreshSplit := by
  intro hFC E Ω _ _ _ _ _ _ U hU T hT n hn
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ψ, h1, h2, h3, h4, u, hu, h5⟩ := core hFC (U ⊓ fixGrp (maximalRealSubfield E) Ω E)
    (hU.inter (isOpen_fixGrp _ Ω E)) T hT n hn
  exact ⟨ψ, h1, fun t A hA => (h2 t A hA).imp_right fun h g hg => (h hg).2, h3, h4, u, hu,
    fun A hA => ⟨fun g hg => ((h5 A hA).1 hg).1, (h5 A hA).2⟩⟩
