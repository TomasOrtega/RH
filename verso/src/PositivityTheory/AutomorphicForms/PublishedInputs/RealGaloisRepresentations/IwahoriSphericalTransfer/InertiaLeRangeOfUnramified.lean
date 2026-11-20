import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HeckeCharacterEqOfCofinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.QuadraticCharacterUnramified

/- English proof (translation)
Rewrite `h`, the goal using `[Filter.eventually_cofinite]`. Use `(h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hne : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`.

Establish `e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v` using `HeightOneSpectrum.ext hl.over.symm`. Conclude with `⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩`.
-/
theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

/- English proof (translation)
Use `filter_upwards [eventually_under (F := F) hq] with v hv`. Take `⟨w, rfl, hw⟩` from `hv`. Take `⟨h1, h3⟩` from `hw (w.under (𝓞 F)) rfl`. Use `⟨w, rfl, h1, (congrArg Units.val h3).trans ?_⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem good {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v ∧
      η.UnrAt v ∧ ((η.val v : ℂˣ) : ℂ) = if normV w = normV v then 1 else -1 := by
  filter_upwards [eventually_under (F := F) hq] with v hv
  obtain ⟨w, rfl, hw⟩ := hv
  obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
  refine ⟨w, rfl, h1, (congrArg Units.val h3).trans ?_⟩
  split_ifs <;> simp

/- English proof (translation)
Use `show η ^ 2 = 1`. Apply `GlobalTheory.T.hecke_character_eq_of_cofinite F (η ^ 2) 1` to reduce the goal to its premises. Use `filter_upwards [good hq] with v hv`. Take `⟨w, -, hu, hval⟩` from `hv`. Use `⟨fun x hx => ?_, fun x _ => rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_two, HChar.loc_mul, hu x hx, one_mul]`. Establish `e1 : (1 : HChar F).val v = 1` using `rfl`. Rewrite using `[pow_two, HChar.val_mul, e1]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, hval, Units.val_one]`.

Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem orderDvd_two {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) : η.OrderDvd 2 := by
  show η ^ 2 = 1
  apply GlobalTheory.T.hecke_character_eq_of_cofinite F (η ^ 2) 1
  filter_upwards [good hq] with v hv
  obtain ⟨w, -, hu, hval⟩ := hv
  refine ⟨fun x hx => ?_, fun x _ => rfl, ?_⟩
  · rw [pow_two, HChar.loc_mul, hu x hx, one_mul]
  · have e1 : (1 : HChar F).val v = 1 := rfl
    rw [pow_two, HChar.val_mul, e1]
    apply Units.ext
    rw [Units.val_mul, hval, Units.val_one]
    split_ifs <;> norm_num

end GlobalTheory.QuadraticCharacterUnramified

/- English proof (translation)
Introduce `N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu`. Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Take `⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`. Take `⟨art, ha⟩` from `N.aut.art F Ω`. Take `⟨δ, hδc, hL⟩` from `ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))`.

Take `⟨ε, hεc, -, hε, hεu⟩` from `UpperTheory.exists_quadratic_sign_character F K Ω 2 h2`. Establish `hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ)` using `fun v hv B hB => ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by`. Rewrite using `[map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv, RingEquiv.apply_symm_apply]⟩`. Establish `hS` using `Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)`. Establish `key` using `GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by`.

Take `⟨⟨w, hwv, hu', hval⟩, hεv⟩` from `not_not.1 hv`. Substitute `hwv` using the available equality. Establish `h1` using `(hE _ hu' B hB).2 σ hσ`. Establish `h3` using `(UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ`. Establish `e : δ σ⁻¹ = ε σ⁻¹` using `Units.ext (ι.injective (by rw [h1, h3, hval]))`.

Rewrite `e` using `[map_inv, map_inv, inv_inj]`. Then use the resulting hypothesis. Introduce `s hs`. Establish `h1 : δ s = 1` using `(hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs`. Establish `h3 : ε s = 1`. Establish `e : δ s = ε s` using `congrFun key s`.

Rewrite using `[← e, h1]`. Conclude with `(hε.1 s).1 h3`.
-/
theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
