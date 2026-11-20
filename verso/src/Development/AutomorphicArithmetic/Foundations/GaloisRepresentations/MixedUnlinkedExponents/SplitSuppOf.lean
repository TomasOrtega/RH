import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

/- English proof (translation)
Unfold `UpperTheory.Gal.GamX.SplitSuppOf`. Introduce `hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw`. Use `haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2`. Break down `GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩` into its components or cases. It suffices to derive a contradiction.

Use `hw fun u => ?_` and prove the remaining obligations. Use `haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2`. Establish `hu : u.1.under (𝓞 K) = v` using `HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm`. Take `⟨-, -, -, h⟩` from `hc`. Conclude with `Subtype.ext (h u.1 hu)`.

Take `⟨hi', hN⟩` from `GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef`. Establish `hi : Continuous i` using `GroundTheory.Global.continuous_adicCompletionMap v w.1`. Establish `hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)` using `GroundTheory.Global.adicCompletionMap_algebraMap v w.1`. Use `⟨i, hi', hi, hcomp, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hNm K L v w]`.

Conclude with `MonoidHom.ext fun y => Units.ext (hN y)`. Introduce and unpack `s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩ haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩ haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)`. Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := L ≃ₐ[K] L)`. Establish `hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat` using `hW`. Take `⟨e, he'⟩` from `hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'`.

Establish `hg : ∀ g : GL (Fin n) (w.1.adicCompletion L), Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g` using `fun g => Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)`. Set `φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n` to `Fin n) i.symm.toRingHom)) τ'.ρ := Representation.Equiv.mk e fun g => LinearMap.ext fun x => by`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]`. Conclude with `(he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))`. Establish `h2` using `(GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ`.

Conclude with `(hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩`.
-/
theorem UpperTheory.Gal.GamX.splitSuppOf :
    UpperTheory.Gal.GamX.SplitSuppOf := by
  unfold UpperTheory.Gal.GamX.SplitSuppOf
  intro hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  rcases GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩
  · exfalso
    refine hw fun u => ?_
    haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2
    have hu : u.1.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm
    obtain ⟨-, -, -, h⟩ := hc
    exact Subtype.ext (h u.1 hu)
  · obtain ⟨hi', hN⟩ := GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf
    set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef
    have hi : Continuous i := GroundTheory.Global.continuous_adicCompletionMap v w.1
    have hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) :=
      GroundTheory.Global.adicCompletionMap_algebraMap v w.1
    refine ⟨i, hi', hi, hcomp, ?_, ?_⟩
    · rw [hNm K L v w]
      exact MonoidHom.ext fun y => Units.ext (hN y)
    · rintro s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩
      haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
      obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat := hW
      obtain ⟨e, he'⟩ := hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'
      have hg : ∀ g : GL (Fin n) (w.1.adicCompletion L),
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) τ'.ρ :=
        Representation.Equiv.mk e fun g => LinearMap.ext fun x => by
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]
          exact (he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))
      have h2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ
      exact (hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩
