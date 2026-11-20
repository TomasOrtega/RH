import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `X k k' _ _ _ _ x x' u u' hsp`. Take `⟨B, _, g, g', ρ, hker, hx, hx'⟩` from `GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes x x' u u' hsp`. Use `set q := RingHom.ker g' with hq`. Use `haveI : q.IsPrime := RingHom.ker_isPrime g'`. Set `D` to `B ⧸ q`.

Set `h' : D →+* k'` to `RingHom.kerLift g'`. Establish `h'inj : Function.Injective h'` using `RingHom.kerLift_injective g'`. Set `h : D →+* k` to `Ideal.Quotient.lift q g (fun b hb => hker hb)`. Take `⟨C, _, _, hCdom, hCint, hCinj, hCroot, hCext⟩` from `GlobalTheory.T.exists_integral_domain_extension_with_monic_roots D`. Take `⟨e', he'inj, he'⟩` from `hCext k' h' h'inj`.

Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed D C k h (by`. Introduce `a ha`. Rewrite `ha`, the goal using `[RingHom.mem_ker]`. Rewrite using `[show a = 0 from hCinj (by rw [ha, map_zero])]; exact map_zero h)`. Set `P` to `RingHom.ker ψ`.

Use `haveI : P.IsPrime := RingHom.ker_isPrime ψ`. Set `R` to `Localization.AtPrime P`. Establish `h0 : (0 : C) ∉ P.primeCompl` using `fun h0 => h0 P.zero_mem`. Establish `hRloc` using `(absIntClosed_localization_and_quotient C ⟨hCdom, hCroot⟩).1 P.primeCompl h0`. Take `⟨hH, hAC, -⟩` from `AbsIntClosedLocal.henselian_isAlgClosed_pow_surj R hRloc`.

Set `φ : B →+* R` to `(algebraMap C R).comp ((algebraMap D C).comp (Ideal.Quotient.mk q))`. Set `f : R →+* k` to `IsLocalization.lift (M := P.primeCompl) (g := ψ) (fun s => by`. Use `IsUnit.mk0 _ ?_` and prove the remaining obligations. Conclude with `s.2)`. Set `f' : R →+* k'` to `IsLocalization.lift (M := P.primeCompl) (g := e') (fun s => by`.

Use `IsUnit.mk0 _ ?_` and prove the remaining obligations. Introduce `hs`. Conclude with `s.2 (by rw [show (s : C) = 0 from he'inj (by rw [hs, map_zero])]; exact P.zero_mem))`. Establish `hf : f.comp φ = g`. Use extensionality with `b`.

Simplify using `only [f, φ, RingHom.comp_apply, IsLocalization.lift_eq]`. Rewrite using `[← RingHom.comp_apply ψ, hψ]`. Both sides reduce to the same expression. Establish `hf' : f'.comp φ = g'`. Use extensionality with `b`.

Simplify using `only [f', φ, RingHom.comp_apply, IsLocalization.lift_eq]`. Rewrite using `[← RingHom.comp_apply e', he']`. Both sides reduce to the same expression. Use `⟨R, inferInstance, hH, hAC, spMap φ ≫ ρ, spMap f, spMap f', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, hx]`.

Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf', hx']`.
-/
theorem geomPoints_factor_henselian_of_specializes :
  ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (R : Type) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsAlgClosed (IsLocalRing.ResidueField R)) (r : Sp R ⟶ X) (i : Sp k ⟶ Sp R) (i' : Sp k' ⟶ Sp R), i ≫ r = x ∧ i' ≫ r = x' := by
  intro X k k' _ _ _ _ x x' u u' hsp
  obtain ⟨B, _, g, g', ρ, hker, hx, hx'⟩ := GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes x x' u u' hsp
  set q := RingHom.ker g' with hq
  haveI : q.IsPrime := RingHom.ker_isPrime g'
  let D := B ⧸ q
  let h' : D →+* k' := RingHom.kerLift g'
  have h'inj : Function.Injective h' := RingHom.kerLift_injective g'
  let h : D →+* k := Ideal.Quotient.lift q g (fun b hb => hker hb)
  obtain ⟨C, _, _, hCdom, hCint, hCinj, hCroot, hCext⟩ := GlobalTheory.T.exists_integral_domain_extension_with_monic_roots D
  obtain ⟨e', he'inj, he'⟩ := hCext k' h' h'inj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed D C k h (by
    intro a ha; rw [RingHom.mem_ker] at ha ⊢
    rw [show a = 0 from hCinj (by rw [ha, map_zero])]; exact map_zero h)
  let P := RingHom.ker ψ
  haveI : P.IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime P
  have h0 : (0 : C) ∉ P.primeCompl := fun h0 => h0 P.zero_mem
  have hRloc := (absIntClosed_localization_and_quotient C ⟨hCdom, hCroot⟩).1 P.primeCompl h0
  obtain ⟨hH, hAC, -⟩ := AbsIntClosedLocal.henselian_isAlgClosed_pow_surj R hRloc
  let φ : B →+* R := (algebraMap C R).comp ((algebraMap D C).comp (Ideal.Quotient.mk q))
  let f : R →+* k := IsLocalization.lift (M := P.primeCompl) (g := ψ) (fun s => by
    refine IsUnit.mk0 _ ?_
    exact s.2)
  let f' : R →+* k' := IsLocalization.lift (M := P.primeCompl) (g := e') (fun s => by
    refine IsUnit.mk0 _ ?_
    intro hs
    exact s.2 (by rw [show (s : C) = 0 from he'inj (by rw [hs, map_zero])]; exact P.zero_mem))
  have hf : f.comp φ = g := by
    ext b
    simp only [f, φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply ψ, hψ]
    rfl
  have hf' : f'.comp φ = g' := by
    ext b
    simp only [f', φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply e', he']
    rfl
  refine ⟨R, inferInstance, hH, hAC, spMap φ ≫ ρ, spMap f, spMap f', ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, hx]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf', hx']

end GlobalTheory
