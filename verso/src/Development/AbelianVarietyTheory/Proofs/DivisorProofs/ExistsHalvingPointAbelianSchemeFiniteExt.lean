import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHomStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfPt

/- English proof (translation)
Use `haveI : IsAffine X := isAffine_of_isAffineHom f`. Set `ψ : CommRingCat.of R ⟶ Γ(X, ⊤)` to `Spec.preimage (X.isoSpec.inv ≫ f)`. Establish `hψ : Spec.map ψ = X.isoSpec.inv ≫ f` using `Spec.map_preimage _`. Use `⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : Surjective (Spec.map ψ)` using `by rw [hψ]; infer_instance`.

Establish `hd : DenseRange (PrimeSpectrum.comap ψ.hom)` using `hs.1.denseRange`. Rewrite `hd` using `[PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Simplify using `using hd hx`.

Establish `hf : IsFinite (Spec.map ψ)` using `by rw [hψ]; infer_instance`. Conclude with `(IsFinite.SpecMap_iff ψ).1 hf`. Conclude with `hψ.symm`.
-/
theorem exists_spec_of_finite_surjective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsFinite f] [Surjective f] :
    ∃ (C : Type) (_ : CommRing C) (φ : R →+* C) (g : Sp C ⟶ X),
      Function.Injective φ ∧ φ.Finite ∧ g ≫ f = spMap φ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩
  · have hs : Surjective (Spec.map ψ) := by rw [hψ]; infer_instance
    have hd : DenseRange (PrimeSpectrum.comap ψ.hom) := hs.1.denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero] at hd
    rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using hd hx
  · have hf : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (IsFinite.SpecMap_iff ψ).1 hf
  · exact hψ.symm

end GlobalTheory.HalfPt

namespace GlobalTheory.HalfPt

/- English proof (translation)
Introduce `R _ _ _ B _ _ a hCN hAb`. Use `haveI : IsNoetherianRing R := hCN.1`. Take `⟨hfin, -⟩` from `GlobalTheory.T.isFinite_and_flat_mul_abelianScheme (Sp R) B hAb 2 (by norm_num)`. Establish `hsurj` using `GlobalTheory.T.semiAbelian_mul_nat_surjective (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero`. Set `m : B.left ⟶ B.left` to `((𝟙 B) ^ 2 : B ⟶ B).left`.

Set `s : Sp R ⟶ B.left` to `a.left`. Use `haveI : IsFinite m := hfin`. Use `haveI : Surjective m := hsurj`. Use `haveI : IsFinite (pullback.snd m s) := inferInstance`. Use `haveI : Surjective (pullback.snd m s) := inferInstance`.

Take `⟨C, _, φ, g, hinj, hφf, hg⟩` from `exists_spec_of_finite_surjective (pullback.snd m s)`. Take `⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩` from `GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R C φ hCN hinj hφf`. Establish `hsB : s ≫ B.hom = 𝟙 (Sp R)` using `Over.w a`. Establish `hmB : m ≫ B.hom = B.hom` using `Over.w ((𝟙 B) ^ 2 : B ⟶ B)`. Establish `hfst : pullback.fst m s ≫ B.hom = pullback.snd m s`.

Rewrite using `[← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]`. Establish `hρ : spMap σ ≫ spMap φ = spMap ρ`. Rewrite using `[← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Set `c : Over.mk (spMap ρ) ⟶ B` to `Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by`. Simplify using `only [Over.mk_hom, Category.assoc]`.

Rewrite using `[hfst, hg, hρ])`. Use `⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩` and prove the remaining obligations. Establish `hc : c ^ 2 = c ≫ (𝟙 B) ^ 2` using `by rw [comp_pow, Category.comp_id]`. Rewrite using `[hc]`. Use `ext`.

Simplify using `only [c, Over.comp_left, Over.homMk_left, Category.assoc]`. Use `show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _`. Rewrite using `[pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]`. Both sides reduce to the same expression.
-/
theorem exists_half_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  intro R _ _ _ B _ _ a hCN hAb
  haveI : IsNoetherianRing R := hCN.1
  obtain ⟨hfin, -⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme (Sp R) B hAb 2 (by norm_num)
  have hsurj := GlobalTheory.T.semiAbelian_mul_nat_surjective (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero
  let m : B.left ⟶ B.left := ((𝟙 B) ^ 2 : B ⟶ B).left
  let s : Sp R ⟶ B.left := a.left
  haveI : IsFinite m := hfin
  haveI : Surjective m := hsurj
  haveI : IsFinite (pullback.snd m s) := inferInstance
  haveI : Surjective (pullback.snd m s) := inferInstance
  obtain ⟨C, _, φ, g, hinj, hφf, hg⟩ := exists_spec_of_finite_surjective (pullback.snd m s)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩ := GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R C φ hCN hinj hφf
  have hsB : s ≫ B.hom = 𝟙 (Sp R) := Over.w a
  have hmB : m ≫ B.hom = B.hom := Over.w ((𝟙 B) ^ 2 : B ⟶ B)
  have hfst : pullback.fst m s ≫ B.hom = pullback.snd m s := by
    rw [← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]
  have hρ : spMap σ ≫ spMap φ = spMap ρ := by
    rw [← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let c : Over.mk (spMap ρ) ⟶ B :=
    Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hfst, hg, hρ])
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩
  have hc : c ^ 2 = c ≫ (𝟙 B) ^ 2 := by rw [comp_pow, Category.comp_id]
  rw [hc]
  ext
  simp only [c, Over.comp_left, Over.homMk_left, Category.assoc]
  show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _
  rw [pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]
  rfl

end GlobalTheory.HalfPt
