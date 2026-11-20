import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Use `haveI : CharZero L := (RingHom.charZero_iff f.injective).1 inferInstance`. Use `letI : Algebra E L := f.toAlgebra`. Use `haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by`. Express the relevant statement in the definitionally equal form `_ = f (algebraMap ℚ E q)`. Simplify using the standard rewrite rules.

Take `⟨σ, hσ⟩` from `(Normal.algHomEquivAut ℚ L E).symm.surjective f'.toRatAlgHom`. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hσ x` as an intermediate fact. Conclude with `this.symm`.
-/
theorem exists_aut_comp_eq_of_normal {E L : Type} [Field E] [CharZero E] [Normal ℚ E] [Field L]
    (f f' : E →+* L) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, f' x = f (σ x) := by
  haveI : CharZero L := (RingHom.charZero_iff f.injective).1 inferInstance
  letI : Algebra E L := f.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    change _ = f (algebraMap ℚ E q)
    simp
  obtain ⟨σ, hσ⟩ := (Normal.algHomEquivAut ℚ L E).symm.surjective f'.toRatAlgHom
  refine ⟨σ, fun x => ?_⟩
  have := DFunLike.congr_fun hσ x
  exact this.symm

/- English proof (translation)
Introduce `D i w hw τ`. Use `haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois`. Take `⟨σ, hσ⟩` from `exists_aut_comp_eq_of_normal (((Br.toLLK (D.nbr i w hw)).comp (D.nd.embK i)).comp D.embE) ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw))`. Take `⟨g, hg⟩` from `(D.host.gal).symm.surjective σ`. Establish `hg' : D.host.sigmaOf g = σ` using `hg`.

Establish `key : ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) = Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))`. Introduce `x`. Rewrite using `[hg']`. Conclude with `hσ x`. Establish `hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x` using `fun x => DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)`.

Use `⟨g, key, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨-, φ, hφ, h⟩`. Establish `: D.host.emb g = φ` using `RingHom.ext fun x => by`. Rewrite using `[← hemb x]`. Conclude with `h x _ (key x).symm`.

Conclude with `((factEmb D.R D.host).2 g).1 (this ▸ hφ)`. Introduce `hgP`. Use `⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, ((factEmb D.R D.host).2 g).2 hgP, ?_⟩` and prove the remaining obligations. Introduce `x y hy`. Establish `hy' : y = D.embE (D.host.sigmaOf g x)` using `(D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))`.

Rewrite using `[hy', hemb]`.
-/
theorem exists_letter_of_local_embedding : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), ∃ g : D.R.GG, (∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) = Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))) ∧ (Br.EmbTypeU D.nbr i w hw τ ↔ g ∈ D.R.Psi) := by
  intro D i w hw τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨σ, hσ⟩ := exists_aut_comp_eq_of_normal
    (((Br.toLLK (D.nbr i w hw)).comp (D.nd.embK i)).comp D.embE)
    ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw))
  obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
  have hg' : D.host.sigmaOf g = σ := hg
  have key : ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
      Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x))) := by
    intro x
    rw [hg']
    exact hσ x
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  refine ⟨g, key, ?_, ?_⟩
  · rintro ⟨-, φ, hφ, h⟩
    have : D.host.emb g = φ := RingHom.ext fun x => by
      rw [← hemb x]
      exact h x _ (key x).symm
    exact ((factEmb D.R D.host).2 g).1 (this ▸ hφ)
  · intro hgP
    refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, ((factEmb D.R D.host).2 g).2 hgP, ?_⟩
    intro x y hy
    have hy' : y = D.embE (D.host.sigmaOf g x) :=
      (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
    rw [hy', hemb]

end GlobalTheory.HTW
