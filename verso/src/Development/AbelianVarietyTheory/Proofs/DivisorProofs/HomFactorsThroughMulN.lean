import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulNDiv

/- English proof (translation)
Use `ext1`. Apply `T.left.affineOpenCover.openCover.hom_ext` to reduce the goal to its premises. Introduce `j`. Set `C : CommRingCat` to `T.left.affineOpenCover.X j`. Set `φ : CommRingCat.of R ⟶ C` to `Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)`.

Use `letI : Algebra R C := φ.hom.toAlgebra`. Set `g : SpAlg R C ⟶ T` to `Over.homMk (T.left.affineOpenCover.f j) (by show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))`. Rewrite using `[← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]`. Use the proof step `rfl)`. Use `congrArg CommaMorphism.left (h C g)` as an intermediate fact.

Simplify using `only [g, Over.comp_left, Over.homMk_left] at this`. Conclude with `this`.
-/
theorem hom_ext_of_spAlg {R : Type} [CommRing R] {T B : Over (Sp R)} (a b : T ⟶ B)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (g : SpAlg R S ⟶ T), g ≫ a = g ≫ b) : a = b := by
  ext1
  apply T.left.affineOpenCover.openCover.hom_ext
  intro j
  let C : CommRingCat := T.left.affineOpenCover.X j
  let φ : CommRingCat.of R ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
  letI : Algebra R C := φ.hom.toAlgebra
  let g : SpAlg R C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
    rfl)
  have := congrArg CommaMorphism.left (h C g)
  simp only [g, Over.comp_left, Over.homMk_left] at this
  exact this

/- English proof (translation)
Introduce `R _ A B _ _ hA _ n hn F hF hker`. Use `haveI := hA.comm`. Take `⟨hfin, hflat, hsurj⟩` from `GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective R A hA n hn`. Use `haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n`. Establish `hqc : QuasiCompact (mulN A n).left` using `inferInstance`.

Establish `h : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1`. Introduce `T x hx`. Apply `hom_ext_of_spAlg` to reduce the goal to its premises. Introduce `S _ _ g`. Establish `hxn : x ^ n = 1`.

Rewrite using `[← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]`. Establish `hz : (g ≫ x) ^ n = 1`. Rewrite using `[← MonObj.comp_pow, hxn, MonObj.comp_one]`. Rewrite using `[← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]`. Take `⟨⟨ψ, hψ, hc⟩, -⟩` from `exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF hflat hsurj hqc h`.

Conclude with `⟨ψ, hψ, hc.symm⟩`.
-/
theorem exists_factor_mulN : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (n : ℕ), 0 < n → ∀ (F : A ⟶ B), IsMonHom F → (∀ (S : Type) [CommRing S] [Algebra R S] (z : SpAlg R S ⟶ A), z ^ n = 1 → z ≫ F = 1) → ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
  intro R _ A B _ _ hA _ n hn F hF hker
  haveI := hA.comm
  obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective R A hA n hn
  haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
  have hqc : QuasiCompact (mulN A n).left := inferInstance
  have h : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
    intro T x hx
    apply hom_ext_of_spAlg
    intro S _ _ g
    have hxn : x ^ n = 1 := by
      rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
    have hz : (g ≫ x) ^ n = 1 := by
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
    rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
    hflat hsurj hqc h
  exact ⟨ψ, hψ, hc.symm⟩

end GlobalTheory.MulNDiv
