import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAwayStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

/- English proof (translation)
Introduce `hbc E _ _ _ H Dw l Xo S _ x s hs p`. Take `⟨g, hg, θ, hθ⟩` from `GlobalTheory.T.exists_local_generator_stable_baseChange hbc E H Dw l Xo S x p`. Establish `hid : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ Xo.X), z = spMap (RingHom.id R) ≫ z`. Introduce `R _ z`. Establish `: spMap (RingHom.id R) = 𝟙 (Sp R)` using `Spec.map_id _`.

Rewrite using `[this, Category.id_comp]`. Take `⟨-, hc2, -, hc4⟩` from `GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo (Localization.Away g) (Localization.Away g) (Localization.Away g) (RingHom.id _) (RingHom.id _) (spMap (algebraMap S (Localization.Away g)) ≫ x) _ _ (hid _ _) (hid _ _)`. Establish `hθθ : SecBC (RingHom.id (Localization.Away g)) 1 _ _ θ θ` using `(hc2 1 θ θ).2 fun i => by rw [(hc4 1 1 i).2.2, _root_.one_mul]`. Establish `hnz` using `(hθ _ (RingHom.id _) _ θ (hid _ _) hθθ).2`. Choose the witnesses or unpack the hypotheses as in `⟨p', hp'⟩ : ∃ p' : PrimeSpectrum (Localization.Away g), PrimeSpectrum.comap (algebraMap S (Localization.Away g)) p' = p := by`.

Establish `h` using `PrimeSpectrum.localization_away_comap_range (Localization.Away g) g`. Establish `: (p : PrimeSpectrum S) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g)))`. Rewrite using `[h]`. Conclude with `hg`. Conclude with `this`.

Take `⟨q, i, hq, hqi⟩` from `hnz p'`. Take `⟨N, s₀, s₁, h01, h1⟩` from `GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away E H Dw l Xo S x g θ`. Establish `hu : IsUnit (scal (spMap (algebraMap S (Localization.Away g)) ≫ x) ((algebraMap S (Localization.Away g)) g ^ N) i)`. Take `⟨v, hv⟩` from `((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow N).exists_right_inv`. Use `IsUnit.of_mul_eq_one (scal _ v i) ?_` and prove the remaining obligations.

Rewrite using `[← (hc4 _ v i).1, hv, (hc4 1 1 i).2.2]`. Establish `hq1 : q ∈ (Gx _).basicOpen (s₁.f i)`. Rewrite using `[h1 i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]`. Conclude with `⟨Scheme.basicOpen_le _ _ hqi, hqi⟩`. Take `⟨q₀, i₀, hq₀, hqi₀⟩` from `(GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S (Localization.Away g) _ x _ rfl s₀ s₁ h01 p').1 ⟨q, i, hq, hq1⟩`.

Take `⟨b, hb, -⟩` from `hs s₀`. Rewrite `hqi₀` using `[hb i₀, Scheme.basicOpen_mul]`. Conclude with `⟨q₀, i₀, hq₀.trans hp', hqi₀.2⟩`.
-/
theorem secNZ_of_secGen : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  intro hbc E _ _ _ H Dw l Xo S _ x s hs p
  obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hbc E H Dw l Xo S x p
  have hid : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ Xo.X), z = spMap (RingHom.id R) ≫ z := by
    intro R _ z
    have : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, hc2, -, hc4⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo (Localization.Away g) (Localization.Away g)
    (Localization.Away g) (RingHom.id _) (RingHom.id _) (spMap (algebraMap S (Localization.Away g)) ≫ x)
    _ _ (hid _ _) (hid _ _)
  have hθθ : SecBC (RingHom.id (Localization.Away g)) 1 _ _ θ θ :=
    (hc2 1 θ θ).2 fun i => by rw [(hc4 1 1 i).2.2, _root_.one_mul]
  have hnz := (hθ _ (RingHom.id _) _ θ (hid _ _) hθθ).2
  obtain ⟨p', hp'⟩ : ∃ p' : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) p' = p := by
    have h := PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
    have : (p : PrimeSpectrum S) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [h]; exact hg
    exact this
  obtain ⟨q, i, hq, hqi⟩ := hnz p'
  obtain ⟨N, s₀, s₁, h01, h1⟩ := GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away E H Dw l Xo S x g θ
  have hu : IsUnit (scal (spMap (algebraMap S (Localization.Away g)) ≫ x)
      ((algebraMap S (Localization.Away g)) g ^ N) i) := by
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow N).exists_right_inv
    refine IsUnit.of_mul_eq_one (scal _ v i) ?_
    rw [← (hc4 _ v i).1, hv, (hc4 1 1 i).2.2]
  have hq1 : q ∈ (Gx _).basicOpen (s₁.f i) := by
    rw [h1 i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    exact ⟨Scheme.basicOpen_le _ _ hqi, hqi⟩
  obtain ⟨q₀, i₀, hq₀, hqi₀⟩ := (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S (Localization.Away g) _ x _ rfl s₀ s₁ h01 p').1
    ⟨q, i, hq, hq1⟩
  obtain ⟨b, hb, -⟩ := hs s₀
  rw [hb i₀, Scheme.basicOpen_mul] at hqi₀
  exact ⟨q₀, i₀, hq₀.trans hp', hqi₀.2⟩

end GlobalTheory.Frames
