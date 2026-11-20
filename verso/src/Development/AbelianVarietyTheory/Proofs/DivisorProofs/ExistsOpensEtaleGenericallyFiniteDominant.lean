import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

/- English proof (translation)
Introduce `k _ X Y _ _ p q D hp hq π hπ hη hd`. Use `GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver` as an intermediate fact. Establish `: IsProper (π ≫ p)` using `hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver`. Establish `: IsProper π` using `IsProper.of_comp π p`. Use `hp.isLocallyNoetherian` as an intermediate fact.

Use `hp.charZero` as an intermediate fact. Take `⟨U, -, hU, hxU, hW, -, hE, -⟩` from `GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)`. Use `⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩` and prove the remaining obligations. Establish `: IsAffine U` using `hU`. Establish `: IsAffine (π ⁻¹ᵁ U)` using `hW`.

Establish `hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale`. Introduce and unpack `_ rfl`. Conclude with `hE`. Establish `e : U.ι ''ᵁ ⊤ = U`. Rewrite using `[Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]`.

Establish `h1 : Etale (π ∣_ U)`. Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]`. Conclude with `(RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)`. Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`.
-/
theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
