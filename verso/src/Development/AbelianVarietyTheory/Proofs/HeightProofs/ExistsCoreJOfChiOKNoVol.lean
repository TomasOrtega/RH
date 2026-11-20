import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdelicCoreWithoutVolumeNormalisationStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdelStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

/- English proof (translation)
Introduce `D hO hZ pb hg chi₀ hchi`. Take `⟨Q, hP, hCan, hpq, hM⟩` from `GlobalTheory.Member.ParExist.exists_par_pins_canon D hO hZ pb hg`. Establish `hle : FO D ≤ Q.c.F`. Rewrite using `[FO, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Take `⟨x, rfl⟩` from `Q.eO.surjective y`. Establish `h : D.what₂.phiO (Q.eO x) = ((x : Q.c.F) : ℂ)` using `hP.2.2.1 x`. Rewrite using `[h]`. Conclude with `(x : Q.c.F).2`. Establish `key : ∀ j, ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, χ Q.c.F.val.toRingHom = chi₀ j ∧ (InR D j → ∀ σ, IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chi₀ j) (χ σ))`.

Introduce `j`. Distinguish the cases in `hj : InR D j`. Take `⟨h1, h2, h3⟩` from `hchi j hj`. Take `⟨χ, hχ, hσ⟩` from `GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles D Q (chi₀ j) h1 h2 (fun x hx => ⟨⟨_, hle (h3 x hx)⟩, rfl⟩)`. Conclude with `⟨χ, hχ, fun _ => hσ⟩`.

Conclude with `⟨fun _ => chi₀ j, rfl, fun h => absurd h hj⟩`. Use `choose chiW h0 hW using key`. Take `⟨T, hJ, hC, hp, hQ, hH⟩` from `GlobalTheory.T.exists_adelicCore_without_volumeNormalisation D Q hP hpq pb hg hM chiW (fun j hj σ _ => by rw [h0 j]; exact hW j hj σ)`. Substitute `hQ` using the available equality. Use `⟨T, hJ, hC, hCan, hp, hpq, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_of_heq hH]`. Conclude with `h0 j`.
-/
theorem exists_coreJ_of_chiOK_noVol : ∀ (D : D7), OFull D → OZeta D → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → ∀ chi₀, ChiOK D chi₀ → ∃ J : CoreJ D, LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ J.pb = pb ∧ (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) ∧ (∀ j, J.chiW j J.σ₀ = chi₀ j) := by
  intro D hO hZ pb hg chi₀ hchi
  classical
  obtain ⟨Q, hP, hCan, hpq, hM⟩ := GlobalTheory.Member.ParExist.exists_par_pins_canon D hO hZ pb hg
  have hle : FO D ≤ Q.c.F := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Q.eO.surjective y
    have h : D.what₂.phiO (Q.eO x) = ((x : Q.c.F) : ℂ) := hP.2.2.1 x
    rw [h]
    exact (x : Q.c.F).2
  have key : ∀ j, ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle,
      χ Q.c.F.val.toRingHom = chi₀ j ∧ (InR D j → ∀ σ,
        IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧
          MuConj Q.c.F.val.toRingHom σ (chi₀ j) (χ σ)) := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨h1, h2, h3⟩ := hchi j hj
      obtain ⟨χ, hχ, hσ⟩ := GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles D Q (chi₀ j) h1 h2
        (fun x hx => ⟨⟨_, hle (h3 x hx)⟩, rfl⟩)
      exact ⟨χ, hχ, fun _ => hσ⟩
    · exact ⟨fun _ => chi₀ j, rfl, fun h => absurd h hj⟩
  choose chiW h0 hW using key
  obtain ⟨T, hJ, hC, hp, hQ, hH⟩ := GlobalTheory.T.exists_adelicCore_without_volumeNormalisation D Q hP hpq pb hg hM chiW
    (fun j hj σ _ => by rw [h0 j]; exact hW j hj σ)
  subst hQ
  refine ⟨T, hJ, hC, hCan, hp, hpq, fun j => ?_⟩
  rw [eq_of_heq hH]
  exact h0 j

end GlobalTheory.FinalJoin2
