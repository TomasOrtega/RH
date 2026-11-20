import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHostStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `R H e hg hp hp' he hs`. Take `⟨⟨P⟩, ⟨W⟩⟩` from `GlobalTheory.nonempty_piBar_and_omg R H`. Establish `hmu : ∀ j : Fin R.m, ∃ χ : HChar H.E, IsMu0 P W (e j) j.1 χ` using `fun j => GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)`. Use `choose mu hmu using hmu`. Take `⟨eta, heta⟩` from `GlobalTheory.T.host_etaTilde_character_exists R H`.

Take `⟨chi, hchi⟩` from `GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H`. Take `⟨d, hd⟩` from `GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp`. Take `⟨d', hd'⟩` from `GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'`. Conclude with `⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩⟩`.
-/
theorem nonempty_hFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  intro R H e hg hp hp' he hs
  obtain ⟨⟨P⟩, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg R H
  have hmu : ∀ j : Fin R.m, ∃ χ : HChar H.E, IsMu0 P W (e j) j.1 χ := fun j =>
    GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.T.host_etaTilde_character_exists R H
  obtain ⟨chi, hchi⟩ := GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H
  obtain ⟨d, hd⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp
  obtain ⟨d', hd'⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩⟩

end GlobalTheory
