import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesOnEtaleNeighbourhood
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.OneCoh

/- English proof (translation)
Take `⟨O, _, _, hSH, hInd, hO⟩` from `GlobalTheory.T.exists_strictHenselization_at_maximal B P hsep`. Establish `hsub : Subsingleton (Ht q (sp O) m i)` using `GlobalTheory.EtC.b2 (ZMod q) O hSH (tw q i) m hm`. Establish `h0 : pull _ (spMap (algebraMap B O)) _ _ y = 0` using `Subsingleton.elim _ _`. Take `⟨D, _, _, _, φ, hD⟩` from `GlobalTheory.T.vanishes_on_etale_neighbourhood q B O hq hInd m i y h0`. Take `⟨hH, -⟩` from `hSH`.

Use `haveI : IsLocalRing O := hH.toIsLocalRing`. Take `⟨hP, hres⟩` from `hO (IsLocalRing.maximalIdeal O) inferInstance`. Use `⟨D, inferInstance, inferInstance, inferInstance, (IsLocalRing.maximalIdeal O).comap φ, ?_, ?_, ?_, hD⟩` and prove the remaining obligations. Conclude with `Ideal.comap_isPrime _ _`. Rewrite using `[← hP]`.

Use extensionality with `b`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]`. Introduce `d`. Take `⟨b, hb⟩` from `hres (φ d)`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_comap, map_sub, AlgHom.commutes]`. Conclude with `hb`.
-/
theorem dies_on_etale_with_point (q : ℕ) [NeZero q] (B : Type) [CommRing B] (hq : IsUnit (q : B))
    (P : Ideal B) [P.IsMaximal] (hsep : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (m i : ℤ) (hm : 0 < m) (y : Ht q (sp B) m i) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D),
      Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧
      pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  obtain ⟨O, _, _, hSH, hInd, hO⟩ := GlobalTheory.T.exists_strictHenselization_at_maximal B P hsep
  have hsub : Subsingleton (Ht q (sp O) m i) := GlobalTheory.EtC.b2 (ZMod q) O hSH (tw q i) m hm
  have h0 : pull _ (spMap (algebraMap B O)) _ _ y = 0 := Subsingleton.elim _ _
  obtain ⟨D, _, _, _, φ, hD⟩ := GlobalTheory.T.vanishes_on_etale_neighbourhood q B O hq hInd m i y h0
  obtain ⟨hH, -⟩ := hSH
  haveI : IsLocalRing O := hH.toIsLocalRing
  obtain ⟨hP, hres⟩ := hO (IsLocalRing.maximalIdeal O) inferInstance
  refine ⟨D, inferInstance, inferInstance, inferInstance, (IsLocalRing.maximalIdeal O).comap φ, ?_, ?_, ?_, hD⟩
  · exact Ideal.comap_isPrime _ _
  · rw [← hP]
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  · intro d
    obtain ⟨b, hb⟩ := hres (φ d)
    refine ⟨b, ?_⟩
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes]
    exact hb

end GlobalTheory.EtC.OneCoh

/- English proof (translation)
Introduce `q _ B _ hq P _ hsep m i hm y` and use `GlobalTheory.EtC.OneCoh.dies_on_etale_with_point q B hq P hsep m i hm y`.
-/
theorem GlobalTheory.EtC.oneCoh_main : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 :=
  fun q _ B _ hq P _ hsep m i hm y => GlobalTheory.EtC.OneCoh.dies_on_etale_with_point q B hq P hsep m i hm y
