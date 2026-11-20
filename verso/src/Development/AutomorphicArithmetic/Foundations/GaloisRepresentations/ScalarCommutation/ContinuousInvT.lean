import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw invT_val invT_invT')
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_coe_inv.matrix_transpose`. Establish `e : (fun g : GL (Fin n) R => ((invT n R g)⁻¹ : GL (Fin n) R).val) = fun g => g.valᵀ`. Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv, invT_val, inv_inv]`.

Rewrite using `[e]`. Conclude with `Units.continuous_val.matrix_transpose`.
-/
private theorem continuous_invT' {n : ℕ} {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (invT n R : GL (Fin n) R → GL (Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · have e : (fun g : GL (Fin n) R => ((invT n R g)⁻¹ : GL (Fin n) R).val) = fun g => g.valᵀ := by
      funext g
      rw [← map_inv, invT_val, inv_inv]
    rw [e]
    exact Units.continuous_val.matrix_transpose

/- English proof (translation)
Introduce `E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ hq r W _ N _ _ L hw Ty hT`. Take `⟨q, hq, hgood, hqw⟩` from `hq`. Establish `hN : 0 < N.1` using `lt_of_lt_of_le (by norm_num) N.2.1`. Establish `hJ : ∀ y : GLw n w₀, y ∈ Ty.J ↔ invT n _ y ∈ V.J` using `fun y => hT.J_iff y _ (invT_val y)`. Establish `hJo : IsOpen (V.J : Set (GLw n w₀))` using `V.Kw0 ▸ V.shape.opn w₀ V.shape.mem`.

Establish `hJc : IsCompact (V.J : Set (GLw n w₀))` using `V.Kw0 ▸ V.shape.cpt w₀ V.shape.mem`. Use `⟨GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N.1 hN, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨K, hK, ho, hc, -⟩` from `hG E n N.1 hN w₀`. Use `⟨K, ho, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hT.L_eq, hT.K₀_eq]`.

Conclude with `hF E A n p S F ⟨w₀, hw⟩ _ (hT.fac _) q hq hgood hqw N.1 hN K hK`. Establish `e : (Ty.J : Set (GLw n w₀)) = invT n _ ⁻¹' (V.J : Set (GLw n w₀))` using `Set.ext hJ`. Rewrite using `[e]`. Conclude with `hJo.preimage continuous_invT'`. Establish `e : (Ty.J : Set (GLw n w₀)) = invT n _ '' (V.J : Set (GLw n w₀))`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨_, (hJ y).1 hy, invT_invT' y⟩`. Introduce and unpack `⟨y', hy', rfl⟩`.

Conclude with `(hJ _).2 (by rwa [invT_invT'])`. Rewrite using `[e]`. Conclude with `hJc.image continuous_invT'`. Establish `hc : Continuous (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J))` using `(continuous_invT'.comp continuous_subtype_val).subtype_mk _`. Establish `e : (Ty.ψ.ker : Set Ty.J) = (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) ⁻¹' {k : V.J | V.χ k = 1}`.

Use extensionality with `y`. Establish `h` using `hT.ψ_eq y ⟨invT n _ y.1, (hJ y.1).1 y.2⟩ (invT_val y.1)`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, h]`. Rewrite using `[e]`. Conclude with `V.ker_open.preimage hc`.

Introduce `σ v hv hσ`. Take `⟨σ', e, he, hcusp⟩` from `hC E n w₀ σ`. Use `hcusp (V.cusp σ' (e v) (fun h => hv (e.map_eq_zero_iff.1 h)) fun g => ?_)` and prove the remaining obligations. Establish `hg : invT n _ g.1 ∈ Ty.J` using `(hJ _).2 (by rw [invT_invT']; exact g.2)`. Establish `hval : (g : GLw n w₀).val = ((invT n _ g.1)⁻¹).valᵀ`.

Rewrite using `[← invT_val, invT_invT']`. Rewrite using `[he _ _ v hval, hσ ⟨_, hg⟩, map_smul, hT.ψ_eq ⟨_, hg⟩ g hval]`.
-/
private theorem tyTop_of (hF : KNFact) (hG : CongGrpEx) (hC : CuspTh) : TyTop := by
  intro E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ hq r W _ N _ _ L hw Ty hT
  obtain ⟨q, hq, hgood, hqw⟩ := hq
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  have hJ : ∀ y : GLw n w₀, y ∈ Ty.J ↔ invT n _ y ∈ V.J := fun y => hT.J_iff y _ (invT_val y)
  have hJo : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  have hJc : IsCompact (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.cpt w₀ V.shape.mem
  refine ⟨GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N.1 hN, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hK, ho, hc, -⟩ := hG E n N.1 hN w₀
    refine ⟨K, ho, hc, ?_⟩
    rw [hT.L_eq, hT.K₀_eq]
    exact hF E A n p S F ⟨w₀, hw⟩ _ (hT.fac _) q hq hgood hqw N.1 hN K hK
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ ⁻¹' (V.J : Set (GLw n w₀)) := Set.ext hJ
    rw [e]
    exact hJo.preimage continuous_invT'
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ '' (V.J : Set (GLw n w₀)) := by
      ext y
      constructor
      · intro hy
        exact ⟨_, (hJ y).1 hy, invT_invT' y⟩
      · rintro ⟨y', hy', rfl⟩
        exact (hJ _).2 (by rwa [invT_invT'])
    rw [e]
    exact hJc.image continuous_invT'
  · have hc : Continuous (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) :=
      (continuous_invT'.comp continuous_subtype_val).subtype_mk _
    have e : (Ty.ψ.ker : Set Ty.J) =
        (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) ⁻¹' {k : V.J | V.χ k = 1} := by
      ext y
      have h := hT.ψ_eq y ⟨invT n _ y.1, (hJ y.1).1 y.2⟩ (invT_val y.1)
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, h]
    rw [e]
    exact V.ker_open.preimage hc
  · intro σ v hv hσ
    obtain ⟨σ', e, he, hcusp⟩ := hC E n w₀ σ
    refine hcusp (V.cusp σ' (e v) (fun h => hv (e.map_eq_zero_iff.1 h)) fun g => ?_)
    have hg : invT n _ g.1 ∈ Ty.J := (hJ _).2 (by rw [invT_invT']; exact g.2)
    have hval : (g : GLw n w₀).val = ((invT n _ g.1)⁻¹).valᵀ := by
      rw [← invT_val, invT_invT']
    rw [he _ _ v hval, hσ ⟨_, hg⟩, map_smul, hT.ψ_eq ⟨_, hg⟩ g hval]

/- English proof (translation)
The claim follows from `tyTop_of (pKNFact (pKNIff (pLatCoord pRepLaws)) pFacEq (pAtApart pJEq) pCongGrpEx (pCongConj UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pLocComm UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pCongGrpEx pCuspTh`.
-/
theorem UpperTheory.Gal.Spc.tyTop :
    UpperTheory.Gal.Spc.TyTop :=
  tyTop_of (pKNFact (pKNIff (pLatCoord pRepLaws)) pFacEq (pAtApart pJEq) pCongGrpEx (pCongConj UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pLocComm
    UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pCongGrpEx pCuspTh
