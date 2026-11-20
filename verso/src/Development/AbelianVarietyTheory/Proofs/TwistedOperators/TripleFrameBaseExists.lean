import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInvStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplectiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarbouxStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model)
open GlobalTheory.WeilSchrodinger

/- English proof (translation)
Take `⟨φ', c1, q1, m1, s1, d1⟩` from `GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg D S T' e₁ hT'`. Take `⟨φ, c2, q2, m2, s2, d2⟩` from `GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv D T S' e₂ hS'`. Take `⟨L, hL, hLs, cL, cL', rL, iL, fL⟩` from `GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic D S T S' T' e₁ e₂`. Establish `m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁` using `fun h => by`. Use extensionality with `i j`.

Establish `t3` using `congrArg (cA D) (congrFun (congrFun (m1 h) i) j)`. Simplify using `only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3`. Conclude with `t3.symm`. Establish `hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)`. Introduce `g h x`.

Establish `u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) = S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹`. Establish `k` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)`. Establish `k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1`. Simplify using `only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]`. Establish `k3` using `congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k`.

Simplify using `only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3`. Conclude with `k3`. Establish `u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm`. Rewrite using `[← m2]`. Simplify using the standard rewrite rules.

Establish `u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ`. Rewrite using `[m1']`. Simplify using the standard rewrite rules. Rewrite using `[hL]`. Unfold `actO`.

Rewrite using `[hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm, ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]`. Simplify using `only [Matrix.mul_assoc, u1]`. Take `⟨ω', hw, hω'⟩` from `GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv D ψ S T S' T' (by simpa using Fintype.card_congr e₂) (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom φ'.toMonoidHom cL cL' rL (fun x y => by rw [hL, hL]; exact GlobalTheory.T.symplectic_hom_transpose_gram_darb …`. Use `⟨ω', hw, fun g h => ⟨φ.symm h, φ'.symm g, ?_, ?_, fun f x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[m1', MulEquiv.apply_symm_apply]`.

Use `m2 (φ.symm h)⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv, map_inv, MulEquiv.apply_symm_apply]`. Rewrite using `[this, Matrix.transpose_transpose]`. Establish `k9` using `congrFun (hω' (φ.symm h) (φ'.symm g) (fun x => f (L.symm x))) (L.symm x)`. Simplify using `only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply] at k9`.

Simplify using `only [← hLs]`. Conclude with `k9`.
-/
theorem exists_swap {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
      ∀ (g : GA D S) (h : GA D T), ∃ (g' : GA D S') (h' : GA D T'),
        Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt S g).map (cA D)).submatrix e₁ e₁ ∧
        Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt T h⁻¹).submatrix e₂ e₂)ᵀ ∧
        ∀ (f : WO S' T' → ℂ) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)),
          ω' (g', h') f (((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) =
          ω (g, h) (fun y : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
            f (((HMul.hMul y ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂)) x := by
  obtain ⟨φ', c1, q1, m1, s1, d1⟩ := GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg D S T' e₁ hT'
  obtain ⟨φ, c2, q2, m2, s2, d2⟩ := GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv D T S' e₂ hS'
  obtain ⟨L, hL, hLs, cL, cL', rL, iL, fL⟩ := GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic D S T S' T' e₁ e₂
  have m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁ := fun h => by
    ext i j
    have t3 := congrArg (cA D) (congrFun (congrFun (m1 h) i) j)
    simp only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3
    exact t3.symm
  have hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x) := by
    intro g h x
    have u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) =
        S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹ := by
      have k := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)
      have k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1 := by
        simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
      have k3 := congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k
      simp only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3
      exact k3
    have u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm := by
      rw [← m2]; simp
    have u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ := by
      rw [m1']; simp
    rw [hL]
    unfold actO
    rw [hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm,
      ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]
    simp only [Matrix.mul_assoc, u1]
  obtain ⟨ω', hw, hω'⟩ := GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv D ψ S T S' T' (by simpa using Fintype.card_congr e₂)
    (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom
    φ'.toMonoidHom cL cL' rL (fun x y => by rw [hL, hL]; exact GlobalTheory.T.symplectic_hom_transpose_gram_darboux D S T S' T' e₁ e₂ hT' hS' x y) iL fL c2 c1 q2 q1
    hact s2 s1 d2 d1 χS χT ω hω
  refine ⟨ω', hw, fun g h => ⟨φ.symm h, φ'.symm g, ?_, ?_, fun f x => ?_⟩⟩
  · rw [m1', MulEquiv.apply_symm_apply]
  · have := m2 (φ.symm h)⁻¹
    rw [inv_inv, map_inv, MulEquiv.apply_symm_apply] at this
    rw [this, Matrix.transpose_transpose]
  · have k9 := congrFun (hω' (φ.symm h) (φ'.symm g) (fun x => f (L.symm x))) (L.symm x)
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.apply_symm_apply] at k9
    simp only [← hLs]
    exact k9

/- English proof (translation)
Establish `hψ` using `hw.std`. Establish `hS` using `hw.hecS`. Establish `hT` using `hw.hecT`. Establish `rS` using `hw.resS`. Establish `rT` using `hw.resT`.

Take `⟨om, hom⟩` from `GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw`. Establish `k2` using `GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`. Establish `k3` using `GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`. Establish `k4` using `GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`. Establish `k5` using `GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`.

Establish `k6` using `GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`. Establish `k7` using `GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom`. Establish `hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ Mo.co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om` using `⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩`. Conclude with `⟨om, ⟨⟨isUSplitting_inr hsp, k6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, k7⟩, k5⟩, hom⟩`.
-/
theorem exists_transport_isWeil {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D) (Y : Spc D.host.F D.host.E T.rank)
    (Z : Spc D.host.F D.host.E S.rank) (eA : Y.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Z.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig Y Z) (hMo : Mo.IsGood ψ) {χ χ' : (AE D)ˣ →* Circle}
    {ω' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : IsWeilDatumO ψ S T χ' χ ω') :
    ∃ om, Mo.IsWeil ψ χ χ' om ∧ IsTransport ψ Mo.co ω' om := by
  have hψ := hw.std
  have hS := hw.hecS
  have hT := hw.hecT
  have rS := hw.resS
  have rT := hw.resT
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw
  have k2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have k3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have k4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have k5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have k6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have k7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D ψ hψ S T χ' χ hS hT rS rT Y.J Z.J (-1) eA eB _ Mo.co hMo.rat ω' hw om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ Mo.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩
  exact ⟨om, ⟨⟨isUSplitting_inr hsp, k6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, k7⟩, k5⟩, hom⟩

/- English proof (translation)
Establish `hω' : IsWeilDatumO B.ψ (sgn ε M) X χ χ' (ω.toSgn ε)` using `hω`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.WeilSchrodingerHerm.main D B hB _ Y r s hY`. Take `⟨hJ, Λ, hΛ, h4, h5, h6⟩` from `GlobalTheory.WeilSchrodingerSkew.main D B hB k Z r' s' hZ`. Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`. Set `T'` to `hspOf D Y.Jᵀ h1 h2 Y.L hY.lat h3 (fun _ => (r, s))`.

Set `S'` to `hspOf D (-D.host.xi0 • Z.J⁻¹) h4 h5 Λ hΛ h6 (fun _ => (s', r'))`. Establish `eA : Y.J = T'.gramᵀ` using `by rw [gram_hspOf]; rfl`. Establish `e0 : (-D.host.xi0 • Z.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Z.J` using `Matrix.inv_eq_left_inv (by`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ, inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])`. Establish `e1 : S'.gram⁻¹ = (-D.host.xi0)⁻¹ • Z.J`.

Rewrite using `[gram_hspOf]`. Conclude with `e0`. Establish `eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Z.J = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S'.gram⁻¹)`. Establish `e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Z.J = -Z.J`. Rewrite using `[smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]`.

Rewrite using `[e1]`. Use `show _ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0)⁻¹ • Z.J)`. Rewrite using `[e2]`. Use function extensionality and compare the values at `i j`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]`.

Establish `hT' : T'.gramᵀ = -((sgn ε M).gram.submatrix (Equiv.refl _) (Equiv.refl _))` using `by rw [← eA, eY, hc]; rfl`. Establish `hS' : S'.gram⁻¹ = -(X.gramᵀ.submatrix e e)`. Rewrite using `[e1, eZ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]`. Take `⟨ω', hw, hr⟩` from `exists_swap (sgn ε M) X S' T' (Equiv.refl _) e hT' hS' hω'`. Take `⟨om, hom, htr⟩` from `exists_transport_isWeil S' T' Y Z eA eB Mo hMo hw`.

Use `⟨om, hom, fun Φ hΦ g h => ?_⟩` and prove the remaining obligations. Take `⟨g', h', a1, a2, a3⟩` from `hr ((ofSgn ε M).symm g) h`. Establish `key` using `(htr (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c eY g) (GlobalTheory.TripleRead.toUX X e eZ h) g' h' a1 a2 Φ hΦ).2`. Use function extensionality and compare the values at `x`. Set `f : Matrix (Fin M.rank) (Fin k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) → ℂ` to `thetaTr D.host.F Mo.co B.ψ Φ`.

Conclude with `(congrFun key _).trans (a3 f x)`.
-/
theorem exists_weil {D : D7} (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig) (ε : Bool) (M X : HSp D) {k : ℕ}
    (e : Fin k ≃ Fin X.rank) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E k) {r s r' s' : ℕ}
    (hY : Y.IsHerm D.sp.cm.sig B r s) (hZ : Z.IsSkew D.sp.cm.sig B r' s') (c : D.host.E) (eY : Y.J = c • M.gram)
    (hc : c • M.gram = -(sgn ε M).gram) (eZ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (Mo : Model D.sp.cm.sig Y Z) (hMo : Mo.IsGood B.ψ) {χ χ' : (AE D)ˣ →* Circle} {ω : WRep M X}
    (hω : IsWeil B.ψ ε M X χ χ' ω) :
    ∃ om, Mo.IsWeil B.ψ χ χ' om ∧ GlobalTheory.TripleRead.IsTransp B.ψ ε Mo om ω e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c eY)
      (GlobalTheory.TripleRead.toUX X e eZ) := by
  have hω' : IsWeilDatumO B.ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D B hB _ Y r s hY
  obtain ⟨hJ, Λ, hΛ, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D B hB k Z r' s' hZ
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T' := hspOf D Y.Jᵀ h1 h2 Y.L hY.lat h3 (fun _ => (r, s))
  let S' := hspOf D (-D.host.xi0 • Z.J⁻¹) h4 h5 Λ hΛ h6 (fun _ => (s', r'))
  have eA : Y.J = T'.gramᵀ := by rw [gram_hspOf]; rfl
  have e0 : (-D.host.xi0 • Z.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Z.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have e1 : S'.gram⁻¹ = (-D.host.xi0)⁻¹ • Z.J := by
    rw [gram_hspOf]
    exact e0
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Z.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S'.gram⁻¹) := by
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Z.J = -Z.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    rw [e1]
    show _ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0)⁻¹ • Z.J)
    rw [e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hT' : T'.gramᵀ = -((sgn ε M).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by rw [← eA, eY, hc]; rfl
  have hS' : S'.gram⁻¹ = -(X.gramᵀ.submatrix e e) := by
    rw [e1, eZ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]
  obtain ⟨ω', hw, hr⟩ := exists_swap (sgn ε M) X S' T' (Equiv.refl _) e hT' hS' hω'
  obtain ⟨om, hom, htr⟩ := exists_transport_isWeil S' T' Y Z eA eB Mo hMo hw
  refine ⟨om, hom, fun Φ hΦ g h => ?_⟩
  obtain ⟨g', h', a1, a2, a3⟩ := hr ((ofSgn ε M).symm g) h
  have key := (htr (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c eY g) (GlobalTheory.TripleRead.toUX X e eZ h) g' h' a1 a2 Φ hΦ).2
  funext x
  let f : Matrix (Fin M.rank) (Fin k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) → ℂ := thetaTr D.host.F Mo.co B.ψ Φ
  exact (congrFun key _).trans (a3 f x)

end GlobalTheory.TripleDarboux

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

/- English proof (translation)
Establish `hfin` using `(GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D α h.hecA).union (GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D β h.hecB)`. Establish `hν : IsHeckeChar D (α / β)` using `⟨h.hecA.1.div' h.hecB.1, fun x => by rw [MonoidHom.div_apply, h.hecA.2, h.hecB.2, div_one]⟩`. Establish `hr : ResEta D (α / β) 0`. Use `resEta_mul h.resA (resEta_inv h.resB)` as an intermediate fact. Rewrite `this` using `[← div_eq_mul_inv]`.

Establish `h1` using `h.rank`. Take `⟨m, hm⟩` from `h.even`. Conclude with `resEta_parity this (by omega)`. Establish `key : ∀ v ∈ hfin.toFinset.image (fun w => w.under (𝓞 D.host.F)), ∃ ε, IsPlaceIdem D v ε ∧ ¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (α / β) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)`. Introduce `v hv`.

Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hv`. Take `⟨ε, hε⟩` from `GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))`. Use `⟨ε, hε, (h.ram _ ε hε).resolve_left fun hu => ?_⟩` and prove the remaining obligations. Break down `hfin.mem_toFinset.1 hw with hw | hw` into its components or cases. Conclude with `hw (GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.1 rfl)`.

Conclude with `hw (GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.2 rfl)`. Use `⟨hfin.toFinset.image (fun w => w.under (𝓞 D.host.F)), fun v hv => ?_, fun w hw hu => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨ε, h1, h2, -, h4⟩` from `key v hv`. Conclude with `⟨GlobalTheory.T.nonempty_algHom_completion_of_split_place D v ε h1 h2, h4⟩`. Take `⟨ε, h1, -, h3, -⟩` from `key _ hw`.

Conclude with `h3 (GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime D _ hν hr _ ε h1 w rfl hu)`. Assume the negation of the conclusion as `hn`. Use `hw (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ?_))` and prove the remaining obligations. Distinguish the cases in `ha : GlobalTheory.LFun.UnrAt α w`. Conclude with `Or.inr fun hb => hn ⟨ha, hb⟩`.

Conclude with `Or.inl ha`.
-/
theorem exists_ram_set {D : D7} {W W₁ X : HSp D} {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ T, Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) ∧
      (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ T → ¬ GlobalTheory.LFun.UnrAt (α / β) w) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ T → GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w := by
  classical
  have hfin := (GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D α h.hecA).union (GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places D β h.hecB)
  have hν : IsHeckeChar D (α / β) :=
    ⟨h.hecA.1.div' h.hecB.1, fun x => by rw [MonoidHom.div_apply, h.hecA.2, h.hecB.2, div_one]⟩
  have hr : ResEta D (α / β) 0 := by
    have := resEta_mul h.resA (resEta_inv h.resB)
    rw [← div_eq_mul_inv] at this
    have h1 := h.rank
    obtain ⟨m, hm⟩ := h.even
    exact resEta_parity this (by omega)
  have key : ∀ v ∈ hfin.toFinset.image (fun w => w.under (𝓞 D.host.F)), ∃ ε, IsPlaceIdem D v ε ∧
      ¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (α / β) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    refine ⟨ε, hε, (h.ram _ ε hε).resolve_left fun hu => ?_⟩
    rcases hfin.mem_toFinset.1 hw with hw | hw
    · exact hw (GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.1 rfl)
    · exact hw (GlobalTheory.BasePairChar.unrAt_of_unramAt hε hu.2 rfl)
  refine ⟨hfin.toFinset.image (fun w => w.under (𝓞 D.host.F)), fun v hv => ?_, fun w hw hu => ?_, fun w hw => ?_⟩
  · obtain ⟨ε, h1, h2, -, h4⟩ := key v hv
    exact ⟨GlobalTheory.T.nonempty_algHom_completion_of_split_place D v ε h1 h2, h4⟩
  · obtain ⟨ε, h1, -, h3, -⟩ := key _ hw
    exact h3 (GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime D _ hν hr _ ε h1 w rfl hu)
  · by_contra hn
    refine hw (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ?_))
    by_cases ha : GlobalTheory.LFun.UnrAt α w
    · exact Or.inr fun hb => hn ⟨ha, hb⟩
    · exact Or.inl ha

/- English proof (translation)
Take `⟨ν, 𝓕, hH, hfd⟩` from `GlobalTheory.Ker.HypModel.exists_haar_fundDom D M`. Take `⟨hH', hfd'⟩` from `GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M c hc eY _ _ hH hfd`. Take `⟨co, hrat⟩` from `GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood B hB Y Z r s r' s' hY hZ`. Establish `hind` using `GlobalTheory.VacIndic.eventually_isVac_indicator B hB Y Z r s r' s' hY hZ co hrat`. Establish `hany` using `GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB Y Z r s r' s' hY hZ co`.

Set `ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ` to `fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1`. Set `vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ` to `fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v else (hany v).choose`. Use `⟨⟨co, vac, _, _⟩, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩` and prove the remaining obligations. Use `show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (vac v)`. Distinguish the cases in `h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (ind v)`.

Simplify using `only [vac, if_pos h]`. Conclude with `h`. Simplify using `only [vac, if_neg h]`. Conclude with `(hany v).choose_spec`. Use `filter_upwards [hind] with v hv show vac v = ind v`.

Conclude with `if_pos hv`.
-/
theorem exists_model {D : D7} (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig) (M : HSp D) {k : ℕ}
    (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E k) {r s r' s' : ℕ}
    (hY : Y.IsHerm D.sp.cm.sig B r s) (hZ : Z.IsSkew D.sp.cm.sig B r' s') (c : D.host.E) (hc : c ≠ 0)
    (eY : Y.J = c • M.gram) : ∃ Mo : Model D.sp.cm.sig Y Z, Mo.IsGood B.ψ := by
  classical
  obtain ⟨ν, 𝓕, hH, hfd⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D M
  obtain ⟨hH', hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M c hc eY _ _ hH hfd
  obtain ⟨co, hrat⟩ := GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood B hB Y Z r s r' s' hY hZ
  have hind := GlobalTheory.VacIndic.eventually_isVac_indicator B hB Y Z r s r' s' hY hZ co hrat
  have hany := GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB Y Z r s r' s' hY hZ co
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ :=
    fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1
  let vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ :=
    fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v
      else (hany v).choose
  refine ⟨⟨co, vac, _, _⟩, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩
  · show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (vac v)
    by_cases h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := Y) (W := Z) co (fun _ => 0) 0 ∅) B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hany v).choose_spec
  · filter_upwards [hind] with v hv
    show vac v = ind v
    exact if_pos hv

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Use `⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩` and prove the remaining obligations. Use `congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Establish `hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q`.

Apply the tactic sequence `ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]`. Rewrite `this` using `[hJ]`. Conclude with `this`.
-/
theorem hasSignature_map_conj {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

/- English proof (translation)
Establish `hex : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ β` using `fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Λ (GlobalTheory.AdelicU.isCMExt_host D)`. Use `⟨fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, fun v => ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ (if h : v.1 ∈ B.P then (hex ⟨v, h⟩).choose else 1)`. Rewrite using `[dif_pos v.2]`. Conclude with `(hex v).choose_spec`.
-/
theorem exists_bas {D : D7} (B : Base D.host.F D.host.E) {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hΛ : Λ.IsLattice D.host.E) : ∃ bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin n) (Fv D.host.F v),
      ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ (bas v) := by
  classical
  have hex : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ β := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Λ (GlobalTheory.AdelicU.isCMExt_host D)
  refine ⟨fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, fun v => ?_⟩
  show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ (if h : v.1 ∈ B.P then (hex ⟨v, h⟩).choose else 1)
  rw [dif_pos v.2]
  exact (hex v).choose_spec

/- English proof (translation)
Establish `hsd` using `GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D S`. Establish `hlat` using `Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1`. Take `⟨bas, hbas⟩` from `exists_bas B _ hlat`. Establish `eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star)` using `fun w => by`. Use extensionality with `a b`.

Simplify using `[gramAt, hB]`. Use `⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩⟩` and prove the remaining obligations. Use `show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _`.

Rewrite using `[eJ]`. Conclude with `GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _`. Rewrite using `[eJ]`. Conclude with `GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)`.
-/
theorem exists_isHerm {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (S : HSp D) (s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D S τ) p q) :
    ∃ Λ bas, Spc.IsHerm D.sp.cm.sig B (Spc.mk ((-1 : D.host.E) • S.gram) Λ (fun w => -s (τf w)) bas) q p := by
  have hsd := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D S
  have hlat := Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star) := fun w => by
    ext a b; simp [gramAt, hB]
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩⟩
  · show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _
    rw [eJ]
    exact GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _
    rw [eJ]
    exact GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)

def zeroSp (D : D7) : HSp D :=
  GlobalTheory.WeilSchrodinger.hspOf D (0 : Matrix (Fin 0) (Fin 0) D.host.E) ⟨fun x y => by
               rw [Subsingleton.elim x 0, Subsingleton.elim y 0]; simp only [map_zero]⟩
    ⟨fun x _ => Subsingleton.elim _ _, fun x _ => Subsingleton.elim _ _⟩ ⊤
    ⟨by rw [Subsingleton.elim (⊤ : Submodule (𝓞 D.host.E) (Fin 0 → D.host.E)) ⊥]; exact Submodule.fg_bot,
      Subsingleton.elim _ _⟩ (Subsingleton.elim _ _) fun _ => (0, 0)

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem blk_empty {R : Type} [Zero R] {n k : ℕ} (e : Fin k ≃ Fin n) (A : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin 0) (Fin 0) R) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk ((Equiv.sumEmpty (Fin n) (Fin 0)).trans e.symm) A Z = A.submatrix e e := by
  ext a b; rfl

open scoped ComplexOrder in

/- English proof (translation)
Set `e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k` to `(Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm`. Establish `hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e'` using `congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm`. Establish `hA` using `GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D X`. Establish `hZ` using `GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)`. Establish `hlat` using `GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'`.

Take `⟨bas, hbas⟩` from `exists_bas B _ hlat`. Establish `hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ)` using `inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))`. Use `⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩⟩` and prove the remaining obligations. Use `show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))`. Rewrite using `[star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]`.

Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _`. Rewrite using `[hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]`. Apply the tactic sequence `have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 := ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩`. Conclude with `GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0`. Use `show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))`.

Rewrite using `[hJ]`. Conclude with `GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) (((s (τf w)).submatrix e e).map conj)`. Rewrite using `[hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]`. Establish `h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1` using `⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by`.

Rewrite using `[Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]`. Conclude with `Matrix.PosDef.one⟩`. Conclude with `GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0`.
-/
theorem exists_isSkew {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D X τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D X τ) p q) :
    ∃ Λ bas, Spc.IsSkew D.sp.cm.sig B (Spc.mk (D.host.xi0 • (X.gramᵀ).submatrix e e) Λ
      (fun w => ((s (τf w)).submatrix e e).map conj) bas) p q := by
  let e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k := (Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm
  have hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e' :=
    congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm
  have hA := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D X
  have hZ := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)
  have hlat := GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))
  refine ⟨_, bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩⟩
  · show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))
    rw [star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]
    have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 :=
      ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩
    exact GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0
  · show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E
      (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))
    rw [hJ]
    exact GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1)
      (((s (τf w)).submatrix e e).map conj)
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]
    have h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1 :=
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by
        rw [Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]; exact Matrix.PosDef.one⟩
    exact GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0

end GlobalTheory.TripleDarboux

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

/- English proof (translation)
Introduce `_ D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB`. Set `e : Fin (W.rank + W₁.rank) ≃ Fin X.rank` to `finCongr h.rank.symm`. Use `choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))`. Use `choose a b ha hb hab using h.gap`. Take `⟨mα, hα, eα⟩` from `GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf`.

Take `⟨mβ, hβ, eβ⟩` from `GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf`. Take `⟨T, hT1, hT2, hT3⟩` from `exists_ram_set h`. Take `⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩` from `exists_good_place D T`. Set `Bs : Base D.host.F D.host.E` to `⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.some, v₁, τ₁⟩`. Establish `hBs : Bs.IsGood D.sp.cm.sig` using `base_isGood Bs hψ fun v hv => (hT1 v hv).2`.

Establish `hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x)` using `fun _ _ => rfl`. Take `⟨p, q, hsig, hn1, hn2⟩` from `h.sig`. Establish `hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ` using `fun τ => by ext i j; simp [gramAt, neg_gram]`. Take `⟨ΛV, basV, hV⟩` from `exists_isHerm Bs τf hemb (sgn true W) (fun τ => sgnM true (A.cart τ)) (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ)) (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)`. Establish `eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram`.

Rewrite using `[neg_gram, neg_smul, one_smul, one_smul, neg_neg]`. Establish `eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w)` using `funext fun w => neg_neg _`. Rewrite `hV` using `[eJ, eθ]`. Take `⟨ΛV', basV', hV'⟩` from `exists_isHerm Bs τf hemb W₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁) fun τ => (hsig τ).2.1`. Take `⟨ΛX, basX, hX⟩` from `exists_isSkew Bs τf hemb X e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B) fun τ => (hsig τ).2.2`.

Establish `e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q)` using `by rw [h.rank]`. Rewrite `hX` using `[e3]`. Take `⟨Mo, hMo⟩` from `exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl`. Take `⟨Mo', hMo'⟩` from `exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl`. Take `⟨om, hom, htr⟩` from `exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA`.

Take `⟨om', hom', htr'⟩` from `exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB`. Establish `hr` using `h.rank`. Establish `hev` using `h.even`. Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `D.sp.cm.deg2`. Establish `hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T` using `by simp [Chars.T]`.

Use `⟨e, Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om', ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr'⟩` and prove the remaining obligations. Use `⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩` and prove the remaining obligations. Establish `h1` using `eα w`. Establish `h3` using `eβ w`. Establish `h4` using `hab (τf w)`.

Rewrite `h4` using `[hr]`. Establish `: (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ)`. Move the coercions through the operations in `at h4 ⊢`. Rewrite using `[h1, h3]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions. Take `⟨m, hm⟩` from `hev show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2`. Use linear arithmetic over natural numbers and integers. Use `⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA), GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _, hTe.le, fun w hw => hT2 w (hTe ▸ …` and prove the remaining obligations. Rewrite using `[hTe]`.

Conclude with `h0`. Rewrite using `[hTe]`. Conclude with `h0`.
-/
theorem exists_reading : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  intro _ D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB
  classical
  let e : Fin (W.rank + W₁.rank) ≃ Fin X.rank := finCongr h.rank.symm
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_ram_set h
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E :=
    ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.some, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨ΛV, basV, hV⟩ := exists_isHerm Bs τf hemb (sgn true W) (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨ΛV', basV', hV'⟩ := exists_isHerm Bs τf hemb W₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨ΛX, basX, hX⟩ := exists_isSkew Bs τf hemb X e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T := by simp [Chars.T]
  refine ⟨e, Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr'⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0

end GlobalTheory.TripleDarboux

end
