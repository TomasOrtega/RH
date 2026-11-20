import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarboux

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigSeesaw

open GlobalTheory.RouteSeesaw

/- English proof (translation)
Take `⟨φ', c1, q1, m1, s1, d1⟩` from `GlobalTheory.GrpConj.exists_conj_equiv D S T' e₁ hT'`. Take `⟨φ, c2, q2, m2, s2, d2⟩` from `GlobalTheory.InvTransposeIso.grp_contra D T S' e₂ hS'`. Take `⟨L, hL, hLs, cL, cL', rL, iL, fL⟩` from `GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D S T S' T' e₁ e₂`. Establish `m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁` using `fun h => by`. Use extensionality with `i j`.

Establish `t3` using `congrArg (cA D) (congrFun (congrFun (m1 h) i) j)`. Simplify using `only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3`. Conclude with `t3.symm`. Establish `hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)`. Introduce `g h x`.

Establish `u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) = S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹`. Establish `k` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)`. Establish `k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1`. Simplify using `only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]`. Establish `k3` using `congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k`.

Simplify using `only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3`. Conclude with `k3`. Establish `u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm`. Rewrite using `[← m2]`. Simplify using the standard rewrite rules.

Establish `u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ`. Rewrite using `[m1']`. Simplify using the standard rewrite rules. Rewrite using `[hL]`. Unfold `actO`.

Rewrite using `[hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm, ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]`. Simplify using `only [Matrix.mul_assoc, u1]`. Establish `hs : ∀ x y, symplO S T (L x) (L y) = symplO S' T' x y` using `fun x y => by`. Rewrite using `[hL, hL]`. Conclude with `GlobalTheory.DarbouxSymp.symplO_darboux D S T S' T' e₁ e₂ hT' hS' x y`.

Take `⟨ω', hw, hω'⟩` from `GlobalTheory.SwapWeil.isWeilDatumO_swap D ψ S T S' T' (by simpa using Fintype.card_congr e₂) (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom φ'.toMonoidHom cL cL' rL hs iL fL c2 c1 q2 q1 hact s2 s1 d2 d1 χS χT ω hω`. Establish `th : IsThetaFunO ψ S' T' (fun w => f (L w))` using `GlobalTheory.SwapWeil.theta_pull L cL (fun x hx => (rL x).2 hx) hs (fun x hx => (iL x).2 hx) (fun x hx => (fL x).2 hx) hf`. Establish `a1 : φ' h' = g`. Establish `k : h' = φ'.symm g` using `GlobalTheory.MixModel.mt_injective T' (by rw [hh, m1', MulEquiv.apply_symm_apply])`. Rewrite using `[k, MulEquiv.apply_symm_apply]`.

Establish `a2 : φ g' = h`. Establish `k : g' = φ.symm h` using `GlobalTheory.MixModel.mt_injective S' (by`. Use `m2 (φ.symm h)⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv, map_inv, MulEquiv.apply_symm_apply]`. Rewrite using `[hg, this, Matrix.transpose_transpose])`.

Rewrite using `[k, MulEquiv.apply_symm_apply]`. Establish `k9` using `congrFun (hω' g' h' f) 0`. Simplify using `only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, a1, a2, map_zero] at k9`. Simplify using `only [← hL]`. Rewrite using `[GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std S' T' χT χS ω₀ ω' hω₀ hw (g', h') _ th]`.

Conclude with `k9`.
-/
theorem swap_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω)
    {ω₀ : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hω₀ : IsWeilDatumO ψ S' T' χT χS ω₀)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (g : GA D S) (h : GA D T) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt S g).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt T h⁻¹).submatrix e₂ e₂)ᵀ) :
    ω₀ (g', h') (fun u => f (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D))) 0 = ω (g, h) f 0 := by
  obtain ⟨φ', c1, q1, m1, s1, d1⟩ := GlobalTheory.GrpConj.exists_conj_equiv D S T' e₁ hT'
  obtain ⟨φ, c2, q2, m2, s2, d2⟩ := GlobalTheory.InvTransposeIso.grp_contra D T S' e₂ hS'
  obtain ⟨L, hL, hLs, cL, cL', rL, iL, fL⟩ := GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D S T S' T' e₁ e₂
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
  have hs : ∀ x y, symplO S T (L x) (L y) = symplO S' T' x y := fun x y => by
    rw [hL, hL]; exact GlobalTheory.DarbouxSymp.symplO_darboux D S T S' T' e₁ e₂ hT' hS' x y
  obtain ⟨ω', hw, hω'⟩ := GlobalTheory.SwapWeil.isWeilDatumO_swap D ψ S T S' T' (by simpa using Fintype.card_congr e₂)
    (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom
    φ'.toMonoidHom cL cL' rL hs iL fL c2 c1 q2 q1 hact s2 s1 d2 d1 χS χT ω hω
  have th : IsThetaFunO ψ S' T' (fun w => f (L w)) :=
    GlobalTheory.SwapWeil.theta_pull L cL (fun x hx => (rL x).2 hx) hs (fun x hx => (iL x).2 hx) (fun x hx => (fL x).2 hx) hf
  have a1 : φ' h' = g := by
    have k : h' = φ'.symm g := GlobalTheory.MixModel.mt_injective T' (by rw [hh, m1', MulEquiv.apply_symm_apply])
    rw [k, MulEquiv.apply_symm_apply]
  have a2 : φ g' = h := by
    have k : g' = φ.symm h := GlobalTheory.MixModel.mt_injective S' (by
      have := m2 (φ.symm h)⁻¹
      rw [inv_inv, map_inv, MulEquiv.apply_symm_apply] at this
      rw [hg, this, Matrix.transpose_transpose])
    rw [k, MulEquiv.apply_symm_apply]
  have k9 := congrFun (hω' g' h' f) 0
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, a1, a2, map_zero] at k9
  simp only [← hL]
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std S' T' χT χS ω₀ ω' hω₀ hw (g', h') _ th]
  exact k9

/- English proof (translation)
Establish `h2` using `GlobalTheory.RouteCoords.inv_mul_gram S`. Establish `h3 : (((negSp S).gram.map (incA D)).map (cA D))ᵀ = -(S.gram.map (incA D))`. Rewrite using `[GlobalTheory.RouteCoords.gram_conj_transpose, negSp_gram, Matrix.map_neg _ (map_neg _)]`. Unfold `adjM`. Rewrite using `[Matrix.map_mul, transpose_mul, h3, transpose_map, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_neg, h2, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]`.

Both sides reduce to the same expression.
-/
theorem adjM_mul_neg {D : D7} (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ ((negSp S).gram.map (incA D)) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) =
      -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have h2 := GlobalTheory.RouteCoords.inv_mul_gram S
  have h3 : (((negSp S).gram.map (incA D)).map (cA D))ᵀ = -(S.gram.map (incA D)) := by
    rw [GlobalTheory.RouteCoords.gram_conj_transpose, negSp_gram, Matrix.map_neg _ (map_neg _)]
  unfold adjM
  rw [Matrix.map_mul, transpose_mul, h3, transpose_map, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_neg, h2,
    Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T L sc G W t i j M e Bs Γ X om om' h hTr hT₁ hT₂ LT hLT hUT sgT hS₁ hS₂ LS hLS hUS sgS ω hω g g₁`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Establish `h1` using `W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)`. Establish `h2` using `W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)`.

Take `⟨ω₂, hω₂, hadj⟩` from `GlobalTheory.SquareDict.ExactBig.adjoint_exact h2`. Establish `hcard : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank`. Simplify using `using Fintype.card_congr e`. Establish `pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2`. Establish `hev` using `hTr.geo.even`.

Rewrite `hev` using `[← hcard, Nat.even_iff]`. Simplify using `only [spV, spV₁] at hev`. Use linear arithmetic over natural numbers and integers. Establish `cT : X.β / X.α = G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹`. Rewrite using `[h.α, h.β]`.

Simplify using `only [GridData.chrT, GridData.chrS, GridData.chr, GlobalTheory.SquareDict.ExactBig.attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]`. Rewrite using `[pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]`. Take `⟨ωA, hA⟩` from `GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) X.β (G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹) (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT (hecke_mul' h1.hecT hω₂. …`. Take `⟨x, hx⟩` from `GlobalTheory.RecDict.exists_isDetRoot D _ g`. Take `⟨y, hy⟩` from `GlobalTheory.RecDict.exists_isDetRoot D _ g₁`.

Use `⟨(((G.chrS (.chi i (j + 1)) / X.β) x : Circle) : ℂ) * ((((G.chrT (.mu t (i + 1) j))⁻¹ / X.β) y : Circle) : ℂ), mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _), fun f₁ f₂ hf₁ hf₂ u g' h' hh hg => ?_⟩` and prove the remaining obligations. Establish `k` using `GlobalTheory.SquareDict.ExactBig.seesaw_exact h1 hω₂ hA hf₁ (hadj _ hf₂).1 (negGA _ u) g g₁ hx hy`. Rewrite `k` using `[(hadj _ hf₂).2]`. Use `k.trans ?_` and prove the remaining obligations. Use `congr 1`.

Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`. Set `e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank)` to `e.symm.trans finSumFinEquiv`. Establish `hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R) (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R), (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugati …` using `fun A B => by`. Use extensionality with `a b`. Simplify using `[GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]`.

Establish `hJ : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂`. Use `h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]`. Both sides reduce to the same expression. Establish `hJu : IsUnit Γ.W.J.det`.

Rewrite using `[hJ, det_smul, det_submatrix_equiv_self, det_transpose]`. Conclude with `(IsUnit.mk0 _ (pow_ne_zero _ hξ)).mul (GlobalTheory.MixModel.gram_isUnit_det _)`. Establish `e0 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J` using `Matrix.inv_eq_left_inv (by`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJu, inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])`. Establish `hT' : (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT).gramᵀ = -((negSp (spW G i j)).gram.submatrix (Equiv.refl _) (Equiv.refl _))`.

Rewrite using `[GlobalTheory.WeilSchrodinger.gram_hspOf, negSp_gram]`. Use `show Γ.V.J = - -(spW G i j).gram`. Rewrite using `[h.JW, one_smul, neg_neg]`. Establish `hS' : (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS).gram⁻¹ = -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂)`. Rewrite using `[GlobalTheory.WeilSchrodinger.gram_hspOf]`.

Use `e0.trans ?_` and prove the remaining obligations. Rewrite using `[hJ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]`. Establish `hbox : IsThetaFunO W.ψ (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (box2 (S` using `negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) f₁ (fun y => f₂ (adjM (spW G i j) (spV₁ G i j) y))) := by`. Rewrite using `[← GlobalTheory.SeesawSumTarget.boxT_sumDec]`. Conclude with `(GlobalTheory.BiTransfer.sumDec _ _).isThetaFunO_boxT hf₁ (hadj _ hf₂).1`.

Establish `hω'` using `hω`. Rewrite `hω'` using `[cT]`. Establish `key` using `swap_eq (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (Equiv.refl (Fin (spW G i j).rank)) e₂ hT' hS' hA hω' hbox (negGA _ u) …`. Rewrite using `[hg, ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]`. Conclude with `congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)`.

Use `key.symm.trans (congrArg (fun F => ω (g', h') F 0) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Establish `k1 : ∀ a, e₂.symm (Fin.castAdd _ a) = e (.inl a)` using `fun a => congrArg e (finSumFinEquiv_symm_apply_castAdd a)`. Establish `k2 : ∀ a, e₂.symm (Fin.natAdd _ a) = e (.inr a)` using `fun a => congrArg e (finSumFinEquiv_symm_apply_natAdd a)`. Use `congrArg₂ (· * ·) (congrArg f₁ ?_) (congrArg f₂ ?_)` and prove the remaining obligations.

Use extensionality with `a b`. Conclude with `Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ => congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k1 a)`. Use `Eq.trans (congrArg (adjM (spW G i j) (spV₁ G i j)) ?_) (adjM_mul_neg (spW G i j) (spV₁ G i j) (z.submatrix id fun k => e (.inr k)))` and prove the remaining obligations. Use extensionality with `a b`. Conclude with `Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ => congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k2 a)`.
-/
theorem seesaw_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : IsTripleOf W M t i j e Bs Γ X) (hTr : IsTriple Bs Γ X om om')
    (hT₁ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).IsSymm) (hT₂ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).Nondegenerate)
    (LT : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E)) (hLT : LT.IsLattice D.host.E)
    (hUT : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ) LT) (sgT : (D.host.E →+* ℂ) → ℕ × ℕ)
    (hS₁ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).IsSymm)
    (hS₂ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).Nondegenerate)
    (LS : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E)) (hLS : LS.IsLattice D.host.E)
    (hUS : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)) LS) (sgS : (D.host.E →+* ℂ) → ℕ × ℕ)
    (ω : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) × GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) →*
      Module.End ℂ (WO (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) → ℂ))
    (hω : IsWeilDatumO W.ψ (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS)
      (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (X.β / X.α) X.β ω)
    (g : GA D (spV G i j)) (g₁ : GA D (spV₁ G i j)), ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ (f₁ : WO (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) → ℂ)
      (f₂ : WO (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) → ℂ),
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) f₁ →
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) f₂ →
      ∀ (u : GA D (spW G i j)) (g' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS))
        (h' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)),
      Formalism.L2.Theta.mt _ h' = (conjU (spW G i j) 1 h.JW u).1.1 → Formalism.L2.Theta.mt _ g' = ((blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))⁻¹).1.1ᵀ →
      W.kerA (.right i (j + 1)) f₁ g u * W.kerA (.down t (i + 1) j) f₂ u g₁ =
        ξ * ω (g', h') (fun x => f₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ) *
          f₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x)) 0 := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr hT₁ hT₂ LT hLT hUT sgT hS₁ hS₂ LS hLS hUS sgS ω hω g g₁
  have hi := i.2
  have hj := j.2
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := GlobalTheory.SquareDict.ExactBig.adjoint_exact h2
  have hcard : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    simpa using Fintype.card_congr e
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    have hev := hTr.geo.even
    rw [← hcard, Nat.even_iff] at hev
    simp only [spV, spV₁] at hev
    omega
  have cT : X.β / X.α = G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    rw [h.α, h.β]
    simp only [GridData.chrT, GridData.chrS, GridData.chr, GlobalTheory.SquareDict.ExactBig.attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (negSp (spW G i j))
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) X.β (G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT (hecke_mul' h1.hecT hω₂.hecT) hω.resT
    (resEta_mul h1.resT hω₂.resT)
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g₁
  refine ⟨(((G.chrS (.chi i (j + 1)) / X.β) x : Circle) : ℂ) * ((((G.chrT (.mu t (i + 1) j))⁻¹ / X.β) y : Circle) : ℂ),
    mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _), fun f₁ f₂ hf₁ hf₂ u g' h' hh hg => ?_⟩
  have k := GlobalTheory.SquareDict.ExactBig.seesaw_exact h1 hω₂ hA hf₁ (hadj _ hf₂).1 (negGA _ u) g g₁ hx hy
  rw [(hadj _ hf₂).2] at k
  refine k.trans ?_
  congr 1
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hJu : IsUnit Γ.W.J.det := by
    rw [hJ, det_smul, det_submatrix_equiv_self, det_transpose]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hξ)).mul (GlobalTheory.MixModel.gram_isUnit_det _)
  have e0 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT).gramᵀ =
      -((negSp (spW G i j)).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf, negSp_gram]
    show Γ.V.J = - -(spW G i j).gram
    rw [h.JW, one_smul, neg_neg]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e0.trans ?_
    rw [hJ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]
  have hbox : IsThetaFunO W.ψ (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
      (box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) f₁
        (fun y => f₂ (adjM (spW G i j) (spV₁ G i j) y))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec _ _).isThetaFunO_boxT hf₁ (hadj _ hf₂).1
  have hω' := hω
  rw [cT] at hω'
  have key := swap_eq (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
    (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)
    (Equiv.refl (Fin (spW G i j).rank)) e₂ hT' hS' hA hω'
    hbox (negGA _ u) (GlobalTheory.SquareComm.blk _ _ (g, g₁)) g' h' hh (by
      rw [hg, ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine key.symm.trans (congrArg (fun F => ω (g', h') F 0) ?_)
  funext z
  have k1 : ∀ a, e₂.symm (Fin.castAdd _ a) = e (.inl a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_castAdd a)
  have k2 : ∀ a, e₂.symm (Fin.natAdd _ a) = e (.inr a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_natAdd a)
  refine congrArg₂ (· * ·) (congrArg f₁ ?_) (congrArg f₂ ?_)
  · ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k1 a)
  · refine Eq.trans (congrArg (adjM (spW G i j) (spV₁ G i j)) ?_)
      (adjM_mul_neg (spW G i j) (spV₁ G i j) (z.submatrix id fun k => e (.inr k)))
    ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k2 a)

end GlobalTheory.BigSeesaw

end
