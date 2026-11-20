import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.MemIntAfAndInIdIffSplitComponents
import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdOverSplitPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Unfold `GlobalTheory.StdPairCone.stdB GlobalTheory.StdPairCone.unitInd`. Distinguish the cases in `h : (∀ i j, Y i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)`. Rewrite using `[if_pos h]`. Distinguish the cases in `h2 : (GlobalTheory.StdPairCone.blk₂ Y).det ≠ 0 ∧ ValuativeRel.valuation k (GlobalTheory.StdPairCone.blk₂ Y).det = 1`. Rewrite using `[dif_pos h2, dif_pos ⟨h2.1, ⟨fun i j => h.1 _ _, h2.2⟩, h.2⟩]`.

Rewrite using `[dif_neg h2, dif_neg fun h3 => h2 ⟨h3.1, h3.2.1.2⟩]`. Rewrite using `[if_neg h, dif_neg]`. Introduce and unpack `⟨-, h1, h2⟩`. Use `h ⟨fun i j => ?_, h2⟩` and prove the remaining obligations. Use `Fin.addCases (fun j => ?_) (fun j => h1.1 i j) j` and prove the remaining obligations.

Establish `h3 : ValuativeRel.valuation k (Y i (Fin.castAdd a' j)) ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k)` using `h2 i j`. Use `(Valuation.mem_integer_iff _ _).2 (h3.trans ?_)` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_le_one' hϖ c`.
-/
private theorem stdB_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) (c a a' : ℕ)
    (Y : Matrix (Fin a') (Fin (a + a')) k) :
    GlobalTheory.StdPairCone.stdB ν ϖ c a a' Y =
      if (∀ i j, Y i j ∈ (ValuativeRel.valuation k).integer) ∧
          ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (GlobalTheory.StdPairCone.blk₂ Y).det else 0 := by
  unfold GlobalTheory.StdPairCone.stdB GlobalTheory.StdPairCone.unitInd
  by_cases h : (∀ i j, Y i j ∈ (ValuativeRel.valuation k).integer) ∧
          ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos h]
    by_cases h2 : (GlobalTheory.StdPairCone.blk₂ Y).det ≠ 0 ∧ ValuativeRel.valuation k (GlobalTheory.StdPairCone.blk₂ Y).det = 1
    · rw [dif_pos h2, dif_pos ⟨h2.1, ⟨fun i j => h.1 _ _, h2.2⟩, h.2⟩]
    · rw [dif_neg h2, dif_neg fun h3 => h2 ⟨h3.1, h3.2.1.2⟩]
  · rw [if_neg h, dif_neg]
    rintro ⟨-, h1, h2⟩
    refine h ⟨fun i j => ?_, h2⟩
    refine Fin.addCases (fun j => ?_) (fun j => h1.1 i j) j
    have h3 : ValuativeRel.valuation k (Y i (Fin.castAdd a' j)) ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) := h2 i j
    refine (Valuation.mem_integer_iff _ _).2 (h3.trans ?_)
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' hϖ c

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem piW_cA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) :
    piW t (cA D w) = piW (t.comp D.sp.cm.sig) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e`. Simplify using the standard rewrite rules.
-/
private theorem piW_incA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (e : D.host.E) : piW t (incA D e) = t e := by
  change GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e
  simp

/- English proof (translation)
Establish `hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹`. Rewrite using `[Matrix.conjTranspose_nonsing_inv]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.DualPairCheck.gram_star A' j i`.

Establish `h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hG i) j`. Express the relevant statement in the definitionally equal form `piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)`. Rewrite using `[piW_incA', ← h]`.

Both sides reduce to the same expression. Establish `h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) = ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e`. Rewrite using `[← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]`. Both sides reduce to the same expression. Establish `h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E), ((M.map (incA D)).map (toEAf D)).map (piF t) = M.map t`. Introduce `p q M`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.map_apply, piF_toEAf, piW_incA']`. Establish `hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (piF t) = ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply, piF_toEAf, piW_cA']`. Establish `hxi : piF t (eToEAf D D.host.xi0) = t D.host.xi0`.

Rewrite using `[← piW_incA' t, ← piF_toEAf]`. Both sides reduce to the same expression. Establish `h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF t) = t D.host.xi0 • ((βA'⁻¹).1.map (piF t) * ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (piF t))`. Rewrite using `[← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Conclude with `map_mul (piF t) _ _`. Rewrite using `[h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]`. Simplify using `only [Pi.smul_apply]`. Use `congr 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
private theorem coord_eq {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (A' WW : HSp D) {d : ℕ} (e : Fin d ≃ Fin WW.rank)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) :
    (βA'⁻¹).1.map (piF t) * (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ * (βW.1.map (piF t)).submatrix e e =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF t)).submatrix id e := by
  have hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.DualPairCheck.gram_star A' j i
  have h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (congrFun hG i) j
    change piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)
    rw [piW_incA', ← h]
    rfl
  have h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) =
      ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e := by
    rw [← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]
    rfl
  have h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e := by
    refine Matrix.ext fun i j => ?_
    simp
  have hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E),
      ((M.map (incA D)).map (toEAf D)).map (piF t) = M.map t := by
    intro p q M
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, piF_toEAf, piW_incA']
  have hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (piF t) =
      ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.transpose_apply, piF_toEAf, piW_cA']
  have hxi : piF t (eToEAf D D.host.xi0) = t D.host.xi0 := by
    rw [← piW_incA' t, ← piF_toEAf]
    rfl
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF t) =
      t D.host.xi0 • ((βA'⁻¹).1.map (piF t) * ((A'.gram⁻¹).map t *
        ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (piF t)) := by
    rw [← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul]
    refine Matrix.ext fun i j => ?_
    exact map_mul (piF t) _ _
  rw [h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_assoc]
  rfl

/- English proof (translation)
Establish `h1 : e₀ • ((y : Matrix _ _ (AE D)).map (cA D))ᵀ = ((y : Matrix _ _ (AE D)).map (cA D))ᵀ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e₀ * cA D (y j i) = cA D (y j i)`. Use `conv_rhs => rw [← hy j i, map_mul, GlobalTheory.DualPairCheck.cA_cA]`. Establish `h2 : toEAf D e₀ • frMapAdj A' WW βA' βW y = frMapAdj A' WW βA' βW y`.

Unfold `frMapAdj`. Use `conv_rhs => rw [← h1, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul]`. Use `congr 2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Conclude with `(map_mul (toEAf D) _ _).symm`. Establish `h3 : toEAf D e₀ • GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord`. Rewrite using `[smul_comm, h2]`. Conclude with `congrFun (congrFun h3 i) j`.
-/
private theorem half_dual {D : D7} (e₀ : AE D) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) (hy : IsHalf (cA D e₀) y) (i j) :
    toEAf D e₀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j := by
  have h1 : e₀ • ((y : Matrix _ _ (AE D)).map (cA D))ᵀ = ((y : Matrix _ _ (AE D)).map (cA D))ᵀ := by
    refine Matrix.ext fun i j => ?_
    change e₀ * cA D (y j i) = cA D (y j i)
    conv_rhs => rw [← hy j i, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  have h2 : toEAf D e₀ • frMapAdj A' WW βA' βW y = frMapAdj A' WW βA' βW y := by
    unfold frMapAdj
    conv_rhs => rw [← h1, Matrix.mul_smul, Matrix.smul_mul]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    refine Matrix.ext fun i j => ?_
    exact (map_mul (toEAf D) _ _).symm
  have h3 : toEAf D e₀ • GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
    rw [smul_comm, h2]
  exact congrFun (congrFun h3 i) j

/- English proof (translation)
Introduce `D e₀ S hS P t hP ht ν c A' WW a hr βA' βW m hm`. Use `⟨fun v => Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹, fun y => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd`. Distinguish the cases in `hy : IsHalf (cA D e₀) y`. Use `swap`.

Rewrite using `[if_neg fun h => hy h.1, if_neg hy]`. Rewrite using `[if_pos hy]`. Establish `hc : ∀ v : P, GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank ((Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹).1 * (ptO (sgn false A').gram (finCongr hr) y).map (piW ((t v).comp D.sp.cm.sig)) * ((D.host.xi0 • (WW.gramᵀ).submatrix (finC …`. Introduce `v`. Rewrite using `[hm v, ← coord_eq]`.

Both sides reduce to the same expression. Use `Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (hc v).symm)` and prove the remaining obligations. Establish `hN` using `half_dual e₀ A' WW βA' βW y hy`. Generalize the expression as in `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = N at hN ⊢`. Establish `hI` using `fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)`.

Establish `hϖ : ∀ v : P, ValuativeRel.valuation (Fv D.host.F v) (unifAt v.1 : (Fv D.host.F v)ˣ) ≤ 1` using `fun v => (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec.mem`. Use `Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (stdB_eq _ _ (hϖ v) _ _ _ _).symm)` and prove the remaining obligations. Distinguish the cases in `h : IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)`. Establish `hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N = fun i j => N i (finCongr hr (Fin.natAdd a j))`. Use function extensionality and compare the values at `i j`.

Establish `hj : a + j.1 < WW.rank` using `hr ▸ Nat.add_lt_add_left j.2 a`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock`. Rewrite using `[dif_pos hj]`. Both sides reduce to the same expression. Rewrite using `[if_pos ⟨hy, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ _ (by rw [hb]; exact fun i j => h.1 _ _)]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos ⟨fun i j => (hI _ _).1.1 (h.1 _ _) v, fun i j => (hI _ _).2.1 (h.2 _ _ j.2) v⟩, hb]`. Both sides reduce to the same expression. Rewrite using `[if_neg fun h' => h h'.2]`. Use `symm`.

Assume the negation of the conclusion as `h0`. Use `h ⟨fun i j => (hI i j).1.2 fun v => ?_, fun i j hj => (hI i j).2.2 fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)`. Conclude with `(ite_ne_right_iff.1 h1).1.1 i ((finCongr hr).symm j)`. Establish `h1` using `Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)`.

Conclude with `(ite_ne_right_iff.1 h1).1.2 i ⟨j.1, hj⟩`.
-/
theorem UpperTheory.exists_gl_stdSnd_eq_product_local :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (A' WW : HSp D) (a : ℕ) (hr : a + A'.rank = WW.rank)
          (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (m : ∀ v : P, GL (Fin (a + A'.rank)) (Fv D.host.F v)),
        (∀ v, (m v).1 = (βW.1.map (piF (t v))).submatrix (finCongr hr) (finCongr hr)) →
        ∃ g : ∀ v : P, GL (Fin A'.rank) (Fv D.host.F v), ∀ y : WO A' WW,
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e₀ (∏ w ∈ S, w.asIdeal ^ c w) a A' WW βA' βW y =
            if IsHalf (cA D e₀) y then ∏ v : P, GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
              ((g v).1 * (ptO (sgn false A').gram (finCongr hr) y).map (piW ((t v).comp D.sp.cm.sig)) *
                ((D.host.xi0 • (WW.gramᵀ).submatrix (finCongr hr) (finCongr hr)).map (t v))ᵀ * (m v).1) else 0 := by
  intro D e₀ S hS P t hP ht ν c A' WW a hr βA' βW m hm
  refine ⟨fun v => Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹, fun y => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  by_cases hy : IsHalf (cA D e₀) y
  swap
  · rw [if_neg fun h => hy h.1, if_neg hy]
  rw [if_pos hy]
  have hc : ∀ v : P, GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
      ((Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹).1 *
        (ptO (sgn false A').gram (finCongr hr) y).map (piW ((t v).comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix (finCongr hr) (finCongr hr)).map (t v))ᵀ * (m v).1) =
      GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
        (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF (t v))).submatrix id (finCongr hr)) := by
    intro v
    rw [hm v, ← coord_eq]
    rfl
  refine Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (hc v).symm)
  have hN := half_dual e₀ A' WW βA' βW y hy
  generalize GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = N at hN ⊢
  have hI := fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)
  have hϖ : ∀ v : P, ValuativeRel.valuation (Fv D.host.F v) (unifAt v.1 : (Fv D.host.F v)ˣ) ≤ 1 := fun v =>
    (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec.mem
  refine Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (stdB_eq _ _ (hϖ v) _ _ _ _).symm)
  by_cases h : IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)
  · have hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N = fun i j => N i (finCongr hr (Fin.natAdd a j)) := by
      funext i j
      have hj : a + j.1 < WW.rank := hr ▸ Nat.add_lt_add_left j.2 a
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock
      rw [dif_pos hj]
      rfl
    rw [if_pos ⟨hy, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ _ (by rw [hb]; exact fun i j => h.1 _ _)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [if_pos ⟨fun i j => (hI _ _).1.1 (h.1 _ _) v, fun i j => (hI _ _).2.1 (h.2 _ _ j.2) v⟩, hb]
    rfl
  · rw [if_neg fun h' => h h'.2]
    symm
    by_contra h0
    refine h ⟨fun i j => (hI i j).1.2 fun v => ?_, fun i j hj => (hI i j).2.2 fun v => ?_⟩
    · have h1 := Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)
      exact (ite_ne_right_iff.1 h1).1.1 i ((finCongr hr).symm j)
    · have h1 := Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)
      exact (ite_ne_right_iff.1 h1).1.2 i ⟨j.1, hj⟩
