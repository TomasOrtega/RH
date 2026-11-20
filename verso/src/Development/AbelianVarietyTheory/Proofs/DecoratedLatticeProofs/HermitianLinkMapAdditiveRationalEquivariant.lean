import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.LinkKappa

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem finPart_conj (z : AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `h1 : (adj z).map φ = 0`. Use function extensionality and compare the values at `i j`. Conclude with `hφ (z j i) (congrFun (congrFun hz j) i)`. Establish `h2` using `map_mul_eq_zero_right φ (giA S) (map_mul_eq_zero_left φ h1 (gA L))`. Use function extensionality and compare the values at `i j`.

Establish `h3 : φ ((giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0` using `congrFun (congrFun h2 i) j`. Use `show φ (incA D (-D.host.xi0⁻¹) * (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0`. Rewrite using `[map_mul, h3, mul_zero]`.
-/
theorem map_ofAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z.map φ = 0) : (ofAdj L S z).map φ = 0 := by
  have h1 : (adj z).map φ = 0 := by
    funext i j
    exact hφ (z j i) (congrFun (congrFun hz j) i)
  have h2 := map_mul_eq_zero_right φ (giA S) (map_mul_eq_zero_left φ h1 (gA L))
  funext i j
  have h3 : φ ((giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D (-D.host.xi0⁻¹) * (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]`.
-/
theorem trace_mul_smul_middle_eq_smul_trace {R : Type} [CommRing R] {m n : ℕ} (c : R) (a : Matrix (Fin m) (Fin m) R)
    (b : Matrix (Fin m) (Fin n) R) (g : Matrix (Fin n) (Fin n) R) (y : Matrix (Fin n) (Fin m) R) :
    (a ⬝ (b ⬝ ((c • g) ⬝ y))).trace = c * (a ⬝ (b ⬝ (g ⬝ y))).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) = incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L'`. Rewrite using `[gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]`. Conclude with `congrArg rat hτ`. Establish `h' : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = (incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L') ⬝ y`. Rewrite using `[← h, Matrix.mul_assoc, Matrix.mul_assoc]`.

Rewrite using `[hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]`. Simplify using `only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]`. Rewrite using `[trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h']`.

Establish `h0` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`. Establish `h1 : incA D c = incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * incA D (c * (D.host.xi0 * star D.host.xi0)))`. Rewrite using `[GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]`.

Clear the denominators using the available nonvanishing facts. Establish `h2` using `trace_mul_smul_middle_eq_smul_trace (R := AE D) (incA D (c * (D.host.xi0 * star D.host.xi0))) (giA S) (adj x) (gA L') y`. Rewrite using `[h1, mul_assoc, mul_assoc]`. Conclude with `congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2`.
-/
theorem hO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (c : D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (c * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    hO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = incA D c * hO S L' y x := by
  have h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) =
      incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L' := by
    rw [gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]; exact congrArg rat hτ
  have h' : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      (incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L') ⬝ y := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]
  simp only [Matrix.mul_assoc]
  rw [h']
  have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h1 : incA D c = incA D (-D.host.xi0⁻¹) *
      (cA D (incA D (-D.host.xi0⁻¹)) * incA D (c * (D.host.xi0 * star D.host.xi0))) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]
    congr 1
    rw [star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    field_simp
  have h2 := trace_mul_smul_middle_eq_smul_trace (R := AE D) (incA D (c * (D.host.xi0 * star D.host.xi0))) (giA S) (adj x) (gA L') y
  rw [h1, mul_assoc, mul_assoc]
  exact congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2

/- English proof (translation)
Rewrite using `[ofAdj, ofAdj, ofAdj, adj_add, Matrix.add_mul, Matrix.mul_add, smul_add]`.
-/
theorem ofAdj_add (L S : HSp D) (z z' : Mx D L.rank S.rank) : ofAdj L S (z + z') = ofAdj L S z + ofAdj L S z' := by
  rw [ofAdj, ofAdj, ofAdj, adj_add, Matrix.add_mul, Matrix.mul_add, smul_add]

/- English proof (translation)
Establish `h1 : Continuous fun z : Mx D L.rank S.rank => (adj z ⬝ gA L : Mx D S.rank L.rank)` using `continuous_adj.matrix_mul continuous_const`. Establish `h2 : Continuous fun z : Mx D L.rank S.rank => (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank)` using `continuous_const.matrix_mul h1`. Conclude with `h2.const_smul (incA D (-D.host.xi0⁻¹))`.
-/
theorem continuous_ofAdj (L S : HSp D) : Continuous (ofAdj L S) := by
  have h1 : Continuous fun z : Mx D L.rank S.rank => (adj z ⬝ gA L : Mx D S.rank L.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun z : Mx D L.rank S.rank => (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D (-D.host.xi0⁻¹))

/- English proof (translation)
The claim follows from `ratMx_smul _ (ratMx_mul (rat_mem S.gram⁻¹) (ratMx_mul (ratMx_adj hz) (rat_mem L.gram)))`.
-/
theorem ofAdj_mem (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z ∈ ratMx D L.rank S.rank) :
    ofAdj L S z ∈ ratMx D S.rank L.rank :=
  ratMx_smul _ (ratMx_mul (rat_mem S.gram⁻¹) (ratMx_mul (ratMx_adj hz) (rat_mem L.gram)))

/- English proof (translation)
Simplify using `only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]`.
-/
theorem mt_inv_ofAdj (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    mt S g⁻¹ ⬝ ofAdj L S z = ofAdj L S (z ⬝ mt S g) := by
  simp only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

/- English proof (translation)
Rewrite using `[← mt_inv_ofAdj, inv_inv]`.
-/
theorem ofAdj_mul_mt_inv (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    ofAdj L S (z ⬝ mt S g⁻¹) = mt S g ⬝ ofAdj L S z := by
  rw [← mt_inv_ofAdj, inv_inv]

/- English proof (translation)
Rewrite using `[symplO_eq, hO_ofAdj L L' S τ _ hτ, ← mul_neg, ← GlobalTheory.OrientedHeis.symplO_skew, symplO_eq, map_intCast, mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]`.
-/
theorem symplO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    symplO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = -((ε : AF D.host.F) * symplO S L' x y) := by
  rw [symplO_eq, hO_ofAdj L L' S τ _ hτ, ← mul_neg, ← GlobalTheory.OrientedHeis.symplO_skew, symplO_eq, map_intCast,
    mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

/- English proof (translation)
Introduce `D L L' S τ ε hτ κ hκ`. Use `⟨fun w w' => ?_, ?_, fun w hw => ?_, fun g w => ?_, fun w w' => ?_, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hκ, hκ, hκ, ← ofAdj_add]`. Conclude with `congrArg (ofAdj L S) (Matrix.mul_add (rat τ : Mx D L.rank L'.rank) w w')`. Establish `h : Continuous fun w : Mx D L'.rank S.rank => ((rat τ : Mx D L.rank L'.rank) ⬝ w : Mx D L.rank S.rank)` using `continuous_const.matrix_mul continuous_id`.

Rewrite using `[funext hκ]`. Conclude with `(continuous_ofAdj L S).comp h`. Rewrite using `[hκ]`. Conclude with `ofAdj_mem L S (ratMx_mul (rat_mem τ) hw)`. Rewrite using `[hκ, hκ, ← ofAdj_mul_mt_inv]`.

Conclude with `congrArg (ofAdj L S) (Matrix.mul_assoc (rat τ : Mx D L.rank L'.rank) w (mt S g⁻¹)).symm`. Rewrite using `[hκ, hκ]`. Conclude with `symplO_ofAdj L L' S τ ε hτ w w'`. Rewrite using `[hκ]`. Conclude with `map_ofAdj_eq_zero (infPart D) (fun z hz => by rw [infPart_conj, hz, map_zero]) L S (map_mul_eq_zero_right (infPart D) _ hw)`.

Rewrite using `[hκ]`. Conclude with `map_ofAdj_eq_zero (finPart D) (fun z hz => by rw [finPart_conj, hz, map_zero]) L S (map_mul_eq_zero_right (finPart D) _ hw)`.
-/
theorem kappa_props : ∀ (D : D7) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ), τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ κ : WO S L' → WO L S, (∀ w, κ w = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) → (∀ w w', κ (w + w') = κ w + κ w') ∧ Continuous κ ∧ (∀ w ∈ ratMx D L'.rank S.rank, κ w ∈ ratMx D S.rank L.rank) ∧ (∀ (g : GA D S) (w : WO S L'), κ (w ⬝ mt S g⁻¹) = mt S g ⬝ κ w) ∧ (∀ w w', symplO L S (κ w) (κ w') = -((ε : AF D.host.F) * symplO S L' w w')) ∧ (∀ w, (w.map (infPart D) = 0 → (κ w).map (infPart D) = 0) ∧ (w.map (finPart D) = 0 → (κ w).map (finPart D) = 0)) := by
  intro D L L' S τ ε hτ κ hκ
  refine ⟨fun w w' => ?_, ?_, fun w hw => ?_, fun g w => ?_, fun w w' => ?_, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [hκ, hκ, hκ, ← ofAdj_add]
    exact congrArg (ofAdj L S) (Matrix.mul_add (rat τ : Mx D L.rank L'.rank) w w')
  · have h : Continuous fun w : Mx D L'.rank S.rank => ((rat τ : Mx D L.rank L'.rank) ⬝ w : Mx D L.rank S.rank) :=
      continuous_const.matrix_mul continuous_id
    rw [funext hκ]
    exact (continuous_ofAdj L S).comp h
  · rw [hκ]
    exact ofAdj_mem L S (ratMx_mul (rat_mem τ) hw)
  · rw [hκ, hκ, ← ofAdj_mul_mt_inv]
    exact congrArg (ofAdj L S) (Matrix.mul_assoc (rat τ : Mx D L.rank L'.rank) w (mt S g⁻¹)).symm
  · rw [hκ, hκ]
    exact symplO_ofAdj L L' S τ ε hτ w w'
  · rw [hκ]
    exact map_ofAdj_eq_zero (infPart D) (fun z hz => by rw [infPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (infPart D) _ hw)
  · rw [hκ]
    exact map_ofAdj_eq_zero (finPart D) (fun z hz => by rw [finPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (finPart D) _ hw)

end GlobalTheory.LinkKappa

end
