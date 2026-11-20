import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitHomBound

variable {D : D7}

/- English proof (translation)
Unfold `Formalism.MainNotions.StandardLattice.latHat`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨b, hb, o, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨b, hb, o • x, Λ.smul_mem o hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, Algebra.smul_def]`. Consider the case `zero`. Establish `h0 : (fun i => (0 : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = 0`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[h0]`. Conclude with `zero_mem _`. Consider the case `add w₁ w₂ _ _ h₁ h₂`. Establish `h3 : (fun i => (w₁ + w₂) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = (fun i => w₁ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) + (fun i => w₂ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i))`.

Use function extensionality and compare the values at `i`. Simplify using `[add_mul]`. Rewrite using `[h3]`. Conclude with `add_mem h₁ h₂`. Consider the case `neg w _ h`.

Establish `h3 : (fun i => (-w) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = -(fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i))`. Use function extensionality and compare the values at `i`. Simplify using `[neg_mul]`. Rewrite using `[h3]`. Conclude with `neg_mem h`.
-/
theorem mul_mem_latHat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) {x : Fin n → D.host.E} (hx : x ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈
      Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨b, hb, o • x, Λ.smul_mem o hx, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have h0 : (fun i => (0 : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = 0 := by
      funext i; simp
    rw [h0]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ =>
    have h3 : (fun i => (w₁ + w₂) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        (fun i => w₁ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) + (fun i => w₂ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [add_mul]
    rw [h3]; exact add_mem h₁ h₂
  | neg w _ h =>
    have h3 : (fun i => (-w) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        -(fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [neg_mul]
    rw [h3]; exact neg_mem h

/- English proof (translation)
Simplify using `only [rdA, rdQ, GlobalTheory.AdelicU.compFin, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Establish `hev : GlobalTheory.AdelicU.evFin D.host.F v (pairA D.host.F 0 α) = evalV D.host.F v α`. Simplify using `only [GlobalTheory.AdelicU.evFin, pairA, sndA, ]`. Both sides reduce to the same expression. Establish `hsm : (evalV D.host.F v α ⊗ₜ[D.host.F] m : Fv D.host.F v ⊗[D.host.F] D.host.E) = evalV D.host.F v α • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] m)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[hev, hsm, map_smul, smul_eq_mul]`.
-/
theorem rdA_pairA_tmul {v : FinPl D} (φ : SplitProj D v) (α : Af D.host.F) (m : D.host.E) :
    rdA φ (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = evalV D.host.F v α * rdQ φ m := by
  simp only [rdA, rdQ, GlobalTheory.AdelicU.compFin, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hev : GlobalTheory.AdelicU.evFin D.host.F v (pairA D.host.F 0 α) = evalV D.host.F v α := by
    simp only [GlobalTheory.AdelicU.evFin, pairA, sndA, ]
    rfl
  have hsm : (evalV D.host.F v α ⊗ₜ[D.host.F] m : Fv D.host.F v ⊗[D.host.F] D.host.E) =
      evalV D.host.F v α • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hev, hsm, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `hq : ∀ x y : D.host.E, rdQ φ (x * y) = rdQ φ x * rdQ φ y`. Introduce `x y`. Simplify using `only [← GlobalTheory.SplitProjChart.emb_apply, map_mul]`. Establish `hqs : ∀ (f : Fin S.rank → D.host.E), rdQ φ (∑ k, f k) = ∑ k, rdQ φ (f k)`. Introduce `f`.

Simplify using `only [← GlobalTheory.SplitProjChart.emb_apply, map_sum]`. Simplify using `only [mapCo, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, rdA_pairA_tmul, hq, hqs, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]`. Use `conv_lhs => enter [2, c]`. Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mapCo_gen {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    mapCo φ S T BS BT (Matrix.of fun (i : Fin T.rank) (j : Fin S.rank) =>
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      evalV D.host.F v α * rdQ φ a * (((BT⁻¹).1 *ᵥ fun k => rdQ φ (t k)) i) *
        (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * BS.1)) j) := by
  have hq : ∀ x y : D.host.E, rdQ φ (x * y) = rdQ φ x * rdQ φ y := by
    intro x y; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_mul]
  have hqs : ∀ (f : Fin S.rank → D.host.E), rdQ φ (∑ k, f k) = ∑ k, rdQ φ (f k) := by
    intro f; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_sum]
  simp only [mapCo, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, rdA_pairA_tmul, hq, hqs,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Introduce `D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a ha u hu`. Take `⟨hch, -, hrdinc, -, -⟩` from `GlobalTheory.SplitProjChart.chart_rdA D v φ e he`. Establish `hfi : ∀ x : D.host.E, finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x`. Introduce `x`. Simplify using `[finPart, incA, inclR]`.

Establish `he1 : finPart D e ∈ intAE D`. Establish `h1` using `(hch.2.2.2 1).2 ⟨1, by simp⟩`. Simplify using `using h1`. Establish `he2 : finPart D (cA D e) ∈ intAE D`. Take `⟨-, -, w, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩` from `he.1`.

Establish `hce : cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) - e`. Rewrite using `[← hsum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hαint : α ∈ intAf D.host.F`. Introduce `v'`.

Distinguish the cases in `h : v' = w`. Substitute `h` using the available equality. Rewrite using `[hα1]`. Conclude with `one_mem _`. Rewrite using `[hα0 v' h]`.

Conclude with `zero_mem _`. Establish `hfa : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]`. Simplify using `only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Both sides reduce to the same expression.

Rewrite using `[hce, map_sub, hfa]`. Conclude with `sub_mem (AddSubgroup.subset_closure ⟨α, hαint, 1, rfl⟩) he1`. Establish `hcainc : ∀ x : D.host.E, cA D (incA D x) = incA D (star x)`. Introduce `x`. Both sides reduce to the same expression.

Establish `h3 : ∀ t ∈ ΛT, ∀ i, Valued.v ((((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdQ φ (t k)) i) ≤ 1`. Introduce `t ht i`. Establish `hm : (fun k => finPart D (e * incA D (t k))) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))`. Simplify `mul_mem_latHat ΛT he1 ht` using `only [map_mul, hfi]`. Simplify `(GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D T ΛT βT hT hfT v φ e he (fun k => incA D (t k))).1 hm i` using `only [hrdinc]`.

Establish `h4 : ∀ s ∈ ΛS, ∀ j, Valued.v (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * (frCo φ βS).1)) j) ≤ 1`. Introduce `s hs j`. Establish `hm : (fun k => finPart D (cA D e * incA D (s k))) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))`. Simplify `mul_mem_latHat ΛS he2 hs` using `only [map_mul, hfi]`. Simplify `(GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D S ΛS βS hS hfS v φ e he (fun k => incA D (s k))).1 hm j` using `only [hcainc, hrdinc]`.

Unfold `latO at hu`. Simplify using `only [not_true_eq_false, false_implies, implies_true, true_and] at hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, c, hc, s, hs, t, ht, rfl⟩` from `hw`.

Introduce `i j`. Rewrite using `[mapCo_gen, Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]`. Establish `h1 : Valued.v (evalV D.host.F v α) ≤ 1`. Establish `h0` using `hα v`. Rewrite `h0` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Consider the case `zero`. Introduce `i j`. Simplify using `[mapCo]`. Consider the case `add x y _ _ hx hy`.

Introduce `i j`. Establish `hxy : mapCo φ S T (frCo φ βS) (frCo φ βT) (x + y) = mapCo φ S T (frCo φ βS) (frCo φ βT) x + mapCo φ S T (frCo φ βS) (frCo φ βT) y`. Simplify using `[mapCo, Matrix.map_add, Matrix.mul_add, Matrix.add_mul]`. Rewrite using `[hxy, Matrix.add_apply]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))`.

Consider the case `neg x _ hx`. Introduce `i j`. Establish `hxn : mapCo φ S T (frCo φ βS) (frCo φ βT) (-x) = -mapCo φ S T (frCo φ βS) (frCo φ βT) x`. Simplify using `[mapCo, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]`. Rewrite using `[hxn, Matrix.neg_apply, Valuation.map_neg]`.

Conclude with `hx i j`.
-/
theorem hbound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (mapCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ a) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a ha u hu
  obtain ⟨hch, -, hrdinc, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hfi : ∀ x : D.host.E, finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    intro x
    simp [finPart, incA, inclR]
  have he1 : finPart D e ∈ intAE D := by
    have h1 := (hch.2.2.2 1).2 ⟨1, by simp⟩
    simpa using h1
  have he2 : finPart D (cA D e) ∈ intAE D := by
    obtain ⟨-, -, w, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he.1
    have hce : cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) - e := by
      rw [← hsum]; ring
    have hαint : α ∈ intAf D.host.F := by
      intro v'
      by_cases h : v' = w
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfa : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        α ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
      rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
      simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hce, map_sub, hfa]
    exact sub_mem (AddSubgroup.subset_closure ⟨α, hαint, 1, rfl⟩) he1
  have hcainc : ∀ x : D.host.E, cA D (incA D x) = incA D (star x) := by
    intro x
    rfl
  have h3 : ∀ t ∈ ΛT, ∀ i, Valued.v ((((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdQ φ (t k)) i) ≤ 1 := by
    intro t ht i
    have hm : (fun k => finPart D (e * incA D (t k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛT he1 ht
    simpa only [hrdinc] using (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D T ΛT βT hT hfT v φ e he (fun k => incA D (t k))).1 hm i
  have h4 : ∀ s ∈ ΛS, ∀ j, Valued.v (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * (frCo φ βS).1)) j) ≤ 1 := by
    intro s hs j
    have hm : (fun k => finPart D (cA D e * incA D (s k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛS he2 hs
    simpa only [hcainc, hrdinc] using (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D S ΛS βS hS hfS v φ e he (fun k => incA D (s k))).1 hm j
  unfold latO at hu
  simp only [not_true_eq_false, false_implies, implies_true, true_and] at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, c, hc, s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [mapCo_gen, Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    have h1 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have h0 := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h0
    calc _ ≤ 1 * Valued.v (rdQ φ a) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' h1 (ha c hc)) (h3 t ht i)) (h4 s hs j)
      _ = Valued.v (rdQ φ a) := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    simp [mapCo]
  | add x y _ _ hx hy =>
    intro i j
    have hxy : mapCo φ S T (frCo φ βS) (frCo φ βT) (x + y) =
        mapCo φ S T (frCo φ βS) (frCo φ βT) x + mapCo φ S T (frCo φ βS) (frCo φ βT) y := by
      simp [mapCo, Matrix.map_add, Matrix.mul_add, Matrix.add_mul]
    rw [hxy, Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))
  | neg x _ hx =>
    intro i j
    have hxn : mapCo φ S T (frCo φ βS) (frCo φ βT) (-x) = -mapCo φ S T (frCo φ βS) (frCo φ βT) x := by
      simp [mapCo, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hxn, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitHomBound

end
