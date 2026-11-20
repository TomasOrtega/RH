import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecCalc

/- English proof (translation)
Introduce `n H _ _ J π _ hJ hπ v hv`. Establish `hG : IsUnit J` using `(Matrix.isUnit_iff_isUnit_det J).2 hJ`. Establish `hv' : v ∈ GlobalTheory.SmVec.smSub J π` using `hv`. Use `⟨fun g hg => GlobalTheory.SmVec.rep_mem hG hπ hv' hg, fun w hw c => ?_, fun X hX => ?_⟩` and prove the remaining obligations. Establish `hw' : w ∈ GlobalTheory.SmVec.smSub J π` using `hw`.

Conclude with `add_mem hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw')`. Establish `hX' : X ∈ GlobalTheory.SmVec.lieG J` using `hX`. Establish `hD` using `GlobalTheory.SmVec.hasDerivAt_dRep hv' hX'`. Use `⟨GlobalTheory.SmVec.dRep_mem hG hπ hv' hX', hD, fun g hg => ?_, fun c => ?_, fun w hw => ⟨?_, fun c => ?_⟩⟩` and prove the remaining obligations. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)`.

Establish `hY : g * X * g⁻¹ ∈ GlobalTheory.SmVec.lieG J`. Use `GlobalTheory.SmVec.conj_mem_lieG hG (GlobalTheory.SmVec.inv_mem_UH hG hg) hX'` as an intermediate fact. Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hd]`. Then use the resulting hypothesis. Rewrite using `[GlobalTheory.SmVec.dRep_rep hG hπ hv' hg hY]`. Use `congr 2`.

Simplify using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]`. Establish `h1 : HasDerivAt (fun t : ℝ => t * c) c 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).mul_const c`. Establish `h2` using `HasDerivAt.scomp_of_eq (0 : ℝ) hD h1 (by simp)`. Rewrite using `[Complex.coe_smul]`.

Use `Eq.trans ?_ h2.deriv` and prove the remaining obligations. Unfold `dRep`. Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp, smul_smul]`.

Establish `hw' : w ∈ GlobalTheory.SmVec.smSub J π` using `hw`. Rewrite using `[GlobalTheory.SmVec.inner_dRep hG hπ hv' hw' hX', neg_neg]`. Establish `hw' : w ∈ GlobalTheory.SmVec.smSub J π` using `hw`. Rewrite using `[GlobalTheory.SmVec.dRep_add hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw') hX', GlobalTheory.SmVec.dRep_smul c hw' hX']`.
-/
theorem smooth_calculus : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → (∀ g ∈ Formalism.QuantumDeterminants.UH J, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (π g v)) ∧ (∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ∀ c : ℂ, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (v + c • w)) ∧ ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π (dRep π X v) ∧ HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH J, π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v)) ∧ (∀ c : ℝ, dRep π (c • X) v = (c : ℂ) • dRep π X v) ∧ ∀ w, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π w → ⟪dRep π X v, w⟫_ℂ = -⟪v, dRep π X w⟫_ℂ ∧ ∀ c : ℂ, dRep π X (v + c • w) = dRep π X v + c • dRep π X w := by
  intro n H _ _ J π _ hJ hπ v hv
  have hG : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have hv' : v ∈ GlobalTheory.SmVec.smSub J π := hv
  refine ⟨fun g hg => GlobalTheory.SmVec.rep_mem hG hπ hv' hg, fun w hw c => ?_, fun X hX => ?_⟩
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    exact add_mem hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw')
  have hX' : X ∈ GlobalTheory.SmVec.lieG J := hX
  have hD := GlobalTheory.SmVec.hasDerivAt_dRep hv' hX'
  refine ⟨GlobalTheory.SmVec.dRep_mem hG hπ hv' hX', hD, fun g hg => ?_, fun c => ?_, fun w hw => ⟨?_, fun c => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
    have hY : g * X * g⁻¹ ∈ GlobalTheory.SmVec.lieG J := by
      have := GlobalTheory.SmVec.conj_mem_lieG hG (GlobalTheory.SmVec.inv_mem_UH hG hg) hX'
      rwa [Matrix.nonsing_inv_nonsing_inv _ hd] at this
    rw [GlobalTheory.SmVec.dRep_rep hG hπ hv' hg hY]
    congr 2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  · have h1 : HasDerivAt (fun t : ℝ => t * c) c 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 := HasDerivAt.scomp_of_eq (0 : ℝ) hD h1 (by simp)
    rw [Complex.coe_smul]
    refine Eq.trans ?_ h2.deriv
    unfold dRep
    congr 1
    funext t
    simp only [Function.comp, smul_smul]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.inner_dRep hG hπ hv' hw' hX', neg_neg]
  · have hw' : w ∈ GlobalTheory.SmVec.smSub J π := hw
    rw [GlobalTheory.SmVec.dRep_add hv' ((GlobalTheory.SmVec.smSub J π).smul_mem c hw') hX', GlobalTheory.SmVec.dRep_smul c hw' hX']

end GlobalTheory.SmVecCalc

end
