import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Matrix GlobalTheory.Mem.Isom GlobalTheory.TriMove
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7} {S S' T T' : HSp D}

/- English proof (translation)
Establish `hu : IsUnit S'.gram.det` using `(GlobalTheory.SmoothAutCheck.gram_det_ne S').isUnit`. Establish `h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * S.gram * I.Q = S'.gram` using `I.symm.gram`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, I.QP, Matrix.mul_one]`.

Use `_ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, I.QP]`.
-/
theorem gramInv_conj (I : IsoMat S S') :
    I.Q * S'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q = S.gram⁻¹ := by
  have hu : IsUnit S'.gram.det := (GlobalTheory.SmoothAutCheck.gram_det_ne S').isUnit
  have h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * S.gram * I.Q = S'.gram := I.symm.gram
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc _ = I.Q * (S'.gram⁻¹ * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * S.gram * I.Q)) * I.P := by
        simp only [Matrix.mul_assoc, I.QP, Matrix.mul_one]
    _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, I.QP]

/- English proof (translation)
Unfold `hO`. Simplify using `only [Matrix.trace, Matrix.diag]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun b _ => sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b`.
-/
theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul ((S.gram⁻¹).map (incA D))
      (HMul.hMul (HMul.hMul (cT (cA D) y) (T.gram.map (incA D))) x)) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b

/- English proof (translation)
Rewrite using `[← hQ, ← hP]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[Matrix.trace_mul_comm]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_conj {A : Type} [CommRing A] {m n k l : ℕ} (s : A →+* A) {H : Matrix (Fin n) (Fin n) A} {H' : Matrix (Fin m) (Fin m) A}
    {Q : Matrix (Fin n) (Fin m) A} (hQ : Q * H' * cT s Q = H) {J : Matrix (Fin k) (Fin k) A} {J' : Matrix (Fin l) (Fin l) A}
    {P : Matrix (Fin l) (Fin k) A} (hP : cT s P * J' * P = J) (x y : Matrix (Fin k) (Fin n) A) :
    Matrix.trace (H' * (cT s (P * y * Q) * J' * (P * x * Q))) = Matrix.trace (H * (cT s y * J * x)) := by
  rw [← hQ, ← hP]
  calc _ = Matrix.trace ((H' * cT s Q * (cT s y * (cT s P * J' * P) * x)) * Q) := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[hO_eq_trace, hO_eq_trace]`. Establish `e : cT (cA D) (IS.Q.map (incA D)) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.Q).map (incA D)`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hQ : HMul.hMul (HMul.hMul IS.aQ ((S'.gram⁻¹).map (incA D))) (cT (cA D) IS.aQ) = (S.gram⁻¹).map (incA D)`.

Rewrite using `[← gramInv_conj IS, Matrix.map_mul, Matrix.map_mul, ← e]`. Both sides reduce to the same expression. Conclude with `trace_conj (cA D) hQ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y`.
-/
theorem hO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    hO S' T' (homMap IS IT x) (homMap IS IT y) = hO S T x y := by
  rw [hO_eq_trace, hO_eq_trace]
  have e : cT (cA D) (IS.Q.map (incA D)) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.Q).map (incA D) := by
    ext i j
    rfl
  have hQ : HMul.hMul (HMul.hMul IS.aQ ((S'.gram⁻¹).map (incA D))) (cT (cA D) IS.aQ) = (S.gram⁻¹).map (incA D) := by
    rw [← gramInv_conj IS, Matrix.map_mul, Matrix.map_mul, ← e]
    rfl
  exact trace_conj (cA D) hQ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y

/- English proof (translation)
Unfold `symplOH symplO`. Rewrite using `[hO_homMap]`.
-/
theorem symplOH_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    symplOH S' T' (homMap IS IT x) (homMap IS IT y) = symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_homMap]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homMap_symm_apply (IS : IsoMat S S') (IT : IsoMat T T') (y : WO S' T') :
    (homMap IS IT).symm y = homMap IS.symm IT.symm y := rfl

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_homMap (IS : IsoMat S S') (IT : IsoMat T T') : Continuous (homMap IS IT) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `continuous_homMap IS.symm IT.symm`.
-/
theorem continuous_homMap_symm (IS : IsoMat S S') (IT : IsoMat T T') : Continuous (homMap IS IT).symm :=
  continuous_homMap IS.symm IT.symm

/- English proof (translation)
Use `show HMul.hMul (HMul.hMul (IT.P.map (incA D)) (γ.map (incA D))) (IS.Q.map (incA D)) = (IT.P * γ * IS.Q).map (incA D)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`.
-/
theorem homMap_ratW (IS : IsoMat S S') (IT : IsoMat T T') (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    homMap IS IT (ratW T S γ) = ratW T' S' (IT.P * γ * IS.Q) := by
  show HMul.hMul (HMul.hMul (IT.P.map (incA D)) (γ.map (incA D))) (IS.Q.map (incA D)) = (IT.P * γ * IS.Q).map (incA D)
  rw [Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Take `⟨z, hz⟩` from `hx`. Establish `h2 : ratW T S z = x` using `hz`. Rewrite using `[← h2, homMap_ratW]`. Conclude with `⟨_, rfl⟩`.
-/
theorem homMap_mem_ratL (IS : IsoMat S S') (IT : IsoMat T T') {x : WO S T} (hx : x ∈ ratL T S) : homMap IS IT x ∈ ratL T' S' := by
  obtain ⟨z, hz⟩ := hx
  have h2 : ratW T S z = x := hz
  rw [← h2, homMap_ratW]
  exact ⟨_, rfl⟩

/- English proof (translation)
Rewrite using `[homMap_apply, Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem map_homMap_zero (IS : IsoMat S S') (IT : IsoMat T T') {B : Type} [CommRing B] (ρ : AE D →+* B) {w : WO S T}
    (h : w.map ρ = 0) : (homMap IS IT w).map ρ = 0 := by
  rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Take `⟨w, rfl⟩` from `(homMap IS IT).surjective w`. Simplify using `only [heisO, trH, ← map_add, AddEquiv.symm_apply_apply, symplOH_homMap]`.
-/
theorem heisO_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S' T' (homMap IS IT u) (trH IS IT f) = trH IS IT (heisO ψ S T u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
  simp only [heisO, trH, ← map_add, AddEquiv.symm_apply_apply, symplOH_homMap]

/- English proof (translation)
Use `⟨fun γ w => ?_, ?_, hf.cont.comp (continuous_homMap_symm IS IT), fun k L hL h0 w => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `(homMap IS IT).surjective w`. Establish `e : ratW T' S' γ = homMap IS IT (ratW T S (IT.Q * γ * IS.P))`. Use `homMap_ratW IS.symm IT.symm γ` as an intermediate fact. Rewrite `this` using `[← homMap_symm_apply]`.

Conclude with `((homMap IS IT).symm_apply_eq.1 this)`. Rewrite using `[e, ← map_add, symplOH_homMap]`. Simplify using `only [trH, AddEquiv.symm_apply_apply]`. Conclude with `hf.quasi _ _`. Take `⟨U, hU, e⟩` from `hf.level`.

Use `⟨U.comap (homMap IS IT).symm.toAddMonoidHom, hU.preimage (continuous_homMap_symm IS IT), fun u hu h0 => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `(homMap IS IT).surjective u`. Establish `hu' : u ∈ U` using `by simpa using hu`. Establish `h1 : u.map (infPart D) = 0`. Use `map_homMap_zero IS.symm IT.symm _ h0` as an intermediate fact.

Rewrite `this` using `[← homMap_symm_apply, AddEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Rewrite using `[heisO_trH, e u hu' h1]`. Use `hf.smooth k ((homMap IS IT).symm.toAddMonoidHom.comp L) ((continuous_homMap_symm IS IT).comp hL) (fun t => map_homMap_zero IS.symm IT.symm _ (h0 t)) ((homMap IS IT).symm w)` as an intermediate fact. Simplify `this` using `[trH]`.
-/
theorem isThetaFunO_trH (IS : IsoMat S S') (IT : IsoMat T T') {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S' T' (trH IS IT f) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (continuous_homMap_symm IS IT), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
    have e : ratW T' S' γ = homMap IS IT (ratW T S (IT.Q * γ * IS.P)) := by
      have := homMap_ratW IS.symm IT.symm γ
      rw [← homMap_symm_apply] at this
      exact ((homMap IS IT).symm_apply_eq.1 this)
    rw [e, ← map_add, symplOH_homMap]
    simp only [trH, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.comap (homMap IS IT).symm.toAddMonoidHom, hU.preimage (continuous_homMap_symm IS IT), fun u hu h0 => ?_⟩
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    have hu' : u ∈ U := by simpa using hu
    have h1 : u.map (infPart D) = 0 := by
      have := map_homMap_zero IS.symm IT.symm _ h0
      rwa [← homMap_symm_apply, AddEquiv.symm_apply_apply] at this
    rw [heisO_trH, e u hu' h1]
  · have := hf.smooth k ((homMap IS IT).symm.toAddMonoidHom.comp L) ((continuous_homMap_symm IS IT).comp hL)
      (fun t => map_homMap_zero IS.symm IT.symm _ (h0 t)) ((homMap IS IT).symm w)
    simpa [trH] using this

/- English proof (translation)
Set `ρ : AE D →+* ℂ` to `(θ τ).comp (infPart D)`. Establish `hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ x` using `fun x => by`. Use `(hθ τ).1 x` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[ρ, incA, inclR, infPart]`.

Establish `e1 : IT.aP.map ρ = IT.pT τ` using `by ext i j; exact hρ _`. Establish `e2 : IS.aQ.map ρ = IS.qT τ` using `by ext i j; exact hρ _`. Use `show (homMap IS IT w).map ρ = IT.pT τ * w.map ρ * IS.qT τ`. Rewrite using `[homMap_apply, Matrix.map_mul, Matrix.map_mul, e1, e2]`.
-/
theorem compAt_homMap (IS : IsoMat S S') (IT : IsoMat T T') {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : WO S T) :
    compAt θ τ (homMap IS IT w) = IT.pT τ * compAt θ τ w * IS.qT τ := by
  let ρ : AE D →+* ℂ := (θ τ).comp (infPart D)
  have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ x := fun x => by
    have := (hθ τ).1 x
    rw [← this]
    simp [ρ, incA, inclR, infPart]
  have e1 : IT.aP.map ρ = IT.pT τ := by ext i j; exact hρ _
  have e2 : IS.aQ.map ρ = IS.qT τ := by ext i j; exact hρ _
  show (homMap IS IT w).map ρ = IT.pT τ * w.map ρ * IS.qT τ
  rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, e1, e2]

/- English proof (translation)
Establish `hL : IsLineAt θ τ z (lineAt θ τ z)` using `Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)`. Establish `hL0 : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) (lineAt θ τ (IT.pT τ * z * IS.qT τ))` using `Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)`. Establish `hN : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z))`. Use `⟨(continuous_homMap IS IT).comp hL.1, fun t => map_homMap_zero IS IT _ (hL.2.1 t), fun t τ' => ?_⟩` and prove the remaining obligations. Use `show compAt θ τ' (homMap IS IT (lineAt θ τ z t)) = _`.

Rewrite using `[compAt_homMap IS IT hθ, hL.2.2 t τ']`. Use `split_ifs with c`. Substitute `c` using the available equality. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[Matrix.mul_zero, Matrix.zero_mul]`.

Rewrite using `[GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL0 hN]`. Both sides reduce to the same expression.
-/
theorem lineAt_homMap (IS : IsoMat S S') (IT : IsoMat T T') {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (IT.pT τ * z * IS.qT τ) t = homMap IS IT (lineAt θ τ z t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  have hL0 : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) (lineAt θ τ (IT.pT τ * z * IS.qT τ)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  have hN : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z)) := by
    refine ⟨(continuous_homMap IS IT).comp hL.1, fun t => map_homMap_zero IS IT _ (hL.2.1 t), fun t τ' => ?_⟩
    show compAt θ τ' (homMap IS IT (lineAt θ τ z t)) = _
    rw [compAt_homMap IS IT hθ, hL.2.2 t τ']
    split_ifs with c
    · subst c
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL0 hN]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Unfold `Formalism.IndefR.Datum.dRho`. Simplify using `only [lineAt_homMap IS IT hθ, heisO_trH]`. Both sides reduce to the same expression.
-/
theorem dRho_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S' T') θ τ (IT.pT τ * z * IS.qT τ) (trH IS IT f) =
      trH IS IT (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_homMap IS IT hθ, heisO_trH]
  rfl

/- English proof (translation)
Unfold `cplxO cartMove`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cplxO_move (IS : IsoMat S S') (IT : IsoMat T T') (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO (cartMove IS τ sS) (cartMove IT τ sT) (IT.pT τ * z * IS.qT τ) = IT.pT τ * cplxO sS sT z * IS.qT τ := by
  unfold cplxO cartMove
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = IT.pT τ * sT * (IT.qT τ * IT.pT τ) * z * (IS.qT τ * IS.pT τ) * sS * IS.qT τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [IT.qT_pT, IS.qT_pT]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Introduce `z'`. Choose the witnesses or unpack the hypotheses as in `⟨z, rfl⟩ : ∃ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, z' = IT.pT τ * z * IS.qT τ := by`. Use `⟨IT.qT τ * z' * IS.pT τ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Unfold `annih`.

Rewrite using `[cplxO_move, dRho_trH IS IT ψ hθ, dRho_trH IS IT ψ hθ]`. Use function extensionality and compare the values at `x`. Conclude with `congrFun (hf z) ((homMap IS IT).symm x)`.
-/
theorem isFockVacAt_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    IsFockVacAt (heisO ψ S' T') θ τ (cplxO (cartMove IS τ sS) (cartMove IT τ sT)) (trH IS IT f) := by
  intro z'
  obtain ⟨z, rfl⟩ : ∃ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, z' = IT.pT τ * z * IS.qT τ := by
    refine ⟨IT.qT τ * z' * IS.pT τ, ?_⟩
    calc z' = (IT.pT τ * IT.qT τ) * z' * (IS.pT τ * IS.qT τ) := by rw [IT.pT_qT, IS.pT_qT, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold annih
  rw [cplxO_move, dRho_trH IS IT ψ hθ, dRho_trH IS IT ψ hθ]
  funext x
  exact congrFun (hf z) ((homMap IS IT).symm x)

/- English proof (translation)
Establish `e : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) D.host.E), (N.map fun e => (β ⊗ₜ[D.host.F] e : AE D)) = (β ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • N.map (incA D)`. Introduce `a b N`. Use extensionality with `i j`. Simplify using `[incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e, e, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]`.
-/
theorem tmul_conj {m n k l : ℕ} (β : AF D.host.F) (P : Matrix (Fin l) (Fin k) D.host.E) (M : Matrix (Fin k) (Fin n) D.host.E)
    (Q : Matrix (Fin n) (Fin m) D.host.E) :
    HMul.hMul (HMul.hMul (P.map (incA D)) (M.map fun e => (β ⊗ₜ[D.host.F] e : AE D))) (Q.map (incA D)) =
      (P * M * Q).map fun e => (β ⊗ₜ[D.host.F] e : AE D) := by
  have e : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) D.host.E), (N.map fun e => (β ⊗ₜ[D.host.F] e : AE D)) =
      (β ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • N.map (incA D) := by
    intro a b N
    ext i j
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Establish `e : ∀ {p q : ℕ} (H : Matrix (Fin p) (Fin p) A) (s : Fin p → A) (t : Fin q → A), (Matrix.of fun i j => a * t i * ∑ c, σ (s c) * H c j) = a • (Matrix.replicateCol (Fin 1) t * (cT σ (Matrix.replicateCol (Fin 1) s) * H))`. Introduce `p q H s t`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, cT, mul_assoc]`. Rewrite using `[e, e, Matrix.replicateCol_mulVec, Matrix.replicateCol_mulVec, cT_mul, Matrix.mul_smul, Matrix.smul_mul]`.

Simplify using `only [Matrix.mul_assoc, h]`.
-/
theorem gen_conj {A : Type} [CommRing A] {m n k l : ℕ} (σ : A →+* A) {G : Matrix (Fin n) (Fin n) A} {G' : Matrix (Fin m) (Fin m) A}
    {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (h : cT σ P * G' = G * Q) (R : Matrix (Fin l) (Fin k) A) (a : A)
    (s : Fin n → A) (t : Fin k → A) :
    R * (Matrix.of fun i j => a * t i * ∑ c, σ (s c) * G c j) * Q =
      Matrix.of fun i j => a * (R *ᵥ t) i * ∑ c, σ ((P *ᵥ s) c) * G' c j := by
  have e : ∀ {p q : ℕ} (H : Matrix (Fin p) (Fin p) A) (s : Fin p → A) (t : Fin q → A),
      (Matrix.of fun i j => a * t i * ∑ c, σ (s c) * H c j) =
        a • (Matrix.replicateCol (Fin 1) t * (cT σ (Matrix.replicateCol (Fin 1) s) * H)) := by
    intro p q H s t
    ext i j
    simp [Matrix.mul_apply, cT, mul_assoc]
  rw [e, e, Matrix.replicateCol_mulVec, Matrix.replicateCol_mulVec, cT_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, h]

/- English proof (translation)
Establish `hle : latO S' T' (latMove IS LS) (latMove IT LT) p ≤ (latO S T LS LT p).comap (homMap IS IT).symm.toAddMonoidHom`. Unfold `latO`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `w ⟨α, hα, hP, a, ha, _, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩`. Use `AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩` and prove the remaining obligations.

Use `(homMap IS IT).symm_apply_eq.2 ?_` and prove the remaining obligations. Establish `h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.P * S'.gram = S.gram * IS.Q`. Rewrite using `[← IS.gram, Matrix.mul_assoc _ IS.P, IS.PQ, Matrix.mul_one]`. Establish `h1` using `tmul_conj (pairA D.host.F 0 α) IT.P (Matrix.of fun i j => a * t i * ∑ c, (D.sp.cm.sig : D.host.E →+* D.host.E) (s c) * S.gram c j) IS.Q`. Rewrite `h1` using `[gen_conj _ h]`.

Conclude with `h1.symm`. Conclude with `hle hu`.
-/
theorem symm_mem_latO (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S' T'}
    (hu : u ∈ latO S' T' (latMove IS LS) (latMove IT LT) p) : (homMap IS IT).symm u ∈ latO S T LS LT p := by
  have hle : latO S' T' (latMove IS LS) (latMove IT LT) p ≤ (latO S T LS LT p).comap (homMap IS IT).symm.toAddMonoidHom := by
    unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, _, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    refine (homMap IS IT).symm_apply_eq.2 ?_
    have h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.P * S'.gram = S.gram * IS.Q := by
      rw [← IS.gram, Matrix.mul_assoc _ IS.P, IS.PQ, Matrix.mul_one]
    have h1 := tmul_conj (pairA D.host.F 0 α) IT.P
      (Matrix.of fun i j => a * t i * ∑ c, (D.sp.cm.sig : D.host.E →+* D.host.E) (s c) * S.gram c j) IS.Q
    rw [gen_conj _ h] at h1
    exact h1.symm
  exact hle hu

/- English proof (translation)
Introduce `i j`. Establish `h : e • u = u`. Use extensionality with `i j`. Conclude with `hu i j`. Establish `h2 : e • homMap IS IT u = homMap IS IT u`.

Rewrite using `[homMap_apply, ← Matrix.smul_mul, ← Matrix.mul_smul, h]`. Conclude with `congrFun (congrFun h2 i) j`.
-/
theorem isHalf_homMap (IS : IsoMat S S') (IT : IsoMat T T') {e : AE D} {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (homMap IS IT u) := by
  intro i j
  have h : e • u = u := by
    ext i j
    exact hu i j
  have h2 : e • homMap IS IT u = homMap IS IT u := by
    rw [homMap_apply, ← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

/- English proof (translation)
Use `⟨fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Establish `h` using `symm_mem_latO IS IT LS LT p hu`. Take `⟨u, rfl⟩` from `(homMap IS IT).surjective u`. Rewrite `h` using `[AddEquiv.symm_apply_apply]`. Rewrite using `[← map_nsmul, heisO_trH, hf.1 u h]`.

Establish `h` using `symm_mem_latO IS IT LS LT p hu`. Establish `h'` using `isHalf_homMap IS.symm IT.symm hh`. Rewrite `h'` using `[← homMap_symm_apply]`. Take `⟨u, rfl⟩` from `(homMap IS IT).surjective u`. Rewrite `h`, `h'` using `[AddEquiv.symm_apply_apply]`.

Rewrite using `[heisO_trH, hf.2 e he u h h']`.
-/
theorem isLatVac_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ)
    (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT p) f) :
    IsLatVac (heisO ψ S' T') (latO S' T' (latMove IS LS) (latMove IT LT) p) (trH IS IT f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h := symm_mem_latO IS IT LS LT p hu
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    rw [AddEquiv.symm_apply_apply] at h
    rw [← map_nsmul, heisO_trH, hf.1 u h]
  · have h := symm_mem_latO IS IT LS LT p hu
    have h' := isHalf_homMap IS.symm IT.symm hh
    rw [← homMap_symm_apply] at h'
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    rw [AddEquiv.symm_apply_apply] at h h'
    rw [heisO_trH, hf.2 e he u h h']

/- English proof (translation)
Take `⟨hμ, h𝓕, h1⟩` from `h`. Use `haveI hB : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI hB' : BorelSpace (WO S' T') := ⟨rfl⟩`. Establish `hc` using `continuous_homMap IS IT`. Establish `hcs` using `continuous_homMap_symm IS IT`.

Set `m : WO S T ≃ᵐ WO S' T'` to `{ toEquiv := (homMap IS IT).toEquiv measurable_toFun := hc.measurable measurable_invFun := hcs.measurable }`. Establish `hmp : MeasurePreserving m (μ.map m.symm) μ` using `(MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)`. Establish `hmp' : MeasurePreserving (homMap IS IT) (μ.map (homMap IS IT).symm) μ` using `hmp`. Use `⟨μ.map (homMap IS IT).symm, homMap IS IT ⁻¹' 𝓕, ⟨AddEquiv.isAddHaarMeasure_map μ (homMap IS IT).symm hcs (by simpa using hc), ?_, ?_⟩, fun f => ?_⟩` and prove the remaining obligations. Set `g : ratL T' S' → ratL T S` to `fun y => ⟨(homMap IS IT).symm y, homMap_mem_ratL IS.symm IT.symm y.2⟩`.

Establish `hg : Function.Bijective g`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `Subtype.ext ((homMap IS IT).symm.injective (congrArg Subtype.val hab))`. Introduce `x`.

Conclude with `⟨⟨homMap IS IT x, homMap_mem_ratL IS IT x.2⟩, Subtype.ext (by simp [g])⟩`. Use `h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_` and prove the remaining obligations. Introduce `y x`. Simplify using `[g, AddSubgroup.vadd_def]`. Conclude with `(hmp'.measure_preimage_emb m.measurableEmbedding 𝓕).trans h1`.

Use `hmp'.setIntegral_preimage_emb m.measurableEmbedding (fun b => ‖trH IS IT f b‖ ^ 2) 𝓕` as an intermediate fact. Unfold `nrm2`. Rewrite using `[← this]`. Simplify using `only [trH, AddEquiv.symm_apply_apply]`.
-/
theorem exists_covolOne (IS : IsoMat S S') (IT : IsoMat T T') {μ : Measure (WO S' T')} {𝓕 : Set (WO S' T')}
    (h : IsCovolOne (ratL T' S') μ 𝓕) : ∃ (ν : Measure (WO S T)) (𝓖 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓖 ∧
      ∀ f : WO S T → ℂ, nrm2 μ 𝓕 (trH IS IT f) = nrm2 ν 𝓖 f := by
  obtain ⟨hμ, h𝓕, h1⟩ := h
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S' T') := ⟨rfl⟩
  have hc := continuous_homMap IS IT
  have hcs := continuous_homMap_symm IS IT
  let m : WO S T ≃ᵐ WO S' T' :=
    { toEquiv := (homMap IS IT).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (homMap IS IT) (μ.map (homMap IS IT).symm) μ := hmp
  refine ⟨μ.map (homMap IS IT).symm, homMap IS IT ⁻¹' 𝓕,
    ⟨AddEquiv.isAddHaarMeasure_map μ (homMap IS IT).symm hcs (by simpa using hc), ?_, ?_⟩, fun f => ?_⟩
  · let g : ratL T' S' → ratL T S := fun y => ⟨(homMap IS IT).symm y, homMap_mem_ratL IS.symm IT.symm y.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext ((homMap IS IT).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨homMap IS IT x, homMap_mem_ratL IS IT x.2⟩, Subtype.ext (by simp [g])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro y x
    simp [g, AddSubgroup.vadd_def]
  · exact (hmp'.measure_preimage_emb m.measurableEmbedding 𝓕).trans h1
  · have := hmp'.setIntegral_preimage_emb m.measurableEmbedding (fun b => ‖trH IS IT f b‖ ^ 2) 𝓕
    unfold nrm2
    rw [← this]
    simp only [trH, AddEquiv.symm_apply_apply]

/- English proof (translation)
Take `⟨hψ, hv⟩` from `hf`. Use `⟨hψ, hv.inf, isThetaFunO_trH IS IT hv.theta, isLatVac_trH IS IT ψ LS LT _ hv.lat, fun τ => isFockVacAt_trH IS IT ψ hv.inf τ _ _ (hv.fock τ), ?_, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `hv.norm.1`. Take `⟨ν, 𝓖, h, -⟩` from `exists_covolOne IS.symm IT.symm hp`. Conclude with `⟨(ν, 𝓖), h⟩`.

Take `⟨ν, 𝓖, h, e⟩` from `exists_covolOne IS IT hp`. Conclude with `(e f).trans (hv.norm.2 (ν, 𝓖) h)`.
-/
theorem isVacO_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ S' T' (fun τ => cartMove IS τ (sS τ)) (fun τ => cartMove IT τ (sT τ)) (latMove IS LS) (latMove IT LT)
      (trH IS IT f) := by
  obtain ⟨hψ, hv⟩ := hf
  refine ⟨hψ, hv.inf, isThetaFunO_trH IS IT hv.theta, isLatVac_trH IS IT ψ LS LT _ hv.lat,
    fun τ => isFockVacAt_trH IS IT ψ hv.inf τ _ _ (hv.fock τ), ?_, fun p hp => ?_⟩
  · obtain ⟨p, hp⟩ := hv.norm.1
    obtain ⟨ν, 𝓖, h, -⟩ := exists_covolOne IS.symm IT.symm hp
    exact ⟨(ν, 𝓖), h⟩
  · obtain ⟨ν, 𝓖, h, e⟩ := exists_covolOne IS IT hp
    exact (e f).trans (hv.norm.2 (ν, 𝓖) h)

def isoSgn (ε : Bool) (I : IsoMat S S') : IsoMat (GlobalTheory.Grid.sgn ε S) (GlobalTheory.Grid.sgn ε S') where
  P := I.P
  Q := I.Q
  PQ := I.PQ
  QP := I.QP
  gram := by
    cases ε
    · exact I.gram
    · show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (-S'.gram) * I.P = -S.gram
      rw [Matrix.mul_neg, Matrix.neg_mul, I.gram]

/- English proof (translation)
Consider the cases of `ε`. Both sides reduce to the same expression. Use `show -(I.pT τ * s * I.qT τ) = I.pT τ * (-s) * I.qT τ`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul]`.
-/
theorem sgnM_cartMove (ε : Bool) (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    GlobalTheory.Grid.sgnM ε (cartMove I τ s) = cartMove I τ (GlobalTheory.Grid.sgnM ε s) := by
  cases ε
  · rfl
  · show -(I.pT τ * s * I.qT τ) = I.pT τ * (-s) * I.qT τ
    rw [Matrix.mul_neg, Matrix.neg_mul]

/- English proof (translation)
Introduce `D ψ θ ε S S' T T' IS IT sS sT LS LT f hf`. Simplify using `only [sgnM_cartMove]`. Conclude with `isVacO_trH (isoSgn ε IS) IT ψ θ (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT hf`.
-/
theorem isVacO_move : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  intro D ψ θ ε S S' T T' IS IT sS sT LS LT f hf
  simp only [sgnM_cartMove]
  exact isVacO_trH (isoSgn ε IS) IT ψ θ (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT hf

end GlobalTheory.VacMove

end
