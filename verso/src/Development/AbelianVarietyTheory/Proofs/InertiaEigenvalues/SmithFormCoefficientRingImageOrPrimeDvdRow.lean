import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SmithOE

/- English proof (translation)
Take `⟨n, snf⟩` from `(LinearMap.range (Matrix.mulVecLin P)).smithNormalForm (Pi.basisFun O (Fin d))`. Use `set U : Matrix (Fin d) (Fin d) O := (Pi.basisFun O (Fin d)).toMatrix snf.bM with hUdef`. Use `set W : Matrix (Fin d) (Fin d) O := snf.bM.toMatrix (Pi.basisFun O (Fin d)) with hWdef`. Establish `hWU : W * U = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`. Establish `hUW : U * W = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`.

Use `⟨U, W, hWU, hUW, fun j => ?_⟩` and prove the remaining obligations. Establish `hUcol : (fun i => U i j) = (snf.bM j : Fin d → O)`. Use function extensionality and compare the values at `i`. Simplify using `[hUdef, Module.Basis.toMatrix_apply]`. Establish `hmem : ∀ k, (fun i => P i k) ∈ LinearMap.range (Matrix.mulVecLin P)` using `fun k => ⟨Pi.single k 1, by funext i; simp⟩`.

Establish `hWP : ∀ k, (W * P) j k = snf.bM.repr (fun i => P i k) j`. Introduce `k`. Establish `h` using `Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O (Fin d)) snf.bM (fun i => P i k)`. Rewrite using `[← h, ← hWdef]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Distinguish the cases in `h : ∃ i, snf.f i = j ∧ IsUnit (snf.a i)`. Take `⟨i, rfl, u, hu⟩` from `h left`. Establish `hN : (snf.bM (snf.f i) : Fin d → O) ∈ LinearMap.range (Matrix.mulVecLin P)`. Establish `h1 : (snf.bM (snf.f i) : Fin d → O) = (↑u⁻¹ : O) • (snf.bN i : Fin d → O)`. Rewrite using `[snf.snf, ← hu, smul_smul, Units.inv_mul, one_smul]`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (snf.bN i).2`. Take `⟨w, hw⟩` from `hN`. Conclude with `⟨w, by rw [hUcol, ← hw]; rfl⟩`. Use `right`.

Introduce `k`. Rewrite using `[hWP k]`. Distinguish the cases in `hj : j ∈ Set.range snf.f`. Take `⟨i, rfl⟩` from `hj`. Establish `h2` using `congrFun (snf.repr_comp_embedding_eq_smul ⟨_, hmem k⟩) i`.

Simplify using `only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2`. Establish `h3 : snf.bM.repr (fun i => P i k) (snf.f i) = snf.a i * snf.bN.repr ⟨_, hmem k⟩ i` using `h2`. Rewrite using `[h3]`. Introduce `hu`. Conclude with `h ⟨i, rfl, isUnit_of_mul_isUnit_left hu⟩`.

Establish `h0` using `snf.repr_eq_zero_of_notMem_range ⟨_, hmem k⟩ hj`. Establish `h0' : snf.bM.repr (fun i => P i k) j = 0` using `h0`. Rewrite using `[h0']`. Conclude with `not_isUnit_zero`.
-/
theorem pid_dichotomy {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (d : ℕ)
    (P : Matrix (Fin d) (Fin d) O) :
    ∃ U W : Matrix (Fin d) (Fin d) O, W * U = 1 ∧ U * W = 1 ∧
      ∀ j, (∃ w : Fin d → O, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, ¬ IsUnit ((W * P) j k)) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin P)).smithNormalForm (Pi.basisFun O (Fin d))
  set U : Matrix (Fin d) (Fin d) O := (Pi.basisFun O (Fin d)).toMatrix snf.bM with hUdef
  set W : Matrix (Fin d) (Fin d) O := snf.bM.toMatrix (Pi.basisFun O (Fin d)) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  refine ⟨U, W, hWU, hUW, fun j => ?_⟩
  have hUcol : (fun i => U i j) = (snf.bM j : Fin d → O) := by
    funext i
    simp [hUdef, Module.Basis.toMatrix_apply]
  have hmem : ∀ k, (fun i => P i k) ∈ LinearMap.range (Matrix.mulVecLin P) := fun k =>
    ⟨Pi.single k 1, by funext i; simp⟩
  have hWP : ∀ k, (W * P) j k = snf.bM.repr (fun i => P i k) j := by
    intro k
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O (Fin d)) snf.bM (fun i => P i k)
    rw [← h, ← hWdef]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  by_cases h : ∃ i, snf.f i = j ∧ IsUnit (snf.a i)
  · obtain ⟨i, rfl, u, hu⟩ := h
    left
    have hN : (snf.bM (snf.f i) : Fin d → O) ∈ LinearMap.range (Matrix.mulVecLin P) := by
      have h1 : (snf.bM (snf.f i) : Fin d → O) = (↑u⁻¹ : O) • (snf.bN i : Fin d → O) := by
        rw [snf.snf, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (snf.bN i).2
    obtain ⟨w, hw⟩ := hN
    exact ⟨w, by rw [hUcol, ← hw]; rfl⟩
  · right
    intro k
    rw [hWP k]
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      have h2 := congrFun (snf.repr_comp_embedding_eq_smul ⟨_, hmem k⟩) i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : snf.bM.repr (fun i => P i k) (snf.f i) = snf.a i * snf.bN.repr ⟨_, hmem k⟩ i := h2
      rw [h3]
      intro hu
      exact h ⟨i, rfl, isUnit_of_mul_isUnit_left hu⟩
    · have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem k⟩ hj
      have h0' : snf.bM.repr (fun i => P i k) j = 0 := h0
      rw [h0']
      exact not_isUnit_zero

end GlobalTheory.SmithOE

namespace GlobalTheory.SmithOE

/- English proof (translation)
Introduce `l _ K bk _ d' P hP`. Establish `hfac` using `(GlobalTheory.OEDvr.main l K bk).2.2.2.1`. Set `P' : Matrix (Fin d') (Fin d') ↥bk.OE` to `Matrix.of fun i j => ⟨P i j, hP i j⟩`. Take `⟨U', W', hWU, hUW, hdich⟩` from `pid_dichotomy d' P'`. Establish `hP'map : P'.map bk.OE.subtype = P` using `by ext; rfl`.

Use `⟨U'.map bk.OE.subtype, W'.map bk.OE.subtype, fun i j => (U' i j).2, fun i j => (W' i j).2, ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero _) (map_one _)]`. Break down `hdich j with ⟨w, hw⟩ | hnu` into its components or cases. Use `left`.

Use `⟨fun i => (w i : WCb l), ?_⟩` and prove the remaining obligations. Rewrite using `[← hP'map]`. Use function extensionality and compare the values at `i`. Use `congrArg Subtype.val (congrFun hw i)` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.mulVec, dotProduct]`.

Simplify using `using this`. Use `right`. Introduce `k`. Establish `heq : ((W'.map bk.OE.subtype) * P) j k = (((W' * P') j k : ↥bk.OE) : WCb l)`. Rewrite using `[← hP'map, ← Matrix.map_mul]`.

Both sides reduce to the same expression. Rewrite using `[heq]`. Establish `hk` using `hnu k`. Generalize the expression as in `(W' * P') j k = x at hk ⊢`. Distinguish the cases in `hx : (x : WCb l) = 0`.

Rewrite using `[hx]`. Conclude with `dvd_zero _`. Take `⟨m, v, v', hv, hv', hvv, hxe⟩` from `hfac x x.2 hx`. Consider the cases of `m with`. Consider the case `zero`.

It suffices to derive a contradiction. Apply `hk` to reduce the goal to its premises. Use `isUnit_iff_exists_inv.2 ⟨⟨v', hv'⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x : WCb l) * v' = 1`. Rewrite using `[hxe, pow_zero, one_mul, hvv]`.

Consider the case `succ m`. Conclude with `⟨(l : WCb l) ^ m * v, by rw [hxe, pow_succ]; ring⟩`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE → ∀ (d' : ℕ) (P : Matrix (Fin d') (Fin d') (WCb l)), (∀ i j, P i j ∈ bk.OE) → ∃ U Uinv : Matrix (Fin d') (Fin d') (WCb l), (∀ i j, U i j ∈ bk.OE) ∧ (∀ i j, Uinv i j ∈ bk.OE) ∧ Uinv * U = 1 ∧ U * Uinv = 1 ∧ ∀ j, (∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, (l : WCb l) ∣ (Uinv * P) j k) := by
  intro l _ K bk _ d' P hP
  have hfac := (GlobalTheory.OEDvr.main l K bk).2.2.2.1
  let P' : Matrix (Fin d') (Fin d') ↥bk.OE := Matrix.of fun i j => ⟨P i j, hP i j⟩
  obtain ⟨U', W', hWU, hUW, hdich⟩ := pid_dichotomy d' P'
  have hP'map : P'.map bk.OE.subtype = P := by ext; rfl
  refine ⟨U'.map bk.OE.subtype, W'.map bk.OE.subtype, fun i j => (U' i j).2, fun i j => (W' i j).2,
    ?_, ?_, fun j => ?_⟩
  · rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases hdich j with ⟨w, hw⟩ | hnu
    · left
      refine ⟨fun i => (w i : WCb l), ?_⟩
      rw [← hP'map]
      funext i
      have := congrArg Subtype.val (congrFun hw i)
      rw [Matrix.mulVec, dotProduct] at this ⊢
      simpa using this
    · right
      intro k
      have heq : ((W'.map bk.OE.subtype) * P) j k = (((W' * P') j k : ↥bk.OE) : WCb l) := by
        rw [← hP'map, ← Matrix.map_mul]; rfl
      rw [heq]
      have hk := hnu k
      generalize (W' * P') j k = x at hk ⊢
      by_cases hx : (x : WCb l) = 0
      · rw [hx]; exact dvd_zero _
      obtain ⟨m, v, v', hv, hv', hvv, hxe⟩ := hfac x x.2 hx
      cases m with
      | zero =>
        exfalso
        apply hk
        refine isUnit_iff_exists_inv.2 ⟨⟨v', hv'⟩, Subtype.ext ?_⟩
        change (x : WCb l) * v' = 1
        rw [hxe, pow_zero, one_mul, hvv]
      | succ m =>
        exact ⟨(l : WCb l) ^ m * v, by rw [hxe, pow_succ]; ring⟩

end GlobalTheory.SmithOE
