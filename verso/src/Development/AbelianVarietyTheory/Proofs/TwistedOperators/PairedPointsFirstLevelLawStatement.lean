import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormulaStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv in

/- English proof (translation)
Introduce `hP hS`. Take `⟨a₁, h₁⟩` from `GlobalTheory.T.first_column_vector_sum_formula hP hS`. Take `⟨a₂, h₂⟩` from `hS`. Use `⟨max a₁ a₂, fun ε CF hC => ?_⟩` and prove the remaining obligations. Establish `hb₁` using `h₁ ε CF (le_of_max_le_left hC)`.

Establish `hb₂` using `h₂ ε CF (le_of_max_le_right hC)`. Take `⟨x₁, hc₁⟩` from `hb₁`. Take `⟨x₂, hc₂⟩` from `hb₂`. Use `⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩` and prove the remaining obligations. Introduce `t a β hβ τ hτ x y k hkl hk v w`.

Establish `key` using `hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk`. Establish `hOK` using `hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a`. Generalize the expression as in `hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at key ⊢`. Establish `hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.2 i))` using `fun d hd => ⟨fun j => vec_theta ch.S.toGridChoice (defPair_top t j) (inRange_top t j) _ ((hOK.vec β τ hτ d hd).1 j), fun i => vec_theta ch.S.toGridChoice (defPair_chi i) (inRange_chi i) _ ((hOK.vec β τ hτ d hd).2 i)⟩`. Take `⟨M, hM⟩` from `GlobalTheory.T.exists_multilinear_columnRowKernelPairing ch.S.toGridChoice t x y v w`.

Establish `thr : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)`. Introduce `d hd i`. Distinguish the cases in `hi0 : i = firstIx D`. Substitute `hi0` using the available equality. Simplify using `only [movedRow, Function.update_self]`.

Conclude with `rowShift0_theta ch.S.toGridChoice k ((hth d hd).2 _)`. Simplify using `only [movedRow, Function.update_of_ne hi0]`. Conclude with `(hth d hd).2 i`. Establish `thr' : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D) (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)`. Introduce `d hd i`.

Distinguish the cases in `hi0 : i = firstIx D`. Substitute `hi0` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `GlobalTheory.OrientedHeis.theta_smul χk (thr d hd _)`. Simplify using `only [Function.update_of_ne hi0]`.

Conclude with `thr d hd i`. Establish `lhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v w = τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i))`. Simplify using `only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[hM, colMap_eq, rowMap_eq, rowMapV_update_zero ch.S.toGridChoice _ y k ((hth d hd).2 _)]`. Establish `e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => ch.S.Z.vec (d.1 j)`. Use function extensionality and compare the values at `fun j => coe_toTh ch.W _ ((hth d hd).1 j)`. Establish `e2 : (fun i : Fin D.R.m => (toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) : WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) = movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))`. Use function extensionality and compare the values at `fun i => coe_toTh ch.W _ (thr d hd i)`.

Rewrite using `[e1, e2]`. Establish `rhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w = τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (ch.S.Z.vec (d.2 i)))`. Simplify using `only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[hM, colMap_eq, rowMap_eq]`. Establish `e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => ch.S.Z.vec (d.1 j)`. Use function extensionality and compare the values at `fun j => coe_toTh ch.W _ ((hth d hd).1 j)`. Establish `e2 : (fun i : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.2 i)) : WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) = fun i : Fin D.R.m => ch.S.Z.vec (d.2 i)`. Use function extensionality and compare the values at `fun i => coe_toTh ch.W _ ((hth d hd).2 i)`.

Rewrite using `[e1, e2]`. Establish `hscale : ∀ d ∈ τ.support, M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D) (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) = χk * M (fun …`. Introduce `d hd`. Establish `eg : (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T) (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D) (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) = Function.update (fun i : Fin D.R.m => toTh ch …`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi0 : i = firstIx D`. Substitute `hi0` using the available equality. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `coe_toTh ch.W _ (thr' d hd (firstIx D))`. Simplify using `only [Function.update_self] at h1 ⊢`.

Rewrite using `[h1, Submodule.coe_smul, coe_toTh ch.W _ (thr d hd _)]`. Simplify using `only [Function.update_of_ne hi0]`. Rewrite using `[eg, MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]`. Rewrite using `[LinearMap.map_smul, smul_eq_mul, lhs, rhs, Finsupp.sum, Finset.mul_sum]`. Establish `step1 : (∑ d ∈ τ.support, χk * (τ d * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)))) = τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (Function.update …`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hscale d hd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[step1]`.

Use `GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq M τ _ _ _ _ fun xs ys => ?_` and prove the remaining obligations. Establish `hk'` using `key xs ys`. Simplify using `only [Finsupp.sum] at hk' ⊢`. Use `(?_ : _ = χk * _).trans (hk'.trans (Finset.sum_congr rfl fun d hd => ?_))` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Simplify using `only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ (thr' d hd _)]`. Rewrite using `[prod_update_smul, Function.update_eq_self]`. Simplify using `only [movedRow]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ ((hth d hd).2 _)]`.
-/
theorem paired_points_first_level_law : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := GlobalTheory.T.first_column_vector_sum_formula hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ x y k hkl hk v w
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at key ⊢
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta ch.S.toGridChoice (defPair_top t j) (inRange_top t j) _ ((hOK.vec β τ hτ d hd).1 j),
      fun i => vec_theta ch.S.toGridChoice (defPair_chi i) (inRange_chi i) _ ((hOK.vec β τ hτ d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_multilinear_columnRowKernelPairing ch.S.toGridChoice t x y v w
  have thr : ∀ d ∈ τ.support, ∀ i,
      IsThetaFunO ch.W.ψ _ _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [movedRow, Function.update_self]
      exact rowShift0_theta ch.S.toGridChoice k ((hth d hd).2 _)
    · simp only [movedRow, Function.update_of_ne hi0]
      exact (hth d hd).2 i
  have thr' : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _
      (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
        (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [Function.update_self]
      exact GlobalTheory.OrientedHeis.theta_smul χk (thr d hd _)
    · simp only [Function.update_of_ne hi0]
      exact thr d hd i
  have lhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, rowMapV_update_zero ch.S.toGridChoice _ y k ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) :=
      funext fun i => coe_toTh ch.W _ (thr d hd i)
    rw [e1, e2]
  have rhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (ch.S.Z.vec (d.2 i))) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.2 i)) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => ch.S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh ch.W _ ((hth d hd).2 i)
    rw [e1, e2]

  have hscale : ∀ d ∈ τ.support,
      M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
      χk * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    intro d hd
    have eg : (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T)
        (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
        Function.update (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T) (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i))
          (firstIx D) (χk • toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D))) := by
      funext i
      by_cases hi0 : i = firstIx D
      · subst hi0
        apply Subtype.ext
        have h1 := coe_toTh ch.W _ (thr' d hd (firstIx D))
        simp only [Function.update_self] at h1 ⊢
        rw [h1, Submodule.coe_smul, coe_toTh ch.W _ (thr d hd _)]
      · simp only [Function.update_of_ne hi0]
    rw [eg, MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]
  rw [LinearMap.map_smul, smul_eq_mul, lhs, rhs, Finsupp.sum, Finset.mul_sum]
  have step1 : (∑ d ∈ τ.support, χk * (τ d * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)))) =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hscale d hd]
    ring
  rw [step1]
  refine GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq M τ _ _ _ _ fun xs ys => ?_
  have hk' := key xs ys
  simp only [Finsupp.sum] at hk' ⊢
  refine (?_ : _ = χk * _).trans (hk'.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ (thr' d hd _)]
    rw [prod_update_smul, Function.update_eq_self]
    simp only [movedRow]
    ring
  · simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ ((hth d hd).2 _)]

end GlobalTheory.FirstRowVertex

end
