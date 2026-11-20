import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastRowMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem negGA_mem_fin (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem fockComp_mul_right (B : VertexFrames G) (i : ℕ) (hi : (Pair.chi i D.R.m : Pair T).InRange D.R.m)
    {f : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.grid i D.R.m)) (b h : FinPt G (.grid (i + 1) D.R.m)) :
    fockComp W B (.chi i D.R.m : Pair T) f a (b * h) =
      fockComp W B (.chi i D.R.m : Pair T) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m : Pair T) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.chi i D.R.m : Pair T) (a : GA D (G.V (Pair.chi i D.R.m : Pair T).small))
      ((b * h : FinPt G (.grid (i + 1) D.R.m)) : GA D _) =
      G.toPair (.chi i D.R.m : Pair T) a b * G.toPair (.chi i D.R.m : Pair T) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff, map_mul]
  have e2 : G.toPair (.chi i D.R.m : Pair T) 1 h.1 = (negGA _ h.1, (1 : GA D _)) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hi) W.θ W.θ_is (negGA _ h.1) (negGA_mem_fin _ h.2)
    1 (one_mem _) _ _ _ _ f _ hf]

/- English proof (translation)
Substitute using the available equality. Simplify using the standard rewrite rules.
-/
theorem update_grid_eq {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : FinPt G (.grid a D.R.m)) :
    Function.update y a v b = h ▸ v := by
  subst h; simp

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem cast_mul_grid {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ (y a * p) : FinPt G (.grid b D.R.m)) = y b * (h ▸ p : FinPt G (.grid b D.R.m)) := by
  subst h; rfl

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem cast_conj_grid {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ ((u (.grid a D.R.m))⁻¹ * p * u (.grid a D.R.m)) : FinPt G (.grid b D.R.m)) =
      (u (.grid b D.R.m))⁻¹ * (h ▸ p : FinPt G (.grid b D.R.m)) * u (.grid b D.R.m) := by
  subst h; rfl

end GlobalTheory.LastRowMove

namespace GlobalTheory.LastRowMove

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem rowMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
    IsThetaFunO W.ψ (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) (gs (lastIx D)) →
    rowMapV S gs (Function.update y D.R.m (y D.R.m * k)) = rowMapV S (Function.update gs (lastIx D) (rowShift S k (gs (lastIx D)))) y := by
  intro D T L sc G W U S gs y k hf
  unfold rowMapV
  refine congrArg (fun q => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) q D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dif_pos hjm, dif_pos hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_grid_eq (lastIx_succ D), cast_mul_grid (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_grid (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (gs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ _ (inRange_chi (lastIx D)) hf',
        show Function.update gs (lastIx D) (rowShift S k (gs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          rowShift S k (gs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dif_neg hjm, dif_neg hjm]

end GlobalTheory.LastRowMove
