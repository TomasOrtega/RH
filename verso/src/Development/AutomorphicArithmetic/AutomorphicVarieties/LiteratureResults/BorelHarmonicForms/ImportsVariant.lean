import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IndepAbs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ a d q s π hπ ω h0 hV c hc`. Establish `hind : iSupIndep fun i => (π i).V` using `UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx) (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))`. Establish `key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0`. Introduce `X k i`. Establish `h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))), (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X` using `fun t f => by`.

Proceed by induction on `t using Finset.cons_induction with`. Consider the case `empty => rfl`. Consider the case `cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, AlternatingMap.add_apply, ih]`. Establish `h1 : ∑ j, c j • cmp k (ω j X) = 0`. Establish `h2` using `congrArg (fun η => cmp k (η X)) hc`.

Simplify `h2` using `only [h, map_sum, AlternatingMap.smul_apply, map_smul, AlternatingMap.zero_apply, map_zero]`. Conclude with `(iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X)) (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)`. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hci`. Use `h0 i (AlternatingMap.ext fun X => ?_)` and prove the remaining obligations.

Rewrite using `[← sum_cmp (ω i X), AlternatingMap.zero_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]`.
-/
theorem UpperTheory.V.Lit.Bor.indep :
    UpperTheory.V.Lit.Bor.Indep := by
  intro E _ _ _ a d q s π hπ ω h0 hV c hc
  have hind : iSupIndep fun i => (π i).V :=
    UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx)
      (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))
  have key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0 := by
    intro X k i
    have h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))),
        (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X := fun t f => by
      induction t using Finset.cons_induction with
      | empty => rfl
      | cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, AlternatingMap.add_apply, ih]
    have h1 : ∑ j, c j • cmp k (ω j X) = 0 := by
      have h2 := congrArg (fun η => cmp k (η X)) hc
      simpa only [h, map_sum, AlternatingMap.smul_apply, map_smul, AlternatingMap.zero_apply, map_zero] using h2
    exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X))
      (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)
  funext i
  by_contra hci
  refine h0 i (AlternatingMap.ext fun X => ?_)
  rw [← sum_cmp (ω i X), AlternatingMap.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]
