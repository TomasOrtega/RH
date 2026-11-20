import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.DetNatAbsLeProdL1Norms

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `ι _ v b hv hb`. Use `haveI := Fintype.ofFinite ι`. Use `set N := Submodule.span ℤ (Set.range v)`. Set `bE : Module.Basis ι ℤ (ι →₀ ℤ)` to `Finsupp.basisSingleOne`. Set `bN : Module.Basis ι ℤ N` to `Module.Basis.span hv`.

Establish `hfin : Finite ((ι →₀ ℤ) ⧸ N)`. Apply `Submodule.finiteQuotientOfFreeOfRankEq` to reduce the goal to its premises. Rewrite using `[Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bE]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.natAbs_det_basis_change bE N bN]`.

Establish `hcoe : ((↑) ∘ bN : ι → (ι →₀ ℤ)) = v`. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hv i)`. Rewrite using `[hcoe, Module.Basis.det_apply, ← Matrix.det_transpose]`. Use `(det_natAbs_le_prod_l1_norms ι _).trans ?_` and prove the remaining obligations.

Establish `hrow : ∀ i, ∑ k, ((bE.toMatrix v).transpose i k).natAbs = l1 (v i)`. Introduce `i`. Simplify using `only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, bE, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, l1]`. Rewrite using `[Finsupp.sum_fintype]`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[hrow]`. Rewrite using `[Nat.card_eq_fintype_card, ← Finset.card_univ]`. Conclude with `Finset.prod_le_pow_card _ _ _ (fun i _ => hb i)`.
-/
theorem UpperTheory.V.KH.indexLe :
    ∀ (ι : Type) [Finite ι] (v : ι → (ι →₀ ℤ)) (b : ℕ), LinearIndependent ℤ v → (∀ i, l1 (v i) ≤ b) →
      CardLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ (Set.range v)) (b ^ Nat.card ι) := by
  intro ι _ v b hv hb
  classical
  haveI := Fintype.ofFinite ι
  set N := Submodule.span ℤ (Set.range v)
  let bE : Module.Basis ι ℤ (ι →₀ ℤ) := Finsupp.basisSingleOne
  let bN : Module.Basis ι ℤ N := Module.Basis.span hv
  have hfin : Finite ((ι →₀ ℤ) ⧸ N) := by
    apply Submodule.finiteQuotientOfFreeOfRankEq
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bE]
  refine ⟨hfin, ?_⟩
  rw [← Submodule.natAbs_det_basis_change bE N bN]
  have hcoe : ((↑) ∘ bN : ι → (ι →₀ ℤ)) = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  rw [hcoe, Module.Basis.det_apply, ← Matrix.det_transpose]
  refine (det_natAbs_le_prod_l1_norms ι _).trans ?_
  have hrow : ∀ i, ∑ k, ((bE.toMatrix v).transpose i k).natAbs = l1 (v i) := by
    intro i
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, bE, Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, l1]
    rw [Finsupp.sum_fintype]
    simp
  simp_rw [hrow]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.prod_le_pow_card _ _ _ (fun i _ => hb i)
