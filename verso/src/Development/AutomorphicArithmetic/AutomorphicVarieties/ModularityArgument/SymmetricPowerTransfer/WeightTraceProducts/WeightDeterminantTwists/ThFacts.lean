import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
The claim follows from `MvPolynomial.eval_rename _ _ _`.
-/
private theorem swp_eval {I : Type} [Fintype I] {d : ℕ} (n : I → ℕ) (Q : Bi d n) (x : (I × Bool) × Fin d → ℂ) :
    MvPolynomial.eval x (swp d n Q).1 = MvPolynomial.eval (x ∘ UpperTheory.V.Z.Sym.Wt.flip I d) Q.1 := MvPolynomial.eval_rename _ _ _

/- English proof (translation)
Introduce `I _ j`. Establish `key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n), swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P)`. Introduce `n g P`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[swp_eval]`. Express the relevant statement in the definitionally equal form `MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 = MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1`. Rewrite using `[eval_mRep, eval_mRep, swp_eval]`. Use `congrArg (fun y => MvPolynomial.eval y P.1) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Take `⟨⟨v, b⟩, i⟩` from `p`. Apply the tactic sequence `cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]`. Establish `hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P`. Introduce `n P`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[swp_eval, swp_eval]`. Use `congrArg (fun y => MvPolynomial.eval y P.1) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Simplify using `[UpperTheory.V.Z.Sym.Wt.flip]`. Establish `hsg : ∀ S : I → Bool, sg S * sg S = 1`. Introduce `S`. Simplify using `only [sg, ← Finset.prod_mul_distrib]`.

Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `v _`. Apply the tactic sequence `split_ifs <;> norm_num`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `P`. Use function extensionality and compare the values at `S`. Simplify using `only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]`. Introduce `g`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `P`. Use function extensionality and compare the values at `S`. Simplify using `only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]`.
-/
theorem UpperTheory.V.Z.Sym.Wt.thFacts :
    UpperTheory.V.Z.Sym.Wt.ThFacts := by
  intro I _ j
  have key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n),
      swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P) := by
    intro n g P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval]
    change MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 =
      MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1
    rw [eval_mRep, eval_mRep, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    obtain ⟨⟨v, b⟩, i⟩ := p
    cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]
  have hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P := by
    intro n P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hsg : ∀ S : I → Bool, sg S * sg S = 1 := by
    intro S
    simp only [sg, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]
  · intro g
    apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]
