import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Introduce `G V V' W _ _ _ _ _ _ _ ρ ρ' ρW σ T hTs hTg M hM R hlin hg hex hiff`. Establish `huniq : ∀ v w1 w2, w1 ∈ M → w2 ∈ M → R v w1 → R v w2 → w1 = w2`. Introduce `v w1 w2 m1 m2 r1 r2`. Establish `h` using `hlin (-1) v v w1 w2 r1 r2`. Establish `hm : σ (-1) • w1 + w2 ∈ M` using `M.add_mem (M.smul_mem _ m1) m2`.

Establish `h0 : (-1 : ℂ) • v + v = 0` using `by simp`. Rewrite `h` using `[h0]`. Establish `h1` using `(hiff 0 _ hm h).1 rfl`. Rewrite `h1` using `[map_neg, map_one, neg_one_smul, neg_add_eq_zero]`. Conclude with `h1`.

Establish `hR0 : R 0 0`. Take `⟨w, hw, hr⟩` from `hex 0`. Rewrite `hr` using `[(hiff 0 w hw hr).1 rfl]`. Then use the resulting hypothesis. Use `choose j hjM hjR using fun v' : V' => hex (T.symm v')`. Establish `hTsymm_smul : ∀ (c : ℂ) (v' : V'), T.symm (c • v') = σ.symm c • T.symm v'`.

Introduce `c v'`. Apply `T.injective` to reduce the goal to its premises. Rewrite using `[hTs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Establish `hTsymm_g : ∀ (g : G) (v' : V'), T.symm (ρ' g v') = ρ g (T.symm v')`. Introduce `g v'`.

Apply `T.injective` to reduce the goal to its premises. Rewrite using `[hTg, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`. Set `J : V' →ₗ[ℂ] W` to `{ toFun := j map_add' := by`. Introduce `a b`. Apply `huniq (T.symm (a + b)) _ _ (hjM _) (M.add_mem (hjM a) (hjM b)) (hjR _)` to reduce the goal to its premises.

Establish `h` using `hlin 1 _ _ _ _ (hjR a) (hjR b)`. Simplify `h` using `[map_add]`. Use the proof step `map_smul' := by`. Introduce `c a`. Apply `huniq (T.symm (c • a)) _ _ (hjM _) (M.smul_mem c (hjM a)) (hjR _)` to reduce the goal to its premises.

Establish `h` using `hlin (σ.symm c) _ _ _ _ (hjR a) hR0`. Simplify `h }` using `[hTsymm_smul]`. Use `⟨J, ?_, hjM, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v' hv'`.

Establish `h` using `(hiff (T.symm v') (j v') (hjM v') (hjR v')).2 hv'`. Simplify using `using congrArg T h`. Introduce `g v'`. Apply `huniq (T.symm (ρ' g v')) _ _ (hjM _) (hM g _ (hjM v')) (hjR _)` to reduce the goal to its premises. Rewrite using `[hTsymm_g]`.

Conclude with `hg g _ _ (hjR v')`.
-/
theorem UpperTheory.V.Cj.graph :
    UpperTheory.V.Cj.Graph := by
  intro G V V' W _ _ _ _ _ _ _ ρ ρ' ρW σ T hTs hTg M hM R hlin hg hex hiff
  have huniq : ∀ v w1 w2, w1 ∈ M → w2 ∈ M → R v w1 → R v w2 → w1 = w2 := by
    intro v w1 w2 m1 m2 r1 r2
    have h := hlin (-1) v v w1 w2 r1 r2
    have hm : σ (-1) • w1 + w2 ∈ M := M.add_mem (M.smul_mem _ m1) m2
    have h0 : (-1 : ℂ) • v + v = 0 := by simp
    rw [h0] at h
    have h1 := (hiff 0 _ hm h).1 rfl
    rw [map_neg, map_one, neg_one_smul, neg_add_eq_zero] at h1
    exact h1
  have hR0 : R 0 0 := by
    obtain ⟨w, hw, hr⟩ := hex 0
    rwa [(hiff 0 w hw hr).1 rfl] at hr
  choose j hjM hjR using fun v' : V' => hex (T.symm v')
  have hTsymm_smul : ∀ (c : ℂ) (v' : V'), T.symm (c • v') = σ.symm c • T.symm v' := by
    intro c v'
    apply T.injective
    rw [hTs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hTsymm_g : ∀ (g : G) (v' : V'), T.symm (ρ' g v') = ρ g (T.symm v') := by
    intro g v'
    apply T.injective
    rw [hTg, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let J : V' →ₗ[ℂ] W :=
    { toFun := j
      map_add' := by
        intro a b
        apply huniq (T.symm (a + b)) _ _ (hjM _) (M.add_mem (hjM a) (hjM b)) (hjR _)
        have h := hlin 1 _ _ _ _ (hjR a) (hjR b)
        simpa [map_add] using h
      map_smul' := by
        intro c a
        apply huniq (T.symm (c • a)) _ _ (hjM _) (M.smul_mem c (hjM a)) (hjR _)
        have h := hlin (σ.symm c) _ _ _ _ (hjR a) hR0
        simpa [hTsymm_smul] using h }
  refine ⟨J, ?_, hjM, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v' hv'
    have h := (hiff (T.symm v') (j v') (hjM v') (hjR v')).2 hv'
    simpa using congrArg T h
  · intro g v'
    apply huniq (T.symm (ρ' g v')) _ _ (hjM _) (hM g _ (hjM v')) (hjR _)
    rw [hTsymm_g]
    exact hg g _ _ (hjR v')
