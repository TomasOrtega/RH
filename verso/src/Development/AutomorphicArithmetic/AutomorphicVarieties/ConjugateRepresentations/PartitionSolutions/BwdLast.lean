import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan`. Take `⟨P, hP1, hPeq, hPvan⟩` from `partOp Γ V S I d G φ hφ q`. Establish `hconst : ∀ i j : I, u [i] = u [j]`. Introduce `i j`. Establish `h` using `hhd [i, j] rfl`.

Simplify using `[UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h`. Establish `h' : u [j] - u [i] = 0`. Rewrite using `[sub_eq_add_neg]`. Simplify using `using h`. Conclude with `(sub_eq_zero.mp h').symm`.

Use `⟨P (fun i => u [i]), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ`. Establish `hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i]`. Use function extensionality and compare the values at `i`. Establish `h` using `hu γ [γ⁻¹ • i] rfl`.

Simplify using `only [List.map_cons, List.map_nil, smul_inv_smul] at h`. Conclude with `h.symm`. Rewrite using `[← hPeq γ (fun i => u [i]), hinv]`. Introduce `x hx match x, hx with`. Consider the case `[i], _`.

Establish `hfun : (fun j => u [j]) = fun _ => u [i]`. Use function extensionality and compare the values at `j`. Conclude with `hconst j i`. Rewrite using `[hfun, hP1]`. Introduce `s p hp`.

Apply `hPvan` to reduce the goal to its premises. Introduce `i hne`. Use `hvan [i] rfl s p hp ?_` and prove the remaining obligations. Introduce `i' hi'`. Rewrite `hi'` using `[List.mem_singleton]`.

Rewrite using `[hi']`. Conclude with `hC i s p hp hne`.
-/
theorem UpperTheory.V.Cj.A.bwdLast :
    BwdLast := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan
  obtain ⟨P, hP1, hPeq, hPvan⟩ := partOp Γ V S I d G φ hφ q
  have hconst : ∀ i j : I, u [i] = u [j] := by
    intro i j
    have h := hhd [i, j] rfl
    simp [UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h
    have h' : u [j] - u [i] = 0 := by
      rw [sub_eq_add_neg]
      simpa using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨P (fun i => u [i]), ?_, ?_, ?_⟩
  · intro γ
    have hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i] := by
      funext i
      have h := hu γ [γ⁻¹ • i] rfl
      simp only [List.map_cons, List.map_nil, smul_inv_smul] at h
      exact h.symm
    rw [← hPeq γ (fun i => u [i]), hinv]
  · intro x hx
    match x, hx with
    | [i], _ =>
      have hfun : (fun j => u [j]) = fun _ => u [i] := by
        funext j
        exact hconst j i
      rw [hfun, hP1]
  · intro s p hp
    apply hPvan
    intro i hne
    refine hvan [i] rfl s p hp ?_
    intro i' hi'
    rw [List.mem_singleton] at hi'
    rw [hi']
    exact hC i s p hp hne
