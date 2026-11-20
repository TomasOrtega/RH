import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R K _ _ _ m lam g hg F`. Establish `hd : g.det ≠ 0` using `hg.ne_zero`. Unfold `nablaLTw nablaL`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨G, hG, rfl⟩`. Rewrite `hG` using `[Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _`. Rewrite using `[map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]`. Conclude with `hG`.

Introduce `hF`. Use `⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _`. Rewrite using `[map_smul]`.

Conclude with `hF`. Express the relevant statement in the definitionally equal form `g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F`. Rewrite using `[smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]`.
-/
theorem nabla_twist_mem : NablaLTwMem := by
  intro R K _ _ _ m lam g hg F
  have hd : g.det ≠ 0 := hg.ne_zero
  unfold nablaLTw nablaL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [Submodule.mem_comap] at hG
    change g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hG
  · intro hF
    refine ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      change rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _
      rw [map_smul]
      exact hF
    · change g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]

end Formalism.GradedWeylDivisibility
