import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem agree_div_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : (ψ i / ψ j) u = (ω i / ω j) u := by
  simp only [MonoidHom.div_apply, h i u hu, h j u hu]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem agree_triv_iff {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (x : k) :
    Triv (ψ i / ψ j) x ↔ Triv (ω i / ω j) x := by
  constructor
  · intro H u hu hx
    rw [← agree_div_apply h i j u hu]
    exact H u hu hx
  · intro H u hu hx
    rw [agree_div_apply h i j u hu]
    exact H u hu hx

/- English proof (translation)
Replace the relevant objects with their definitions. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem agree_nxt_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : nxt ψ m u = nxt ω m u := by
  unfold nxt
  split_ifs
  · exact h _ u hu
  · rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem agree_ev {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (x : k) :
    ev (ψ m / nxt ψ m) x = ev (ω m / nxt ω m) x := by
  unfold ev
  split_ifs with hx
  · have hv : valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) : k) = 1 := by
      simpa using hx
    rw [MonoidHom.div_apply, MonoidHom.div_apply, h m _ hv, agree_nxt_apply h m _ hv]
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem agree_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧
      ∀ r, Cut ψ r → Cut ω r := by
  intro k _ _ _ _ n ψ ω h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, agree_triv_iff h]
  · funext g
    unfold theta
    exact Finset.prod_congr rfl fun m _ => agree_ev h m _
  · intro H i a b j hi ha hb x hT
    rw [← agree_triv_iff h]
    exact H i a b j hi ha hb x ((agree_triv_iff h i j x).2 hT)
  · intro r H i j hi hj hT
    exact H i j hi hj ((agree_triv_iff h i j 1).2 hT)

end GlobalTheory.PsType
