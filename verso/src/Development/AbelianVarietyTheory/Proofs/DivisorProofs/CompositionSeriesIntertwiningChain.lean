import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair

open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL

namespace GlobalTheory.FiltStepCut

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exists_prod_maps {J : Type} [AddCommGroup J] [Module ℂ J] {N : ℕ}
    (S : Fin (N + 1) → Submodule ℂ J) (t₀ : Fin N) (Q : Fin N → Module.End ℂ J)
    (hQ : ∀ t, t ≠ t₀ → ∀ w ∈ S t.succ, Q t w ∈ S t.castSucc) (j j' : Fin (N + 1)) :
    j ≤ j' → (∀ t : Fin N, j ≤ t.castSucc → t.succ ≤ j' → t ≠ t₀) →
      ∃ l : List (Fin N), (∀ t ∈ l, t ≠ t₀) ∧ ∀ w ∈ S j', (l.map Q).prod w ∈ S j := by
  induction j' using Fin.induction with
  | zero =>
    intro h _
    obtain rfl : j = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨[], by simp, by simp⟩
  | succ i ih =>
    intro h ht
    rcases h.eq_or_lt with rfl | h
    · exact ⟨[], by simp, by simp⟩
    · have h' : j ≤ i.castSucc := Fin.le_castSucc_iff.2 h
      have hi : i ≠ t₀ := ht i h' le_rfl
      obtain ⟨l, hl, hm⟩ := ih h' fun t a b => ht t a (b.trans (Fin.castSucc_lt_succ).le)
      refine ⟨l ++ [i], ?_, fun w hw => ?_⟩
      · intro t htl
        rcases List.mem_append.1 htl with a | a
        · exact hl t a
        · rw [List.mem_singleton.1 a]; exact hi
      · rw [List.map_append, List.prod_append]
        simpa using hm _ (hQ i hi w hw)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_prod_mem_range : ∀ (L J : Type) [Group L] [AddCommGroup J] [Module ℂ J]
    (ρ : Representation ℂ L J) (N : ℕ)
    (S : Fin (N + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
    ∀ (t₀ : Fin N) (z : Fin N → L) (c : Fin N → ℂ), (∀ t y, y * z t = z t * y) →
      (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) (z t) y = c t • y) →
      ∃ (l : List (Fin N))
        (A : Representation.IntertwiningMap (subQuot (S t₀.succ) (S t₀.castSucc)) ρ),
        (∀ t ∈ l, t ≠ t₀) ∧ ∀ w, (l.map fun t => ρ (z t) - c t • (1 : Module.End ℂ J)).prod w ∈
          LinearMap.range A.toLinearMap := by
  intro L J _ _ _ ρ N S _ h0 hN t₀ z c hz hc
  set Q : Fin N → Module.End ℂ J := fun t => ρ (z t) - c t • (1 : Module.End ℂ J) with hQdef
  have hQ : ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, Q t w ∈ (S t.castSucc).toSubmodule := by
    intro t ht w hw
    have h1 := hc t ht (Submodule.Quotient.mk ⟨w, hw⟩)
    rw [← Submodule.Quotient.mk_smul] at h1
    exact (Submodule.Quotient.eq ((S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)
      (x := (S t.succ).toRepresentation (z t) ⟨w, hw⟩) (y := c t • (⟨w, hw⟩ : (S t.succ).toSubmodule))).1 h1
  have hcomm : ∀ t y, Commute (ρ y) (Q t) := by
    intro t y
    refine Commute.sub_right ?_ ((Commute.one_right _).smul_right _)
    show ρ y * ρ (z t) = ρ (z t) * ρ y
    rw [← map_mul, ← map_mul, hz]
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ t₀.succ (Fin.last N)
    (Fin.le_last _) (by
      rintro t a - rfl
      exact absurd a (not_le.2 Fin.castSucc_lt_succ))
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_prod_maps (fun j => (S j).toSubmodule) t₀ Q hQ 0 t₀.castSucc
    (Fin.zero_le _) (by
      rintro t - a rfl
      exact absurd a (not_le.2 Fin.castSucc_lt_succ))
  have hP : ∀ y, Commute (ρ y) (l₂.map Q).prod := fun y =>
    Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact hcomm t y
  have hker : (S t₀.castSucc).toSubmodule.comap (S t₀.succ).toSubmodule.subtype ≤
      LinearMap.ker ((l₂.map Q).prod ∘ₗ (S t₀.succ).toSubmodule.subtype) := by
    intro x hx
    have := hm₂ _ hx
    simp only [h0] at this
    exact this
  refine ⟨l₂ ++ l₁, ⟨Submodule.liftQ _ _ hker, fun g => Submodule.linearMap_qext _
    (LinearMap.ext fun x => ?_)⟩, ?_, fun w => ?_⟩
  · exact (LinearMap.congr_fun (hP g).eq (x : J)).symm
  · intro t htl
    rcases List.mem_append.1 htl with a | a
    · exact hl₂ t a
    · exact hl₁ t a
  · have hw : w ∈ (S (Fin.last N)).toSubmodule := by rw [hN]; trivial
    refine ⟨Submodule.Quotient.mk ⟨_, hm₁ w hw⟩, ?_⟩
    rw [List.map_append, List.prod_append]
    rfl

end GlobalTheory.FiltStepCut
