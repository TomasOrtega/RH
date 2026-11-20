import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.CartanMove

variable {G G' : Type} [Group G] [Group G']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem closure_symm_eq (e : G ≃* G') {l : ℕ} (t' : Fin l → G') :
    Submonoid.closure (Set.range fun j => e.symm (t' j)) =
      (Submonoid.closure (Set.range t')).map e.symm.toMonoidHom := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts.
-/
theorem apply_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G}
    (hs : s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j))) :
    e s ∈ Submonoid.closure (Set.range t') := by
  rw [closure_symm_eq] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  simpa using hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isCartan_comap (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by
  obtain ⟨c', t', h1, h2, h3, h4⟩ := h
  have hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom := fun {x} hx => by
    simpa [Subgroup.mem_comap] using hx
  refine ⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [Subgroup.mem_comap] using h1 i (e k)
  · intro i j
    exact (h2 i j).map e.symm
  · intro g
    obtain ⟨i, j, s, hs, k, hk, k', hk', hg⟩ := h3 (e g)
    refine ⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩
    apply e.injective
    simpa [map_mul] using hg
  · intro s hs s' hs' k hk
    obtain ⟨a, ha, b, hb, hab⟩ := h4 (e s) (apply_mem_closure e t' hs) (e s')
      (apply_mem_closure e t' hs') (e k) hk
    refine ⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩
    apply e.injective
    simpa [map_mul] using hab

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem stMove : StMove := by
  intro G G' _ _ _ _ e h U hU
  have hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') := by
    have : ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G) := rfl
    rw [this]
    exact e.toHomeomorph.isOpenMap _ hU
  obtain ⟨K', hK'U, hoK', hcK', d, l, hC⟩ := h _ hopen
  refine ⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hK'U hx
    have : u = x := e.toMulEquiv.injective hux
    exact this ▸ hu
  · exact hoK'.preimage e.toHomeomorph.continuous
  · exact e.toHomeomorph.isCompact_preimage.2 hcK'

end GlobalTheory.CompanionTheory.CartanMove
