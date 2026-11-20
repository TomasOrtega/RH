import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.CartanMove

variable {G G' : Type} [Group G] [Group G']

/- English proof (translation)
Rewrite using `[MonoidHom.map_mclosure, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem closure_symm_eq (e : G ≃* G') {l : ℕ} (t' : Fin l → G') :
    Submonoid.closure (Set.range fun j => e.symm (t' j)) =
      (Submonoid.closure (Set.range t')).map e.symm.toMonoidHom := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

/- English proof (translation)
Rewrite `hs` using `[closure_symm_eq]`. Take `⟨x, hx, rfl⟩` from `hs`. Simplify using `using hx`.
-/
theorem apply_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G}
    (hs : s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j))) :
    e s ∈ Submonoid.closure (Set.range t') := by
  rw [closure_symm_eq] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  simpa using hx

/- English proof (translation)
Rewrite using `[closure_symm_eq]`. Conclude with `⟨s, hs, rfl⟩`.
-/
theorem symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩

/- English proof (translation)
Take `⟨c', t', h1, h2, h3, h4⟩` from `h`. Establish `hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom` using `fun {x} hx => by`. Simplify `hx` using `[Subgroup.mem_comap]`. Use `⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i k`.

Simplify `h1 i (e k)` using `[Subgroup.mem_comap]`. Introduce `i j`. Conclude with `(h2 i j).map e.symm`. Introduce `g`. Take `⟨i, j, s, hs, k, hk, k', hk', hg⟩` from `h3 (e g)`.

Use `⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Simplify `hg` using `[map_mul]`. Introduce `s hs s' hs' k hk`. Take `⟨a, ha, b, hb, hab⟩` from `h4 (e s) (apply_mem_closure e t' hs) (e s') (apply_mem_closure e t' hs') (e k) hk`.

Use `⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Simplify `hab` using `[map_mul]`.
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
Introduce `G G' _ _ _ _ e h U hU`. Establish `hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G')`. Establish `: ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G)` using `rfl`. Rewrite using `[this]`. Conclude with `e.toHomeomorph.isOpenMap _ hU`.

Take `⟨K', hK'U, hoK', hcK', d, l, hC⟩` from `h _ hopen`. Use `⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨u, hu, hux⟩` from `hK'U hx`. Establish `: u = x` using `e.toMulEquiv.injective hux`.

Conclude with `this ▸ hu`. Conclude with `hoK'.preimage e.toHomeomorph.continuous`. Conclude with `e.toHomeomorph.isCompact_preimage.2 hcK'`.
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
