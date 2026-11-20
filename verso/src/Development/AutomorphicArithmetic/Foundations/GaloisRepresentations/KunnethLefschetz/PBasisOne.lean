import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Introduce `F M _ _ _ _ lam hlam`. Distinguish the cases in `h0 : lam = 0`. Use `haveI := hlam h0`. Conclude with `⟨0, Module.Basis.empty M, fun t => t.elim0⟩`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h0 (LinearMap.ext hc)`. Use `set v : M := (lam x)⁻¹ • x with hvdef`. Establish `hv : lam v = 1`.

Rewrite using `[hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]`. Use `set N := LinearMap.ker lam`. Set `e` to `Module.finBasis F N`. Set `f : Fin (Module.finrank F N + 1) → M` to `Fin.cons v (fun i => v + (e i : M))`. Establish `hrange : LinearMap.range lam = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `c _`. Conclude with `⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩`. Establish `hcard : Fintype.card (Fin (Module.finrank F N + 1)) = Module.finrank F M`. Rewrite using `[Fintype.card_fin, ← LinearMap.finrank_range_add_finrank_ker lam, hrange, finrank_top, Module.finrank_self, add_comm]`.

Establish `hvmem : v ∈ Submodule.span F (Set.range f)` using `Submodule.subset_span ⟨0, by simp [f]⟩`. Establish `hemem : ∀ i, (e i : M) ∈ Submodule.span F (Set.range f)`. Introduce `i`. Establish `h1 : v + (e i : M) ∈ Submodule.span F (Set.range f)` using `Submodule.subset_span ⟨i.succ, by simp [f]⟩`. Use `Submodule.sub_mem _ h1 hvmem` as an intermediate fact.

Simplify using `using this`. Establish `hNmem : ∀ y : N, (y : M) ∈ Submodule.span F (Set.range f)`. Introduce `y`. Rewrite using `[← e.sum_repr y]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`.

Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hemem i))`. Establish `hspan : ⊤ ≤ Submodule.span F (Set.range f)`. Introduce `z _`. Establish `hz : z - lam z • v ∈ N`. Rewrite using `[LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]`.

Establish `h2` using `hNmem ⟨_, hz⟩`. Establish `h3` using `Submodule.add_mem _ h2 (Submodule.smul_mem _ (lam z) hvmem)`. Simplify using `using h3`. Use `⟨_, basisOfTopLeSpanOfCardEqFinrank f hspan hcard, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfTopLeSpanOfCardEqFinrank]`.

Use `Fin.cases ?_ (fun i => ?_) t` and prove the remaining obligations. Simplify `hv` using `[f]`. Establish `hk : lam (e i : M) = 0` using `(e i).2`. Simplify using `[f, hv, hk]`.
-/
theorem basisOne_holds : BasisOne := by
  intro F M _ _ _ _ lam hlam
  by_cases h0 : lam = 0
  · haveI := hlam h0
    exact ⟨0, Module.Basis.empty M, fun t => t.elim0⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (LinearMap.ext hc)
  set v : M := (lam x)⁻¹ • x with hvdef
  have hv : lam v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  set N := LinearMap.ker lam
  let e := Module.finBasis F N
  let f : Fin (Module.finrank F N + 1) → M := Fin.cons v (fun i => v + (e i : M))
  have hrange : LinearMap.range lam = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hcard : Fintype.card (Fin (Module.finrank F N + 1)) = Module.finrank F M := by
    rw [Fintype.card_fin, ← LinearMap.finrank_range_add_finrank_ker lam, hrange, finrank_top,
      Module.finrank_self, add_comm]
  have hvmem : v ∈ Submodule.span F (Set.range f) :=
    Submodule.subset_span ⟨0, by simp [f]⟩
  have hemem : ∀ i, (e i : M) ∈ Submodule.span F (Set.range f) := by
    intro i
    have h1 : v + (e i : M) ∈ Submodule.span F (Set.range f) :=
      Submodule.subset_span ⟨i.succ, by simp [f]⟩
    have := Submodule.sub_mem _ h1 hvmem
    simpa using this
  have hNmem : ∀ y : N, (y : M) ∈ Submodule.span F (Set.range f) := by
    intro y
    rw [← e.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hemem i))
  have hspan : ⊤ ≤ Submodule.span F (Set.range f) := by
    intro z _
    have hz : z - lam z • v ∈ N := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have h2 := hNmem ⟨_, hz⟩
    have h3 := Submodule.add_mem _ h2 (Submodule.smul_mem _ (lam z) hvmem)
    simpa using h3
  refine ⟨_, basisOfTopLeSpanOfCardEqFinrank f hspan hcard, fun t => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  refine Fin.cases ?_ (fun i => ?_) t
  · simpa [f] using hv
  · have hk : lam (e i : M) = 0 := (e i).2
    simp [f, hv, hk]

end UpperTheory.Gal.KunnethLefschetz
