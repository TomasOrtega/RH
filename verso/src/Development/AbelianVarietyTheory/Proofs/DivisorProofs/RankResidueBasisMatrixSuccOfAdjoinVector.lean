import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `hϖ h1 h2 h3 h4 h5`. Use `set bar := residue O with hbar`. Establish `hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O), (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v)`. Introduce `A v`. Use function extensionality and compare the values at `i`.

Conclude with `(RingHom.map_mulVec bar A v i).symm`. Establish `hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z`. Introduce `z`. Use `⟨fun i => (residue_surjective (z i)).choose, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Conclude with `(residue_surjective (z i)).choose_spec`. Use `set V := LinearMap.range (As.map bar).mulVecLin`. Use `set Wc := LinearMap.range (Ac.map bar).mulVecLin`. Use `set xb : Fin n → ResidueField O := bar ∘ x`. Establish `hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb}`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `v ⟨z, rfl⟩`. Take `⟨w, rfl⟩` from `hlift z`. Take `⟨u, c, hc⟩` from `h2 w`. Rewrite using `[Matrix.mulVecLin_apply, hmap, hc]`.

Establish `: bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb`. Rewrite using `[hmap]`. Use function extensionality and compare the values at `i`. Simplify using `[xb]`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))`. Apply `sup_le` to reduce the goal to its premises. Introduce and unpack `v ⟨z, rfl⟩`. Take `⟨u, rfl⟩` from `hlift z`. Take `⟨w, hw⟩` from `h4 u`.

Use `⟨bar ∘ w, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Take `⟨w, hw⟩` from `h3`. Conclude with `⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩`.

Establish `hxb : xb ∉ Wc`. Introduce and unpack `⟨z, hz⟩`. Take `⟨u, rfl⟩` from `hlift z`. Rewrite `hz` using `[Matrix.mulVecLin_apply, hmap]`. Establish `hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ}`.

Introduce `a`. Rewrite using `[← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]`. Use `congrFun hz a` as an intermediate fact. Simplify using `only [Function.comp_apply, xb] at this`. Rewrite using `[Pi.sub_apply, map_sub, ← hbar, this, sub_self]`.

Use `choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)`. Take `⟨u', hu'⟩` from `h1 y`. Apply `h5` to reduce the goal to its premises. Use `⟨u + u', ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, hu']`.

Use function extensionality and compare the values at `a`. Use `hy a` as an intermediate fact. Simplify using `only [Pi.sub_apply] at this`. Simplify using `only [Pi.add_apply]`. Rewrite using `[mul_comm, this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hxb0 : xb ≠ 0`. Introduce `h`. Conclude with `hxb (h ▸ Wc.zero_mem)`. Establish `hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `v ⟨hvW, hvs⟩`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hvs`. Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`.

Conclude with `absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb`. Establish `key` using `Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})`. Rewrite `key` using `[hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV]`. Use `show Module.finrank _ V = Module.finrank _ Wc + 1`. Conclude with `key`.
-/
theorem rank_residue_succ_of_adjoin
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O) :
    Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) →
    (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) →
    (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) →
    (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  intro hϖ h1 h2 h3 h4 h5
  set bar := residue O with hbar
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O),
      (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v) := by
    intro A v; funext i; exact (RingHom.map_mulVec bar A v i).symm
  have hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z := by
    intro z
    refine ⟨fun i => (residue_surjective (z i)).choose, ?_⟩
    funext i; exact (residue_surjective (z i)).choose_spec
  set V := LinearMap.range (As.map bar).mulVecLin
  set Wc := LinearMap.range (Ac.map bar).mulVecLin
  set xb : Fin n → ResidueField O := bar ∘ x
  have hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb} := by
    apply le_antisymm
    · rintro v ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hlift z
      obtain ⟨u, c, hc⟩ := h2 w
      rw [Matrix.mulVecLin_apply, hmap, hc]
      have : bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb := by
        rw [hmap]; funext i; simp [xb]
      rw [this]
      exact Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · apply sup_le
      · rintro v ⟨z, rfl⟩
        obtain ⟨u, rfl⟩ := hlift z
        obtain ⟨w, hw⟩ := h4 u
        refine ⟨bar ∘ w, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨w, hw⟩ := h3
        exact ⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩
  have hxb : xb ∉ Wc := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hlift z
    rw [Matrix.mulVecLin_apply, hmap] at hz
    have hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ} := by
      intro a
      rw [← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
      have := congrFun hz a
      simp only [Function.comp_apply, xb] at this
      rw [Pi.sub_apply, map_sub, ← hbar, this, sub_self]
    choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)
    obtain ⟨u', hu'⟩ := h1 y
    apply h5
    refine ⟨u + u', ?_⟩
    rw [Matrix.mulVec_add, hu']
    funext a
    have := hy a
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    rw [mul_comm, this]; ring
  have hxb0 : xb ≠ 0 := by
    intro h; exact hxb (h ▸ Wc.zero_mem)
  have hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb
  have key := Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV] at key
  show Module.finrank _ V = Module.finrank _ Wc + 1
  exact key

end GlobalTheory
