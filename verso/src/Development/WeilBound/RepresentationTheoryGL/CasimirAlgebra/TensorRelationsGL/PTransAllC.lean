import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllB

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)

def labR : {p // ¬ lab p = τ₀} → {τ // τ ≠ τ₀} := fun p => ⟨lab p.1, p.2⟩

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Rewrite using `[cj_apply]`. Apply `(spl (n := n) (M := M) fun p => lab p = τ₀).injective` to reduce the goal to its premises. Establish `h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ`. Use extensionality with `x`.

Simplify using `[fib, Finset.mem_subtype, x.2]`. Establish `h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅`. Use extensionality with `x`. Simplify using `[fib, Finset.mem_subtype, x.2]`. Rewrite using `[LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]`.
-/
theorem conj_tensor_entry_base (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (tE Finset.univ (fun a b => lift (F a b)) c d) =
      tE (fib lab τ₀) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Rewrite using `[cj_apply]`. Apply `(spl (n := n) (M := M) fun p => lab p = τ₀).injective` to reduce the goal to its premises. Establish `h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅`. Use extensionality with `x`.

Simplify using `only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`. Rewrite using `[x.2]`. Conclude with `fun h => τ.2 h.symm`. Establish `h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ`. Use extensionality with `x`.

Simplify using `[fib, labR, Finset.mem_subtype, Subtype.ext_iff]`. Rewrite using `[LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]`.
-/
theorem conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

omit [DecidableEq P] in
/- English proof (translation)
Use `Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢`. Conclude with `hp`. Introduce `p _ q _ h`.

Conclude with `Subtype.ext h`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Use `⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]`.

Conclude with `hp`.
-/
theorem card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp

omit [Fintype P] in
/- English proof (translation)
Establish `hfib : ∀ τ, fib lab τ = ∅` using `fun τ => Finset.eq_empty_of_isEmpty _`. Establish `hG : colG col = {1}`. Use extensionality with `σ`. Simplify using `[colG, Subsingleton.elim σ 1]`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hℓ (LinearMap.ext h)`. Use `⟨1, Subalgebra.one_mem _, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hm` to reduce the goal to its premises. Use `LinearMap.congr_fun h (fun _ => m)` as an intermediate fact. Simplify `this` using `[cA, alt, hG, pm]`. Introduce `τ u`. Establish `hc` using `qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u`.

Simplify using `only [hfib, tE_empty]`. Rewrite using `[hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl

end PositivityTheory.Rg.Cz.TA

end
