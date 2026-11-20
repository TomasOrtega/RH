import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.SmGL.CuspSpan

/- English proof (translation)
Break down `s with p | q` into its components or cases. Rewrite using `[← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]`. Both sides reduce to the same expression. Rewrite using `[← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]`. Both sides reduce to the same expression.
-/
theorem blk_two_apply {α β n : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α ⊕ β ≃ n) (s : α ⊕ β) : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two c) (c s) = s.isRight := by
  rcases s with p | q
  · rw [← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]; rfl
  · rw [← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]; rfl

/- English proof (translation)
Establish `h : a + b = N`. Use `Fintype.card_congr e` as an intermediate fact. Simplify using `using this.symm`. Establish `H` using `((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb`. Establish `H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm)))`.

Use `GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H` and prove the remaining obligations. Establish `h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight` using `fun i => blk_two_apply (stdSum h) (e i)`. Establish `h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight` using `fun i => by`. Use `blk_two_apply e.symm (e i)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Then use the resulting hypothesis.

Rewrite `hij` using `[h1, h1]`. Rewrite using `[h2, h2]`. Conclude with `hij`. Establish `htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤` using `Submodule.Quotient.subsingleton_iff.1 H'`. Establish `hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1` using `htop ▸ Submodule.mem_top`.

Use `(Submodule.span_le.2 ?_) hw` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Use `Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)), v, ?_⟩` and prove the remaining obligations. Establish `hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)))`. Establish `hent` using `GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2`.

Establish `h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight` using `fun i => by`. Use `blk_two_apply e.symm (e i)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Use extensionality with `i j`. Rewrite using `[hu, Matrix.reindex_apply, Matrix.submatrix_apply]`.

Simplify using `only [Equiv.symm_symm]`. Take `⟨s, rfl⟩` from `e.symm.surjective i`. Take `⟨t, rfl⟩` from `e.symm.surjective j`. Simplify using `only [Equiv.apply_symm_apply]`. Apply the tactic sequence `rcases s with p | p <;> rcases t with q | q`.

Rewrite using `[hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[Matrix.fromBlocks_apply₁₂, Matrix.of_apply]`. Rewrite using `[hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]`. Simplify using `[Matrix.one_apply]`.

Rewrite using `[hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[← hn]`. Simplify using the standard rewrite rules.
-/
theorem mem_span_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.SmGL.IsCuspidal π) (a b : ℕ)
    (e : Fin N ≃ Fin a ⊕ Fin b) (ha : 0 < a) (hb : 0 < b)
    (u : (Fin a → Fin b → k) → GL (Fin N) k)
    (hu : ∀ X, (u X : Matrix (Fin N) (Fin N) k) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) (w : V) :
    w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  have h : a + b = N := by
    have := Fintype.card_congr e
    simpa using this.symm
  have H := ((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb
  have H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm))) := by
    refine GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H
    have h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight :=
      fun i => blk_two_apply (stdSum h) (e i)
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, h1] at hij
    rw [h2, h2]
    exact hij
  have htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 H'
  have hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 := htop ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)),
    v, ?_⟩
  have hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))) := by
    have hent := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    ext i j
    rw [hu, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    obtain ⟨s, rfl⟩ := e.symm.surjective i
    obtain ⟨t, rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    rcases s with p | p <;> rcases t with q | q
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]
      simp [Matrix.one_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]
  rw [← hn]
  simp

end GlobalTheory.SmGL.CuspSpan
