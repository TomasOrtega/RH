import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Lemmata.GeneralBFactLeftSide.Imports

open MvPolynomial Matrix Formalism.GradedWeylDivisibility

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_left'''''.goal1 .. | (apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left''' …`.
-/
theorem prodSpan {O A I : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype I] [DecidableEq I]
    {B : I → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module O (B i)] (ε : ∀ i, B i →ₗ[O] A) (T : ∀ i, Set (B i)) :
    Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
      Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  first | exact Bl.general_b_fact_left'''''.goal1 .. | (apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Establish `h : (MvPolynomial.map φ).comp (rowAct R (n` using `n) g).toRingHom = (rowAct S (n := n) (g.map φ)).toRingHom.comp (MvPolynomial.map φ) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[rowAct]`. Introduce `x`.

Simplify using `[rowAct]`. Conclude with `RingHom.congr_fun h F`.
-/
theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (F : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R g F) = rowAct S (g.map φ) (MvPolynomial.map φ F) := by
  have h : (MvPolynomial.map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h F

/- English proof (translation)
Establish `e : rowAct R (n` using `n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [rowAct, aeval_X, AlgHom.id_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Matrix.one_apply_ne (Ne.symm hb)]`. Simplify using the standard rewrite rules. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem rowAct_one {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) F = F := by
  have e : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e]; rfl

/- English proof (translation)
Establish `h1` using `rowActMul R r n g gi`. Rewrite `h1` using `[h]`. Establish `h2` using `congrArg (fun f => f F) h1`. Simplify using `only [AlgHom.comp_apply] at h2`. Rewrite using `[h2, rowAct_one]`.
-/
theorem rowAct_cancel {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by
  have h1 := rowActMul R r n g gi
  rw [h] at h1
  have h2 := congrArg (fun f => f F) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, rowAct_one]

/- English proof (translation)
Unfold `weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨w, by rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx`. Establish `e1 : MvPolynomial.map (Int.castRingHom O) (c • x) = (c : O) • MvPolynomial.map (Int.castRingHom O) x`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_weyl {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    MvPolynomial.map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨w, by rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : MvPolynomial.map (Int.castRingHom O) (c • x) = (c : O) • MvPolynomial.map (Int.castRingHom O) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]; rfl
    rw [e1]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _`. Rewrite using `[← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `map_mem_weyl hn ν f hf`.
-/
theorem weyl_eq_span_int (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by
  apply le_antisymm
  · show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by
      show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact map_mem_weyl hn ν f hf

end Formalism.L2.G.RelativeIndexFlags.Core
