import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniSeqBasic

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => intro γ hγ`. Conclude with `⟨γ, List.Perm.refl _, hγ⟩`. Consider the case `cons x _ ih`. Introduce `γ hγ`.

Break down `γ with _ | ⟨a, γ⟩` into its components or cases. Simplify using `at hγ`. Simplify using `only [List.map_cons, List.cons.injEq] at hγ`. Take `⟨γ', h1, h2⟩` from `ih γ hγ.2`. Conclude with `⟨a :: γ', h1.cons a, by simp [h2, hγ.1]⟩`.

Consider the case `swap x y l`. Introduce `γ hγ`. Break down `γ with _ | ⟨a, _ | ⟨b, γ⟩⟩` into its components or cases. Simplify using `at hγ`. Simplify using `at hγ`.

Simplify using `only [List.map_cons, List.cons.injEq] at hγ`. Conclude with `⟨b :: a :: γ, List.Perm.swap _ _ _, by simp [hγ.1, hγ.2.1, hγ.2.2]⟩`. Consider the case `trans _ _ ih1 ih2`. Introduce `γ hγ`. Take `⟨γ1, p1, e1⟩` from `ih1 γ hγ`.

Take `⟨γ2, p2, e2⟩` from `ih2 γ1 e1`. Conclude with `⟨γ2, p1.trans p2, e2⟩`.
-/
theorem perm_lift {α β : Type} (f : α → β) {l l' : List β} (h : l.Perm l') :
    ∀ γ : List α, γ.map f = l → ∃ γ' : List α, γ.Perm γ' ∧ γ'.map f = l' := by
  induction h with
  | nil => intro γ hγ; exact ⟨γ, List.Perm.refl _, hγ⟩
  | cons x _ ih =>
    intro γ hγ
    rcases γ with _ | ⟨a, γ⟩
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      obtain ⟨γ', h1, h2⟩ := ih γ hγ.2
      exact ⟨a :: γ', h1.cons a, by simp [h2, hγ.1]⟩
  | swap x y l =>
    intro γ hγ
    rcases γ with _ | ⟨a, _ | ⟨b, γ⟩⟩
    · simp at hγ
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      exact ⟨b :: a :: γ, List.Perm.swap _ _ _, by simp [hγ.1, hγ.2.1, hγ.2.2]⟩
  | trans _ _ ih1 ih2 =>
    intro γ hγ
    obtain ⟨γ1, p1, e1⟩ := ih1 γ hγ
    obtain ⟨γ2, p2, e2⟩ := ih2 γ1 e1
    exact ⟨γ2, p1.trans p2, e2⟩

def Orth (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a b : M × (M →ₗ[R] R)) : Prop := a.2 b.1 = 0 ∧ b.2 a.1 = 0

/- English proof (translation)
Introduce `_ _ h` and use `⟨h.2, h.1⟩`.
-/
theorem orth_symm (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    Symmetric (Orth R M) := fun _ _ h => ⟨h.2, h.1⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf⟩`. Use `⟨(List.finRange l.length).map (fun i => (l.get i, f i)), ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply List.ext_getElem <;> simp`. Introduce `p hp`.

Take `⟨i, -, rfl⟩` from `List.mem_map.mp hp`. Simplify using `using hf i i`. Rewrite using `[List.pairwise_map]`. Use `(List.pairwise_lt_finRange l.length).imp fun {i j} hij => ?_` and prove the remaining obligations. Establish `hne : i ≠ j` using `ne_of_lt hij`.

Conclude with `⟨by simpa [hne] using hf i j, by simpa [hne.symm] using hf j i⟩`. Introduce and unpack `⟨γ, rfl, hone, hpw⟩`. Use `⟨fun i => (γ[i.1]'(by simpa using i.2)).2, fun i j => ?_⟩` and prove the remaining obligations. Establish `hi : i.1 < γ.length` using `by simpa using i.2`. Establish `hj : j.1 < γ.length` using `by simpa using j.2`.

Rewrite `hpw` using `[List.pairwise_iff_getElem]`. Simplify using `only [List.get_eq_getElem, List.getElem_map]`. Use `split_ifs with hij`. Substitute `hij` using the available equality. Conclude with `hone _ (List.getElem_mem _)`.

Break down `lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h` into its components or cases. Conclude with `(hpw _ _ hi hj h).1`. Conclude with `(hpw _ _ hj hi h).2`.
-/
theorem mem_uniM_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ γ : List (M × (M →ₗ[R] R)), γ.map Prod.fst = l ∧
      (∀ p ∈ γ, p.2 p.1 = 1) ∧ γ.Pairwise (Orth R M) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(List.finRange l.length).map (fun i => (l.get i, f i)), ?_, ?_, ?_⟩
    · apply List.ext_getElem <;> simp
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simpa using hf i i
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange l.length).imp fun {i j} hij => ?_
      have hne : i ≠ j := ne_of_lt hij
      exact ⟨by simpa [hne] using hf i j, by simpa [hne.symm] using hf j i⟩
  · rintro ⟨γ, rfl, hone, hpw⟩
    refine ⟨fun i => (γ[i.1]'(by simpa using i.2)).2, fun i j => ?_⟩
    have hi : i.1 < γ.length := by simpa using i.2
    have hj : j.1 < γ.length := by simpa using j.2
    rw [List.pairwise_iff_getElem] at hpw
    simp only [List.get_eq_getElem, List.getElem_map]
    split_ifs with hij
    · subst hij
      exact hone _ (List.getElem_mem _)
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact (hpw _ _ hi hj h).1
      · exact (hpw _ _ hj hi h).2

/- English proof (translation)
Introduce `R M _ _ _`. Establish `key : ∀ (ψ : M ≃ₗ[R] M) (l : List M), l ∈ uniM R M → l.map ψ ∈ uniM R M`. Introduce `ψ l hl`. Take `⟨γ, rfl, hone, hpw⟩` from `(mem_uniM_iff R M l).mp hl`. Use `(mem_uniM_iff R M _).mpr ⟨γ.map (fun p => (ψ p.1, p.2 ∘ₗ (ψ.symm : M →ₗ[R] M))), ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[List.map_map, Function.comp_def]`. Introduce `p hp`. Take `⟨q, hq, rfl⟩` from `List.mem_map.mp hp`. Simplify using `using hone q hq`. Rewrite using `[List.pairwise_map]`.

Use `hpw.imp fun {a b} h => ?_` and prove the remaining obligations. Simplify `h` using `[Orth]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl l' hsub`. Take `⟨γ, rfl, hone, hpw⟩` from `(mem_uniM_iff R M l).mp hl`.

Take `⟨γ', hγ', rfl⟩` from `List.sublist_map_iff.mp hsub`. Conclude with `(mem_uniM_iff R M _).mpr ⟨γ', rfl, fun p hp => hone p (hγ'.subset hp), hpw.sublist hγ'⟩`. Introduce `l l' hperm hl`. Take `⟨γ, hγ, hone, hpw⟩` from `(mem_uniM_iff R M l).mp hl`. Take `⟨γ', hp, hm⟩` from `perm_lift Prod.fst hperm γ hγ`.

Conclude with `(mem_uniM_iff R M _).mpr ⟨γ', hm, fun p hq => hone p (hp.symm.subset hq), hpw.perm hp (fun {_ _} h => orth_symm R M h)⟩`. Introduce `ψ l`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `key ψ.symm _ h` as an intermediate fact.

Simplify `this` using `[List.map_map, Function.comp_def]`. Conclude with `key ψ l`.
-/
theorem main : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  intro R M _ _ _
  have key : ∀ (ψ : M ≃ₗ[R] M) (l : List M), l ∈ uniM R M → l.map ψ ∈ uniM R M := by
    intro ψ l hl
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    refine (mem_uniM_iff R M _).mpr
      ⟨γ.map (fun p => (ψ p.1, p.2 ∘ₗ (ψ.symm : M →ₗ[R] M))), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa using hone q hq
    · rw [List.pairwise_map]
      refine hpw.imp fun {a b} h => ?_
      simpa [Orth] using h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hsub
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hγ', rfl⟩ := List.sublist_map_iff.mp hsub
    exact (mem_uniM_iff R M _).mpr ⟨γ', rfl, fun p hp => hone p (hγ'.subset hp), hpw.sublist hγ'⟩
  · intro l l' hperm hl
    obtain ⟨γ, hγ, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hp, hm⟩ := perm_lift Prod.fst hperm γ hγ
    exact (mem_uniM_iff R M _).mpr
      ⟨γ', hm, fun p hq => hone p (hp.symm.subset hq), hpw.perm hp (fun {_ _} h => orth_symm R M h)⟩
  · intro ψ l
    constructor
    · intro h
      have := key ψ.symm _ h
      simpa [List.map_map, Function.comp_def] using this
    · exact key ψ l

end GlobalTheory.UniSeqBasic

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.UniSeqBasic.main`. Consider the case `exact @GlobalTheory.UniSeqBasic.mem_uniM_iff`. Consider the case `exact @GlobalTheory.UniSeqBasic.orth_symm`. Consider the case `exact @GlobalTheory.UniSeqBasic.perm_lift`.
-/
theorem _root_.GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniSeqBasic.main
  | exact @GlobalTheory.UniSeqBasic.mem_uniM_iff
  | exact @GlobalTheory.UniSeqBasic.orth_symm
  | exact @GlobalTheory.UniSeqBasic.perm_lift
end
