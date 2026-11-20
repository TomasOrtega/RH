import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver

open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

/- English proof (translation)
The claim follows from `le_sInf fun _ hN => hN.1`.
-/
theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

/- English proof (translation)
Introduce `_ hx` and use `Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx`.
-/
theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

/- English proof (translation)
Introduce `g hg x hx`. Rewrite `hx`, the goal using `[stabClosure, Submodule.mem_sInf]`. Introduce `N hN`. Conclude with `hN.2.1 g hg x (hx N hN)`.
-/
theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

/- English proof (translation)
The claim follows from `sInf_le ⟨h1, h2, h3⟩`.
-/
theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

/- English proof (translation)
The claim follows from `closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T) (h.trans (subset_closure Op Rel T))`.
-/
theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

/- English proof (translation)
Take `⟨L, hL⟩` from `hL`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M)`. Introduce `F`.

Take `⟨N, h1, h2, h3, h4⟩` from `hne F`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))`. Use `choose pick hpick using hx`.

Establish `hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M)`. Use `strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Conclude with `closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))`. Introduce `h`. Apply `hpick (chainSet pick n)` to reduce the goal to its premises.

Establish `hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M)` using `subset_closure Op Rel _ (by simp [chainSet])`. Rewrite `hmem` using `[← h]`. Conclude with `hmem`. Use `hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M)) (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
