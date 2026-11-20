import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

/- English proof (translation)
Introduce `G _ LL _ O _ _ _ hinj`. Establish `hli : LinearIndependent O (fun _ : Unit => (1 : LL))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Consider the cases of `i`.

Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg`. Conclude with `(map_eq_zero_iff _ hinj).mp (by simpa using hg)`. Use `⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `g x hx`. Simplify using `using hx`.

Conclude with `Submodule.fg_span (Set.finite_range _)`. Conclude with `Module.Free.of_basis (Module.Basis.span hli)`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)` using `Submodule.subset_span ⟨(), rfl⟩`.

Establish `h2` using `Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x (Submodule.subset_span h1)`. Simplify using `using h2`.
-/
theorem existsStableLattice_holds : ExLattice := by
  intro G _ LL _ O _ _ _ hinj
  have hli : LinearIndependent O (fun _ : Unit => (1 : LL)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg
    exact (map_eq_zero_iff _ hinj).mp (by simpa using hg)
  refine ⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩
  · intro g x hx
    simpa using hx
  · exact Submodule.fg_span (Set.finite_range _)
  · exact Module.Free.of_basis (Module.Basis.span hli)
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL) :=
      Submodule.subset_span ⟨(), rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x
      (Submodule.subset_span h1)
    simpa using h2

end Formalism.WeaklyAdmissibleFiltrations
