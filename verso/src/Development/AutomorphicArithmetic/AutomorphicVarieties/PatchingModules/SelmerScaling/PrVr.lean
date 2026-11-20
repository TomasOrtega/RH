import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ S g i j`. Establish `hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N`. Rewrite using `[← S.U.span]`. Conclude with `Submodule.subset_span ⟨g, rfl⟩`. Establish `hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N` using `(S.pr1 (S.U.vr g i j)).2`.

Establish `hd` using `Submodule.disjoint_def.1 S.U.compl.disjoint`. Establish `h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA)` using `Submodule.mem_one.2 ⟨_, rfl⟩`. Use `⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)`. Apply `S.U.inj` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use `hd _ h1 ?_` and prove the remaining obligations. Use `S.U.N.sub_mem ((hm i j).2 e) hN` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
