import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LEmptyPf

/- English proof (translation)
Establish `ht : IsTerminal (F.obj.obj (Opposite.op X))` using `Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)`. Establish `hz : IsZero (F.obj.obj (Opposite.op X))` using `ht.isZero`. Conclude with `ModuleCat.subsingleton_of_isZero hz`.
-/
theorem sec_subsingleton {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) :
    Subsingleton (Sec F X) := by
  have ht : IsTerminal (F.obj.obj (Opposite.op X)) :=
    Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)
  have hz : IsZero (F.obj.obj (Opposite.op X)) := ht.isZero
  exact ModuleCat.subsingleton_of_isZero hz

/- English proof (translation)
Take `⟨Y, f, -, -, hx⟩` from `a5 R X F n hn x`. Establish `: IsEmpty Y` using `Function.isEmpty f.base`. Establish `: IsIso f` using `isIso_of_isEmpty f`. Establish `h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x)`. Rewrite using `[← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]`.

Rewrite using `[h1, hx, map_zero]`.
-/
theorem pos_zero (a5 : A5) {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) (n : ℤ)
    (hn : 0 < n) (x : H R (sch.obj X) F n) : x = 0 := by
  obtain ⟨Y, f, -, -, hx⟩ := a5 R X F n hn x
  have : IsEmpty Y := Function.isEmpty f.base
  have : IsIso f := isIso_of_isEmpty f
  have h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) := by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  rw [h1, hx, map_zero]

/- English proof (translation)
Introduce `a5 a9 R _ X hX F n`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy n 0 with h | rfl | h` into its components or cases. Conclude with `((a9 R F).1 _ n h).elim a b`. Take `⟨e, -⟩` from `(a9 R F).2`.

Use `sec_subsingleton X F` as an intermediate fact. Conclude with `(e X).symm.injective (Subsingleton.elim _ _)`. Rewrite using `[pos_zero a5 X F n h a, pos_zero a5 X F n h b]`.
-/
theorem LEmpty_of : LateralTheory.EtaleTrace.LPdCut.LEmpty := by
  intro a5 a9 R _ X hX F n
  refine ⟨fun a b => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact ((a9 R F).1 _ n h).elim a b
  · obtain ⟨e, -⟩ := (a9 R F).2
    have := sec_subsingleton X F
    exact (e X).symm.injective (Subsingleton.elim _ _)
  · rw [pos_zero a5 X F n h a, pos_zero a5 X F n h b]

end LateralTheory.EtaleTrace.LEmptyPf
