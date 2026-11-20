import Development.EtaleCohomology.EtaleSheaves.InjStepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

/- English proof (translation)
Establish `hT` using `Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)`. Conclude with `(ModuleCat.isZero_iff_subsingleton).1 hT.isZero`.
-/
theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

/- English proof (translation)
Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Use `(hH.a9 R F).1 (sch.obj Y) n hn` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Take `⟨e, -, -⟩` from `(hH.a9 R F).2`. Use `sec_subsingleton F Y` as an intermediate fact.

Rewrite using `[← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]`. Take `⟨Z, f, -, -, hf⟩` from `hH.a5 R Y F n hn x`. Establish `: IsIso (sch.map f)` using `inferInstance`. Establish `h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0` using `by rw [pull_comp, hf, map_zero]`. Simplify `h1` using `[pull_id]`.
-/
theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

/- English proof (translation)
Introduce `hH q X S p U hU i n x`. Establish `: IsEmpty U` using `⟨fun u => by`. Establish `h : (u.1 : S) ∈ (U : Set S)` using `u.2`. Rewrite `h` using `[hU]`. Conclude with `h⟩`.

Establish `: IsEmpty (overO p U)` using `⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩`. Conclude with `h_empty hH _ _ n x`.
-/
theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
