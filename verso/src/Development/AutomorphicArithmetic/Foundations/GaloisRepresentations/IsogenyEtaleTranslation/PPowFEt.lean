import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

open AlgebraicGeometry CategoryTheory Limits

namespace UpperTheory.Gal.FixZ

section Coord

variable {C : Type*} [Category C] {A : C} {k : ℕ} [HasProduct (fun _ : Fin k => A)]

private noncomputable def coordMap (j : Fin k) (φ : A ⟶ A) :
    (∏ᶜ fun _ : Fin k => A) ⟶ ∏ᶜ fun _ : Fin k => A :=
  Pi.lift fun i => if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i

/- English proof (translation)
Simplify using `[coordMap]`.
-/
private lemma coordMap_π (j i : Fin k) (φ : A ⟶ A) :
    coordMap j φ ≫ Pi.π (fun _ : Fin k => A) i =
      if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i := by
  simp [coordMap]

/- English proof (translation)
Use `⟨⟨by simp [coordMap_π]⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => Pi.lift fun i => if i = j then s.snd else s.fst ≫ Pi.π (fun _ : Fin k => A) i) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Use `Pi.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, coordMap_π]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `using s.condition.symm`. Simplify using `[h]`. Introduce `s`. Simplify using the standard rewrite rules.

Introduce `s m h₁ h₂`. Use `Pi.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using h₂`.

Use `congrArg (· ≫ Pi.π (fun _ : Fin k => A) i) h₁` as an intermediate fact. Simplify `this` using `[coordMap_π, h]`.
-/
private lemma coordMap_isPullback (j : Fin k) (φ : A ⟶ A) :
    IsPullback (coordMap j φ) (Pi.π (fun _ : Fin k => A) j) (Pi.π (fun _ : Fin k => A) j) φ := by
  refine ⟨⟨by simp [coordMap_π]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Pi.lift fun i => if i = j then s.snd else s.fst ≫ Pi.π (fun _ : Fin k => A) i)
    ?_ ?_ ?_⟩⟩
  · intro s
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, coordMap_π]
    by_cases h : i = j
    · subst h
      simpa using s.condition.symm
    · simp [h]
  · intro s
    simp
  · intro s m h₁ h₂
    refine Pi.hom_ext _ _ fun i => ?_
    by_cases h : i = j
    · subst h
      simpa using h₂
    · have := congrArg (· ≫ Pi.π (fun _ : Fin k => A) i) h₁
      simpa [coordMap_π, h] using this

end Coord

/- English proof (translation)
Establish `step : ∀ j : ℕ, j ≤ k → ∃ h : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k, P h.left ∧ ∀ i : Fin k, h ≫ GlobalTheory.KS.pr A i = if i.val < j then GlobalTheory.KS.pr A i ≫ f i else GlobalTheory.KS.pr A i`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`.

Conclude with `⟨𝟙 _, by simpa using P.id_mem _, fun i => by simp⟩`. Consider the case `succ j ih`. Introduce `hj`. Take `⟨h, hP, hh⟩` from `ih (by omega)`. Set `j' : Fin k` to `⟨j, by omega⟩`.

Establish `hb : IsPullback (coordMap j' (f j')).left (GlobalTheory.KS.pr A j').left (GlobalTheory.KS.pr A j').left (f j').left` using `(coordMap_isPullback j' (f j')).map (Over.forget S)`. Establish `he : P (coordMap j' (f j')).left` using `P.of_isPullback hb.flip (hf j')`. Use `⟨h ≫ coordMap j' (f j'), ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left]`. Conclude with `P.comp_mem _ _ hP he`.

Rewrite using `[Category.assoc, GlobalTheory.KS.pr, coordMap_π]`. Distinguish the cases in `hi : i = j'`. Substitute `hi` using the available equality. Establish `h0 : h ≫ Pi.π (fun _ : Fin k => A) j' = Pi.π (fun _ : Fin k => A) j'`. Use `hh j'` as an intermediate fact.

Simplify `this` using `[GlobalTheory.KS.pr, j']`. Rewrite using `[if_pos rfl, if_pos (by simp [j']), ← Category.assoc, h0]`. Establish `hne : i.val ≠ j` using `fun e => hi (Fin.ext e)`. Use `hh i` as an intermediate fact. Simplify using `only [GlobalTheory.KS.pr] at this`.

Simplify using `only [hi, if_false, this]`. Distinguish the cases in `hlt : i.val < j`. Simplify using `[hlt, Nat.lt_succ_of_lt hlt]`. Establish `: ¬ i.val < j + 1` using `by omega`. Simplify using `[hlt, this]`.

Take `⟨h, hP, hh⟩` from `step k le_rfl`. Establish `: g = h` using `Pi.hom_ext _ _ fun i => by`. Use `hh i` as an intermediate fact. Simplify using `only [i.isLt, if_true] at this`. Conclude with `(hg i).trans this.symm`.

Rewrite using `[this]`. Conclude with `hP`.
-/
private lemma pow_prop (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{0}} (A : Over S) (k : ℕ) (f : Fin k → (A ⟶ A))
    (hf : ∀ i, P (f i).left) (g : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k)
    (hg : ∀ i, g ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ f i) : P g.left := by
  have step : ∀ j : ℕ, j ≤ k → ∃ h : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k, P h.left ∧
      ∀ i : Fin k, h ≫ GlobalTheory.KS.pr A i =
        if i.val < j then GlobalTheory.KS.pr A i ≫ f i else GlobalTheory.KS.pr A i := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨𝟙 _, by simpa using P.id_mem _, fun i => by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨h, hP, hh⟩ := ih (by omega)
      let j' : Fin k := ⟨j, by omega⟩
      have hb : IsPullback (coordMap j' (f j')).left (GlobalTheory.KS.pr A j').left
          (GlobalTheory.KS.pr A j').left (f j').left :=
        (coordMap_isPullback j' (f j')).map (Over.forget S)
      have he : P (coordMap j' (f j')).left := P.of_isPullback hb.flip (hf j')
      refine ⟨h ≫ coordMap j' (f j'), ?_, fun i => ?_⟩
      · rw [Over.comp_left]
        exact P.comp_mem _ _ hP he
      · rw [Category.assoc, GlobalTheory.KS.pr, coordMap_π]
        by_cases hi : i = j'
        · subst hi
          have h0 : h ≫ Pi.π (fun _ : Fin k => A) j' = Pi.π (fun _ : Fin k => A) j' := by
            have := hh j'
            simpa [GlobalTheory.KS.pr, j'] using this
          rw [if_pos rfl, if_pos (by simp [j']), ← Category.assoc, h0]
        · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
          have := hh i
          simp only [GlobalTheory.KS.pr] at this
          simp only [hi, if_false, this]
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨h, hP, hh⟩ := step k le_rfl
  have : g = h := Pi.hom_ext _ _ fun i => by
    have := hh i
    simp only [i.isLt, if_true] at this
    exact (hg i).trans this.symm
  rw [this]
  exact hP

/- English proof (translation)
Introduce `S A k f hf g hg`. Conclude with `⟨pow_prop @IsFinite A k f (fun i => (hf i).1) g hg, pow_prop @Etale A k f (fun i => (hf i).2.1) g hg, pow_prop @Surjective A k f (fun i => (hf i).2.2) g hg⟩`.
-/
theorem powFEt_of : PowFEt := by
  intro S A k f hf g hg
  exact ⟨pow_prop @IsFinite A k f (fun i => (hf i).1) g hg,
    pow_prop @Etale A k f (fun i => (hf i).2.1) g hg,
    pow_prop @Surjective A k f (fun i => (hf i).2.2) g hg⟩

end UpperTheory.Gal.FixZ
