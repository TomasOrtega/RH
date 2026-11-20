import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ProjFinProd

/- English proof (translation)
Introduce `O _ ι _ X s`. Proceed by induction on `ι using Finite.induction_empty_option with`. Consider the case `of_equiv e ih`. Introduce `Y f hs hf`. Name the introduced variables `α β`.

Take `⟨P, p0, p, hP, hp, hu⟩` from `ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)`. Establish `key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h)`. Introduce `j`. Take `⟨i, rfl⟩` from `e.surjective j`. Use `⟨p i, hp i, fun i' h => ?_⟩` and prove the remaining obligations.

Take `rfl` from `e.injective h`. Simplify using the standard rewrite rules. Use `choose q hq1 hq2 using key`. Establish `hq : ∀ i, q (e i) = p i` using `fun i => by simpa using hq2 (e i) i rfl`. Use `⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩` and prove the remaining obligations.

Take `⟨h, ⟨h1, h2⟩, h3⟩` from `hu Z a (fun i => b (e i)) (fun i => hb _)`. Use `⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `e.surjective j`. Rewrite using `[hq]`. Conclude with `h2 i`.

Rewrite using `[← hq]`. Conclude with `hh.2 _`. Consider the case `h_empty`. Introduce `Y f hs hf`. Use `⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩` and prove the remaining obligations.

Conclude with `⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩`. Consider the case `h_option ih`. Introduce `Y f hs hf`. Take `⟨P, p0, p, hP, hp, hu⟩` from `ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)`. Use `⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0, fun i => match i with` and prove the remaining obligations.

Consider the case `none => pullback.snd _ _`. Consider the case `some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩`. Rewrite using `[Category.assoc]`. Conclude with `isProjOver_pullback hP (hf none)`. Introduce and unpack `(_ | i)`.

Simplify using `only [Category.assoc]`. Conclude with `pullback.condition.symm`. Simplify using `only [Category.assoc]`. Rewrite using `[hp i]`. Take `⟨h, ⟨h1, h2⟩, h3⟩` from `hu Z a (fun i => b (some i)) (fun i => hb _)`.

Use `⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩` and prove the remaining obligations. Rewrite using `[pullback.lift_fst_assoc, h1]`. Introduce and unpack `(_ | i)`. Conclude with `pullback.lift_snd _ _ _`. Conclude with `(pullback.lift_fst_assoc _ _ _ _).trans (h2 i)`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Use `h3 _ ⟨by simpa using hh.1, fun i => ?_⟩` and prove the remaining obligations. Simplify using `using hh.2 (some i)`. Rewrite using `[pullback.lift_snd]`.

Conclude with `hh.2 none`.
-/
theorem exists_isProjOver_finite_prod : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  intro O _ ι _ X s
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro Y f hs hf
    rename_i α β
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)
    have key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h) := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      refine ⟨p i, hp i, fun i' h => ?_⟩
      obtain rfl := e.injective h
      simp
    choose q hq1 hq2 using key
    have hq : ∀ i, q (e i) = p i := fun i => by simpa using hq2 (e i) i rfl
    refine ⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩
    obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (e i)) (fun i => hb _)
    refine ⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩
    · obtain ⟨i, rfl⟩ := e.surjective j
      rw [hq]; exact h2 i
    · rw [← hq]; exact hh.2 _
  | h_empty =>
    intro Y f hs hf
    refine ⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩
    exact ⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩
  | h_option ih =>
    intro Y f hs hf
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)
    refine ⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0,
      fun i => match i with
        | none => pullback.snd _ _
        | some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩
    · rw [Category.assoc]
      exact isProjOver_pullback hP (hf none)
    · rintro (_ | i)
      · simp only [Category.assoc]; exact pullback.condition.symm
      · simp only [Category.assoc]; rw [hp i]
    · obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (some i)) (fun i => hb _)
      refine ⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩
      · rw [pullback.lift_fst_assoc, h1]
      · rintro (_ | i)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h2 i)
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine h3 _ ⟨by simpa using hh.1, fun i => ?_⟩
          simpa using hh.2 (some i)
        · rw [pullback.lift_snd]; exact hh.2 none

end GlobalTheory.ProjFinProd
