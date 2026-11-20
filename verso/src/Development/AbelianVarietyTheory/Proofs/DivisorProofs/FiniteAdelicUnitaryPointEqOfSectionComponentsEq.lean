import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Unfold `toSub at e`. Rewrite `e` using `[dif_pos hg, dif_pos hh]`. Conclude with `congrArg Subtype.val e`.
-/
theorem eq_of_toSub_eq {G : Type} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H)
    (e : toSub H g = toSub H h) : g = h := by
  unfold toSub at e
  rw [dif_pos hg, dif_pos hh] at e
  exact congrArg Subtype.val e

/- English proof (translation)
The claim follows from `(GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2 (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))`.
-/
theorem under_conjSrc (w : Pl E) :
    (conjSrc (GlobalTheory.SplitPts.conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
    (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `hw ⟨_, h, under_conjSrc w⟩`.
-/
theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  by_contra h
  exact hw ⟨_, h, under_conjSrc w⟩

/- English proof (translation)
Introduce and unpack `v rfl f hf h`. Establish `hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧ ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)` using `⟨f, hf, h⟩`. Establish `hcj : cj v = hex.choose` using `by unfold cj; rw [dif_pos hex]`. Rewrite using `[hcj]`. Conclude with `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1 (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _`.
-/
theorem ext_cj (w : Pl E) (a : Af E) : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
    Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      f (pLoc E v a) = cj w (pLoc E w a) := by
  rintro v rfl f hf h
  have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
  have hcj : cj v = hex.choose := by unfold cj; rw [dif_pos hex]
  rw [hcj]
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
    (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _

/- English proof (translation)
Establish `hUL : UL n w = UJ (cj w) 1` using `by unfold UL; rw [if_neg hw]`. Rewrite using `[hUL]`. Use `show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1`. Establish `hc` using `GlobalTheory.SplitPts.comp_eq x w`. Establish `e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) = (cLoc w x).val.map (cj w)`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1`. Rewrite `hc` using `[e]`. Rewrite using `[Matrix.mul_one]`. Conclude with `hc`.
-/
theorem cLoc_mem_UL {w : Pl E} (hw : ¬ IsSplitAt w) (x : UA E n) : cLoc w x ∈ UL n w := by
  have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
  rw [hUL]
  show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1
  have hc := GlobalTheory.SplitPts.comp_eq x w
  have e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) =
      (cLoc w x).val.map (cj w) := by
    refine Matrix.ext fun i j => ?_
    exact ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1
      (conjLoc_spec _ w).2.1
  rw [e] at hc
  rw [Matrix.mul_one]
  exact hc

/- English proof (translation)
Establish `hx` using `GlobalTheory.SplitPts.comp_eq x w`. Establish `hy` using `GlobalTheory.SplitPts.comp_eq y w`. Rewrite `hx` using `[h]`. Establish `e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ`. Establish `h1` using `mul_eq_one_comm.1 hx`.

Establish `h2` using `mul_eq_one_comm.1 hy`. Combine the equalities or inequalities in the displayed calculation. Use `Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)` and prove the remaining obligations. Use `congrFun (congrFun e j) i` as an intermediate fact. Simplify using `using this`.
-/
theorem cLoc_conj_eq (w : Pl E) (x y : UA E n) (h : cLoc w x = cLoc w y) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y := by
  have hx := GlobalTheory.SplitPts.comp_eq x w
  have hy := GlobalTheory.SplitPts.comp_eq y w
  rw [h] at hx
  have e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ := by
    have h1 := mul_eq_one_comm.1 hx
    have h2 := mul_eq_one_comm.1 hy
    calc _ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
            ((cLoc w y).val * ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map
              (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ) := by rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)
  have := congrFun (congrFun e j) i
  simpa using this

end GlobalTheory.LocInj

open GlobalTheory.LocInj in
/- English proof (translation)
Introduce `E _ _ _ _ n S hS x y hxy`. Establish `hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n)`. Introduce `w hw`. Distinguish the cases in `hsp : IsSplitAt w`. Establish `hUL : ∀ g, g ∈ UL n w` using `fun g => by unfold UL; rw [if_pos hsp]; trivial`.

Conclude with `eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)`. Conclude with `eq_of_toSub_eq (cLoc_mem_UL hsp _) (cLoc_mem_UL hsp _) (hxy w hw)`. Establish `hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n)`. Introduce `u`. Take `⟨s, ⟨hsS, hsu⟩, -⟩` from `hS u`.

Distinguish the cases in `hus : u = s`. Substitute `hus` using the available equality. Conclude with `hS' u hsS`. Establish `hsp : IsSplitAt s` using `⟨u, hus, hsu.symm⟩`. Take `⟨-, -, hover⟩` from `GlobalTheory.SplitPts.over_split hsp`.

Break down `hover u hsu.symm with h | h` into its components or cases. Conclude with `absurd h hus`. Substitute `h` using the available equality. Conclude with `cLoc_conj_eq s _ _ (hS' s hsS)`. Establish `hxi : cInf (x : UA E n) = 1` using `MonoidHom.mem_ker.1 x.2`.

Establish `hyi : cInf (y : UA E n) = 1` using `MonoidHom.mem_ker.1 y.2`. Use `Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))` and prove the remaining obligations. Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)`.
-/
theorem GlobalTheory.BCT.finU_eq_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ S : Set (Pl E), IsSection S → ∀ x y : finU E n,
      (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  intro E _ _ _ _ n S hS x y hxy

  have hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n) := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have hUL : ∀ g, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hsp]; trivial
      exact eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)
    · exact eq_of_toSub_eq (cLoc_mem_UL hsp _) (cLoc_mem_UL hsp _) (hxy w hw)

  have hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n) := by
    intro u
    obtain ⟨s, ⟨hsS, hsu⟩, -⟩ := hS u
    by_cases hus : u = s
    · subst hus; exact hS' u hsS
    · have hsp : IsSplitAt s := ⟨u, hus, hsu.symm⟩
      obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
      rcases hover u hsu.symm with h | h
      · exact absurd h hus
      · subst h; exact cLoc_conj_eq s _ _ (hS' s hsS)
  have hxi : cInf (x : UA E n) = 1 := MonoidHom.mem_ker.1 x.2
  have hyi : cInf (y : UA E n) = 1 := MonoidHom.mem_ker.1 y.2
  refine Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
  exact congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
