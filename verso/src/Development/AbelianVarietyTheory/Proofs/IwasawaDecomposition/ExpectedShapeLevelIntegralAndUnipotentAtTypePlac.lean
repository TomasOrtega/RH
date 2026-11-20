import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevShapeBound

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Establish `key : ∀ z : AL L, s.proj z = (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L))) (fun _ _ => Commute.all _ _)) (compAt L s.v z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`.

Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add]`. Rewrite using `[key, key, h]`.
-/
theorem proj_eq_of_compAt (s : SplitPlace L) {x y : AL L}
    (h : compAt L s.v x = compAt L s.v y) : s.proj x = s.proj y := by
  have key : ∀ z : AL L, s.proj z =
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L)))
        (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  rw [key, key, h]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hij` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.map_apply] at hij`. Conclude with `proj_eq_of_compAt s hij`.
-/
theorem loc_eq_of_comp (s : SplitPlace L) {x y : GAf L n}
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)) :
    s.loc n x = s.loc n y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  exact proj_eq_of_compAt s hij

end Gen

/- English proof (translation)
Introduce `D η J hG hS κ hκ`. Take `⟨hprod, hpara, huni, hhyp⟩` from `hS`. Establish `hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧ (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) = (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w)`. Introduce `w`. Take `⟨κ', hκ', htr, heq⟩` from `hprod κ hκ w`.

Use `⟨κ', hκ', ?_, heq⟩` and prove the remaining obligations. Distinguish the cases in `hg : w ∈ gPl D`. Take `⟨k, v, s, hsv, hsw⟩` from `hG.2.1 w hg`. Substitute `hsv` using the available equality. Establish `hu` using `(huni k v s hsw κ' htr).1 hκ'`.

Conclude with `(GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1`. Distinguish the cases in `hq : w ∈ qPl D η`. Take `⟨s, hsv, hs⟩` from `hpara w hq`. Substitute `hsv` using the available equality. Establish `hp` using `(hs κ' htr).1 hκ'`.

Conclude with `(GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1`. Use `(hhyp κ' ?_).1 hκ'` and prove the remaining obligations. Introduce `u hu`. Apply `htr u` to reduce the goal to its premises. Introduce and unpack `rfl`.

Simplify using `only [Set.mem_compl_iff, not_not, Set.mem_union] at hu`. Break down `hu with h | h` into its components or cases. Conclude with `hg h`. Conclude with `hq h`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Apply `GlobalTheory.FormInner.mem_ALint_of_comp` to reduce the goal to its premises. Introduce `w`. Take `⟨κ', -, hU, heq⟩` from `hloc w`. Use `⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩` and prove the remaining obligations.

Use `congrFun (congrFun heq i) j` as an intermediate fact. Simplify `this` using `only [Matrix.map_apply]`. Introduce `k v s hsw`. Take `⟨κ', hκ', htr, heq⟩` from `hprod κ hκ s.v`. Establish `hu` using `(huni k v s hsw κ' htr).1 hκ'`.

Rewrite `hu` using `[loc_eq_of_comp s heq]`. Then use the resulting hypothesis.
-/
theorem bound : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  intro D η J hG hS κ hκ
  obtain ⟨hprod, hpara, huni, hhyp⟩ := hS

  have hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧
      (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) =
        (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) := by
    intro w
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ w
    refine ⟨κ', hκ', ?_, heq⟩
    by_cases hg : w ∈ gPl D
    · obtain ⟨k, v, s, hsv, hsw⟩ := hG.2.1 w hg
      subst hsv
      have hu := (huni k v s hsw κ' htr).1 hκ'
      exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1
    · by_cases hq : w ∈ qPl D η
      · obtain ⟨s, hsv, hs⟩ := hpara w hq
        subst hsv
        have hp := (hs κ' htr).1 hκ'
        exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1
      · refine (hhyp κ' ?_).1 hκ'
        intro u hu
        apply htr u
        rintro rfl
        simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hu
        rcases hu with h | h
        · exact hg h
        · exact hq h
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.FormInner.mem_ALint_of_comp
    intro w
    obtain ⟨κ', -, hU, heq⟩ := hloc w
    refine ⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩
    have := congrFun (congrFun heq i) j
    simpa only [Matrix.map_apply] using this
  · intro k v s hsw
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ s.v
    have hu := (huni k v s hsw κ' htr).1 hκ'
    rwa [loc_eq_of_comp s heq] at hu

end GlobalTheory.LevShapeBound

end
