import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CollectComb

/- English proof (translation)
Establish `hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x, o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x)`. Introduce `b t hb x`. Proceed by induction on `t with`. Consider the case `nil => rfl`. Consider the case `cons a t ih`.

Establish `hab : a ≠ b` using `fun h => hb (h ▸ List.mem_cons_self)`. Establish `hbt : b ∉ t` using `fun h => hb (List.mem_cons_of_mem _ h)`. Simplify using `only [List.foldr_cons]`. Rewrite using `[← ih hbt, hc a b hab]`. Introduce `l hl F`.

Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a t ih`. Rewrite `hl` using `[List.nodup_cons]`. Simplify using `only [List.foldr_cons]`.

Rewrite using `[ih hl.2, hpast a t hl.1]`.
-/
theorem foldr_comp_eq {ι X : Type} (c o : ι → X → X) (hc : ∀ a b, a ≠ b → ∀ x, c a (o b x) = o b (c a x)) :
    ∀ (l : List ι), l.Nodup → ∀ F : X,
      l.foldr (fun i g => c i (o i g)) F = l.foldr (fun i g => c i g) (l.foldr (fun i g => o i g) F) := by
  have hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x,
      o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x) := by
    intro b t hb x
    induction t with
    | nil => rfl
    | cons a t ih =>
      have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
      have hbt : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      simp only [List.foldr_cons]
      rw [← ih hbt, hc a b hab]
  intro l hl F
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    rw [ih hl.2, hpast a t hl.1]

end GlobalTheory.CollectComb

/- English proof (translation)
Introduce `D ψ hψ S T M M' hM hM' n L hinj F`. Establish `hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o` using `fun i => ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu), fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩`. Use `GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _ (List.nodup_finRange n) F` and prove the remaining obligations. Introduce `a b hab x`. Establish `hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v` using `fun p ha hb => hab (hinj (ha.symm.trans hb))`.

Conclude with `(GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x`.
-/
theorem GlobalTheory.CollectComb.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  intro D ψ hψ S T M M' hM hM' n L hinj F
  have hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o := fun i =>
    ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu),
     fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩
  refine GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _
    (List.nodup_finRange n) F
  intro a b hab x
  have hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v := fun p ha hb => hab (hinj (ha.symm.trans hb))
  exact (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x
