import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumFamilyOfReductions

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `h2 hred E Ω _ _ _ _ _ l _ ι c hc`. Take `⟨c, rfl⟩ : ∃ c', c = c' + 1` from `⟨c - 1, by omega⟩`. Use `clear hc`. Proceed by induction on `c with`. Consider the case `zero`.

Introduce `N hN n hn r p HT H`. Establish `hn' : N 0 = n` using `by simpa using hn`. Substitute `hn'` using the available equality. Establish `e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = p 0 w A h rc`. Introduce `w A h rc`.

Simplify using `[sumList, WD.lpSum_zero]`. Establish `e' : (fun τ => ∑ i, HT i τ) = HT 0`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Use `⟨r 0, ⟨(H 0).cont, (H 0).ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[e']`. Conclude with `(H 0).ht w fun A h rc hrc => by`. Use `hg A h rc hrc` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[e]`.

Conclude with `(H 0).par w A h rc hrc`. Take `rfl : i = 0` from `Subsingleton.elim (α := Fin 1) _ _`. Conclude with `hi`. Consider the case `succ c ih`. Introduce `N hN n hn r p HT H`.

Rewrite `hn` using `[Fin.sum_univ_succ]`. Substitute `hn` using the available equality. Take `⟨R, hR, -⟩` from `ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ) (fun i => HT i.succ) (fun i => H i.succ)`. Establish `hS` using `h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR`. Establish `e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = (p 0 w A h rc).lpSum (sumList (List.ofFn fun i : Fin (c + 1) => p i.succ w A h rc))`.

Introduce `w A h rc`. Rewrite using `[List.ofFn_succ (f := fun i => p i w A h rc)]`. Both sides reduce to the same expression. Establish `e' : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ`. Use function extensionality and compare the values at `τ`.

Rewrite using `[Fin.sum_univ_succ]`. Use `⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ?_⟩` and prove the remaining obligations. Rewrite using `[e']`. Conclude with `hS.ht w fun A h rc hrc => by`. Use `hg A h rc hrc` as an intermediate fact.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[e]`. Conclude with `hS.par w A h rc hrc`. Use `absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)` and prove the remaining obligations. Conclude with `le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))`.
-/
theorem UpperTheory.V.Z.Win.Gu.sumFamG :
    SumTwoG → SumRed → SumFamG := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = p 0 w A h rc := by
      intro w A h rc
      simp [sumList, WD.lpSum_zero]
    have e' : (fun τ => ∑ i, HT i τ) = HT 0 := by
      funext τ
      simp
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · rw [e']
      exact (H 0).ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact (H 0).par w A h rc hrc
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) =
        (p 0 w A h rc).lpSum (sumList (List.ofFn fun i : Fin (c + 1) => p i.succ w A h rc)) := by
      intro w A h rc
      rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    have e' : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
      funext τ
      rw [Fin.sum_univ_succ]
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ?_⟩
    · rw [e']
      exact hS.ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact hS.par w A h rc hrc
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
