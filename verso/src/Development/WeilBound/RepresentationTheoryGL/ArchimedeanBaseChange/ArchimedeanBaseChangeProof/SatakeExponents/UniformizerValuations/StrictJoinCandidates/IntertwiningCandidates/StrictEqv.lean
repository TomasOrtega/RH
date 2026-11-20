import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictEquivalence

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨x1, x2⟩` from `x`. Take `⟨y1, y2⟩` from `y`. Take `⟨h, hI⟩` from `h`. Simplify using `only at h`. Substitute `h` using the available equality.

Conclude with `⟨rfl, F5.Bo.isoV_symm' hx hI⟩`.
-/
theorem siso_symm (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hx : IsStable x.2) (h : SIso x y) : SIso y x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := h
  simp only at h
  subst h
  exact ⟨rfl, F5.Bo.isoV_symm' hx hI⟩

/- English proof (translation)
Take `⟨x1, x2⟩` from `x`. Take `⟨y1, y2⟩` from `y`. Take `⟨z1, z2⟩` from `z`. Take `⟨h, hI⟩` from `h`. Take `⟨h', hI'⟩` from `h'`.

Simplify using `only at h h'`. Substitute `h h'` using the available equality. Conclude with `⟨rfl, F5.Bo.isoV_trans' hI hI'⟩`.
-/
theorem siso_trans (x y z : Σ M : ℕ, Submodule ℂ (Sm E M)) (h : SIso x y) (h' : SIso y z) : SIso x z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h, hI⟩ := h
  obtain ⟨h', hI'⟩ := h'
  simp only at h h'
  subst h h'
  exact ⟨rfl, F5.Bo.isoV_trans' hI hI'⟩

/- English proof (translation)
The claim follows from `| _, _, _, List.Forall₂.nil => List.Forall₂.nil | _, _, hp, List.Forall₂.cons hab htl => List.Forall₂.cons (hRS _ _ (hp _ (List.mem_cons_self ..)) hab) (forall₂_flip_of hRS (fun x hx => hp x (List.mem_cons_of_mem _ hx)) htl)`.
-/
theorem forall₂_flip_of {α : Type} {R S : α → α → Prop} {p : α → Prop} (hRS : ∀ x y, p x → R x y → S y x) :
    ∀ {l l' : List α}, (∀ x ∈ l, p x) → List.Forall₂ R l l' → List.Forall₂ S l' l
  | _, _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, hp, List.Forall₂.cons hab htl =>
      List.Forall₂.cons (hRS _ _ (hp _ (List.mem_cons_self ..)) hab)
        (forall₂_flip_of hRS (fun x hx => hp x (List.mem_cons_of_mem _ hx)) htl)

/- English proof (translation)
The claim follows from `| _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil | _, _, _, List.Forall₂.cons hab htl, List.Forall₂.cons hbc htl' => List.Forall₂.cons (hR _ _ _ hab hbc) (forall₂_trans_of hR htl htl')`.
-/
theorem forall₂_trans_of {α : Type} {R : α → α → Prop} (hR : ∀ x y z, R x y → R y z → R x z) :
    ∀ {l l' l'' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l'' → List.Forall₂ R l l''
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons hab htl, List.Forall₂.cons hbc htl' =>
      List.Forall₂.cons (hR _ _ _ hab hbc) (forall₂_trans_of hR htl htl')

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[parts, List.mem_ofFn]`. Take `⟨i, rfl⟩` from `hx`. Conclude with `(P.discrete i).stable`.
-/
theorem parts_stable {n : ℕ} (P : Pre E n) : ∀ x ∈ parts P, IsStable x.2 := by
  intro x hx
  rw [parts, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (P.discrete i).stable

end StrictEquivalence

open StrictEquivalence in
/- English proof (translation)
Introduce `E _ _ _ n P P' P''`. Use `⟨fun ⟨hF, hc, hm⟩ => ⟨forall₂_flip_of (p := fun x => IsStable x.2) (fun x y hx h => siso_symm x y hx h) (parts_stable P) hF, hc.symm, fun i => ?_⟩, fun ⟨hF, hc, hm⟩ ⟨hF', hc', hm'⟩ => ⟨forall₂_trans_of siso_trans hF hF', hc.trans hc', fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hm (Fin.cast hc.symm i)]`. Use `congr 1`. Rewrite using `[hm i, hm' (Fin.cast hc i)]`.

Use `congr 1`.
-/
theorem StrictEqv_holds : StrictEqv := by
  intro E _ _ _ n P P' P''
  refine ⟨fun ⟨hF, hc, hm⟩ => ⟨forall₂_flip_of (p := fun x => IsStable x.2) (fun x y hx h => siso_symm x y hx h)
      (parts_stable P) hF, hc.symm, fun i => ?_⟩, fun ⟨hF, hc, hm⟩ ⟨hF', hc', hm'⟩ =>
      ⟨forall₂_trans_of siso_trans hF hF', hc.trans hc', fun i => ?_⟩⟩
  · rw [hm (Fin.cast hc.symm i)]
    congr 1
  · rw [hm i, hm' (Fin.cast hc i)]
    congr 1

end PositivityTheory.Rg.BcB.F.FX.Bo

end
