import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ`. Take `⟨K, hKf, hK⟩` from `hB D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ`. Take `⟨-, hsymm, htrans⟩` from `hA D F0 Λ`. Unfold `cntE`. Rewrite using `[Set.encard_ne_top_iff]`.

Use `(hKf.image (fun k : (Fin D.R.rS → (VS D).V) × (VS D).V => {F'' : LFlag (VS D) D.R.rS (Tn u') | F'' ∈ EZ (Tn u') F0 Λ Z ∧ ∃ n ∈ N0 F0 Λ, (∀ a, n (k.1 a) = F''.fl.e a) ∧ n k.2 = F''.fl.z})).subset ?_` and prove the remaining obligations. Introduce and unpack `O ⟨F', hF', rfl⟩`. Take `⟨n₀, hn₀, hk⟩` from `hK F' hF'`. Use `⟨_, hk, ?_⟩` and prove the remaining obligations. Use extensionality with `F''`.

Simplify using `only [Set.mem_setOf_eq, NilradicalFlagMoved]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hE, m, hm, he, hz⟩`. Use `⟨hE, n₀.trans m, htrans _ hn₀ _ hm, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using he a`.

Simplify using `using hz`. Introduce and unpack `⟨hE, n, hn, he, hz⟩`. Use `⟨hE, n₀.symm.trans n, htrans _ (hsymm _ hn₀) _ hn, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using he a`. Simplify using `using hz`.
-/
theorem orbitFinite_of (hA : UnipotentIntegralIsGroup) (hB : OrbitReps) : OrbitFinite := by
  intro D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨K, hKf, hK⟩ := hB D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨-, hsymm, htrans⟩ := hA D F0 Λ
  unfold cntE
  rw [Set.encard_ne_top_iff]
  refine (hKf.image (fun k : (Fin D.R.rS → (VS D).V) × (VS D).V =>
      {F'' : LFlag (VS D) D.R.rS (Tn u') | F'' ∈ EZ (Tn u') F0 Λ Z ∧
        ∃ n ∈ N0 F0 Λ, (∀ a, n (k.1 a) = F''.fl.e a) ∧ n k.2 = F''.fl.z})).subset ?_
  rintro O ⟨F', hF', rfl⟩
  obtain ⟨n₀, hn₀, hk⟩ := hK F' hF'
  refine ⟨_, hk, ?_⟩
  ext F''
  simp only [Set.mem_setOf_eq, NilradicalFlagMoved]
  constructor
  · rintro ⟨hE, m, hm, he, hz⟩
    refine ⟨hE, n₀.trans m, htrans _ hn₀ _ hm, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz
  · rintro ⟨hE, n, hn, he, hz⟩
    refine ⟨hE, n₀.symm.trans n, htrans _ (hsymm _ hn₀) _ hn, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz

end PI.UnitaryGroupMassFormula.CntFormula
