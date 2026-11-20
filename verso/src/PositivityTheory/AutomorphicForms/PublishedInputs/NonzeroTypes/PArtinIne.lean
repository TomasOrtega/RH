import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_artinIne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem val_ine (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact ord_eq_zero_iff.mp h0

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem exists_ine (ha : IsLocalArtin h a) (u : (w.adicCompletion E)ˣ)
    (hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1) :
    ∃ t : Ine (F := E) A, a (ineIncl h t) = u := by
  obtain ⟨σ, hσ⟩ := ha.surj u
  have h0 := ha.ord_eq σ
  rw [hσ, ord_eq_zero hu] at h0
  have hd : deg σ = 0 := by omega
  refine ⟨⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩, ?_⟩
  have e : ineIncl h ⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩ = σ := Subtype.ext rfl
  rw [e, hσ]

end P_artinIne

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem step_artinIne : ArtinInertiaProp := by
  intro E Ω _ _ _ _ _ A w h a ha
  exact ⟨P_artinIne.val_ine ha, P_artinIne.exists_ine ha⟩

end UpperTheory.TNZ
