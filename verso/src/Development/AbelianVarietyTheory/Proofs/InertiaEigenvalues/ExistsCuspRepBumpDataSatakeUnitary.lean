import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.BumpData

/- English proof (translation)
Substitute using the available equality. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem exists_enum {X : Type} (M : Multiset X) {a : ℕ} (h : M.card = a) :
    ∃ f : Fin a → X, Finset.univ.val.map f = M := by
  subst h
  obtain ⟨l, rfl⟩ := Quotient.exists_rep M
  refine ⟨fun i => l.get ⟨i, by simpa using i.2⟩, ?_⟩
  rw [Fin.univ_val_map]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bumpData : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  intro E _ _ _ a π hπ T hT
  induction π using Quotient.inductionOn with | _ π₀ => ?_
  obtain ⟨ω, hωu, hω⟩ := hπ
  have hsat : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, (CG.mk π₀).HasSat w.1 (sat (CG.mk π₀) w.1) := by
    intro w
    have hx : ∃ B, (CG.mk π₀).HasSat w.1 B := hT w.1 w.2
    unfold sat
    rw [dif_pos hx]
    exact hx.choose_spec
  have hα : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∃ f : Fin a → ℂˣ,
      Finset.univ.val.map f = sat (CG.mk π₀) w.1 := fun w => exists_enum _ (hsat w).card
  choose α hα using hα
  refine ⟨α, π₀, ω, hα, rfl, hωu, hω, ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩, fun w => ?_⟩
  rw [hα w]
  exact hsat w

end GlobalTheory.BumpData
