import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Proceed by induction. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P := by
  intro K S hS hSl hP ιr M _ _ hM
  obtain ⟨r, hr⟩ := hM
  have : Finite S := hS
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact gsEulerRatio_eq_one_of_subsingleton S M ιr
  | succ r ih =>
    letI : Module (ULift.{0} ℤ) M := M.hV2
    let T : Module.End (ULift.{0} ℤ) M := (ℓ : Module.End (ULift.{0} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : Finite (Rep.subrepresentation M ⊤ hD) :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0 :=
      ⟨r + 1, fun m => Subtype.ext (hr m.1)⟩
    have hmul := ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl
    have h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1 := by
      refine h K S hS hSl hP ιr _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr :=
      (gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3, mul_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ratioOne_of_killed (P : FiniteSubfield → Prop) (h : RatioOneKilled 2 P) : RatioOne 2 P :=
  ratioOne_of_killed_l 2 P h

end PositivityTheory.Lit1.GEN.W_devis
