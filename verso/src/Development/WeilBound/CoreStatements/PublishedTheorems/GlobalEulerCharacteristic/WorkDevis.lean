import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

/- English proof (translation)
Introduce `K S hS hSl hP ιr M _ _ hM`. Take `⟨r, hr⟩` from `hM`. Establish `: Finite S` using `hS`. Proceed by induction on `r generalizing M with`. Consider the case `zero`.

Establish `: Subsingleton M` using `⟨fun a b => by`. Establish `ha` using `hr a`. Establish `hb` using `hr b`. Simplify using `only [pow_zero, one_smul] at ha hb`. Rewrite using `[ha, hb]⟩`.

Conclude with `gsEulerRatio_eq_one_of_subsingleton S M ιr`. Consider the case `succ r ih`. Use `letI : Module (ULift.{0} ℤ) M := M.hV2`. Set `T : Module.End (ULift.{0} ℤ) M` to `(ℓ : Module.End (ULift.{0} ℤ) M)`. Establish `hTx : ∀ x : M, T x = ℓ • x` using `fun x => Module.End.natCast_apply ℓ x`.

Establish `hT : ∀ g, Commute T (M.ρ g)` using `fun g => Nat.cast_commute ℓ _`. Establish `hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤` using `fun _ => le_top`. Establish `hSE` using `rangeStepComplex_shortExact T hT ⊤ hD`. Establish `: Finite (Rep.subrepresentation M ⊤ hD)` using `Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h`. Establish `: Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD))` using `Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M)) fun _ _ h => Subtype.ext h`.

Establish `: Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD))` using `Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M)) fun _ _ h => Subtype.ext h`. Establish `hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0` using `⟨r + 1, fun m => Subtype.ext (hr m.1)⟩`. Establish `hmul` using `ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl`. Establish `h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1`. Use `h K S hS hSl hP ιr _ fun m => Subtype.ext ?_` and prove the remaining obligations.

Establish `h' : T m.1 = 0` using `m.2.2`. Rewrite `h'` using `[hTx]`. Conclude with `h'`. Establish `h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1`. Use `ih _ fun m => Subtype.ext ?_` and prove the remaining obligations.

Take `⟨x, -, hx⟩` from `m.2`. Express the relevant statement in the definitionally equal form `(ℓ ^ r) • m.1 = 0`. Rewrite using `[← hx, hTx, smul_smul, ← pow_succ]`. Conclude with `hr x`. Establish `htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr` using `(gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm`.

Rewrite using `[htop, hmul, h1, h3, mul_one]`.
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
The claim follows from `ratioOne_of_killed_l 2 P h`.
-/
theorem ratioOne_of_killed (P : FiniteSubfield → Prop) (h : RatioOneKilled 2 P) : RatioOne 2 P :=
  ratioOne_of_killed_l 2 P h

end PositivityTheory.Lit1.GEN.W_devis
