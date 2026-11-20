import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFramePStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroupStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.SumK

/- English proof (translation)
Use `⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩` and prove the remaining obligations. Apply `(h.2.union h'.2).subset` to reduce the goal to its premises. Introduce `p hp`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc`.

Conclude with `hp (by rw [hc.1, hc.2])`.
-/
theorem inGen_symm_of {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (hE : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p))) {d y y' : Dat Z FP}
    (h : InGen d y) (h' : InGen d y') : InGen y y' := by
  refine ⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩
  apply (h.2.union h'.2).subset
  intro p hp
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2])

/- English proof (translation)
Introduce `D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω`. Substitute `hK` using the available equality. Take `⟨hEq, -, hRel⟩` from `GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR`. Establish `hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z` using `Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' := fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩`. Establish `hout : ∀ o : Quot (GRel (Z` using `Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by`.

Introduce `o y h`. Conclude with `(hQ _ _).1 (by rw [h, Quot.out_eq])`. Establish `hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ}, ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1`. Introduce and unpack `⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩`. Conclude with `⟨y, t, ht, Λ, h1, h2, h3, h4⟩`.

Use `choose yOf hyOf using hex`. Use `set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ`. Establish `hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' → LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y'` using `fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 => ((hRel Λ Λ' y y' h3 h4).1).1 (GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)`. Establish `hImg : ∀ κ, InGen d (φ κ).out`. Introduce `κ`.

Take `⟨t, -, Λ, h1, h2, h3, -⟩` from `hyOf κ`. Conclude with `hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))`. Unfold `massA`. Rewrite using `[← ENNReal.tsum_fiberwise _ φ]`. Use `tsum_congr fun o => ?_` and prove the remaining obligations.

Distinguish the cases in `ho : InGen d o.out`. Rewrite using `[if_pos ho]`. Establish `hIG01 : InGen y₀ o.out` using `inGen_symm_of (hRelEqv D Z FP) hIG₀ ho`. Take `⟨Λ₁, hLO₁, hloc⟩` from `GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01`. Take `⟨t₁, hTG₁⟩` from `GlobalTheory.T.exists_rowTerm_of_local_completions_terms D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁`.

Establish `ht₁ : t₁ ∈ TS` using `hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀`. Take `⟨-, hcarry, hwt, hmass⟩` from `GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl`. Establish `hRefl : LRel F F' Λ₁ Λ₁` using `((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)`. Establish `hStab : stabL F F' Λ₁ = stabY F F' o.out` using `(hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2`. Establish `hfib : Subtype.val '' (φ ⁻¹' {o}) = {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ}`.

Use extensionality with `κ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Take `⟨t, -, Λ, h1, h2, -, h4⟩` from `hyOf b`. Establish `hb' : φ b = o` using `hb`.

Use `⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩` and prove the remaining obligations. Introduce and unpack `hκ`. Take `⟨t, hTG, hkey⟩` from `hcarry κ hκ`. Establish `htS : t ∈ TS` using `hTS t₁ t Λ₁ Λ₁ hTG₁ hTG (fun p => ⟨1, Subgroup.one_mem _, by`. Simplify using `[LocNG.img]⟩) ht₁`.

Establish `hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ}` using `⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩`. Use `⟨⟨κ, hmem⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show φ ⟨κ, hmem⟩ = o`. Take `⟨t', -, Λ', h1, h2, -, h4⟩` from `hyOf ⟨κ, hmem⟩`. Rewrite using `[hφ]`.

Simplify using `only`. Rewrite using `[← Quot.out_eq o]`. Conclude with `Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))`. Establish `hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2)`. Introduce `b`.

Establish `hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o})` using `⟨b.1, b.2, rfl⟩`. Rewrite `hb` using `[hfib]`. Take `⟨t, hTG, hkey⟩` from `hcarry _ hb`. Rewrite using `[hω b.1 t hkey, hwt t Λ₁ hTG hRefl]`. Rewrite using `[tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]`.

Rewrite using `[if_neg ho]`. Use `ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim` and prove the remaining obligations. Establish `hb : φ b.1 = o` using `b.2`. Rewrite using `[← hb]`. Conclude with `hImg b.1`.
-/
theorem weights_add_up_to_mass_of
    (hRelEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)))
    (hInv : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y') :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  intro D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω
  subst hK
  obtain ⟨hEq, -, hRel⟩ := GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR
  have hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z := Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' :=
    fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩
  have hout : ∀ o : Quot (GRel (Z := Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by
    intro o y h
    exact (hQ _ _).1 (by rw [h, Quot.out_eq])

  have hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ},
      ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1 := by
    rintro ⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩
    exact ⟨y, t, ht, Λ, h1, h2, h3, h4⟩
  choose yOf hyOf using hex
  set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ
  have hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' →
      LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y' := fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 =>
    ((hRel Λ Λ' y y' h3 h4).1).1 (GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)
  have hImg : ∀ κ, InGen d (φ κ).out := by
    intro κ
    obtain ⟨t, -, Λ, h1, h2, h3, -⟩ := hyOf κ
    exact hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))
  unfold massA
  rw [← ENNReal.tsum_fiberwise _ φ]
  refine tsum_congr fun o => ?_
  by_cases ho : InGen d o.out
  · rw [if_pos ho]
    have hIG01 : InGen y₀ o.out := inGen_symm_of (hRelEqv D Z FP) hIG₀ ho
    obtain ⟨Λ₁, hLO₁, hloc⟩ := GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01
    obtain ⟨t₁, hTG₁⟩ := GlobalTheory.T.exists_rowTerm_of_local_completions_terms D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁
    have ht₁ : t₁ ∈ TS := hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀
    obtain ⟨-, hcarry, hwt, hmass⟩ := GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl
    have hRefl : LRel F F' Λ₁ Λ₁ := ((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)
    have hStab : stabL F F' Λ₁ = stabY F F' o.out := (hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2

    have hfib : Subtype.val '' (φ ⁻¹' {o}) =
        {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ} := by
      ext κ
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨t, -, Λ, h1, h2, -, h4⟩ := hyOf b
        have hb' : φ b = o := hb
        refine ⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩
      · rintro hκ
        obtain ⟨t, hTG, hkey⟩ := hcarry κ hκ
        have htS : t ∈ TS := hTS t₁ t Λ₁ Λ₁ hTG₁ hTG
          (fun p => ⟨1, Subgroup.one_mem _, by
            simp [LocNG.img]⟩) ht₁
        have hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} :=
          ⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩
        refine ⟨⟨κ, hmem⟩, ?_, rfl⟩
        show φ ⟨κ, hmem⟩ = o
        obtain ⟨t', -, Λ', h1, h2, -, h4⟩ := hyOf ⟨κ, hmem⟩
        rw [hφ]
        simp only
        rw [← Quot.out_eq o]
        exact Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))
    have hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2) := by
      intro b
      have hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o}) := ⟨b.1, b.2, rfl⟩
      rw [hfib] at hb
      obtain ⟨t, hTG, hkey⟩ := hcarry _ hb
      rw [hω b.1 t hkey, hwt t Λ₁ hTG hRefl]
    rw [tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]
  · rw [if_neg ho]
    refine ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim
    have hb : φ b.1 = o := b.2
    rw [← hb]
    exact hImg b.1

/- English proof (translation)
The claim follows from `weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place GlobalTheory.T.genus_stable_under_rationalComplementGroup`.
-/
theorem weights_add_up_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d :=
  weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place GlobalTheory.T.genus_stable_under_rationalComplementGroup

end GlobalTheory.Unfold.SumK
