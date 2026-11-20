import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentralizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryLocalComponentToLocalUnitaryGroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetsMeetingCompactSupportConjStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `E _ _ _ hU n hn S hS K' hK' f hf γ hγ`. Establish `hTB` using `fun w : Pl E => GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w`. Establish `hKo : ∀ w : Pl E, IsOpen (KL n w : Set (UL n w))` using `fun w => (hTB w).2.2.2.2.2.2.1`. Establish `hKc : ∀ w : Pl E, IsCompact (KL n w : Set (UL n w))` using `fun w => (hTB w).2.2.2.2.2.2.2.1`. Set `p : ∀ i : S, finU E n →* UL n i.1` to `fun i => ((cLoc i.1).comp (finU E n).subtype).codRestrict (UL n i.1) (fun x => GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)`.

Establish `hp : ∀ (i : S) (x : finU E n), p i x = toSub (UL n i.1) (cLoc i.1 (x : UA E n))`. Introduce `i x`. Unfold `toSub`. Rewrite using `[dif_pos (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)]`. Both sides reduce to the same expression.

Establish `hδ : ∀ i : S, p i (finPt γ) = locPt i.1 γ` using `fun i => (hp i _).trans (GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint E hU n γ i.1)`. Establish `hsep : ∀ w : Pl E, (locPt w γ).1.val.charpoly.Separable`. Introduce `w`. Rewrite using `[GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational E hU n γ w]`. Use `show ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) |>.charpoly.Separable`.

Rewrite using `[Matrix.charpoly_map]`. Conclude with `hγ.map`. Establish `hlev : ∀ w : Pl E, IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w)` using `fun w => ⟨hKo w, le_rfl, fun k hk => hk⟩`. Establish `hglob : globFn S f = fun x => ∏ᶠ i : S, f i.1 (p i x)`. Use function extensionality and compare the values at `x`.

Unfold `globFn`. Conclude with `(finprod_subtype_eq_finprod_cond (f := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n)))) (fun w => w ∈ S)).symm.trans (finprod_congr fun i => by rw [hp])`. Establish `hK : ∀ x : finU E n, x ∈ globLev S (KL n) ↔ ∀ i : S, p i x ∈ KL n i.1`. Introduce `x`. Unfold `globLev`.

Simplify using `only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Take `⟨k, hk, hke⟩` from `h i.1 i.2`. Establish `: p i x = k` using `Subtype.ext hke.symm`.

Rewrite using `[this]`. Conclude with `hk`. Introduce `h w hw`. Conclude with `⟨p ⟨w, hw⟩ x, h ⟨w, hw⟩, rfl⟩`. Rewrite using `[hglob]`.

Establish `hmain` using `GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod S (finU E n) (fun i : S => UL n i.1) p (globLev S (KL n)) (fun i => KL n i.1) (finPt γ) (fun i => f i.1) (fun i => by`. Establish `hfun : (p i : finU E n → UL n i.1) = fun x : finU E n => toSub (UL n i.1) (cLoc i.1 (x : UA E n))` using `funext (hp i)`. Rewrite using `[hfun]`. Conclude with `GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup E hU n i.1)`. Use the proof step `(fun x y h => GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq E hU n S hS x y (fun w hw => by rw [← hp ⟨w, hw⟩, ← hp ⟨w, hw⟩]; exact h ⟨w, hw⟩))`.

Use the proof step `(fun y hy => by`. Set `y' : ∀ w : Pl E, UL n w` to `fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 1`. Establish `hy' : ∀ᶠ w in cofinite, y' w ∈ KL n w`. Rewrite `hy`, the goal using `[Filter.eventually_cofinite]`. Use `(hy.image Subtype.val).subset ?_` and prove the remaining obligations.

Introduce `w hw`. Distinguish the cases in `hwS : w ∈ S`. Conclude with `⟨⟨w, hwS⟩, by simpa [y', hwS] using hw, rfl⟩`. Conclude with `absurd (by simp only [y', dif_neg hwS]; exact one_mem _) hw`. Take `⟨x, hx⟩` from `GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family E hU n S hS y' hy'`.

Conclude with `⟨x, fun i => by rw [hp, hx i.1 i.2]; simp [y', i.2]⟩)`. Use the proof step `(fun x => by`. Establish `h` using `GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral E hU n x`. Rewrite `h`, the goal using `[Filter.eventually_cofinite]`. Use `(h.preimage Subtype.val_injective.injOn).subset ?_` and prove the remaining obligations.

Introduce `i hi`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢`. Rewrite using `[← hp])` and apply the resulting hypothesis. Use `hK`. Use the proof step `(fun C hC hCK => by`.

Set `C' : ∀ w : Pl E, Set (UL n w)` to `fun w => if hw : w ∈ S then C ⟨w, hw⟩ else (KL n w : Set (UL n w))`. Establish `hC' : ∀ᶠ w in cofinite, C' w = KL n w`. Rewrite `hCK`, the goal using `[Filter.eventually_cofinite]`. Use `(hCK.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce `w hw`.

Distinguish the cases in `hwS : w ∈ S`. Conclude with `⟨⟨w, hwS⟩, by simpa [C', hwS] using hw, rfl⟩`. Conclude with `absurd (by simp only [C', dif_neg hwS]) hw`. Establish `h` using `GlobalTheory.T.isCompact_definiteUnitary_restricted_product E hU n S hS C' (fun w => by`. Distinguish the cases in `hw : w ∈ S`.

Simplify using `only [C', dif_pos hw]`. Conclude with `hC _`. Simplify using `only [C', dif_neg hw]`. Conclude with `hKc w) hC'`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hx w hw`. Use `hx ⟨w, hw⟩` as an intermediate fact.

Rewrite `this` using `[hp]`. Simplify `this` using `[C', hw]`. Introduce `hx i`. Use `hx i.1 i.2` as an intermediate fact. Rewrite using `[hp]`.

Simplify `this)` using `[C', i.2]`. Use the proof step `(fun i => hKc i.1)`. Use the proof step `(fun i => by rw [hδ]; exact GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable E hU n i.1 (locPt i.1 γ) (hsep i.1))`. Use the proof step `(fun i x => by rw [hδ]; exact (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).1 x)`. Use the proof step `(fun i x => GlobalTheory.T.rightStabilizer_conj_biinvariant_finiteIndex (UL n i.1) (KL n i.1) (K' i.1) (f i.1) (p i (finPt γ)) (hKc i.1) (hK'.1 i.1).1 (hK'.1 i.1).2.1 (hf.1 i.1).2 x)`.

Use the proof step `(fun i => by`. Rewrite using `[hδ]`. Conclude with `GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj (UL n i.1) (twCent (MonoidHom.id (UL n i.1)) (locPt i.1 γ)) (KL n i.1) (locPt i.1 γ) (f i.1) (hKc i.1) (hf.1 i.1).1 (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hs …`. Use the proof step `(by`. Establish `hgood` using `(GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact E hU n γ hγ).and (hf.2.and ((GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral E hU n hn γ hγ).and (GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ)))`.

Rewrite `hgood`, the goal using `[Filter.eventually_cofinite]`. Use `(hgood.preimage Subtype.val_injective.injOn).subset ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hδ]`. Conclude with `h)`. Rewrite using `[hmain]`. Repeatedly rewrite using `[hδ]`.

Conclude with `finprod_subtype_eq_finprod_cond (f := fun w => twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) (fun w => w ∈ S)`.
-/
theorem twOrb_globFn_eq_finprod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) = ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  have hTB := fun w : Pl E => GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w
  have hKo : ∀ w : Pl E, IsOpen (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.1
  have hKc : ∀ w : Pl E, IsCompact (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.2.1
  let p : ∀ i : S, finU E n →* UL n i.1 := fun i =>
    ((cLoc i.1).comp (finU E n).subtype).codRestrict (UL n i.1) (fun x => GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)
  have hp : ∀ (i : S) (x : finU E n), p i x = toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := by
    intro i x
    unfold toSub
    rw [dif_pos (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)]
    rfl
  have hδ : ∀ i : S, p i (finPt γ) = locPt i.1 γ := fun i => (hp i _).trans (GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint E hU n γ i.1)
  have hsep : ∀ w : Pl E, (locPt w γ).1.val.charpoly.Separable := by
    intro w
    rw [GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational E hU n γ w]
    show ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) |>.charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hγ.map
  have hlev : ∀ w : Pl E, IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    fun w => ⟨hKo w, le_rfl, fun k hk => hk⟩
  have hglob : globFn S f = fun x => ∏ᶠ i : S, f i.1 (p i x) := by
    funext x
    unfold globFn
    exact (finprod_subtype_eq_finprod_cond (f := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n)))) (fun w => w ∈ S)).symm.trans
      (finprod_congr fun i => by rw [hp])
  have hK : ∀ x : finU E n, x ∈ globLev S (KL n) ↔ ∀ i : S, p i x ∈ KL n i.1 := by
    intro x
    unfold globLev
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · intro h i
      obtain ⟨k, hk, hke⟩ := h i.1 i.2
      have : p i x = k := Subtype.ext hke.symm
      rw [this]; exact hk
    · intro h w hw
      exact ⟨p ⟨w, hw⟩ x, h ⟨w, hw⟩, rfl⟩
  rw [hglob]
  have hmain := GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod S (finU E n) (fun i : S => UL n i.1) p (globLev S (KL n)) (fun i => KL n i.1) (finPt γ)
    (fun i => f i.1)
    (fun i => by
      have hfun : (p i : finU E n → UL n i.1) = fun x : finU E n => toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := funext (hp i)
      rw [hfun]; exact GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup E hU n i.1)
    (fun x y h => GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq E hU n S hS x y (fun w hw => by rw [← hp ⟨w, hw⟩, ← hp ⟨w, hw⟩]; exact h ⟨w, hw⟩))
    (fun y hy => by
      let y' : ∀ w : Pl E, UL n w := fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 1
      have hy' : ∀ᶠ w in cofinite, y' w ∈ KL n w := by
        rw [Filter.eventually_cofinite] at hy ⊢
        refine (hy.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [y', hwS] using hw, rfl⟩
        · exact absurd (by simp only [y', dif_neg hwS]; exact one_mem _) hw
      obtain ⟨x, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family E hU n S hS y' hy'
      exact ⟨x, fun i => by rw [hp, hx i.1 i.2]; simp [y', i.2]⟩)
    (fun x => by
      have h := GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral E hU n x
      rw [Filter.eventually_cofinite] at h ⊢
      refine (h.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      rwa [← hp])
    hK
    (fun C hC hCK => by
      let C' : ∀ w : Pl E, Set (UL n w) := fun w => if hw : w ∈ S then C ⟨w, hw⟩ else (KL n w : Set (UL n w))
      have hC' : ∀ᶠ w in cofinite, C' w = KL n w := by
        rw [Filter.eventually_cofinite] at hCK ⊢
        refine (hCK.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [C', hwS] using hw, rfl⟩
        · exact absurd (by simp only [C', dif_neg hwS]) hw
      have h := GlobalTheory.T.isCompact_definiteUnitary_restricted_product E hU n S hS C' (fun w => by
        by_cases hw : w ∈ S
        · simp only [C', dif_pos hw]; exact hC _
        · simp only [C', dif_neg hw]; exact hKc w) hC'
      convert h using 1
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx w hw
        have := hx ⟨w, hw⟩
        rw [hp] at this
        simpa [C', hw] using this
      · intro hx i
        have := hx i.1 i.2
        rw [hp]
        simpa [C', i.2] using this)
    (fun i => hKc i.1)
    (fun i => by rw [hδ]; exact GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable E hU n i.1 (locPt i.1 γ) (hsep i.1))
    (fun i x => by rw [hδ]; exact (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).1 x)
    (fun i x => GlobalTheory.T.rightStabilizer_conj_biinvariant_finiteIndex (UL n i.1) (KL n i.1) (K' i.1) (f i.1) (p i (finPt γ)) (hKc i.1) (hK'.1 i.1).1
      (hK'.1 i.1).2.1 (hf.1 i.1).2 x)
    (fun i => by
      rw [hδ]
      exact GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj (UL n i.1) (twCent (MonoidHom.id (UL n i.1)) (locPt i.1 γ)) (KL n i.1) (locPt i.1 γ) (f i.1)
        (hKc i.1) (hf.1 i.1).1 (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).2)
    (by
      have hgood := (GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact E hU n γ hγ).and (hf.2.and ((GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral E hU n hn γ hγ).and (GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ)))
      rw [Filter.eventually_cofinite] at hgood ⊢
      refine (hgood.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      intro h
      apply hi
      rw [hδ]
      exact h)
  rw [hmain]
  simp_rw [hδ]
  exact finprod_subtype_eq_finprod_cond (f := fun w => twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) (fun w => w ∈ S)

end GlobalTheory.BCT
