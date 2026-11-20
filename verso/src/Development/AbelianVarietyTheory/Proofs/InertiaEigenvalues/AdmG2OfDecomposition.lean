import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.GTwoTheta

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

/- English proof (translation)
Take `⟨hlow, -, hcl, h0⟩` from `hc j hj1 hjm ρ`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `Nat.cast_nonneg _`. Consider the cases of `up`. Simplify using `only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]`. Introduce and unpack `(h | h)`.

Use `hcl _ h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith`. Simplify `h0` using `only [JW, cloudT, lowT, ↓reduceIte]`.
-/
theorem zero_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hjm ρ
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]
    rintro (h | h)
    · have := hcl _ h; linarith
    · rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith
  · simpa only [JW, cloudT, lowT, ↓reduceIte] using h0

/- English proof (translation)
Introduce `q hq`. Consider the cases of `up`. Simplify using `only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq`. Simplify using `only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]`. Break down `hq with h | h` into its components or cases.

Conclude with `Or.inl (Or.inl h)`. Conclude with `Or.inl (Or.inr h)`. Simplify using `only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq`. Simplify using `only [JJ, ↓reduceIte, Jp, Set.mem_union]`. Conclude with `Or.inl hq`.
-/
theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]
    rcases hq with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inl hq

/- English proof (translation)
Introduce `h` and use `((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)`.
-/
theorem neg_one_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (-1 : ℚ) ∉ JW D up j ρ :=
  fun h => ((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

/- English proof (translation)
Use `D.nd.lPrime i` as an intermediate fact. Establish `hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t` using `D.R.t) (r π) (ρ π) (D.nd.chi i) e := (GlobalTheory.DecompForms.main D i r ρ π).1 hD`. Establish `hsum` using `(GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc`. Conclude with `⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1, (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩`.
-/
theorem dR_WT (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  have := D.nd.lPrime i
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e :=
    (GlobalTheory.DecompForms.main D i r ρ π).1 hD
  have hsum := (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc
  exact ⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1,
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

/- English proof (translation)
Use `D.nd.lPrime i` as an intermediate fact. Establish `hjr` using `D.nd.j_range i`. Take `⟨hdrW, hdrT⟩` from `dR_WT D i r ρ π w hw C hD hc`. Take `⟨τ₀⟩` from `GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le`. Take `⟨g, ρ', -, -, hW⟩` from `hJ i r hr w hw C τ₀`.

Take `⟨-, hW0, -, hT0⟩` from `hW ρ π hπ hD 0`. Prove the components needed by the constructor for the conclusion. Use `GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_` and prove the remaining obligations. Use `hW0.trans ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Use `push_cast`. Conclude with `zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _`. Use `GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_` and prove the remaining obligations. Use `hT0.trans ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Rewrite using `[GlobalTheory.JumpSets.dualS_int]`. Use `push_cast`. Conclude with `neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _`.
-/
theorem twistedRep_no_invariants_purity (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hr : GoodR D.nd i r)
    (hπ : π ∈ D.nd.Z i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) = ⊥ ∧ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) = ⊥ := by
  have := D.nd.lPrime i
  have hjr := D.nd.j_range i
  obtain ⟨hdrW, hdrT⟩ := dR_WT D i r ρ π w hw C hD hc
  obtain ⟨τ₀⟩ := GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le
  obtain ⟨g, ρ', -, -, hW⟩ := hJ i r hr w hw C τ₀
  obtain ⟨-, hW0, -, hT0⟩ := hW ρ π hπ hD 0
  constructor
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_
    refine hW0.trans ?_
    rw [if_neg]
    push_cast
    exact zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_
    refine hT0.trans ?_
    rw [if_neg]
    rw [GlobalTheory.JumpSets.dualS_int]
    push_cast
    exact neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

/- English proof (translation)
Use `D.nd.lPrime i` as an intermediate fact. Establish `hm` using `hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a`. Use `(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _ (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_` and prove the remaining obligations. Use `(Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem chi_jump (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hamb : ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0)
    (c : ℕ) (hc1 : 1 ≤ c) (hct : c ≤ D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a ↔ a = (c : ℤ) - 1 := by
  have := D.nd.lPrime i
  have hm := hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a
  refine (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _
    (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_
  refine (Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_
  split_ifs with h <;> simp [h]

/- English proof (translation)
Establish `hjr` using `D.nd.j_range i`. Take `⟨g, ρ', -, hx, -⟩` from `hJ i r hr w hw C τ`. Use `⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]`. Apply the tactic sequence `rw [← locC_rTwO, (hx x a).2.1] split_ifs <;> norm_num`.

Rewrite using `[← locC_rTwO, (hx x (-1)).1]`. Use `push_cast`. Conclude with `((hJc _ hjr.1 hjr.2 ρ').2.1 _).1`.
-/
theorem tw_jumps (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    (∀ (x y : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a =
        multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r y)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a) ∧
    (∀ (x : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a ≤ 1) ∧
    (∀ x : D.nd.X i,
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ (-1)) := by
  have hjr := D.nd.j_range i
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i r hr w hw C τ
  refine ⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩
  · rw [← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]
  · rw [← locC_rTwO, (hx x a).2.1]
    split_ifs <;> norm_num
  · rw [← locC_rTwO, (hx x (-1)).1]
    push_cast
    exact ((hJc _ hjr.1 hjr.2 ρ').2.1 _).1

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

/- English proof (translation)
Introduce `hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C`. Take `⟨ep, hJ⟩` from `hJa`. Establish `hcrys` using `GlobalTheory.CrysFromGTwo.main hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C`. Establish `hamb` using `GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C`. Establish `hH` using `twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2`.

Use `⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1, fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, h …` and prove the remaining obligations. Rewrite using `[← locC_rTwO]`. Conclude with `(hcrys.2 x).2`.
-/
theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  intro hF D L hG2 hJa hJc i r ρ π hr h0 h1 hπ hD w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hcrys := GlobalTheory.CrysFromGTwo.main hF D i r ρ π hr (hG2 i r hr) h0 h1 hD w hw C
  have hamb := GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i r ρ π hD hπ h0 h1 w hw C
  have hH := twistedRep_no_invariants_purity D L ep hJ hJc i r ρ π hr hπ w hw C hD (hcrys.2 π).2
  refine ⟨⟨fun x => (hcrys.2 x).1, fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).1,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.1,
    fun c hc1 hct τ a => chi_jump D i r ρ π w hw C (fun τ => (hamb τ).2) c hc1 hct τ a,
    fun τ => (tw_jumps D L ep hJ hJc i r hr w hw C τ).2.2, hH.1, hH.2⟩, fun x => ?_⟩
  rw [← locC_rTwO]
  exact (hcrys.2 x).2

end GlobalTheory.GTwoTheta
