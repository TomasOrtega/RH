import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SolvableAscentInduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwistStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

namespace GalTw

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

/- English proof (translation)
Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `K _ _ _ _ _ _ _ hd π χ hsc r hr N hN hS`. Take `⟨hgal, hsol, hdec⟩` from `hS`. Distinguish the cases in `h1 : Module.finrank K M = 1`.

Take `⟨P, hP⟩` from `GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne K M h1 a ha π`. Take `⟨⟨χ', hχ'⟩, -⟩` from `GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K M l a ha π χ P hP.1 hsc`. Conclude with `⟨P, χ', hχ', hP⟩`. Use `haveI : Group.IsSolvable (M ≃ₐ[K] M) := hsol`. Use `haveI : Nontrivial (M ≃ₐ[K] M) := by`.

Rewrite using `[← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]`. Use `Module.finrank_pos (R := K) (M := M)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨H, hH, hp⟩` from `GlobalTheory.SolvUp.exists_normal_prime_index (M ≃ₐ[K] M)`. Set `K₁` to `IntermediateField.fixedField H`.

Use `haveI : IsGalois K K₁ := IsGalois.of_fixedField_normal_subgroup H`. Use `haveI : IsCMField K₁ := GlobalTheory.SolvUp.isCMField_intermediate Ω K M K₁`. Use `haveI : Module.IsTorsionFree K₁ Ω := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : IsAlgClosure K₁ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) K₁⟩`. Use `haveI : Group.IsSolvable (M ≃ₐ[K₁] M) := Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom K) (AlgEquiv.restrictScalars_injective K)`.

Establish `hdeg : Module.finrank K K₁ = H.index`. Establish `h2` using `Module.finrank_mul_finrank K K₁ M`. Rewrite `h2` using `[IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M, ← H.index_mul_card]`. Conclude with `Nat.eq_of_mul_eq_mul_right Nat.card_pos h2`. Establish `hp₁ : (Module.finrank K K₁).Prime` using `hdeg ▸ hp`.

Establish `hlt : Module.finrank K₁ M < d`. Rewrite using `[← hd, ← Module.finrank_mul_finrank K K₁ M, hdeg]`. Conclude with `lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt`. Establish `hmove : ∃ g : G K Ω, (∃ x : K₁, g (algebraMap K₁ Ω x) ≠ algebraMap K₁ Ω x) ∧ (r g).val.trace ≠ 0`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : K₁, x ∉ Set.range (algebraMap K K₁) := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hb : Function.Bijective (algebraMap K K₁)` using `⟨(algebraMap K K₁).injective, fun y => hc y⟩`. Conclude with `hp.one_lt.ne' (hdeg ▸ Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb)`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `hfixN : ∀ n ∈ N, n (algebraMap K₁ Ω x) = algebraMap K₁ Ω x`. Introduce `n hn`. Assume the negation of the conclusion as `hne`. Conclude with `hN n hn (hc n ⟨x, hne⟩)`.

Establish `hfix : ∀ g : G K Ω, g (algebraMap K₁ Ω x) = algebraMap K₁ Ω x`. Introduce `g`. Take `⟨z, n, hn, rfl⟩` from `hdec g`. Establish `hz : algebraMap K₁ Ω x = algebraMap M Ω (x : M)` using `IsScalarTower.algebraMap_apply K₁ M Ω x`. Use `show z (n (algebraMap K₁ Ω x)) = _`.

Rewrite using `[hfixN n hn, hz]`. Conclude with `z.commutes _`. Establish `hmem : algebraMap K₁ Ω x ∈ (⊥ : IntermediateField K Ω)`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω), IntermediateField.fixingSubgroup_bot, IntermediateField.mem_fixedField_iff]`. Introduce `g _`.

Conclude with `hfix g`. Take `⟨k, hk⟩` from `IntermediateField.mem_bot.1 hmem`. Apply `hx` to reduce the goal to its premises. Use `⟨k, (algebraMap K₁ Ω).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, ← IsScalarTower.algebraMap_apply]`.

Establish `hnotw : ∀ η : HChar K, UpperTheory.V.Published.IsNormChar K₁ η → ¬ UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η`. Introduce `η hη hst`. Take `⟨g, hgM, htr⟩` from `hmove`. Conclude with `htr (GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist Ω K K₁ hp₁ l ι a π r hr η hη hst g hgM)`. Take `⟨P₁, hP₁⟩` from `hI.ac K K₁ hp₁ a ha π hnotw`.

Establish `hc₁ : CharLift π P₁` using `hI.chl K K₁ hp₁ a ha π P₁ hP₁`. Take `⟨⟨χ₁, hχ₁⟩, -⟩` from `GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K K₁ l a ha π χ P₁ hP₁ hsc`. Establish `hr₁ : Weak P₁ ι (resTo K₁ r)` using `GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict K K₁ Ω l ι a π P₁ hP₁ r hr`. Set `N₁ : Subgroup (G K₁ Ω)` to `N.comap (AlgEquiv.restrictScalarsHom K)`. Establish `hS₁ : SolvDisj M N₁`.

Use `⟨inferInstance, ‹Group.IsSolvable (M ≃ₐ[K₁] M)›, fun g₁ => ?_⟩` and prove the remaining obligations. Take `⟨z, n, hn, he⟩` from `hdec (AlgEquiv.restrictScalarsHom K g₁)`. Establish `hn₁ : ∀ y : K₁, n (algebraMap K₁ Ω y) = algebraMap K₁ Ω y`. Introduce `y`. Establish `hy : algebraMap K₁ Ω y = algebraMap M Ω (y : M)` using `IsScalarTower.algebraMap_apply K₁ M Ω y`.

Establish `h3` using `DFunLike.congr_fun he (algebraMap K₁ Ω y)`. Express the relevant statement in the definitionally equal form `g₁ (algebraMap K₁ Ω y) = z (n (algebraMap K₁ Ω y)) at h3`. Rewrite `h3` using `[g₁.commutes]`. Apply `z.injective` to reduce the goal to its premises. Rewrite using `[← h3, hy]`.

Conclude with `(z.commutes _).symm`. Set `n₁ : G K₁ Ω` to `AlgEquiv.ofRingEquiv (f := n.toRingEquiv) hn₁`. Use `⟨z, n₁, ?_, ?_⟩` and prove the remaining obligations. Use `show AlgEquiv.restrictScalarsHom K n₁ ∈ N`. Use `hn using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `w`. Both sides reduce to the same expression. Use extensionality with `w`. Establish `h3` using `DFunLike.congr_fun he w`. Conclude with `h3`.

Take `⟨P, χ', hsc', hc'⟩` from `ih _ hlt K₁ rfl P₁ χ₁ hχ₁ (resTo K₁ r) hr₁ N₁ (fun n hn => hN _ hn) hS₁`. Conclude with `⟨P, χ', hsc', GlobalTheory.T.cuspRep_characterSupportLift_trans_tower K K₁ M a π P₁ P hc₁ hc'⟩`.
-/
theorem isWeaklyAttached_of_cmBaseChange_of_finrank (hI : UpperTheory.Gal.ToralGalois.Inq) (Ω : Type) [Field Ω] (M : Type) [Field M] [NumberField M] [IsCMField M]
    [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (d : ℕ) :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra K M]
      [IsScalarTower K M Ω], Module.finrank K M = d → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)),
      InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω),
      (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N →
      ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K _ _ _ _ _ _ _ hd π χ hsc r hr N hN hS
  obtain ⟨hgal, hsol, hdec⟩ := hS
  by_cases h1 : Module.finrank K M = 1
  · obtain ⟨P, hP⟩ := GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne K M h1 a ha π
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K M l a ha π χ P hP.1 hsc
    exact ⟨P, χ', hχ', hP⟩
  haveI : Group.IsSolvable (M ≃ₐ[K] M) := hsol
  haveI : Nontrivial (M ≃ₐ[K] M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := K) (M := M)
    omega
  obtain ⟨H, hH, hp⟩ := GlobalTheory.SolvUp.exists_normal_prime_index (M ≃ₐ[K] M)
  let K₁ := IntermediateField.fixedField H
  haveI : IsGalois K K₁ := IsGalois.of_fixedField_normal_subgroup H
  haveI : IsCMField K₁ := GlobalTheory.SolvUp.isCMField_intermediate Ω K M K₁
  haveI : Module.IsTorsionFree K₁ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K₁ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) K₁⟩
  haveI : Group.IsSolvable (M ≃ₐ[K₁] M) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom K) (AlgEquiv.restrictScalars_injective K)
  have hdeg : Module.finrank K K₁ = H.index := by
    have h2 := Module.finrank_mul_finrank K K₁ M
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M, ← H.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hp₁ : (Module.finrank K K₁).Prime := hdeg ▸ hp
  have hlt : Module.finrank K₁ M < d := by
    rw [← hd, ← Module.finrank_mul_finrank K K₁ M, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt

  have hmove : ∃ g : G K Ω, (∃ x : K₁, g (algebraMap K₁ Ω x) ≠ algebraMap K₁ Ω x) ∧ (r g).val.trace ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x : K₁, x ∉ Set.range (algebraMap K K₁) := by
      by_contra hc
      push_neg at hc
      have hb : Function.Bijective (algebraMap K K₁) := ⟨(algebraMap K K₁).injective, fun y => hc y⟩
      exact hp.one_lt.ne' (hdeg ▸ Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb)
    by_contra hc
    push_neg at hc
    have hfixN : ∀ n ∈ N, n (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro n hn
      by_contra hne
      exact hN n hn (hc n ⟨x, hne⟩)
    have hfix : ∀ g : G K Ω, g (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro g
      obtain ⟨z, n, hn, rfl⟩ := hdec g
      have hz : algebraMap K₁ Ω x = algebraMap M Ω (x : M) := IsScalarTower.algebraMap_apply K₁ M Ω x
      show z (n (algebraMap K₁ Ω x)) = _
      rw [hfixN n hn, hz]
      exact z.commutes _
    have hmem : algebraMap K₁ Ω x ∈ (⊥ : IntermediateField K Ω) := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω), IntermediateField.fixingSubgroup_bot,
        IntermediateField.mem_fixedField_iff]
      intro g _
      exact hfix g
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hmem
    apply hx
    refine ⟨k, (algebraMap K₁ Ω).injective ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply]

  have hnotw : ∀ η : HChar K, UpperTheory.V.Published.IsNormChar K₁ η → ¬ UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η := by
    intro η hη hst
    obtain ⟨g, hgM, htr⟩ := hmove
    exact htr (GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist Ω K K₁ hp₁ l ι a π r hr η hη hst g hgM)
  obtain ⟨P₁, hP₁⟩ := hI.ac K K₁ hp₁ a ha π hnotw
  have hc₁ : CharLift π P₁ := hI.chl K K₁ hp₁ a ha π P₁ hP₁
  obtain ⟨⟨χ₁, hχ₁⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K K₁ l a ha π χ P₁ hP₁ hsc
  have hr₁ : Weak P₁ ι (resTo K₁ r) := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict K K₁ Ω l ι a π P₁ hP₁ r hr
  let N₁ : Subgroup (G K₁ Ω) := N.comap (AlgEquiv.restrictScalarsHom K)
  have hS₁ : SolvDisj M N₁ := by
    refine ⟨inferInstance, ‹Group.IsSolvable (M ≃ₐ[K₁] M)›, fun g₁ => ?_⟩
    obtain ⟨z, n, hn, he⟩ := hdec (AlgEquiv.restrictScalarsHom K g₁)
    have hn₁ : ∀ y : K₁, n (algebraMap K₁ Ω y) = algebraMap K₁ Ω y := by
      intro y
      have hy : algebraMap K₁ Ω y = algebraMap M Ω (y : M) := IsScalarTower.algebraMap_apply K₁ M Ω y
      have h3 := DFunLike.congr_fun he (algebraMap K₁ Ω y)
      change g₁ (algebraMap K₁ Ω y) = z (n (algebraMap K₁ Ω y)) at h3
      rw [g₁.commutes] at h3
      apply z.injective
      rw [← h3, hy]
      exact (z.commutes _).symm
    let n₁ : G K₁ Ω := AlgEquiv.ofRingEquiv (f := n.toRingEquiv) hn₁
    refine ⟨z, n₁, ?_, ?_⟩
    · show AlgEquiv.restrictScalarsHom K n₁ ∈ N
      convert hn using 1
      ext w
      rfl
    · ext w
      have h3 := DFunLike.congr_fun he w
      exact h3
  obtain ⟨P, χ', hsc', hc'⟩ := ih _ hlt K₁ rfl P₁ χ₁ hχ₁ (resTo K₁ r) hr₁ N₁ (fun n hn => hN _ hn) hS₁
  exact ⟨P, χ', hsc', GlobalTheory.T.cuspRep_characterSupportLift_trans_tower K K₁ M a π P₁ P hc₁ hc'⟩

/- English proof (translation)
Introduce `hI Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ l _ ι a ha π χ hsc r hr N hN hS`. Conclude with `isWeaklyAttached_of_cmBaseChange_of_finrank hI Ω M l ι a ha _ K rfl π χ hsc r hr N hN hS`.
-/
theorem upWeak : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  intro hI Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ l _ ι a ha π χ hsc r hr N hN hS
  exact isWeaklyAttached_of_cmBaseChange_of_finrank hI Ω M l ι a ha _ K rfl π χ hsc r hr N hN hS

end GlobalTheory.RoadU

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | (exact @GlobalTheory.RoadU.upWeak) | (exact GlobalTheory.RoadU.upWeak) | (intros; apply GlobalTheory.RoadU.upWeak <;> assumption)`.
-/
theorem GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  first | (exact @GlobalTheory.RoadU.upWeak) | (exact GlobalTheory.RoadU.upWeak) | (intros; apply GlobalTheory.RoadU.upWeak  <;> assumption)

end
