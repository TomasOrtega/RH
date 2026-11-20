import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

/- English proof (translation)
Distinguish the cases in `h : Module.Finite κ V`. Establish `: Finite V` using `Module.finite_of_finite κ`. Rewrite using `[Module.natCard_eq_pow_finrank (K := κ)]`. Use `push_cast`. Rewrite using `[Real.log_pow]`.

Rewrite using `[Module.finrank_of_not_finite h]`. Establish `: Infinite V`. Assume the negation of the conclusion as `h'`. Use `not_infinite_iff_finite.1 h'` as an intermediate fact. Conclude with `h (Module.Finite.of_finite)`.

Simplify using `[Nat.card_eq_zero_of_infinite]`.
-/
theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

/- English proof (translation)
Establish `hdim` using `VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz`. Take `⟨W, j, _, _, rfl⟩` from `exists_isClosedImmersion_genericPoint z`. Establish `hrange : Set.range j = closure {j (genericPoint W)}`. Rewrite using `[← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]`. Use `letI := algebraΓAlong κ j`.

Establish `hW : topologicalKrullDim W = (0 : ℕ)` using `(topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim`. Rewrite using `[InterModel.interNumRed_eq_interNumOn _ j _ hrange, interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]`. Establish `hu (w : W) : w = genericPoint W`. Use `Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0 from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩` as an intermediate fact. Conclude with `IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)`.

Establish `hZ : ({genericPoint W} : Set W) = Set.univ` using `Set.eq_univ_of_forall hu`. Establish `hc : IsClosed ({genericPoint W} : Set W)` using `hZ ▸ isClosed_univ`. Use `isClosed_singleton_iff_isClosedImmersion.1 hc` as an intermediate fact. Establish `: Surjective (W.fromSpecResidueField (genericPoint W))` using `⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩`. Use `isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))` as an intermediate fact.

Establish `: IsAffine W` using `.of_isIso (inv (W.fromSpecResidueField (genericPoint W)))`. Establish `: IsIso (W.fromSpecResidueField (genericPoint W)).appTop` using `inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))`. Establish `b₁ : Function.Bijective (j.residueFieldMap (genericPoint W))`. Use `⟨RingHom.injective _, fun a => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `W.residue_surjective _ a`.

Take `⟨b, rfl⟩` from `j.stalkMap_surjective _ a`. Conclude with `⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩`. Establish `b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫ (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom)` using `ConcreteCategory.bijective_of_isIso _`. Establish `e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W))` using `(Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm`. Rewrite using `[← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ Y)] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

/- English proof (translation)
Introduce `k _ Y _ _ q hA hd l _ _ f hf`. Establish `: Module.Finite ℤ k` using `hA.finite`. Establish `: AlgebraicGeometry.IsNoetherian Y` using `hA.isNoetherian`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Take `⟨hpr, H, hH⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver`.

Establish `hp : IsProjOver (strHom (ZMod l) Y)`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`.

Establish `: IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)))` using `by rw [e]; infer_instance`. Establish `: IsProper (strHom (ZMod l) Y)` using `IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))`. Conclude with `(isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩`. Establish `: IsProper (strHom (ZMod l) Y)` using `(isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Establish `hd' : topologicalKrullDim Y = (0 + 1 : ℕ)` using `hd`.

Set `r : (LB.triv Y).ι → Y.functionFieldˣ` to `fun _ => Units.mk0 f hf`. Establish `hr : IsRatSec (LB.triv Y) r` using `fun _ _ h => by simp [r]`. Establish `hM` using `LB.isLB_triv Y`. Establish `key` using `GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr`. Rewrite `key` using `[interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)]`.

Establish `hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z` using `((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq`. Establish `hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w * interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y)` using `(CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)`. Establish `em` using `(AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin`. Rewrite `em` using `[← key]`. Simplify using `only [map_zero] at em`.

Use `(finsum_congr fun z => ?_).trans em.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _`. Rewrite using `[hm]`. Distinguish the cases in `hz : Scheme.ord f z = 0`. Simplify using `[hz]`.

Establish `hc : Order.coheight z = 1`. Assume the negation of the conclusion as `h`. Conclude with `hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)`. Rewrite using `[Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]`.
-/
theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) Y) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) Y) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) Y) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
