import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Simplify using `only [Nat.le_zero]`. Conclude with `iSup_iSup_eq_left`.
-/
private theorem iSup_le_zero_nat {Y : Scheme.{u}} (G : ℕ → Y.IdealSheafData) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 := by
  simp only [Nat.le_zero]
  exact iSup_iSup_eq_left

namespace BlowupSequenceData

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Rewrite using `[controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]`. Conclude with `h`. Consider the case `succ t ih`.

Rewrite using `[controlledTransform_succ, controlledTransform_succ, ih]`.
-/
theorem controlledTransform_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (I I' : X.IdealSheafData)
    (h : I.comap (d.projectionToBase 0) = I'.comap (d.projectionToBase 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rw [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Rewrite using `[boundary_zero, boundary_zero, ← d.projectionToBase_zero]`. Conclude with `h`. Consider the case `succ t ih`.

Rewrite using `[boundary_succ, boundary_succ, ih]`.
-/
theorem boundary_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (E E' : List X.IdealSheafData)
    (h : List.map (fun D => D.comap (d.projectionToBase 0)) E = List.map (fun D => D.comap (d.projectionToBase 0)) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rw [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

/- English proof (translation)
Establish `hpowMul` using `d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK`. Establish `hAs` using `d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA`. Establish `hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤ (d.controlledTransform A m t ^ (m - l)).comap (d.map t)` using `Scheme.IdealSheafData.comap_mono _ hle`. Rewrite `hcomap` using `[Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs, mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m]`. Conclude with `(hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap`.
-/
theorem pow_controlledTransform_le_pow_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l t : ℕ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map t) (d.center t)))
    (hK : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ (m - l) * B =
        (d.controlledTransform K (m - l) t).comap (d.map t))
    (hA : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ m * B = (d.controlledTransform A m t).comap (d.map t))
    (hle : d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l)) :
    d.controlledTransform K (m - l) (t + 1) ^ m ≤ d.controlledTransform A m (t + 1) ^ (m - l) := by
  have hpowMul := d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK
  have hAs := d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA
  have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
      (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
    Scheme.IdealSheafData.comap_mono _ hle
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
  exact (hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap

end BlowupSequenceData

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[mem_orderAtLeastLocus_iff]`. Rewrite using `[mem_orderAtLeastLocus_iff]`. Establish `hm : 1 ≤ m` using `Nat.one_le_iff_ne_zero.mpr (by omega)`. Establish `hml : 1 ≤ m - l` using `by omega`.

Establish `h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x` using `orderAt_le_of_le h x`. Rewrite `h1` using `[orderAt_pow k p A (m - l) x, orderAt_pow k p K m x]`. Establish `h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x` using `(natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx`. Establish `h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3`.
-/
theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K A : Y.IdealSheafData) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hml : 1 ≤ m - l := by omega
  have h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  have h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x :=
    (natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx
  have h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x := by
    calc ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞)
        = ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) := mul_comm _ _
      _ ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x := h2
      _ ≤ ((m : ℕ) : ℕ∞) * orderAt K x := h1
  exact (natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]`. Consider the case `succ n ih`. Rewrite using `[Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]`.
-/
theorem comap_iSup_le_nat {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → Y.IdealSheafData) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]
  | succ n ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]

/- English proof (translation)
Use `revert h`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `h`. Rewrite using `[iSup_le_zero_nat]`.

Conclude with `h 0 le_rfl`. Consider the case `succ n ih`. Introduce `h`. Rewrite using `[Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Conclude with `(mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (ih fun l hl => h l (hl.trans (Nat.le_succ n)))`. Conclude with `(mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)`.
-/
theorem mem_support_iSup_le_nat {Y : Scheme.{u}} (n : ℕ) (G : ℕ → Y.IdealSheafData) (y : Y)
    (h : ∀ l ≤ n, y ∈ (G l).support) : y ∈ (⨆ l ≤ n, G l).support := by
  revert h
  induction n with
  | zero =>
    intro h
    rw [iSup_le_zero_nat]
    exact h 0 le_rfl
  | succ n ih =>
    intro h
    rw [Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]
    refine sup_le ?_ ?_
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        (ih fun l hl => h l (hl.trans (Nat.le_succ n)))
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

noncomputable abbrev divisorEmbedding : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t ⟶ Spec (CommRingCat.of T.base) :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Establish `h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme` using `ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr`. Rewrite using `[BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]`. Conclude with `Category.comp_id _`.

Consider the case `succ t ih`. Establish `hmap` using `embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t`. Establish `hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1)`. Rewrite using `[SequenceOfBlowups.blowupMorphism_eq_transitionMap]`. Conclude with `SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)`.

Establish `e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) = embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫ (ambientBlowupSeq hres hno …` using `congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f) (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)`. Establish `e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) = (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ (ambientBlowupSeq hres hno T j …` using `(Category.assoc _ _ _).symm`. Establish `e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t = (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫ (ambientBlow …` using `congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap`. Establish `e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t = s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).pro …` using `Category.assoc _ _ _`. Establish `e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) = s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀)` using `congrArg (fun f => s.transitionMapSucc t ≫ f) ih`.

Establish `e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) = (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀` using `(Category.assoc _ _ _).symm`. Establish `e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ = s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀` using `congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct`. Conclude with `e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))`.
-/
theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ := by
  induction t with
  | zero =>
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme :=
      ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]
    exact Category.comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)
    have e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) =
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f)
        (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      (Category.assoc _ _ _).symm
    have e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap
    have e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      Category.assoc _ _ _
    have e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) :=
      congrArg (fun f => s.transitionMapSucc t ≫ f) ih
    have e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) =
        (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ :=
      (Category.assoc _ _ _).symm
    have e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ =
        s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀ :=
      congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
