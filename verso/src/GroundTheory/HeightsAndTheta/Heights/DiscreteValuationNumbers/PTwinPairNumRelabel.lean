import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordCompMidSwapVars
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace PairNumberRelabelAlt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mcIdeal_map_rename {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (y ∘ σ)).map (rename σ) = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y :=
  pointIdeal_map_rename e σ hσ y

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Simplify by unfolding definitions.

Substitute using the available equality. Supply the required witnesses or components.
-/
theorem mem_ratios {Ω₁ : Type*} [Field Ω₁] {K₀ : Type} {κ : K₀ → Type} (y : (Σ k, κ k) → Ω₁) (z : Ω₁) :
    z ∈ Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ↔
      ∃ a b : Σ k, κ k, a.1 = b.1 ∧ y a / y b = z := by
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨k, i⟩, ⟨k, j⟩, rfl, rfl⟩
  · rintro ⟨⟨k, i⟩, ⟨k', j⟩, h, rfl⟩
    dsimp only at h
    subst h
    exact ⟨⟨k, i, j⟩, rfl⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem fnField_comp {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} (O : Type) [CommRing O] {Ω : Type}
    [Field Ω] [Algebra O Ω] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Ω) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (y ∘ σ) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 1
  ext z
  simp only [Set.mem_union]
  refine or_congr_right ?_
  rw [mem_ratios, mem_ratios]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨σ.symm a, σ.symm b, ?_, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩
    apply e.injective
    rw [← hσ, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hab]
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨σ a, σ b, by rw [hσ, hσ, hab], rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem pairNum_eq_intNum (hF : VerticalComponentFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : IFamily (IsLocalRing.ResidueField O) ι) (hI : IsFieldIntersection I)
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d)
    {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P (y l - y' l) (f l) (g l))
    (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hM := ((BundleExamples.isModelOver_iff O P d).1 hP).2
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv := (VerticalDivisorCharacterisation.proof O K ι P ϖ (y l - y' l) (f l) (g l) hϖ hM.multiProj).1 (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hvar : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW0
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hvar
  · rfl

end PairNumberRelabelAlt

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal) in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem PairNumberRelabelAlt.proof (hF : VerticalComponentFibre.Statement) : PairNumberRelabelAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K₁ _ ι₁ _ K₂ _ ι₂ _ e σ hσ y d hM
  have hmap := PairNumberRelabelAlt.mcIdeal_map_rename O e σ hσ y
  have hM₁ := (BundleExamples.isModelOver_iff O (mcIdeal O (y ∘ σ)) d).1 hM
  have hM₂' : IsModelOver ((mcIdeal O (y ∘ σ)).map (rename σ)) d := by
    rw [PairNumberRelabel.map_rename_eq σ]
    exact PairNumberRelabel.isModelOver_map e σ hσ _ d hM₁.2
  have hM₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d := by
    rw [← hmap]
    exact (BundleExamples.isModelOver_iff O _ d).2 ⟨⟨e hM₁.1.some⟩, hM₂'⟩
  have hvd : ∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
      IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g → IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g) := by
    intro b f g h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h1 := (VerticalDivisorCharacterisation.proof O K₁ ι₁ _ ϖ (b ∘ e) f g hϖ hM₁.2.multiProj).1 h
    have h2 := PairNumberRelabel.isVerticalDivisor_map e σ hσ _ ϖ b f g h1
    rw [← PairNumberRelabel.map_rename_eq σ] at h2
    rw [← hmap]
    exact (VerticalDivisorCharacterisation.proof O K₂ ι₂ _ ϖ b _ _ hϖ hM₂'.multiProj).2 h2
  refine ⟨hM₂, PairNumberRelabelAlt.fnField_comp O e σ hσ y, hvd, ?_⟩
  intro I₁ I hI₁ hI n a a' f g hfg H hH
  have hfg' : ∀ i, IsVertDiv O (mcIdeal O y) (a i - a' i) (rename σ (f i)) (rename σ (g i)) :=
    fun i => hvd (a i - a' i) (f i) (g i) (hfg i)
  rw [PairNumberRelabelAlt.pairNum_eq_intNum hF I₁ hI₁ _ d hM (fun i => a i ∘ e) (fun i => a' i ∘ e) f g hfg H,
    PairNumberRelabelAlt.pairNum_eq_intNum hF I hI _ d hM₂ a a' _ _ hfg' H,
    BundleExamples.pairNum_eq _ d _ _ f g hH, BundleExamples.pairNum_eq _ d a a' _ _ hH, ← hmap,
    PairNumberRelabel.map_rename_eq σ, PairNumberRelabel.pairNum_map e σ hσ _ a a' f g]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
