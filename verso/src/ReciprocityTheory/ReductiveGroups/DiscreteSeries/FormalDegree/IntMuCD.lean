import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def intMuCD_pM (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := fun kz => polarM kz

def intMuCD_P (ε : Fin n → Bool) : Measure (KG ε × (PCoord ε → ℂ)) :=
  (dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intMuCD_muPolarMat_eq (ε : Fin n → Bool) :
    muPolarMat ε = Measure.map (intMuCD_pM ε) (intMuCD_P ε) := rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lintegral_comap_embedding {α : Type*} [MeasurableSpace α] {e : α → (Fin n → Fin n → ℂ)}
    (he : MeasurableEmbedding e) (μ : Measure (Fin n → Fin n → ℂ)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range e)
    (F : (Fin n → Fin n → ℂ) → ENNReal) :
    ∫⁻ g, F (e g) ∂(Measure.comap e μ) = ∫⁻ x, F x ∂μ := by
  have h1 := he.lintegral_map (μ := Measure.comap e μ) F
  rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem hμ] at h1
  exact h1.symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intMuCD_measurable_pM (ε : Fin n → Bool) : Measurable (intMuCD_pM ε) := by
  exact Continuous.measurable (f := intMuCD_pM ε) (polarM_continuous ε)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem intMuCD_polar_int (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x ∂(muPolarMat ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hpm := intMuCD_measurable_pM ε
  have hJ : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [intMuCD_muPolarMat_eq, lintegral_map hF hpm, intMuCD_P]
  refine (lintegral_prod (F ∘ intMuCD_pM ε) (hF.comp hpm).aemeasurable).trans ?_
  refine lintegral_congr (fun k => ?_)
  refine (lintegral_withDensity_eq_lintegral_mul _ hJ (hF.comp (hpm.comp measurable_prodMk_left))).trans ?_
  refine lintegral_congr (fun z => ?_)
  exact mul_comm _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intMuCD_ae_range (ε : Fin n → Bool) (S : Set (Fin n → Fin n → ℂ)) (hS : MeasurableSet S)
    (h : ∀ kz : KG ε × (PCoord ε → ℂ), intMuCD_pM ε kz ∈ S) : ∀ᵐ x ∂(muPolarMat ε), x ∈ S := by
  rw [intMuCD_muPolarMat_eq]
  exact (ae_map_iff (p := fun x => x ∈ S) (intMuCD_measurable_pM ε).aemeasurable hS).2 (ae_of_all _ h)

def intMuCD_eM (ε : Fin n → Bool) : UJ ε → (Fin n → Fin n → ℂ) := fun g => toM g

def intMuCD_eU (ε : Fin n → Bool) : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := fun g => Formalism.MainNotions.S.umat g

/- English proof (translation)
Treat this case separately. Treat this case separately. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
private theorem Jm_mul_self_eq_oneFormalDegree (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  first
  | exact Jm_mul_Jm ε
  | (rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
     congr 1
     funext a
     split_ifs <;> norm_num)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * gᴴ * Jm ε * g = 1 := by
  have hg' : gᴴ * (Jm ε * g) = Jm ε := by
    rw [← Matrix.mul_assoc]
    exact hg
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_self_eq_oneFormalDegree]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem exists_UJ_toM_eq_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ u : UJ ε, toM u = g := by
  have hl := Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ' hg
  have hr : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp hl
    | exact Matrix.mul_eq_one_comm.mp hl
    | (letI := Matrix.invertibleOfLeftInverse g _ hl
       exact mul_invOf_self g)
  exact ⟨⟨⟨g, Jm ε * gᴴ * Jm ε, hr, hl⟩, hg⟩, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem isClosedEmbedding_intMuCD_eM (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (intMuCD_eM ε) := by
  have hC : ∀ g : UJ ε, inUJ ε (toM g) := fun g => g.2
  have hcont : Continuous (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hJt : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => Jm ε * xᴴ * Jm ε) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hG : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => (x, MulOpposite.op (Jm ε * xᴴ * Jm ε))) := by
    first
    | exact continuous_id.prodMk (MulOpposite.continuous_op.comp hJt)
    | exact continuous_id.prod_mk (MulOpposite.continuous_op.comp hJt)
  have hcomp : (fun x : Matrix (Fin n) (Fin n) ℂ => (x, MulOpposite.op (Jm ε * xᴴ * Jm ε))) ∘
        (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ (fun g : UJ ε => (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
    funext g
    have h1 : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Jm ε * (toM g)ᴴ * Jm ε :=
      Units.inv_eq_of_mul_eq_one_left (Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ' (g := toM g) (hC g))
    show (toM g, MulOpposite.op (Jm ε * (toM g)ᴴ * Jm ε)) = Units.embedProduct _ (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    rw [Units.embedProduct_apply, h1]
  have hind : Topology.IsInducing (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
    refine Topology.IsInducing.of_comp hcont hG ?_
    rw [hcomp]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hrange : Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = {x | inUJ ε x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact hC g
    · intro hx
      exact exists_UJ_toM_eq_of_inUJ hx
  have hclosed : IsClosed (Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))) := by
    rw [hrange]
    show IsClosed {x : Matrix (Fin n) (Fin n) ℂ | xᴴ * Jm ε * x = Jm ε}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hce : Topology.IsClosedEmbedding (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :=
    ⟨⟨hind, fun a b h => Subtype.ext (Units.ext h)⟩, hclosed⟩
  exact hce

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem lintegral_muPolar (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (toM g) ∂(muPolar ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eM ε) := (isClosedEmbedding_intMuCD_eM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eM ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (toM g) ∂(muPolar ε)
        = ∫⁻ g, F (intMuCD_eM ε g) ∂(Measure.comap (intMuCD_eM ε) (muPolarMat ε)) := rfl
    _ = ∫⁻ x, F x ∂(muPolarMat ε) := lintegral_comap_embedding hemb _ hae F
    _ = _ := intMuCD_polar_int ε F hF

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem lintegral_muCD (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eU ε) := by
    first
    | exact (isClosedEmbedding_intMuCD_eM ε).measurableEmbedding
    | exact (isClosedEmbedding_intMuCD_eM ε).measurableEmbedding (α := Formalism.REAL.UJ ε)
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eU ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε)
        = ENNReal.ofReal (cPQ ε) *
            ∫⁻ g, F (intMuCD_eU ε g) ∂(Measure.comap (intMuCD_eU ε) (muPolarMat ε)) := by
          rw [muCD, lintegral_smul_measure]
          rfl
    _ = _ := by rw [lintegral_comap_embedding hemb _ hae F, intMuCD_polar_int ε F hF]

end ReciprocityTheory.ChartRestriction.DS
