import Development.EtaleCohomology.EtaleSheaves.ChowCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf

def OpenNbhdIC : Prop := ∀ {Z : Scheme.{0}} (U : Z.Opens), AICSch Z → (U : Set Z).Nonempty → AICSch U.toScheme

def FFAlg : Prop := ∀ {Z : Scheme.{0}} [IsIntegral Z], AICSch Z → IsAlgClosed Z.functionField

def NormAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g], AICSch g.normalization

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem spec_field_qc (K : Type) [Field K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W) : QuasiCompact g := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  exact (Set.toFinite _).isCompact

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem Norm_of (h0 : OpenNbhdIC) (h1 : FFAlg) (h2 : NormAIC) : LateralTheory.E.ChowCut.Norm := by
  intro Z W f _ hZ ⟨U, s, hU, hs⟩
  have : IsIntegral Z := hZ.1
  have hUa := h0 U hZ hU
  have := hUa.1
  have := h1 hUa
  let g0 : Spec (CommRingCat.of U.toScheme.functionField) ⟶ U.toScheme := U.toScheme.fromSpecStalk _
  let g := g0 ≫ s
  have := spec_field_qc _ g
  refine ⟨g.normalization, g.fromNormalization, inferInstance, h2 _ g, ?_⟩
  have hg0 : IsDominant g0 := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.range_fromSpecStalk]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec U.toScheme).def ▸ closure_mono (Set.singleton_subset_iff.mpr (specializes_refl _)))
  have hU' : IsDominant U.ι := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).closure_eq
  have e : g.toNormalization ≫ g.fromNormalization ≫ f = g0 ≫ U.ι := by
    rw [reassoc_of% g.toNormalization_fromNormalization, Category.assoc, hs]
  have : IsDominant (g.toNormalization ≫ g.fromNormalization ≫ f) := by rw [e]; infer_instance
  exact IsDominant.of_comp g.toNormalization _

end LateralTheory.E.NormPf

end
