import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hom_eq_zero_of_basicOpen_cover {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i (f : Γ(X, V i)) (s : Γ(M, X.basicOpen f)), φ.app (X.basicOpen f) s = 0) :
    φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov' : W ≤ ⨆ p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W}, X.basicOpen p.1.2 := by
    intro x hx
    have hx' : x ∈ iSup V := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨f, hfW, hxf⟩ := (hV i).exists_basicOpen_le ⟨x, hx⟩ hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨i, f⟩, hfW⟩, hxf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W} ↦ X.basicOpen p.1.2) W
    (fun p ↦ homOfLE p.2) hcov' _ _ fun p ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE p.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE p.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h p.1.1 p.1.2 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem app_basicOpen_eq_zero {X : Scheme.{0}} {M N : X.Modules} [M.IsQuasicoherent] (φ : M ⟶ N)
    {U : X.Opens} (hU : IsAffineOpen U) (h0 : ∀ t : Γ(M, U), φ.app U t = 0) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) : φ.app (X.basicOpen f) s = 0 := by
  obtain ⟨n, t, ht⟩ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff M f).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen M hU f)).1 s
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n) :=
    (GlobalTheory.QCoh.isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n
  have nat := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) t
  have key : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • φ.app (X.basicOpen f) s = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, ht]
    refine nat.trans ?_
    change (ConcreteCategory.hom (N.presheaf.map (homOfLE (X.basicOpen_le f)).op)) (φ.app U t) = 0
    rw [h0 t]
    simp
  exact (hu.smul_eq_zero).1 key

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem le_of_secs_subset_cover {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent]
    (S T : Subobject E) (hS : (S : X.Modules).IsQuasicoherent)
    (_hT : (T : X.Modules).IsQuasicoherent) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, secs S (V i) ⊆ secs T (V i)) : S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basicOpen_cover _ V hV hcov fun i f s ↦ ?_
    refine app_basicOpen_eq_zero _ (hV i) (fun t ↦ ?_) f s
    obtain ⟨y, hy⟩ := h i ⟨t, rfl⟩
    have hz : (T.arrow ≫ cokernel.π T.arrow).app (V i) y = 0 := by
      rw [cokernel.condition]; rfl
    change (cokernel.π T.arrow).app (V i) (S.arrow.app (V i) t) = 0
    rw [← hy]
    exact hz
  exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
