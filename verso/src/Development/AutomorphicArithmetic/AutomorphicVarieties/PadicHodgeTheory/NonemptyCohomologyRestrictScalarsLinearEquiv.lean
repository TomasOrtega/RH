import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private def subEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' : Submodule Q X) (Z : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) : Z' ≃ₗ[Q] Z where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem quotEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' B' : Submodule Q X) (Z B : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) (hB : ∀ x, x ∈ B' ↔ x ∈ B) :
    Nonempty ((Z' ⧸ B'.comap Z'.subtype) ≃ₗ[Q] (Z ⧸ B.comap Z.subtype)) := by
  refine ⟨(Submodule.Quotient.equiv (B'.comap Z'.subtype) ((B.comap Z.subtype).restrictScalars Q)
    (subEq Z' Z hZ) ?_).trans (Submodule.Quotient.restrictScalarsEquiv Q (B.comap Z.subtype))⟩
  ext ⟨x, hx⟩
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : (y : X) = x := congrArg Subtype.val hyx
    show x ∈ B
    rw [← this]
    exact (hB _).1 hy
  · intro h
    exact ⟨⟨x, (hZ x).2 hx⟩, (hB x).2 h, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Unfold both sides to obtain the same proposition, which implies itself. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Unfold both sides to obtain the same proposition, which implies itself. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately.
-/
theorem UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv :
    ∀ (Q : Type) {A : Type} [CommRing Q] [CommRing A] [Algebra Q A] {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [ContinuousConstSMul Q V] (ρ : Representation A G V), Nonempty (↥(H0 (resCoef Q ρ)) ≃ₗ[Q] ↥(H0 ρ)) ∧ Nonempty (H1 (resCoef Q ρ) ≃ₗ[Q] H1 ρ) ∧ Nonempty (H2 (resCoef Q ρ) ≃ₗ[Q] H2 ρ) ∧ ∀ n, Nonempty (Hn (resCoef Q ρ) n ≃ₗ[Q] Hn ρ n) := by
  intro Q A _ _ _ G _ _ V _ _ _ _ _ _ _ _ ρ
  have hd : ∀ n (f : (Fin n → G) → V), dn (resCoef Q ρ) n f = dn ρ n f := by
    intro n f
    funext g
    rw [dn_apply, dn_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul A ((-1 : Q) ^ ((j : ℕ) + 1))]
    simp
  refine ⟨⟨subEq _ _ fun x => Iff.rfl⟩, quotEq _ _ _ _ (fun x => Iff.rfl) ?_,
    quotEq _ _ _ _ (fun x => Iff.rfl) ?_, fun n => quotEq _ _ _ _ ?_ ?_⟩
  · intro x
    simp only [ReciprocityTheory.Gal.B1, LinearMap.mem_range]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.B2, Submodule.mem_map, mem_contMaps]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.Zn, Submodule.mem_inf, LinearMap.mem_ker, ReciprocityTheory.Gal.Cn,
      mem_contMaps, hd]
  · intro x
    cases n with
    | zero => simp [ReciprocityTheory.Gal.Bn]
    | succ n => simp only [ReciprocityTheory.Gal.Bn, Submodule.mem_map, ReciprocityTheory.Gal.Cn, mem_contMaps, hd]
