import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem push_mat_eq_mat_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : GQ l) : (push f r s).mat = (r s).mat.map f := by
  rfl
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem sh_push_eq_sh_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) (s : GQ l) : D.sh (push f r) a s = (D.sh r a s).map f := by
  ext i j
  simp only [Dat3.sh, Matrix.sub_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, push_mat_eq_mat_map, map_sub]
  split_ifs <;> simp
/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
private theorem tr_push_algHom_eq_map_tr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) : D.tr (push f r) a = f (D.tr r a) := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [Dat3.tr, sh_push_eq_sh_map, push_mat_eq_mat_map, h, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem map_dd_eq_dd_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) : f (D.dd r a) = D.dd (push f r) a := by
  simp only [Dat3.dd, tr_push_algHom_eq_map_tr, map_sub, map_mul, AlgHom.commutes]
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem map_coeff_charpoly_sub_prod_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : GQ l) (i : ℕ) : f (((r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) = (((push f r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) := by
  have h1 : (push f r s).mat.charpoly = (r s).mat.charpoly.map (f : C →+* C') := by
    rw [push_mat_eq_mat_map]
    exact Matrix.charpoly_map _ _
  have h2 : ∀ a : Fin 3, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))) = (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))).map (f : C →+* C') := by
    intro a
    simp
  rw [h1, Finset.prod_congr rfl (fun a _ => h2 a), ← Polynomial.map_prod, ← Polynomial.map_sub, Polynomial.coeff_map]
  rfl
/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
private theorem map_sh_triple_prod_apply_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : Fin 3 → GQ l) (i j : Fin 3) : f ((D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j) = (D.sh (push f r) 0 (s 0) * D.sh (push f r) 1 (s 1) * D.sh (push f r) 2 (s 2)) i j := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [sh_push_eq_sh_map, h, Matrix.map_apply]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_map_algHom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  intro l _ O _ _ _ D C C' _ _ _ _ f r
  refine ⟨?_, fun a => map_dd_eq_dd_push D f r a, ?_⟩
  · simp only [Dat3.ordIdeal]
    rw [Ideal.map_span, Set.image_union]
    congr 2
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
        exact ⟨s, hs, i, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
      · rintro ⟨s, hs, i, rfl⟩
        exact ⟨_, ⟨s, hs, i, rfl⟩, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
        exact ⟨s, hs, i, j, map_sh_triple_prod_apply_eq_push D f r s i j⟩
      · rintro ⟨s, hs, i, j, rfl⟩
        exact ⟨_, ⟨s, hs, i, j, rfl⟩, map_sh_triple_prod_apply_eq_push D f r s i j⟩
  · simp only [Dat3.del, map_mul, map_natCast, map_dd_eq_dd_push]
