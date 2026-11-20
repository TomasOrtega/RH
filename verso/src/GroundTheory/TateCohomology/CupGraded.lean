import Mathlib
import GroundTheory.TateCohomology.CupProduct
import GroundTheory.TateCohomology.CochainReverse
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem braiding_hom_tmul (X Y : Rep k G) (a : X) (b : Y) :
    (β_ X Y).hom.hom ((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G))) = b ⊗ₜ[k] a :=
  rfl

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem revCochain_cupCochain (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by
  subst h'
  have hpre : (fun i : Fin p => revInv x ⟨i, by omega⟩) =
      revInv (fun j : Fin p => x ⟨q + j, by omega⟩) := by
    funext i
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hsuf : (fun j : Fin q => revInv x ⟨p + j, by omega⟩) =
      revInv (fun i : Fin q => x ⟨i, by omega⟩) := by
    funext j
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hP₁ : Fin.partialProd (revInv x) ⟨p, by omega⟩ =
      (Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p))⁻¹ := by
    rw [← partialProd_prefix (revInv x) (m := p) (by omega) le_rfl, hpre, ← partialProd_last_revInv]
    rfl
  have hP : Fin.partialProd x (Fin.last (q + p)) =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) *
        Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p) := by
    have := partialProd_add x (fun j : Fin p => x ⟨q + j, by omega⟩) (p := q) (q := p)
      le_rfl (fun _ => rfl) le_rfl
    rw [← partialProd_prefix x (m := q) (by omega) le_rfl] at this
    exact this
  have hP₂ : Fin.partialProd x ⟨q, by omega⟩ =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) :=
    (partialProd_prefix x (m := q) (by omega) le_rfl).symm
  rw [revCochain_apply, cupCochain_apply, cupCochain_apply, revCochain_apply, revCochain_apply,
    hpre, hsuf, hP₁, hP₂, map_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    map_smul, braiding_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, hP, mul_inv_cancel_right, smul_smul, ← pow_add, ← pow_add,
    triangle_add]
  congr 2
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cupH_eq_neg_one_pow_smul_map_braiding (h : p + q = n) (h' : q + p = n)
    (x : groupCohomology A p) (y : groupCohomology B q) :
    cupH h x y = (-1 : k) ^ (p * q) • map (MonoidHom.id G) (β_ B A).hom n (cupH h' y x) := by
  refine groupCohomology_induction_on x fun z => ?_
  refine groupCohomology_induction_on y fun w => ?_
  have key : HomologicalComplex.cyclesMap (revHom (A ⊗ B)) n (cupCocycles h z w) =
      (-1 : k) ^ (p * q) • cocyclesMap (MonoidHom.id G) (β_ B A).hom n
        (cupCocycles h' (HomologicalComplex.cyclesMap (revHom B) q w)
          (HomologicalComplex.cyclesMap (revHom A) p z)) := by
    refine cocycles_ext ?_
    rw [iCocycles_cyclesMap_revHom, map_smul, iCocycles_cocyclesMap, iCocycles_cupCocycles]
    erw [iCocycles_cupCocycles]
    rw [iCocycles_cyclesMap_revHom, iCocycles_cyclesMap_revHom]
    funext x
    exact revCochain_cupCochain h h' _ _ x
  rw [cupH_π, ← π_cyclesMap_revHom (cupCocycles h z w), key, map_smul, ← map_π_apply]
  erw [← cupH_π]
  rw [π_cyclesMap_revHom, π_cyclesMap_revHom]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem map_braiding_cupH (h : p + q = n) (h' : q + p = n) (x : groupCohomology A p)
    (y : groupCohomology B q) :
    map (MonoidHom.id G) (β_ A B).hom n (cupH h x y) = (-1 : k) ^ (p * q) • cupH h' y x := by
  rw [cupH_eq_neg_one_pow_smul_map_braiding h' h y x, smul_smul, ← pow_add, mul_comm q p,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

end GroundTheory.GroupCoh
