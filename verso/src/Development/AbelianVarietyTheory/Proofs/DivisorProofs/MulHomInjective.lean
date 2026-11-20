import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

def crd (y : B.A) : Fin a → w.adicCompletion E := fun i => e (b.repr y i)

def ofCrd (v : Fin a → w.adicCompletion E) : B.A := b.equivFun.symm fun i => e.symm (v i)

def mulHom : B.A →+* Matrix (Fin a) (Fin a) (w.adicCompletion E) :=
  e.toRingHom.mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

def mulGL : B.Aˣ →* GLw a w := Units.map (mulHom e b).toMonoidHom

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem mulHom_eq (t : B.A) : mulHom e b t = GlobalTheory.TwLat.mulMat e b t := by
  ext i j
  simp [mulHom, GlobalTheory.TwLat.mulMat, Algebra.leftMulMatrix_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem latOf_eq (q : GLw a w) :
    GlobalTheory.TwLat.lat e b q = Submodule.span K.O (Set.range fun j => ofCrd e b fun i => q.val i j) := by
  simp [GlobalTheory.TwLat.lat, ofCrd, Module.Basis.equivFun_symm_apply]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem crd_ofCrd (v : Fin a → w.adicCompletion E) : crd e b (ofCrd e b v) = v := by
  funext i
  simp only [crd, ofCrd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ofCrd_crd (y : B.A) : ofCrd e b (crd e b y) = y := by
  simp [crd, ofCrd]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulHom_apply (t : B.A) (i j : Fin a) : mulHom e b t i j = e (b.repr (t * b j) i) := by
  simp [mulHom, Algebra.leftMulMatrix_eq_repr_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulGL_val (t : B.Aˣ) : (mulGL e b t).val = GlobalTheory.TwLat.mulMat e b t := mulHom_eq e b t

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mulHom_injective : Function.Injective (mulHom e b) := by
  intro x y h
  apply Algebra.leftMulMatrix_injective b
  ext i j
  have := congrFun (congrFun h i) j
  exact e.injective (by simpa [mulHom] using this)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mulGL_injective : Function.Injective (mulGL e b) := by
  intro x y h
  exact Units.ext (mulHom_injective e b (congrArg Units.val h))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem crd_injective : Function.Injective (crd e b) := fun x y h => by
  rw [← ofCrd_crd e b x, h, ofCrd_crd]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem crd_add (y z : B.A) : crd e b (y + z) = crd e b y + crd e b z := by
  funext i; simp [crd]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem crd_smul (c : K.E) (y : B.A) : crd e b (c • y) = e c • crd e b y := by
  funext i; simp [crd]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem crd_mul (t y : B.A) : crd e b (t * y) = mulHom e b t *ᵥ crd e b y := by
  funext i
  simp only [crd, mulHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Algebra.leftMulMatrix_mulVec_repr]
  simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, crd]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem ofCrd_mulVec (t : B.A) (v : Fin a → w.adicCompletion E) :
    ofCrd e b (mulHom e b t *ᵥ v) = t * ofCrd e b v := by
  apply crd_injective e b
  rw [crd_mul, crd_ofCrd, crd_ofCrd]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem col_mul (M N : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (j : Fin a) :
    (fun i => (M * N) i j) = M *ᵥ fun i => N i j := by
  funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.
-/
theorem crd_sum (s : Finset (Fin a)) (f : Fin a → B.A) : crd e b (∑ j ∈ s, f j) = ∑ j ∈ s, crd e b (f j) := by
  induction s using Finset.induction_on with
  | empty => funext i; simp [crd]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, crd_add, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem latOf_mul (t : B.Aˣ) (q : GLw a w) :
    GlobalTheory.TwLat.lat e b (mulGL e b t * q) = GlobalTheory.UnitLemma.mulLat K.O (t : B.A) (GlobalTheory.TwLat.lat e b q) := by
  rw [latOf_eq, latOf_eq]
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span K.O) (congrArg Set.range (funext fun j => ?_))
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, Units.val_mul]
  change (ofCrd e b fun i => (mulHom e b (t : B.A) * q.val) i j) = _
  rw [col_mul (mulHom e b (t : B.A)) q.val j, ofCrd_mulVec]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem latOf_isLat (q : GLw a w) : GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b q) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [latOf_eq, Submodule.span_span_of_tower, eq_top_iff]
  intro z _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b z) j), ?_⟩
  apply crd_injective e b
  rw [crd_sum]
  have h1 : crd e b z = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_rhs => rw [h1]
  funext i
  simp [crd_smul, crd_ofCrd, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

end GlobalTheory.TwOrbLat
