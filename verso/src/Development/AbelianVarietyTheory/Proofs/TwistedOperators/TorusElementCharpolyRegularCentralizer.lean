import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.GamAlg

section Base

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem tmul_smul_tmul (a : k) (e : E) (c : k) (y : Fld P) :
    (a ⊗ₜ[F] e) • (c ⊗ₜ[F] y) = (a * c) ⊗ₜ[F] (e • y) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, AlgHom.id_apply,
    IsScalarTower.coe_toAlgHom', ← Algebra.smul_def]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem lT_smul (f : Fld P →ₗ[E] E) (a : k ⊗[F] E) (z : k ⊗[F] Fld P) :
    LinearMap.lTensor k (f.restrictScalars F) (a • z) = a * LinearMap.lTensor k (f.restrictScalars F) z := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [add_smul, map_add, ha, hb, add_mul]
  | tmul k1 e1 =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, mul_add]
    | tmul k2 l =>
      rw [tmul_smul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, f.map_smul, smul_eq_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E (Fld P))

def crd (i : ι) : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E := LinearMap.lTensor k ((b.coord i).restrictScalars F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crd_tmul (i : ι) (c : k) (y : Fld P) : crd P k b i (c ⊗ₜ[F] y) = c ⊗ₜ[F] b.repr y i := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem crd_smul (i : ι) (a : k ⊗[F] E) (z : k ⊗[F] Fld P) : crd P k b i (a • z) = a * crd P k b i z :=
  lT_smul P k _ a z

def tEquiv : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (ι → k ⊗[F] E) where
  toFun z i := crd P k b i z
  map_add' z w := funext fun i => map_add _ _ _
  map_smul' a z := funext fun i => lT_smul P k _ a z
  invFun v := ∑ i, v i • ((1 : k) ⊗ₜ[F] b i)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw =>
      simp only [map_add, add_smul, Finset.sum_add_distrib] at hz hw ⊢
      rw [hz, hw]
    | tmul c y =>
      simp only [crd_tmul, tmul_smul_tmul, mul_one]
      rw [← TensorProduct.tmul_sum, b.sum_repr]
  right_inv v := by
    funext j
    simp only [map_sum]
    rw [Finset.sum_eq_single j]
    · rw [crd_smul, crd_tmul]
      simp [← Algebra.TensorProduct.one_def]
    · intro i _ hij
      rw [crd_smul, crd_tmul]
      simp [Finsupp.single_apply, hij]
    · simp

def bb : Module.Basis ι (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Basis.ofEquivFun (tEquiv P k b)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem bb_apply (i : ι) : bb P k b i = (1 : k) ⊗ₜ[F] b i := by
  rw [bb, Module.Basis.coe_ofEquivFun]
  change ∑ j, (Pi.single i (1 : k ⊗[F] E) : ι → k ⊗[F] E) j • ((1 : k) ⊗ₜ[F] b j) = _
  rw [Finset.sum_eq_single i (fun j _ h => by simp [Pi.single_apply, h]) (by simp)]
  simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem bb_repr (z : k ⊗[F] Fld P) (i : ι) : (bb P k b).repr z i = crd P k b i z := by
  simp [bb, tEquiv]

end Base

end GlobalTheory.TrEll.GamAlg

namespace GlobalTheory.TrEll.GamAlg

section Mat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pb : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pb_gen : (pb P).gen = alpha P := AdjoinRoot.powerBasis_gen _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem minpoly_gen : minpoly E (pb P).gen = P.1 := by
  have e := AdjoinRoot.minpoly_powerBasis_gen P.2.2.1.ne_zero
  have m : P.1.leadingCoeff = 1 := P.2.1
  rw [m, inv_one, C_1, mul_one] at e
  exact e

instance free_base : Module.Free (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Free.of_basis (bb P k (pb P).basis)

instance finite_base : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.of_basis (bb P k (pb P).basis)

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem toMatrix_lmul {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E (Fld P)) (y : Fld P) :
    LinearMap.toMatrix (bb P k b) (bb P k b) (Algebra.lmul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] y)) =
      (Algebra.leftMulMatrix b y).map (inclR k) := by
  ext i j
  rw [LinearMap.toMatrix_apply, bb_repr, bb_apply]
  change crd P k b i (((1 : k) ⊗ₜ[F] y) * ((1 : k) ⊗ₜ[F] b j)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem charpoly_lmul :
    (Algebra.lmul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR k) := by
  rw [← LinearMap.charpoly_toMatrix _ (bb P k (pb P).basis), toMatrix_lmul, Matrix.charpoly_map, ← pb_gen,
    charpoly_leftMulMatrix, minpoly_gen]

variable {k} {n : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem toMatrix_conj (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (f : k ⊗[F] Fld P →ₗ[k ⊗[F] E] k ⊗[F] Fld P) :
    LinearMap.toMatrix ((Pi.basisFun (k ⊗[F] E) (Fin n)).map φ.symm) ((Pi.basisFun (k ⊗[F] E) (Fin n)).map φ.symm) f =
      LinearMap.toMatrix' (φ.conj f) := by
  ext i j
  simp [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem charpoly_mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (z : k ⊗[F] Fld P) :
    (mulMat φ z).charpoly = (Algebra.lmul (k ⊗[F] E) (k ⊗[F] Fld P) z).charpoly := by
  rw [← LinearMap.charpoly_toMatrix _ ((Pi.basisFun (k ⊗[F] E) (Fin n)).map φ.symm), toMatrix_conj]
  rfl

variable (k) in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trBase_smul (a : k ⊗[F] E) (z : k ⊗[F] Fld P) : trBase P k (a • z) = a * trBase P k z :=
  lT_smul P k (Algebra.trace E (Fld P)) a z

variable (k) in

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem eq_zero_of_trBase [NumberField E] (z : k ⊗[F] Fld P) (hz : ∀ y, trBase P k (z * y) = 0) : z = 0 := by
  classical
  let b := (pb P).basis
  have hnd := traceForm_nondegenerate E (Fld P)
  let d := (Algebra.traceForm E (Fld P)).dualBasis hnd b
  apply (bb P k b).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  have key : ∀ j, trBase P k ((1 : k) ⊗ₜ[F] (b j * d i)) = if j = i then 1 else 0 := by
    intro j
    have := LinearMap.BilinForm.apply_dualBasis_left hnd b i j
    rw [Algebra.traceForm_apply, mul_comm] at this
    rw [trBase, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]
  have h := hz ((1 : k) ⊗ₜ[F] d i)
  rw [← (bb P k b).sum_repr z, Finset.sum_mul, map_sum] at h
  simp only [smul_mul_assoc, trBase_smul, bb_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, key, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

variable {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem gam_mat {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    (GlobalTheory.AdelicU.matHom k σ J (gam h)).1 = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ ((torUnit (diagH (star' P) (one₁ P) k (alphaRat P))).1) = _
  congr 1
  change ((diagH (star' P) (one₁ P) k (alphaRat P)).1.1).det = _
  rw [Matrix.det_fin_one]
  first
    | (simp only [diagH, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Formalism.UG.bc, Units.coe_map, alphaRat, Matrix.GeneralLinearGroup.scalar]; simp; done)
    | rfl
    | (simp [diagH, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU, Formalism.UG.bc, alphaRat, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]; done)

end Mat

end GlobalTheory.TrEll.GamAlg

namespace GlobalTheory.TrEll.GamAlg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [CommRing k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def mulAlg (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    k ⊗[F] Fld P →ₐ[k ⊗[F] E] Matrix (Fin n) (Fin n) (k ⊗[F] E) :=
  (LinearMap.toMatrixAlgEquiv' (R := k ⊗[F] E) (n := Fin n)).toAlgHom.comp
    ((φ.conjAlgEquiv (k ⊗[F] E)).toAlgHom.comp (Algebra.lmul (k ⊗[F] E) (k ⊗[F] Fld P)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulAlg_apply (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (z : k ⊗[F] Fld P) :
    mulAlg φ z = mulMat φ z := rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem mulMat_injective (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Function.Injective (mulMat φ) :=
  fun z z' e => by
    have h1 := mulMat_mulVec φ z 1
    have h2 := mulMat_mulVec φ z' 1
    rw [e, h2, mul_one, mul_one] at h1
    exact φ.injective h1.symm

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem tor_comm (t s : Tor P k) : t * s = s * t := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (t.1.1 * s.1.1) i j = (s.1.1 * t.1.1) i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem torUnit_injective : Function.Injective (torUnit (P := P) (k := k)) := fun t s e => by
  have e' : (t.1.1).det = (s.1.1).det := congrArg Units.val e
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at e'
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact e'

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem commute_mulMat {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} {G : Matrix (Fin n) (Fin n) (k ⊗[F] E)}
    (hG : Commute G (mulMat φ ((1 : k) ⊗ₜ[F] alpha P))) (z : k ⊗[F] Fld P) : Commute G (mulMat φ z) := by
  rw [← (bb P k (pb P).basis).sum_repr z, ← mulAlg_apply, map_sum]
  refine Commute.sum_right _ _ _ fun i _ => ?_
  rw [map_smul, bb_apply, PowerBasis.coe_basis, pb_gen, ← one_pow (i : ℕ), ← Algebra.TensorProduct.tmul_pow, map_pow,
    mulAlg_apply]
  exact (hG.pow_right _).smul_right _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem eq_mulMat {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} {G : Matrix (Fin n) (Fin n) (k ⊗[F] E)}
    (hG : Commute G (mulMat φ ((1 : k) ⊗ₜ[F] alpha P))) :
    G = mulMat φ (φ.symm (G *ᵥ φ 1)) := by
  have key : ∀ y, G *ᵥ φ y = φ (φ.symm (G *ᵥ φ 1) * y) := fun y => by
    have e1 : φ y = mulMat φ y *ᵥ φ 1 := by rw [mulMat_mulVec, mul_one]
    rw [e1, Matrix.mulVec_mulVec, (commute_mulMat hG y).eq, ← Matrix.mulVec_mulVec, ← φ.apply_symm_apply (G *ᵥ φ 1),
      mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_comm]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  obtain ⟨y, rfl⟩ := φ.surjective v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, key, mulMat_mulVec]

end Main

end GlobalTheory.TrEll.GamAlg

namespace GlobalTheory.TrEll.GamAlg

section Cent

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [CommRing k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cent_gam [NumberField E] (x : plusUnits P k) {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x.1.1 φ) : cent (gam h) = (torEmb h).range := by
  have hA : (gam h).1.1 = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := gam_mat P h
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have hc : Commute g.1.1 (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)) := by
      rw [← hA]
      first
        | exact (congrArg (fun u : HA k σ J => u.1.1) hg)
        | exact (congrArg (fun u : HA k σ J => u.1.1) hg).symm
    set c := φ.symm (g.1.1 *ᵥ φ 1) with hcdef
    have hG : g.1.1 = mulMat φ c := eq_mulMat hc
    have hu : Formalism.UG.cT (sigR k σ) g.1.1 * JR k J * g.1.1 = JR k J := g.2
    have hn : c * sigR k (star' P) c = 1 := by
      have hz : x.1.1 * (c * sigR k (star' P) c - 1) = 0 := by
        apply eq_zero_of_trBase P k
        intro y
        have e := Formalism.UG.P.hform_mulVec (sigR k σ) (JR k J) g.1.1 (φ 1) (φ y)
        rw [hu] at e
        rw [hG, mulMat_mulVec, mulMat_mulVec] at e
        change Formalism.UG.hform (sigR k σ) (JR k J) (φ (c * 1)) (φ (c * y)) =
          Formalism.UG.hform (sigR k σ) (JR k J) (φ 1) (φ y) at e
        rw [h, h, hx, hx] at e
        rw [show x.1.1 * (c * sigR k (star' P) c - 1) * y =
            x.1.1 * (c * y) * sigR k (star' P) (c * 1) - x.1.1 * y * sigR k (star' P) 1 by
              rw [mul_one, map_one]; ring, map_sub, e, sub_self]
      exact sub_eq_zero.1 ((x.1.isUnit.mul_right_eq_zero).1 hz)
    let u : (k ⊗[F] Fld P)ˣ := ⟨c, sigR k (star' P) c, hn, by rw [mul_comm]; exact hn⟩
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, ?_⟩, ?_⟩
    · change Formalism.UG.cT _ _ * _ * _ = _
      ext i j
      simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, JR, u, mul_comm, hn]
    · apply Subtype.ext
      apply Units.ext
      change mulMat φ (torUnit _).1 = g.1.1
      rw [hG]
      congr 1
      change (Matrix.GeneralLinearGroup.scalar (Fin 1) u).1.det = c
      rw [Matrix.det_fin_one]
      simp [u]
  · rintro ⟨t, rfl⟩
    change torEmb h t * torEmb h _ = torEmb h _ * torEmb h t
    rw [← map_mul, ← map_mul, tor_comm]

end Cent

end GlobalTheory.TrEll.GamAlg

namespace GlobalTheory.TrEll

open GamAlg in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem gam_charpoly_regular_cent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k)
      (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ),
      (GlobalTheory.AdelicU.matHom k σ J (gam h)).1.charpoly = P.1.map (inclR k) ∧
      IsRegSS (GlobalTheory.AdelicU.matHom k σ J (gam h)).1 ∧ Function.Injective (torEmb h) ∧
      cent (gam h) = (torEmb h).range := by
  intro F E _ _ _ _ _ σ _ r n P J _ k _ _ x φ h
  have hcp : (GlobalTheory.AdelicU.matHom k σ J (gam h)).1.charpoly = P.1.map (inclR k) := by
    rw [gam_mat P h, charpoly_mulMat, charpoly_lmul]
  refine ⟨hcp, ?_, ?_, cent_gam x h⟩
  · change Polynomial.Separable _
    rw [hcp]
    exact (Irreducible.separable P.2.2.1).map
  · intro t s e
    apply torUnit_injective
    apply Units.ext
    apply mulMat_injective φ
    exact congrArg (fun u : HA k σ J => u.1.1) e

end GlobalTheory.TrEll
