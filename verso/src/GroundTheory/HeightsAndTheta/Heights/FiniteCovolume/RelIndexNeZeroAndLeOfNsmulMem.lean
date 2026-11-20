import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsIntegralVecCoordsOfMemAdelicLatticeOne

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

section Index

/- English proof (translation)
Use `haveI : Module.Finite ℤ P.toIntSubmodule := Module.Finite.of_injective (Submodule.inclusion hPQ) (Submodule.inclusion_injective hPQ)`. Establish `key` using `AddSubgroup.relIndex_map_nsmul n P`. Establish `hle : P.map (nsmulAddMonoidHom (α` using `W) n) ≤ L := by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hnL y hy`.

Establish `hne : (P.map (nsmulAddMonoidHom (α` using `W) n)).relIndex P ≠ 0 := by`. Rewrite using `[key]`. Conclude with `pow_ne_zero _ hn`. Establish `hrank : finrank ℤ P.toIntSubmodule ≤ finrank ℤ Q` using `Submodule.finrank_mono hPQ`. Use `⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hle h0), ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIndex_ne_zero_and_le_of_nsmul_mem {W : Type*} [AddCommGroup W]
    [Module.IsTorsionFree ℤ W] {L P : AddSubgroup W} {Q : Submodule ℤ W} [Module.Finite ℤ Q]
    (hLP : L ≤ P) (hPQ : P.toIntSubmodule ≤ Q) {n : ℕ} (hn : n ≠ 0) (hnL : ∀ y ∈ P, n • y ∈ L) :
    L.relIndex P ≠ 0 ∧ L.relIndex P ≤ n ^ finrank ℤ Q := by
  haveI : Module.Finite ℤ P.toIntSubmodule :=
    Module.Finite.of_injective (Submodule.inclusion hPQ) (Submodule.inclusion_injective hPQ)
  have key := AddSubgroup.relIndex_map_nsmul n P
  have hle : P.map (nsmulAddMonoidHom (α := W) n) ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnL y hy
  have hne : (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hn
  have hrank : finrank ℤ P.toIntSubmodule ≤ finrank ℤ Q := Submodule.finrank_mono hPQ
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hle h0), ?_⟩
  calc L.relIndex P ≤ (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P :=
        AddSubgroup.relIndex_le_of_le_left hle hne
    _ = n ^ finrank ℤ P.toIntSubmodule := key
    _ ≤ n ^ finrank ℤ Q := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hrank

end Index

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Coordinates

variable (F) in

def coordEquiv (v : Basis ι E W) : W ≃+ (ι → F ⊗[F] E) :=
  v.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (Algebra.TensorProduct.lid F E).symm.toAddEquiv)

/- English proof (translation)
Simplify using `[coordEquiv, Algebra.TensorProduct.lid_symm_apply]`.
-/
theorem coordEquiv_apply (v : Basis ι E W) (x : W) (i : ι) :
    coordEquiv F v x i = (1 : F) ⊗ₜ[F] v.repr x i := by
  simp [coordEquiv, Algebra.TensorProduct.lid_symm_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [coordEquiv_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_smul, Finsupp.smul_apply]`.
-/
theorem coordEquiv_smul (v : Basis ι E W) (e : E) (x : W) :
    coordEquiv F v (e • x) = ((1 : F) ⊗ₜ[F] e) • coordEquiv F v x := by
  funext i
  simp only [coordEquiv_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, map_smul, Finsupp.smul_apply]

/- English proof (translation)
Rewrite using `[sesq_eq_sum h.toSesq v x y, pairE, hermPair]`. Simplify using `only [dotProduct, mulVec, baseMatrix, Matrix.map_apply, coordEquiv_apply, conjBase_tmul, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Finset.mul_sum, ← TensorProduct.tmul_sum, Algebra.TensorProduct.lid_tmul, one_smul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairE_coordEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x y : W) :
    pairE (gram h.toSesq v) (coordEquiv F v x) (coordEquiv F v y) = h.toSesq x y := by
  rw [sesq_eq_sum h.toSesq v x y, pairE, hermPair]
  simp only [dotProduct, mulVec, baseMatrix, Matrix.map_apply, coordEquiv_apply, conjBase_tmul,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Finset.mul_sum, ← TensorProduct.tmul_sum, Algebra.TensorProduct.lid_tmul, one_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[vecCoords, coordEquiv_apply, repr_one_tmul, Algebra.algebraMap_self, RingHom.id_apply]`.
-/
theorem vecCoords_coordEquiv {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W) (x : W)
    (i : ι) (k : κ) : vecCoords F b (coordEquiv F v x) (i, k) = b.repr (v.repr x i) k := by
  rw [vecCoords, coordEquiv_apply, repr_one_tmul, Algebra.algebraMap_self, RingHom.id_apply]

end Coordinates

section Equivariance

variable (h : HermitianForm F E W) (v : Basis ι E W)

/- English proof (translation)
Use `set γ' := (unitaryPointsRationalEquivHermitian F E h v).symm γ`. Establish `h1 : unitaryPointsRationalEquiv F E (gram h.toSesq v) γ' = unitaryGroupEquivMatrix h v γ` using `by show unitaryPointsRationalEquiv F E _ (((unitaryPointsRationalEquiv F E _).trans (unitaryGroupEquivMatrix h v).symm).symm γ) = _`. Rewrite using `[MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]`. Establish `hM : (unitaryMat γ').map (Algebra.TensorProduct.lid F E) = LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)`. Rewrite using `[← unitaryGroupEquivMatrix_apply, ← h1]`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Apply `(Algebra.TensorProduct.lid F E).injective` to reduce the goal to its premises. Rewrite using `[coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul, show v.repr ((γ : W ≃ₗ[E] W) y) = v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) y) from rfl, ← LinearMap.toMatrix_mulVec_repr v v, ← hM]`. Simplify using `only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul]`.
-/
theorem mulVec_coordEquiv (γ : h.unitaryGroup) (y : W) :
    unitaryMat ((unitaryPointsRationalEquivHermitian F E h v).symm γ) *ᵥ coordEquiv F v y =
      coordEquiv F v ((γ : W ≃ₗ[E] W) y) := by
  set γ' := (unitaryPointsRationalEquivHermitian F E h v).symm γ
  have h1 : unitaryPointsRationalEquiv F E (gram h.toSesq v) γ' = unitaryGroupEquivMatrix h v γ := by
    show unitaryPointsRationalEquiv F E _ (((unitaryPointsRationalEquiv F E _).trans
      (unitaryGroupEquivMatrix h v).symm).symm γ) = _
    rw [MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  have hM : (unitaryMat γ').map (Algebra.TensorProduct.lid F E) =
      LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [← unitaryGroupEquivMatrix_apply, ← h1]
    rfl
  funext i
  apply (Algebra.TensorProduct.lid F E).injective
  rw [coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul,
    show v.repr ((γ : W ≃ₗ[E] W) y) = v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) y) from rfl,
    ← LinearMap.toMatrix_mulVec_repr v v, ← hM]
  simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, coordEquiv_apply,
    Algebra.TensorProduct.lid_tmul, one_smul]

variable [IsTotallyReal F] [IsTotallyComplex E]

/- English proof (translation)
Apply `unitaryCoords_injective _ _ (Module.finBasis F E)` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Simplify using `[adeleSplit, unitaryCongr_apply, hermitianDiagonal, unitaryDiagonal, finDiag, unitaryCoords_unitaryMap, adeleRingEquivProd]`. Use `erw [unitaryCongr_apply, unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]`. Both sides reduce to the same expression.
-/
theorem adeleSplit_snd_hermitianDiagonal (γ : h.unitaryGroup) :
    (adeleSplit h v (hermitianDiagonal h v γ)).2 =
      finDiag (gram h.toSesq v) ((unitaryPointsRationalEquivHermitian F E h v).symm γ) := by
  apply unitaryCoords_injective _ _ (Module.finBasis F E)
  funext p
  simp [adeleSplit, unitaryCongr_apply, hermitianDiagonal, unitaryDiagonal, finDiag,
    unitaryCoords_unitaryMap, adeleRingEquivProd]
  erw [unitaryCongr_apply, unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
  rfl

end Equivariance

section Lattice

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

def dictLattice (d : ℤ) (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) : AddSubgroup W :=
  (coreLattice b (gram h.toSesq v) g).comap
    ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp (DistribMulAction.toAddMonoidHom W ((d : E)⁻¹)))

variable {b h v}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dictLattice {d : ℤ} {g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} {x : W} :
    x ∈ dictLattice b h v d g ↔ coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[← coreLattice_eq_iff b]`. Establish `hsurj : Function.Surjective ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp (DistribMulAction.toAddMonoidHom W ((d : E)⁻¹)))`. Introduce `X`. Use `⟨(d : E) • (coordEquiv F v).symm X, ?_⟩` and prove the remaining obligations. Use `show coordEquiv F v ((d : E)⁻¹ • ((d : E) • (coordEquiv F v).symm X)) = X`.

Rewrite using `[inv_smul_smul₀ (by exact_mod_cast hd), AddEquiv.apply_symm_apply]`. Conclude with `(AddSubgroup.comap_injective hsurj).eq_iff`.
-/
theorem dictLattice_eq_iff {d : ℤ} (hd : d ≠ 0) {g g' : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} :
    dictLattice b h v d g = dictLattice b h v d g' ↔ g⁻¹ * g' ∈ coreStabilizer b (gram h.toSesq v) := by
  rw [← coreLattice_eq_iff b]
  have hsurj : Function.Surjective ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp
      (DistribMulAction.toAddMonoidHom W ((d : E)⁻¹))) := by
    intro X
    refine ⟨(d : E) • (coordEquiv F v).symm X, ?_⟩
    show coordEquiv F v ((d : E)⁻¹ • ((d : E) • (coordEquiv F v).symm X)) = X
    rw [inv_smul_smul₀ (by exact_mod_cast hd), AddEquiv.apply_symm_apply]
  exact (AddSubgroup.comap_injective hsurj).eq_iff

/- English proof (translation)
Conclude with `AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem`.
-/
theorem mem_smul_addSubgroup_iff (γ : h.unitaryGroup) (S : AddSubgroup W) (x : W) :
    x ∈ γ • S ↔ γ⁻¹ • x ∈ S := by
  exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem

variable [IsTotallyReal F] [IsTotallyComplex E]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_smul_addSubgroup_iff, mem_dictLattice, mem_dictLattice, adeleSplit_snd_hermitianDiagonal, ← mulVec_mem_coreLattice_iff b ((unitaryPointsRationalEquivHermitian F E h v).symm γ) g, mulVec_coordEquiv]`. Establish `: ((γ : W ≃ₗ[E] W) ((d : E)⁻¹ • (γ⁻¹ • x))) = (d : E)⁻¹ • x`. Rewrite using `[map_smul]`. Use `congr 1`.

Use `show (γ : W ≃ₗ[E] W) (((γ⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) x) = x`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `LinearEquiv.apply_symm_apply _ x`. Rewrite using `[this]`.
-/
theorem dictLattice_diagonal_mul (d : ℤ) (γ : h.unitaryGroup)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    dictLattice b h v d ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • dictLattice b h v d g := by
  ext x
  rw [mem_smul_addSubgroup_iff, mem_dictLattice, mem_dictLattice, adeleSplit_snd_hermitianDiagonal,
    ← mulVec_mem_coreLattice_iff b ((unitaryPointsRationalEquivHermitian F E h v).symm γ) g,
    mulVec_coordEquiv]
  have : ((γ : W ≃ₗ[E] W) ((d : E)⁻¹ • (γ⁻¹ • x))) = (d : E)⁻¹ • x := by
    rw [map_smul]
    congr 1
    show (γ : W ≃ₗ[E] W) (((γ⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) x) = x
    rw [Subgroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ x
  rw [this]

end Lattice

end GroundTheory.Heights₂.Heights.FiniteCovolume
