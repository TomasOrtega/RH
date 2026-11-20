import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n H hH hH' hd R _ _ K _ _ ψ β x t hx`. Set `L` to `K ⊗[↥(maximalRealSubfield E)] E`. Use `letI : Algebra ℚ L := ((algebraMap K L).comp (ψ.comp (algebraMap ℚ R))).toAlgebra`. Set `s : R →+* L` to `(algebraMap K L).comp ψ`. Set `e : E →+* L` to `Algebra.TensorProduct.includeRight.toRingHom`.

Set `f : R →ₐ[ℚ] Matrix (Fin n) (Fin n) L` to `((algebraMap L (Matrix (Fin n) (Fin n) L)).comp s).toRatAlgHom`. Set `g : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) L` to `(e.mapMatrix).toRatAlgHom`. Establish `hfg : ∀ a b, Commute (f a) (g b)` using `fun a b => Algebra.commutes (s a) (g b)`. Set `φ` to `Algebra.TensorProduct.lift f g hfg`. Establish `hφ : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), φ (r ⊗ₜ m) = s r • m.map e`.

Introduce `r m`. Use `show f r * g m = _`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Set `c` to `GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K`.

Establish `hc1 : ∀ y : E, c (e y) = e (cj E y)`. Introduce `y`. Simplify using `[c, e, GlobalTheory.HermGlobal.baseConj]`. Establish `hc2 : ∀ r : R, c (s r) = s r`. Introduce `r`.

Use `show c (ψ r ⊗ₜ 1) = ψ r ⊗ₜ 1`. Simplify using `[c, GlobalTheory.HermGlobal.baseConj]`. Establish `hHu : IsUnit H.det` using `isUnit_iff_ne_zero.mpr hd`. Establish `hinv : (H.map e)⁻¹ = H⁻¹.map e`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]`. Establish `hright : H.map e * H⁻¹.map e = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]`. Establish `hmap : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), (s r • m.map e).map c = s r • (m.map (cj E)).map e`. Introduce `r m`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc1, hc2]`. Establish `hH2 : H.map ⇑(↑(IsCMField.complexConj E) : E →+* E) = H` using `hH'`. Establish `hstar : ∀ y, φ (MulOpposite.unop ((starT (hermStar H hd) R) y)) = H⁻¹.map e * ((φ y).map c)ᵀ * H.map e`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r m`. Rewrite using `[starT_tmul, hermStar_apply, hφ, hφ, hmap, hH2, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]`. Consider the case `add a b ha hb`.

Simplify using `only [map_add, MulOpposite.unop_add, ha, hb]`. Rewrite using `[Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]`. Use `⟨φ x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit.map φ)`. Establish `key` using `congrArg φ hx`.

Rewrite `key` using `[map_mul, map_mul, hstar, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hφ, hφ, map_one, one_smul, Matrix.map_one _ (map_zero e) (map_one e)]`. Use `show φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ = ψ t • H⁻¹.map e`. Establish `hsm : ψ t • H⁻¹.map e = s t • H⁻¹.map e` using `(algebraMap_smul L (ψ t) _).symm`. Rewrite using `[hsm]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc, hright, Matrix.mul_one]`. Use `_ = s t • H⁻¹.map e := by`. Rewrite using `[key, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem UpperTheory.Gal.G1.pTrivMat :
    TrivMat := by
  intro E _ _ _ n H hH hH' hd R _ _ K _ _ ψ β x t hx
  let L := K ⊗[↥(maximalRealSubfield E)] E
  letI : Algebra ℚ L := ((algebraMap K L).comp (ψ.comp (algebraMap ℚ R))).toAlgebra
  let s : R →+* L := (algebraMap K L).comp ψ
  let e : E →+* L := Algebra.TensorProduct.includeRight.toRingHom
  let f : R →ₐ[ℚ] Matrix (Fin n) (Fin n) L := ((algebraMap L (Matrix (Fin n) (Fin n) L)).comp s).toRatAlgHom
  let g : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) L := (e.mapMatrix).toRatAlgHom
  have hfg : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes (s a) (g b)
  let φ := Algebra.TensorProduct.lift f g hfg
  have hφ : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), φ (r ⊗ₜ m) = s r • m.map e := by
    intro r m
    show f r * g m = _
    rw [Algebra.smul_def]
    rfl
  let c := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  have hc1 : ∀ y : E, c (e y) = e (cj E y) := by
    intro y
    simp [c, e, GlobalTheory.HermGlobal.baseConj]
  have hc2 : ∀ r : R, c (s r) = s r := by
    intro r
    show c (ψ r ⊗ₜ 1) = ψ r ⊗ₜ 1
    simp [c, GlobalTheory.HermGlobal.baseConj]
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  have hinv : (H.map e)⁻¹ = H⁻¹.map e := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hright : H.map e * H⁻¹.map e = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hmap : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E),
      (s r • m.map e).map c = s r • (m.map (cj E)).map e := by
    intro r m
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc1, hc2]
  have hH2 : H.map ⇑(↑(IsCMField.complexConj E) : E →+* E) = H := hH'
  have hstar : ∀ y, φ (MulOpposite.unop ((starT (hermStar H hd) R) y)) =
      H⁻¹.map e * ((φ y).map c)ᵀ * H.map e := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [starT_tmul, hermStar_apply, hφ, hφ, hmap, hH2, Matrix.map_mul, Matrix.map_mul,
        Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
    | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, ha, hb]
      rw [Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  refine ⟨φ x, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit.map φ)
  · have key := congrArg φ hx
    rw [map_mul, map_mul, hstar, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, hφ, hφ, map_one, one_smul, Matrix.map_one _ (map_zero e) (map_one e)] at key
    show φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ = ψ t • H⁻¹.map e
    have hsm : ψ t • H⁻¹.map e = s t • H⁻¹.map e := (algebraMap_smul L (ψ t) _).symm
    rw [hsm]
    calc φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ
        = φ x * β.map e * (H⁻¹.map e * ((φ x).map c)ᵀ * H.map e) * H⁻¹.map e := by
          rw [Matrix.map_mul]
          simp only [Matrix.mul_assoc, hright, Matrix.mul_one]
      _ = s t • H⁻¹.map e := by
          rw [key, Matrix.smul_mul, Matrix.one_mul]
