import Mathlib
import GroundTheory.AutomorphicForms.UnitaryGroupScheme

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable (F : Type*) [Field F]

instance isQuadraticExtension_prod : Algebra.IsQuadraticExtension F (F × F) where
  finrank_eq_two' := by rw [Module.finrank_prod, Module.finrank_self]

variable {F}

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (Basis.finTwoProd F), Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Basis.finTwoProd_zero, Basis.finTwoProd_one, Basis.coe_finTwoProd_repr, Basis.coe_finTwoProd_repr]`. Simplify using the standard rewrite rules.
-/
theorem trace_prod (x : F × F) : Algebra.trace F (F × F) x = x.1 + x.2 := by
  rw [Algebra.trace_eq_matrix_trace (Basis.finTwoProd F), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, Basis.coe_finTwoProd_repr, Basis.coe_finTwoProd_repr]
  simp

/- English proof (translation)
Rewrite using `[conj_apply, trace_prod]`. Apply the tactic sequence `ext <;> simp`.
-/
theorem conj_prod (x : F × F) : conj F (F × F) x = (x.2, x.1) := by
  rw [conj_apply, trace_prod]
  ext <;> simp

section Split

variable (F) (R : Type*) [CommRing R] [Algebra F R]

noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))

variable {F R}

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitEquiv_tmul (r : R) (x : F × F) : splitEquiv F R (r ⊗ₜ x) = (x.1 • r, x.2 • r) := rfl

variable (F R) in

noncomputable def splitFst : R ⊗[F] (F × F) →+* R :=
  (RingHom.fst R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)

variable (F R) in

noncomputable def splitSnd : R ⊗[F] (F × F) →+* R :=
  (RingHom.snd R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitFst_apply (z : R ⊗[F] (F × F)) : splitFst F R z = (splitEquiv F R z).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitSnd_apply (z : R ⊗[F] (F × F)) : splitSnd F R z = (splitEquiv F R z).2 := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x => simp [conj_prod]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Prod.swap_add]`.
-/
theorem splitEquiv_conjBase (z : R ⊗[F] (F × F)) :
    splitEquiv F R (conjBase F (F × F) R z) = (splitEquiv F R z).swap := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [conj_prod]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Prod.swap_add]

/- English proof (translation)
Rewrite using `[splitFst_apply, splitEquiv_conjBase]`. Both sides reduce to the same expression.
-/
theorem splitFst_conjBase (z : R ⊗[F] (F × F)) :
    splitFst F R (conjBase F (F × F) R z) = splitSnd F R z := by
  rw [splitFst_apply, splitEquiv_conjBase]; rfl

/- English proof (translation)
Rewrite using `[splitSnd_apply, splitEquiv_conjBase]`. Both sides reduce to the same expression.
-/
theorem splitSnd_conjBase (z : R ⊗[F] (F × F)) :
    splitSnd F R (conjBase F (F × F) R z) = splitFst F R z := by
  rw [splitSnd_apply, splitEquiv_conjBase]; rfl

/- English proof (translation)
Simplify using `[splitFst_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]`.
-/
theorem splitFst_includeRight (x : F × F) :
    splitFst F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.1 := by
  simp [splitFst_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Simplify using `[splitSnd_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]`.
-/
theorem splitSnd_includeRight (x : F × F) :
    splitSnd F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.2 := by
  simp [splitSnd_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x => simp [splitFst_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem splitFst_tensorMap {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (z : R ⊗[F] (F × F)) : splitFst F S (tensorMap (F × F) f z) = f (splitFst F R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [splitFst_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Apply `(splitEquiv F R).injective` to reduce the goal to its premises. Conclude with `Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)`.
-/
theorem split_matrix_ext {X Y : Matrix ι ι (R ⊗[F] (F × F))}
    (h1 : X.map (splitFst F R) = Y.map (splitFst F R)) (h2 : X.map (splitSnd F R) = Y.map (splitSnd F R)) :
    X = Y := by
  ext i j
  apply (splitEquiv F R).injective
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `hc : (φ : A → B) ∘ s = ψ` using `funext hs`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hc]`.
-/
theorem map_unitaryExpr_of_comp {A B : Type*} [CommRing A] [CommRing B] [Fintype ι]
    (φ ψ : A →+* B) (s : A →+* A) (hs : ∀ x, φ (s x) = ψ x) (H M : Matrix ι ι A) :
    ((M.map s)ᵀ * H * M).map φ = (M.map ψ)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ s = ψ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hc]

variable (H : Matrix ι ι (F × F))

variable (R) in

noncomputable def splitHom : unitaryPoints F (F × F) H R →* GL ι R :=
  (Matrix.GeneralLinearGroup.map (splitFst F R)).comp (unitaryPoints F (F × F) H R).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitHom_apply (g : unitaryPoints F (F × F) H R) :
    ((splitHom R H g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Conclude with `splitFst_includeRight _`.
-/
theorem map_splitFst_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitFst F R) =
      H.map fun x => algebraMap F R x.1 := by
  ext i j; exact splitFst_includeRight _

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Conclude with `splitSnd_includeRight _`.
-/
theorem map_splitSnd_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitSnd F R) =
      H.map fun x => algebraMap F R x.2 := by
  ext i j; exact splitSnd_includeRight _

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun hH i) j` as an intermediate fact. Simplify using `only [transpose_apply, map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom, conj_prod] at this`. Simplify using `[← this]`.
-/
theorem hermitian_split (hH : IsHermitianFor (conjHom F (F × F)) H) :
    (H.map fun x => algebraMap F R x.2) = (H.map fun x => algebraMap F R x.1)ᵀ := by
  ext i j
  have := congrFun (congrFun hH i) j
  simp only [transpose_apply, map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_toAlgHom, conj_prod] at this
  simp [← this]

/- English proof (translation)
Use `set HR := H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)) with hHR`. Use `set H₁ := H.map fun x => algebraMap F R x.1 with hH₁`. Establish `h21` using `hermitian_split (R := R) H hH`. Establish `hU : IsUnit H` using `(Matrix.isUnit_iff_isUnit_det H).2 hdet`. Establish `hU₁ : IsUnit H₁` using `hU.map (RingHom.mapMatrix ((algebraMap F R).comp (RingHom.fst F F)))`.

Establish `hUR : IsUnit HR` using `hU.map (RingHom.mapMatrix (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)).toRingHom)`. Establish `hdetR : IsUnit HR.det` using `(Matrix.isUnit_iff_isUnit_det HR).1 hUR`. Establish `hR1 : HR.map (splitFst F R) = H₁` using `map_splitFst_H H`. Establish `hR2 : HR.map (splitSnd F R) = H₁ᵀ` using `(map_splitSnd_H H).trans h21`. Establish `eq₁ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)), ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitFst F R) = (X.map (splitSnd F R))ᵀ * H₁ * X.map (splitFst F R)` using `fun X => by`.

Rewrite using `[map_unitaryExpr_of_comp _ _ _ splitFst_conjBase, hR1]`. Establish `eq₂ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)), ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitSnd F R) = (X.map (splitFst F R))ᵀ * H₁ᵀ * X.map (splitSnd F R)` using `fun X => by`. Rewrite using `[map_unitaryExpr_of_comp _ _ _ splitSnd_conjBase, hR2]`. Prove the components needed by the constructor for the conclusion. Introduce `g g' hgg'`.

Establish `h1 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) = ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R)`. Rewrite using `[← splitHom_apply, ← splitHom_apply, hgg']`. Establish `hg` using `congrArg (fun M => M.map (splitFst F R)) (show (((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (conjBase F (F × F) R))ᵀ * HR * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))) = HR from g.2)`. Establish `hg'` using `congrArg (fun M => M.map (splitFst F R)) (show (((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (conjBase F (F × F) R))ᵀ * HR * ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))) = HR from g'.2)`. Simplify using `only [eq₁, hR1] at hg hg'`.

Establish `hunit : IsUnit (H₁ * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R))`. Use `hU₁.mul ?_` and prove the remaining obligations. Rewrite using `[← splitHom_apply]`. Conclude with `Units.isUnit _`. Establish `h2 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) = ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R)`.

Apply `Matrix.transpose_injective` to reduce the goal to its premises. Apply `(hunit.mul_left_inj).1` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc, hg, h1, ← Matrix.mul_assoc, hg']`. Conclude with `Subtype.ext (Units.ext (split_matrix_ext h1 h2))`. Introduce `m set m₁ : Matrix ι ι R := (↑m : Matrix ι ι R) set g₂ : Matrix ι ι R := (H₁ * (↑m⁻¹ : Matrix ι ι R) * H₁⁻¹)ᵀ`.

Set `X : Matrix ι ι (R ⊗[F] (F × F))` to `fun i j => (splitEquiv F R).symm (m₁ i j, g₂ i j)`. Establish `hX1 : X.map (splitFst F R) = m₁`. Use extensionality with `i j`. Use `show splitFst F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = m₁ i j`. Rewrite using `[splitFst_apply, AlgEquiv.apply_symm_apply]`.

Establish `hX2 : X.map (splitSnd F R) = g₂`. Use extensionality with `i j`. Use `show splitSnd F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = g₂ i j`. Rewrite using `[splitSnd_apply, AlgEquiv.apply_symm_apply]`. Establish `hdet₁ : IsUnit H₁.det` using `(Matrix.isUnit_iff_isUnit_det H₁).1 hU₁`.

Establish `key₁ : g₂ᵀ * H₁ * m₁ = H₁`. Simplify using `only [g₂, transpose_transpose]`. Rewrite using `[Matrix.mul_assoc (H₁ * _), Matrix.nonsing_inv_mul _ hdet₁, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Establish `hXeq : (X.map (conjBase F (F × F) R))ᵀ * HR * X = HR`. Apply `split_matrix_ext` to reduce the goal to its premises.

Rewrite using `[eq₁, hR1, hX1, hX2, key₁]`. Rewrite using `[eq₂, hR2, hX1, hX2] conv_rhs => rw [← key₁]`. Rewrite using `[transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]`. Take `⟨u, hu, hux⟩` from `(exists_mem_unitaryGroupMatrix_iff _ hdetR X).2 hXeq`. Use `⟨⟨u, hu⟩, Units.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[splitHom_apply]`. Simplify using `only [hux, hX1, m₁]`.
-/
theorem splitHom_bijective (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det) :
    Function.Bijective (splitHom R H) := by
  set HR := H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)) with hHR
  set H₁ := H.map fun x => algebraMap F R x.1 with hH₁
  have h21 := hermitian_split (R := R) H hH
  have hU : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hU₁ : IsUnit H₁ := hU.map (RingHom.mapMatrix ((algebraMap F R).comp (RingHom.fst F F)))
  have hUR : IsUnit HR := hU.map (RingHom.mapMatrix
    (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)).toRingHom)
  have hdetR : IsUnit HR.det := (Matrix.isUnit_iff_isUnit_det HR).1 hUR
  have hR1 : HR.map (splitFst F R) = H₁ := map_splitFst_H H
  have hR2 : HR.map (splitSnd F R) = H₁ᵀ := (map_splitSnd_H H).trans h21

  have eq₁ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitFst F R) =
        (X.map (splitSnd F R))ᵀ * H₁ * X.map (splitFst F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitFst_conjBase, hR1]
  have eq₂ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitSnd F R) =
        (X.map (splitFst F R))ᵀ * H₁ᵀ * X.map (splitSnd F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitSnd_conjBase, hR2]
  constructor
  · intro g g' hgg'
    have h1 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := by
      rw [← splitHom_apply, ← splitHom_apply, hgg']
    have hg := congrArg (fun M => M.map (splitFst F R))
      (show (((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g.2)
    have hg' := congrArg (fun M => M.map (splitFst F R))
      (show (((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g'.2)
    simp only [eq₁, hR1] at hg hg'
    have hunit : IsUnit (H₁ * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R)) := by
      refine hU₁.mul ?_
      rw [← splitHom_apply]
      exact Units.isUnit _
    have h2 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) := by
      apply Matrix.transpose_injective
      apply (hunit.mul_left_inj).1
      rw [← Matrix.mul_assoc, hg, h1, ← Matrix.mul_assoc, hg']
    exact Subtype.ext (Units.ext (split_matrix_ext h1 h2))
  · intro m
    set m₁ : Matrix ι ι R := (↑m : Matrix ι ι R)
    set g₂ : Matrix ι ι R := (H₁ * (↑m⁻¹ : Matrix ι ι R) * H₁⁻¹)ᵀ
    let X : Matrix ι ι (R ⊗[F] (F × F)) := fun i j => (splitEquiv F R).symm (m₁ i j, g₂ i j)
    have hX1 : X.map (splitFst F R) = m₁ := by
      ext i j
      show splitFst F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = m₁ i j
      rw [splitFst_apply, AlgEquiv.apply_symm_apply]
    have hX2 : X.map (splitSnd F R) = g₂ := by
      ext i j
      show splitSnd F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = g₂ i j
      rw [splitSnd_apply, AlgEquiv.apply_symm_apply]
    have hdet₁ : IsUnit H₁.det := (Matrix.isUnit_iff_isUnit_det H₁).1 hU₁
    have key₁ : g₂ᵀ * H₁ * m₁ = H₁ := by
      simp only [g₂, transpose_transpose]
      rw [Matrix.mul_assoc (H₁ * _), Matrix.nonsing_inv_mul _ hdet₁, Matrix.mul_one,
        Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    have hXeq : (X.map (conjBase F (F × F) R))ᵀ * HR * X = HR := by
      apply split_matrix_ext
      · rw [eq₁, hR1, hX1, hX2, key₁]
      · rw [eq₂, hR2, hX1, hX2]
        conv_rhs => rw [← key₁]
        rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    obtain ⟨u, hu, hux⟩ := (exists_mem_unitaryGroupMatrix_iff _ hdetR X).2 hXeq
    refine ⟨⟨u, hu⟩, Units.ext ?_⟩
    rw [splitHom_apply]
    simp only [hux, hX1, m₁]

variable (R) in

noncomputable def unitaryPointsSplitEquiv (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) : unitaryPoints F (F × F) H R ≃* GL ι R :=
  MulEquiv.ofBijective (splitHom R H) (splitHom_bijective H hH hdet)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitaryPointsSplitEquiv_apply (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) (g : unitaryPoints F (F × F) H R) :
    ((unitaryPointsSplitEquiv R H hH hdet g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[unitaryPointsSplitEquiv_apply, unitaryMap_apply]`. Use extensionality with `i j`. Simplify using `[unitaryPointsSplitEquiv_apply, Matrix.GeneralLinearGroup.map, splitFst_tensorMap]`.
-/
theorem unitaryPointsSplitEquiv_natural {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det)
    (g : unitaryPoints F (F × F) H R) :
    unitaryPointsSplitEquiv S H hH hdet (unitaryMap F (F × F) H f g) =
      Matrix.GeneralLinearGroup.map (f : R →+* S) (unitaryPointsSplitEquiv R H hH hdet g) := by
  apply Units.ext
  rw [unitaryPointsSplitEquiv_apply, unitaryMap_apply]
  ext i j
  simp [unitaryPointsSplitEquiv_apply, Matrix.GeneralLinearGroup.map, splitFst_tensorMap]

end Split

section SplitFunctor

open CategoryTheory

universe u

variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]

noncomputable def generalLinearFunctor : CommAlgCat.{u} F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (GL ι R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map (f.hom : _ →+* _))
  map_id R := by
    rw [CommAlgCat.hom_id]
    exact congrArg GrpCat.ofHom Matrix.GeneralLinearGroup.map_id
  map_comp f g := by
    rw [CommAlgCat.hom_comp]
    exact congrArg GrpCat.ofHom (Matrix.GeneralLinearGroup.map_comp _ _)

variable {F ι}

noncomputable def unitaryFunctorSplitIso (H : Matrix ι ι (F × F))
    (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det) :
    unitaryFunctor F (F × F) H ≅ generalLinearFunctor F ι :=
  NatIso.ofComponents (fun R => (unitaryPointsSplitEquiv R H hH hdet).toGrpIso) fun {R S} f => by
    ext g : 2
    exact unitaryPointsSplitEquiv_natural H f.hom hH hdet g

end SplitFunctor

end GroundTheory.Automorphic
