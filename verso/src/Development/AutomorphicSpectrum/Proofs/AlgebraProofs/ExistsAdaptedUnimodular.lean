import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ToricBasis

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem transpose_mul_mul_apply_eq_dot_product_mul_vec {m n R : Type*} [Fintype m]
    [CommSemiring R] (P : Matrix m n R) (A : Matrix m m R) (x y : n) :
    (Pᵀ * A * P) x y = Pᵀ x ⬝ᵥ A *ᵥ Pᵀ y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Use `haveI : Module.Free ℤ (LinearMap.range f) := Module.free_of_finite_type_torsion_free'`. Take `⟨t, ht⟩` from `LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)`. Establish `hft : ∀ y : LinearMap.range f, f (t y) = y` using `fun y => congrArg Subtype.val (LinearMap.congr_fun ht y)`. Use `⟨LinearMap.range t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`.

Introduce and unpack `x ⟨y, rfl⟩ hy`. Rewrite `hy` using `[LinearMap.mem_ker]`. Establish `hy0 : y = 0` using `Subtype.ext ((hft y).symm.trans hy)`. Rewrite using `[hy0, map_zero]`. Rewrite using `[codisjoint_iff, eq_top_iff]`.

Introduce `x _`. Rewrite using `[Submodule.mem_sup]`. Use `⟨t (f.rangeRestrict x), LinearMap.mem_range_self _ _, x - t (f.rangeRestrict x), ?_, by abel⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hft, sub_eq_zero]`. Both sides reduce to the same expression.
-/
theorem exists_isCompl_ker {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ M : Submodule ℤ (Fin g → ℤ), IsCompl M (LinearMap.ker f) := by
  haveI : Module.Free ℤ (LinearMap.range f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨t, ht⟩ :=
    LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have hft : ∀ y : LinearMap.range f, f (t y) = y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun ht y)
  refine ⟨LinearMap.range t, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : y = 0 := Subtype.ext ((hft y).symm.trans hy)
    rw [hy0, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨t (f.rangeRestrict x), LinearMap.mem_range_self _ _, x - t (f.rangeRestrict x), ?_,
      by abel⟩
    rw [LinearMap.mem_ker, map_sub, hft, sub_eq_zero]
    rfl

/- English proof (translation)
Take `⟨M, hM⟩` from `GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker f`. Use `haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'`. Use `haveI : Module.Free ℤ (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'`. Take `⟨bM⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ M)) ℤ M)` from `⟨Module.finBasis ℤ M⟩`. Take `⟨bK⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ (LinearMap.ker f))) ℤ (LinearMap.ker f))` from `⟨Module.finBasis ℤ (LinearMap.ker f)⟩`.

Establish `hb : ∀ i, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) i = ((bM.prod bK i).1 : Fin g → ℤ) + ((bM.prod bK i).2 : Fin g → ℤ)` using `fun i => by`. Rewrite using `[Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']`. Use `⟨_, _, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM), ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Rewrite using `[hb, Module.Basis.prod_apply]`.

Simplify using `only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, ZeroMemClass.coe_zero, zero_add]`. Conclude with `LinearMap.mem_ker.mp (bK k).2`. Introduce `x hx`. Establish `hinl : ∀ a, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) (Sum.inl a) = (bM a : Fin g → ℤ)` using `fun a => by`. Rewrite using `[hb, Module.Basis.prod_apply]`.

Simplify using `only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, ZeroMemClass.coe_zero, add_zero]`. Simplify using `only [hinl] at hx`. Establish `hmem : (∑ a, x a • (bM a : Fin g → ℤ)) ∈ M` using `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bM a).2`. Establish `h0` using `Submodule.disjoint_def.mp hM.disjoint _ hmem (LinearMap.mem_ker.mpr hx)`. Establish `h0' : ∑ a, x a • bM a = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Simplify `h0` using `only [Submodule.coe_smul, ZeroMemClass.coe_zero]`. Use function extensionality and compare the values at `a`. Conclude with `Fintype.linearIndependent_iff.mp bM.linearIndependent x h0' a`.
-/
theorem exists_adapted_basis {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ (r s : ℕ) (b : Module.Basis (Fin r ⊕ Fin s) ℤ (Fin g → ℤ)),
      (∀ k, f (b (Sum.inr k)) = 0) ∧
      ∀ x : Fin r → ℤ, f (∑ a, x a • b (Sum.inl a)) = 0 → x = 0 := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker f
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨bM⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ M)) ℤ M) :=
    ⟨Module.finBasis ℤ M⟩
  obtain ⟨bK⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ (LinearMap.ker f))) ℤ
      (LinearMap.ker f)) := ⟨Module.finBasis ℤ (LinearMap.ker f)⟩
  have hb : ∀ i, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) i =
      ((bM.prod bK i).1 : Fin g → ℤ) + ((bM.prod bK i).2 : Fin g → ℤ) := fun i => by
    rw [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨_, _, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM), ?_, ?_⟩
  · intro k
    rw [hb, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, ZeroMemClass.coe_zero,
      zero_add]
    exact LinearMap.mem_ker.mp (bK k).2
  · intro x hx
    have hinl : ∀ a, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM)
        (Sum.inl a) = (bM a : Fin g → ℤ) := fun a => by
      rw [hb, Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, ZeroMemClass.coe_zero,
        add_zero]
    simp only [hinl] at hx
    have hmem : (∑ a, x a • (bM a : Fin g → ℤ)) ∈ M :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bM a).2
    have h0 := Submodule.disjoint_def.mp hM.disjoint _ hmem (LinearMap.mem_ker.mpr hx)
    have h0' : ∑ a, x a • bM a = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero] using h0
    funext a
    exact Fintype.linearIndependent_iff.mp bM.linearIndependent x h0' a

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial, Int.cast_sum, Int.cast_mul]`.
-/
theorem cast_quad {g : ℕ} (A : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (v i : ℝ))
      = ((v ⬝ᵥ A *ᵥ v : ℤ) : ℝ) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
    Int.cast_sum, Int.cast_mul]

/- English proof (translation)
Establish `h` using `hA.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))`. Rewrite `h` using `[GlobalTheory.CompanionTheory.ToricBasis.cast_quad]`. Conclude with `h` after adjusting the coercions.
-/
theorem quad_nonneg {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ A *ᵥ v := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad] at h
  exact_mod_cast h

/- English proof (translation)
Establish `h1 : star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (v i : ℝ)) = 0`. Rewrite using `[GlobalTheory.CompanionTheory.ToricBasis.cast_quad, h, Int.cast_zero]`. Establish `h2` using `(hA.dotProduct_mulVec_zero_iff _).mp h1`. Use function extensionality and compare the values at `i`. Establish `h3` using `congrFun h2 i`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h3 ⊢`. Conclude with `h3` after adjusting the coercions.
-/
theorem mulVec_eq_zero_of_quad {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h : v ⬝ᵥ A *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have h1 : star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ
      (fun i => (v i : ℝ)) = 0 := by
    rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad, h, Int.cast_zero]
  have h2 := (hA.dotProduct_mulVec_zero_iff _).mp h1
  funext i
  have h3 := congrFun h2 i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h3 ⊢
  exact_mod_cast h3

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `hA.isHermitian.apply i j`. Simplify using `only [Matrix.map_apply, star_trivial] at h`. Rewrite using `[Matrix.transpose_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem symm_of_posSemidef {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) : Aᵀ = A := by
  ext i j
  have h := hA.isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  rw [Matrix.transpose_apply]
  exact_mod_cast h

/- English proof (translation)
Introduce `g J _ B hB`. Take `⟨S, hSdef⟩ : ∃ S : Matrix (Fin g) (Fin g) ℤ, S = ∑ j, B j` from `⟨_, rfl⟩`. Rewrite using `[← hSdef]`. Establish `hSpsd : (S.map (fun x : ℤ => (x : ℝ))).PosSemidef`. Establish `hmap : S.map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ))`.

Use extensionality with `i i'`. Simplify using `only [hSdef, Matrix.map_apply, Matrix.sum_apply, Int.cast_sum]`. Rewrite using `[hmap]`. Conclude with `Matrix.posSemidef_sum Finset.univ fun j _ => hB j`. Take `⟨r, s, b, hker, hinj⟩` from `GlobalTheory.CompanionTheory.ToricBasis.exists_adapted_basis (Matrix.mulVecLin S)`.

Establish `hcard : g = r + s`. Establish `h` using `Module.finrank_eq_card_basis b`. Rewrite `h` using `[Module.finrank_fin_fun ℤ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Then use the resulting hypothesis. Take `⟨e⟩ : Nonempty (Fin r ⊕ Fin s ≃ Fin g)` from `⟨finSumFinEquiv.trans (finCongr hcard.symm)⟩`. Take `⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin g) (Fin g) ℤ, Q = (Pi.basisFun ℤ (Fin g)).toMatrix (b.reindex e)` from `⟨_, rfl⟩`.

Establish `hQ : ∀ i m, Q i m = b (e.symm m) i`. Introduce `i m`. Rewrite using `[hQdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply]`. Establish `hunit : IsUnit Q.det`. Rewrite using `[hQdef]`.

Use `letI := Module.Basis.invertibleToMatrix (Pi.basisFun ℤ (Fin g)) (b.reindex e)`. Conclude with `Matrix.isUnit_det_of_invertible _`. Establish `hcol : ∀ α, Qᵀ (e α) = b α` using `fun α => funext fun i => by`. Rewrite using `[Matrix.transpose_apply, hQ, e.symm_apply_apply]`. Apply the tactic sequence `have hentry : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (α β : Fin r ⊕ Fin s), ((Qᵀ * X * Q).submatrix e e) α β = b α ⬝ᵥ X *ᵥ b β := by`.

Introduce `X α β`. Rewrite using `[Matrix.submatrix_apply, transpose_mul_mul_apply_eq_dot_product_mul_vec, hcol, hcol]`. Establish `hBk : ∀ j k, B j *ᵥ b (Sum.inr k) = 0`. Introduce `j k`. Establish `hSk : S *ᵥ b (Sum.inr k) = 0`.

Establish `h` using `hker k`. Rewrite `h` using `[Matrix.mulVecLin_apply]`. Then use the resulting hypothesis. Establish `hsum : ∑ i, b (Sum.inr k) ⬝ᵥ B i *ᵥ b (Sum.inr k) = 0`. Rewrite using `[← dotProduct_sum, ← Matrix.sum_mulVec, ← hSdef, hSk, dotProduct_zero]`. Establish `hj` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => GlobalTheory.CompanionTheory.ToricBasis.quad_nonneg (hB i) _)).mp hsum j (Finset.mem_univ _)`.

Conclude with `GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad (hB j) _ hj`. Use `⟨r, s, e, Q, hunit, ?_, ?_⟩` and prove the remaining obligations. Introduce `j k l`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hentry, Matrix.dotProduct_mulVec, ← GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (hB j), Matrix.vecMul_transpose, hBk, zero_dotProduct]`.

Rewrite using `[hentry, hBk, dotProduct_zero]`. Take `⟨C, hC⟩ : ∃ C : Matrix (Fin g) (Fin r) ℤ, ∀ i a, C i a = b (Sum.inl a) i` from `⟨Matrix.of fun i a => b (Sum.inl a) i, fun _ _ => rfl⟩`. Establish `hCt : ∀ a, Cᵀ a = b (Sum.inl a)` using `fun a => funext fun i => by`. Rewrite using `[Matrix.transpose_apply, hC]`. Establish `hMC : ((Qᵀ * S * Q).submatrix e e).toBlocks₁₁ = Cᵀ * S * C`.

Use extensionality with `a a'`. Rewrite using `[transpose_mul_mul_apply_eq_dot_product_mul_vec, hCt, hCt, ← hentry]`. Both sides reduce to the same expression. Rewrite using `[hMC]`. Establish `hN : (Cᵀ * S * C).map (fun x : ℤ => (x : ℝ)) = (C.map (fun x : ℤ => (x : ℝ)))ᴴ * S.map (fun x : ℤ => (x : ℝ)) * C.map (fun x : ℤ => (x : ℝ))`.

Use extensionality with `a a'`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial, Int.cast_sum, Int.cast_mul]`. Establish `hNpsd : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).PosSemidef`. Rewrite using `[hN]`. Conclude with `hSpsd.conjTranspose_mul_mul_same _`.

Use `Matrix.PosDef.of_dotProduct_mulVec_pos hNpsd.isHermitian ?_` and prove the remaining obligations. Introduce `x hx`. Use `lt_of_le_of_ne (hNpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_` and prove the remaining obligations. Establish `hNx` using `(hNpsd.dotProduct_mulVec_zero_iff x).mp h0.symm`. Establish `hdetN : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).det = 0` using `Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hNx⟩`.

Establish `hdetZ : (Cᵀ * S * C).det = 0`. Establish `h1 : (((Cᵀ * S * C).det : ℤ) : ℝ) = 0`. Rewrite using `[← hdetN]`. Establish `h2` using `RingHom.map_det (Int.castRingHom ℝ) (Cᵀ * S * C)`. Rewrite `h2` using `[RingHom.mapMatrix_apply]`.

Conclude with `h2`. Conclude with `h1` after adjusting the coercions. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ`. Establish `hquad : (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) = 0`. Establish `h3 : v ⬝ᵥ (Cᵀ * S * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v)`.

Rewrite using `[← Matrix.mulVec_mulVec v (Cᵀ * S) C, ← Matrix.mulVec_mulVec (C *ᵥ v) Cᵀ S, Matrix.dotProduct_mulVec v Cᵀ, Matrix.vecMul_transpose C v]`. Rewrite using `[← h3, hv0, dotProduct_zero]`. Establish `hSw` using `GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad hSpsd (C *ᵥ v) hquad`. Establish `hCv : C *ᵥ v = ∑ a, v a • b (Sum.inl a)`. Use extensionality with `i`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, hC, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Conclude with `hv (hinj v (by rw [Matrix.mulVecLin_apply, ← hCv]; exact hSw))`.
-/
theorem exists_adapted_unimodular :
    ∀ (g : ℕ) (J : Type) [Fintype J] (B : J → Matrix (Fin g) (Fin g) ℤ), (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin g) (Q : Matrix (Fin g) (Fin g) ℤ), IsUnit Q.det ∧ (∀ j k l, ((Qᵀ * B j * Q).submatrix e e) (Sum.inr k) l = 0 ∧ ((Qᵀ * B j * Q).submatrix e e) l (Sum.inr k) = 0) ∧ ((((Qᵀ * (∑ j, B j) * Q).submatrix e e).toBlocks₁₁).map (fun x : ℤ => (x : ℝ))).PosDef := by
  intro g J _ B hB
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin g) (Fin g) ℤ, S = ∑ j, B j := ⟨_, rfl⟩
  rw [← hSdef]
  have hSpsd : (S.map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    have hmap : S.map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
      ext i i'
      simp only [hSdef, Matrix.map_apply, Matrix.sum_apply, Int.cast_sum]
    rw [hmap]
    exact Matrix.posSemidef_sum Finset.univ fun j _ => hB j
  obtain ⟨r, s, b, hker, hinj⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_adapted_basis (Matrix.mulVecLin S)
  have hcard : g = r + s := by
    have h := Module.finrank_eq_card_basis b
    rwa [Module.finrank_fin_fun ℤ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  obtain ⟨e⟩ : Nonempty (Fin r ⊕ Fin s ≃ Fin g) := ⟨finSumFinEquiv.trans (finCongr hcard.symm)⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin g) (Fin g) ℤ,
      Q = (Pi.basisFun ℤ (Fin g)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : ∀ i m, Q i m = b (e.symm m) i := by
    intro i m
    rw [hQdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply]
  have hunit : IsUnit Q.det := by
    rw [hQdef]
    letI := Module.Basis.invertibleToMatrix (Pi.basisFun ℤ (Fin g)) (b.reindex e)
    exact Matrix.isUnit_det_of_invertible _
  have hcol : ∀ α, Qᵀ (e α) = b α := fun α => funext fun i => by
    rw [Matrix.transpose_apply, hQ, e.symm_apply_apply]
  have hentry : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (α β : Fin r ⊕ Fin s),
      ((Qᵀ * X * Q).submatrix e e) α β = b α ⬝ᵥ X *ᵥ b β := by
    intro X α β
    rw [Matrix.submatrix_apply, transpose_mul_mul_apply_eq_dot_product_mul_vec, hcol, hcol]
  have hBk : ∀ j k, B j *ᵥ b (Sum.inr k) = 0 := by
    intro j k
    have hSk : S *ᵥ b (Sum.inr k) = 0 := by
      have h := hker k
      rwa [Matrix.mulVecLin_apply] at h
    have hsum : ∑ i, b (Sum.inr k) ⬝ᵥ B i *ᵥ b (Sum.inr k) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, ← hSdef, hSk, dotProduct_zero]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      GlobalTheory.CompanionTheory.ToricBasis.quad_nonneg (hB i) _)).mp hsum j
        (Finset.mem_univ _)
    exact GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad (hB j) _ hj
  refine ⟨r, s, e, Q, hunit, ?_, ?_⟩
  · intro j k l
    refine ⟨?_, ?_⟩
    · rw [hentry, Matrix.dotProduct_mulVec,
        ← GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (hB j), Matrix.vecMul_transpose, hBk,
        zero_dotProduct]
    · rw [hentry, hBk, dotProduct_zero]
  · obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin g) (Fin r) ℤ, ∀ i a, C i a = b (Sum.inl a) i :=
      ⟨Matrix.of fun i a => b (Sum.inl a) i, fun _ _ => rfl⟩
    have hCt : ∀ a, Cᵀ a = b (Sum.inl a) := fun a => funext fun i => by
      rw [Matrix.transpose_apply, hC]
    have hMC : ((Qᵀ * S * Q).submatrix e e).toBlocks₁₁ = Cᵀ * S * C := by
      ext a a'
      rw [transpose_mul_mul_apply_eq_dot_product_mul_vec, hCt, hCt, ← hentry]
      rfl
    rw [hMC]
    have hN : (Cᵀ * S * C).map (fun x : ℤ => (x : ℝ)) =
        (C.map (fun x : ℤ => (x : ℝ)))ᴴ * S.map (fun x : ℤ => (x : ℝ)) *
          C.map (fun x : ℤ => (x : ℝ)) := by
      ext a a'
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, star_trivial, Int.cast_sum, Int.cast_mul]
    have hNpsd : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
      rw [hN]
      exact hSpsd.conjTranspose_mul_mul_same _
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hNpsd.isHermitian ?_
    intro x hx
    refine lt_of_le_of_ne (hNpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_
    have hNx := (hNpsd.dotProduct_mulVec_zero_iff x).mp h0.symm
    have hdetN : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hNx⟩
    have hdetZ : (Cᵀ * S * C).det = 0 := by
      have h1 : (((Cᵀ * S * C).det : ℤ) : ℝ) = 0 := by
        rw [← hdetN]
        have h2 := RingHom.map_det (Int.castRingHom ℝ) (Cᵀ * S * C)
        rw [RingHom.mapMatrix_apply] at h2
        exact h2
      exact_mod_cast h1
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
    have hquad : (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) = 0 := by
      have h3 : v ⬝ᵥ (Cᵀ * S * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) := by
        rw [← Matrix.mulVec_mulVec v (Cᵀ * S) C, ← Matrix.mulVec_mulVec (C *ᵥ v) Cᵀ S,
          Matrix.dotProduct_mulVec v Cᵀ, Matrix.vecMul_transpose C v]
      rw [← h3, hv0, dotProduct_zero]
    have hSw := GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad hSpsd
      (C *ᵥ v) hquad
    have hCv : C *ᵥ v = ∑ a, v a • b (Sum.inl a) := by
      ext i
      rw [Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, hC, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    exact hv (hinj v (by rw [Matrix.mulVecLin_apply, ← hCv]; exact hSw))

end GlobalTheory.CompanionTheory.ToricBasis
