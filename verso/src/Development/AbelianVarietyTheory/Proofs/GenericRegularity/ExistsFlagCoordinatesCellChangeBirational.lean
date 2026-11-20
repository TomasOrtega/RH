import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsLowerMulUpperOfLeadingMinors
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.Reg.CellChange

open Matrix

/- English proof (translation)
Establish `htop : IntermediateField.adjoin κ (Set.range y) = ⊤`. Establish `hp : ∀ p : MvPolynomial ι κ, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) p ∈ IntermediateField.adjoin κ (Set.range y)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`.

Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Conclude with `IntermediateField.algebraMap_mem _ a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p v hp => rw [map_mul]`.

Conclude with `mul_mem hp (hy v)`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial ι κ) x`. Conclude with `div_mem (hp a) (hp b)`.

Establish `hX : AlgebraicIndependent κ (fun v : ι => algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v))` using `(MvPolynomial.algebraicIndependent_X ι κ).map' (f := IsScalarTower.toAlgHom κ (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ))) (IsFractionRing.injective _ _)`. Establish `halg : Algebra.IsAlgebraic (Algebra.adjoin κ (Set.range y)) (FractionRing (MvPolynomial ι κ))`. Rewrite using `[← IntermediateField.isAlgebraic_adjoin_iff_top, htop]`. Conclude with `⟨fun x => isAlgebraic_algebraMap (⟨x, trivial⟩ : (⊤ : IntermediateField κ _))⟩`. Establish `hind : AlgebraicIndependent κ y` using `(Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite κ y hX.cardinalMk_le_trdeg).1`.

Establish `hinj : Function.Injective (MvPolynomial.aeval y : MvPolynomial ι κ →ₐ[κ] _)` using `algebraicIndependent_iff_injective_aeval.1 hind`. Set `f : FractionRing (MvPolynomial ι κ) →ₐ[κ] FractionRing (MvPolynomial ι κ)` to `IsFractionRing.liftAlgHom hinj`. Establish `hf : ∀ v, f (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v`. Introduce `v`. Simplify using `[f]`.

Establish `hs : Function.Surjective f`. Establish `: IntermediateField.adjoin κ (Set.range y) ≤ f.fieldRange`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `⟨_, hf v⟩`.

Introduce `x`. Conclude with `this (htop ▸ IntermediateField.mem_top)`. Conclude with `⟨AlgEquiv.ofBijective f ⟨f.injective, hs⟩, hf⟩`.
-/
theorem exists_algEquiv_of_generates {κ ι : Type} [Field κ] [Finite ι] (y : ι → FractionRing (MvPolynomial ι κ))
    (hy : ∀ v, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v) ∈
      IntermediateField.adjoin κ (Set.range y)) :
    ∃ e : FractionRing (MvPolynomial ι κ) ≃ₐ[κ] FractionRing (MvPolynomial ι κ),
      ∀ v, e (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
  have htop : IntermediateField.adjoin κ (Set.range y) = ⊤ := by
    have hp : ∀ p : MvPolynomial ι κ, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) p ∈
        IntermediateField.adjoin κ (Set.range y) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p v hp => rw [map_mul]; exact mul_mem hp (hy v)
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι κ) x
    exact div_mem (hp a) (hp b)
  have hX : AlgebraicIndependent κ (fun v : ι =>
      algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v)) :=
    (MvPolynomial.algebraicIndependent_X ι κ).map'
      (f := IsScalarTower.toAlgHom κ (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)))
      (IsFractionRing.injective _ _)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin κ (Set.range y)) (FractionRing (MvPolynomial ι κ)) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop]
    exact ⟨fun x => isAlgebraic_algebraMap (⟨x, trivial⟩ : (⊤ : IntermediateField κ _))⟩
  have hind : AlgebraicIndependent κ y :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite κ y hX.cardinalMk_le_trdeg).1
  have hinj : Function.Injective (MvPolynomial.aeval y : MvPolynomial ι κ →ₐ[κ] _) :=
    algebraicIndependent_iff_injective_aeval.1 hind
  let f : FractionRing (MvPolynomial ι κ) →ₐ[κ] FractionRing (MvPolynomial ι κ) :=
    IsFractionRing.liftAlgHom hinj
  have hf : ∀ v, f (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
    intro v
    simp [f]
  have hs : Function.Surjective f := by
    have : IntermediateField.adjoin κ (Set.range y) ≤ f.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact ⟨_, hf v⟩
    intro x
    exact this (htop ▸ IntermediateField.mem_top)
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hs⟩, hf⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.cell_coordinates_exists_unique R n n (Function.Embedding.refl _) g).1`.
-/
theorem minors_iff {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    (∀ k (hk : k ≤ n), IsUnit (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) ↔
      ∃ u b : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b :=
  (GlobalTheory.cell_coordinates_exists_unique R n n (Function.Embedding.refl _) g).1

/- English proof (translation)
Establish `hd` using `GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu`. Establish `hbi : b⁻¹.BlockTriangular id`. Set `_` to `Matrix.invertibleOfIsUnitDet b hd`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Use `⟨hbi, fun i => ?_, Matrix.mul_nonsing_inv _ hd⟩` and prove the remaining obligations.

Establish `h1 : IsUnit b⁻¹.det` using `Matrix.isUnit_nonsing_inv_det _ hd`. Rewrite `h1` using `[Matrix.det_of_upperTriangular hbi]`. Conclude with `IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)`.
-/
theorem upper_inv {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) : b⁻¹.BlockTriangular id ∧ (∀ i, IsUnit (b⁻¹ i i)) ∧ b * b⁻¹ = 1 := by
  have hd := GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu
  have hbi : b⁻¹.BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet b hd
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨hbi, fun i => ?_, Matrix.mul_nonsing_inv _ hd⟩
  have h1 : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hd
  rw [Matrix.det_of_upperTriangular hbi] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

/- English proof (translation)
Establish `h1 : IsUnit (b * c).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `(GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu).mul (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag c hc hv)`. Rewrite `h1` using `[Matrix.det_of_upperTriangular (hb.mul hc)]`. Conclude with `IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)`.
-/
theorem upper_mul_diag {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) (hc : c.BlockTriangular id) (hv : ∀ i, IsUnit (c i i)) (i : Fin n) :
    IsUnit ((b * c) i i) := by
  have h1 : IsUnit (b * c).det := by
    rw [Matrix.det_mul]
    exact (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu).mul (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag c hc hv)
  rw [Matrix.det_of_upperTriangular (hb.mul hc)] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

/- English proof (translation)
Establish `hm` using `(minors_iff (M.map φ)).2 ⟨l, b, h0, h1, hb, hu, h⟩`. Take `⟨u, c, hu0, hu1, hc, hcu, hM⟩` from `(minors_iff M).1 (fun k hk => by`. Establish `h2` using `hm k hk`. Rewrite `h2` using `[Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Rewrite `h2`, the goal using `[isUnit_iff_ne_zero]`.

Introduce `h3`. Conclude with `h2 (by rw [h3, map_zero]))`. Use `(GlobalTheory.cell_coordinates_exists_unique K n n (Function.Embedding.refl _) l).2 l (u.map φ) b (c.map φ) ⟨h0, h1⟩ ⟨fun i j hij => by simpa using hu0 i j hij, fun i => by simp [hu1 i]⟩ hb (hc.map φ) hu (by rw [← h, hM, Matrix.map_mul])` as an intermediate fact. Conclude with `⟨u i j, by rw [this.1]; rfl⟩`.
-/
theorem lower_mem_range {F K : Type} [Field F] [Field K] (φ : F →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (l b : Matrix (Fin n) (Fin n) K) (h0 : ∀ i j : Fin n, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (h : M.map φ = l * b) (i j : Fin n) :
    ∃ x, φ x = l i j := by
  have hm := (minors_iff (M.map φ)).2 ⟨l, b, h0, h1, hb, hu, h⟩
  obtain ⟨u, c, hu0, hu1, hc, hcu, hM⟩ := (minors_iff M).1 (fun k hk => by
    have h2 := hm k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [isUnit_iff_ne_zero] at h2 ⊢
    intro h3
    exact h2 (by rw [h3, map_zero]))
  have := (GlobalTheory.cell_coordinates_exists_unique K n n (Function.Embedding.refl _) l).2 l (u.map φ) b (c.map φ)
    ⟨h0, h1⟩ ⟨fun i j hij => by simpa using hu0 i j hij, fun i => by simp [hu1 i]⟩ hb
    (hc.map φ) hu (by rw [← h, hM, Matrix.map_mul])
  exact ⟨u i j, by rw [this.1]; rfl⟩

/- English proof (translation)
Establish `key : ∀ M : Matrix (Fin n) (Fin n) (Polynomial κ), (∀ k (hk : k ≤ n), (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∀ k (hk : k ≤ n), IsUnit ((M.map (algebraMap _ (RatFunc κ))).submatrix (Fin.castLE hk) (Fin.castLE hk)).det`. Introduce `M hM k hk`. Rewrite using `[Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (hM k hk)`. Take `⟨l, b, h0, h1, hb, hu, h⟩` from `(minors_iff _).1 (key (Matrix.charmatrix (-A⁻¹)) (fun k hk => by`.

Establish `: (Matrix.charmatrix (-A⁻¹)).submatrix (Fin.castLE hk) (Fin.castLE hk) = Matrix.charmatrix ((-A⁻¹).submatrix (Fin.castLE hk) (Fin.castLE hk))`. Use extensionality with `i j : 2`. Simplify using `[Matrix.charmatrix_apply, Matrix.diagonal_apply]`. Rewrite using `[this]`. Conclude with `(Matrix.charpoly_monic _).ne_zero))`.

Take `⟨u, c, hu0, hu1, hc, hcu, h'⟩` from `(minors_iff _).1 (key (1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C) (fun k hk h2 => by`. Establish `h3` using `congrArg (Polynomial.evalRingHom (0 : κ)) h2`. Rewrite `h3` using `[RingHom.map_det, map_zero]`. Establish `: (Polynomial.evalRingHom (0 : κ)).mapMatrix ((1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C).submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1`. Use extensionality with `i j`.

Simplify using `[Matrix.one_apply, apply_ite]`. Rewrite `h3` using `[this, Matrix.det_one]`. Conclude with `one_ne_zero h3))`. Take `⟨hbi, hbu, hbb⟩` from `upper_inv b hb hu`. Use `⟨l, h0, h1, (minors_iff _).2 ⟨u, c * b⁻¹, hu0, hu1, hc.mul hbi, upper_mul_diag _ _ hc hcu hbi hbu, ?_⟩⟩` and prove the remaining obligations.

Establish `e1 : A.map Polynomial.C * Matrix.charmatrix (-A⁻¹) = 1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C`. Rewrite using `[Matrix.charmatrix, Matrix.mul_sub, map_neg, Matrix.mul_neg, RingHom.mapMatrix_apply, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, sub_neg_eq_add, add_comm, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `congr 1`. Use extensionality with `i j : 2`. Rewrite using `[Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]`.

Establish `e2 : A.map (algebraMap κ (RatFunc κ)) = (A.map Polynomial.C).map (algebraMap _ (RatFunc κ))`. Use extensionality with `i j`. Conclude with `IsScalarTower.algebraMap_apply κ (Polynomial κ) (RatFunc κ) (A i j)`. Rewrite using `[← Matrix.mul_assoc, ← h', ← e1, Matrix.map_mul, h, ← e2, Matrix.mul_assoc, Matrix.mul_assoc, hbb, Matrix.mul_one]`.
-/
theorem exists_lower_minors {κ : Type} [Field κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) κ) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin n) (Fin n) (RatFunc κ), (∀ i j : Fin n, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      ∀ k (hk : k ≤ n), IsUnit ((A.map (algebraMap κ (RatFunc κ)) * l).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
  have key : ∀ M : Matrix (Fin n) (Fin n) (Polynomial κ),
      (∀ k (hk : k ≤ n), (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      ∀ k (hk : k ≤ n), IsUnit ((M.map (algebraMap _ (RatFunc κ))).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro M hM k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (hM k hk)
  obtain ⟨l, b, h0, h1, hb, hu, h⟩ := (minors_iff _).1 (key (Matrix.charmatrix (-A⁻¹)) (fun k hk => by
    have : (Matrix.charmatrix (-A⁻¹)).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        Matrix.charmatrix ((-A⁻¹).submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
      ext i j : 2
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply]
    rw [this]
    exact (Matrix.charpoly_monic _).ne_zero))
  obtain ⟨u, c, hu0, hu1, hc, hcu, h'⟩ := (minors_iff _).1
    (key (1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C) (fun k hk h2 => by
      have h3 := congrArg (Polynomial.evalRingHom (0 : κ)) h2
      rw [RingHom.map_det, map_zero] at h3
      have : (Polynomial.evalRingHom (0 : κ)).mapMatrix ((1 + (Polynomial.X : Polynomial κ) •
          A.map Polynomial.C).submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      rw [this, Matrix.det_one] at h3
      exact one_ne_zero h3))
  obtain ⟨hbi, hbu, hbb⟩ := upper_inv b hb hu
  refine ⟨l, h0, h1, (minors_iff _).2 ⟨u, c * b⁻¹, hu0, hu1, hc.mul hbi, upper_mul_diag _ _ hc hcu hbi hbu, ?_⟩⟩
  have e1 : A.map Polynomial.C * Matrix.charmatrix (-A⁻¹) = 1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C := by
    rw [Matrix.charmatrix, Matrix.mul_sub, map_neg, Matrix.mul_neg, RingHom.mapMatrix_apply, ← Matrix.map_mul,
      Matrix.mul_nonsing_inv _ hA, sub_neg_eq_add, add_comm, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j : 2
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have e2 : A.map (algebraMap κ (RatFunc κ)) = (A.map Polynomial.C).map (algebraMap _ (RatFunc κ)) := by
    ext i j
    exact IsScalarTower.algebraMap_apply κ (Polynomial κ) (RatFunc κ) (A i j)
  rw [← Matrix.mul_assoc, ← h', ← e1, Matrix.map_mul, h, ← e2, Matrix.mul_assoc, Matrix.mul_assoc, hbb,
    Matrix.mul_one]

section Low
variable {T S S' : Type} [CommRing S] [CommRing S'] {r : T → ℕ}

/- English proof (translation)
Simplify using `[lowM, h.not_gt, h.ne']`.
-/
theorem lowM_upper (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i j : Fin (r τ))
    (h : i < j) : lowM x τ i j = 0 := by
  simp [lowM, h.not_gt, h.ne']

/- English proof (translation)
Simplify using `[lowM]`.
-/
theorem lowM_diag (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i : Fin (r τ)) :
    lowM x τ i i = 1 := by
  simp [lowM]

/- English proof (translation)
Take `⟨τ, ⟨i, j⟩, h⟩` from `v`. Conclude with `dif_pos h`.
-/
theorem lowM_entry (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
    (v : Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) : lowM x v.1 v.2.1.2 v.2.1.1 = x v := by
  obtain ⟨τ, ⟨i, j⟩, h⟩ := v
  exact dif_pos h

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lowM, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lowM_map (f : S →+* S') (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    (lowM x τ).map f = lowM (fun v => f (x v)) τ := by
  ext i j
  simp only [lowM, Matrix.map_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lowM]`. Use `split_ifs with h h'`. Both sides reduce to the same expression. Rewrite using `[h', h1]`.

Conclude with `(h0 i j (lt_of_le_of_ne (not_lt.1 h) (Ne.symm h'))).symm`.
-/
theorem lowM_of_lower (l : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (τ : T)
    (h0 : ∀ i j, i < j → l τ i j = 0) (h1 : ∀ i, l τ i i = 1) :
    lowM (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) τ = l τ := by
  ext i j
  simp only [lowM]
  split_ifs with h h'
  · rfl
  · rw [h', h1]
  · exact (h0 i j (lt_of_le_of_ne (not_lt.1 h) (Ne.symm h'))).symm

end Low

/- English proof (translation)
Use `choose l h0 h1 hm using fun τ => exists_lower_minors (A τ) (hA τ)`. Introduce `h`. Set `φ : MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ →ₐ[κ] RatFunc κ` to `MvPolynomial.aeval (fun v => l v.1 v.2.1.2 v.2.1.1)`. Establish `h2` using `congrArg φ.toRingHom h`. Rewrite `h2` using `[RingHom.map_det, map_zero, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, lowM_map]`.

Apply `(hm τ k hk).ne_zero` to reduce the goal to its premises. Rewrite using `[← h2, ← lowM_of_lower l τ (h0 τ) (h1 τ)]`. Use `congr 3`. Use extensionality with `i j`. Conclude with `(φ.commutes _).symm`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `[φ]`.
-/
theorem generic_minors {κ T : Type} [Field κ] {r : T → ℕ} (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) (k : ℕ) (hk : k ≤ r τ) :
    (((A τ).map (algebraMap κ (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) *
      lowM MvPolynomial.X τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  choose l h0 h1 hm using fun τ => exists_lower_minors (A τ) (hA τ)
  intro h
  let φ : MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ →ₐ[κ] RatFunc κ :=
    MvPolynomial.aeval (fun v => l v.1 v.2.1.2 v.2.1.1)
  have h2 := congrArg φ.toRingHom h
  rw [RingHom.map_det, map_zero, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, lowM_map] at h2
  apply (hm τ k hk).ne_zero
  rw [← h2, ← lowM_of_lower l τ (h0 τ) (h1 τ)]
  congr 3
  · ext i j
    exact (φ.commutes _).symm
  · congr 1
    funext v
    simp [φ]

end GlobalTheory.Reg.CellChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

/- English proof (translation)
Introduce `κ T _ _ _ r G σ hG`. Set `P` to `MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ`. Set `K` to `FractionRing P`. Set `A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ` to `fun τ => (G τ).submatrix (σ τ) id`. Establish `hA : ∀ τ, IsUnit (A τ).det` using `fun τ => by`.

Simplify using `only [A]`. Rewrite using `[Matrix.det_permute]`. Conclude with `(((Equiv.Perm.sign (σ τ)).isUnit).map (Int.castRingHom κ)).mul (hG τ)`. Establish `hdec` using `fun τ => (CellChange.minors_iff ((A τ).map (algebraMap κ K) * lowM (fun v => algebraMap P K (MvPolynomial.X v)) τ)).1 (fun k hk => by`. Establish `h` using `(map_ne_zero_iff (algebraMap P K) (IsFractionRing.injective _ _)).2 (CellChange.generic_minors A hA τ k hk)`.

Rewrite `h` using `[RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]`. Conclude with `isUnit_iff_ne_zero.2 h)`. Use `choose l b h0 h1 hb hu h using hdec`. Take `⟨e, he⟩` from `CellChange.exists_algEquiv_of_generates (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) (fun v => by set y : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → K := fun v => l v.1 v.2.1.2 v.2.1.1 with hy`. Set `F` to `IntermediateField.adjoin κ (Set.range y)`.

Take `⟨hbi, hbu, hbb⟩` from `CellChange.upper_inv _ (hb v.1) (hu v.1)`. Take `⟨x, hx⟩` from `CellChange.lower_mem_range (algebraMap F K) ((A v.1)⁻¹.map (algebraMap κ F) * lowM (fun w => (⟨y w, IntermediateField.subset_adjoin _ _ ⟨w, rfl⟩⟩ : F)) v.1) (lowM (fun v => algebraMap P K (MvPolynomial.X v)) v.1) (b v.1)⁻¹ (CellChange.lowM_upper _ _) (CellChange.lowM_diag _ _) hb …`. Rewrite using `[Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]`. Express the relevant statement in the definitionally equal form `(A v.1)⁻¹.map (algebraMap κ K) * lowM y v.1 = _`. Rewrite using `[hy, CellChange.lowM_of_lower l v.1 (h0 _) (h1 _), ← Matrix.mul_one (l v.1), ← hbb, ← Matrix.mul_assoc (l v.1), ← h, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hA _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul])`.

Use the proof step `v.2.1.2 v.2.1.1`. Rewrite `hx` using `[CellChange.lowM_entry]`. Establish `hx' : (x : K) ∈ F` using `x.2`. Conclude with `hx ▸ hx')`. Use `⟨e, b, fun τ => ⟨hb τ, fun i => (hu τ i).ne_zero⟩, fun τ => ?_⟩` and prove the remaining obligations.

Simplify using `only [he]`. Rewrite using `[CellChange.lowM_of_lower l τ (h0 τ) (h1 τ)]`. Use extensionality with `i j`. Use `congrFun (congrFun (h τ) ((σ τ).symm i)) j` as an intermediate fact. Simplify `this` using `[A, Matrix.mul_apply]`.
-/
theorem GlobalTheory.Reg.cell_change_birational :
    ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  intro κ T _ _ _ r G σ hG
  let P := MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ
  let K := FractionRing P
  let A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ := fun τ => (G τ).submatrix (σ τ) id
  have hA : ∀ τ, IsUnit (A τ).det := fun τ => by
    simp only [A]
    rw [Matrix.det_permute]
    exact (((Equiv.Perm.sign (σ τ)).isUnit).map (Int.castRingHom κ)).mul (hG τ)
  have hdec := fun τ => (CellChange.minors_iff ((A τ).map (algebraMap κ K) *
      lowM (fun v => algebraMap P K (MvPolynomial.X v)) τ)).1 (fun k hk => by
    have h := (map_ne_zero_iff (algebraMap P K) (IsFractionRing.injective _ _)).2
      (CellChange.generic_minors A hA τ k hk)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, CellChange.lowM_map,
      Matrix.map_map] at h
    exact isUnit_iff_ne_zero.2 h)
  choose l b h0 h1 hb hu h using hdec
  obtain ⟨e, he⟩ := CellChange.exists_algEquiv_of_generates
    (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) (fun v => by
      set y : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → K := fun v => l v.1 v.2.1.2 v.2.1.1 with hy
      let F := IntermediateField.adjoin κ (Set.range y)
      obtain ⟨hbi, hbu, hbb⟩ := CellChange.upper_inv _ (hb v.1) (hu v.1)
      obtain ⟨x, hx⟩ := CellChange.lower_mem_range (algebraMap F K)
        ((A v.1)⁻¹.map (algebraMap κ F) * lowM (fun w => (⟨y w, IntermediateField.subset_adjoin _ _ ⟨w, rfl⟩⟩ : F)) v.1)
        (lowM (fun v => algebraMap P K (MvPolynomial.X v)) v.1) (b v.1)⁻¹
        (CellChange.lowM_upper _ _) (CellChange.lowM_diag _ _) hbi hbu (by
          rw [Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]
          change (A v.1)⁻¹.map (algebraMap κ K) * lowM y v.1 = _
          rw [hy, CellChange.lowM_of_lower l v.1 (h0 _) (h1 _), ← Matrix.mul_one (l v.1), ← hbb,
            ← Matrix.mul_assoc (l v.1), ← h, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
            Matrix.nonsing_inv_mul _ (hA _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul])
        v.2.1.2 v.2.1.1
      rw [CellChange.lowM_entry] at hx
      have hx' : (x : K) ∈ F := x.2
      exact hx ▸ hx')
  refine ⟨e, b, fun τ => ⟨hb τ, fun i => (hu τ i).ne_zero⟩, fun τ => ?_⟩
  simp only [he]
  rw [CellChange.lowM_of_lower l τ (h0 τ) (h1 τ)]
  ext i j
  have := congrFun (congrFun (h τ) ((σ τ).symm i)) j
  simpa [A, Matrix.mul_apply] using this
