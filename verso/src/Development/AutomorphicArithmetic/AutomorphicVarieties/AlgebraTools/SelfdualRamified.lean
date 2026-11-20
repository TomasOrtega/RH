import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AlmostSelfdual
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmithZeroOne

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Establish `h' : ∀ j, ∃ a : Fin n → A, ∑ i, a i • c i = X *ᵥ c j` using `fun j => (Submodule.mem_span_range_iff_exists_fun A).mp (h j)`. Use `choose a ha using h'`. Use `⟨(Matrix.of a)ᵀ, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (ha j) i` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
private theorem UpperTheory.V.AlgebraTools.selfdual_ramified_coord {A : Type} [CommRing A] {F : Type} [Field F]
    [Algebra A F] {n : ℕ} (c : Fin n → Fin n → F) (X : Matrix (Fin n) (Fin n) F)
    (h : ∀ j, X *ᵥ c j ∈ Submodule.span A (Set.range c)) :
    ∃ R : Matrix (Fin n) (Fin n) A,
      X * (Matrix.of c)ᵀ = (Matrix.of c)ᵀ * R.map (algebraMap A F) := by
  have h' : ∀ j, ∃ a : Fin n → A, ∑ i, a i • c i = X *ᵥ c j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun A).mp (h j)
  choose a ha using h'
  refine ⟨(Matrix.of a)ᵀ, ?_⟩
  ext i j
  have := congrFun (ha j) i
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Set `ρ : G →* Module.End F (Fin n → F)` to `{ toFun := fun g => Matrix.toLin' ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)) map_one' := by`. Simplify using `[Module.End.one_eq_id]`. Use the proof step `map_mul' := by`. Introduce `g h`. Simplify using `[Matrix.map_mul, Module.End.mul_eq_comp] }`.

Establish `hρ : ∀ g y, ρ g y = (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F) *ᵥ y` using `fun g y => rfl`. Establish `hs : (Matrix.toBilin' H).IsSymm`. Prove the components needed by the constructor for the conclusion. Introduce `x y`. Simplify using `only [Matrix.toBilin'_apply']`.

Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH, dotProduct_comm]`. Establish `hn : (Matrix.toBilin' H).Nondegenerate` using `LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet`. Establish `hB : ∀ g y z, Matrix.toBilin' H (ρ g y) (ρ (σ g) z) = algebraMap A F (u g) * Matrix.toBilin' H y z`. Introduce `g y z`. Simplify using `only [hρ, Matrix.toBilin'_apply']`.

Rewrite using `[← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Establish `hY₀ : Submodule.IsLattice F (Submodule.span A (Set.range (Pi.basisFun F (Fin n))))`. Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_span_of_tower, Module.Basis.span_eq]`. Establish `hst : ∀ g, ∀ y ∈ Submodule.span A (Set.range (Pi.basisFun F (Fin n))), ρ g y ∈ Submodule.span A (Set.range (Pi.basisFun F (Fin n)))`.

Introduce `g y hy`. Rewrite `hy`, the goal using `[Module.Basis.mem_span_iff_repr_mem]`. Introduce `i`. Use `choose a ha using hy`. Use `⟨∑ j, (r g : Matrix (Fin n) (Fin n) A) i j * a j, ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.basisFun_repr] at ha`. Simplify using `[hρ, Matrix.mulVec, dotProduct, ha]`. Take `⟨Y, hY, h1, h2, h3, h4⟩` from `UpperTheory.V.AlgebraTools.almost_selfdual (Matrix.toBilin' H) ρ σ u hs hn hσ hB _ hY₀ hst`. Establish `hZ` using `(UpperTheory.V.AlgebraTools.dual_lattice (Matrix.toBilin' H) hs hn Y hY).1`. Take `⟨b, S, hb1, hb2⟩` from `UpperTheory.V.AlgebraTools.smith_zero_one ϖ Y _ hϖ hZ h3 h4`.

Establish `hfin : Module.finrank F (Fin n → F) = n` using `by simp`. Set `e : Fin (Module.finrank F (Fin n → F)) ≃ Fin n` to `finCongr hfin`. Use `⟨b.reindex e, S.map e.toEmbedding, Y, h1, h2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.range_reindex]`. Conclude with `hb1`.

Rewrite using `[hb2]`. Use `congr 1`. Rewrite using `[← e.surjective.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.AlgebraTools.selfdual_ramified_basis {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {F G : Type} [Field F] [Algebra A F] [IsFractionRing A F] [Group G]
    {n : ℕ} (H : Matrix (Fin n) (Fin n) F) (r : G →* GL (Fin n) A) (σ : G → G) (u : G → A) (ϖ : A)
    (hϖ : Irreducible ϖ) (hH : Hᵀ = H) (hdet : H.det ≠ 0) (hσ : Function.Surjective σ)
    (hr : ∀ g, ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F))ᵀ * H *
      (r (σ g) : Matrix (Fin n) (Fin n) A).map (algebraMap A F) = algebraMap A F (u g) • H) :
    ∃ (b : Module.Basis (Fin n) F (Fin n → F)) (S : Finset (Fin n))
      (Y : Submodule A (Fin n → F)),
      (∀ g, ∀ y ∈ Y, (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F) *ᵥ y ∈ Y) ∧
      (∀ g, ∀ y ∈ (Matrix.toBilin' H).dualSubmodule Y,
        (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F) *ᵥ y ∈
          (Matrix.toBilin' H).dualSubmodule Y) ∧
      (Matrix.toBilin' H).dualSubmodule Y = Submodule.span A (Set.range b) ∧
      Y = Submodule.span A (Set.range fun i => if i ∈ S then ϖ • b i else b i) := by
  classical
  let ρ : G →* Module.End F (Fin n → F) :=
    { toFun := fun g => Matrix.toLin' ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F))
      map_one' := by
        simp [Module.End.one_eq_id]
      map_mul' := by
        intro g h
        simp [Matrix.map_mul, Module.End.mul_eq_comp] }
  have hρ : ∀ g y, ρ g y = (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F) *ᵥ y :=
    fun g y => rfl
  have hs : (Matrix.toBilin' H).IsSymm := by
    constructor
    intro x y
    simp only [Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH, dotProduct_comm]
  have hn : (Matrix.toBilin' H).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  have hB : ∀ g y z, Matrix.toBilin' H (ρ g y) (ρ (σ g) z) =
      algebraMap A F (u g) * Matrix.toBilin' H y z := by
    intro g y z
    simp only [hρ, Matrix.toBilin'_apply']
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hr, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hY₀ : Submodule.IsLattice F (Submodule.span A (Set.range (Pi.basisFun F (Fin n)))) := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [Submodule.span_span_of_tower, Module.Basis.span_eq]
  have hst : ∀ g, ∀ y ∈ Submodule.span A (Set.range (Pi.basisFun F (Fin n))),
      ρ g y ∈ Submodule.span A (Set.range (Pi.basisFun F (Fin n))) := by
    intro g y hy
    rw [Module.Basis.mem_span_iff_repr_mem] at hy ⊢
    intro i
    choose a ha using hy
    refine ⟨∑ j, (r g : Matrix (Fin n) (Fin n) A) i j * a j, ?_⟩
    simp only [Pi.basisFun_repr] at ha
    simp [hρ, Matrix.mulVec, dotProduct, ha]
  obtain ⟨Y, hY, h1, h2, h3, h4⟩ :=
    UpperTheory.V.AlgebraTools.almost_selfdual (Matrix.toBilin' H) ρ σ u hs hn hσ hB _ hY₀ hst
  have hZ := (UpperTheory.V.AlgebraTools.dual_lattice (Matrix.toBilin' H) hs hn Y hY).1
  obtain ⟨b, S, hb1, hb2⟩ := UpperTheory.V.AlgebraTools.smith_zero_one ϖ Y _ hϖ hZ h3 h4
  have hfin : Module.finrank F (Fin n → F) = n := by simp
  let e : Fin (Module.finrank F (Fin n → F)) ≃ Fin n := finCongr hfin
  refine ⟨b.reindex e, S.map e.toEmbedding, Y, h1, h2, ?_, ?_⟩
  · rw [Module.Basis.range_reindex]; exact hb1
  · rw [hb2]
    congr 1
    rw [← e.surjective.range_comp]
    congr 1
    funext i
    simp

/- English proof (translation)
Take `⟨b, S, Y, h1, h2, h3, h4⟩` from `UpperTheory.V.AlgebraTools.selfdual_ramified_basis H r σ u ϖ hϖ hH hdet hσ hr`. Use `set c : Fin n → Fin n → F := fun i => if i ∈ S then ϖ • b i else b i with hc`. Use `set D : Matrix (Fin n) (Fin n) F := Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) with hD`. Use `set Q : Matrix (Fin n) (Fin n) F := (Matrix.of b)ᵀ with hQ`. Establish `hinj : Function.Injective (algebraMap A F)` using `IsFractionRing.injective A F`.

Establish `hcQ : (Matrix.of c)ᵀ = Q * D`. Use extensionality with `i j`. Rewrite using `[hD, Matrix.mul_diagonal]`. Apply the tactic sequence `by_cases hj : j ∈ S <;> simp [hc, hQ, hj, Algebra.smul_def, mul_comm]`. Establish `hQdet : Q.det ≠ 0`.

Establish `: Q = (Pi.basisFun F (Fin n)).toMatrix b`. Use extensionality with `i j`. Simplify using `[hQ, Module.Basis.toMatrix_apply]`. Rewrite using `[this]`. Conclude with `((Pi.basisFun F (Fin n)).isUnit_det b).ne_zero`.

Establish `hDdet : D.det ≠ 0`. Rewrite using `[hD, Matrix.det_diagonal, Finset.prod_ne_zero_iff]`. Introduce `i _`. Rewrite using `[map_ne_zero_iff _ hinj]`. Use `split_ifs`.

Conclude with `hϖ.ne_zero`. Conclude with `one_ne_zero`. Establish `hbZ : ∀ i, b i ∈ (Matrix.toBilin' H).dualSubmodule Y` using `fun i => h3 ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hcY : ∀ i, c i ∈ Y` using `fun i => h4 ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hX : ∀ i j, (Qᵀ * H * Q * D) i j = Matrix.toBilin' H (b i) (c j)`.

Introduce `i j`. Rewrite using `[Matrix.mul_assoc _ Q, ← hcQ, Matrix.mul_assoc, Matrix.toBilin'_apply']`. Both sides reduce to the same expression. Establish `hM : ∀ i j, ∃ a : A, algebraMap A F a = Matrix.toBilin' H (b i) (c j)` using `fun i j => Submodule.mem_one.mp (hbZ i _ (hcY j))`. Use `choose M hM using hM`.

Establish `hXM : Qᵀ * H * Q * D = (Matrix.of M).map (algebraMap A F)`. Use extensionality with `i j`. Rewrite using `[hX, ← hM]`. Both sides reduce to the same expression. Establish `hXdet : IsUnit (Qᵀ * H * Q * D).det`.

Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `(mul_ne_zero (mul_ne_zero (mul_ne_zero hQdet hdet) hQdet) hDdet).isUnit`. Establish `hz : ∀ k j, Matrix.toBilin' H (∑ i, (Qᵀ * H * Q * D)⁻¹ k i • b i) (c j) = (1 : Matrix (Fin n) (Fin n) F) k j`. Introduce `k j`. Rewrite using `[← Matrix.nonsing_inv_mul _ hXdet, Matrix.mul_apply, map_sum, LinearMap.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, hX, smul_eq_mul]`. Establish `hzZ : ∀ k, ∃ a : Fin n → A, ∑ i, a i • b i = ∑ i, (Qᵀ * H * Q * D)⁻¹ k i • b i`. Introduce `k`. Rewrite using `[← Submodule.mem_span_range_iff_exists_fun, ← h3]`.

Introduce `y hy`. Rewrite `hy` using `[h4]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`.

Rewrite using `[hz, Matrix.one_apply]`. Use `split_ifs`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Conclude with `zero_mem _`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[← algebraMap_smul F a x, map_smul, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Use `choose N hN using hzZ`. Establish `hNM : Matrix.of N * Matrix.of M = 1`. Use extensionality with `k j`. Apply `hinj` to reduce the goal to its premises.

Use `hz k j` as an intermediate fact. Rewrite `this` using `[← hN, map_sum, LinearMap.sum_apply]`. Rewrite using `[Matrix.mul_apply, map_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans ?_)` and prove the remaining obligations. Rewrite using `[← algebraMap_smul F (N k i), map_smul, LinearMap.smul_apply, ← hM, map_mul]`.

Both sides reduce to the same expression. Apply the tactic sequence `simp only [Matrix.one_apply] split_ifs <;> simp`. Use `⟨Q, S, Matrix.of M, hQdet, Matrix.isUnit_det_of_left_inverse hNM, hXM, fun g => ?_⟩` and prove the remaining obligations. Take `⟨R, hR⟩` from `UpperTheory.V.AlgebraTools.selfdual_ramified_coord (A := A) b ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)) (fun j => h3 ▸ h2 g _ (hbZ j))`. Take `⟨T, hT⟩` from `UpperTheory.V.AlgebraTools.selfdual_ramified_coord (A := A) c ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)) (fun j => h4 ▸ h1 g _ (hcY j))`.

Use `⟨R, T, hR, ?_⟩` and prove the remaining obligations. Rewrite `hR` using `[← hQ]`. Rewrite `hT` using `[hcQ, ← Matrix.mul_assoc, hR, Matrix.mul_assoc, Matrix.mul_assoc]`. Establish `hQu : IsUnit Q` using `(Matrix.isUnit_iff_isUnit_det Q).mpr hQdet.isUnit`. Conclude with `hQu.mul_left_cancel hT`.
-/
private theorem UpperTheory.V.AlgebraTools.selfdual_ramified_mat {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {F G : Type} [Field F] [Algebra A F] [IsFractionRing A F] [Group G]
    {n : ℕ} (H : Matrix (Fin n) (Fin n) F) (r : G →* GL (Fin n) A) (σ : G → G) (u : G → A) (ϖ : A)
    (hϖ : Irreducible ϖ) (hH : Hᵀ = H) (hdet : H.det ≠ 0) (hσ : Function.Surjective σ)
    (hr : ∀ g, ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F))ᵀ * H *
      (r (σ g) : Matrix (Fin n) (Fin n) A).map (algebraMap A F) = algebraMap A F (u g) • H) :
    ∃ (Q : Matrix (Fin n) (Fin n) F) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) A),
      Q.det ≠ 0 ∧ IsUnit M.det ∧
      Qᵀ * H * Q * Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) =
        M.map (algebraMap A F) ∧
      ∀ g, ∃ R T : Matrix (Fin n) (Fin n) A,
        (r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F) * Q = Q * R.map (algebraMap A F) ∧
        R.map (algebraMap A F) *
            Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) =
          Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) *
            T.map (algebraMap A F) := by
  classical
  obtain ⟨b, S, Y, h1, h2, h3, h4⟩ :=
    UpperTheory.V.AlgebraTools.selfdual_ramified_basis H r σ u ϖ hϖ hH hdet hσ hr
  set c : Fin n → Fin n → F := fun i => if i ∈ S then ϖ • b i else b i with hc
  set D : Matrix (Fin n) (Fin n) F :=
    Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) with hD
  set Q : Matrix (Fin n) (Fin n) F := (Matrix.of b)ᵀ with hQ
  have hinj : Function.Injective (algebraMap A F) := IsFractionRing.injective A F
  have hcQ : (Matrix.of c)ᵀ = Q * D := by
    ext i j
    rw [hD, Matrix.mul_diagonal]
    by_cases hj : j ∈ S <;> simp [hc, hQ, hj, Algebra.smul_def, mul_comm]
  have hQdet : Q.det ≠ 0 := by
    have : Q = (Pi.basisFun F (Fin n)).toMatrix b := by
      ext i j
      simp [hQ, Module.Basis.toMatrix_apply]
    rw [this]
    exact ((Pi.basisFun F (Fin n)).isUnit_det b).ne_zero
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    rw [map_ne_zero_iff _ hinj]
    split_ifs
    · exact hϖ.ne_zero
    · exact one_ne_zero
  have hbZ : ∀ i, b i ∈ (Matrix.toBilin' H).dualSubmodule Y := fun i =>
    h3 ▸ Submodule.subset_span ⟨i, rfl⟩
  have hcY : ∀ i, c i ∈ Y := fun i => h4 ▸ Submodule.subset_span ⟨i, rfl⟩
  have hX : ∀ i j, (Qᵀ * H * Q * D) i j = Matrix.toBilin' H (b i) (c j) := by
    intro i j
    rw [Matrix.mul_assoc _ Q, ← hcQ, Matrix.mul_assoc, Matrix.toBilin'_apply']
    rfl
  have hM : ∀ i j, ∃ a : A, algebraMap A F a = Matrix.toBilin' H (b i) (c j) := fun i j =>
    Submodule.mem_one.mp (hbZ i _ (hcY j))
  choose M hM using hM
  have hXM : Qᵀ * H * Q * D = (Matrix.of M).map (algebraMap A F) := by
    ext i j
    rw [hX, ← hM]; rfl
  have hXdet : IsUnit (Qᵀ * H * Q * D).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hQdet hdet) hQdet) hDdet).isUnit
  have hz : ∀ k j, Matrix.toBilin' H (∑ i, (Qᵀ * H * Q * D)⁻¹ k i • b i) (c j) =
      (1 : Matrix (Fin n) (Fin n) F) k j := by
    intro k j
    rw [← Matrix.nonsing_inv_mul _ hXdet, Matrix.mul_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, hX, smul_eq_mul]
  have hzZ : ∀ k, ∃ a : Fin n → A, ∑ i, a i • b i = ∑ i, (Qᵀ * H * Q * D)⁻¹ k i • b i := by
    intro k
    rw [← Submodule.mem_span_range_iff_exists_fun, ← h3]
    intro y hy
    rw [h4] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hz, Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul F a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  choose N hN using hzZ
  have hNM : Matrix.of N * Matrix.of M = 1 := by
    ext k j
    apply hinj
    have := hz k j
    rw [← hN, map_sum, LinearMap.sum_apply] at this
    rw [Matrix.mul_apply, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans ?_)
    · rw [← algebraMap_smul F (N k i), map_smul, LinearMap.smul_apply, ← hM, map_mul]
      rfl
    · simp only [Matrix.one_apply]
      split_ifs <;> simp
  refine ⟨Q, S, Matrix.of M, hQdet, Matrix.isUnit_det_of_left_inverse hNM, hXM, fun g => ?_⟩
  obtain ⟨R, hR⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified_coord (A := A) b
    ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)) (fun j => h3 ▸ h2 g _ (hbZ j))
  obtain ⟨T, hT⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified_coord (A := A) c
    ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)) (fun j => h4 ▸ h1 g _ (hcY j))
  refine ⟨R, T, hR, ?_⟩
  rw [← hQ] at hR
  rw [hcQ, ← Matrix.mul_assoc, hR, Matrix.mul_assoc, Matrix.mul_assoc] at hT
  have hQu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hQdet.isUnit
  exact hQu.mul_left_cancel hT

/- English proof (translation)
Introduce `A _ _ _ F G _ _ _ _ n H r σ u A' F' _ _ _ φ φF ϖ s hϖ hs hφ hinj hH hdet hσ hr`. Take `⟨Q, S, M, hQ, hM, hQM, hRT⟩` from `UpperTheory.V.AlgebraTools.selfdual_ramified_mat H r σ u ϖ hϖ hH hdet hσ hr`. Establish `hinjA : Function.Injective (algebraMap A F)` using `IsFractionRing.injective A F`. Establish `hsϖ : algebraMap A' F' s * algebraMap A' F' s = φF (algebraMap A F ϖ)`. Rewrite using `[← map_mul, ← sq, hs, hφ]`.

Establish `hs0 : algebraMap A' F' s ≠ 0`. Introduce `h`. Rewrite `hsϖ` using `[h, mul_zero, eq_comm, map_eq_zero, map_eq_zero_iff _ hinjA]`. Conclude with `hϖ.ne_zero hsϖ`. Use `set E : Matrix (Fin n) (Fin n) F' := Matrix.diagonal (fun i => algebraMap A' F' (if i ∈ S then s else 1)) with hE`.

Use `set D : Matrix (Fin n) (Fin n) F := Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) with hD`. Establish `hEE : E * E = D.map φF`. Rewrite using `[hE, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `split_ifs`. Conclude with `hsϖ`. Simplify using the standard rewrite rules. Establish `hEdet : E.det ≠ 0`. Rewrite using `[hE, Matrix.det_diagonal, Finset.prod_ne_zero_iff]`.

Introduce `i _`. Use `split_ifs`. Conclude with `hs0`. Simplify using the standard rewrite rules. Establish `hQdet : (Q.map φF).det ≠ 0`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Simplify using `using hQ`. Establish `hPdet : (Q.map φF * E).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hQdet hEdet`.

Establish `hPu : IsUnit (Q.map φF * E)` using `(Matrix.isUnit_iff_isUnit_det _).mpr hPdet.isUnit`. Establish `hmapinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) A' => X.map (algebraMap A' F'))` using `Matrix.map_injective hinj`. Use `set H0 : Matrix (Fin n) (Fin n) F := Qᵀ * H * Q with hH0`. Establish `hH0s : ∀ i j, H0 j i = H0 i j`. Introduce `i j`.

Establish `: H0ᵀ = H0`. Rewrite using `[hH0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH, Matrix.mul_assoc]`. Conclude with `congrFun (congrFun this i) j`. Establish `hent : ∀ i j, φF (H0 i j) * φF (algebraMap A F (if j ∈ S then ϖ else 1)) = algebraMap A' F' (φ (M i j))`. Introduce `i j`.

Use `congrFun (congrFun hQM i) j` as an intermediate fact. Rewrite `this` using `[hD, Matrix.mul_diagonal, Matrix.map_apply]`. Rewrite using `[← map_mul, this, hφ]`. Establish `hH' : ∀ i j, ∃ a : A', algebraMap A' F' a = (E * H0.map φF * E) i j`. Introduce `i j`.

Rewrite using `[hE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`. Establish `h1` using `hent i j`. Establish `h2` using `hent j i`. Rewrite `h2` using `[hH0s]`. Distinguish the cases in `hj : j ∈ S`.

Distinguish the cases in `hi : i ∈ S`. Use `⟨φ (M i j), ?_⟩` and prove the remaining obligations. Simplify using `only [hi, hj, if_true] at h1 ⊢`. Rewrite using `[← h1, ← hsϖ]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨φ (M j i) * s, ?_⟩` and prove the remaining obligations. Simplify using `only [hi, hj, if_true, if_false, map_one, mul_one, one_mul] at h2 ⊢`. Rewrite using `[h2, map_mul]`. Use `⟨(if i ∈ S then s else 1) * φ (M i j), ?_⟩` and prove the remaining obligations. Simplify using `only [hj, if_false, map_one, mul_one] at h1 ⊢`.

Rewrite using `[h1, map_mul]`. Use `choose H' hH' using hH'`. Establish `hH'm : (Matrix.of H').map (algebraMap A' F') = E * H0.map φF * E`. Use extensionality with `i j`. Conclude with `hH' i j`.

Establish `hH'det : (Matrix.of H').det = φ M.det`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hφ, RingHom.map_det (algebraMap A' F'), RingHom.map_det (algebraMap A F), RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hH'm, ← hQM, RingHom.map_det φF, RingHom.mapMatrix_apply, Matrix.map_mul (L := H0) (M := D), ← hEE]`. Simplify using `only [Matrix.det_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hH'u : IsUnit (Matrix.of H')`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, hH'det]`. Conclude with `hM.map φ`. Establish `hr' : ∀ g, ∃ X : Matrix (Fin n) (Fin n) A', (r g : Matrix (Fin n) (Fin n) A).map (fun a => algebraMap A' F' (φ a)) * (Q.map φF * E) = (Q.map φF * E) * X.map (algebraMap A' F')`. Introduce `g`.

Take `⟨R, T, hR, hT⟩` from `hRT g`. Establish `hX : ∀ i j, ∃ a : A', algebraMap A' F' (if i ∈ S then s else 1) * algebraMap A' F' a = algebraMap A' F' (φ (R i j)) * algebraMap A' F' (if j ∈ S then s else 1)`. Introduce `i j`. Establish `h1` using `congrArg φF (congrFun (congrFun hT i) j)`. Rewrite `h1` using `[hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.map_apply, map_mul, map_mul, hφ (R i j), hφ (T i j)]`.

Distinguish the cases in `hi : i ∈ S`. Distinguish the cases in `hj : j ∈ S`. Use `⟨φ (R i j), ?_⟩` and prove the remaining obligations. Simplify using `only [hi, hj, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨s * φ (T i j), ?_⟩` and prove the remaining obligations. Simplify using `only [hi, hj, if_true, if_false, map_one, mul_one] at h1 ⊢`. Rewrite using `[h1, ← hsϖ, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨φ (R i j) * (if j ∈ S then s else 1), ?_⟩` and prove the remaining obligations.

Simplify using `only [hi, if_false, map_one, one_mul, map_mul]`. Use `choose X hX using hX`. Use `⟨Matrix.of X, ?_⟩` and prove the remaining obligations. Establish `h1 : E * (Matrix.of X).map (algebraMap A' F') = (R.map (algebraMap A F)).map φF * E`. Use extensionality with `i j`.

Rewrite using `[hE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hφ]`. Conclude with `hX i j`. Establish `h2 : (r g : Matrix (Fin n) (Fin n) A).map (fun a => algebraMap A' F' (φ a)) = ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)).map φF`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, hφ]`.

Rewrite using `[Matrix.mul_assoc, h1, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hR]`. Use `choose X hX using hr'`. Establish `hfun : (fun a => algebraMap A' F' (φ a)) = ((algebraMap A' F').comp φ : A →+* F')` using `rfl`. Set `ρ : G →* Matrix (Fin n) (Fin n) A'` to `{ toFun := X map_one' := by`. Apply `hmapinj` to reduce the goal to its premises.

Apply `hPu.mul_left_cancel` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← hX, hfun]`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`.

Introduce `g h`. Apply `hmapinj` to reduce the goal to its premises. Apply `hPu.mul_left_cancel` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← hX, Matrix.map_mul, ← Matrix.mul_assoc _ ((X g).map _), ← hX g, Matrix.mul_assoc _ _ ((X h).map _), ← hX h, map_mul, Units.val_mul, hfun, Matrix.map_mul, Matrix.mul_assoc] }`.

Use `⟨hPu.unit, hH'u.unit, ρ.toHomUnits, ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, IsUnit.unit_spec, hH'm, hH0, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Establish `: Eᵀ = E` using `Matrix.diagonal_transpose _`. Rewrite using `[this]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[IsUnit.unit_spec]`. Conclude with `hX g`.
-/
theorem UpperTheory.V.AlgebraTools.selfdual_ramified :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F G : Type} [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {n : ℕ} (H : Matrix (Fin n) (Fin n) F) (r : G →* GL (Fin n) A) (σ : G → G) (u : G → A) {A' F' : Type} [CommRing A'] [Field F'] [Algebra A' F'] (φ : A →+* A') (φF : F →+* F') (ϖ : A) (s : A'), Irreducible ϖ → s ^ 2 = φ ϖ → (∀ a, φF (algebraMap A F a) = algebraMap A' F' (φ a)) → Function.Injective (algebraMap A' F') → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F))ᵀ * H * (r (σ g) : Matrix (Fin n) (Fin n) A).map (algebraMap A F) = algebraMap A F (u g) • H) → ∃ (P : GL (Fin n) F') (H' : GL (Fin n) A') (r' : G →* GL (Fin n) A'), (P : Matrix (Fin n) (Fin n) F')ᵀ * H.map φF * P = (H' : Matrix (Fin n) (Fin n) A').map (algebraMap A' F') ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) A).map (fun a => algebraMap A' F' (φ a)) * P = (P : Matrix (Fin n) (Fin n) F') * (r' g : Matrix (Fin n) (Fin n) A').map (algebraMap A' F') := by
  intro A _ _ _ F G _ _ _ _ n H r σ u A' F' _ _ _ φ φF ϖ s hϖ hs hφ hinj hH hdet hσ hr
  obtain ⟨Q, S, M, hQ, hM, hQM, hRT⟩ :=
    UpperTheory.V.AlgebraTools.selfdual_ramified_mat H r σ u ϖ hϖ hH hdet hσ hr
  have hinjA : Function.Injective (algebraMap A F) := IsFractionRing.injective A F
  have hsϖ : algebraMap A' F' s * algebraMap A' F' s = φF (algebraMap A F ϖ) := by
    rw [← map_mul, ← sq, hs, hφ]
  have hs0 : algebraMap A' F' s ≠ 0 := by
    intro h
    rw [h, mul_zero, eq_comm, map_eq_zero, map_eq_zero_iff _ hinjA] at hsϖ
    exact hϖ.ne_zero hsϖ
  set E : Matrix (Fin n) (Fin n) F' :=
    Matrix.diagonal (fun i => algebraMap A' F' (if i ∈ S then s else 1)) with hE
  set D : Matrix (Fin n) (Fin n) F :=
    Matrix.diagonal (fun i => algebraMap A F (if i ∈ S then ϖ else 1)) with hD
  have hEE : E * E = D.map φF := by
    rw [hE, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs
    · exact hsϖ
    · simp
  have hEdet : E.det ≠ 0 := by
    rw [hE, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    split_ifs
    · exact hs0
    · simp
  have hQdet : (Q.map φF).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hQ
  have hPdet : (Q.map φF * E).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hQdet hEdet
  have hPu : IsUnit (Q.map φF * E) := (Matrix.isUnit_iff_isUnit_det _).mpr hPdet.isUnit
  have hmapinj : Function.Injective
      (fun X : Matrix (Fin n) (Fin n) A' => X.map (algebraMap A' F')) :=
    Matrix.map_injective hinj
  set H0 : Matrix (Fin n) (Fin n) F := Qᵀ * H * Q with hH0
  have hH0s : ∀ i j, H0 j i = H0 i j := by
    intro i j
    have : H0ᵀ = H0 := by
      rw [hH0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH,
        Matrix.mul_assoc]
    exact congrFun (congrFun this i) j
  have hent : ∀ i j, φF (H0 i j) * φF (algebraMap A F (if j ∈ S then ϖ else 1)) =
      algebraMap A' F' (φ (M i j)) := by
    intro i j
    have := congrFun (congrFun hQM i) j
    rw [hD, Matrix.mul_diagonal, Matrix.map_apply] at this
    rw [← map_mul, this, hφ]
  have hH' : ∀ i j, ∃ a : A', algebraMap A' F' a = (E * H0.map φF * E) i j := by
    intro i j
    rw [hE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    have h1 := hent i j
    have h2 := hent j i
    rw [hH0s] at h2
    by_cases hj : j ∈ S
    · by_cases hi : i ∈ S
      · refine ⟨φ (M i j), ?_⟩
        simp only [hi, hj, if_true] at h1 ⊢
        rw [← h1, ← hsϖ]; ring
      · refine ⟨φ (M j i) * s, ?_⟩
        simp only [hi, hj, if_true, if_false, map_one, mul_one, one_mul] at h2 ⊢
        rw [h2, map_mul]
    · refine ⟨(if i ∈ S then s else 1) * φ (M i j), ?_⟩
      simp only [hj, if_false, map_one, mul_one] at h1 ⊢
      rw [h1, map_mul]
  choose H' hH' using hH'
  have hH'm : (Matrix.of H').map (algebraMap A' F') = E * H0.map φF * E := by
    ext i j
    exact hH' i j
  have hH'det : (Matrix.of H').det = φ M.det := by
    apply hinj
    rw [← hφ, RingHom.map_det (algebraMap A' F'), RingHom.map_det (algebraMap A F),
      RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hH'm, ← hQM, RingHom.map_det φF,
      RingHom.mapMatrix_apply, Matrix.map_mul (L := H0) (M := D), ← hEE]
    simp only [Matrix.det_mul]
    ring
  have hH'u : IsUnit (Matrix.of H') := by
    rw [Matrix.isUnit_iff_isUnit_det, hH'det]
    exact hM.map φ
  have hr' : ∀ g, ∃ X : Matrix (Fin n) (Fin n) A',
      (r g : Matrix (Fin n) (Fin n) A).map (fun a => algebraMap A' F' (φ a)) * (Q.map φF * E) =
        (Q.map φF * E) * X.map (algebraMap A' F') := by
    intro g
    obtain ⟨R, T, hR, hT⟩ := hRT g
    have hX : ∀ i j, ∃ a : A', algebraMap A' F' (if i ∈ S then s else 1) * algebraMap A' F' a =
        algebraMap A' F' (φ (R i j)) * algebraMap A' F' (if j ∈ S then s else 1) := by
      intro i j
      have h1 := congrArg φF (congrFun (congrFun hT i) j)
      rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.map_apply,
        map_mul, map_mul, hφ (R i j), hφ (T i j)] at h1
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · refine ⟨φ (R i j), ?_⟩
          simp only [hi, hj, if_true]
          ring
        · refine ⟨s * φ (T i j), ?_⟩
          simp only [hi, hj, if_true, if_false, map_one, mul_one] at h1 ⊢
          rw [h1, ← hsϖ, map_mul]; ring
      · refine ⟨φ (R i j) * (if j ∈ S then s else 1), ?_⟩
        simp only [hi, if_false, map_one, one_mul, map_mul]
    choose X hX using hX
    refine ⟨Matrix.of X, ?_⟩
    have h1 : E * (Matrix.of X).map (algebraMap A' F') = (R.map (algebraMap A F)).map φF * E := by
      ext i j
      rw [hE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.map_apply,
        Matrix.map_apply, hφ]
      exact hX i j
    have h2 : (r g : Matrix (Fin n) (Fin n) A).map (fun a => algebraMap A' F' (φ a)) =
        ((r g : Matrix (Fin n) (Fin n) A).map (algebraMap A F)).map φF := by
      ext i j
      simp only [Matrix.map_apply, hφ]
    rw [Matrix.mul_assoc, h1, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
      ← Matrix.map_mul, hR]
  choose X hX using hr'
  have hfun : (fun a => algebraMap A' F' (φ a)) = ((algebraMap A' F').comp φ : A →+* F') := rfl
  let ρ : G →* Matrix (Fin n) (Fin n) A' :=
    { toFun := X
      map_one' := by
        apply hmapinj
        apply hPu.mul_left_cancel
        simp only
        rw [← hX, hfun]
        simp
      map_mul' := by
        intro g h
        apply hmapinj
        apply hPu.mul_left_cancel
        simp only
        rw [← hX, Matrix.map_mul, ← Matrix.mul_assoc _ ((X g).map _), ← hX g,
          Matrix.mul_assoc _ _ ((X h).map _), ← hX h, map_mul, Units.val_mul, hfun,
          Matrix.map_mul, Matrix.mul_assoc] }
  refine ⟨hPu.unit, hH'u.unit, ρ.toHomUnits, ?_, fun g => ?_⟩
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, hH'm, hH0, Matrix.transpose_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.transpose_map]
    have : Eᵀ = E := Matrix.diagonal_transpose _
    rw [this]
    simp only [Matrix.mul_assoc]
  · rw [IsUnit.unit_spec]
    exact hX g
