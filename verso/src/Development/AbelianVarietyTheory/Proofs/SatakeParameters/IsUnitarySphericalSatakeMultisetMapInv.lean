import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexGlMapStandardLatticeOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardQuotMatrixRangeDvrEqResiduePowCorankStatement

noncomputable section

namespace GlobalTheory.SatakeInv

open GlobalTheory.LatHecke GlobalTheory.RowSatakeBound Matrix

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r A g hg h3`. Rewrite using `[(GlobalTheory.T.relIndex_glMap_standardLattice_of_integral O K r A g hg).1, GlobalTheory.T.card_quot_matrix_range_dvr_eq_residue_pow_corank O r A ((GlobalTheory.T.relIndex_glMap_standardLattice_of_integral O K r A g hg).2 h3)]`.
-/
theorem relIndex_eq_pow_rank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  intro O K _ _ _ _ _ _ _ r A g hg h3
  rw [(GlobalTheory.T.relIndex_glMap_standardLattice_of_integral O K r A g hg).1, GlobalTheory.T.card_quot_matrix_range_dvr_eq_residue_pow_corank O r A ((GlobalTheory.T.relIndex_glMap_standardLattice_of_integral O K r A g hg).2 h3)]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔ _`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩ j`. Use `⟨c j, ?_⟩` and prove the remaining obligations.

Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`. Introduce `h choose c hc using h`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]`.
-/
theorem mem_std_iff {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ} (x : Fin r → K) :
    x ∈ (std O K r).1 ↔ ∀ i, x i ∈ (algebraMap O K).range := by
  change x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.map _ (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) ≤ (std O K r).1 ↔ _`. Rewrite using `[Submodule.map_span, Submodule.span_le, ← Set.range_comp, Set.range_subset_iff, forall_swap]`. Use `forall_congr' fun j => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, LinearMap.coe_restrictScalars, Pi.basisFun_apply, Matrix.toLin'_apply, SetLike.mem_coe, mem_std_iff, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem glMap_std_le_iff (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (g : GL (Fin r) K) :
    glMap g (std O K r).1 ≤ (std O K r).1 ↔ ∀ i j, (g : Matrix (Fin r) (Fin r) K) i j ∈ (algebraMap O K).range := by
  change Submodule.map _ (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) ≤ (std O K r).1 ↔ _
  rw [Submodule.map_span, Submodule.span_le, ← Set.range_comp, Set.range_subset_iff, forall_swap]
  refine forall_congr' fun j => ?_
  simp only [Function.comp_apply, LinearMap.coe_restrictScalars, Pi.basisFun_apply,
    Matrix.toLin'_apply, SetLike.mem_coe, mem_std_iff, Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Establish `hr : Module.finrank R M = n`. Rewrite using `[Submodule.IsLattice.finrank_of_pi K M, Fintype.card_fin]`. Set `b : Module.Basis (Fin n) R M` to `Module.finBasisOfFinrankEq R M hr`. Set `c : Module.Basis (Fin n) K (Fin n → K)` to `b.extendOfIsLattice K`. Set `p` to `Pi.basisFun K (Fin n)`.

Set `B : GL (Fin n) K` to `⟨p.toMatrix c, c.toMatrix p, by simp, by simp⟩`. Establish `hB : ∀ x i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i = c.repr x i`. Introduce `x i`. Use `congrFun (Module.Basis.toMatrix_mulVec_repr p c x) i` as an intermediate fact. Conclude with `this`.

Use `⟨B, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [hB]`. Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Use `⟨b.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations.

Establish `h1 : x = ∑ j, algebraMap R K (b.repr ⟨x, hx⟩ j) • c j`. Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [c, Module.Basis.extendOfIsLattice_apply, algebraMap_smul]`. Conclude with `this.symm`.

Establish `h2` using `congrFun (c.repr_sum_self fun j => algebraMap R K (b.repr ⟨x, hx⟩ j)) i`. Rewrite `h2` using `[← h1]`. Conclude with `h2.symm`. Introduce `h choose r hr using h`. Rewrite using `[← c.sum_repr x]`.

Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hr, algebraMap_smul]`. Use `M.smul_mem _ ?_` and prove the remaining obligations. Simplify using `[c]`.
-/
theorem exists_matrix_of_isLattice' {R K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {n : ℕ} (M : Submodule R (Fin n → K)) [Submodule.IsLattice K M] :
    ∃ B : GL (Fin n) K, ∀ x : Fin n → K, x ∈ M ↔
      ∀ i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i ∈ (algebraMap R K).range := by
  have hr : Module.finrank R M = n := by
    rw [Submodule.IsLattice.finrank_of_pi K M, Fintype.card_fin]
  let b : Module.Basis (Fin n) R M := Module.finBasisOfFinrankEq R M hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsLattice K
  let p := Pi.basisFun K (Fin n)
  let B : GL (Fin n) K := ⟨p.toMatrix c, c.toMatrix p, by simp, by simp⟩
  have hB : ∀ x i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i = c.repr x i := by
    intro x i
    have := congrFun (Module.Basis.toMatrix_mulVec_repr p c x) i
    exact this
  refine ⟨B, fun x => ?_⟩
  simp only [hB]
  constructor
  · intro hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, algebraMap R K (b.repr ⟨x, hx⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [c, Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
      exact this.symm
    have h2 := congrFun (c.repr_sum_self fun j => algebraMap R K (b.repr ⟨x, hx⟩ j)) i
    rw [← h1] at h2
    exact h2.symm
  · intro h
    choose r hr using h
    rw [← c.sum_repr x]
    refine sum_mem fun j _ => ?_
    rw [← hr, algebraMap_smul]
    refine M.smul_mem _ ?_
    simp [c]

/- English proof (translation)
Use `haveI := L.2`. Take `⟨B, hB⟩` from `exists_matrix_of_isLattice' (R := O) (K := K) L.1`. Use `⟨B, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hB]`.

Establish `e : (∀ i, ((B⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVec x i ∈ (algebraMap O K).range) ↔ ((B⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVec x ∈ (std O K r).1` using `(mem_std_iff _).symm`. Rewrite using `[e]`. Simplify using `only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]` and apply the resulting hypothesis. Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem exists_glMap_std_eq (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (L : Lat O K r) :
    ∃ h : GL (Fin r) K, glMap h (std O K r).1 = L.1 := by
  haveI := L.2
  obtain ⟨B, hB⟩ := exists_matrix_of_isLattice' (R := O) (K := K) L.1
  refine ⟨B, ?_⟩
  ext x
  rw [hB]
  have e : (∀ i, ((B⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVec x i ∈ (algebraMap O K).range) ↔
      ((B⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVec x ∈ (std O K r).1 := (mem_std_iff _).symm
  rw [e]
  simp only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Introduce `hϖ hu`. Rewrite using `[hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]`. Establish `hf : ∀ y : Fin r → K, Matrix.toLin' ((scalGL u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) y = ϖ • y`. Introduce `y`. Rewrite using `[scalGL_val, Matrix.toLin'_apply, Matrix.scalar_apply]`.

Use extensionality with `i`. Rewrite using `[Matrix.mulVec_diagonal]`. Simplify using `[hu, Algebra.smul_def]`. Use extensionality with `x`. Simplify using `only [glMap, Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists, LinearMap.coe_restrictScalars, hf]`.
-/
theorem glMap_scalGL_std (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (ϖ : O) (u : Kˣ) :
    Irreducible ϖ → (u : K) = algebraMap O K ϖ →
    glMap (scalGL u) (std O K r).1 = IsLocalRing.maximalIdeal O • (std O K r).1 := by
  intro hϖ hu
  rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
  have hf : ∀ y : Fin r → K,
      Matrix.toLin' ((scalGL u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) y = ϖ • y := by
    intro y
    rw [scalGL_val, Matrix.toLin'_apply, Matrix.scalar_apply]
    ext i
    rw [Matrix.mulVec_diagonal]
    simp [hu, Algebra.smul_def]
  ext x
  simp only [glMap, Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists,
    LinearMap.coe_restrictScalars, hf]

section Lattices

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

/- English proof (translation)
Rewrite using `[glMap_std_le_iff O K r, glMap_std_le_iff O K r]`. Simplify using `only [tinv_inv_val, transpose_apply]`. Conclude with `forall_swap`.
-/
theorem glMap_tinv_inv_le_iff (A : GL (Fin r) K) :
    glMap (tinv A)⁻¹ (std O K r).1 ≤ (std O K r).1 ↔ glMap A (std O K r).1 ≤ (std O K r).1 := by
  rw [glMap_std_le_iff O K r, glMap_std_le_iff O K r]
  simp only [tinv_inv_val, transpose_apply]
  exact forall_swap

/- English proof (translation)
Establish `h1 : glMap X⁻¹ (std O K r).1 = (std O K r).1` using `by conv_lhs => rw [← h, ← glMap_mul, inv_mul_cancel, glMap_one]`. Establish `a1 : glMap (tinv X) (std O K r).1 ≤ (std O K r).1`. Use `(glMap_tinv_inv_le_iff (O := O) X⁻¹).2 h1.le` as an intermediate fact. Rewrite `this` using `[map_inv, inv_inv]`. Then use the resulting hypothesis. Establish `a2 : glMap (tinv X)⁻¹ (std O K r).1 ≤ (std O K r).1` using `(glMap_tinv_inv_le_iff X).2 h.le`.

Use `le_antisymm a1 ?_` and prove the remaining obligations. Use `(glMap_le_glMap_iff (tinv X) _ _).2 a2` as an intermediate fact. Rewrite `this` using `[← glMap_mul, mul_inv_cancel, glMap_one]`. Then use the resulting hypothesis.
-/
theorem glMap_tinv_std (X : GL (Fin r) K) (h : glMap X (std O K r).1 = (std O K r).1) :
    glMap (tinv X) (std O K r).1 = (std O K r).1 := by
  have h1 : glMap X⁻¹ (std O K r).1 = (std O K r).1 := by
    conv_lhs => rw [← h, ← glMap_mul, inv_mul_cancel, glMap_one]
  have a1 : glMap (tinv X) (std O K r).1 ≤ (std O K r).1 := by
    have := (glMap_tinv_inv_le_iff (O := O) X⁻¹).2 h1.le
    rwa [map_inv, inv_inv] at this
  have a2 : glMap (tinv X)⁻¹ (std O K r).1 ≤ (std O K r).1 := (glMap_tinv_inv_le_iff X).2 h.le
  refine le_antisymm a1 ?_
  have := (glMap_le_glMap_iff (tinv X) _ _).2 a2
  rwa [← glMap_mul, mul_inv_cancel, glMap_one] at this

/- English proof (translation)
Establish `hint` using `(glMap_std_le_iff O K r g).1 h1`. Use `choose A hA using hint`. Set `A' : Matrix (Fin r) (Fin r) O` to `Matrix.of A`. Establish `hg : (g : Matrix (Fin r) (Fin r) K) = A'.map (algebraMap O K)`. Use extensionality with `i j`.

Conclude with `(hA i j).symm`. Establish `hgt : (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = A'ᵀ.map (algebraMap O K)`. Rewrite using `[tinv_inv_val, hg, Matrix.transpose_map]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `h0 : algebraMap O K ϖ ≠ 0` using `by simpa using hϖ.ne_zero`.

Set `u : Kˣ` to `Units.mk0 _ h0`. Establish `hz` using `glMap_scalGL_std O K r ϖ u hϖ rfl`. Establish `h3' : IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap (tinv g)⁻¹ (std O K r).1`. Rewrite `h3`, the goal using `[← hz]`. Establish `e1 : glMap (scalGL u) (std O K r).1 = glMap (tinv g)⁻¹ (glMap (tinv g * scalGL u) (std O K r).1)`.

Rewrite using `[← glMap_mul, inv_mul_cancel_left]`. Establish `eΦ : tinv g * scalGL u = (tinv (g⁻¹ * scalGL u))⁻¹`. Rewrite using `[map_mul, map_inv, tinv_scalGL', _root_.mul_inv_rev, inv_inv, inv_inv, scalGL_comm]`. Rewrite using `[e1, glMap_le_glMap_iff, eΦ, glMap_tinv_inv_le_iff]`. Use `(glMap_le_glMap_iff g⁻¹ _ _).2 h3` as an intermediate fact.

Rewrite `this` using `[← glMap_mul, ← glMap_mul, inv_mul_cancel, glMap_one]`. Then use the resulting hypothesis. Rewrite using `[relIndex_eq_pow_rank O K r A' g hg h3, relIndex_eq_pow_rank O K r A'ᵀ _ hgt h3', Matrix.transpose_map, Matrix.rank_transpose]`.
-/
theorem relIndex_tinv_inv {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}
    (g : GL (Fin r) K) (h1 : glMap g (std O K r).1 ≤ (std O K r).1)
    (h3 : IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1) :
    (glMap (tinv g)⁻¹ (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup =
      (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup := by
  have hint := (glMap_std_le_iff O K r g).1 h1
  choose A hA using hint
  let A' : Matrix (Fin r) (Fin r) O := Matrix.of A
  have hg : (g : Matrix (Fin r) (Fin r) K) = A'.map (algebraMap O K) := by
    ext i j; exact (hA i j).symm
  have hgt : (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = A'ᵀ.map (algebraMap O K) := by
    rw [tinv_inv_val, hg, Matrix.transpose_map]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  let u : Kˣ := Units.mk0 _ h0
  have hz := glMap_scalGL_std O K r ϖ u hϖ rfl
  have h3' : IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap (tinv g)⁻¹ (std O K r).1 := by
    rw [← hz] at h3 ⊢
    have e1 : glMap (scalGL u) (std O K r).1 =
        glMap (tinv g)⁻¹ (glMap (tinv g * scalGL u) (std O K r).1) := by
      rw [← glMap_mul, inv_mul_cancel_left]
    have eΦ : tinv g * scalGL u = (tinv (g⁻¹ * scalGL u))⁻¹ := by
      rw [map_mul, map_inv, tinv_scalGL', _root_.mul_inv_rev, inv_inv, inv_inv, scalGL_comm]
    rw [e1, glMap_le_glMap_iff, eΦ, glMap_tinv_inv_le_iff]
    have := (glMap_le_glMap_iff g⁻¹ _ _).2 h3
    rwa [← glMap_mul, ← glMap_mul, inv_mul_cancel, glMap_one] at this
  rw [relIndex_eq_pow_rank O K r A' g hg h3, relIndex_eq_pow_rank O K r A'ᵀ _ hgt h3', Matrix.transpose_map, Matrix.rank_transpose]

variable [Finite (IsLocalRing.ResidueField O)]

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hg`. Express the relevant statement in the definitionally equal form `glMap g (std O K r).1 ≤ (std O K r).1 at h1`. Express the relevant statement in the definitionally equal form `(glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = qRes O ^ k at h2`. Express the relevant statement in the definitionally equal form `IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 at h3`. Establish `hz` using `glMap_scalGL_std O K r ϖ u hϖ hu`.

Establish `h3' : glMap (scalGL u) (std O K r).1 ≤ glMap g (std O K r).1` using `hz ▸ h3`. Establish `eΦ : scalGL u * tinv g = (tinv (g⁻¹ * scalGL u))⁻¹`. Rewrite using `[map_mul, map_inv, tinv_scalGL', _root_.mul_inv_rev, inv_inv, inv_inv]`. Establish `ha : glMap (scalGL u * tinv g) (std O K r).1 ≤ (std O K r).1`. Rewrite using `[eΦ, glMap_tinv_inv_le_iff]`.

Use `(glMap_le_glMap_iff g⁻¹ _ _).2 h3'` as an intermediate fact. Rewrite `this` using `[← glMap_mul, ← glMap_mul, inv_mul_cancel, glMap_one]`. Then use the resulting hypothesis. Establish `e : glMap (scalGL u) (std O K r).1 = glMap (scalGL u * tinv g) (glMap (tinv g)⁻¹ (std O K r).1)`. Rewrite using `[← glMap_mul, mul_assoc, mul_inv_cancel, mul_one]`. Establish `hb : glMap (scalGL u) (std O K r).1 ≤ glMap (scalGL u * tinv g) (std O K r).1`.

Rewrite using `[e, glMap_le_glMap_iff, glMap_tinv_inv_le_iff]`. Conclude with `h1`. Establish `hidx1 : (glMap (scalGL u) (std O K r).1).toAddSubgroup.relIndex (glMap (scalGL u * tinv g) (std O K r).1).toAddSubgroup = qRes O ^ k`. Rewrite using `[e, relIndex_glMap, relIndex_tinv_inv g h1 h3, h2]`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex (glMap (scalGL u) (std O K r).1).toAddSubgroup (glMap (scalGL u * tinv g) (std O K r).1).toAddSubgroup (std O K r).1.toAddSubgroup hb ha`.

Establish `hmax` using `relIndex_maxMul (std O K r)`. Rewrite `hmax` using `[maxMul_val, ← hz]`. Rewrite `hmul` using `[hidx1, hmax]`. Use `⟨⟨ha, ?_⟩, hz ▸ hb⟩` and prove the remaining obligations. Establish `hq : 0 < qRes O ^ k` using `pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _`.

Use `Nat.eq_of_mul_eq_mul_left hq ?_` and prove the remaining obligations. Conclude with `hmul.trans (by rw [← pow_add, Nat.add_sub_cancel' hk])`.
-/
theorem dual_mem_subElem {k : ℕ} (hk : k ≤ r) (ϖ : O) (u : Kˣ) (hϖ : Irreducible ϖ)
    (hu : (u : K) = algebraMap O K ϖ) (g : GL (Fin r) K)
    (hg : g • std O K r ∈ subElem k (std O K r)) :
    (scalGL u * tinv g) • std O K r ∈ subElem (r - k) (std O K r) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  change glMap g (std O K r).1 ≤ (std O K r).1 at h1
  change (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = qRes O ^ k at h2
  change IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 at h3
  have hz := glMap_scalGL_std O K r ϖ u hϖ hu
  have h3' : glMap (scalGL u) (std O K r).1 ≤ glMap g (std O K r).1 := hz ▸ h3
  have eΦ : scalGL u * tinv g = (tinv (g⁻¹ * scalGL u))⁻¹ := by
    rw [map_mul, map_inv, tinv_scalGL', _root_.mul_inv_rev, inv_inv, inv_inv]
  have ha : glMap (scalGL u * tinv g) (std O K r).1 ≤ (std O K r).1 := by
    rw [eΦ, glMap_tinv_inv_le_iff]
    have := (glMap_le_glMap_iff g⁻¹ _ _).2 h3'
    rwa [← glMap_mul, ← glMap_mul, inv_mul_cancel, glMap_one] at this
  have e : glMap (scalGL u) (std O K r).1 =
      glMap (scalGL u * tinv g) (glMap (tinv g)⁻¹ (std O K r).1) := by
    rw [← glMap_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hb : glMap (scalGL u) (std O K r).1 ≤ glMap (scalGL u * tinv g) (std O K r).1 := by
    rw [e, glMap_le_glMap_iff, glMap_tinv_inv_le_iff]; exact h1
  have hidx1 : (glMap (scalGL u) (std O K r).1).toAddSubgroup.relIndex
      (glMap (scalGL u * tinv g) (std O K r).1).toAddSubgroup = qRes O ^ k := by
    rw [e, relIndex_glMap, relIndex_tinv_inv g h1 h3, h2]
  have hmul := AddSubgroup.relIndex_mul_relIndex (glMap (scalGL u) (std O K r).1).toAddSubgroup
    (glMap (scalGL u * tinv g) (std O K r).1).toAddSubgroup (std O K r).1.toAddSubgroup hb ha
  have hmax := relIndex_maxMul (std O K r)
  rw [maxMul_val, ← hz] at hmax
  rw [hidx1, hmax] at hmul
  refine ⟨⟨ha, ?_⟩, hz ▸ hb⟩
  have hq : 0 < qRes O ^ k := pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  exact hmul.trans (by rw [← pow_add, Nat.add_sub_cancel' hk])

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hh`. Take `⟨g, hg, rfl⟩` from `hh`. Take `⟨M, hM, hMe⟩` from `hs.mapsTo (Finset.mem_coe.2 hg)`.

Establish `hM' : g • std O K r ∈ subElem k (std O K r)`. Establish `: M = g • std O K r` using `Subtype.ext hMe`. Rewrite using `[← this]` and apply the resulting hypothesis. Conclude with `⟨_, dual_mem_subElem hk ϖ u hϖ hu g hM', rfl⟩`. Introduce `h1 hh1 h2 hh2 e`.

Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hh1 hh2`. Take `⟨g1, hg1, rfl⟩` from `hh1`. Take `⟨g2, hg2, rfl⟩` from `hh2`. Simplify using `only at e`. Rewrite `e` using `[glMap_eq_glMap_iff]`.

Establish `e1 : (scalGL u * tinv g1)⁻¹ * (scalGL u * tinv g2) = tinv (g1⁻¹ * g2)`. Rewrite using `[map_mul, map_inv, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`. Rewrite `e` using `[e1]`. Establish `e2` using `glMap_tinv_std _ e`. Rewrite `e2` using `[tinv_tinv, ← glMap_eq_glMap_iff]`.

Rewrite using `[hs.injOn (Finset.mem_coe.2 hg1) (Finset.mem_coe.2 hg2) e2]`. Introduce and unpack `_ ⟨M, hM, rfl⟩`. Take `⟨h, hh⟩` from `exists_glMap_std_eq O K r M`. Establish `hMh : M = h • std O K r` using `Subtype.ext hh.symm`. Use `dual_mem_subElem (Nat.sub_le r k) ϖ u hϖ hu h (hMh ▸ hM)` as an intermediate fact.

Rewrite `this` using `[Nat.sub_sub_self hk]`. Take `⟨g, hg, hge⟩` from `hs.surjOn ⟨_, this, rfl⟩`. Use `⟨scalGL u * tinv g, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `glMap (scalGL u * tinv g) (std O K r).1 = M.1`. Rewrite using `[← hh]`.

Express the relevant statement in the definitionally equal form `glMap g (std O K r).1 = glMap (scalGL u * tinv h) (std O K r).1 at hge`. Rewrite `hge`, the goal using `[glMap_eq_glMap_iff]`. Establish `h4` using `glMap_tinv_std _ hge`. Establish `e2 : tinv (g⁻¹ * (scalGL u * tinv h)) = (scalGL u * tinv g)⁻¹ * h`. Rewrite using `[map_mul, map_mul, map_inv, tinv_scalGL', tinv_tinv, _root_.mul_inv_rev, mul_assoc]`.

Rewrite `h4` using `[e2]`. Then use the resulting hypothesis.
-/
theorem bijOn_dual [DecidableEq (GL (Fin r) K)] {k : ℕ} (hk : k ≤ r) (ϖ : O) (u : Kˣ)
    (hϖ : Irreducible ϖ) (hu : (u : K) = algebraMap O K ϖ) (s : Finset (GL (Fin r) K))
    (hs : Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r))) :
    Set.BijOn (fun g => glMap g (std O K r).1) (s.image fun g => scalGL u * tinv g)
      (Subtype.val '' subElem (r - k) (std O K r)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    obtain ⟨M, hM, hMe⟩ := hs.mapsTo (Finset.mem_coe.2 hg)
    have hM' : g • std O K r ∈ subElem k (std O K r) := by
      have : M = g • std O K r := Subtype.ext hMe
      rwa [← this]
    exact ⟨_, dual_mem_subElem hk ϖ u hϖ hu g hM', rfl⟩
  · intro h1 hh1 h2 hh2 e
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hh1 hh2
    obtain ⟨g1, hg1, rfl⟩ := hh1
    obtain ⟨g2, hg2, rfl⟩ := hh2
    simp only at e
    rw [glMap_eq_glMap_iff] at e
    have e1 : (scalGL u * tinv g1)⁻¹ * (scalGL u * tinv g2) = tinv (g1⁻¹ * g2) := by
      rw [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    rw [e1] at e
    have e2 := glMap_tinv_std _ e
    rw [tinv_tinv, ← glMap_eq_glMap_iff] at e2
    rw [hs.injOn (Finset.mem_coe.2 hg1) (Finset.mem_coe.2 hg2) e2]
  · rintro _ ⟨M, hM, rfl⟩
    obtain ⟨h, hh⟩ := exists_glMap_std_eq O K r M
    have hMh : M = h • std O K r := Subtype.ext hh.symm
    have := dual_mem_subElem (Nat.sub_le r k) ϖ u hϖ hu h (hMh ▸ hM)
    rw [Nat.sub_sub_self hk] at this
    obtain ⟨g, hg, hge⟩ := hs.surjOn ⟨_, this, rfl⟩
    refine ⟨scalGL u * tinv g, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg), ?_⟩
    change glMap (scalGL u * tinv g) (std O K r).1 = M.1
    rw [← hh]
    change glMap g (std O K r).1 = glMap (scalGL u * tinv h) (std O K r).1 at hge
    rw [glMap_eq_glMap_iff] at hge ⊢
    have h4 := glMap_tinv_std _ hge
    have e2 : tinv (g⁻¹ * (scalGL u * tinv h)) = (scalGL u * tinv g)⁻¹ * h := by
      rw [map_mul, map_mul, map_inv, tinv_scalGL', tinv_tinv, _root_.mul_inv_rev, mul_assoc]
    rwa [e2] at h4

end Lattices

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r β hβ`. Take `⟨hc, V, i1, i2, ρ, v, hρ, hv, hfix, hT⟩` from `hβ`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `h0 : algebraMap O K ϖ ≠ 0` using `by simpa using hϖ.ne_zero`. Set `u : Kˣ` to `Units.mk0 _ h0`.

Establish `hu : (u : K) = algebraMap O K ϖ` using `rfl`. Establish `hz` using `glMap_scalGL_std O K r ϖ u hϖ hu`. Establish `hzv : ρ (scalGL u) v = β.esymm r • v`. Use `hT r le_rfl {scalGL u} (by` as an intermediate fact. Establish `e1 : Subtype.val '' ({maxMul (std O K r)} : Set (Lat O K r)) = {glMap (scalGL u) (std O K r).1}`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨M, hM, rfl⟩`. Establish `hM' : M = maxMul (std O K r)` using `hM`. Substitute `hM'` using the available equality.

Use `show IsLocalRing.maximalIdeal O • (std O K r).1 = glMap (scalGL u) (std O K r).1`. Conclude with `hz.symm`. Introduce `hx`. Establish `hx' : x = glMap (scalGL u) (std O K r).1` using `hx`. Conclude with `⟨maxMul (std O K r), rfl, by rw [hx', hz]; rfl⟩`.

Rewrite using `[Finset.coe_singleton, subElem_top, e1]`. Conclude with `Set.bijOn_singleton.2 rfl)`. Simplify using `using this`. Establish `hr : β.esymm r ≠ 0`. Introduce `h`.

Use `hρ (scalGL u) v` as an intermediate fact. Rewrite `this` using `[hzv, h, zero_smul, norm_zero]`. Conclude with `hv (norm_eq_zero.1 this.symm)`. Establish `hprod : β.esymm r = β.prod`. Rewrite using `[← hc, Multiset.esymm, Multiset.powersetCard_self]`.

Simplify using the standard rewrite rules. Establish `hne : ∀ b ∈ β, b ≠ 0` using `fun b hb h => hr (by rw [hprod]; exact Multiset.prod_eq_zero (h ▸ hb))`. Use `⟨by simp [hc], V, i1, i2, ρ.comp tinv, v, fun g x => hρ _ x, hv, fun g hg => hfix _ (glMap_tinv_std g hg), ?_⟩` and prove the remaining obligations. Introduce `k hk s hs`. Establish `hb` using `bijOn_dual hk ϖ u hϖ hu s hs`.

Establish `hT'` using `hT (r - k) (Nat.sub_le r k) _ hb`. Rewrite `hT'` using `[Finset.sum_image (fun a _ b _ e => tinv_injective (mul_left_cancel e))]`. Establish `hterm : ∀ g, ρ (scalGL u * tinv g) v = β.esymm r • (ρ.comp tinv) g v`. Introduce `g`. Rewrite using `[scalGL_comm, map_mul, Module.End.mul_apply, hzv, map_smul]`.

Both sides reduce to the same expression. Simplify using `only [hterm, ← Finset.smul_sum] at hT'`. Use `smul_right_injective V hr ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hT', smul_smul]`.

Use `congr 1`. Establish `hM` using `esymm_inv_mul_esymm_card β hne (hc ▸ hk)`. Rewrite `hM` using `[hc]`. Rewrite using `[← hM]`. Establish `: ((r - k : ℕ) : ℝ) * ((r : ℝ) - ((r - k : ℕ) : ℝ)) / 2 = (k : ℝ) * ((r : ℝ) - k) / 2`.

Rewrite using `[Nat.cast_sub hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isUnitarySatake_map_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (β : Multiset ℂ), IsUnitarySatake O K r β → IsUnitarySatake O K r (β.map (·⁻¹)) := by
  intro O K _ _ _ _ _ _ _ r β hβ
  classical
  obtain ⟨hc, V, i1, i2, ρ, v, hρ, hv, hfix, hT⟩ := hβ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  let u : Kˣ := Units.mk0 _ h0
  have hu : (u : K) = algebraMap O K ϖ := rfl
  have hz := glMap_scalGL_std O K r ϖ u hϖ hu
  have hzv : ρ (scalGL u) v = β.esymm r • v := by
    have := hT r le_rfl {scalGL u} (by
      have e1 : Subtype.val '' ({maxMul (std O K r)} : Set (Lat O K r)) =
          {glMap (scalGL u) (std O K r).1} := by
        ext x
        constructor
        · rintro ⟨M, hM, rfl⟩
          have hM' : M = maxMul (std O K r) := hM
          subst hM'
          show IsLocalRing.maximalIdeal O • (std O K r).1 = glMap (scalGL u) (std O K r).1
          exact hz.symm
        · intro hx
          have hx' : x = glMap (scalGL u) (std O K r).1 := hx
          exact ⟨maxMul (std O K r), rfl, by rw [hx', hz]; rfl⟩
      rw [Finset.coe_singleton, subElem_top, e1]
      exact Set.bijOn_singleton.2 rfl)
    simpa using this
  have hr : β.esymm r ≠ 0 := by
    intro h
    have := hρ (scalGL u) v
    rw [hzv, h, zero_smul, norm_zero] at this
    exact hv (norm_eq_zero.1 this.symm)
  have hprod : β.esymm r = β.prod := by
    rw [← hc, Multiset.esymm, Multiset.powersetCard_self]; simp
  have hne : ∀ b ∈ β, b ≠ 0 := fun b hb h => hr (by rw [hprod]; exact Multiset.prod_eq_zero (h ▸ hb))
  refine ⟨by simp [hc], V, i1, i2, ρ.comp tinv, v, fun g x => hρ _ x, hv,
    fun g hg => hfix _ (glMap_tinv_std g hg), ?_⟩
  intro k hk s hs
  have hb := bijOn_dual hk ϖ u hϖ hu s hs
  have hT' := hT (r - k) (Nat.sub_le r k) _ hb
  rw [Finset.sum_image (fun a _ b _ e => tinv_injective (mul_left_cancel e))] at hT'
  have hterm : ∀ g, ρ (scalGL u * tinv g) v = β.esymm r • (ρ.comp tinv) g v := by
    intro g
    rw [scalGL_comm, map_mul, Module.End.mul_apply, hzv, map_smul]; rfl
  simp only [hterm, ← Finset.smul_sum] at hT'
  refine smul_right_injective V hr ?_
  simp only
  rw [hT', smul_smul]
  congr 1
  have hM := esymm_inv_mul_esymm_card β hne (hc ▸ hk)
  rw [hc] at hM
  rw [← hM]
  have : ((r - k : ℕ) : ℝ) * ((r : ℝ) - ((r - k : ℕ) : ℝ)) / 2 = (k : ℝ) * ((r : ℝ) - k) / 2 := by
    rw [Nat.cast_sub hk]; ring
  rw [this]; ring

end GlobalTheory.SatakeInv
