import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthDet

namespace KStar.Selmer

open Matrix Module

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

private noncomputable def fracInv (K : Type*) [Field K] [Algebra O K] (Φ : Matrix n n O) :
    (n → O) →ₗ[O] (n → FracMod O K) :=
  LinearMap.pi fun i => (1 : Submodule O K).mkQ ∘ₗ
    LinearMap.toSpanSingleton O K (algebraMap O K Φ.det)⁻¹ ∘ₗ LinearMap.proj i ∘ₗ
      Φ.adjugate.mulVecLin

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem fracInv_apply (Φ : Matrix n n O) (y : n → O) (i : n) :
    fracInv K Φ y i =
      (1 : Submodule O K).mkQ ((Φ.adjugate *ᵥ y) i • (algebraMap O K Φ.det)⁻¹) := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`.
-/
private theorem mkQ_eq_zero_iff (z : K) :
    (1 : Submodule O K).mkQ z = 0 ↔ ∃ y : O, algebraMap O K y = z := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]

omit [IsDiscreteValuationRing O] in
/- English proof (translation)
Establish `hK : algebraMap O K Φ.det ≠ 0` using `fun h0 => h (IsFractionRing.injective O K (by rw [h0, map_zero]))`. Use extensionality with `y`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `: ∀ i, ∃ x : O, algebraMap O K x = (Φ.adjugate *ᵥ y) i • (algebraMap O K Φ.det)⁻¹` using `fun i => (mkQ_eq_zero_iff _).1 (congrFun hy i)`. Use `choose x hx using this`. Establish `h1 : Φ.det • x = Φ.adjugate *ᵥ y`. Use function extensionality and compare the values at `i`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, hx, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `h2 : Φ.det • (Φ *ᵥ x) = Φ.det • y`. Rewrite using `[← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Use function extensionality and compare the values at `i`. Conclude with `mul_left_cancel₀ h (congrFun h2 i)`. Introduce and unpack `⟨x, rfl⟩`. Use function extensionality and compare the values at `i`. Rewrite using `[fracInv_apply, Pi.zero_apply, mkQ_eq_zero_iff]`.

Use `⟨x i, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem ker_fracInv (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    LinearMap.ker (fracInv K Φ) = LinearMap.range Φ.mulVecLin := by
  have hK : algebraMap O K Φ.det ≠ 0 := fun h0 =>
    h (IsFractionRing.injective O K (by rw [h0, map_zero]))
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hy
    have : ∀ i, ∃ x : O, algebraMap O K x =
        (Φ.adjugate *ᵥ y) i • (algebraMap O K Φ.det)⁻¹ := fun i =>
      (mkQ_eq_zero_iff _).1 (congrFun hy i)
    choose x hx using this
    have h1 : Φ.det • x = Φ.adjugate *ᵥ y := by
      funext i
      apply IsFractionRing.injective O K
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hx, Algebra.smul_def]
      field_simp
    refine ⟨x, ?_⟩
    have h2 : Φ.det • (Φ *ᵥ x) = Φ.det • y := by
      rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    exact mul_left_cancel₀ h (congrFun h2 i)
  · rintro ⟨x, rfl⟩
    funext i
    rw [fracInv_apply, Pi.zero_apply, mkQ_eq_zero_iff]
    refine ⟨x i, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
    field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Establish `hK : algebraMap O K Φ.det ≠ 0` using `fun h0 => h (IsFractionRing.injective O K (by rw [h0, map_zero]))`. Use extensionality with `w`. Rewrite using `[H1c, LinearMap.mem_ker, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Use function extensionality and compare the values at `i`. Rewrite using `[coefMap_apply, Pi.zero_apply]`. Simplify using `only [fracInv_apply, ← map_smul, ← map_sum]`. Rewrite using `[mkQ_eq_zero_iff]`. Use `⟨y i, ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_smul, ← Finset.sum_smul]`. Establish `h2 : ∑ j, Φ i j * (Φ.adjugate *ᵥ y) j = Φ.det * y i`. Establish `: (Φ *ᵥ (Φ.adjugate *ᵥ y)) i = Φ.det * y i`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]`. Conclude with `this`.

Rewrite using `[h2, Algebra.smul_def, map_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `hw choose z hz using fun i => (1 : Submodule O K).mkQ_surjective (w i)`. Establish `: ∀ i, ∃ y : O, algebraMap O K y = ∑ j, Φ i j • z j` using `fun i => by`. Rewrite using `[← mkQ_eq_zero_iff, map_sum]`.

Use `congrFun hw i` as an intermediate fact. Rewrite `this` using `[coefMap_apply, Pi.zero_apply]`. Simplify `this` using `only [map_smul, hz]`. Use `choose y hy using this`. Use `⟨y, funext fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[fracInv_apply, ← hz]`. Use `congr 1`. Establish `h3 : algebraMap O K ((Φ.adjugate *ᵥ y) i) = algebraMap O K Φ.det * z i`. Establish `h4 : algebraMap O K ((Φ.adjugate *ᵥ y) i) = ∑ k, (Φ.adjugate * Φ) i k • z k`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, hy, Matrix.mul_apply, Finset.sum_smul, ← Algebra.smul_def, Finset.smul_sum, smul_smul]`.

Conclude with `Finset.sum_comm`. Rewrite using `[h4, Matrix.adjugate_mul, ← Algebra.smul_def]`. Simplify using `[Matrix.one_apply, ite_smul]`. Rewrite using `[Algebra.smul_def, h3]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem range_fracInv (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    LinearMap.range (fracInv K Φ) = H1c Φ (FracMod O K) := by
  have hK : algebraMap O K Φ.det ≠ 0 := fun h0 =>
    h (IsFractionRing.injective O K (by rw [h0, map_zero]))
  ext w
  rw [H1c, LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    funext i
    rw [coefMap_apply, Pi.zero_apply]
    simp only [fracInv_apply, ← map_smul, ← map_sum]
    rw [mkQ_eq_zero_iff]
    refine ⟨y i, ?_⟩
    simp only [smul_smul, ← Finset.sum_smul]
    have h2 : ∑ j, Φ i j * (Φ.adjugate *ᵥ y) j = Φ.det * y i := by
      have : (Φ *ᵥ (Φ.adjugate *ᵥ y)) i = Φ.det * y i := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.smul_apply, smul_eq_mul]
      exact this
    rw [h2, Algebra.smul_def, map_mul]
    field_simp
  · intro hw
    choose z hz using fun i => (1 : Submodule O K).mkQ_surjective (w i)
    have : ∀ i, ∃ y : O, algebraMap O K y = ∑ j, Φ i j • z j := fun i => by
      rw [← mkQ_eq_zero_iff, map_sum]
      have := congrFun hw i
      rw [coefMap_apply, Pi.zero_apply] at this
      simpa only [map_smul, hz] using this
    choose y hy using this
    refine ⟨y, funext fun i => ?_⟩
    rw [fracInv_apply, ← hz]
    congr 1
    have h3 : algebraMap O K ((Φ.adjugate *ᵥ y) i) = algebraMap O K Φ.det * z i := by
      have h4 : algebraMap O K ((Φ.adjugate *ᵥ y) i) =
          ∑ k, (Φ.adjugate * Φ) i k • z k := by
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hy, Matrix.mul_apply,
          Finset.sum_smul, ← Algebra.smul_def, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      rw [h4, Matrix.adjugate_mul, ← Algebra.smul_def]
      simp [Matrix.one_apply, ite_smul]
    rw [Algebra.smul_def, h3]
    field_simp

/- English proof (translation)
Rewrite using `[← length_cokernel_eq_addVal_det, ← range_fracInv Φ h, ← (fracInv K Φ).quotKerEquivRange.length_eq]`. Conclude with `(Submodule.quotEquivOfEq _ _ (ker_fracInv Φ h)).length_eq`.
-/
private theorem length_kernel_fraction_module_of_det_ne_zero (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    Module.length O (H1c Φ (FracMod O K)) = IsDiscreteValuationRing.addVal O Φ.det := by
  rw [← length_cokernel_eq_addVal_det, ← range_fracInv Φ h,
    ← (fracInv K Φ).quotKerEquivRange.length_eq]
  exact (Submodule.quotEquivOfEq _ _ (ker_fracInv Φ h)).length_eq

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Rewrite using `[ENat.eq_top_iff_forall_ge]`. Introduce `k`. Establish `hd : (Matrix.of fun (_ _ : Unit) => ϖ ^ k).det = ϖ ^ k` using `by simp`. Use `length_kernel_fraction_module_of_det_ne_zero (K := K) (Matrix.of fun (_ _ : Unit) => ϖ ^ k) (by rw [hd]; exact pow_ne_zero _ hϖ.ne_zero)` as an intermediate fact.

Rewrite `this` using `[hd, hϖ.addVal_pow]`. Rewrite using `[← this]`. Conclude with `Module.length_le_of_injective _ (Submodule.subtype_injective _)`.
-/
private theorem length_fracMod : Module.length O (Unit → FracMod O K) = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  have hd : (Matrix.of fun (_ _ : Unit) => ϖ ^ k).det = ϖ ^ k := by simp
  have := length_kernel_fraction_module_of_det_ne_zero (K := K) (Matrix.of fun (_ _ : Unit) => ϖ ^ k)
    (by rw [hd]; exact pow_ne_zero _ hϖ.ne_zero)
  rw [hd, hϖ.addVal_pow] at this
  rw [← this]
  exact Module.length_le_of_injective _ (Submodule.subtype_injective _)

/- English proof (translation)
Distinguish the cases in `h : Φ.det = 0`. Rewrite using `[h, IsDiscreteValuationRing.addVal_zero, eq_top_iff, ← length_fracMod (O := O) (K := K)]`. Take `⟨v, hv, hΦ⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hv`. Establish `hK : algebraMap O K (v i) ≠ 0` using `fun h0 => hi (IsFractionRing.injective O K (by rw [h0, Pi.zero_apply, map_zero]))`.

Use `Module.length_le_of_surjective ((LinearMap.pi fun _ : Unit => LinearMap.proj i) ∘ₗ (H1c Φ (FracMod O K)).subtype) ?_` and prove the remaining obligations. Introduce `t`. Take `⟨z, hz⟩` from `(1 : Submodule O K).mkQ_surjective (t ())`. Use `⟨⟨fun j => v j • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[H1c, LinearMap.mem_ker]`.

Use function extensionality and compare the values at `a`. Rewrite using `[coefMap_apply]`. Simplify using `only [smul_smul, ← Finset.sum_smul]`. Establish `: ∑ j, Φ a j * v j = 0` using `congrFun hΦ a`. Rewrite using `[this, zero_smul, Pi.zero_apply]`.

Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `v i • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z) = t ()`. Rewrite using `[← map_smul, ← hz, Algebra.smul_def, mul_inv_cancel_left₀ hK]`. Conclude with `length_kernel_fraction_module_of_det_ne_zero Φ h`.
-/
theorem length_kernel_fraction_module_eq_addVal_det (Φ : Matrix n n O) :
    Module.length O (H1c Φ (FracMod O K)) = IsDiscreteValuationRing.addVal O Φ.det := by
  by_cases h : Φ.det = 0
  · rw [h, IsDiscreteValuationRing.addVal_zero, eq_top_iff, ← length_fracMod (O := O) (K := K)]
    obtain ⟨v, hv, hΦ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have hK : algebraMap O K (v i) ≠ 0 := fun h0 =>
      hi (IsFractionRing.injective O K (by rw [h0, Pi.zero_apply, map_zero]))
    refine Module.length_le_of_surjective
      ((LinearMap.pi fun _ : Unit => LinearMap.proj i) ∘ₗ (H1c Φ (FracMod O K)).subtype) ?_
    intro t
    obtain ⟨z, hz⟩ := (1 : Submodule O K).mkQ_surjective (t ())
    refine ⟨⟨fun j => v j • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z), ?_⟩, ?_⟩
    · rw [H1c, LinearMap.mem_ker]
      funext a
      rw [coefMap_apply]
      simp only [smul_smul, ← Finset.sum_smul]
      have : ∑ j, Φ a j * v j = 0 := congrFun hΦ a
      rw [this, zero_smul, Pi.zero_apply]
    · funext u
      change v i • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z) = t ()
      rw [← map_smul, ← hz, Algebra.smul_def, mul_inv_cancel_left₀ hK]
  · exact length_kernel_fraction_module_of_det_ne_zero Φ h

end KStar.Selmer
