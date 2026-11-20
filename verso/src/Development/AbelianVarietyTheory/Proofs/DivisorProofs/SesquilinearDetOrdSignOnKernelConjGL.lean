import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

/- English proof (translation)
Establish `hx' : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Establish `hy' : Valued.v y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`. Establish `hxy' : Valued.v (x * y) ≠ 0` using `(Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)`. Unfold `ordL`. Rewrite using `[dif_neg hx', dif_neg hy', dif_neg hxy']`.

Establish `: WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy'`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]`. Rewrite using `[this, toAdd_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordL_mul_of_ne [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hσd : σ d ≠ 0` using `(map_ne_zero σ).2 hd`. Establish `hσo : ordL (σ d) = ordL d`. Unfold `ordL`.

Simplify using `only [hσ]`. Rewrite using `[ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul, (even_two_mul (ordL d)).neg_one_zpow, one_mul]`.
-/
theorem sign_mul_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {d : K} (hd : d ≠ 0) (x : K) :
    (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_eq_mul (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (v : ι → Fin n → K) :
    (Matrix.of fun i j => hform σ H (v i) (v j)) =
      cT σ (Matrix.of fun p i => v i p) * H * Matrix.of fun p i => v i p := by
  ext i j
  simp only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use extensionality with `p i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.
-/
theorem cols_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {ι : Type} (v : ι → Fin n → K) :
    (Matrix.of fun p i => (M *ᵥ v i) p) = M * Matrix.of fun p i => v i p := by
  ext p i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/- English proof (translation)
Unfold `cT`. Rewrite using `[Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_cT (σ : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K) :
    (cT σ T).det = σ T.det := by
  unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

/- English proof (translation)
Use `set T := b.toMatrix b' with hT`. Establish `hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T`. Use extensionality with `p j`. Establish `hs` using `congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs`.

Rewrite using `[Matrix.of_apply, ← hs, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]`. Establish `hTT : T * b'.toMatrix b = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip b b'`. Establish `hd : T.det ≠ 0`.

Introduce `h0`. Use `congrArg Matrix.det hTT` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`. Use `⟨T.det, hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol, cT_mul]`. Use `set B := Matrix.of fun p i => (b i : Fin n → K) p`. Rewrite using `[show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]`. Simplify using `only [Matrix.det_mul, det_cT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_det_change (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b b' : Module.Basis ι K W) :
    ∃ d : K, d ≠ 0 ∧
      (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
        σ d * d * (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set T := b.toMatrix b' with hT
  have hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T := by
    ext p j
    have hs := congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [Matrix.of_apply, ← hs, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]
  have hTT : T * b'.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b'
  have hd : T.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨T.det, hd, ?_⟩
  rw [gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol,
    cT_mul]
  set B := Matrix.of fun p i => (b i : Fin n → K) p
  rw [show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]
  simp only [Matrix.det_mul, det_cT]
  ring

/- English proof (translation)
Use `set e : ι' ≃ ι := b'.indexEquiv b`. Establish `hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) = (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e`. Use extensionality with `i j`. Simplify using `[Module.Basis.reindex_apply]`. Take `⟨d, hd, hdet⟩` from `gram_det_change σ H W (b.reindex e.symm) b'`.

Rewrite using `[hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]`.
-/
theorem sign_basis [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι K W) (b' : Module.Basis ι' K W) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set e : ι' ≃ ι := b'.indexEquiv b
  have hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) =
      (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e := by
    ext i j
    simp [Module.Basis.reindex_apply]
  obtain ⟨d, hd, hdet⟩ := gram_det_change σ H W (b.reindex e.symm) b'
  rw [hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]

/- English proof (translation)
Establish `hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`.

Rewrite using `[pow_succ, ih, pow_succ]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range]`. Simplify using `only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem aeval_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    aeval (k⁻¹ * a * k).val Q = (k⁻¹).val * aeval a.val Q * k.val := by
  have hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UnitaryClasses.SgnConj

namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `congrArg (fun y => k.val *ᵥ y) h` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`. Introduce `h`. Rewrite using `[h, Matrix.mulVec_zero]`.
-/
theorem ker_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) =
      (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).comap (Matrix.toLin' k.val) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun y => k.val *ᵥ y) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_zero]

def invEquiv {n : ℕ} (k : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' (k⁻¹).val) (Matrix.toLin' k.val)
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])

/- English proof (translation)
Rewrite using `[ker_conj, Submodule.map_equiv_eq_comap_symm]`. Both sides reduce to the same expression.
-/
theorem map_invEquiv {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).map (invEquiv k : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) := by
  rw [ker_conj, Submodule.map_equiv_eq_comap_symm]
  rfl

/- English proof (translation)
Introduce `K _ _ σ hσ n Q a k`. Use `set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))`. Use `set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))`. Set `b0` to `Module.finBasis K V`. Set `b'' : Module.Basis (Fin (Module.finrank K V)) K V'` to `b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))`.

Establish `hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K)`. Introduce `i`. Simplify using `[b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]`. Unfold `sgnOn gramOn`. Rewrite using `[sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]`.

Use `congr 3`. Rewrite using `[gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]`. Simplify using `only [hb'']`. Rewrite using `[cols_mulVec, cT_mul]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.
-/
theorem sgnOn_conj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K),
    sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  intro K _ _ σ hσ n Q a k
  set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))
  set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))
  let b0 := Module.finBasis K V
  let b'' : Module.Basis (Fin (Module.finrank K V)) K V' :=
    b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))
  have hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K) := by
    intro i
    simp [b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]
  unfold sgnOn gramOn
  rw [sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]
  congr 3
  rw [gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]
  simp only [hb'']
  rw [cols_mulVec, cT_mul]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.UnitaryClasses.SgnConj
