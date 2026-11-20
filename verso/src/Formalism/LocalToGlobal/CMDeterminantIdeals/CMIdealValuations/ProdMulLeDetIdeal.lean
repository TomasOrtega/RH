import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace A2

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))`.
-/
theorem absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))

/- English proof (translation)
Establish `hJ : J ≠ 0`. Introduce and unpack `rfl`. Conclude with `hI (FractionalIdeal.le_zero_iff.1 hIJ)`. Establish `hX : I * J⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨X, hX'⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX`. Establish `hdec : I = J * (I * J⁻¹)`. Rewrite using `[mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]`. Establish `hIJ0 : I * J⁻¹ ≠ 0` using `mul_ne_zero hI (inv_ne_zero hJ)`. Establish `hX0 : X ≠ ⊥`.

Introduce and unpack `rfl`. Apply `hIJ0` to reduce the goal to its premises. Rewrite using `[← hX']`. Conclude with `FractionalIdeal.coeIdeal_bot`. Establish `hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹)`.

Rewrite using `[← hX', FractionalIdeal.coeIdeal_absNorm]`. Establish `: Ideal.absNorm X ≠ 0` using `fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem absNorm_anti' {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact hI (FractionalIdeal.le_zero_iff.1 hIJ)
  have hX : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hIJ le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : I = J * (I * J⁻¹) := by
    rw [mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  have hIJ0 : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hX0 : X ≠ ⊥ := by
    rintro rfl
    apply hIJ0
    rw [← hX']
    exact FractionalIdeal.coeIdeal_bot
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hX', FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  calc FractionalIdeal.absNorm J = FractionalIdeal.absNorm J * 1 := (mul_one _).symm
    _ ≤ FractionalIdeal.absNorm J * FractionalIdeal.absNorm (I * J⁻¹) :=
        mul_le_mul_of_nonneg_left hN (FractionalIdeal.absNorm_nonneg _)
    _ = FractionalIdeal.absNorm I := by rw [← map_mul, ← hdec]

/- English proof (translation)
Establish `h2` using `congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)`. Simplify using `only [norm_prod] at h2`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]`. Simplify using the standard rewrite rules.
-/
theorem abs_norm_eq_prod (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]
  simp

/- English proof (translation)
Rewrite using `[FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]`.
-/
theorem absNorm_span_real (x : K) :
    ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]

/- English proof (translation)
Simplify using `using (Complex.lt_def.1 h.det_pos).1`.
-/
theorem det_re_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosDef) : 0 < A.det.re := by
  simpa using (Complex.lt_def.1 h.det_pos).1

/- English proof (translation)
Establish `hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K), IsLocalization.IsInteger (𝓞 K) (a • b)` using `fun i => FractionalIdeal.isFractional_of_fg (hM.map _)`. Use `choose a ha hb using hc`. Use `⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hxi` using `hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]`.

Conclude with `IsLocalization.isInteger_smul hxi`.
-/
theorem exists_den {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K)) (hM : M.FG) :
    ∃ a ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (a • x i) := by
  have hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K),
      IsLocalization.IsInteger (𝓞 K) (a • b) :=
    fun i => FractionalIdeal.isFractional_of_fg (hM.map _)
  choose a ha hb using hc
  refine ⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩
  have hxi := hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact IsLocalization.isInteger_smul hxi

/- English proof (translation)
Establish `hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j` using `fun i j => hx i j`. Use `choose y hy using hx'`. Use `⟨(Matrix.of y).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[hy]`.
-/
theorem isInteger_det {m : ℕ} (x : Fin m → Fin m → K) (hx : ∀ i j, IsLocalization.IsInteger (𝓞 K) (x i j)) :
    IsLocalization.IsInteger (𝓞 K) (Matrix.of x).det := by
  have hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j := fun i j => hx i j
  choose y hy using hx'
  refine ⟨(Matrix.of y).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hy]

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `exists_den L.M hM`. Use `⟨a ^ m, pow_mem ha m, fun b hb => ?_⟩` and prove the remaining obligations. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem d hd`. Take `⟨x, hx, rfl⟩` from `hd`.

Establish `: (a ^ m) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det`. Rewrite using `[show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by`. Use extensionality with `i j`. Simplify using `[Algebra.smul_def]]`. Rewrite using `[Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]`.

Rewrite using `[this]`. Conclude with `isInteger_det _ fun i j => hint _ (hx i) j`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `IsLocalization.isInteger_add hx hy`.

Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `IsLocalization.isInteger_smul hx`.
-/
theorem detSub_isFractional {m : ℕ} (L : MLat K m) (hM : L.M.FG) : IsFractional (𝓞 K)⁰ L.detSub := by
  obtain ⟨a, ha, hint⟩ := exists_den L.M hM
  refine ⟨a ^ m, pow_mem ha m, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ m) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

/- English proof (translation)
Establish `e : L.detIdeal = ⟨L.detSub, h⟩` using `dif_pos h`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem detIdeal_coe {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by
  have e : L.detIdeal = ⟨L.detSub, h⟩ := dif_pos h
  rw [e]
  rfl

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem det_mem {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Take `⟨s, hs, hspan, hli⟩` from `exists_linearIndependent K (M : Set (Fin m → K))`. Set `B` to `Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))`. Set `e` to `B.indexEquiv (Pi.basisFun K (Fin m))`. Use `⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩` and prove the remaining obligations. Establish `hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K))` using `hli.comp _ e.symm.injective`.

Establish `: IsUnit (Matrix.of fun i => (e.symm i : Fin m → K))` using `Matrix.linearIndependent_rows_iff_isUnit.1 hli'`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero`.
-/
theorem exists_det_ne {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K))
    (hM : Submodule.span K (M : Set (Fin m → K)) = ⊤) :
    ∃ x : Fin m → Fin m → K, (∀ i, x i ∈ M) ∧ (Matrix.of x).det ≠ 0 := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (M : Set (Fin m → K))
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))
  let e := B.indexEquiv (Pi.basisFun K (Fin m))
  refine ⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩
  have hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K)) := hli.comp _ e.symm.injective
  have : IsUnit (Matrix.of fun i => (e.symm i : Fin m → K)) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

/- English proof (translation)
Establish `hf` using `detSub_isFractional L hL.1`. Take `⟨x, hx, hd⟩` from `exists_det_ne L.M hL.2.1`. Introduce `h0`. Establish `hmem : (Matrix.of x).det ∈ (L.detIdeal : Submodule (𝓞 K) K)`. Rewrite using `[detIdeal_coe L hf]`.

Conclude with `det_mem L x hx`. Rewrite `hmem` using `[h0]`. Conclude with `hd ((FractionalIdeal.mem_zero_iff _).1 hmem)`.
-/
theorem detIdeal_ne_zero {m : ℕ} (L : MLat K m) (hL : L.Good) : L.detIdeal ≠ 0 := by
  have hf := detSub_isFractional L hL.1
  obtain ⟨x, hx, hd⟩ := exists_det_ne L.M hL.2.1
  intro h0
  have hmem : (Matrix.of x).det ∈ (L.detIdeal : Submodule (𝓞 K) K) := by
    rw [detIdeal_coe L hf]; exact det_mem L x hx
  rw [h0] at hmem
  exact hd ((FractionalIdeal.mem_zero_iff _).1 hmem)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem deg_detLine {m : ℕ} (L : MLat K m) : L.detLine.deg =
    -Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) - ∑ σ, Real.log (Real.sqrt (L.H σ).det.re) := rfl

end A2

open A2 in
/- English proof (translation)
Introduce `K _ _ m L hL`. Use `⟨detSub_isFractional L hL.1, ?_⟩` and prove the remaining obligations. Use `show L.detIdeal ≠ 0 ∧ ∀ σ, 0 < Real.sqrt (L.H σ).det.re`. Conclude with `⟨detIdeal_ne_zero L hL, fun σ => Real.sqrt_pos.2 (det_re_pos (hL.2.2 σ))⟩`.
-/
theorem detLineAdmissible : DetGood := by
  intro K _ _ m L hL
  refine ⟨detSub_isFractional L hL.1, ?_⟩
  show L.detIdeal ≠ 0 ∧ ∀ σ, 0 < Real.sqrt (L.H σ).det.re
  exact ⟨detIdeal_ne_zero L hL, fun σ => Real.sqrt_pos.2 (det_re_pos (hL.2.2 σ))⟩

namespace A2
variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨x, hx, hd⟩ => ⟨x, fun i => h (hx i), hd⟩`.
-/
theorem detSub_mono {m : ℕ} {L L' : MLat K m} (h : L'.M ≤ L.M) : L'.detSub ≤ L.detSub :=
  Submodule.span_mono fun _ ⟨x, hx, hd⟩ => ⟨x, fun i => h (hx i), hd⟩

end A2

open A2 in
/- English proof (translation)
Introduce `K _ _ m L L' hL hL' hH hM`. Establish `hf` using `detSub_isFractional L hL.1`. Establish `hf'` using `detSub_isFractional L' hL'.1`. Establish `hle : L'.detIdeal ≤ L.detIdeal`. Rewrite using `[← FractionalIdeal.coe_le_coe, detIdeal_coe L hf, detIdeal_coe L' hf']`.

Conclude with `detSub_mono hM`. Establish `hN` using `absNorm_anti' hle (detIdeal_ne_zero L' hL')`. Establish `hpos` using `absNorm_pos' (detIdeal_ne_zero L hL)`. Rewrite using `[deg_detLine, deg_detLine, hH]`. Establish `: Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤ Real.log ((FractionalIdeal.absNorm L'.detIdeal : ℚ) : ℝ)` using `Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hN)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem detLineMono : DetMono := by
  intro K _ _ m L L' hL hL' hH hM
  have hf := detSub_isFractional L hL.1
  have hf' := detSub_isFractional L' hL'.1
  have hle : L'.detIdeal ≤ L.detIdeal := by
    rw [← FractionalIdeal.coe_le_coe, detIdeal_coe L hf, detIdeal_coe L' hf']
    exact detSub_mono hM
  have hN := absNorm_anti' hle (detIdeal_ne_zero L' hL')
  have hpos := absNorm_pos' (detIdeal_ne_zero L hL)
  rw [deg_detLine, deg_detLine, hH]
  have : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      Real.log ((FractionalIdeal.absNorm L'.detIdeal : ℚ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hN)
  linarith

namespace A2
variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `d ⟨x, hx, rfl⟩`. Establish `: ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i` using `fun i => by`. Use `hx i` as an intermediate fact.

Rewrite `this` using `[hb]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 this`. Use `choose c hc using this`. Establish `hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b`. Use extensionality with `i j`.

Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]`. Rewrite using `[← hc i]`. Simplify using `[Finset.sum_apply, Algebra.smul_def]`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Use `⟨(Matrix.of c).det, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]`. Both sides reduce to the same expression. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Use `Submodule.subset_span ⟨b, fun i => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hb]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem detSub_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro d ⟨x, hx, rfl⟩
    have : ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i := fun i => by
      have := hx i
      rw [hb] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using this
    have hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
      rw [← hc i]
      simp [Finset.sum_apply, Algebra.smul_def]
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨b, fun i => ?_, rfl⟩
    rw [hb]
    exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Use `show (L.detIdeal : Submodule (𝓞 K) K) = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det : Submodule (𝓞 K) K)`. Rewrite using `[detIdeal_coe L (detSub_isFractional L hL.1), FractionalIdeal.coe_spanSingleton, detSub_free L b hb]`.
-/
theorem detIdeal_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K) (hL : L.Good)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detIdeal = FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det := by
  apply FractionalIdeal.coeToSubmodule_injective
  show (L.detIdeal : Submodule (𝓞 K) K) = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det : Submodule (𝓞 K) K)
  rw [detIdeal_coe L (detSub_isFractional L hL.1), FractionalIdeal.coe_spanSingleton, detSub_free L b hb]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, …`. Conclude with `Finset.sum_comm`.
-/
theorem gramC_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by
  ext i j
  simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose, RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]`. Simplify using `only [RingHom.mapMatrix_apply, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramC_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    (ReciprocityTheory.MultiplicativeHeights.gramC H σ b).det = (Complex.normSq (σ (Matrix.of b).det) : ℂ) * H.det := by
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]
  simp only [RingHom.mapMatrix_apply, Complex.star_def]
  ring

end A2

open A2 in
/- English proof (translation)
Introduce `K _ _ m L b hL hb`. Establish `hI` using `detIdeal_free L b hL hb`. Establish `hne : (Matrix.of b).det ≠ 0`. Introduce `h`. Apply `detIdeal_ne_zero L hL` to reduce the goal to its premises.

Rewrite using `[hI, h, FractionalIdeal.spanSingleton_zero]`. Establish `hσ : ∀ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re = 2 * Real.log ‖σ (Matrix.of b).det‖ + 2 * Real.log (Real.sqrt (L.H σ).det.re)`. Introduce `σ`. Establish `hD` using `det_re_pos (hL.2.2 σ)`. Establish `hn : 0 < ‖σ (Matrix.of b).det‖` using `norm_pos_iff.2 ((map_ne_zero σ).2 hne)`.

Rewrite using `[gramC_det, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, Real.log_mul (by positivity) hD.ne', Real.log_pow, Real.log_sqrt hD.le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[deg_detLine, hI, absNorm_span_real, Real.log_prod (fun σ _ => (norm_pos_iff.2 ((map_ne_zero σ).2 hne)).ne')]`. Repeatedly rewrite using `[hσ, Finset.sum_add_distrib, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem detLineFree : DetFree := by
  intro K _ _ m L b hL hb
  have hI := detIdeal_free L b hL hb
  have hne : (Matrix.of b).det ≠ 0 := by
    intro h
    apply detIdeal_ne_zero L hL
    rw [hI, h, FractionalIdeal.spanSingleton_zero]
  have hσ : ∀ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re =
      2 * Real.log ‖σ (Matrix.of b).det‖ + 2 * Real.log (Real.sqrt (L.H σ).det.re) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hn : 0 < ‖σ (Matrix.of b).det‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hne)
    rw [gramC_det, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, Real.log_mul (by positivity) hD.ne',
      Real.log_pow, Real.log_sqrt hD.le]
    push_cast
    ring
  rw [deg_detLine, hI, absNorm_span_real,
    Real.log_prod (fun σ _ => (norm_pos_iff.2 ((map_ne_zero σ).2 hne)).ne')]
  simp_rw [hσ, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/- English proof (translation)
Introduce `m A hA`. Establish `hdpos : ∀ i, 0 < (A i i).re` using `fun i => by`. Simplify using `using (Complex.lt_def.1 (hA.diag_pos (i := i))).1`. Establish `hdiag : ∀ i, A i i = ((A i i).re : ℂ)` using `fun i => (hA.isHermitian.coe_re_apply_self i).symm`. Use `set s : Fin m → ℝ := fun i => (Real.sqrt (A i i).re)⁻¹ with hs`.

Establish `hspos : ∀ i, 0 < s i` using `fun i => inv_pos.2 (Real.sqrt_pos.2 (hdpos i))`. Establish `hs2 : ∀ i, s i ^ 2 * (A i i).re = 1` using `fun i => by`. Rewrite using `[hs]`. Simplify using `only`. Rewrite using `[inv_pow, Real.sq_sqrt (hdpos i).le, inv_mul_cancel₀ (hdpos i).ne']`.

Use `set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (s i : ℂ) with hD`. Establish `hDh : D.conjTranspose = D`. Rewrite using `[hD, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Establish `hDdet : D.det = ∏ i, (s i : ℂ)` using `by rw [hD, Matrix.det_diagonal]`. Establish `hDu : IsUnit D`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, hDdet]`. Conclude with `IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hspos i).ne')`.

Establish `hC : (D.conjTranspose * A * D).PosDef` using `hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hDu)`. Use `set C := D.conjTranspose * A * D with hCdef`. Establish `hCii : ∀ i, C i i = 1` using `fun i => by`. Rewrite using `[hCdef, hDh, hD]`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Rewrite using `[hdiag i]`. Rewrite using `[show (s i : ℂ) * ((A i i).re : ℂ) * (s i : ℂ) = ((s i ^ 2 * (A i i).re : ℝ) : ℂ) by push_cast; ring, hs2 i]`. Simplify using the standard rewrite rules. Establish `hCdet : C.det = A.det * ∏ i, ((s i ^ 2 : ℝ) : ℂ)`. Rewrite using `[hCdef, Matrix.det_mul, Matrix.det_mul, hDh, hDdet]`.

Use `push_cast`. Rewrite using `[Finset.prod_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev` using `hC.isHermitian.det_eq_prod_eigenvalues`. Establish `htr` using `hC.isHermitian.trace_eq_sum_eigenvalues`.

Use `set ev := hC.isHermitian.eigenvalues with hev_def`. Establish `hevpos : ∀ i, 0 < ev i` using `hC.eigenvalues_pos`. Establish `hsum : ∑ i, ev i = m`. Establish `: C.trace = (m : ℂ)`. Simplify using `[Matrix.trace, hCii]`.

Rewrite `htr` using `[this]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `htr.symm`. Establish `hprod : ∏ i, ev i ≤ 1`.

Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `hmR : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `amgm` using `Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev (fun _ _ => zero_le_one) (by simp [hmR]) (fun i _ => (hevpos i).le)`.

Simplify using `only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum, div_self hmR.ne'] at amgm`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Use `Real.one_lt_rpow hlt (inv_pos.2 hmR)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA' : A.det = (∏ i, ev i : ℝ) * ∏ i, (((A i i).re : ℝ) : ℂ)`. Establish `h1 : C.det = ((∏ i, ev i : ℝ) : ℂ)` using `by rw [hev]; push_cast; rfl`. Establish `h2 : (∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[← Complex.ofReal_mul, hs2 i, Complex.ofReal_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA', ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hadamardInequality : HadamardPD := by
  intro m A hA
  have hdpos : ∀ i, 0 < (A i i).re := fun i => by
    simpa using (Complex.lt_def.1 (hA.diag_pos (i := i))).1
  have hdiag : ∀ i, A i i = ((A i i).re : ℂ) := fun i => (hA.isHermitian.coe_re_apply_self i).symm
  set s : Fin m → ℝ := fun i => (Real.sqrt (A i i).re)⁻¹ with hs
  have hspos : ∀ i, 0 < s i := fun i => inv_pos.2 (Real.sqrt_pos.2 (hdpos i))
  have hs2 : ∀ i, s i ^ 2 * (A i i).re = 1 := fun i => by
    rw [hs]; simp only
    rw [inv_pow, Real.sq_sqrt (hdpos i).le, inv_mul_cancel₀ (hdpos i).ne']
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (s i : ℂ) with hD
  have hDh : D.conjTranspose = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hDdet : D.det = ∏ i, (s i : ℂ) := by rw [hD, Matrix.det_diagonal]
  have hDu : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det, hDdet]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hspos i).ne')
  have hC : (D.conjTranspose * A * D).PosDef := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hDu)
  set C := D.conjTranspose * A * D with hCdef
  have hCii : ∀ i, C i i = 1 := fun i => by
    rw [hCdef, hDh, hD]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hdiag i]
    rw [show (s i : ℂ) * ((A i i).re : ℂ) * (s i : ℂ) = ((s i ^ 2 * (A i i).re : ℝ) : ℂ) by push_cast; ring, hs2 i]
    simp
  have hCdet : C.det = A.det * ∏ i, ((s i ^ 2 : ℝ) : ℂ) := by
    rw [hCdef, Matrix.det_mul, Matrix.det_mul, hDh, hDdet]
    push_cast
    rw [Finset.prod_pow]
    ring
  have hev := hC.isHermitian.det_eq_prod_eigenvalues
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  set ev := hC.isHermitian.eigenvalues with hev_def
  have hevpos : ∀ i, 0 < ev i := hC.eigenvalues_pos
  have hsum : ∑ i, ev i = m := by
    have : C.trace = (m : ℂ) := by
      simp [Matrix.trace, hCii]
    rw [this] at htr
    apply Complex.ofReal_injective
    push_cast
    exact htr.symm
  have hprod : ∏ i, ev i ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev
      (fun _ _ => zero_le_one) (by simp [hmR]) (fun i _ => (hevpos i).le)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hsum, div_self hmR.ne'] at amgm
    by_contra hlt
    push Not at hlt
    have := Real.one_lt_rpow hlt (inv_pos.2 hmR)
    linarith
  have hA' : A.det = (∏ i, ev i : ℝ) * ∏ i, (((A i i).re : ℝ) : ℂ) := by
    have h1 : C.det = ((∏ i, ev i : ℝ) : ℂ) := by rw [hev]; push_cast; rfl
    have h2 : (∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [← Complex.ofReal_mul, hs2 i, Complex.ofReal_one]
    calc A.det = A.det * ((∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ)) := by rw [h2, mul_one]
      _ = C.det * ∏ i, (((A i i).re : ℝ) : ℂ) := by rw [hCdet]; ring
      _ = _ := by rw [h1]
  rw [hA', ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  calc (∏ i, ev i) * ∏ i, (A i i).re ≤ 1 * ∏ i, (A i i).re :=
        mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg fun i _ => (hdpos i).le)
    _ = _ := one_mul _

namespace A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [FractionalIdeal.coe_one]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coe_mul, ih]`.
-/
theorem coe_prod_fi {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ j ∈ s, I j : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ j ∈ s, (I j : Submodule (𝓞 K) K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.coe_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coe_mul, ih]

/- English proof (translation)
Rewrite using `[← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, detIdeal_coe L (detSub_isFractional L hL.1), coe_prod_fi, Submodule.mul_le]`. Introduce `p hp q hq`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hq`. Rewrite using `[mul_smul_comm]`. Apply `Submodule.smul_mem` to reduce the goal to its premises.

Establish `hspan : ∏ j, ((ℓ j).I : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) (∏ j, (((ℓ j).I : Submodule (𝓞 K) K) : Set K))`. Rewrite using `[← Submodule.prod_span]`. Simplify using `only [Submodule.span_eq]`. Rewrite `hp` using `[hspan]`. Proceed by induction on `hp using Submodule.span_induction with`.

Consider the case `mem p hp`. Take `⟨g, hg, rfl⟩` from `(Set.mem_finsetProd _ _ _).1 hp`. Establish `: (∏ j, g j) * (Matrix.of u).det = (Matrix.of fun j k => g j * u j k).det`. Conclude with `(Matrix.det_mul_column g (Matrix.of u)).symm`. Rewrite using `[this]`.

Conclude with `det_mem L _ fun j => by`. Use `hu j (g j) (hg (Finset.mem_univ j))` as an intermediate fact. Simplify `this` using `[Pi.smul_def, smul_eq_mul]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem prod_mul_le_detIdeal {m : ℕ} (L : MLat K m) (hL : L.Good) (ℓ : Fin m → MLine K)
    (u : Fin m → Fin m → K) (hu : ∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ L.detIdeal := by
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    detIdeal_coe L (detSub_isFractional L hL.1), coe_prod_fi, Submodule.mul_le]
  intro p hp q hq
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
  rw [mul_smul_comm]
  apply Submodule.smul_mem
  have hspan : ∏ j, ((ℓ j).I : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) (∏ j, (((ℓ j).I : Submodule (𝓞 K) K) : Set K)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hspan] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hp
    have : (∏ j, g j) * (Matrix.of u).det = (Matrix.of fun j k => g j * u j k).det := by
      exact (Matrix.det_mul_column g (Matrix.of u)).symm
    rw [this]
    exact det_mem L _ fun j => by
      have := hu j (g j) (hg (Finset.mem_univ j))
      simpa [Pi.smul_def, smul_eq_mul] using this
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

end A2

open A2 in
/- English proof (translation)
Introduce `K _ _ m L ℓ u La hL hℓ hli hu hLa hsq`. Use `set d := (Matrix.of u).det with hd`. Establish `hdne : d ≠ 0`. Establish `: IsUnit (Matrix.of u)` using `Matrix.linearIndependent_rows_iff_isUnit.1 hli`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero`.

Establish `hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1) (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])`. Establish `hN` using `absNorm_anti' (prod_mul_le_detIdeal L hL ℓ u hu) hX0`. Establish `hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)` using `fun j => by`. Conclude with `absNorm_pos' (hℓ j).1` after adjusting the coercions. Establish `hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖` using `fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)`.

Establish `hposD` using `absNorm_pos' (detIdeal_ne_zero L hL)`. Establish `hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) = (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖`. Rewrite using `[map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, absNorm_span_real]`. Establish `hlogN : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤ ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖`. Rewrite using `[← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'), ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]`.

Conclude with `Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)`. Establish `hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (L.H σ).det.re) ≤ ∑ j, (Real.log La + Real.log ((ℓ j).n σ))`. Introduce `σ`. Establish `hD` using `det_re_pos (hL.2.2 σ)`. Establish `hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u).PosDef`.

Rewrite using `[gramC_eq]`. Apply `(hL.2.2 σ).conjTranspose_mul_mul_same` to reduce the goal to its premises. Apply `Matrix.mulVec_injective_iff_isUnit.2` to reduce the goal to its premises. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)`.

Establish `hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re` using `fun j => by`. Simplify using `using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1`. Establish `hH` using `hadamardInequality m _ hGpd`. Rewrite `hH` using `[gramC_det, Complex.re_ofReal_mul]`. Establish `hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2`.

Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `j _`. Conclude with `(hdiagpos j).le`. Introduce `j _`. Conclude with `hsq σ j`.

Establish `key : ‖σ d‖ ^ 2 * (L.H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Conclude with `hH.trans hbound`. Establish `hpos' : 0 < ‖σ d‖ ^ 2 * (L.H σ).det.re`. Use `hposd σ` as an intermediate fact.

Check the signs of the components of the expression. Establish `hlog` using `Real.log_le_log hpos' key`. Establish `hnpos : ∀ j, 0 < (ℓ j).n σ` using `fun j => (hℓ j).2 σ`. Rewrite `hlog` using `[Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow, Real.log_prod (fun j _ => by have := hnpos j; positivity)]`. Establish `hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ))`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hlog` using `[hs]`. Rewrite using `[Real.log_sqrt hD.le]`. Move the coercions through the operations in `at hlog`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsumσ` using `Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumσ`. Establish `hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ)` using `Finset.sum_comm`. Establish `hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K`. Conclude with `NumberField.Embeddings.card K ℂ` after adjusting the coercions.

Rewrite `hsumσ` using `[hc, hcard]`. Rewrite using `[deg_detLine]`. Simplify using `only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hadamardIdeals : HadamardIdeals := by
  intro K _ _ m L ℓ u La hL hℓ hli hu hLa hsq
  set d := (Matrix.of u).det with hd
  have hdne : d ≠ 0 := by
    have : IsUnit (Matrix.of u) := Matrix.linearIndependent_rows_iff_isUnit.1 hli
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1)
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hN := absNorm_anti' (prod_mul_le_detIdeal L hL ℓ u hu) hX0
  have hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) := fun j => by
    exact_mod_cast absNorm_pos' (hℓ j).1
  have hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)
  have hposD := absNorm_pos' (detIdeal_ne_zero L hL)
  have hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) =
      (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖ := by
    rw [map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, absNorm_span_real]
  have hlogN : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
    rw [← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'),
      ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]
    exact Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)
  have hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (L.H σ).det.re) ≤
      ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u).PosDef := by
      rw [gramC_eq]
      apply (hL.2.2 σ).conjTranspose_mul_mul_same
      apply Matrix.mulVec_injective_iff_isUnit.2
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)
    have hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re := fun j => by
      simpa using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1
    have hH := hadamardInequality m _ hGpd
    rw [gramC_det, Complex.re_ofReal_mul] at hH
    have hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro j _
        exact (hdiagpos j).le
      · intro j _
        exact hsq σ j
    have key : ‖σ d‖ ^ 2 * (L.H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hH.trans hbound
    have hpos' : 0 < ‖σ d‖ ^ 2 * (L.H σ).det.re := by
      have := hposd σ
      positivity
    have hlog := Real.log_le_log hpos' key
    have hnpos : ∀ j, 0 < (ℓ j).n σ := fun j => (hℓ j).2 σ
    rw [Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow,
      Real.log_prod (fun j _ => by have := hnpos j; positivity)] at hlog
    have hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']
      push_cast
      ring
    rw [hs] at hlog
    rw [Real.log_sqrt hD.le]
    push_cast at hlog
    linarith
  have hsumσ := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ) :=
    Finset.sum_comm
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  rw [hc, hcard] at hsumσ
  rw [deg_detLine]
  simp only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith

end Formalism.L2.LamCM
