import Mathlib

open NumberField Matrix

namespace GlobalTheory.PrimAnnih

/- English proof (translation)
Set `I : Ideal W` to `Ideal.span (Set.range w)`. Take `⟨c, hc⟩` from `(IsPrincipalIdealRing.principal I).principal`. Establish `hdvd : ∀ i, c ∣ w i` using `fun i => by`. Establish `: w i ∈ I` using `Ideal.subset_span ⟨i, rfl⟩`. Rewrite `this` using `[hc]`.

Conclude with `Ideal.mem_span_singleton.1 this`. Use `choose v hv using hdvd`. Establish `hcI : c ∈ I` using `by rw [hc]; exact Submodule.mem_span_singleton_self c`. Take `⟨a, ha⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hcI`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[hv i, zero_mul]`. Both sides reduce to the same expression.

Establish `hsum : ∑ i, a i * v i = 1`. Apply `mul_left_cancel₀ hc0` to reduce the goal to its premises. Rewrite using `[mul_one, Finset.mul_sum]`. Use `conv_rhs => rw [← ha]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hv i]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨v, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu push_neg at hnu`. Establish `h1 : (1 : W) ∈ IsLocalRing.maximalIdeal W`.

Rewrite using `[← hsum]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu i))`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Establish `h2 : c • ∑ i, v i • u i = 0`. Rewrite using `[Finset.smul_sum, ← h]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hv i]`. Conclude with `(smul_eq_zero.1 h2).resolve_left hc0`.
-/
theorem exists_unit_coeff {W V ι : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [AddCommGroup V] [Module W V] [NoZeroSMulDivisors W V] [Fintype ι] (u : ι → V) (w : ι → W)
    (hw : w ≠ 0) (h : ∑ i, w i • u i = 0) :
    ∃ v : ι → W, (∃ i, IsUnit (v i)) ∧ ∑ i, v i • u i = 0 := by
  classical
  let I : Ideal W := Ideal.span (Set.range w)
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdvd : ∀ i, c ∣ w i := fun i => by
    have : w i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [hc] at this
    exact Ideal.mem_span_singleton.1 this
  choose v hv using hdvd
  have hcI : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw; funext i; rw [hv i, zero_mul]; rfl
  have hsum : ∑ i, a i * v i = 1 := by
    apply mul_left_cancel₀ hc0
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv i]; ring
  refine ⟨v, ?_, ?_⟩
  · by_contra hnu
    push_neg at hnu
    have h1 : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu i))
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · have h2 : c • ∑ i, v i • u i = 0 := by
      rw [Finset.smul_sum, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← hv i]
    exact (smul_eq_zero.1 h2).resolve_left hc0

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push_neg at H`. Set `L` to `FractionRing W`. Set `g : L →+* Ω` to `IsFractionRing.lift hf`. Establish `hg : ∀ r, g (algebraMap W L r) = f r` using `fun r => IsFractionRing.lift_algebraMap hf r`.

Set `AL : Matrix ι κ L` to `A.map (algebraMap W L)`. Establish `hker : LinearMap.ker AL.vecMulLinear = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `l hl`. Take `⟨⟨c, hc⟩, hint⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors W) Finset.univ l`.

Use `choose w hw using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))`. Establish `hl' : l ᵥ* AL = 0` using `hl`. Establish `h1 : w ᵥ* A = 0`. Use function extensionality and compare the values at `j`. Apply `IsFractionRing.injective W L` to reduce the goal to its premises.

Rewrite using `[RingHom.map_vecMul, Pi.zero_apply, map_zero]`. Establish `e : (algebraMap W L ∘ w) = fun i => algebraMap W L c * l i`. Use function extensionality and compare the values at `i`. Simplify `hw i` using `[Algebra.smul_def]`. Rewrite using `[e]`.

Use `congrFun hl' j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this ⊢`. Simplify using `only [mul_assoc, ← Finset.mul_sum, this, mul_zero, AL]`. Establish `hw0 : w = 0`. Assume the negation of the conclusion as `hw0`.

Conclude with `H w hw0 h1`. Use function extensionality and compare the values at `i`. Establish `e1` using `hw i`. Rewrite `e1` using `[hw0, Pi.zero_apply, map_zero, Algebra.smul_def]`. Establish `hc0 : algebraMap W L c ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc`.

Conclude with `(mul_eq_zero.1 e1.symm).resolve_left hc0`. Take `⟨G, hG⟩` from `LinearMap.exists_leftInverse_of_injective AL.vecMulLinear hker`. Set `P` to `LinearMap.toMatrix' G`. Establish `hP : AL * P.transpose = 1`. Use extensionality with `i j`.

Use `congrArg (fun φ => φ (Pi.single i 1) j) hG` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite `this` using `[← LinearMap.toMatrix'_mulVec G]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, show (if i = j then (1:L) else 0) = (Pi.single i (1:L) : ι → L) j by simp [Pi.single_apply, eq_comm], ← this]`. Simplify using `[Matrix.mulVec, dotProduct, P, mul_comm, Matrix.vecMulLinear_apply]`.

Establish `hAf : AL.map g = A.map f` using `by ext i j; simp [AL, hg]`. Establish `hP' : A.map f * (P.transpose.map g) = 1`. Rewrite using `[← hAf, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero g) (map_one g)]`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← Matrix.vecMul_one x, ← hP', ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]`.
-/
theorem exists_vecMul_eq_zero {W Ω ι κ : Type} [CommRing W] [IsDomain W] [Field Ω] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : W →+* Ω) (hf : Function.Injective f)
    (A : Matrix ι κ W) (x : ι → Ω) (hx : x ≠ 0) (h : x ᵥ* A.map f = 0) :
    ∃ w : ι → W, w ≠ 0 ∧ w ᵥ* A = 0 := by
  classical
  by_contra H
  push_neg at H
  let L := FractionRing W
  let g : L →+* Ω := IsFractionRing.lift hf
  have hg : ∀ r, g (algebraMap W L r) = f r := fun r => IsFractionRing.lift_algebraMap hf r
  let AL : Matrix ι κ L := A.map (algebraMap W L)
  have hker : LinearMap.ker AL.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    obtain ⟨⟨c, hc⟩, hint⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors W) Finset.univ l
    choose w hw using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
    have hl' : l ᵥ* AL = 0 := hl
    have h1 : w ᵥ* A = 0 := by
      funext j
      apply IsFractionRing.injective W L
      rw [RingHom.map_vecMul, Pi.zero_apply, map_zero]
      have e : (algebraMap W L ∘ w) = fun i => algebraMap W L c * l i := by
        funext i; simpa [Algebra.smul_def] using hw i
      rw [e]
      have := congrFun hl' j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this ⊢
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero, AL]
    have hw0 : w = 0 := by
      by_contra hw0; exact H w hw0 h1
    funext i
    have e1 := hw i
    rw [hw0, Pi.zero_apply, map_zero, Algebra.smul_def] at e1
    have hc0 : algebraMap W L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact (mul_eq_zero.1 e1.symm).resolve_left hc0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective AL.vecMulLinear hker
  let P := LinearMap.toMatrix' G
  have hP : AL * P.transpose = 1 := by
    ext i j
    have := congrArg (fun φ => φ (Pi.single i 1) j) hG
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← LinearMap.toMatrix'_mulVec G] at this
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (if i = j then (1:L) else 0) = (Pi.single i (1:L) : ι → L) j by simp [Pi.single_apply, eq_comm], ← this]
    simp [Matrix.mulVec, dotProduct, P, mul_comm, Matrix.vecMulLinear_apply]
  have hAf : AL.map g = A.map f := by ext i j; simp [AL, hg]
  have hP' : A.map f * (P.transpose.map g) = 1 := by
    rw [← hAf, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero g) (map_one g)]
  apply hx
  rw [← Matrix.vecMul_one x, ← hP', ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

end GlobalTheory.PrimAnnih

namespace GlobalTheory.PrimAnnih

/- English proof (translation)
Establish `hk : RingHom.ker σ = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[RingHom.comap_ker, show σ.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom Ω from RingHom.ext_int _ _]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective`. Establish `hinj : Function.Injective σ` using `(RingHom.injective_iff_ker_eq_bot σ).2 hk`.

Conclude with `⟨(IsFractionRing.lift hinj : F →+* Ω).toRatAlgHom, fun a => IsFractionRing.lift_algebraMap hinj a⟩`.
-/
theorem exists_extend (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω]
    (σ : 𝓞 F →+* Ω) : ∃ σ' : F →ₐ[ℚ] Ω, ∀ a : 𝓞 F, σ' (algebraMap (𝓞 F) F a) = σ a := by
  have hk : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [RingHom.comap_ker, show σ.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom Ω from
      RingHom.ext_int _ _]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot σ).2 hk
  exact ⟨(IsFractionRing.lift hinj : F →+* Ω).toRatAlgHom,
    fun a => IsFractionRing.lift_algebraMap hinj a⟩

/- English proof (translation)
Introduce `F _ _ W Ω _ _ _ _ _ _ f hf n M σ hσ ι _ b`. Set `b' : Module.Basis ι ℚ F` to `Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) F b`. Establish `hb' : ∀ i, b' i = algebraMap (𝓞 F) F (b i)` using `fun i => Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) F b i`. Take `⟨σ', hσ'⟩` from `exists_extend F Ω σ`. Establish `hcard : Fintype.card ι = Fintype.card (F →ₐ[ℚ] Ω)`.

Rewrite using `[AlgHom.card, Module.finrank_eq_card_basis b']`. Set `q` to `Fintype.equivOfCardEq hcard`. Set `P` to `Algebra.embeddingsMatrixReindex ℚ Ω b' q`. Establish `hPij : ∀ i j, P i j = q j (b' i)` using `fun i j => by`. Simplify using `[P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]`.

Establish `hP : P.det ≠ 0`. Establish `hd` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b' q`. Introduce `h0`. Rewrite `hd` using `[h0, zero_pow two_ne_zero, map_eq_zero]`. Conclude with `Algebra.discr_not_zero_of_basis ℚ b' hd`.

Establish `inj : ∀ z : ι → Ω, (∀ τ : F →ₐ[ℚ] Ω, ∑ i, z i * τ (b' i) = 0) → z = 0`. Introduce `z hz`. Use `Matrix.eq_zero_of_vecMul_eq_zero hP (funext fun j => ?_)` and prove the remaining obligations. Simplify `hz (q j)` using `[Matrix.vecMul, dotProduct, hPij]`. Set `y : ι → Ω` to `fun j => if q j = σ' then 1 else 0`.

Set `x : ι → Ω` to `y ᵥ* P⁻¹`. Establish `hx : ∀ τ, ∑ i, x i * τ (b' i) = if τ = σ' then 1 else 0`. Introduce `τ`. Establish `h1 : x ᵥ* P = y`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP), Matrix.vecMul_one]`.

Use `congrFun h1 (q.symm τ)` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, hPij, y]`. Set `Φ : 𝓞 F →+* Matrix (Fin n) (Fin n) Ω` to `f.mapMatrix.comp M`. Establish `hΦ : ∀ a, Φ a = (M a).map f` using `fun a => rfl`. Establish `hcoef : ∀ (a : 𝓞 F) j, ∑ i, x i * (b.repr (a * b i) j : Ω) = σ a * x j`.

Introduce `a`. Establish `hrep : ∀ i (τ : F →ₐ[ℚ] Ω), ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) = τ (algebraMap (𝓞 F) F a) * τ (b' i)`. Introduce `i τ`. Establish `e` using `congrArg (fun t : 𝓞 F => τ (algebraMap (𝓞 F) F t)) (b.sum_repr (a * b i))`. Simplify using `only [map_sum, map_zsmul, map_mul, zsmul_eq_mul] at e`.

Simplify `e` using `[hb']`. Use `inj (fun j => ∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) (fun τ => by` as an intermediate fact. Establish `key : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, mul_assoc]`.

Use `_ = ∑ i, x i * ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) := by`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.mul_sum]`. Use `_ = ∑ i, x i * (τ (algebraMap (𝓞 F) F a) * τ (b' i)) := by simp only [hrep]`. Use `_ = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`. Establish `e2 : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) * τ (b' j) = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) - σ a * ∑ j, x j * τ (b' j)`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]`. Rewrite using `[e2, key, hx]`. Use `split_ifs with hτ`.

Substitute `hτ` using the available equality. Rewrite using `[hσ']`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `ring)`. Introduce `j`.

Conclude with `sub_eq_zero.1 (congrFun this j)`. Set `N : Matrix (Fin n) (Fin n) Ω` to `∑ i, x i • Φ (b i)`. Establish `hN : ∀ a, Φ a * N = σ a • N`. Introduce `a`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [N, Finset.mul_sum, Matrix.mul_smul, map_mul]`. Use `_ = ∑ i, x i • ∑ j, (b.repr (a * b i) j : Ω) • Φ (b j) := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr (a * b i)]`. Simplify using `only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]`.

Use `_ = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) • Φ (b j) := by`. Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ j, (σ a * x j) • Φ (b j) := by simp only [hcoef]`. Use `_ = σ a • N := by simp only [N, Finset.smul_sum, smul_smul]`.

Establish `hN0 : N = 0`. Use extensionality with `j k`. Use `hσ (fun j => N j k) (fun a => by` as an intermediate fact. Use function extensionality and compare the values at `r`. Establish `e` using `congrFun (congrFun (hN a) r) k`.

Simplify `e)` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ]`. Simplify using `using congrFun this j`. Set `A : Matrix ι (Fin n × Fin n) W` to `Matrix.of fun i p => M (b i) p.1 p.2`. Establish `hx0 : x ≠ 0`. Introduce `h0`.

Use `hx σ'` as an intermediate fact. Simplify using `[h0] at this`. Establish `hxA : x ᵥ* A.map f = 0`. Use function extensionality and compare the values at `p`. Use `congrFun (congrFun hN0 p.1) p.2` as an intermediate fact.

Simplify `this` using `[Matrix.vecMul, dotProduct, A, N, hΦ, Matrix.sum_apply, mul_comm]`. Take `⟨w, hw0, hwA⟩` from `exists_vecMul_eq_zero f hf A x hx0 hxA`. Use `haveI : NoZeroSMulDivisors W (Matrix (Fin n) (Fin n) W) := inferInstanceAs (NoZeroSMulDivisors W (Fin n → Fin n → W))`. Use `exists_unit_coeff (fun i => M (b i)) w hw0 ?_` and prove the remaining obligations. Use extensionality with `j k`.

Use `congrFun hwA (j, k)` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, A, Matrix.sum_apply, mul_comm]`.
-/
theorem exists_primitive_annihilator : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  intro F _ _ W Ω _ _ _ _ _ _ f hf n M σ hσ ι _ b
  classical
  let b' : Module.Basis ι ℚ F := Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) F b
  have hb' : ∀ i, b' i = algebraMap (𝓞 F) F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) F b i
  obtain ⟨σ', hσ'⟩ := exists_extend F Ω σ
  have hcard : Fintype.card ι = Fintype.card (F →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b']
  let q := Fintype.equivOfCardEq hcard
  let P := Algebra.embeddingsMatrixReindex ℚ Ω b' q
  have hPij : ∀ i j, P i j = q j (b' i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b' q
    intro h0
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at hd
    exact Algebra.discr_not_zero_of_basis ℚ b' hd
  have inj : ∀ z : ι → Ω, (∀ τ : F →ₐ[ℚ] Ω, ∑ i, z i * τ (b' i) = 0) → z = 0 := by
    intro z hz
    refine Matrix.eq_zero_of_vecMul_eq_zero hP (funext fun j => ?_)
    simpa [Matrix.vecMul, dotProduct, hPij] using hz (q j)
  let y : ι → Ω := fun j => if q j = σ' then 1 else 0
  let x : ι → Ω := y ᵥ* P⁻¹
  have hx : ∀ τ, ∑ i, x i * τ (b' i) = if τ = σ' then 1 else 0 := by
    intro τ
    have h1 : x ᵥ* P = y := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP),
        Matrix.vecMul_one]
    have := congrFun h1 (q.symm τ)
    simpa [Matrix.vecMul, dotProduct, hPij, y] using this

  let Φ : 𝓞 F →+* Matrix (Fin n) (Fin n) Ω := f.mapMatrix.comp M
  have hΦ : ∀ a, Φ a = (M a).map f := fun a => rfl
  have hcoef : ∀ (a : 𝓞 F) j, ∑ i, x i * (b.repr (a * b i) j : Ω) = σ a * x j := by
    intro a
    have hrep : ∀ i (τ : F →ₐ[ℚ] Ω), ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) =
        τ (algebraMap (𝓞 F) F a) * τ (b' i) := by
      intro i τ
      have e := congrArg (fun t : 𝓞 F => τ (algebraMap (𝓞 F) F t)) (b.sum_repr (a * b i))
      simp only [map_sum, map_zsmul, map_mul, zsmul_eq_mul] at e
      simpa [hb'] using e
    have := inj (fun j => ∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) (fun τ => by
      have key : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) =
          τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
        calc ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j)
            = ∑ j, ∑ i, x i * ((b.repr (a * b i) j : Ω) * τ (b' j)) := by
              simp only [Finset.sum_mul, mul_assoc]
          _ = ∑ i, x i * ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) := by
              rw [Finset.sum_comm]; simp only [Finset.mul_sum]
          _ = ∑ i, x i * (τ (algebraMap (𝓞 F) F a) * τ (b' i)) := by simp only [hrep]
          _ = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) * τ (b' j) =
          ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) -
            σ a * ∑ j, x j * τ (b' j) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      rw [e2, key, hx]
      split_ifs with hτ
      · subst hτ; rw [hσ']; ring
      · ring)
    intro j
    exact sub_eq_zero.1 (congrFun this j)
  let N : Matrix (Fin n) (Fin n) Ω := ∑ i, x i • Φ (b i)
  have hN : ∀ a, Φ a * N = σ a • N := by
    intro a
    calc Φ a * N = ∑ i, x i • Φ (a * b i) := by
          simp only [N, Finset.mul_sum, Matrix.mul_smul, map_mul]
      _ = ∑ i, x i • ∑ j, (b.repr (a * b i) j : Ω) • Φ (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (a * b i)]
          simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) • Φ (b j) := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
      _ = ∑ j, (σ a * x j) • Φ (b j) := by simp only [hcoef]
      _ = σ a • N := by simp only [N, Finset.smul_sum, smul_smul]
  have hN0 : N = 0 := by
    ext j k
    have := hσ (fun j => N j k) (fun a => by
      funext r
      have e := congrFun (congrFun (hN a) r) k
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ] using e)
    simpa using congrFun this j
  let A : Matrix ι (Fin n × Fin n) W := Matrix.of fun i p => M (b i) p.1 p.2
  have hx0 : x ≠ 0 := by
    intro h0
    have := hx σ'
    simp [h0] at this
  have hxA : x ᵥ* A.map f = 0 := by
    funext p
    have := congrFun (congrFun hN0 p.1) p.2
    simpa [Matrix.vecMul, dotProduct, A, N, hΦ, Matrix.sum_apply, mul_comm] using this
  obtain ⟨w, hw0, hwA⟩ := exists_vecMul_eq_zero f hf A x hx0 hxA
  haveI : NoZeroSMulDivisors W (Matrix (Fin n) (Fin n) W) :=
    inferInstanceAs (NoZeroSMulDivisors W (Fin n → Fin n → W))
  refine exists_unit_coeff (fun i => M (b i)) w hw0 ?_
  ext j k
  have := congrFun hwA (j, k)
  simpa [Matrix.vecMul, dotProduct, A, Matrix.sum_apply, mul_comm] using this

end GlobalTheory.PrimAnnih
