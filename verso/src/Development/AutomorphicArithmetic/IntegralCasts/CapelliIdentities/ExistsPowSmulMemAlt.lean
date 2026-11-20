import Mathlib

/- English proof (translation)
Establish `h1 : IsAlgebraic ℚ_[l] c` using `Algebra.IsAlgebraic.isAlgebraic c`. Establish `h2 : IsAlgebraic ℤ_[l] c` using `(IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).mpr h1`. Take `⟨y, hy, hint⟩` from `h2.exists_integral_multiple`. Use `⟨y.valuation, ?_⟩` and prove the remaining obligations. Establish `hspec` using `PadicInt.unitCoeff_spec hy`.

Use `set u := PadicInt.unitCoeff hy`. Establish `h3 : ((l : ℤ_[l]) ^ y.valuation) = (↑u⁻¹ : ℤ_[l]) * y`. Rewrite using `[Units.eq_inv_mul_iff_mul_eq]`. Conclude with `hspec.symm`. Establish `h4 : (l : K) ^ y.valuation * c = (↑u⁻¹ : ℤ_[l]) • (y • c)`.

Rewrite using `[← mul_smul, ← h3, Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[h4]`. Conclude with `hint.smul _`.
-/
private theorem UpperTheory.pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (c : K) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℚ_[l] c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hspec := PadicInt.unitCoeff_spec hy
  set u := PadicInt.unitCoeff hy
  have h3 : ((l : ℤ_[l]) ^ y.valuation) = (↑u⁻¹ : ℤ_[l]) * y := by
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact hspec.symm
  have h4 : (l : K) ^ y.valuation * c = (↑u⁻¹ : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, ← h3, Algebra.smul_def, map_pow, map_natCast]
  rw [h4]
  exact hint.smul _

/- English proof (translation)
Introduce `l _ K _ _ _ _ _ O _ _ V _ _ _ _ T hO hT v`. Establish `hpow : ∀ (m : ℕ) (w : V), w ∈ T → (l : K) ^ m • w ∈ T`. Introduce `m w hw`. Establish `h : (l : K) ^ m = algebraMap O K ((l : O) ^ m)`. Rewrite using `[map_pow, map_natCast]`.

Rewrite using `[h, algebraMap_smul]`. Conclude with `T.smul_mem _ hw`. Establish `hv : v ∈ Submodule.span K (T : Set V)` using `hT ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨0, by simpa using hx⟩`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Use `⟨a + b, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `T.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[add_comm, pow_add, mul_smul]`. Conclude with `hpow _ _ ha`. Rewrite using `[pow_add, mul_smul]`.

Conclude with `hpow _ _ hb`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Take `⟨n, hn⟩` from `UpperTheory.pow_mul_isIntegral (l := l) c`. Take `⟨o, ho⟩` from `hO _ hn`.

Use `⟨n + a, ?_⟩` and prove the remaining obligations. Establish `h : (l : K) ^ (n + a) • c • x = o • ((l : K) ^ a • x)`. Rewrite using `[← algebraMap_smul K o, ho, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h]`. Conclude with `T.smul_mem _ ha`.
-/
theorem UpperTheory.exists_pow_smul_mem_alt :
    ∀ {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K] {O : Type} [CommRing O] [Algebra O K] {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (T : Submodule O V), (∀ c : K, IsIntegral ℤ_[l] c → ∃ o : O, algebraMap O K o = c) → Submodule.span K (T : Set V) = ⊤ → ∀ v : V, ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  intro l _ K _ _ _ _ _ O _ _ V _ _ _ _ T hO hT v
  have hpow : ∀ (m : ℕ) (w : V), w ∈ T → (l : K) ^ m • w ∈ T := by
    intro m w hw
    have h : (l : K) ^ m = algebraMap O K ((l : O) ^ m) := by
      rw [map_pow, map_natCast]
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := hT ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact hpow _ _ ha
    · rw [pow_add, mul_smul]
      exact hpow _ _ hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨n, hn⟩ := UpperTheory.pow_mul_isIntegral (l := l) c
    obtain ⟨o, ho⟩ := hO _ hn
    refine ⟨n + a, ?_⟩
    have h : (l : K) ^ (n + a) • c • x = o • ((l : K) ^ a • x) := by
      rw [← algebraMap_smul K o, ho, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ ha
