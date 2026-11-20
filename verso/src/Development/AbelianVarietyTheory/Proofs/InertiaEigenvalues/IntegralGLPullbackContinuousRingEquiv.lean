import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector

open IsDedekindDomain NumberField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntegralPullback

open Filter Topology ValuativeRel

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`.

Establish `hcz : c z ≠ 0` using `(map_ne_zero c).mpr hz0`. Establish `hinv : Valued.v z⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ h`. Establish `ht : Tendsto (fun n : ℕ => (c z⁻¹) ^ n) atTop (𝓝 0)`.

Use `(hc.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hinv)` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_pow]`. Establish `h1 : 1 ≤ Valued.v (c z⁻¹)`. Rewrite using `[map_inv₀]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← map_mul, inv_mul_cancel₀ hcz, map_one]`. Use `_ ≤ Valued.v (c z)⁻¹ * 1 := by gcongr`. Use `_ = Valued.v (c z)⁻¹ := mul_one _`. Establish `hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E)` using `Valued.mem_nhds_zero.mpr ⟨1, fun y hy => by simpa using hy⟩`. Take `⟨n, hn⟩` from `(ht.eventually_mem hU).exists`.

Establish `hn' : Valued.v ((c z⁻¹) ^ n) < 1` using `hn`. Rewrite `hn'` using `[map_pow]`. Conclude with `absurd hn' (not_lt.mpr (one_le_pow₀ h1))`.
-/
theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) ≤ 1) : Valued.v z ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at h
  have hcz : c z ≠ 0 := (map_ne_zero c).mpr hz0

  have hinv : Valued.v z⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h
  have ht : Tendsto (fun n : ℕ => (c z⁻¹) ^ n) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hinv)
    simpa [Function.comp_def, map_pow] using this

  have h1 : 1 ≤ Valued.v (c z⁻¹) := by
    rw [map_inv₀]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c z)⁻¹ * Valued.v (c z) := by
          rw [← map_mul, inv_mul_cancel₀ hcz, map_one]
      _ ≤ Valued.v (c z)⁻¹ * 1 := by gcongr
      _ = Valued.v (c z)⁻¹ := mul_one _
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨n, hn⟩ := (ht.eventually_mem hU).exists
  have hn' : Valued.v ((c z⁻¹) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ h1))

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← Valuation.vle_one_iff (valuation (w.adicCompletion E))]`. Use `show Valued.v z ≤ Valued.v 1 ↔ _`. Rewrite using `[map_one]`.
-/
theorem mem_integer_iff {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (z : w.adicCompletion E) :
    z ∈ (valuation (w.adicCompletion E)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff (valuation (w.adicCompletion E))]
  show Valued.v z ≤ Valued.v 1 ↔ _
  rw [map_one]

/- English proof (translation)
Set `P : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer` to `Matrix.of fun i j => ⟨_, h1 i j⟩`. Set `Q : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Set `f` to `algebraMap (valuation (v.adicCompletion F)).integer (v.adicCompletion F)`. Establish `hP : P.map f = (A : Matrix (Fin n) (Fin n) _)`. Use extensionality with `i j`.

Simplify using `only [P, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]`. Establish `hQ : Q.map f = ((A⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)`. Use extensionality with `i j`. Simplify using `only [Q, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]`. Establish `inj : ∀ X Y : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer, X.map f = Y.map f → X = Y`.

Introduce `X Y h`. Conclude with `Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)`. Establish `hPQ : P * Q = 1` using `inj _ _ (by`. Rewrite using `[Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]`. Conclude with `A.mul_inv)`.

Establish `hQP : Q * P = 1` using `inj _ _ (by`. Rewrite using `[Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]`. Conclude with `A.inv_mul)`. Unfold `GlobalTheory.SplitWeil.KO`. Use `MonoidHom.mem_range.mpr ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩` and prove the remaining obligations.

Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.map_apply]`. Conclude with `congrFun (congrFun hP i) j`.
-/
private theorem mem_KO_of_integral_entries' {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (A : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer)
    (h2 : ∀ i j, ((A⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ (valuation (v.adicCompletion F)).integer) :
    A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by

  let P : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h2 i j⟩
  let f := algebraMap (valuation (v.adicCompletion F)).integer (v.adicCompletion F)
  have hP : P.map f = (A : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [P, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have hQ : Q.map f = ((A⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [Q, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have inj : ∀ X Y : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer,
      X.map f = Y.map f → X = Y := by
    intro X Y h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hPQ : P * Q = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.mul_inv)
  have hQP : Q * P = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.inv_mul)
  unfold GlobalTheory.SplitWeil.KO
  refine MonoidHom.mem_range.mpr ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hP i) j

/- English proof (translation)
Unfold `GlobalTheory.SplitWeil.KO at hM`. Take `⟨C, hC⟩` from `MonoidHom.mem_range.mp hM`. Rewrite using `[GlobalTheory.IntegralPullback.mem_integer_iff]`. Apply `valued_le_one_of_map c hc` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.IntegralPullback.mem_integer_iff]`.

Establish `hij` using `congrArg (fun g : GL (Fin n) (w.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) hC`. Simplify using `only [Matrix.GeneralLinearGroup.map_apply] at hij`. Establish `: c ((M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) = ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j : w.adicCompletion E)` using `hij.symm`. Rewrite using `[this]`. Conclude with `((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j).2`.
-/
private theorem entry_mem_integer_of_map_mem_KO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (M : GL (Fin n) (v.adicCompletion F))
    (hM : Matrix.GeneralLinearGroup.map c.toRingHom M ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n))
    (i j : Fin n) :
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer := by
  unfold GlobalTheory.SplitWeil.KO at hM
  obtain ⟨C, hC⟩ := MonoidHom.mem_range.mp hM
  rw [GlobalTheory.IntegralPullback.mem_integer_iff]
  apply valued_le_one_of_map c hc
  rw [← GlobalTheory.IntegralPullback.mem_integer_iff]
  have hij := congrArg (fun g : GL (Fin n) (w.adicCompletion E) =>
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) hC
  simp only [Matrix.GeneralLinearGroup.map_apply] at hij
  have : c ((M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) =
      ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j :
        w.adicCompletion E) := hij.symm
  rw [this]
  exact ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j).2

/- English proof (translation)
Introduce `F E _ _ _ _ v w c hc n A hA`. Establish `hAinv : Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹ ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)`. Rewrite using `[map_inv]`. Conclude with `inv_mem hA`. Conclude with `mem_KO_of_integral_entries' A (entry_mem_integer_of_map_mem_KO c hc A hA) (entry_mem_integer_of_map_mem_KO c hc A⁻¹ hAinv)`.
-/
theorem mem_KO_of_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (c : v.adicCompletion F ≃+* w.adicCompletion E), Continuous c → ∀ {n : ℕ} (A : GL (Fin n) (v.adicCompletion F)), Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) → A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by
  intro F E _ _ _ _ v w c hc n A hA
  have hAinv : Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹ ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [map_inv]
    exact inv_mem hA
  exact mem_KO_of_integral_entries' A (entry_mem_integer_of_map_mem_KO c hc A hA) (entry_mem_integer_of_map_mem_KO c hc A⁻¹ hAinv)

end GlobalTheory.IntegralPullback
