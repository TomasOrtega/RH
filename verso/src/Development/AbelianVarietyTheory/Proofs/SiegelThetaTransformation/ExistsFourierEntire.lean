import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTube
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.LevelTheta

/- English proof (translation)
Take `⟨a, h1, h2⟩` from `exists_fourier_expansion_tube ι Set.univ f isOpen_univ convex_univ hf.differentiableOn (fun z _ m => hper z m)`. Use `⟨a, fun z => h1 z trivial, fun w ν => ?_⟩` and prove the remaining obligations. Establish `key` using `Koecher.setIntegral_unitCube_tube (U := Set.univ) (f := fun z => f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))) isOpen_univ isPreconnected_univ (fun _ _ _ => trivial) (hf.differentiableOn.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => ?_) (Set.mem_univ (fu …`. Rewrite using `[h2 0 trivial ν]`. Use `Eq.trans ?_ key` and prove the remaining obligations.

Conclude with `(setIntegral_congr_set (μ := volume) (Measure.univ_pi_Ico_ae_eq_Icc (f := (0 : ι → ℝ)) (g := 1)))`. Establish `e0 : (Pi.single i 1 : ι → ℂ) = fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hij]`. Establish `e : ∑ j, (ν j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j = ∑ j, (ν j : ℂ) * z j + ν i`. Simplify using `[mul_add, Finset.sum_add_distrib, Pi.single_apply]`. Rewrite using `[e, e0, hper z, mul_add, neg_add, Complex.exp_add]`.

Establish `: cexp (-(2 * π * I * (ν i : ℂ))) = 1`. Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I (-ν i)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, mul_one]`.
-/
theorem exists_fourier_entire {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z, ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) :
    ∃ a : (ι → ℤ) → ℂ,
      (∀ z, HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
      ∀ (w : ι → ℂ) (ν : ι → ℤ), a ν = ∫ x in Set.Icc (0 : ι → ℝ) 1,
        f ((fun i => (x i : ℂ)) + w) *
          cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + w i))) := by
  obtain ⟨a, h1, h2⟩ := exists_fourier_expansion_tube ι Set.univ f isOpen_univ convex_univ
    hf.differentiableOn (fun z _ m => hper z m)
  refine ⟨a, fun z => h1 z trivial, fun w ν => ?_⟩
  have key := Koecher.setIntegral_unitCube_tube (U := Set.univ)
    (f := fun z => f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))) isOpen_univ
    isPreconnected_univ (fun _ _ _ => trivial)
    (hf.differentiableOn.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => ?_)
    (Set.mem_univ (fun i => I * (((0 : ι → ℝ) i : ℝ) : ℂ))) (Set.mem_univ w)
  · rw [h2 0 trivial ν]
    refine Eq.trans ?_ key
    exact (setIntegral_congr_set (μ := volume) (Measure.univ_pi_Ico_ae_eq_Icc
      (f := (0 : ι → ℝ)) (g := 1)))
  · have e0 : (Pi.single i 1 : ι → ℂ) = fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ) := by
      funext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    have e : ∑ j, (ν j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j
        = ∑ j, (ν j : ℂ) * z j + ν i := by
      simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
    rw [e, e0, hper z, mul_add, neg_add, Complex.exp_add]
    have : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-ν i)]
      congr 1
      push_cast
      ring
    rw [this, mul_one]

/- English proof (translation)
Establish `: v ⬝ᵥ τ *ᵥ u = u ⬝ᵥ τ *ᵥ v`. Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]`. Rewrite using `[mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_add {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} (h : τ.IsSymm) (u v : ι → ℂ) :
    (u + v) ⬝ᵥ τ *ᵥ (u + v) = u ⬝ᵥ τ *ᵥ u + 2 * (u ⬝ᵥ τ *ᵥ v) + v ⬝ᵥ τ *ᵥ v := by
  have : v ⬝ᵥ τ *ᵥ u = u ⬝ᵥ τ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, this]
  ring

/- English proof (translation)
Introduce `n g τ hτ N hN Θ hΘ hp hq`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Take `⟨a, hs, ha⟩` from `exists_fourier_entire (ι := Fin n × Fin g) (fun z => Θ fun k i => N * z (k, i)) (hΘ.comp (by fun_prop)) (fun z m => by`. Rewrite using `[← hp (fun k i => m (k, i)) fun k i => N * z (k, i)]`.

Use `congr 1`. Use function extensionality and compare the values at `k i`. Simplify using `[mul_add])`. Set `e : (Fin n × Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ` to `fun ν => Matrix.of fun k i => (ν (k, i) : ℚ) / N`. Establish `he : Function.Injective e`.

Introduce `m m' hmn`. Use function extensionality and compare the values at `⟨k, i⟩`. Establish `h1 : (m (k, i) : ℚ) / N = (m' (k, i) : ℚ) / N` using `congrFun (congrFun hmn k) i`. Conclude with `(div_left_inj' hNq).1 h1` after adjusting the coercions. Set `Q : Matrix (Fin n) (Fin g) ℚ → ℂ` to `fun x => ∑ k, qv (x k) ⬝ᵥ τ *ᵥ qv (x k)`.

Set `φ : TF n g` to `fun x => Function.extend e a 0 x * cexp (-(π * I * Q x))`. Establish `hφe : ∀ ν, φ (e ν) = a ν * cexp (-(π * I * Q (e ν)))` using `fun ν => by`. Simplify using `only [φ, he.extend_apply]`. Establish `hφ0 : ∀ x, x ∉ Set.range e → φ x = 0` using `fun x hx => by`. Simplify using `only [φ]`.

Rewrite using `[Function.extend_apply' _ _ _ hx]`. Simplify using the standard rewrite rules. Establish `hshift : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ), e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ)) = e (fun p => ν p + N ^ 2 * b p.1 p.2)`. Introduce `ν b`. Use extensionality with `k i`.

Simplify using `only [e, of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hlaw : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ), φ (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = φ (e ν)`. Introduce `ν b`.

Establish `hQ : Q (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = Q (e ν) + 2 * ∑ k, ∑ i, (ν (k, i) : ℂ) * (τ *ᵥ fun j => (b k j : ℂ)) i + ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ))`. Simplify using `only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1 : qv ((e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) k) = qv (e ν k) + fun i => (N * b k i : ℂ)`. Use function extensionality and compare the values at `i`.

Simplify using `[qv]`. Rewrite using `[h1, quad_add hτ.1]`. Use `congr 2`. Establish `h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ)`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[h2, mulVec_smul, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [qv, e, of_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `h` using `hφe (fun p => ν p + N ^ 2 * b p.1 p.2)`. Rewrite `h` using `[← hshift]`. Rewrite using `[h, hφe, hQ, ha 0, ha (fun p => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) ν, ← integral_mul_const, ← integral_mul_const]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[← hq b]`. Establish `h3 : (fun k => (fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) k + τ *ᵥ fun i => (N * b k i : ℂ)) = fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + fun p : Fin n × Fin g => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) (k, i)`. Use function extensionality and compare the values at `k i`. Establish `h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ)`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[h2, mulVec_smul]`. Simplify using `[mul_add]`. Rewrite using `[h3, mul_comm (cexp _) (Θ _)]`.

Simplify using `only [mul_assoc (Θ _), ← Complex.exp_add]`. Use `congr 2`. Establish `h4 : ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ (fun i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) = ∑ k, ∑ i, (N : ℂ) ^ 2 * b k i * x (k, i)`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.zero_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, h4]`. Simplify using `only [Fintype.sum_prod_type, Pi.zero_apply, add_zero, mul_add, add_mul, Finset.sum_add_distrib, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨φ, ⟨N, hN, fun x hx => ?_, fun x y hy => ?_⟩, fun ζ => ?_⟩` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨ν, rfl⟩ : x ∈ Set.range e := by`. Assume the negation of the conclusion as `h`. Conclude with `hx (hφ0 x h)`. Introduce `k i`. Establish `: ((N : ℚ) • e ν) k i = algebraMap ℤ ℚ (ν (k, i))`.

Simplify using `only [e, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Establish `: ∀ k i, ∃ m : ℤ, (m : ℚ) = y k i` using `fun k i => by`.

Simplify using `using IsIntegrallyClosed.isIntegral_iff.1 (hy k i)`. Use `choose b hb using this`. Choose the witnesses or unpack the hypotheses as in `rfl : y = Matrix.of fun k i => (b k i : ℚ) := by`. Use extensionality with `k i`. Simplify using `[hb]`.

Distinguish the cases in `hx : x ∈ Set.range e`. Take `⟨ν, rfl⟩` from `hx`. Conclude with `hlaw ν b`. Rewrite using `[hφ0 x hx]`. Use `hφ0 _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨ν, hν⟩`. Use `hx ⟨fun p => ν p + N ^ 2 * (-b) p.1 p.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hshift, hν]`. Use extensionality with `k i`. Simplify using the standard rewrite rules.

Establish `h1` using `hs fun p => ζ p.1 p.2 / N`. Establish `h2 : (fun k i => (N : ℂ) * (ζ k i / N)) = ζ`. Use function extensionality and compare the values at `k i`. Clear the denominators using the available nonvanishing facts. Simplify using `only [h2] at h1`.

Use `HasSum.tsum_eq ?_` and prove the remaining obligations. Use `(he.hasSum_iff fun x hx => by rw [hφ0 x hx, zero_mul]).1 ?_` and prove the remaining obligations. Use `h1 using 2 with ν` and compare the differences between its conclusion and the goal. Simplify using `only [Function.comp_apply]`. Rewrite using `[hφe, mul_assoc, ← Complex.exp_add]`.

Use `congr 2`. Establish `h3 : ∑ k, qv (e ν k) ⬝ᵥ ζ k = ∑ p : Fin n × Fin g, (ν p : ℂ) * (ζ p.1 p.2 / N)`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [qv, e, of_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, h3]`. Simplify using `only [Q]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_thS_eq : ∀ (n g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ Siegel (Fin g) → ∀ (N : ℕ), 0 < N → ∀ Θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ Θ → (∀ (a : Fin n → Fin g → ℤ) ζ, Θ (fun k i => ζ k i + N * a k i) = Θ ζ) → (∀ (b : Fin n → Fin g → ℤ) ζ, cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k))) * Θ (fun k => ζ k + τ *ᵥ fun i => (N * b k i : ℂ)) = Θ ζ) → ∃ φ : TF n g, IsSB φ ∧ ∀ ζ, thS φ τ ζ = Θ ζ := by
  intro n g τ hτ N hN Θ hΘ hp hq
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨a, hs, ha⟩ := exists_fourier_entire (ι := Fin n × Fin g)
    (fun z => Θ fun k i => N * z (k, i)) (hΘ.comp (by fun_prop)) (fun z m => by
      rw [← hp (fun k i => m (k, i)) fun k i => N * z (k, i)]
      congr 1
      funext k i
      simp [mul_add])
  let e : (Fin n × Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ :=
    fun ν => Matrix.of fun k i => (ν (k, i) : ℚ) / N
  have he : Function.Injective e := by
    intro m m' hmn
    funext ⟨k, i⟩
    have h1 : (m (k, i) : ℚ) / N = (m' (k, i) : ℚ) / N := congrFun (congrFun hmn k) i
    exact_mod_cast (div_left_inj' hNq).1 h1
  let Q : Matrix (Fin n) (Fin g) ℚ → ℂ := fun x => ∑ k, qv (x k) ⬝ᵥ τ *ᵥ qv (x k)
  let φ : TF n g := fun x => Function.extend e a 0 x * cexp (-(π * I * Q x))
  have hφe : ∀ ν, φ (e ν) = a ν * cexp (-(π * I * Q (e ν))) := fun ν => by
    simp only [φ, he.extend_apply]
  have hφ0 : ∀ x, x ∉ Set.range e → φ x = 0 := fun x hx => by
    simp only [φ]
    rw [Function.extend_apply' _ _ _ hx]
    simp
  have hshift : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ)) =
        e (fun p => ν p + N ^ 2 * b p.1 p.2) := by
    intro ν b
    ext k i
    simp only [e, of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have hlaw : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      φ (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = φ (e ν) := by
    intro ν b
    have hQ : Q (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) =
        Q (e ν) + 2 * ∑ k, ∑ i, (ν (k, i) : ℂ) * (τ *ᵥ fun j => (b k j : ℂ)) i +
          ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) := by
      simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : qv ((e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) k) =
          qv (e ν k) + fun i => (N * b k i : ℂ) := by
        funext i
        simp [qv]
      rw [h1, quad_add hτ.1]
      congr 2
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    have h := hφe (fun p => ν p + N ^ 2 * b p.1 p.2)
    rw [← hshift] at h
    rw [h, hφe, hQ, ha 0, ha (fun p => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) ν,
      ← integral_mul_const, ← integral_mul_const]
    congr 1
    funext x
    rw [← hq b]
    have h3 : (fun k => (fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) k +
        τ *ᵥ fun i => (N * b k i : ℂ)) =
        fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) +
          fun p : Fin n × Fin g => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) (k, i) := by
      funext k i
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul]
      simp [mul_add]
    rw [h3, mul_comm (cexp _) (Θ _)]
    simp only [mul_assoc (Θ _), ← Complex.exp_add]
    congr 2
    have h4 : ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ
        (fun i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) =
        ∑ k, ∑ i, (N : ℂ) ^ 2 * b k i * x (k, i) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.zero_apply]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h4]
    simp only [Fintype.sum_prod_type, Pi.zero_apply, add_zero, mul_add, add_mul,
      Finset.sum_add_distrib, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring
  refine ⟨φ, ⟨N, hN, fun x hx => ?_, fun x y hy => ?_⟩, fun ζ => ?_⟩
  · obtain ⟨ν, rfl⟩ : x ∈ Set.range e := by
      by_contra h
      exact hx (hφ0 x h)
    intro k i
    have : ((N : ℚ) • e ν) k i = algebraMap ℤ ℚ (ν (k, i)) := by
      simp only [e, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      field_simp
    rw [this]
    exact isIntegral_algebraMap
  · have : ∀ k i, ∃ m : ℤ, (m : ℚ) = y k i := fun k i => by
      simpa using IsIntegrallyClosed.isIntegral_iff.1 (hy k i)
    choose b hb using this
    obtain rfl : y = Matrix.of fun k i => (b k i : ℚ) := by
      ext k i
      simp [hb]
    by_cases hx : x ∈ Set.range e
    · obtain ⟨ν, rfl⟩ := hx
      exact hlaw ν b
    · rw [hφ0 x hx]
      refine hφ0 _ ?_
      rintro ⟨ν, hν⟩
      refine hx ⟨fun p => ν p + N ^ 2 * (-b) p.1 p.2, ?_⟩
      rw [← hshift, hν]
      ext k i
      simp
  · have h1 := hs fun p => ζ p.1 p.2 / N
    have h2 : (fun k i => (N : ℂ) * (ζ k i / N)) = ζ := by
      funext k i
      field_simp
    simp only [h2] at h1
    refine HasSum.tsum_eq ?_
    refine (he.hasSum_iff fun x hx => by rw [hφ0 x hx, zero_mul]).1 ?_
    convert h1 using 2 with ν
    simp only [Function.comp_apply]
    rw [hφe, mul_assoc, ← Complex.exp_add]
    congr 2
    have h3 : ∑ k, qv (e ν k) ⬝ᵥ ζ k = ∑ p : Fin n × Fin g, (ν p : ℂ) * (ζ p.1 p.2 / N) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply]
      push_cast
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3]
    simp only [Q]
    ring

end GlobalTheory.Ker.LevelTheta
