import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
open Classical MeasureTheory

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

def scalAt {a : ℕ} (τ₀ : ι) (ζ : ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ₀ then ζ • 1 else 1

def degAt {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : ℕ := t.sum fun y n => if y.1 = τ₀ then n else 0

/- English proof (translation)
Take `⟨τ, i, j⟩` from `y`. Distinguish the cases in `h : τ = τ₀`. Substitute `h` using the available equality. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[scalAt, Matrix.smul_apply, Matrix.one_apply]`.

Introduce `b _ hb`. Simplify using `[scalAt, Matrix.smul_apply, Matrix.one_apply, hb]`. Simplify using the standard rewrite rules. Simplify using `[scalAt, h, Matrix.one_apply]`.
-/
theorem colSub_scalAt_X {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (y : Var ι d a) :
    (∑ j' : Fin a, C (scalAt τ₀ ζ y.1 j' y.2.2) * (X (y.1, y.2.1, j') : Pol ι d a)) =
      C (if y.1 = τ₀ then ζ else 1) * X y := by
  obtain ⟨τ, i, j⟩ := y
  by_cases h : τ = τ₀
  · subst h
    rw [Finset.sum_eq_single j]
    · simp [scalAt, Matrix.smul_apply, Matrix.one_apply]
    · intro b _ hb
      simp [scalAt, Matrix.smul_apply, Matrix.one_apply, hb]
    · simp
  · simp [scalAt, h, Matrix.one_apply]

/- English proof (translation)
Unfold `colSub`. Rewrite using `[aeval_monomial]`. Simplify using `only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]`. Establish `h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t)`. Unfold `Finsupp.prod degAt Finsupp.sum`.

Rewrite using `[← Finset.prod_pow_eq_pow_sum, map_prod]`. Use `Finset.prod_congr rfl fun y _ => ?_` and prove the remaining obligations. Use `beta_reduce`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]`.
-/
theorem colSub_scalAt_monomial {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by
  unfold colSub
  rw [aeval_monomial]
  simp only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]
  have h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t) := by
    unfold Finsupp.prod degAt Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

/- English proof (translation)
Unfold `degAt Finsupp.sum`. Apply the tactic sequence `exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega`.
-/
theorem degAt_le {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by
  unfold degAt Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `: (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `y`. Simplify using `only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this`.
-/
theorem colSub_mul {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by
  have : (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

/- English proof (translation)
Generalize the expression as in `hM : N + P.totalDegree + 1 = M at hω ⊢`. Use `conv_lhs => rw [as_sum P]`. Simplify using `only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun t ht => ?_` and prove the remaining obligations.

Establish `hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0`. Establish `hne : ω ^ (N + degAt τ₀ t) ≠ 1`. Rewrite using `[Ne, hω.pow_eq_one_iff_dvd]`. Introduce `hdvd`. Establish `h1` using `degAt_le τ₀ t`.

Establish `h2` using `le_totalDegree ht`. Use `Nat.le_of_dvd (by omega) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]`. Establish `: ∀ k ∈ Finset.range M, (ω ^ k) ^ N • (monomial t (coeff t P * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) = monomial t (coeff t P * (ω ^ (N + degAt τ₀ t)) ^ k)`.

Introduce `k _`. Rewrite using `[smul_monomial, smul_eq_mul]`. Use `congr 1`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]`.
-/
theorem sum_scalAt_eq_zero {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by
  generalize hM : N + P.totalDegree + 1 = M at hω ⊢
  conv_lhs => rw [as_sum P]
  simp only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0 := by
    have hne : ω ^ (N + degAt τ₀ t) ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hdvd
      have h1 := degAt_le τ₀ t
      have h2 := le_totalDegree ht
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ k ∈ Finset.range M,
      (ω ^ k) ^ N • (monomial t (coeff t P * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) =
        monomial t (coeff t P * (ω ^ (N + degAt τ₀ t)) ^ k) := by
    intro k _
    rw [smul_monomial, smul_eq_mul]
    congr 1
    rw [← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single τ₀]`. Simplify using `[scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]`. Introduce `τ _ h`. Simplify using `[scalAt, h]`. Simplify using the standard rewrite rules.
-/
theorem prod_det_scalAt_zpow {ι : Type} [Fintype ι] {a : ℕ} (τ₀ : ι) (ζ : ℂ) (m : ι → ℤ) (n : ℕ)
    (hn : (n : ℤ) = m τ₀) : (∏ τ, (scalAt (a := a) τ₀ ζ τ).det ^ (m τ)) = ζ ^ (a * n) := by
  rw [Finset.prod_eq_single τ₀]
  · simp [scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]
  · intro τ _ h
    simp [scalAt, h]
  · simp

/- English proof (translation)
Introduce `ι _ a d m τ₀ ha hm K _ _ ν hν hinv ρ _ hρ Λ P`. Use `set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def`. Use `set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def`. Use `set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def`. Use `show ∫ g, f g ∂ν = 0`.

Distinguish the cases in `hint : Integrable f ν`. Use `swap`. Conclude with `integral_undef hint`. Establish `hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν`. Introduce `u`.

Establish `hmap : Measure.map (fun x => u * x) ν = ν` using `map_mul_left_eq_self ν u`. Establish `hae : AEMeasurable (fun x => u * x) ν`. Assume the negation of the conclusion as `h`. Rewrite `hmap` using `[Measure.map_of_not_aemeasurable h]`. Conclude with `(IsProbabilityMeasure.ne_zero ν) hmap.symm`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Integrable f (Measure.map (fun x => u * x) ν)` using `by rw [hmap]; exact hint`. Conclude with `this.comp_aemeasurable hae`. Establish `h` using `integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)`. Rewrite `h` using `[hmap]`.

Conclude with `h.symm`. Take `⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀` from `⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩`. Establish `hnpos : 0 < n` using `by omega`. Use `set N := a * n with hN_def`. Establish `hN : 0 < N` using `Nat.mul_pos ha hnpos`.

Use `set M := N + P.totalDegree + 1 with hM_def`. Establish `hM0 : M ≠ 0` using `by omega`. Use `set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def`. Establish `hω : IsPrimitiveRoot ω M` using `Complex.isPrimitiveRoot_exp M hM0`. Establish `hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ`.

Introduce `k`. Establish `hnorm : ‖ω ^ k‖ = 1` using `by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]`. Establish `hc : ω ^ k * star (ω ^ k) = 1`. Rewrite using `[RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]`. Evaluate the numerical expressions.

Rewrite using `[Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hc, one_smul]`. Set `U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ` to `fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1`. Establish `hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ`. Introduce `k τ`. Simplify using `only [U, scalAt]`.

Apply the tactic sequence `split_ifs <;> rfl`. Use `choose u hu using fun k => hρ (U k)`. Establish `hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P))`. Introduce `k g`. Establish `hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ`.

Use function extensionality and compare the values at `τ`. Simplify using `only [hB_def, map_mul, Pi.mul_apply, hu k]`. Rewrite using `[Submonoid.coe_mul, hU k τ]`. Simplify using `only [scalAt]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]`.

Simplify using `only [hf_def, hc_def]`. Rewrite using `[hBu, colSub_mul, map_smul, smul_eq_mul]`. Simplify using `only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Rewrite using `[prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0`. Introduce `g`. Simplify using `only [hpt, ← Finset.mul_sum, ← map_sum]`. Establish `: ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) = colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P)`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul]`. Rewrite using `[this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]`. Establish `hkey : (M : ℂ) * ∫ x, f x ∂ν = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Use `_ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν := (integral_finset_sum _ fun k _ => (hinvar (u k)).1).symm`. Use `_ = 0 := by simp [hsum0]`. Conclude with `(mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)`.
-/
theorem integral_detZpow_colSub_eq_zero :
    ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K]
      [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
    ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)),
      (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
      Function.Surjective ρ →
    ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d m τ₀ ha hm K _ _ ν hν hinv ρ _ hρ Λ P
  set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def
  set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def
  set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def
  show ∫ g, f g ∂ν = 0
  by_cases hint : Integrable f ν
  swap
  · exact integral_undef hint

  have hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν := by
    intro u
    have hmap : Measure.map (fun x => u * x) ν = ν := map_mul_left_eq_self ν u
    have hae : AEMeasurable (fun x => u * x) ν := by
      by_contra h
      rw [Measure.map_of_not_aemeasurable h] at hmap
      exact (IsProbabilityMeasure.ne_zero ν) hmap.symm
    refine ⟨?_, ?_⟩
    · have : Integrable f (Measure.map (fun x => u * x) ν) := by rw [hmap]; exact hint
      exact this.comp_aemeasurable hae
    · have h := integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀ := ⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩
  have hnpos : 0 < n := by omega
  set N := a * n with hN_def
  have hN : 0 < N := Nat.mul_pos ha hnpos
  set M := N + P.totalDegree + 1 with hM_def
  have hM0 : M ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM0
  have hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    intro k
    have hnorm : ‖ω ^ k‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]
    have hc : ω ^ k * star (ω ^ k) = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      hc, one_smul]
  let U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ := fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1
  have hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ := by
    intro k τ
    simp only [U, scalAt]
    split_ifs <;> rfl
  choose u hu using fun k => hρ (U k)

  have hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P)) := by
    intro k g
    have hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ := by
      funext τ
      simp only [hB_def, map_mul, Pi.mul_apply, hu k]
      rw [Submonoid.coe_mul, hU k τ]
      simp only [scalAt]
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    simp only [hf_def, hc_def]
    rw [hBu, colSub_mul, map_smul, smul_eq_mul]
    simp only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    rw [prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]
    ring
  have hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0 := by
    intro g
    simp only [hpt, ← Finset.mul_sum, ← map_sum]
    have : ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) =
        colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P) := by
      rw [map_sum]; simp only [map_smul]
    rw [this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]
  have hkey : (M : ℂ) * ∫ x, f x ∂ν = 0 := by
    calc (M : ℂ) * ∫ x, f x ∂ν = ∑ k ∈ Finset.range M, ∫ x, f (u k * x) ∂ν := by
          rw [Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν :=
          (integral_finset_sum _ fun k _ => (hinvar (u k)).1).symm
      _ = 0 := by simp [hsum0]
  exact (mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)

end GlobalTheory.MinorFrame
