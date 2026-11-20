import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.Twist.FockLogDeriv

/- English proof (translation)
Apply `hT` to reduce the goal to its premises. Introduce `z`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.mp hU`. Establish `h0 : T y₀ b = 0` using `hb y₀ (hball (Metric.mem_ball_self hε))`. Establish `hz1 : 0 < ‖z‖ + 1` using `by positivity`.

Use `set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht`. Establish `htpos : 0 < t` using `by positivity`. Establish `htz : t * (‖z‖ + 1) = ε / 2`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts.

Establish `hmem : y₀ + t • z ∈ U`. Apply `hball` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]`. Use polynomial arithmetic with `[norm_nonneg z]`. Establish `h1` using `hb _ hmem`.

Rewrite `h1` using `[map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h0, zero_add, smul_eq_mul]`. Conclude with `(mul_eq_zero.mp h1).resolve_left htpos.ne'`.
-/
theorem eq_zero_of_forall_nhds {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (y₀ : V) (U : Set V) (hU : U ∈ 𝓝 y₀) (b : V) (hb : ∀ y ∈ U, T y b = 0) : b = 0 := by
  apply hT
  intro z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h0 : T y₀ b = 0 := hb y₀ (hball (Metric.mem_ball_self hε))
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have htz : t * (‖z‖ + 1) = ε / 2 := by
    rw [ht]; field_simp
  have hmem : y₀ + t • z ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    nlinarith [norm_nonneg z]
  have h1 := hb _ hmem
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h0, zero_add, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left htpos.ne'

/- English proof (translation)
Set `Φ : V × V →ₗ[ℝ] (V → ℂ)` to `{ toFun := fun p y => fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y map_add' := by`. Introduce `p q`. Use function extensionality and compare the values at `y`. Simplify using `only [Prod.fst_add, Prod.snd_add, map_add, Complex.ofReal_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := by`. Introduce `s p`. Use function extensionality and compare the values at `y`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Pi.smul_apply, Complex.real_smul]`. Use `ring }`.

Establish `hΦ : ∀ p y, Φ p y = fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y` using `fun p y => rfl`. Establish `hEΦ : ∀ p y, Φ (Jm p) y = Complex.I * Φ p y` using `fun p y => by rw [hΦ, hΦ]; exact hE p y`. Establish `hΦ0 : ∀ w y, Φ (0, w) y = (-(2 * Real.pi * Complex.I)) * ((T y w : ℝ) : ℂ) * f₀ y`. Introduce `w y`. Rewrite using `[hΦ]`.

Simplify using `only [map_zero, zero_add]`. Set `Q : V × V →ₗ[ℝ] V × V` to `(LinearMap.inr ℝ V V) ∘ₗ (LinearMap.fst ℝ V V) + Jm ∘ₗ (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.snd ℝ V V)`. Set `Θ : V × V →ₗ[ℝ] (V → ℂ)` to `Φ ∘ₗ Q`. Establish `hΘ : ∀ w₁ w₂ y, Θ (w₁, w₂) y = (-(2 * Real.pi * Complex.I)) * ((T y w₁ : ℝ) : ℂ) * f₀ y + Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y w₂ : ℝ) : ℂ) * f₀ y)`. Introduce `w₁ w₂ y`.

Establish `e : Θ (w₁, w₂) = Φ (0, w₁) + Φ (Jm (0, w₂))` using `map_add Φ _ _`. Rewrite using `[e, Pi.add_apply, hEΦ, hΦ0, hΦ0]`. Choose the witnesses or unpack the hypotheses as in `⟨y₀, hy₀⟩ : ∃ y₀, f₀ y₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hf (SchwartzMap.ext fun y => by simp [h y])`. Establish `hU : {y | f₀ y ≠ 0} ∈ 𝓝 y₀` using `(isOpen_compl_singleton.preimage f₀.continuous).mem_nhds hy₀`. Establish `hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `hinj : Function.Injective Θ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce and unpack `⟨w₁, w₂⟩ h`. Establish `hsplit : ∀ y ∈ {y | f₀ y ≠ 0}, T y w₁ = 0 ∧ T y w₂ = 0`. Introduce `y hy`. Establish `h0 : Θ (w₁, w₂) y = 0` using `by rw [h]; rfl`. Rewrite `h0` using `[hΘ]`.

Establish `h3 : ((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ) = 0`. Establish `h4 : (-(2 * Real.pi * Complex.I)) * f₀ y * (((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ)) = 0`. Rewrite using `[← h0]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp h4 with h5 | h5` into its components or cases.

Break down `mul_eq_zero.mp h5 with h6 | h6` into its components or cases. Conclude with `absurd h6 hc`. Conclude with `absurd h6 hy`. Conclude with `h5`. Establish `hre` using `congrArg Complex.re h3`.

Establish `him` using `congrArg Complex.im h3`. Simplify using `at hre him`. Conclude with `⟨hre, him⟩`. Establish `e1` using `eq_zero_of_forall_nhds T hT y₀ _ hU w₁ fun y hy => (hsplit y hy).1`. Establish `e2` using `eq_zero_of_forall_nhds T hT y₀ _ hU w₂ fun y hy => (hsplit y hy).2`.

Rewrite using `[e1, e2]`. Both sides reduce to the same expression. Establish `hle : LinearMap.range Θ ≤ LinearMap.range Φ` using `LinearMap.range_comp_le_range Q Φ`. Establish `hrange : LinearMap.range Θ = LinearMap.range Φ`. Apply `Submodule.eq_of_le_of_finrank_le hle` to reduce the goal to its premises.

Rewrite using `[LinearMap.finrank_range_of_inj hinj]`. Conclude with `LinearMap.finrank_range_le Φ`. Establish `hmem : ∀ a, (Φ ∘ₗ LinearMap.inl ℝ V V) a ∈ LinearMap.range Θ` using `fun a => by`. Rewrite using `[hrange]`. Conclude with `LinearMap.mem_range_self Φ _`.

Set `e` to `LinearEquiv.ofInjective Θ hinj`. Set `W : V →ₗ[ℝ] V × V` to `e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Θ) (Φ ∘ₗ LinearMap.inl ℝ V V) hmem`. Establish `hW : ∀ a, Θ (W a) = Φ (a, 0)`. Introduce `a`. Establish `h` using `congrArg Subtype.val (e.apply_symm_apply ⟨Φ (a, 0), hmem a⟩)`.

Conclude with `h`. Set `m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ` to `LinearMap.mk₂ ℝ (fun a y => (-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) + Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) (by intro a₁ a₂ y; simp only [map_add, Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring) (by intro s a y; simp only [map …`. Use `⟨m, fun a y => ?_⟩` and prove the remaining obligations. Establish `h1 : Φ (a, 0) y = fderiv ℝ f₀ y a`. Rewrite using `[hΦ]`.

Simplify using `only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]`. Establish `h2` using `hΘ (W a).1 (W a).2 y`. Rewrite `h2` using `[Prod.mk.eta, hW, h1]`. Rewrite using `[h2]`. Use `show _ = ((-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) + Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) * f₀ y`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (Jm : V × V →ₗ[ℝ] V × V) (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (hE : ∀ (p : V × V) (y : V), fderiv ℝ f₀ y (Jm p).1
        + (-(2 * Real.pi * Complex.I)) * ((T y (Jm p).2 : ℝ) : ℂ) * f₀ y
      = Complex.I * (fderiv ℝ f₀ y p.1
        + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y)) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ, ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y := by
  let Φ : V × V →ₗ[ℝ] (V → ℂ) :=
    { toFun := fun p y => fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y
      map_add' := by
        intro p q
        funext y
        simp only [Prod.fst_add, Prod.snd_add, map_add, Complex.ofReal_add, Pi.add_apply]
        ring
      map_smul' := by
        intro s p
        funext y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Pi.smul_apply, Complex.real_smul]
        ring }
  have hΦ : ∀ p y, Φ p y = fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y :=
    fun p y => rfl
  have hEΦ : ∀ p y, Φ (Jm p) y = Complex.I * Φ p y := fun p y => by rw [hΦ, hΦ]; exact hE p y
  have hΦ0 : ∀ w y, Φ (0, w) y = (-(2 * Real.pi * Complex.I)) * ((T y w : ℝ) : ℂ) * f₀ y := by
    intro w y
    rw [hΦ]
    simp only [map_zero, zero_add]
  let Q : V × V →ₗ[ℝ] V × V :=
    (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.fst ℝ V V) + Jm ∘ₗ (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.snd ℝ V V)
  let Θ : V × V →ₗ[ℝ] (V → ℂ) := Φ ∘ₗ Q
  have hΘ : ∀ w₁ w₂ y, Θ (w₁, w₂) y = (-(2 * Real.pi * Complex.I)) * ((T y w₁ : ℝ) : ℂ) * f₀ y +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y w₂ : ℝ) : ℂ) * f₀ y) := by
    intro w₁ w₂ y
    have e : Θ (w₁, w₂) = Φ (0, w₁) + Φ (Jm (0, w₂)) := map_add Φ _ _
    rw [e, Pi.add_apply, hEΦ, hΦ0, hΦ0]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f₀ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SchwartzMap.ext fun y => by simp [h y])
  have hU : {y | f₀ y ≠ 0} ∈ 𝓝 y₀ := (isOpen_compl_singleton.preimage f₀.continuous).mem_nhds hy₀
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w₁, w₂⟩ h
    have hsplit : ∀ y ∈ {y | f₀ y ≠ 0}, T y w₁ = 0 ∧ T y w₂ = 0 := by
      intro y hy
      have h0 : Θ (w₁, w₂) y = 0 := by rw [h]; rfl
      rw [hΘ] at h0
      have h3 : ((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ) = 0 := by
        have h4 : (-(2 * Real.pi * Complex.I)) * f₀ y *
            (((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ)) = 0 := by
          rw [← h0]; ring
        rcases mul_eq_zero.mp h4 with h5 | h5
        · rcases mul_eq_zero.mp h5 with h6 | h6
          · exact absurd h6 hc
          · exact absurd h6 hy
        · exact h5
      have hre := congrArg Complex.re h3
      have him := congrArg Complex.im h3
      simp at hre him
      exact ⟨hre, him⟩
    have e1 := eq_zero_of_forall_nhds T hT y₀ _ hU w₁ fun y hy => (hsplit y hy).1
    have e2 := eq_zero_of_forall_nhds T hT y₀ _ hU w₂ fun y hy => (hsplit y hy).2
    rw [e1, e2]; rfl
  have hle : LinearMap.range Θ ≤ LinearMap.range Φ := LinearMap.range_comp_le_range Q Φ
  have hrange : LinearMap.range Θ = LinearMap.range Φ := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.finrank_range_of_inj hinj]
    exact LinearMap.finrank_range_le Φ
  have hmem : ∀ a, (Φ ∘ₗ LinearMap.inl ℝ V V) a ∈ LinearMap.range Θ := fun a => by
    rw [hrange]; exact LinearMap.mem_range_self Φ _
  let e := LinearEquiv.ofInjective Θ hinj
  let W : V →ₗ[ℝ] V × V :=
    e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Θ) (Φ ∘ₗ LinearMap.inl ℝ V V) hmem
  have hW : ∀ a, Θ (W a) = Φ (a, 0) := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨Φ (a, 0), hmem a⟩)
    exact h
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun a y => (-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ)))
    (by intro a₁ a₂ y; simp only [map_add, Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
    (by intro a y₁ y₂; simp only [map_add, LinearMap.add_apply, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
  refine ⟨m, fun a y => ?_⟩
  have h1 : Φ (a, 0) y = fderiv ℝ f₀ y a := by
    rw [hΦ]; simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  have h2 := hΘ (W a).1 (W a).2 y
  rw [Prod.mk.eta, hW, h1] at h2
  rw [h2]
  show _ = ((-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) * f₀ y
  ring

end GlobalTheory.CompanionTheory.Twist.FockLogDeriv
