import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaTangent

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_closure_iff_frequently]`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Filter.not_frequently]`. Apply `h0` to reduce the goal to its premises.

Establish `h1 : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ))` using `h.mono fun y hy => by simpa using hy`. Use `GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hf.differentiableOn (differentiableOn_const (0 : ℂ)) (Set.mem_univ x) h1` as an intermediate fact. Use function extensionality and compare the values at `y`. Conclude with `this (Set.mem_univ y)`.
-/
theorem dense_ne_zero [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f)
    (h0 : f ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  rw [mem_closure_iff_frequently]
  by_contra h
  rw [Filter.not_frequently] at h
  apply h0
  have h1 : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := h.mono fun y hy => by simpa using hy
  have := GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hf.differentiableOn
    (differentiableOn_const (0 : ℂ)) (Set.mem_univ x) h1
  funext y
  exact this (Set.mem_univ y)

/- English proof (translation)
Use `choose φ hφ using h`. Use `⟨fun a => φ a a, fun a => ?_, fun x => (hφ x).self_of_nhds.2⟩` and prove the remaining obligations. Establish `key : (fun x => φ x x) =ᶠ[𝓝 a] φ a` using `by filter_upwards [(hφ a).eventually_nhds] with x hx`. Establish `hfr : ∃ᶠ y in 𝓝 x, y ∈ {x | θ x ≠ 0}` using `mem_closure_iff_frequently.mp (hU x)`. Establish `hfr2 : ∃ᶠ y in 𝓝 x, φ x y = φ a y`.

Use `(hfr.and_eventually (hx.and (hφ x))).mono ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy, ⟨-, h1⟩, -, h2⟩`. Conclude with `mul_right_cancel₀ hy (h2.symm.trans h1)`. Conclude with `tendsto_nhds_unique_of_frequently_eq (hφ x).self_of_nhds.1.continuousAt hx.self_of_nhds.1.continuousAt hfr2`. Conclude with `(hφ a).self_of_nhds.1.congr_of_eventuallyEq key`.
-/
theorem exists_entire_quotient {θ D : E → ℂ} (hU : Dense {x | θ x ≠ 0})
    (h : ∀ a, ∃ φ : E → ℂ, ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ φ x ∧ D x = φ x * θ x) :
    ∃ ψ : E → ℂ, Differentiable ℂ ψ ∧ ∀ x, D x = ψ x * θ x := by
  choose φ hφ using h
  refine ⟨fun a => φ a a, fun a => ?_, fun x => (hφ x).self_of_nhds.2⟩
  have key : (fun x => φ x x) =ᶠ[𝓝 a] φ a := by
    filter_upwards [(hφ a).eventually_nhds] with x hx
    have hfr : ∃ᶠ y in 𝓝 x, y ∈ {x | θ x ≠ 0} := mem_closure_iff_frequently.mp (hU x)
    have hfr2 : ∃ᶠ y in 𝓝 x, φ x y = φ a y := by
      refine (hfr.and_eventually (hx.and (hφ x))).mono ?_
      rintro y ⟨hy, ⟨-, h1⟩, -, h2⟩
      exact mul_right_cancel₀ hy (h2.symm.trans h1)
    exact tendsto_nhds_unique_of_frequently_eq (hφ x).self_of_nhds.1.continuousAt
      hx.self_of_nhds.1.continuousAt hfr2
  exact (hφ a).self_of_nhds.1.congr_of_eventuallyEq key

/- English proof (translation)
Use `set k : ℂ := (m : ℂ) + 1 with hk`. Establish `hk0 : k ≠ 0` using `Nat.cast_add_one_ne_zero m`. Use `set D : E → ℂ := fun x => fderiv ℂ θ x ξ with hD`. Establish `hDd : Differentiable ℂ D`. Rewrite using `[← differentiableOn_univ]`.

Conclude with `GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_univ hθ.differentiableOn ξ`. Establish `hU` using `dense_ne_zero hθ h0`. Establish `hUo : IsOpen {x | θ x ≠ 0}` using `isOpen_ne_fun hθ.continuous continuous_const`. Take `⟨x₀, hx₀⟩ : ∃ x, θ x ≠ 0` from `hU.nonempty`. Establish `hU' : ∀ (p : E) (c : ℂ), c ≠ 0 → Dense {x | θ (p - c • x) ≠ 0}`.

Introduce `p c hc`. Use `dense_ne_zero (f := fun x => θ (p - c • x)) (hθ.comp (by fun_prop)) fun h => hx₀ ?_` and prove the remaining obligations. Use `congrFun h (c⁻¹ • (p - x₀))` as an intermediate fact. Simplify `this` using `[smul_smul, hc]`. Take `⟨ψ, hψ, hDψ⟩` from `exists_entire_quotient (D := D) hU (by`.

Introduce `a`. Take `⟨b, hb1, hb2⟩` from `((hU' (s - a) k hk0).inter_of_isOpen_right hU hUo).nonempty`. Simplify using `only [Set.mem_setOf_eq] at hb1 hb2`. Use `⟨fun x => γ - k * D b / θ b - D (s - x - k • b) / θ (s - x - k • b), ?_⟩` and prove the remaining obligations. Establish `hc : ContinuousAt (fun x => θ (s - x - k • b)) a` using `(hθ.continuous.comp (by fun_prop)).continuousAt`.

Use `filter_upwards [hc.eventually_ne hb1] with x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `d1 : DifferentiableAt ℂ (fun x => D (s - x - k • b)) x` using `(hDd.comp (f := fun x => s - x - k • b) (by fun_prop)) x`. Establish `d2 : DifferentiableAt ℂ (fun x => θ (s - x - k • b)) x` using `(hθ.comp (f := fun x => s - x - k • b) (by fun_prop)) x`. Simplify using `only [div_eq_mul_inv]`.

Conclude with `(differentiableAt_const _).sub (d1.mul (d2.inv hx))`. Use `hrel x b` as an intermediate fact. Establish `hp : θ b ^ m ≠ 0` using `pow_ne_zero _ hb2`. Clear the denominators using the available nonvanishing facts. Apply `mul_left_cancel₀ hp` to reduce the goal to its premises.

Simplify using `only [hD]`. Take the linear combination `this)`. Establish `hψc` using `hψ.continuous`. Establish `hfun : ∀ a b : E, ψ a + k * ψ b + ψ (s - a - k • b) = γ`. Establish `h1 : ∀ b, θ b ≠ 0 → ∀ a, ψ a + k * ψ b + ψ (s - a - k • b) = γ`.

Introduce `b hb a`. Establish `hd` using `(hU' (s - k • b) 1 one_ne_zero).inter_of_isOpen_right hU hUo`. Use `congrFun (Continuous.ext_on hd (f := fun a => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ) (by fun_prop) continuous_const ?_) a` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`. Simplify using `only [Set.mem_setOf_eq, one_smul] at hx1 hx2`.

Rewrite `hx1` using `[sub_right_comm]`. Use `hrel x b` as an intermediate fact. Establish `e1` using `hDψ x`. Establish `e2` using `hDψ b`. Establish `e3` using `hDψ (s - x - k • b)`.

Simplify using `only [hD] at e1 e2 e3`. Rewrite `this` using `[e1, e2, e3]`. Apply `mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hx2 (pow_ne_zero (m + 1) hb)) hx1)` to reduce the goal to its premises. Take the linear combination `this`. Introduce `a b`.

Conclude with `congrFun (Continuous.ext_on hU (f := fun b => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ) (by fun_prop) continuous_const fun x hx => h1 x hx a) b`. Establish `hdiff : ∀ y w : E, ψ (y + w) = ψ y + (ψ w - ψ 0)`. Introduce `y w`. Establish `e1` using `hfun (y + w) (k⁻¹ • (s - y - w))`. Establish `e2` using `hfun y (k⁻¹ • (s - y - w))`.

Rewrite `e1`, `e2` using `[smul_inv_smul₀ hk0]`. Rewrite `e1` using `[show s - (y + w) - (s - y - w) = 0 by abel]`. Rewrite `e2` using `[show s - y - (s - y - w) = w by abel]`. Take the linear combination `e1 - e2`. Establish `hκ : Differentiable ℂ (fun r : ℂ => ψ (r • ξ) - ψ 0)` using `by fun_prop`.

Take `⟨K, hK⟩` from `hκ.isExactOn_univ`. Use `⟨fun y => Complex.exp (t * ψ y + (K t - K 0)), by fun_prop, fun y => Complex.exp_ne_zero _, fun y => ?_⟩` and prove the remaining obligations. Establish `hF : ∀ r : ℂ, HasDerivAt (fun r : ℂ => θ (y + r • ξ) * Complex.exp (-(r * ψ y + K r))) 0 r`. Introduce `r`. Establish `hl : HasDerivAt (fun r : ℂ => y + r • ξ) ξ r`.

Simplify using `using ((hasDerivAt_id r).smul_const ξ).const_add y`. Establish `h1 : HasDerivAt (fun r : ℂ => θ (y + r • ξ)) (D (y + r • ξ)) r` using `(hθ (y + r • ξ)).hasFDerivAt.comp_hasDerivAt r hl`. Establish `h2 : HasDerivAt (fun r : ℂ => -(r * ψ y + K r)) (-(1 * ψ y + (ψ (r • ξ) - ψ 0))) r` using `(((hasDerivAt_id r).mul_const (ψ y)).add (hK r (Set.mem_univ r))).neg`. Use `(h1.mul h2.cexp).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[hDψ, hdiff]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt) (fun r => (hF r).deriv) t 0`. Simplify using `only [zero_smul, add_zero, zero_mul, zero_add] at hc`. Establish `e : θ (y + t • ξ) = (θ (y + t • ξ) * Complex.exp (-(t * ψ y + K t))) * Complex.exp (t * ψ y + K t)`. Rewrite using `[mul_assoc, ← Complex.exp_add]`.

Simplify using the standard rewrite rules. Rewrite using `[e, hc, mul_assoc, ← Complex.exp_add, mul_comm]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_unit_of_three_term [FiniteDimensional ℂ E] {θ : E → ℂ} (hθ : Differentiable ℂ θ)
    (h0 : θ ≠ 0) (ξ s : E) (γ : ℂ) (m : ℕ)
    (hrel : ∀ a b : E,
      fderiv ℂ θ a ξ * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * (((m : ℂ) + 1) * θ b ^ m * fderiv ℂ θ b ξ) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * θ b ^ (m + 1) * fderiv ℂ θ (s - a - ((m : ℂ) + 1) • b) ξ
      = γ * (θ a * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b))) (t : ℂ) :
    ∃ h : E → ℂ, Differentiable ℂ h ∧ (∀ y, h y ≠ 0) ∧ ∀ y, θ (y + t • ξ) = h y * θ y := by
  set k : ℂ := (m : ℂ) + 1 with hk
  have hk0 : k ≠ 0 := Nat.cast_add_one_ne_zero m
  set D : E → ℂ := fun x => fderiv ℂ θ x ξ with hD
  have hDd : Differentiable ℂ D := by
    rw [← differentiableOn_univ]
    exact GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_univ hθ.differentiableOn ξ
  have hU := dense_ne_zero hθ h0
  have hUo : IsOpen {x | θ x ≠ 0} := isOpen_ne_fun hθ.continuous continuous_const
  obtain ⟨x₀, hx₀⟩ : ∃ x, θ x ≠ 0 := hU.nonempty
  have hU' : ∀ (p : E) (c : ℂ), c ≠ 0 → Dense {x | θ (p - c • x) ≠ 0} := by
    intro p c hc
    refine dense_ne_zero (f := fun x => θ (p - c • x)) (hθ.comp (by fun_prop)) fun h => hx₀ ?_
    have := congrFun h (c⁻¹ • (p - x₀))
    simpa [smul_smul, hc] using this
  obtain ⟨ψ, hψ, hDψ⟩ := exists_entire_quotient (D := D) hU (by
    intro a
    obtain ⟨b, hb1, hb2⟩ := ((hU' (s - a) k hk0).inter_of_isOpen_right hU hUo).nonempty
    simp only [Set.mem_setOf_eq] at hb1 hb2
    refine ⟨fun x => γ - k * D b / θ b - D (s - x - k • b) / θ (s - x - k • b), ?_⟩
    have hc : ContinuousAt (fun x => θ (s - x - k • b)) a :=
      (hθ.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [hc.eventually_ne hb1] with x hx
    refine ⟨?_, ?_⟩
    · have d1 : DifferentiableAt ℂ (fun x => D (s - x - k • b)) x :=
        (hDd.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      have d2 : DifferentiableAt ℂ (fun x => θ (s - x - k • b)) x :=
        (hθ.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      simp only [div_eq_mul_inv]
      exact (differentiableAt_const _).sub (d1.mul (d2.inv hx))
    · have := hrel x b
      have hp : θ b ^ m ≠ 0 := pow_ne_zero _ hb2
      field_simp
      apply mul_left_cancel₀ hp
      simp only [hD]
      linear_combination this)
  have hψc := hψ.continuous
  have hfun : ∀ a b : E, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
    have h1 : ∀ b, θ b ≠ 0 → ∀ a, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
      intro b hb a
      have hd := (hU' (s - k • b) 1 one_ne_zero).inter_of_isOpen_right hU hUo
      refine congrFun (Continuous.ext_on hd
        (f := fun a => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const ?_) a
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_setOf_eq, one_smul] at hx1 hx2
      rw [sub_right_comm] at hx1
      have := hrel x b
      have e1 := hDψ x
      have e2 := hDψ b
      have e3 := hDψ (s - x - k • b)
      simp only [hD] at e1 e2 e3
      rw [e1, e2, e3] at this
      apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hx2 (pow_ne_zero (m + 1) hb)) hx1)
      linear_combination this
    intro a b
    exact congrFun (Continuous.ext_on hU
        (f := fun b => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const fun x hx => h1 x hx a) b
  have hdiff : ∀ y w : E, ψ (y + w) = ψ y + (ψ w - ψ 0) := by
    intro y w
    have e1 := hfun (y + w) (k⁻¹ • (s - y - w))
    have e2 := hfun y (k⁻¹ • (s - y - w))
    rw [smul_inv_smul₀ hk0] at e1 e2
    rw [show s - (y + w) - (s - y - w) = 0 by abel] at e1
    rw [show s - y - (s - y - w) = w by abel] at e2
    linear_combination e1 - e2
  have hκ : Differentiable ℂ (fun r : ℂ => ψ (r • ξ) - ψ 0) := by fun_prop
  obtain ⟨K, hK⟩ := hκ.isExactOn_univ
  refine ⟨fun y => Complex.exp (t * ψ y + (K t - K 0)), by fun_prop,
    fun y => Complex.exp_ne_zero _, fun y => ?_⟩
  have hF : ∀ r : ℂ, HasDerivAt
      (fun r : ℂ => θ (y + r • ξ) * Complex.exp (-(r * ψ y + K r))) 0 r := by
    intro r
    have hl : HasDerivAt (fun r : ℂ => y + r • ξ) ξ r := by
      simpa using ((hasDerivAt_id r).smul_const ξ).const_add y
    have h1 : HasDerivAt (fun r : ℂ => θ (y + r • ξ)) (D (y + r • ξ)) r :=
      (hθ (y + r • ξ)).hasFDerivAt.comp_hasDerivAt r hl
    have h2 : HasDerivAt (fun r : ℂ => -(r * ψ y + K r)) (-(1 * ψ y + (ψ (r • ξ) - ψ 0))) r :=
      (((hasDerivAt_id r).mul_const (ψ y)).add (hK r (Set.mem_univ r))).neg
    refine (h1.mul h2.cexp).congr_deriv ?_
    rw [hDψ, hdiff]
    ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) t 0
  simp only [zero_smul, add_zero, zero_mul, zero_add] at hc
  have e : θ (y + t • ξ) = (θ (y + t • ξ) * Complex.exp (-(t * ψ y + K t)))
      * Complex.exp (t * ψ y + K t) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [e, hc, mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

end General

/- English proof (translation)
Introduce `H1 H2 H3 g τ hτ N hN z ξ γ hf`. Take `⟨m, rfl⟩ : ∃ m, N = m + 3` from `⟨N - 3, by omega⟩`. Take `⟨⟨hθ, hlaw⟩, h0⟩` from `H1 g τ hτ`. Establish `hper` using `H2 g τ hτ`. Establish `hdisc` using `(H3 g τ hτ).1`.

Use `set θ : (Fin g → ℂ) → ℂ := fun z => theta 0 0 z τ with hθdef`. Establish `hmem : ∀ t : ℂ, t • ξ ∈ periodLattice τ`. Introduce `t`. Take `⟨h, h1, h2, h3⟩` from `exists_unit_of_three_term hθ h0 ξ (((m : ℂ) + 3) • z) γ m (by`. Introduce `a b`.

Use `set c := ((m : ℂ) + 3) • z - a - ((m : ℂ) + 1) • b with hc`. Establish `hd : ∀ p : Fin g → ℂ, HasFDerivAt (fun x => θ (x + (p - z))) (fderiv ℂ θ p) z`. Introduce `p`. Use `(hθ p).hasFDerivAt` as an intermediate fact. Rewrite `this` using `[show p = z + (p - z) by abel]`.

Rewrite `this` using `[← hasFDerivAt_comp_add_right]`. Simplify using `using this`. Establish `hdd : ∀ p : Fin g → ℂ, Differentiable ℂ (fun x => θ (x + (p - z)))` using `fun p => hθ.comp (by fun_prop)`. Establish `key` using `hf (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z))) ⟨((hdd a).mul ((hdd b).pow _)).mul (hdd c), ?_⟩`. Establish `hD` using `(((hd a).mul ((hd b).pow (m + 1))).mul (hd c)).fderiv`.

Establish `e : (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z))) = ((fun x => θ (x + (a - z))) * (fun x => θ (x + (b - z)) ^ (m + 1))) * fun x => θ (x + (c - z))` using `rfl`. Rewrite `key` using `[e, hD]`. Simplify using `at key`. Take the linear combination `key`. Introduce `n n' x`.

Establish `e : ∀ p : Fin g → ℂ, x + τ *ᵥ ofIntVec n + ofIntVec n' + p = x + p + τ *ᵥ ofIntVec n + ofIntVec n'` using `fun p => by abel`. Simplify using `only [e]`. Rewrite using `[hlaw n n', hlaw n n', hlaw n n', mul_pow]`. Establish `e2 : eC (-((m + 3 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ x)) = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ (x + (a - z)))) * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ (x + (b - z)))) ^ (m + 1) * eC (-(1 : …`. Unfold `eC`.

Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hc]`. Use `congr 1`. Simplify using `only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Use the proof step `ring) t`. Conclude with `hper _ h h1 h2 h3`. Establish `hcont : Continuous (fun t : ℂ => (⟨t • ξ, hmem t⟩ : periodLattice τ))` using `Continuous.subtype_mk (by fun_prop) _`. Use `PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hcont (x := 1) (y := 0)` as an intermediate fact.

Simplify using `using congrArg Subtype.val this`.
-/
theorem level_three_separates_tangent_vectors :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) := by
  intro H1 H2 H3 g τ hτ N hN z ξ γ hf
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
  obtain ⟨⟨hθ, hlaw⟩, h0⟩ := H1 g τ hτ
  have hper := H2 g τ hτ
  have hdisc := (H3 g τ hτ).1
  set θ : (Fin g → ℂ) → ℂ := fun z => theta 0 0 z τ with hθdef
  have hmem : ∀ t : ℂ, t • ξ ∈ periodLattice τ := by
    intro t
    obtain ⟨h, h1, h2, h3⟩ := exists_unit_of_three_term hθ h0 ξ (((m : ℂ) + 3) • z) γ m (by
      intro a b
      set c := ((m : ℂ) + 3) • z - a - ((m : ℂ) + 1) • b with hc
      have hd : ∀ p : Fin g → ℂ, HasFDerivAt (fun x => θ (x + (p - z))) (fderiv ℂ θ p) z := by
        intro p
        have := (hθ p).hasFDerivAt
        rw [show p = z + (p - z) by abel] at this
        rw [← hasFDerivAt_comp_add_right] at this
        simpa using this
      have hdd : ∀ p : Fin g → ℂ, Differentiable ℂ (fun x => θ (x + (p - z))) := fun p =>
        hθ.comp (by fun_prop)
      have key := hf (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
        ⟨((hdd a).mul ((hdd b).pow _)).mul (hdd c), ?_⟩
      · have hD := (((hd a).mul ((hd b).pow (m + 1))).mul (hd c)).fderiv
        have e : (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
          = ((fun x => θ (x + (a - z))) * (fun x => θ (x + (b - z)) ^ (m + 1)))
            * fun x => θ (x + (c - z)) := rfl
        rw [e, hD] at key
        simp at key
        linear_combination key
      · intro n n' x
        have e : ∀ p : Fin g → ℂ, x + τ *ᵥ ofIntVec n + ofIntVec n' + p
            = x + p + τ *ᵥ ofIntVec n + ofIntVec n' := fun p => by abel
        simp only [e]
        rw [hlaw n n', hlaw n n', hlaw n n', mul_pow]
        have e2 : eC (-((m + 3 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ x))
            = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ (x + (a - z))))
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (b - z)))) ^ (m + 1)
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (c - z)))) := by
          unfold eC
          rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hc]
          congr 1
          simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          push_cast
          ring
        rw [e2]
        ring) t
    exact hper _ h h1 h2 h3
  have hcont : Continuous (fun t : ℂ => (⟨t • ξ, hmem t⟩ : periodLattice τ)) :=
    Continuous.subtype_mk (by fun_prop) _
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hcont (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

end GlobalTheory.ThetaTangent
