import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.CayleyHamiltonId

/- English proof (translation)
Establish `hPa : ∀ i j k l u, P i j (P k l u) = if j = k then P i l u else 0`. Introduce `i j k l u`. Use `LinearMap.congr_fun (hP i j k l) u` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply]`. Apply the tactic sequence `rw [this]; split_ifs <;> rfl`.

Use `set W := LinearMap.range (P i₀ i₀)`. Establish `hW : ∀ k u, P i₀ k u ∈ W` using `fun k u => ⟨P i₀ k u, by rw [hPa, if_pos rfl]⟩`. Establish `hfix : ∀ w ∈ W, P i₀ i₀ w = w`. Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[hPa, if_pos rfl]`.

Set `b` to `Module.finBasis E W`. Set `π : Fin (Module.finrank E W) → U →ₗ[E] (ι → E)` to `fun i => LinearMap.pi fun k => (b.coord i).comp (LinearMap.codRestrict W (P i₀ k) (hW k))`. Set `s : Fin (Module.finrank E W) → (ι → E) →ₗ[E] U` to `fun i => ∑ k, (LinearMap.proj k : (ι → E) →ₗ[E] E).smulRight (P k i₀ (b i))`. Establish `hπ : ∀ i u k, π i u k = b.repr ⟨P i₀ k u, hW k u⟩ i` using `fun i u k => rfl`. Establish `hs : ∀ i v, s i v = ∑ k, v k • P k i₀ (b i)`.

Introduce `i v`. Simplify using `[s, LinearMap.sum_apply]`. Establish `hrec : ∀ k u, ∑ i, b.repr ⟨P i₀ k u, hW k u⟩ i • (b i : U) = P i₀ k u`. Introduce `k u`. Establish `h'` using `congrArg Subtype.val (b.sum_repr ⟨P i₀ k u, hW k u⟩)`.

Rewrite `h'` using `[Submodule.coe_sum]`. Simplify `h'` using `only [Submodule.coe_smul]`. Use `⟨Module.finrank E W, π, s, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i M`. Use extensionality with `u k`.

Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, hπ]`. Establish `e : (⟨P i₀ k ((∑ a, ∑ b', M a b' • P a b') u), hW k _⟩ : W) = ∑ b', M k b' • (⟨P i₀ b' u, hW b' u⟩ : W)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[LinearMap.sum_apply, map_sum, map_smul, hPa]`. Rewrite using `[e, map_sum, Finsupp.finset_sum_apply]`.

Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hπ]`. Introduce `i M`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, hs]`. Simplify using `[LinearMap.sum_apply, map_sum, map_smul, hPa, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]`.

Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]`. Introduce `i j`. Use `LinearMap.ext fun v => funext fun k => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, hπ, hs]`. Establish `e : (⟨P i₀ k (∑ l, v l • P l i₀ (b j)), hW k _⟩ : W) = v k • b j`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[map_sum, map_smul, hPa, hfix _ (b j).2]`. Rewrite using `[e]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, Ne.symm h]`. Use extensionality with `u`.

Simplify using `only [LinearMap.sum_apply, LinearMap.comp_apply, hs, hπ, LinearMap.id_apply]`. Rewrite using `[Finset.sum_comm]`. Establish `hk : ∀ k, ∑ x, b.repr ⟨P i₀ k u, hW k u⟩ x • P k i₀ (b x) = P k k u`. Introduce `k`. Use `congrArg (P k i₀) (hrec k u)` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul] at this`. Rewrite using `[this, hPa, if_pos rfl]`. Simplify using `only [hk]`. Rewrite using `[← LinearMap.sum_apply, h1, Module.End.one_apply]`.
-/
theorem exists_decomp {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (P : ι → ι → Module.End E U)
    (hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0)
    (h1 : ∑ i, P i i = 1) :
    ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (ι → E)) (s : Fin m → (ι → E) →ₗ[E] U),
      (∀ i (M : Matrix ι ι E), π i ∘ₗ (∑ a, ∑ b, M a b • P a b) = Matrix.toLin' M ∘ₗ π i) ∧
      (∀ i (M : Matrix ι ι E), (∑ a, ∑ b, M a b • P a b) ∘ₗ s i = s i ∘ₗ Matrix.toLin' M) ∧
      (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧
      ∑ i, s i ∘ₗ π i = LinearMap.id := by
  classical
  have hPa : ∀ i j k l u, P i j (P k l u) = if j = k then P i l u else 0 := by
    intro i j k l u
    have := LinearMap.congr_fun (hP i j k l) u
    rw [Module.End.mul_apply] at this
    rw [this]; split_ifs <;> rfl
  set W := LinearMap.range (P i₀ i₀)
  have hW : ∀ k u, P i₀ k u ∈ W := fun k u => ⟨P i₀ k u, by rw [hPa, if_pos rfl]⟩
  have hfix : ∀ w ∈ W, P i₀ i₀ w = w := by
    rintro _ ⟨u, rfl⟩; rw [hPa, if_pos rfl]
  let b := Module.finBasis E W
  let π : Fin (Module.finrank E W) → U →ₗ[E] (ι → E) :=
    fun i => LinearMap.pi fun k => (b.coord i).comp (LinearMap.codRestrict W (P i₀ k) (hW k))
  let s : Fin (Module.finrank E W) → (ι → E) →ₗ[E] U :=
    fun i => ∑ k, (LinearMap.proj k : (ι → E) →ₗ[E] E).smulRight (P k i₀ (b i))
  have hπ : ∀ i u k, π i u k = b.repr ⟨P i₀ k u, hW k u⟩ i := fun i u k => rfl
  have hs : ∀ i v, s i v = ∑ k, v k • P k i₀ (b i) := by
    intro i v; simp [s, LinearMap.sum_apply]
  have hrec : ∀ k u, ∑ i, b.repr ⟨P i₀ k u, hW k u⟩ i • (b i : U) = P i₀ k u := by
    intro k u
    have h' := congrArg Subtype.val (b.sum_repr ⟨P i₀ k u, hW k u⟩)
    rw [Submodule.coe_sum] at h'
    simpa only [Submodule.coe_smul] using h'
  refine ⟨Module.finrank E W, π, s, ?_, ?_, ?_, ?_⟩
  · intro i M
    ext u k
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hπ]
    have e : (⟨P i₀ k ((∑ a, ∑ b', M a b' • P a b') u), hW k _⟩ : W)
        = ∑ b', M k b' • (⟨P i₀ b' u, hW b' u⟩ : W) := by
      apply Subtype.ext
      simp [LinearMap.sum_apply, map_sum, map_smul, hPa]
    rw [e, map_sum, Finsupp.finset_sum_apply]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hπ]
  · intro i M
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hs]
    simp [LinearMap.sum_apply, map_sum, map_smul, hPa, Matrix.mulVec, dotProduct, Finset.sum_smul,
      mul_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  · intro i j
    refine LinearMap.ext fun v => funext fun k => ?_
    simp only [LinearMap.comp_apply, hπ, hs]
    have e : (⟨P i₀ k (∑ l, v l • P l i₀ (b j)), hW k _⟩ : W) = v k • b j := by
      apply Subtype.ext
      simp [map_sum, map_smul, hPa, hfix _ (b j).2]
    rw [e]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  · ext u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hs, hπ, LinearMap.id_apply]
    rw [Finset.sum_comm]
    have hk : ∀ k, ∑ x, b.repr ⟨P i₀ k u, hW k u⟩ x • P k i₀ (b x) = P k k u := by
      intro k
      have := congrArg (P k i₀) (hrec k u)
      rw [map_sum] at this
      simp only [map_smul] at this
      rw [this, hPa, if_pos rfl]
    simp only [hk]
    rw [← LinearMap.sum_apply, h1, Module.End.one_apply]

/- English proof (translation)
Introduce `E _ _ h2 G _ ρ hirr U _ _ _ σ hrel`. Set `R : G →* Matrix (Fin 2) (Fin 2) E` to `(Units.coeHom _).comp ρ`. Establish `hRg : ∀ g, R g = (ρ g : Matrix (Fin 2) (Fin 2) E)` using `fun g => rfl`. Establish `hspan` using `GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R (fun W hW => hirr W hW)`. Set `Φ : MonoidAlgebra E G →ₐ[E] Module.End E U` to `MonoidAlgebra.lift E (Module.End E U) G σ`.

Set `Ψ : MonoidAlgebra E G →ₐ[E] Matrix (Fin 2) (Fin 2) E` to `MonoidAlgebra.lift E (Matrix (Fin 2) (Fin 2) E) G R`. Establish `hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = c • σ g` using `fun g c => MonoidAlgebra.lift_single _ _ _`. Establish `hΨ : ∀ g c, Ψ (MonoidAlgebra.single g c) = c • R g` using `fun g c => MonoidAlgebra.lift_single _ _ _`. Establish `hsurj : ∀ M, ∃ y, Ψ y = M`. Introduce `M`.

Establish `hle : Submodule.span E (Set.range R) ≤ LinearMap.range Ψ.toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨MonoidAlgebra.single g 1, by simp [hΨ]⟩`. Take `⟨y, hy⟩` from `hle (hspan ▸ Submodule.mem_top : M ∈ Submodule.span E (Set.range R))`.

Conclude with `⟨y, hy⟩`. Establish `hinv : ∀ g, (R g).det • σ g⁻¹ = (R g).trace • 1 - σ g`. Introduce `g`. Establish `h` using `congrArg (· * σ g⁻¹) (hrel g)`. Establish `hgg : σ g * σ g⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`.

Simplify using `only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, hgg, mul_one, one_mul, zero_mul] at h`. Rewrite using `[hRg]`. Take the linear combination `(norm := module) h`. Establish `hpair : ∀ g h, σ g * σ h + σ h * σ g - (R h).trace • σ g - (R g).trace • σ h + ((R g).trace * (R h).trace - (R g * R h).trace) • (1 : Module.End E U) = 0`. Introduce `g h`.

Establish `e1` using `hinv (g * h)`. Establish `e2 : (R (g*h)).det • σ (g*h)⁻¹ = ((R h).det • σ h⁻¹) * ((R g).det • σ g⁻¹)`. Rewrite using `[_root_.mul_inv_rev, map_mul σ, map_mul R, det_mul, smul_mul_smul_comm, mul_comm (R g).det]`. Rewrite `e1` using `[e2, hinv g, hinv h, map_mul σ, map_mul R]`. Simplify using `only [mul_sub, sub_mul, smul_mul_smul_comm, one_mul, mul_one, smul_mul_assoc, mul_smul_comm] at e1`.

Take the linear combination `(norm := module) e1`. Establish `hB : ∀ x y, Φ x * Φ y + Φ y * Φ x - (Ψ y).trace • Φ x - (Ψ x).trace • Φ y + ((Ψ x).trace * (Ψ y).trace - (Ψ x * Ψ y).trace) • (1 : Module.End E U) = 0`. Introduce `x y`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x₁ x₂ h₁ h₂`. Simplify using `only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢`. Take the linear combination `(norm := module) h₁ + h₂`. Consider the case `single g c`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂`. Simplify using `only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢`. Take the linear combination `(norm := module) h₁ + h₂`. Consider the case `single h d`.

Simplify using `only [hΦ, hΨ, trace_smul, smul_mul_smul_comm, smul_eq_mul]`. Take the linear combination `(norm := module) (c * d) • hpair g h`. Establish `hanti : ∀ x y, Ψ x = 0 → Φ x * Φ y + Φ y * Φ x = (Ψ y).trace • Φ x`. Introduce `x y hx`. Use `hB x y` as an intermediate fact.

Simplify using `only [hx, trace_zero, zero_mul, mul_zero, sub_self, zero_smul, add_zero, sub_zero] at this`. Take the linear combination `(norm := module) this`. Establish `h2c : ∀ X : Module.End E U, X + X = 0 → X = 0`. Introduce `X hX`. Rewrite `hX` using `[← two_smul E X]`.

Conclude with `(smul_eq_zero.mp hX).resolve_left h2`. Take `⟨y₁, hy₁⟩` from `hsurj (Matrix.single 0 1 1)`. Take `⟨y₂, hy₂⟩` from `hsurj (Matrix.single 1 0 1)`. Establish `hc : Ψ (y₁ * y₂ - y₂ * y₁) = !![1, 0; 0, -1]`. Rewrite using `[map_sub, map_mul, map_mul, hy₁, hy₂]`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]`. Establish `hc2 : Ψ ((y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1) = 0`. Rewrite using `[map_sub, map_mul, hc, map_one]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`. Establish `ht1 : (Ψ y₁).trace = 0` using `by rw [hy₁]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]`.

Establish `ht2 : (Ψ y₂).trace = 0` using `by rw [hy₂]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]`. Establish `htc : (Ψ (y₁ * y₂ - y₂ * y₁)).trace = 0` using `by rw [hc]; simp [Matrix.trace, Fin.sum_univ_two]`. Establish `hJ : ∀ x, Ψ x = 0 → Φ x = 0`. Introduce `x hx`. Use `set N := Φ x`.

Use `set a := Φ y₁`. Use `set b := Φ y₂`. Establish `e1 : N * a = -(a * N)` using `eq_neg_of_add_eq_zero_left (by rw [hanti x y₁ hx, ht1, zero_smul])`. Establish `e2 : N * b = -(b * N)` using `eq_neg_of_add_eq_zero_left (by rw [hanti x y₂ hx, ht2, zero_smul])`. Establish `k1 : N * (a * b) = a * b * N`.

Rewrite using `[← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]`. Establish `k2 : N * (b * a) = b * a * N`. Rewrite using `[← mul_assoc, e2, neg_mul, mul_assoc, e1, mul_neg, neg_neg, mul_assoc]`. Establish `hC : Φ (y₁ * y₂ - y₂ * y₁) = a * b - b * a` using `by rw [map_sub, map_mul, map_mul]`. Establish `hNC : N * (a * b - b * a) = 0`.

Establish `h3` using `hanti x (y₁ * y₂ - y₂ * y₁) hx`. Rewrite `h3` using `[htc, zero_smul, hC]`. Apply `h2c` to reduce the goal to its premises. Establish `: (a * b - b * a) * N = N * (a * b - b * a)` using `by rw [mul_sub, sub_mul, k1, k2]`. Rewrite `h3` using `[this]`.

Conclude with `h3`. Use `set x' := (y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1`. Establish `hN' : Φ x' * Φ x' = 0`. Apply `h2c` to reduce the goal to its premises. Rewrite using `[hanti x' x' hc2, hc2, trace_zero, zero_smul]`.

Establish `hNN' : N * Φ x' = -N`. Establish `hx' : Φ x' = (a * b - b * a) * (a * b - b * a) - 1`. Simplify using `only [x']`. Rewrite using `[map_sub, map_mul, hC, map_one]`. Rewrite using `[hx', mul_sub, mul_one, ← mul_assoc, hNC, zero_mul, zero_sub]`.

Establish `h5 : N * Φ x' * Φ x' = 0` using `by rw [mul_assoc, hN', mul_zero]`. Rewrite `h5` using `[hNN', neg_mul, hNN', neg_neg]`. Conclude with `h5`. Establish `hΦeq : ∀ x y, Ψ x = Ψ y → Φ x = Φ y`. Introduce `x y h`.

Use `hJ (x - y) (by rw [map_sub, h, sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Use `choose yP hyP using fun i j : Fin 2 => hsurj (Matrix.single i j 1)`. Set `P : Fin 2 → Fin 2 → Module.End E U` to `fun i j => Φ (yP i j)`. Establish `hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0`.

Introduce `i j k l`. Simplify using `only [P, ← map_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality. Apply `hΦeq` to reduce the goal to its premises.

Rewrite using `[map_mul, hyP, hyP, hyP, Matrix.single_mul_single_same, mul_one]`. Rewrite using `[← map_zero Φ]`. Apply `hΦeq` to reduce the goal to its premises. Rewrite using `[map_mul, hyP, hyP, map_zero]`. Simplify using `[h]`.

Establish `hsum : ∑ i, P i i = 1`. Simplify using `only [P]`. Rewrite using `[← map_sum, ← map_one Φ]`. Apply `hΦeq` to reduce the goal to its premises. Rewrite using `[map_sum, map_one]`.

Simplify using `only [hyP]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]`. Establish `hσ : ∀ g, σ g = ∑ a, ∑ b, (R g) a b • P a b`. Introduce `g`. Establish `e : σ g = Φ (MonoidAlgebra.single g 1)` using `by rw [hΦ, one_smul]`.

Rewrite using `[e]`. Simplify using `only [P, ← map_smul, ← map_sum]`. Apply `hΦeq` to reduce the goal to its premises. Simplify using `only [map_sum, map_smul, hΨ, hyP, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Conclude with `Matrix.matrix_eq_sum_single (R g)`.

Take `⟨m, π, s, k1, k2, k3, k4⟩` from `exists_decomp (0 : Fin 2) P hP hsum`. Use `⟨m, π, s, fun i g => ?_, fun i g => ?_, k3, k4⟩` and prove the remaining obligations. Rewrite using `[hσ g]`. Conclude with `k1 i (R g)`. Rewrite using `[hσ g]`.

Conclude with `k2 i (R g)`.
-/
theorem isotypic_of_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  intro E _ _ h2 G _ ρ hirr U _ _ _ σ hrel
  classical
  let R : G →* Matrix (Fin 2) (Fin 2) E := (Units.coeHom _).comp ρ
  have hRg : ∀ g, R g = (ρ g : Matrix (Fin 2) (Fin 2) E) := fun g => rfl
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R (fun W hW => hirr W hW)
  let Φ : MonoidAlgebra E G →ₐ[E] Module.End E U := MonoidAlgebra.lift E (Module.End E U) G σ
  let Ψ : MonoidAlgebra E G →ₐ[E] Matrix (Fin 2) (Fin 2) E :=
    MonoidAlgebra.lift E (Matrix (Fin 2) (Fin 2) E) G R
  have hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = c • σ g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hΨ : ∀ g c, Ψ (MonoidAlgebra.single g c) = c • R g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hsurj : ∀ M, ∃ y, Ψ y = M := by
    intro M
    have hle : Submodule.span E (Set.range R) ≤ LinearMap.range Ψ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [hΨ]⟩
    obtain ⟨y, hy⟩ := hle (hspan ▸ Submodule.mem_top : M ∈ Submodule.span E (Set.range R))
    exact ⟨y, hy⟩

  have hinv : ∀ g, (R g).det • σ g⁻¹ = (R g).trace • 1 - σ g := by
    intro g
    have h := congrArg (· * σ g⁻¹) (hrel g)
    have hgg : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, hgg, mul_one, one_mul, zero_mul] at h
    rw [hRg]
    linear_combination (norm := module) h
  have hpair : ∀ g h, σ g * σ h + σ h * σ g - (R h).trace • σ g - (R g).trace • σ h
      + ((R g).trace * (R h).trace - (R g * R h).trace) • (1 : Module.End E U) = 0 := by
    intro g h
    have e1 := hinv (g * h)
    have e2 : (R (g*h)).det • σ (g*h)⁻¹ = ((R h).det • σ h⁻¹) * ((R g).det • σ g⁻¹) := by
      rw [_root_.mul_inv_rev, map_mul σ, map_mul R, det_mul, smul_mul_smul_comm, mul_comm (R g).det]
    rw [e2, hinv g, hinv h, map_mul σ, map_mul R] at e1
    simp only [mul_sub, sub_mul, smul_mul_smul_comm, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm] at e1
    linear_combination (norm := module) e1
  have hB : ∀ x y, Φ x * Φ y + Φ y * Φ x - (Ψ y).trace • Φ x - (Ψ x).trace • Φ y
      + ((Ψ x).trace * (Ψ y).trace - (Ψ x * Ψ y).trace) • (1 : Module.End E U) = 0 := by
    intro x y
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
      linear_combination (norm := module) h₁ + h₂
    | single g c =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
        linear_combination (norm := module) h₁ + h₂
      | single h d =>
        simp only [hΦ, hΨ, trace_smul, smul_mul_smul_comm, smul_eq_mul]
        linear_combination (norm := module) (c * d) • hpair g h

  have hanti : ∀ x y, Ψ x = 0 → Φ x * Φ y + Φ y * Φ x = (Ψ y).trace • Φ x := by
    intro x y hx
    have := hB x y
    simp only [hx, trace_zero, zero_mul, mul_zero, sub_self, zero_smul, add_zero, sub_zero] at this
    linear_combination (norm := module) this
  have h2c : ∀ X : Module.End E U, X + X = 0 → X = 0 := by
    intro X hX
    rw [← two_smul E X] at hX
    exact (smul_eq_zero.mp hX).resolve_left h2
  obtain ⟨y₁, hy₁⟩ := hsurj (Matrix.single 0 1 1)
  obtain ⟨y₂, hy₂⟩ := hsurj (Matrix.single 1 0 1)
  have hc : Ψ (y₁ * y₂ - y₂ * y₁) = !![1, 0; 0, -1] := by
    rw [map_sub, map_mul, map_mul, hy₁, hy₂]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hc2 : Ψ ((y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1) = 0 := by
    rw [map_sub, map_mul, hc, map_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ht1 : (Ψ y₁).trace = 0 := by rw [hy₁]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have ht2 : (Ψ y₂).trace = 0 := by rw [hy₂]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have htc : (Ψ (y₁ * y₂ - y₂ * y₁)).trace = 0 := by rw [hc]; simp [Matrix.trace, Fin.sum_univ_two]
  have hJ : ∀ x, Ψ x = 0 → Φ x = 0 := by
    intro x hx
    set N := Φ x
    set a := Φ y₁
    set b := Φ y₂
    have e1 : N * a = -(a * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₁ hx, ht1, zero_smul])
    have e2 : N * b = -(b * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₂ hx, ht2, zero_smul])
    have k1 : N * (a * b) = a * b * N := by
      rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]
    have k2 : N * (b * a) = b * a * N := by
      rw [← mul_assoc, e2, neg_mul, mul_assoc, e1, mul_neg, neg_neg, mul_assoc]
    have hC : Φ (y₁ * y₂ - y₂ * y₁) = a * b - b * a := by rw [map_sub, map_mul, map_mul]
    have hNC : N * (a * b - b * a) = 0 := by
      have h3 := hanti x (y₁ * y₂ - y₂ * y₁) hx
      rw [htc, zero_smul, hC] at h3
      apply h2c
      have : (a * b - b * a) * N = N * (a * b - b * a) := by rw [mul_sub, sub_mul, k1, k2]
      rw [this] at h3; exact h3
    set x' := (y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1
    have hN' : Φ x' * Φ x' = 0 := by
      apply h2c
      rw [hanti x' x' hc2, hc2, trace_zero, zero_smul]
    have hNN' : N * Φ x' = -N := by
      have hx' : Φ x' = (a * b - b * a) * (a * b - b * a) - 1 := by
        simp only [x']; rw [map_sub, map_mul, hC, map_one]
      rw [hx', mul_sub, mul_one, ← mul_assoc, hNC, zero_mul, zero_sub]
    have h5 : N * Φ x' * Φ x' = 0 := by rw [mul_assoc, hN', mul_zero]
    rw [hNN', neg_mul, hNN', neg_neg] at h5
    exact h5

  have hΦeq : ∀ x y, Ψ x = Ψ y → Φ x = Φ y := by
    intro x y h
    have := hJ (x - y) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  choose yP hyP using fun i j : Fin 2 => hsurj (Matrix.single i j 1)
  let P : Fin 2 → Fin 2 → Module.End E U := fun i j => Φ (yP i j)
  have hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0 := by
    intro i j k l
    simp only [P, ← map_mul]
    split_ifs with h
    · subst h
      apply hΦeq
      rw [map_mul, hyP, hyP, hyP, Matrix.single_mul_single_same, mul_one]
    · rw [← map_zero Φ]
      apply hΦeq
      rw [map_mul, hyP, hyP, map_zero]
      simp [h]
  have hsum : ∑ i, P i i = 1 := by
    simp only [P]
    rw [← map_sum, ← map_one Φ]
    apply hΦeq
    rw [map_sum, map_one]
    simp only [hyP]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]
  have hσ : ∀ g, σ g = ∑ a, ∑ b, (R g) a b • P a b := by
    intro g
    have e : σ g = Φ (MonoidAlgebra.single g 1) := by rw [hΦ, one_smul]
    rw [e]
    simp only [P, ← map_smul, ← map_sum]
    apply hΦeq
    simp only [map_sum, map_smul, hΨ, hyP, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single (R g)
  obtain ⟨m, π, s, k1, k2, k3, k4⟩ := exists_decomp (0 : Fin 2) P hP hsum
  refine ⟨m, π, s, fun i g => ?_, fun i g => ?_, k3, k4⟩
  · rw [hσ g]; exact k1 i (R g)
  · rw [hσ g]; exact k2 i (R g)

end GlobalTheory.CayleyHamiltonId
