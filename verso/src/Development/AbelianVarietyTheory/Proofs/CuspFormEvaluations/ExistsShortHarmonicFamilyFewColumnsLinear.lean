import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {Λ : Submodule (𝓞 E) (Fin n → E)}

/- English proof (translation)
Use `set M := ReciprocityTheory.ChartRestriction.G.TB.hMat h e e' with hMdef`. Establish `hM : ∀ a', M a' c = h (e' a') (e c)` using `fun _ => rfl`. Establish `hadj : ∀ a, ∑ a', M.adjugate a a' * M a' c = if a = c then M.det else 0`. Introduce `a`. Use `congrFun (congrFun (Matrix.adjugate_mul M) a) c` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Establish `hrow : ∀ a, ∑ a', M.adjugate a a' * h g (e a) * h (e' a') (e c) = h g (e a) * if a = c then M.det else 0`. Introduce `a`. Rewrite using `[← hadj a, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [perpVec, ← hMdef, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hrow, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem perpVec_apply_eq_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {m : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin m → V) (g : V) (c : Fin m) :
    h (perpVec h e e' g) (e c) = 0 := by
  set M := ReciprocityTheory.ChartRestriction.G.TB.hMat h e e' with hMdef
  have hM : ∀ a', M a' c = h (e' a') (e c) := fun _ => rfl
  have hadj : ∀ a, ∑ a', M.adjugate a a' * M a' c = if a = c then M.det else 0 := by
    intro a
    have := congrFun (congrFun (Matrix.adjugate_mul M) a) c
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hrow : ∀ a, ∑ a', M.adjugate a a' * h g (e a) * h (e' a') (e c) =
      h g (e a) * if a = c then M.det else 0 := by
    intro a
    rw [← hadj a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [hM]
    ring
  simp only [perpVec, ← hMdef, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, hrow, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

/- English proof (translation)
Take `⟨v, hvΛ, -, hvspan, hvlen⟩` from `GlobalTheory.exists_short_vectors Λ hfg hint hdual`. Establish `hN1 : 1 ≤ p + q` using `one_le_add_of_one_le_typeDegree ha`. Establish `hn1 : 1 ≤ n` using `hN1.trans hn`. Establish `hf1 : 1 ≤ fdeg E` using `one_le_fdeg`. Establish `hrd : 1 ≤ rdE E` using `one_le_rdE`.

Take `⟨dg, hdg⟩ : ∃ dg, dg = (2 * (p + q) + 1) * typeDegree c c'` from `⟨_, rfl⟩`. Establish `hdg1 : 1 ≤ dg` using `by rw [hdg]; exact Nat.mul_pos (Nat.succ_pos _) ha`. Take `⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E` from `⟨_, rfl⟩`. Establish `hρ1 : 1 ≤ ρ`. Establish `h1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ ((3 : ℝ) / 2)` using `Real.one_le_rpow (by exact_mod_cast hf1) (by norm_num)`.

Establish `h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2` using `one_le_pow₀ (by exact_mod_cast hn1)`. Establish `h3 : (1 : ℝ) ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2)` using `by linarith`. Rewrite using `[hρ]`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) hrd`. Take `⟨R, hR⟩ : ∃ R : ℝ, R = ((2 * fdeg E * n : ℕ) : ℝ) * (dg : ℝ) * ρ` from `⟨_, rfl⟩`.

Establish `hR1 : 1 ≤ R`. Establish `h1 : (1 : ℝ) ≤ ((2 * fdeg E * n : ℕ) : ℝ)`. Conclude with `Nat.mul_pos (Nat.mul_pos two_pos hf1) hn1` after adjusting the coercions. Establish `h2 : (1 : ℝ) ≤ (dg : ℝ)` using `by exact_mod_cast hdg1`. Rewrite using `[hR]`.

Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hρ1`. Set `h` to `hermPairing E n`. Establish `hpair : ∀ x y, h x y = herm 1 x y` using `fun _ _ => rfl`. Establish `hh : ∀ x y, h x y = ∑ k, x k * cc (y k)` using `fun x y => (hpair x y).trans (herm_one_eq_sum x y)`. Establish `hcomb : ∀ A : Fin (2 * fdeg E * n) → ℕ, ∑ i, (A i : E) • v i ∈ Λ` using `fun A => Λ.sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hvΛ i) _`.

Establish `hlen : ∀ (σ : E →+* ℂ) (A : Fin (2 * fdeg E * n) → ℕ), (∀ i, A i ≤ dg) → ∑ k, ‖σ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ R ^ 2`. Introduce `σ A hA`. Use `sum_sq_combination_le σ v (ρ := ρ) (fun i => by rw [hρ]; exact hvlen i σ) A hA` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Rewrite using `[hR]`.

Conclude with `this`. Set `comb : (Fin (2 * fdeg E * n) → ℕ) → Fin n → E` to `fun A => ∑ i, (A i : E) • v i`. Set `F : (Fin p → Fin (2 * fdeg E * n) → ℕ) × (Fin p → Fin (2 * fdeg E * n) → ℕ) × (Fin q → Fin (2 * fdeg E * n) → ℕ) → (Fin p → Fin n → E) × (Fin q → Fin n → E)` to `fun x => (fun a => comb (x.1 a), fun b => perpVec h (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a)) (comb (x.2.2 b)))`. Set `G` to `(Fintype.piFinset fun _ : Fin p => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) => Finset.range (dg + 1)) ×ˢ (Fintype.piFinset fun _ : Fin p => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) => Finset.range (dg + 1)) ×ˢ (Fintype.piFinset fun _ : Fin q => Fintype.piFinset fun _ : …`. Establish `hG : ∀ x ∈ G, (∀ a i, x.1 a i ≤ dg) ∧ (∀ a i, x.2.1 a i ≤ dg) ∧ (∀ b i, x.2.2 b i ≤ dg)`.

Introduce `x hx`. Simplify using `only [G, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hx`. Conclude with `⟨fun a i => Nat.lt_succ_iff.mp (hx.1 a i), fun a i => Nat.lt_succ_iff.mp (hx.2.1 a i), fun b i => Nat.lt_succ_iff.mp (hx.2.2 b i)⟩`. Use `⟨G.image F, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Take `⟨x, -, rfl⟩` from `Finset.mem_image.mp hs`. Use `⟨fun a => hcomb _, fun b => perpVec_hermPairing_mem hint (fun a => hcomb _) (fun a => hcomb _) (hcomb _), fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hpair]`. Conclude with `perpVec_apply_eq_zero h _ _ _ a`. Introduce `K _ _ τ hτ`.

Rewrite using `[(rowHighest_orbitSpan_main hn c c' K).2.1, ← span_grid_perpVec_eq_orbitSpan τ hτ hn h hh v hvspan c c' (le_of_eq hdg.symm)]`. Use `congr 1`. Rewrite using `[Finset.coe_image, ← Set.image_comp]`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨h1, h2, h3⟩` from `hG x hx`. Conclude with `⟨x.1, x.2.1, x.2.2, h1, h2, h3, rfl⟩`. Introduce and unpack `⟨A, A', B, h1, h2, h3, rfl⟩`. Use `⟨(A, A', B), ?_, rfl⟩` and prove the remaining obligations.

Simplify using `only [G, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]`. Conclude with `⟨fun a i => Nat.lt_succ_of_le (h1 a i), fun a i => Nat.lt_succ_of_le (h2 a i), fun b i => Nat.lt_succ_of_le (h3 b i)⟩`. Introduce `τ s hs`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hs`. Take `⟨hA, hA', hB⟩` from `hG x hx`.

Establish `hR0 : 0 ≤ R` using `by linarith`. Establish `hRR : R ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1)`. Establish `h1 : (1 : ℝ) ≤ ((p + q + 1).factorial : ℝ)`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)` after adjusting the coercions. Establish `h2 : R ≤ R ^ (2 * (p + q) + 1)`.

Simplify using `using pow_le_pow_right₀ hR1 (Nat.le_add_left 1 (2 * (p + q)))`. Combine the equalities or inequalities in the displayed calculation. Establish `hR'0 : 0 ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1)` using `by linarith`. Use `(l1Norm_rowBlockLeadingMinorProduct_le c c' _ _ hR'0 ?_ ?_ (Nat.le_add_right p q) (Nat.le_add_left q p)).trans (le_of_eq ?_)` and prove the remaining obligations. Introduce `t a`.

Use `hlen ((τ t).comp (IsCMField.complexConj E : E →+* E)) (x.1 a) (hA a)` as an intermediate fact. Conclude with `this.trans (pow_le_pow_left₀ hR0 hRR 2)`. Introduce `t b`. Use `sum_sq_perpVec_le (τ t) h hh (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a)) (comb (x.2.2 b)) (R := R) (fun a => hlen _ _ (hA a)) (fun a => hlen _ _ (hA' a)) (hlen _ _ (hB b))` as an intermediate fact. Use `this.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg hR0 _)) ?_ 2)` and prove the remaining obligations.

Establish `h1 : ((p + 1).factorial : ℝ) ≤ ((p + q + 1).factorial : ℝ)`. Conclude with `Nat.factorial_le (by omega)` after adjusting the coercions. Establish `h2 : R ^ (2 * p + 1) ≤ R ^ (2 * (p + q) + 1)` using `pow_le_pow_right₀ hR1 (by omega)`. Conclude with `mul_le_mul h1 h2 (pow_nonneg hR0 _) (by positivity)`. Substitute `hR hρ hdg` using the available equality.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.card_image_le.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [G, Finset.card_product, Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_short_harmonic_family_few_columns (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    {p q : ℕ} (hn : p + q ≤ n) {T : Type*} [Fintype T] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
    ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
      (∀ s ∈ S, (∀ a, s.1 a ∈ Λ) ∧ (∀ b, s.2 b ∈ Λ) ∧ ∀ a b, herm 1 (s.2 b) (s.1 a) = 0) ∧
      (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
        (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) →
        Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
          minorProd c c' (fun t a k => τ t (cc (s.1 a k))) fun t b k => τ t (s.2 b k)) '' S) =
          rowHighest K c c') ∧
      (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
        l1Norm (minorProd c c' (fun t a k => τ t (cc (s.1 a k))) fun t b k => τ t (s.2 b k)) ≤
          (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) *
            ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
            (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^
            typeDegree c c') ∧
      S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  classical
  obtain ⟨v, hvΛ, -, hvspan, hvlen⟩ := GlobalTheory.exists_short_vectors Λ hfg hint hdual
  have hN1 : 1 ≤ p + q := one_le_add_of_one_le_typeDegree ha
  have hn1 : 1 ≤ n := hN1.trans hn
  have hf1 : 1 ≤ fdeg E := one_le_fdeg
  have hrd : 1 ≤ rdE E := one_le_rdE
  obtain ⟨dg, hdg⟩ : ∃ dg, dg = (2 * (p + q) + 1) * typeDegree c c' := ⟨_, rfl⟩
  have hdg1 : 1 ≤ dg := by rw [hdg]; exact Nat.mul_pos (Nat.succ_pos _) ha
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := by
    have h1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast hf1) (by norm_num)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn1)
    have h3 : (1 : ℝ) ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) := by linarith
    rw [hρ]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) hrd
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((2 * fdeg E * n : ℕ) : ℝ) * (dg : ℝ) * ρ := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ ((2 * fdeg E * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos two_pos hf1) hn1
    have h2 : (1 : ℝ) ≤ (dg : ℝ) := by exact_mod_cast hdg1
    rw [hR]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hρ1
  let h := hermPairing E n
  have hpair : ∀ x y, h x y = herm 1 x y := fun _ _ => rfl
  have hh : ∀ x y, h x y = ∑ k, x k * cc (y k) := fun x y => (hpair x y).trans (herm_one_eq_sum x y)
  have hcomb : ∀ A : Fin (2 * fdeg E * n) → ℕ, ∑ i, (A i : E) • v i ∈ Λ := fun A =>
    Λ.sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hvΛ i) _
  have hlen : ∀ (σ : E →+* ℂ) (A : Fin (2 * fdeg E * n) → ℕ), (∀ i, A i ≤ dg) →
      ∑ k, ‖σ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ R ^ 2 := by
    intro σ A hA
    have := sum_sq_combination_le σ v (ρ := ρ) (fun i => by rw [hρ]; exact hvlen i σ) A hA
    rw [Fintype.card_fin] at this
    rw [hR]
    exact this
  let comb : (Fin (2 * fdeg E * n) → ℕ) → Fin n → E := fun A => ∑ i, (A i : E) • v i
  let F : (Fin p → Fin (2 * fdeg E * n) → ℕ) × (Fin p → Fin (2 * fdeg E * n) → ℕ) ×
      (Fin q → Fin (2 * fdeg E * n) → ℕ) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
    fun x => (fun a => comb (x.1 a),
      fun b => perpVec h (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a)) (comb (x.2.2 b)))
  let G := (Fintype.piFinset fun _ : Fin p => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) =>
      Finset.range (dg + 1)) ×ˢ (Fintype.piFinset fun _ : Fin p =>
      Fintype.piFinset fun _ : Fin (2 * fdeg E * n) => Finset.range (dg + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin q => Fintype.piFinset fun _ : Fin (2 * fdeg E * n) =>
      Finset.range (dg + 1))
  have hG : ∀ x ∈ G, (∀ a i, x.1 a i ≤ dg) ∧ (∀ a i, x.2.1 a i ≤ dg) ∧ (∀ b i, x.2.2 b i ≤ dg) := by
    intro x hx
    simp only [G, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hx
    exact ⟨fun a i => Nat.lt_succ_iff.mp (hx.1 a i), fun a i => Nat.lt_succ_iff.mp (hx.2.1 a i),
      fun b i => Nat.lt_succ_iff.mp (hx.2.2 b i)⟩
  refine ⟨G.image F, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨fun a => hcomb _, fun b => perpVec_hermPairing_mem hint (fun a => hcomb _)
      (fun a => hcomb _) (hcomb _), fun a b => ?_⟩
    rw [← hpair]
    exact perpVec_apply_eq_zero h _ _ _ a
  · intro K _ _ τ hτ
    rw [(rowHighest_orbitSpan_main hn c c' K).2.1,
      ← span_grid_perpVec_eq_orbitSpan τ hτ hn h hh v hvspan c c' (le_of_eq hdg.symm)]
    congr 1
    rw [Finset.coe_image, ← Set.image_comp]
    ext P
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hG x hx
      exact ⟨x.1, x.2.1, x.2.2, h1, h2, h3, rfl⟩
    · rintro ⟨A, A', B, h1, h2, h3, rfl⟩
      refine ⟨(A, A', B), ?_, rfl⟩
      simp only [G, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_range]
      exact ⟨fun a i => Nat.lt_succ_of_le (h1 a i), fun a i => Nat.lt_succ_of_le (h2 a i),
        fun b i => Nat.lt_succ_of_le (h3 b i)⟩
  · intro τ s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hA, hA', hB⟩ := hG x hx
    have hR0 : 0 ≤ R := by linarith
    have hRR : R ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by
      have h1 : (1 : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : R ≤ R ^ (2 * (p + q) + 1) := by
        simpa using pow_le_pow_right₀ hR1 (Nat.le_add_left 1 (2 * (p + q)))
      calc R ≤ R ^ (2 * (p + q) + 1) := h2
        _ = 1 * R ^ (2 * (p + q) + 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg hR0 _)
    have hR'0 : 0 ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by linarith
    refine (l1Norm_rowBlockLeadingMinorProduct_le c c' _ _ hR'0 ?_ ?_ (Nat.le_add_right p q)
      (Nat.le_add_left q p)).trans (le_of_eq ?_)
    · intro t a
      have := hlen ((τ t).comp (IsCMField.complexConj E : E →+* E)) (x.1 a) (hA a)
      exact this.trans (pow_le_pow_left₀ hR0 hRR 2)
    · intro t b
      have := sum_sq_perpVec_le (τ t) h hh (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a))
        (comb (x.2.2 b)) (R := R) (fun a => hlen _ _ (hA a)) (fun a => hlen _ _ (hA' a))
        (hlen _ _ (hB b))
      refine this.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg hR0 _)) ?_ 2)
      have h1 : ((p + 1).factorial : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h2 : R ^ (2 * p + 1) ≤ R ^ (2 * (p + q) + 1) := pow_le_pow_right₀ hR1 (by omega)
      exact mul_le_mul h1 h2 (pow_nonneg hR0 _) (by positivity)
    · subst hR hρ hdg
      push_cast
      ring
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    simp only [G, Finset.card_product, Fintype.card_piFinset, Finset.card_range,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdg]
    ring

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Subalgebra.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem (Subalgebra.prod_mem _ fun i _ => hM _ _) _`.
-/
private theorem det_mem_subalgebra_of_entries_mem' {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Subalgebra A B) {m : ℕ} (M : Matrix (Fin m) (Fin m) B) (hM : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => hM _ _) _

/- English proof (translation)
Unfold `Ha`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem]`. Apply `minorProd_mem_rowHighest` to reduce the goal to its premises. Introduce `t a b`.

Use `congrArg (τ t) (hef a b)` as an intermediate fact. Rewrite `this` using `[herm_one_eq_sum, map_sum, map_zero]`. Simplify `this` using `[dotProduct, map_mul]`. Express the relevant statement in the definitionally equal form `minorProd c c' _ _ ∈ symO p q τ Λ`. Unfold `symO minorProd`.

Use `Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _) (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)` and prove the remaining obligations. Unfold `xMinor`. Conclude with `det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)`. Unfold `yMinor`. Conclude with `det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)`.
-/
private theorem minorProd_mem_Ha_of_herm_orthogonal {K : Type} [Field K] {T : Type*} [Fintype T] {p q : ℕ}
    (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (e : Fin p → Fin n → E)
    (f : Fin q → Fin n → E) (he : ∀ a, e a ∈ Λ) (hf : ∀ b, f b ∈ Λ)
    (hef : ∀ a b, herm 1 (e a) (f b) = 0) :
    minorProd c c' (fun t a k => τ t (e a k)) (fun t b k => τ t (cc (f b k))) ∈ Ha τ c c' Λ := by
  unfold Ha
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    apply minorProd_mem_rowHighest
    intro t a b
    have := congrArg (τ t) (hef a b)
    rw [herm_one_eq_sum, map_sum, map_zero] at this
    simpa [dotProduct, map_mul] using this
  · change minorProd c c' _ _ ∈ symO p q τ Λ
    unfold symO minorProd
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · unfold xMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)
    · unfold yMinor
      exact det_mem_subalgebra_of_entries_mem' _ _ fun a b => Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)

/- English proof (translation)
Take `⟨hfg', hint', hdual'⟩` from `conjLattice_selfDual hfg hint hdual`. Take `⟨S', hS'1, hS'2, hS'3, hS'4⟩` from `exists_short_harmonic_family_few_columns (Λ := conjLattice Λ) hfg' hint' hdual' hn c c' ha`. Set `cj : (Fin p → Fin n → E) × (Fin q → Fin n → E) → (Fin p → Fin n → E) × (Fin q → Fin n → E)` to `fun s => (fun a => conjVec E n (s.1 a), fun b => conjVec E n (s.2 b))`. Establish `hcc : ∀ x : E, cc (cc x) = x` using `fun x => by`. Use `congrFun (conjVec_conjVec (E := E) (n := 1) (fun _ => x)) 0` as an intermediate fact.

Simplify `this` using `only [conjVec_apply]`. Establish `hpoly : ∀ (K : Type) [Field K] (τ : T → E →+* K) (s : (Fin p → Fin n → E) × (Fin q → Fin n → E)), minorProd c c' (fun t a k => τ t ((cj s).1 a k)) (fun t b k => τ t (cc ((cj s).2 b k))) = minorProd c c' (fun t a k => τ t (cc (s.1 a k))) (fun t b k => τ t (s.2 b k))`. Introduce `K _ τ s`. Simplify using `only [cj, conjVec_apply, hcc]`. Establish `hmem : ∀ s ∈ S', (∀ a, (cj s).1 a ∈ Λ) ∧ (∀ b, (cj s).2 b ∈ Λ) ∧ ∀ a b, herm 1 ((cj s).1 a) ((cj s).2 b) = 0`.

Introduce `s hs`. Take `⟨h1, h2, h3⟩` from `hS'1 s hs`. Use `⟨fun a => mem_conjLattice.mp (h1 a), fun b => mem_conjLattice.mp (h2 b), fun a b => ?_⟩` and prove the remaining obligations. Simplify using `only [cj]`. Rewrite using `[herm_conjVec]`.

Conclude with `h3 a b`. Use `⟨S'.image cj, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Take `⟨s', hs', rfl⟩` from `Finset.mem_image.mp hs`. Conclude with `hmem s' hs'`.

Introduce `K _ τ s hs`. Take `⟨s', hs', rfl⟩` from `Finset.mem_image.mp hs`. Take `⟨h1, h2, h3⟩` from `hmem s' hs'`. Conclude with `minorProd_mem_Ha_of_herm_orthogonal τ c c' _ _ h1 h2 h3`. Introduce `K _ _ τ hτ`.

Rewrite using `[← hS'2 K τ hτ, Finset.coe_image, ← Set.image_comp]`. Conclude with `congrArg _ (Set.image_congr fun s _ => hpoly K τ s)`. Introduce `τ s hs`. Take `⟨s', hs', rfl⟩` from `Finset.mem_image.mp hs`. Rewrite using `[hpoly ℂ τ s']`.

Conclude with `hS'3 τ s' hs'`. Conclude with `Finset.card_image_le.trans hS'4`.
-/
theorem exists_short_harmonic_family_few_columns_linear (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    {p q : ℕ} (hn : p + q ≤ n) {T : Type*} [Fintype T] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c') :
    ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
      (∀ s ∈ S, (∀ a, s.1 a ∈ Λ) ∧ (∀ b, s.2 b ∈ Λ) ∧ ∀ a b, herm 1 (s.1 a) (s.2 b) = 0) ∧
      (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S,
        (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ∈
          Ha τ c c' Λ) ∧
      (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
        (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) →
        Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
          minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) '' S) =
          rowHighest K c c') ∧
      (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
        l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ≤
          (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) *
            ((2 * (p + q : ℕ) + 1) * typeDegree c c') *
            (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^
            typeDegree c c') ∧
      S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  classical
  obtain ⟨hfg', hint', hdual'⟩ := conjLattice_selfDual hfg hint hdual
  obtain ⟨S', hS'1, hS'2, hS'3, hS'4⟩ :=
    exists_short_harmonic_family_few_columns (Λ := conjLattice Λ) hfg' hint' hdual' hn c c' ha
  let cj : (Fin p → Fin n → E) × (Fin q → Fin n → E) → (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
    fun s => (fun a => conjVec E n (s.1 a), fun b => conjVec E n (s.2 b))
  have hcc : ∀ x : E, cc (cc x) = x := fun x => by
    have := congrFun (conjVec_conjVec (E := E) (n := 1) (fun _ => x)) 0
    simpa only [conjVec_apply] using this
  have hpoly : ∀ (K : Type) [Field K] (τ : T → E →+* K) (s : (Fin p → Fin n → E) × (Fin q → Fin n → E)),
      minorProd c c' (fun t a k => τ t ((cj s).1 a k)) (fun t b k => τ t (cc ((cj s).2 b k))) =
        minorProd c c' (fun t a k => τ t (cc (s.1 a k))) (fun t b k => τ t (s.2 b k)) := by
    intro K _ τ s
    simp only [cj, conjVec_apply, hcc]
  have hmem : ∀ s ∈ S', (∀ a, (cj s).1 a ∈ Λ) ∧ (∀ b, (cj s).2 b ∈ Λ) ∧
      ∀ a b, herm 1 ((cj s).1 a) ((cj s).2 b) = 0 := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hS'1 s hs
    refine ⟨fun a => mem_conjLattice.mp (h1 a), fun b => mem_conjLattice.mp (h2 b), fun a b => ?_⟩
    simp only [cj]
    rw [herm_conjVec]
    exact h3 a b
  refine ⟨S'.image cj, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact hmem s' hs'
  · intro K _ τ s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨h1, h2, h3⟩ := hmem s' hs'
    exact minorProd_mem_Ha_of_herm_orthogonal τ c c' _ _ h1 h2 h3
  · intro K _ _ τ hτ
    rw [← hS'2 K τ hτ, Finset.coe_image, ← Set.image_comp]
    exact congrArg _ (Set.image_congr fun s _ => hpoly K τ s)
  · intro τ s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    rw [hpoly ℂ τ s']
    exact hS'3 τ s' hs'
  · exact Finset.card_image_le.trans hS'4

end

/- English proof (translation)
Introduce `E _ _ _ n Λ hfg hint hdual p q hn T _ c c' ha`. Take `⟨S, -, h2, h3, h4, h5⟩` from `exists_short_harmonic_family_few_columns_linear hfg hint hdual hn c c' ha`. Conclude with `⟨S, h2, h3, h4, h5⟩`.
-/
theorem short_harmonic_family_few_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ (p q : ℕ), p + q ≤ n → ∀ (T : Type) [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), 1 ≤ typeDegree c c' → ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)), (∀ (K : Type) [Field K] (τ : T → E →+* K), ∀ s ∈ S, (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ∈ Ha τ c c' Λ) ∧ (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K), (Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x)) → Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) => minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) '' S) = rowHighest K c c') ∧ (∀ (τ : T → E →+* ℂ), ∀ s ∈ S, l1Norm (minorProd c c' (fun t a k => τ t (s.1 a k)) fun t b k => τ t (cc (s.2 b k))) ≤ (((p + q : ℕ) : ℝ) * Real.sqrt n * (((p + q) + 1).factorial * ((2 * fdeg E * n) * ((2 * (p + q : ℕ) + 1) * typeDegree c c') * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E)) ^ (2 * (p + q) + 1))) ^ typeDegree c c') ∧ S.card ≤ ((2 * (p + q) + 1) * typeDegree c c' + 1) ^ (2 * fdeg E * n * (2 * p + q)) := by
  intro E _ _ _ n Λ hfg hint hdual p q hn T _ c c' ha
  obtain ⟨S, -, h2, h3, h4, h5⟩ := exists_short_harmonic_family_few_columns_linear hfg hint hdual hn c c' ha
  exact ⟨S, h2, h3, h4, h5⟩

end GlobalTheory.Harm
