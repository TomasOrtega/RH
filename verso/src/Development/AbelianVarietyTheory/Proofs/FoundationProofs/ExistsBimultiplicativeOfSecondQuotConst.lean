import Mathlib

open Filter Module TensorProduct

namespace GlobalTheory

section SecondDifference

variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]

def secondDiff (f : X → A) (a μ ν : X) : A :=
  f (a + μ + ν) - f (a + μ) - f (a + ν) + f a

def HasConstSecondDiff (f : X → A) : Prop :=
  ∀ a a' μ ν : X, secondDiff f a μ ν = secondDiff f a' μ ν

/- English proof (translation)
Simplify using `only [secondDiff, add_right_comm a μ ν]`. Normalize the expressions using the abelian group laws.
-/
theorem secondDiff_comm (f : X → A) (a μ ν : X) : secondDiff f a μ ν = secondDiff f a ν μ := by
  simp only [secondDiff, add_right_comm a μ ν]
  abel

/- English proof (translation)
Simplify using `only [secondDiff, ← add_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem secondDiff_add_left (f : X → A) (a μ μ' ν : X) :
    secondDiff f a (μ + μ') ν = secondDiff f a μ ν + secondDiff f (a + μ) μ' ν := by
  simp only [secondDiff, ← add_assoc]
  abel

/- English proof (translation)
Simplify using `[secondDiff]`.
-/
theorem secondDiff_zero (f : X → A) (μ ν : X) :
    secondDiff f 0 μ ν = f (μ + ν) - f μ - f ν + f 0 := by
  simp [secondDiff]

/- English proof (translation)
Use `⟨fun h a μ ν => ?_, fun h a a' μ ν => ?_⟩` and prove the remaining obligations. Rewrite using `[← secondDiff_zero, ← h a 0]`. Both sides reduce to the same expression. Conclude with `(h a μ ν).trans (h a' μ ν).symm`.
-/
theorem hasConstSecondDiff_iff (f : X → A) :
    HasConstSecondDiff f ↔ ∀ a μ ν : X,
      f (a + μ + ν) - f (a + μ) - f (a + ν) + f a = f (μ + ν) - f μ - f ν + f 0 := by
  refine ⟨fun h a μ ν => ?_, fun h a a' μ ν => ?_⟩
  · rw [← secondDiff_zero, ← h a 0]; rfl
  · exact (h a μ ν).trans (h a' μ ν).symm

namespace HasConstSecondDiff

variable {f : X → A}

def bilin (h : HasConstSecondDiff f) : X →ₗ[ℤ] X →ₗ[ℤ] A :=
  have hl : ∀ μ μ' ν : X,
      secondDiff f 0 (μ + μ') ν = secondDiff f 0 μ ν + secondDiff f 0 μ' ν := fun μ μ' ν => by
    rw [secondDiff_add_left, h (0 + μ) 0]
  have hr : ∀ μ ν ν' : X,
      secondDiff f 0 μ (ν + ν') = secondDiff f 0 μ ν + secondDiff f 0 μ ν' := fun μ ν ν' => by
    rw [secondDiff_comm, hl, secondDiff_comm f 0 ν, secondDiff_comm f 0 ν']
  (AddMonoidHom.mk' (fun μ => (AddMonoidHom.mk' (fun ν => secondDiff f 0 μ ν) (hr μ)).toIntLinearMap)
    (fun μ μ' => LinearMap.ext fun ν => hl μ μ' ν)).toIntLinearMap

/- English proof (translation)
The claim follows from `h 0 a μ ν`.
-/
theorem bilin_apply (h : HasConstSecondDiff f) (a μ ν : X) :
    h.bilin μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a :=
  h 0 a μ ν

/- English proof (translation)
The claim follows from `secondDiff_zero f μ ν`.
-/
theorem bilin_apply_zero (h : HasConstSecondDiff f) (μ ν : X) :
    h.bilin μ ν = f (μ + ν) - f μ - f ν + f 0 :=
  secondDiff_zero f μ ν

/- English proof (translation)
The claim follows from `secondDiff_comm f 0 μ ν`.
-/
theorem bilin_comm (h : HasConstSecondDiff f) (μ ν : X) : h.bilin μ ν = h.bilin ν μ :=
  secondDiff_comm f 0 μ ν

/- English proof (translation)
Rewrite using `[h.bilin_apply_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem map_add (h : HasConstSecondDiff f) (μ ν : X) :
    f (μ + ν) - f 0 = (f μ - f 0) + (f ν - f 0) + h.bilin μ ν := by
  rw [h.bilin_apply_zero]; abel

/- English proof (translation)
Establish `h₁` using `h.map_add x (-x)`. Rewrite `h₁` using `[add_neg_cancel, sub_self, he, map_neg]`. Rewrite using `[two_smul]`. Conclude with `(add_neg_eq_zero.1 h₁.symm).symm`.
-/
theorem bilin_self (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (x : X) :
    h.bilin x x = 2 • (f x - f 0) := by
  have h₁ := h.map_add x (-x)
  rw [add_neg_cancel, sub_self, he, map_neg] at h₁
  rw [two_smul]
  exact (add_neg_eq_zero.1 h₁.symm).symm

/- English proof (translation)
Establish `hn : ∀ n : ℕ, f ((n : ℤ) • x) - f 0 = ((n : ℤ) * n) • (f x - f 0)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ, add_smul, one_smul, h.map_add, ih, map_smul, LinearMap.smul_apply, h.bilin_self he]`.

Use `module`. Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`. Conclude with `hn m`. Rewrite using `[neg_smul, he, neg_mul_neg, hn]`.
-/
theorem map_zsmul (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (n : ℤ) (x : X) :
    f (n • x) - f 0 = (n * n) • (f x - f 0) := by
  have hn : ∀ n : ℕ, f ((n : ℤ) • x) - f 0 = ((n : ℤ) * n) • (f x - f 0) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul, h.map_add, ih, map_smul, LinearMap.smul_apply,
        h.bilin_self he]
      module
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact hn m
  · rw [neg_smul, he, neg_mul_neg, hn]

def quadraticMap (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) : QuadraticMap ℤ X A where
  toFun x := f x - f 0
  toFun_smul := h.map_zsmul he
  exists_companion' := ⟨h.bilin, h.map_add⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quadraticMap_apply (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (x : X) :
    h.quadraticMap he x = f x - f 0 := rfl

/- English proof (translation)
Simplify using `only [QuadraticMap.polar, quadraticMap_apply, h.bilin_apply_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem polar_quadraticMap (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (μ ν : X) :
    QuadraticMap.polar (h.quadraticMap he) μ ν = h.bilin μ ν := by
  simp only [QuadraticMap.polar, quadraticMap_apply, h.bilin_apply_zero]
  abel

/- English proof (translation)
The claim follows from `LinearMap.ext₂ (h.polar_quadraticMap he)`.
-/
theorem polarBilin_quadraticMap (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) :
    (h.quadraticMap he).polarBilin = h.bilin :=
  LinearMap.ext₂ (h.polar_quadraticMap he)

/- English proof (translation)
Introduce `a a' μ ν` and use `by simpa [secondDiff] using congrArg v (h a a' μ ν)`.
-/
theorem comp_left {A' : Type*} [AddCommGroup A'] (h : HasConstSecondDiff f) (v : A →+ A') :
    HasConstSecondDiff (v ∘ f) := fun a a' μ ν => by
  simpa [secondDiff] using congrArg v (h a a' μ ν)

/- English proof (translation)
Simplify using `[bilin_apply_zero]`.
-/
theorem bilin_comp_left {A' : Type*} [AddCommGroup A'] (h : HasConstSecondDiff f) (v : A →+ A')
    (μ ν : X) : (h.comp_left v).bilin μ ν = v (h.bilin μ ν) := by
  simp [bilin_apply_zero]

end HasConstSecondDiff

/- English proof (translation)
Establish `key : ∀ a μ ν, secondDiff (fun x => Q x + c) a μ ν = QuadraticMap.polar Q μ ν`. Introduce `a μ ν`. Simplify using `only [secondDiff, QuadraticMap.map_add Q, QuadraticMap.polar_add_left]`. Normalize the expressions using the abelian group laws. Introduce `a a' μ ν`.

Rewrite using `[key, key]`.
-/
theorem hasConstSecondDiff_quadraticMap_add (Q : QuadraticMap ℤ X A) (c : A) :
    HasConstSecondDiff fun x => Q x + c := by
  have key : ∀ a μ ν, secondDiff (fun x => Q x + c) a μ ν = QuadraticMap.polar Q μ ν := by
    intro a μ ν
    simp only [secondDiff, QuadraticMap.map_add Q, QuadraticMap.polar_add_left]
    abel
  intro a a' μ ν
  rw [key, key]

/- English proof (translation)
Establish `h' : HasConstSecondDiff f` using `h`. Conclude with `⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, h'.bilin_apply, h'.bilin_comm⟩`.
-/
theorem exists_biadditive_of_secondDiff_const (f : X → A)
    (h : ∀ a a' μ ν : X, f (a + μ + ν) - f (a + μ) - f (a + ν) + f a =
      f (a' + μ + ν) - f (a' + μ) - f (a' + ν) + f a') :
    ∃ B : X →+ X →+ A, (∀ a μ ν, B μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a) ∧
      ∀ μ ν, B μ ν = B ν μ := by
  have h' : HasConstSecondDiff f := h
  exact ⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, h'.bilin_apply, h'.bilin_comm⟩

/- English proof (translation)
Take `⟨B, hB, hs⟩` from `exists_biadditive_of_secondDiff_const (fun x => (Additive.ofMul (ψ x) : Additive G)) h`. Use `⟨fun μ ν => (B μ ν).toMul, fun a μ ν => congrArg Additive.toMul (hB a μ ν), fun μ μ' ν => ?_, fun μ ν ν' => ?_, fun μ ν => congrArg Additive.toMul (hs μ ν)⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem exists_bimultiplicative_of_secondQuot_const {G : Type*} [CommGroup G] (ψ : X → G)
    (h : ∀ a a' μ ν : X, ψ (a + μ + ν) / ψ (a + μ) / ψ (a + ν) * ψ a =
      ψ (a' + μ + ν) / ψ (a' + μ) / ψ (a' + ν) * ψ a') :
    ∃ τ : X → X → G, (∀ a μ ν, τ μ ν = ψ (a + μ + ν) / ψ (a + μ) / ψ (a + ν) * ψ a) ∧
      (∀ μ μ' ν, τ (μ + μ') ν = τ μ ν * τ μ' ν) ∧ (∀ μ ν ν', τ μ (ν + ν') = τ μ ν * τ μ ν') ∧
      ∀ μ ν, τ μ ν = τ ν μ := by
  obtain ⟨B, hB, hs⟩ := exists_biadditive_of_secondDiff_const
    (fun x => (Additive.ofMul (ψ x) : Additive G)) h
  refine ⟨fun μ ν => (B μ ν).toMul, fun a μ ν => congrArg Additive.toMul (hB a μ ν),
    fun μ μ' ν => ?_, fun μ ν ν' => ?_, fun μ ν => congrArg Additive.toMul (hs μ ν)⟩
  · simp
  · simp

end SecondDifference

section Definite

/- English proof (translation)
Establish `h : Continuous fun v => (QuadraticMap.associated Q).toContinuousBilinearMap v v` using `by fun_prop`. Conclude with `h.congr fun v => QuadraticMap.associated_eq_self_apply ℝ Q v`.
-/
private theorem continuous_quadraticForm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) : Continuous Q := by
  have h : Continuous fun v => (QuadraticMap.associated Q).toContinuousBilinearMap v v := by
    fun_prop
  exact h.congr fun v => QuadraticMap.associated_eq_self_apply ℝ Q v

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Establish `hc : Continuous Q` using `continuous_quadraticForm Q`. Establish `key : ∀ v : ι → ℝ, v ≠ 0 → ¬ (Q v < 0 ∨ (Q v = 0 ∧ ∀ r, QuadraticMap.polar Q v r = 0))`. Introduce `v hv hQ`. Take `⟨C, hC⟩` from `(isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image hc.continuousOn`.

Take `⟨D, hD⟩` from `(isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image (f := fun r => -QuadraticMap.polar Q v r) (Q.polarBilin v).continuous_of_finiteDimensional.neg.continuousOn`. Set `n : ℕ → ι → ℤ` to `fun t i => ⌊(t : ℝ) * v i⌋`. Establish `hn : Tendsto n atTop cofinite`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hv`. Establish `hi' : v i ≠ 0` using `hi`.

Establish `h₁ : Tendsto (fun t => n t i) atTop cofinite`. Rewrite using `[Int.cofinite_eq]`. Break down `hi'.lt_or_gt with h₀ | h₀` into its components or cases. Conclude with `(tendsto_floor_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀)).mono_right le_sup_left`. Conclude with `(tendsto_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const h₀)).mono_right le_sup_right`.

Introduce `s hs`. Use `h₁ (Set.Finite.compl_mem_cofinite ((Set.Finite.image (fun m => m i) hs)))` as an intermediate fact. Rewrite `this`, the goal using `[mem_map]`. Use `filter_upwards [this] with t ht`. Assume the negation of the conclusion as `hts`.

Conclude with `ht ⟨n t, hts, rfl⟩`. Establish `hval : ∀ t : ℕ, ∃ r ∈ Set.Icc (0 : ι → ℝ) 1, (Q fun i => (n t i : ℝ)) = (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) + Q r`. Introduce `t`. Use `⟨fun i => Int.fract ((t : ℝ) * v i), ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, ?_⟩` and prove the remaining obligations. Establish `e : (fun i => (n t i : ℝ)) = (t : ℝ) • v + -fun i => Int.fract ((t : ℝ) * v i)`.

Use extensionality with `i`. Simplify using `[n, ← sub_eq_add_neg]`. Rewrite using `[e, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_neg, QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hev : ∀ᶠ t : ℕ in atTop, (Q fun i => (n t i : ℝ)) ≤ C`. Break down `hQ with h₀ | ⟨h₀, h₁⟩` into its components or cases. Use `filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀).eventually_le_atBot (-D)] with t ht`. Take `⟨r, hr, e⟩` from `hval t`. Establish `h₂ : Q r ≤ C` using `hC ⟨r, hr, rfl⟩`.

Establish `h₃ : -QuadraticMap.polar Q v r ≤ D` using `hD ⟨r, hr, rfl⟩`. Establish `h₄ : (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg t) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Eventually.of_forall fun t => ?_` and prove the remaining obligations. Take `⟨r, hr, e⟩` from `hval t`.

Establish `h₂ : Q r ≤ C` using `hC ⟨r, hr, rfl⟩`. Rewrite using `[e, h₀, h₁]`. Simplify using `using h₂`. Take `⟨t, h₁, h₂⟩` from `(hev.and ((h.comp hn).eventually_gt_atTop C)).exists`. Conclude with `absurd h₁ (not_le.2 h₂)`.

Establish `hnn : ∀ v, 0 ≤ Q v` using `fun v => by`. Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Conclude with `not_lt.1 fun h₀ => key v hv (Or.inl h₀)`. Introduce `v hv`.

Use `(hnn v).lt_of_ne' fun h₀ => key v hv (Or.inr ⟨h₀, fun r => ?_⟩)` and prove the remaining obligations. Assume the negation of the conclusion as `hr`. Use `hnn ((-(Q r + 1) / QuadraticMap.polar Q v r) • v + r)` as an intermediate fact. Rewrite `this` using `[QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_left, h₀, smul_zero, smul_eq_mul, div_mul_cancel₀ _ hr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posDef_of_tendsto_intCast {ι : Type*} [Finite ι] (Q : QuadraticForm ℝ (ι → ℝ))
    (h : Tendsto (fun n : ι → ℤ => Q fun i => (n i : ℝ)) cofinite atTop) : Q.PosDef := by
  have := Fintype.ofFinite ι
  have hc : Continuous Q := continuous_quadraticForm Q

  have key : ∀ v : ι → ℝ, v ≠ 0 → ¬ (Q v < 0 ∨ (Q v = 0 ∧ ∀ r, QuadraticMap.polar Q v r = 0)) := by
    intro v hv hQ
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).bddAbove_image
      (f := fun r => -QuadraticMap.polar Q v r)
      (Q.polarBilin v).continuous_of_finiteDimensional.neg.continuousOn

    let n : ℕ → ι → ℤ := fun t i => ⌊(t : ℝ) * v i⌋
    have hn : Tendsto n atTop cofinite := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      have hi' : v i ≠ 0 := hi
      have h₁ : Tendsto (fun t => n t i) atTop cofinite := by
        rw [Int.cofinite_eq]
        rcases hi'.lt_or_gt with h₀ | h₀
        · exact (tendsto_floor_atBot.comp
            (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀)).mono_right le_sup_left
        · exact (tendsto_floor_atTop.comp
            (tendsto_natCast_atTop_atTop.atTop_mul_const h₀)).mono_right le_sup_right
      intro s hs
      have := h₁ (Set.Finite.compl_mem_cofinite ((Set.Finite.image (fun m => m i) hs)))
      rw [mem_map] at this ⊢
      filter_upwards [this] with t ht
      by_contra hts
      exact ht ⟨n t, hts, rfl⟩
    have hval : ∀ t : ℕ, ∃ r ∈ Set.Icc (0 : ι → ℝ) 1, (Q fun i => (n t i : ℝ)) =
        (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) + Q r := by
      intro t
      refine ⟨fun i => Int.fract ((t : ℝ) * v i),
        ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, ?_⟩
      have e : (fun i => (n t i : ℝ)) = (t : ℝ) • v + -fun i => Int.fract ((t : ℝ) * v i) := by
        ext i
        simp [n, ← sub_eq_add_neg]
      rw [e, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_neg,
        QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left]
      simp only [smul_eq_mul]
      ring
    have hev : ∀ᶠ t : ℕ in atTop, (Q fun i => (n t i : ℝ)) ≤ C := by
      rcases hQ with h₀ | ⟨h₀, h₁⟩
      · filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h₀).eventually_le_atBot
          (-D)] with t ht
        obtain ⟨r, hr, e⟩ := hval t
        have h₂ : Q r ≤ C := hC ⟨r, hr, rfl⟩
        have h₃ : -QuadraticMap.polar Q v r ≤ D := hD ⟨r, hr, rfl⟩
        have h₄ : (t : ℝ) * (t * Q v + -QuadraticMap.polar Q v r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg t) (by linarith)
        linarith
      · refine Eventually.of_forall fun t => ?_
        obtain ⟨r, hr, e⟩ := hval t
        have h₂ : Q r ≤ C := hC ⟨r, hr, rfl⟩
        rw [e, h₀, h₁]
        simpa using h₂
    obtain ⟨t, h₁, h₂⟩ := (hev.and ((h.comp hn).eventually_gt_atTop C)).exists
    exact absurd h₁ (not_le.2 h₂)
  have hnn : ∀ v, 0 ≤ Q v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact not_lt.1 fun h₀ => key v hv (Or.inl h₀)
  intro v hv
  refine (hnn v).lt_of_ne' fun h₀ => key v hv (Or.inr ⟨h₀, fun r => ?_⟩)
  by_contra hr
  have := hnn ((-(Q r + 1) / QuadraticMap.polar Q v r) • v + r)
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_left, h₀,
    smul_zero, smul_eq_mul, div_mul_cancel₀ _ hr] at this
  linarith

/- English proof (translation)
Take `⟨κ, a, -, hspan, hli⟩` from `exists_linearIndependent' ℝ (φ : X → V)`. Establish `: Finite κ` using `hli.finite`. Use `Fintype.ofFinite κ` as an intermediate fact. Set `b : Basis κ ℝ V` to `Basis.mk hli (by rw [hspan, hφ])`. Establish `hb : ∀ n : κ → ℤ, φ (∑ i, n i • a i) = b.equivFun.symm fun i => (n i : ℝ)` using `fun n => by`.

Simplify using `[b, Int.cast_smul_eq_zsmul]`. Establish `hinj : Function.Injective fun n : κ → ℤ => ∑ i, n i • a i` using `fun n m e => by`. Establish `e'` using `congrArg φ e`. Simplify using `only [hb] at e'`. Use extensionality with `i`.

Conclude with `congrFun (b.equivFun.symm.injective e') i` after adjusting the coercions. Establish `hp` using `posDef_of_tendsto_intCast (Q.comp b.equivFun.symm.toLinearMap) ((h.comp hinj.tendsto_cofinite).congr fun n => by simp [hb])`. Introduce `v hv`. Simplify `hv)` using `using hp (b.equivFun v) (by simpa`.
-/
theorem posDef_of_tendsto_comp {X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (φ : X →+ V) (hφ : Submodule.span ℝ (Set.range φ) = ⊤)
    (Q : QuadraticForm ℝ V) (h : Tendsto (fun x => Q (φ x)) cofinite atTop) : Q.PosDef := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℝ (φ : X → V)
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  let b : Basis κ ℝ V := Basis.mk hli (by rw [hspan, hφ])
  have hb : ∀ n : κ → ℤ, φ (∑ i, n i • a i) = b.equivFun.symm fun i => (n i : ℝ) := fun n => by
    simp [b, Int.cast_smul_eq_zsmul]
  have hinj : Function.Injective fun n : κ → ℤ => ∑ i, n i • a i := fun n m e => by
    have e' := congrArg φ e
    simp only [hb] at e'
    ext i
    exact_mod_cast congrFun (b.equivFun.symm.injective e') i
  have hp := posDef_of_tendsto_intCast (Q.comp b.equivFun.symm.toLinearMap)
    ((h.comp hinj.tendsto_cofinite).congr fun n => by simp [hb])
  intro v hv
  simpa using hp (b.equivFun v) (by simpa using hv)

/- English proof (translation)
Use `FiniteDimensional.proper_real V` as an intermediate fact. Take `⟨c, hc, h⟩` from `(isCompact_sphere (0 : V) 1).exists_forall_le' (continuous_quadraticForm Q).continuousOn (a := 0) (fun v hv => hQ v (by rintro rfl; simp at hv))`. Use `⟨c, hc, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`.

Establish `hn : ‖v‖ ≠ 0` using `norm_ne_zero_iff.2 hv`. Establish `h₁` using `h (‖v‖⁻¹ • v) (by simp [norm_smul, hn])`. Rewrite `h₁` using `[QuadraticMap.map_smul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pos_mul_norm_sq_le_of_posDef {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ Q v := by
  have := FiniteDimensional.proper_real V
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le'
    (continuous_quadraticForm Q).continuousOn (a := 0)
    (fun v hv => hQ v (by rintro rfl; simp at hv))
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have h₁ := h (‖v‖⁻¹ • v) (by simp [norm_smul, hn])
  rw [QuadraticMap.map_smul, smul_eq_mul] at h₁
  calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * ‖v‖⁻¹ * Q v * ‖v‖ ^ 2 := by gcongr
    _ = Q v := by field_simp

end Definite

section RealExtension

variable {X : Type*} [AddCommGroup X]

noncomputable def realExtBilin (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : LinearMap.BilinForm ℝ (ℝ ⊗[ℤ] X) :=
  LinearMap.liftBaseChange ℝ
    ((LinearMap.liftBaseChangeEquiv (R := ℤ) (M := X) (N := ℝ) ℝ).toLinearMap.restrictScalars ℤ
      ∘ₗ B)

/- English proof (translation)
Simplify using `[realExtBilin, mul_assoc]`.
-/
@[simp] theorem realExtBilin_tmul (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s t : ℝ) (x y : X) :
    realExtBilin B (s ⊗ₜ x) (t ⊗ₜ y) = s * t * B x y := by
  simp [realExtBilin, mul_assoc]

noncomputable def realExt (Q : QuadraticMap ℤ X ℝ) : QuadraticForm ℝ (ℝ ⊗[ℤ] X) :=
  (2⁻¹ : ℝ) • (realExtBilin Q.polarBilin).toQuadraticMap

/- English proof (translation)
Simplify using `only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply, realExtBilin_tmul, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, smul_eq_mul, two_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
@[simp] theorem realExt_tmul (Q : QuadraticMap ℤ X ℝ) (s : ℝ) (x : X) :
    realExt Q (s ⊗ₜ x) = s * s * Q x := by
  simp only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    realExtBilin_tmul, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, smul_eq_mul,
    two_smul]
  ring

/- English proof (translation)
Simplify using `only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem realExt_apply (Q : QuadraticMap ℤ X ℝ) (v : ℝ ⊗[ℤ] X) :
    realExt Q v = realExtBilin Q.polarBilin v v / 2 := by
  simp only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `only [QuadraticMap.polar, ← tmul_add, realExt_tmul, one_mul]`.
-/
theorem polar_realExt_one_tmul (Q : QuadraticMap ℤ X ℝ) (x y : X) :
    QuadraticMap.polar (realExt Q) (1 ⊗ₜ x) (1 ⊗ₜ y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← tmul_add, realExt_tmul, one_mul]

/- English proof (translation)
Use extensionality with `x y`. Simplify using `[polar_realExt_one_tmul]`.
-/
theorem polarBilin_realExt (Q : QuadraticMap ℤ X ℝ) :
    (realExt Q).polarBilin = realExtBilin Q.polarBilin := by
  ext x y
  simp [polar_realExt_one_tmul]

/- English proof (translation)
Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Proceed by induction on `v with`. Consider the case `zero => exact zero_mem _`. Consider the case `add v w hv hw => exact add_mem (hv trivial) (hw trivial)`. Consider the case `tmul s x`.

Establish `: s ⊗ₜ[ℤ] x = s • ((1 : ℝ) ⊗ₜ[ℤ] x)` using `by simp [smul_tmul']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`.
-/
theorem span_range_one_tmul :
    Submodule.span ℝ (Set.range fun x : X => (1 : ℝ) ⊗ₜ[ℤ] x) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  induction v with
  | zero => exact zero_mem _
  | add v w hv hw => exact add_mem (hv trivial) (hw trivial)
  | tmul s x =>
    have : s ⊗ₜ[ℤ] x = s • ((1 : ℝ) ⊗ₜ[ℤ] x) := by simp [smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

/- English proof (translation)
Apply `QuadraticMap.polarBilin_injective (R := ℝ) (IsUnit.mk0 2 two_ne_zero)` to reduce the goal to its premises. Use extensionality with `x y`. Simplify using `[QuadraticMap.polar, ← tmul_add, h]`.
-/
theorem eq_realExt (Q : QuadraticMap ℤ X ℝ) (P : QuadraticForm ℝ (ℝ ⊗[ℤ] X))
    (h : ∀ x, P (1 ⊗ₜ x) = Q x) : P = realExt Q := by
  apply QuadraticMap.polarBilin_injective (R := ℝ) (IsUnit.mk0 2 two_ne_zero)
  ext x y
  simp [QuadraticMap.polar, ← tmul_add, h]

/- English proof (translation)
The claim follows from `posDef_of_tendsto_comp (TensorProduct.mk ℤ ℝ X 1).toAddMonoidHom span_range_one_tmul _ (h.congr fun x => by simp)`.
-/
theorem posDef_realExt_of_tendsto [Module.Finite ℤ X] (Q : QuadraticMap ℤ X ℝ)
    (h : Tendsto Q cofinite atTop) : (realExt Q).PosDef :=
  posDef_of_tendsto_comp (TensorProduct.mk ℤ ℝ X 1).toAddMonoidHom span_range_one_tmul _
    (h.congr fun x => by simp)

/- English proof (translation)
Set `e : EuclideanSpace ℝ ι ≃ₗ[ℝ] ℝ ⊗[ℤ] X` to `(WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans (b.baseChange ℝ).equivFun.symm`. Take `⟨c, hc, h⟩` from `exists_pos_mul_norm_sq_le_of_posDef (Q := (realExt Q).comp e.toLinearMap) (fun v hv => hQ _ (by simpa using hv))`. Use `⟨c, hc, fun x => ?_⟩` and prove the remaining obligations. Establish `h₁` using `h (e.symm (1 ⊗ₜ x))`. Rewrite `h₁` using `[EuclideanSpace.real_norm_sq_eq, QuadraticMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply]`.

Simplify `h₁` using `[e]`.
-/
theorem exists_pos_mul_sum_sq_le_of_posDef_realExt {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ∑ i, (b.repr x i : ℝ) ^ 2 ≤ Q x := by
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] ℝ ⊗[ℤ] X :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans (b.baseChange ℝ).equivFun.symm
  obtain ⟨c, hc, h⟩ := exists_pos_mul_norm_sq_le_of_posDef (Q := (realExt Q).comp e.toLinearMap)
    (fun v hv => hQ _ (by simpa using hv))
  refine ⟨c, hc, fun x => ?_⟩
  have h₁ := h (e.symm (1 ⊗ₜ x))
  rw [EuclideanSpace.real_norm_sq_eq, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    e.apply_symm_apply] at h₁
  simpa [e] using h₁

/- English proof (translation)
Set `b` to `Module.finBasis ℤ X`. Take `⟨c, hc, h⟩` from `exists_pos_mul_sum_sq_le_of_posDef_realExt b hQ`. Use `tendsto_atTop.2 fun C => eventually_cofinite.2 ?_` and prove the remaining obligations. Use `((Set.finite_Icc (fun _ => -⌈C / c⌉) (fun _ => ⌈C / c⌉)).preimage b.equivFun.injective.injOn).subset fun x hx => ?_` and prove the remaining obligations. Establish `hx' : Q x < C` using `not_le.1 hx`.

Establish `hi : ∀ i, |b.repr x i| ≤ ⌈C / c⌉` using `fun i => by`. Establish `h₁ : (b.repr x i : ℝ) ^ 2 ≤ ∑ i, (b.repr x i : ℝ) ^ 2` using `Finset.single_le_sum (f := fun i => (b.repr x i : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `h₂ : (b.repr x i : ℝ) ^ 2 ≤ C / c`. Rewrite using `[le_div_iff₀' hc]`. Conclude with `((mul_le_mul_of_nonneg_left h₁ hc.le).trans (h x)).trans hx'.le`.

Establish `h₃ : (b.repr x i) ^ 2 ≤ ⌈C / c⌉` using `by exact_mod_cast h₂.trans (Int.le_ceil _)`. Use `le_trans ?_ h₃` and prove the remaining obligations. Rewrite using `[← sq_abs]`. Conclude with `Int.le_self_sq _`. Conclude with `⟨fun i => (abs_le.1 (hi i)).1, fun i => (abs_le.1 (hi i)).2⟩`.
-/
theorem tendsto_of_posDef_realExt [Module.Free ℤ X] [Module.Finite ℤ X]
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) : Tendsto Q cofinite atTop := by
  let b := Module.finBasis ℤ X
  obtain ⟨c, hc, h⟩ := exists_pos_mul_sum_sq_le_of_posDef_realExt b hQ
  refine tendsto_atTop.2 fun C => eventually_cofinite.2 ?_
  refine ((Set.finite_Icc (fun _ => -⌈C / c⌉) (fun _ => ⌈C / c⌉)).preimage
    b.equivFun.injective.injOn).subset fun x hx => ?_
  have hx' : Q x < C := not_le.1 hx
  have hi : ∀ i, |b.repr x i| ≤ ⌈C / c⌉ := fun i => by
    have h₁ : (b.repr x i : ℝ) ^ 2 ≤ ∑ i, (b.repr x i : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i => (b.repr x i : ℝ) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h₂ : (b.repr x i : ℝ) ^ 2 ≤ C / c := by
      rw [le_div_iff₀' hc]
      exact ((mul_le_mul_of_nonneg_left h₁ hc.le).trans (h x)).trans hx'.le
    have h₃ : (b.repr x i) ^ 2 ≤ ⌈C / c⌉ := by exact_mod_cast h₂.trans (Int.le_ceil _)
    refine le_trans ?_ h₃
    rw [← sq_abs]
    exact Int.le_self_sq _
  exact ⟨fun i => (abs_le.1 (hi i)).1, fun i => (abs_le.1 (hi i)).2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨tendsto_of_posDef_realExt, posDef_realExt_of_tendsto Q⟩`.
-/
theorem posDef_realExt_iff_tendsto [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : QuadraticMap ℤ X ℝ) : (realExt Q).PosDef ↔ Tendsto Q cofinite atTop :=
  ⟨tendsto_of_posDef_realExt, posDef_realExt_of_tendsto Q⟩

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun w hw => ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[QuadraticMap.polar_comm]`. Establish `h` using `hQ ((b.baseChange ℝ).equivFun.symm w) ((b.baseChange ℝ).equivFun.symm.map_ne_zero_iff.2 hw)`. Rewrite `h` using `[realExt_apply]`.

Establish `e : realExtBilin Q.polarBilin ((b.baseChange ℝ).equivFun.symm w) ((b.baseChange ℝ).equivFun.symm w) = star w ⬝ᵥ (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).mulVec w`. Simplify using `only [Basis.equivFun_symm_apply, Basis.baseChange_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, realExtBilin_tmul, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (b j) (b i), smul_eq_mul, Matrix.of_apply, Pi.star_apply, star_trivial]`. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posDef_gram_of_posDef_realExt {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun w hw => ?_
  · ext i j
    simp [QuadraticMap.polar_comm]
  · have h := hQ ((b.baseChange ℝ).equivFun.symm w)
      ((b.baseChange ℝ).equivFun.symm.map_ne_zero_iff.2 hw)
    rw [realExt_apply] at h
    have e : realExtBilin Q.polarBilin ((b.baseChange ℝ).equivFun.symm w)
        ((b.baseChange ℝ).equivFun.symm w) =
        star w ⬝ᵥ (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).mulVec w := by
      simp only [Basis.equivFun_symm_apply, Basis.baseChange_apply, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, realExtBilin_tmul, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (b j) (b i),
        smul_eq_mul, Matrix.of_apply, Pi.star_apply, star_trivial]
      ring
    linarith

/- English proof (translation)
Introduce `x hx`. Establish `h` using `hQ (1 ⊗ₜ x) fun h₀ => hx <| by`. Set `b` to `Module.finBasis ℤ X`. Use `b.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations. Simplify using `using congrArg (fun v => (b.baseChange ℝ).repr v i) h₀`.

Simplify using `using h`.
-/
theorem posDef_of_posDef_realExt [Module.Free ℤ X] [Module.Finite ℤ X]
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) : Q.PosDef := by
  intro x hx
  have h := hQ (1 ⊗ₜ x) fun h₀ => hx <| by
    let b := Module.finBasis ℤ X
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    simpa using congrArg (fun v => (b.baseChange ℝ).repr v i) h₀
  simpa using h

/- English proof (translation)
The claim follows from `posDef_realExt_of_tendsto _ (tendsto_atTop_add_const_right _ (-f 0) ht)`.
-/
theorem HasConstSecondDiff.posDef_realExt [Module.Finite ℤ X] {f : X → ℝ}
    (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    (realExt (h.quadraticMap he)).PosDef :=
  posDef_realExt_of_tendsto _ (tendsto_atTop_add_const_right _ (-f 0) ht)

/- English proof (translation)
Establish `h' : HasConstSecondDiff f` using `h`. Establish `hp` using `h'.posDef_realExt he ht`. Use `⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, realExt (h'.quadraticMap he), h'.bilin_apply, h'.bilin_comm, fun x => ?_, posDef_of_posDef_realExt hp, hp, fun x => by simp, fun μ ν => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = h'.bilin x x / 2`. Rewrite using `[h'.bilin_self he, two_smul]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(polar_realExt_one_tmul _ μ ν).trans (h'.polar_quadraticMap he μ ν)`.
-/
theorem exists_posDef_of_secondDiff_const [Module.Free ℤ X] [Module.Finite ℤ X] (f : X → ℝ)
    (h : ∀ a a' μ ν : X, f (a + μ + ν) - f (a + μ) - f (a + ν) + f a =
      f (a' + μ + ν) - f (a' + μ) - f (a' + ν) + f a')
    (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    ∃ (B : X →+ X →+ ℝ) (Q : QuadraticForm ℝ (ℝ ⊗[ℤ] X)),
      (∀ a μ ν, B μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a) ∧
      (∀ μ ν, B μ ν = B ν μ) ∧ (∀ x, f x - f 0 = B x x / 2) ∧ (∀ x, x ≠ 0 → 0 < f x - f 0) ∧
      Q.PosDef ∧ (∀ x, Q (1 ⊗ₜ x) = f x - f 0) ∧
      ∀ μ ν, QuadraticMap.polar Q (1 ⊗ₜ μ) (1 ⊗ₜ ν) = B μ ν := by
  have h' : HasConstSecondDiff f := h
  have hp := h'.posDef_realExt he ht
  refine ⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, realExt (h'.quadraticMap he),
    h'.bilin_apply, h'.bilin_comm, fun x => ?_, posDef_of_posDef_realExt hp, hp,
    fun x => by simp, fun μ ν => ?_⟩
  · change _ = h'.bilin x x / 2
    rw [h'.bilin_self he, two_smul]
    ring
  · exact (polar_realExt_one_tmul _ μ ν).trans (h'.polar_quadraticMap he μ ν)

/- English proof (translation)
Use `⟨fun a a' μ ν => ?_, fun x => by simp, tendsto_atTop_add_const_right _ _ ?_⟩` and prove the remaining obligations. Simplify using `only [secondDiff]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h : Tendsto (fun x : ℤ => |(x : ℝ)|) cofinite atTop`.

Rewrite using `[Int.cofinite_eq, tendsto_sup]`. Conclude with `⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id), tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩`. Simplify `(tendsto_pow_atTop two_ne_zero).comp h` using `[Function.comp_def]`.
-/
example : HasConstSecondDiff (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) ∧
    (∀ x : ℤ, (((-x : ℤ) : ℝ) ^ 2 + 1) = (x : ℝ) ^ 2 + 1) ∧
    Tendsto (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) cofinite atTop := by
  refine ⟨fun a a' μ ν => ?_, fun x => by simp, tendsto_atTop_add_const_right _ _ ?_⟩
  · simp only [secondDiff]
    push_cast
    ring
  · have h : Tendsto (fun x : ℤ => |(x : ℝ)|) cofinite atTop := by
      rw [Int.cofinite_eq, tendsto_sup]
      exact ⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id),
        tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩
    simpa [Function.comp_def] using (tendsto_pow_atTop two_ne_zero).comp h

end RealExtension

end GlobalTheory
