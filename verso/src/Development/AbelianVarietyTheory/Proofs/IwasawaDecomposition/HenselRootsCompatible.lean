import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top]`.
-/
theorem mem_ideal_smul_top_iff_mem {V : Type} [CommRing V] (I : Ideal V) (x : V) :
    x ∈ I • (⊤ : Submodule V V) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Establish `h1 : (maximalIdeal A).map α ≤ maximalIdeal V`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Conclude with `map_nonunit α y hy`. Use `Ideal.mem_map_of_mem α hx` as an intermediate fact.

Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 n this`.
-/
theorem localHom_map_mem_maximalIdeal_pow {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) {x : A}
    (hx : x ∈ maximalIdeal A ^ n) : α x ∈ maximalIdeal V ^ n := by
  have h1 : (maximalIdeal A).map α ≤ maximalIdeal V := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact map_nonunit α y hy
  have := Ideal.mem_map_of_mem α hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this

/- English proof (translation)
Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))`.
-/
theorem eval_map_mem_maximalIdeal_pow_of_coeff_mem {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))

/- English proof (translation)
Introduce `A R V _ _ _ _ _ _ _ φ α hα θ η q hq hqθ hqη happ hinj`. Establish `hq1 : q ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hqθ`. Establish `key : ∀ (n : ℕ) (P P' : Polynomial A), (P.map φ).eval θ - (P'.map φ).eval θ ∈ maximalIdeal R ^ n → (P.map α).eval η - (P'.map α).eval η ∈ maximalIdeal V ^ n`.

Introduce `n P P' h`. Establish `hD` using `Polynomial.modByMonic_add_div (P - P') q`. Establish `e1 : (P.map φ).eval θ - (P'.map φ).eval θ = (((P - P') %ₘ q).map φ).eval θ`. Rewrite using `[← Polynomial.eval_sub, ← Polynomial.map_sub]`. Use `conv_lhs => rw [← hD]`.

Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul, hqθ, zero_mul, add_zero]`. Establish `e2 : (P.map α).eval η - (P'.map α).eval η = (((P - P') %ₘ q).map α).eval η`. Rewrite using `[← Polynomial.eval_sub, ← Polynomial.map_sub]`. Use `conv_lhs => rw [← hD]`. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul, hqη, zero_mul, add_zero]`.

Rewrite using `[e2]`. Rewrite `h` using `[e1]`. Conclude with `eval_map_mem_maximalIdeal_pow_of_coeff_mem α n _ (hinj n _ (Polynomial.natDegree_modByMonic_lt _ hq hq1) h) η`. Establish `hmem : ∀ (n : ℕ) (x : V), x ∈ (maximalIdeal V ^ n) • (⊤ : Submodule V V) ↔ x ∈ maximalIdeal V ^ n` using `fun n x => mem_ideal_smul_top_iff_mem _ x`. Establish `ex : ∀ r : R, ∃ L : V, ∀ (n : ℕ) (P : Polynomial A), r - (P.map φ).eval θ ∈ maximalIdeal R ^ n → L - (P.map α).eval η ∈ maximalIdeal V ^ n`.

Introduce `r`. Use `choose Pn hPn using fun n => happ n r`. Establish `hc : ∀ {m n : ℕ}, m ≤ n → ((Pn m).map α).eval η ≡ ((Pn n).map α).eval η [SMOD (maximalIdeal V ^ m • (⊤ : Submodule V V))]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, hmem]`.

Apply `key` to reduce the goal to its premises. Establish `h1 : r - ((Pn n).map φ).eval θ ∈ maximalIdeal R ^ m` using `Ideal.pow_le_pow_right hmn (hPn n)`. Use `Ideal.sub_mem _ h1 (hPn m)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨L, hL⟩` from `IsPrecomplete.prec (f := fun k => ((Pn k).map α).eval η) inferInstance hc`. Use `⟨L, fun n P hP => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hmem n _).1 ((SModEq.sub_mem).1 (hL n))`. Establish `h2 : ((Pn n).map α).eval η - (P.map α).eval η ∈ maximalIdeal V ^ n`. Apply `key` to reduce the goal to its premises.

Use `Ideal.sub_mem _ hP (hPn n)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `Ideal.sub_mem _ h2 h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `haus : ∀ x : V, (∀ n, x ∈ maximalIdeal V ^ n) → x = 0`. Introduce `x hx`. Conclude with `IsHausdorff.haus inferInstance x fun n => SModEq.sub_mem.2 (by rw [sub_zero, hmem]; exact hx n)`. Use `choose ψ0 hψ0 using ex`.

Establish `char : ∀ (x : R) (b : V), (∀ n, ∃ P : Polynomial A, x - (P.map φ).eval θ ∈ maximalIdeal R ^ n ∧ b - (P.map α).eval η ∈ maximalIdeal V ^ n) → ψ0 x = b`. Introduce `x b h`. Rewrite using `[← sub_eq_zero]`. Apply `haus` to reduce the goal to its premises. Introduce `n`.

Take `⟨P, h1, h2⟩` from `h n`. Use `Ideal.sub_mem _ (hψ0 x n P h1) h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Set `ψ : R →+* V` to `{ toFun := ψ0 map_one' := char 1 1 fun n => ⟨1, by simp, by simp⟩ map_zero' := char 0 0 fun n => ⟨0, by simp, by simp⟩ map_add' := fun x y => char _ _ fun n => by`.

Take `⟨Px, hx⟩` from `happ n x`. Take `⟨Py, hy⟩` from `happ n y`. Use `⟨Px + Py, ?_, ?_⟩` and prove the remaining obligations. Use `Ideal.add_mem _ hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Polynomial.map_add, Polynomial.eval_add]`. Expand and normalize the polynomial expressions, which then agree. Use `Ideal.add_mem _ (hψ0 x n Px hx) (hψ0 y n Py hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Polynomial.map_add, Polynomial.eval_add]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_mul' := fun x y => char _ _ fun n => by`. Take `⟨Px, hx⟩` from `happ n x`. Take `⟨Py, hy⟩` from `happ n y`. Use `⟨Px * Py, ?_, ?_⟩` and prove the remaining obligations.

Use `Ideal.add_mem _ (Ideal.mul_mem_right y _ hx) (Ideal.mul_mem_left _ ((Px.map φ).eval θ) hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Polynomial.map_mul, Polynomial.eval_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `Ideal.add_mem _ (Ideal.mul_mem_right (ψ0 y) _ (hψ0 x n Px hx)) (Ideal.mul_mem_left _ ((Px.map α).eval η) (hψ0 y n Py hy))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Polynomial.map_mul, Polynomial.eval_mul]`. Use `ring }`. Use `⟨ψ, ?_, ⟨fun r hr => ?_⟩⟩` and prove the remaining obligations. Use extensionality with `a show ψ0 (φ a) = α a`.

Conclude with `char _ _ fun n => ⟨Polynomial.C a, by simp, by simp⟩`. Assume the negation of the conclusion as `hnu`. Establish `hrm : r ∈ maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal r).2 hnu`. Take `⟨P, hP⟩` from `happ 1 r`. Rewrite `hP` using `[pow_one]`.

Establish `h1 : (P.map φ).eval θ - ((0 : Polynomial A).map φ).eval θ ∈ maximalIdeal R ^ 1`. Simplify using `only [Polynomial.map_zero, Polynomial.eval_zero, sub_zero, pow_one]`. Use `Ideal.sub_mem _ hrm hP` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `key 1 P 0 h1`. Establish `h3` using `hψ0 r 1 P (by rw [pow_one]; exact hP)`. Establish `h4` using `Ideal.add_mem _ h3 h2`. Rewrite `h4` using `[pow_one]`. Establish `h5 : ψ0 r ∈ maximalIdeal V`.

Use `h4 using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h5 hr`.
-/
theorem lift_of_compatible_approx : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (φ : A →+* R) (α : A →+* V), IsLocalHom α → ∀ (θ : R) (η : V) (q : Polynomial A), q.Monic →
    (q.map φ).eval θ = 0 → (q.map α).eval η = 0 →
    (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) →
    (∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree →
      (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) →
    ∃ ψ : R →+* V, ψ.comp φ = α ∧ IsLocalHom ψ := by
  intro A R V _ _ _ _ _ _ _ φ α hα θ η q hq hqθ hqη happ hinj
  classical
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hqθ
  have key : ∀ (n : ℕ) (P P' : Polynomial A),
      (P.map φ).eval θ - (P'.map φ).eval θ ∈ maximalIdeal R ^ n →
      (P.map α).eval η - (P'.map α).eval η ∈ maximalIdeal V ^ n := by
    intro n P P' h
    have hD := Polynomial.modByMonic_add_div (P - P') q
    have e1 : (P.map φ).eval θ - (P'.map φ).eval θ = (((P - P') %ₘ q).map φ).eval θ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqθ, zero_mul, add_zero]
    have e2 : (P.map α).eval η - (P'.map α).eval η = (((P - P') %ₘ q).map α).eval η := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqη, zero_mul, add_zero]
    rw [e2]
    rw [e1] at h
    exact eval_map_mem_maximalIdeal_pow_of_coeff_mem α n _
      (hinj n _ (Polynomial.natDegree_modByMonic_lt _ hq hq1) h) η
  have hmem : ∀ (n : ℕ) (x : V),
      x ∈ (maximalIdeal V ^ n) • (⊤ : Submodule V V) ↔ x ∈ maximalIdeal V ^ n :=
    fun n x => mem_ideal_smul_top_iff_mem _ x
  have ex : ∀ r : R, ∃ L : V, ∀ (n : ℕ) (P : Polynomial A),
      r - (P.map φ).eval θ ∈ maximalIdeal R ^ n → L - (P.map α).eval η ∈ maximalIdeal V ^ n := by
    intro r
    choose Pn hPn using fun n => happ n r
    have hc : ∀ {m n : ℕ}, m ≤ n → ((Pn m).map α).eval η ≡ ((Pn n).map α).eval η
        [SMOD (maximalIdeal V ^ m • (⊤ : Submodule V V))] := by
      intro m n hmn
      rw [SModEq.sub_mem, hmem]
      apply key
      have h1 : r - ((Pn n).map φ).eval θ ∈ maximalIdeal R ^ m :=
        Ideal.pow_le_pow_right hmn (hPn n)
      have := Ideal.sub_mem _ h1 (hPn m)
      convert this using 1
      ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun k => ((Pn k).map α).eval η) inferInstance hc
    refine ⟨L, fun n P hP => ?_⟩
    have h1 := (hmem n _).1 ((SModEq.sub_mem).1 (hL n))
    have h2 : ((Pn n).map α).eval η - (P.map α).eval η ∈ maximalIdeal V ^ n := by
      apply key
      have := Ideal.sub_mem _ hP (hPn n)
      convert this using 1
      ring
    have := Ideal.sub_mem _ h2 h1
    convert this using 1
    ring
  have haus : ∀ x : V, (∀ n, x ∈ maximalIdeal V ^ n) → x = 0 := by
    intro x hx
    exact IsHausdorff.haus inferInstance x fun n =>
      SModEq.sub_mem.2 (by rw [sub_zero, hmem]; exact hx n)
  choose ψ0 hψ0 using ex
  have char : ∀ (x : R) (b : V), (∀ n, ∃ P : Polynomial A,
      x - (P.map φ).eval θ ∈ maximalIdeal R ^ n ∧ b - (P.map α).eval η ∈ maximalIdeal V ^ n) →
      ψ0 x = b := by
    intro x b h
    rw [← sub_eq_zero]
    apply haus
    intro n
    obtain ⟨P, h1, h2⟩ := h n
    have := Ideal.sub_mem _ (hψ0 x n P h1) h2
    convert this using 1
    ring
  let ψ : R →+* V :=
    { toFun := ψ0
      map_one' := char 1 1 fun n => ⟨1, by simp, by simp⟩
      map_zero' := char 0 0 fun n => ⟨0, by simp, by simp⟩
      map_add' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px + Py, ?_, ?_⟩
        · have := Ideal.add_mem _ hx hy
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
        · have := Ideal.add_mem _ (hψ0 x n Px hx) (hψ0 y n Py hy)
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
      map_mul' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px * Py, ?_, ?_⟩
        · have := Ideal.add_mem _ (Ideal.mul_mem_right y _ hx)
            (Ideal.mul_mem_left _ ((Px.map φ).eval θ) hy)
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring
        · have := Ideal.add_mem _ (Ideal.mul_mem_right (ψ0 y) _ (hψ0 x n Px hx))
            (Ideal.mul_mem_left _ ((Px.map α).eval η) (hψ0 y n Py hy))
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring }
  refine ⟨ψ, ?_, ⟨fun r hr => ?_⟩⟩
  · ext a
    show ψ0 (φ a) = α a
    exact char _ _ fun n => ⟨Polynomial.C a, by simp, by simp⟩
  · by_contra hnu
    have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 hnu
    obtain ⟨P, hP⟩ := happ 1 r
    rw [pow_one] at hP
    have h1 : (P.map φ).eval θ - ((0 : Polynomial A).map φ).eval θ ∈ maximalIdeal R ^ 1 := by
      simp only [Polynomial.map_zero, Polynomial.eval_zero, sub_zero, pow_one]
      have := Ideal.sub_mem _ hrm hP
      convert this using 1
      ring
    have h2 := key 1 P 0 h1
    have h3 := hψ0 r 1 P (by rw [pow_one]; exact hP)
    have h4 := Ideal.add_mem _ h3 h2
    rw [pow_one] at h4
    have h5 : ψ0 r ∈ maximalIdeal V := by
      convert h4 using 1
      simp
    exact (IsLocalRing.mem_maximalIdeal _).1 h5 hr

end GlobalTheory
