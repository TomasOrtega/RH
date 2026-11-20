import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CrisSec
open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

def T (φ : R →+* R) (x y : Matrix (Fin d) (Fin d) R) (n : ℕ) : Matrix (Fin d) (Fin d) R :=
  Nat.rec 1 (fun _ M => x * M.map φ * y) n

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem T_zero (φ : R →+* R) (x y : Matrix (Fin d) (Fin d) R) : T φ x y 0 = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem T_succ (φ : R →+* R) (x y : Matrix (Fin d) (Fin d) R) (n : ℕ) :
    T φ x y (n + 1) = x * (T φ x y n).map φ * y := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul' (φ : R →+* R) (c : R) (M : Matrix (Fin d) (Fin d) R) : (c • M).map φ = φ c • M.map φ := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_sub' (φ : R →+* R) (M M' : Matrix (Fin d) (Fin d) R) : (M - M').map φ = M.map φ - M'.map φ := by
  ext i j; simp

/- English proof (translation)
Rewrite using `[map_smul', Matrix.map_one _ φ.map_zero φ.map_one]`.
-/
theorem map_one_smul (φ : R →+* R) (c : R) : (c • (1 : Matrix (Fin d) (Fin d) R)).map φ = φ c • 1 := by
  rw [map_smul', Matrix.map_one _ φ.map_zero φ.map_one]

end GlobalTheory.CrisSec

namespace GlobalTheory.CrisSec
variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih => exact hl x (ih _ (by rw [← mul_assoc, ← pow_succ]; exact h))`.
-/
theorem pow_canc {l : ℕ} (hl : ∀ x : R, (l : R) * x = 0 → x = 0) (n : ℕ) (x : R) (h : (l : R) ^ n * x = 0) :
    x = 0 := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih => exact hl x (ih _ (by rw [← mul_assoc, ← pow_succ]; exact h))

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`. Conclude with `sub_eq_zero.1 (pow_canc hl n _ (by rw [mul_sub, this, sub_self]))`.
-/
theorem smul_canc {l : ℕ} (hl : ∀ x : R, (l : R) * x = 0 → x = 0) (n : ℕ) {M M' : Matrix (Fin d) (Fin d) R}
    (h : (l : R) ^ n • M = (l : R) ^ n • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (pow_canc hl n _ (by rw [mul_sub, this, sub_self]))

/- English proof (translation)
Use extensionality with `i k`. Use `hc.haus' _ fun n => ?_` and prove the remaining obligations. Take `⟨Z, hZ⟩` from `h n`. Rewrite using `[SModEq.sub_mem, sub_zero, hZ, Matrix.smul_apply, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem haus {l : ℕ} (hc : IsHausdorff (Ideal.span {(l : R)}) R) {M : Matrix (Fin d) (Fin d) R}
    (h : ∀ j, ∃ Z : Matrix (Fin d) (Fin d) R, M = (l : R) ^ j • Z) : M = 0 := by
  ext i k
  refine hc.haus' _ fun n => ?_
  obtain ⟨Z, hZ⟩ := h n
  rw [SModEq.sub_mem, sub_zero, hZ, Matrix.smul_apply, Ideal.span_singleton_pow, Ideal.smul_eq_mul,
    Ideal.mul_top, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hdet : ∀ z : R, x.det * z = 0 → z = 0` using `fun z hz => by`. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]`. Apply `pow_canc hl (m * d)` to reduce the goal to its premises. Rewrite using `[← h1, mul_comm x.det, mul_assoc, hz, mul_zero]`.

Establish `h0 : x * (y * x - (l : R) ^ m • 1) = 0`. Rewrite using `[mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, sub_self]`. Establish `h2 : x.det • (y * x - (l : R) ^ m • 1) = 0`. Rewrite using `[← Matrix.one_mul (y * x - _), ← smul_mul_assoc, ← Matrix.adjugate_mul, Matrix.mul_assoc, h0, Matrix.mul_zero]`. Rewrite using `[← sub_eq_zero]`.

Use extensionality with `i j`. Use `congrFun (congrFun h2 i) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this ⊢`. Conclude with `hdet _ this`.
-/
theorem comm_of_mul {l : ℕ} (hl : ∀ x : R, (l : R) * x = 0 → x = 0) (m : ℕ) {x y : Matrix (Fin d) (Fin d) R}
    (h : x * y = (l : R) ^ m • 1) : y * x = (l : R) ^ m • 1 := by
  have hdet : ∀ z : R, x.det * z = 0 → z = 0 := fun z hz => by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul] at h1
    apply pow_canc hl (m * d)
    rw [← h1, mul_comm x.det, mul_assoc, hz, mul_zero]
  have h0 : x * (y * x - (l : R) ^ m • 1) = 0 := by
    rw [mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, sub_self]
  have h2 : x.det • (y * x - (l : R) ^ m • 1) = 0 := by
    rw [← Matrix.one_mul (y * x - _), ← smul_mul_assoc, ← Matrix.adjugate_mul, Matrix.mul_assoc, h0,
      Matrix.mul_zero]
  rw [← sub_eq_zero]; ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this ⊢
  exact hdet _ this

/- English proof (translation)
Use `set D : R := (l : R) ^ (2 * N) with hD`. Establish `hφD : φ D = D` using `by simp [hD]`. Establish `hφl : φ (l : R) = l` using `map_natCast φ l`. Establish `p1 : ∀ n, ∃ G, (l : R) • (T φ x y (n + 1) - D • T φ x y n) = u ^ (q ^ (n + 1)) • G`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Use `⟨Γ, ?_⟩` and prove the remaining obligations. Rewrite using `[T_succ, T_zero, Matrix.map_one _ φ.map_zero φ.map_one, Matrix.mul_one, hΓ, zero_add, pow_one]`. Consider the case `succ n ih`.

Take `⟨G, hG⟩` from `ih`. Use `⟨x * G.map φ * y, ?_⟩` and prove the remaining obligations. Establish `e : (l : R) • (T φ x y (n + 1 + 1) - D • T φ x y (n + 1)) = x * ((l : R) • (T φ x y (n + 1) - D • T φ x y n)).map φ * y`. Rewrite using `[T_succ, T_succ φ x y n, map_smul', map_sub', map_smul', hφl, hφD]`. Simplify using `only [smul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]`.

Rewrite using `[e, hG, map_smul', map_pow, hu, Matrix.mul_smul, Matrix.smul_mul, ← pow_mul, pow_succ q (n + 1), mul_comm q]`. Use `⟨p1 n, ?_⟩` and prove the remaining obligations. Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`.

Take `⟨Y, hY⟩` from `ih`. Take `⟨G, hG⟩` from `p1 n`. Use `⟨((l : R) ^ n * u ^ (q ^ (n + 1) - 1)) • G + ((l : R) * D) • Y, ?_⟩` and prove the remaining obligations. Establish `e : (l : R) ^ (n + 1) • (T φ x y (n + 1) - D ^ (n + 1) • 1) = (l : R) ^ n • ((l : R) • (T φ x y (n + 1) - D • T φ x y n)) + ((l : R) * D) • ((l : R) ^ n • (T φ x y n - D ^ n • 1))` using `by module`. Establish `hu1 : u ^ (q ^ (n + 1)) = u * u ^ (q ^ (n + 1) - 1)`.

Rewrite using `[← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)]`. Rewrite using `[e, hG, hY, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, hu1]`. Apply the tactic sequence `congr 1 <;> congr 1 <;> ring`.
-/
theorem tseq (l q N : ℕ) (φ : R →+* R) (u : R) (hu : φ u = u ^ q) (hq : 0 < q) (x y Γ : Matrix (Fin d) (Fin d) R)
    (hΓ : (l : R) • (x * y - ((l : R) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) R)) = u ^ q • Γ) (n : ℕ) :
    (∃ G, (l : R) • (T φ x y (n + 1) - (l : R) ^ (2 * N) • T φ x y n) = u ^ (q ^ (n + 1)) • G) ∧
    ∃ Y, (l : R) ^ n • (T φ x y n - ((l : R) ^ (2 * N)) ^ n • (1 : Matrix (Fin d) (Fin d) R)) = u • Y := by
  set D : R := (l : R) ^ (2 * N) with hD
  have hφD : φ D = D := by simp [hD]
  have hφl : φ (l : R) = l := map_natCast φ l
  have p1 : ∀ n, ∃ G, (l : R) • (T φ x y (n + 1) - D • T φ x y n) = u ^ (q ^ (n + 1)) • G := by
    intro n
    induction n with
    | zero =>
      refine ⟨Γ, ?_⟩
      rw [T_succ, T_zero, Matrix.map_one _ φ.map_zero φ.map_one, Matrix.mul_one, hΓ, zero_add, pow_one]
    | succ n ih =>
      obtain ⟨G, hG⟩ := ih
      refine ⟨x * G.map φ * y, ?_⟩
      have e : (l : R) • (T φ x y (n + 1 + 1) - D • T φ x y (n + 1)) =
          x * ((l : R) • (T φ x y (n + 1) - D • T φ x y n)).map φ * y := by
        rw [T_succ, T_succ φ x y n, map_smul', map_sub', map_smul', hφl, hφD]
        simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rw [e, hG, map_smul', map_pow, hu, Matrix.mul_smul, Matrix.smul_mul, ← pow_mul, pow_succ q (n + 1), mul_comm q]
  refine ⟨p1 n, ?_⟩
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    obtain ⟨G, hG⟩ := p1 n
    refine ⟨((l : R) ^ n * u ^ (q ^ (n + 1) - 1)) • G + ((l : R) * D) • Y, ?_⟩
    have e : (l : R) ^ (n + 1) • (T φ x y (n + 1) - D ^ (n + 1) • 1) =
        (l : R) ^ n • ((l : R) • (T φ x y (n + 1) - D • T φ x y n)) +
          ((l : R) * D) • ((l : R) ^ n • (T φ x y n - D ^ n • 1)) := by
      module
    have hu1 : u ^ (q ^ (n + 1)) = u * u ^ (q ^ (n + 1) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)]
    rw [e, hG, hY, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, hu1]
    congr 1 <;> congr 1 <;> ring

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]`.
-/
theorem smod_iff (l n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {(l : R)}) ^ n • (⊤ : Submodule R R)] ↔ (l : R) ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

/- English proof (translation)
Establish `hent : ∀ i k, ∃ L : R, ∀ n, (l : R) ^ n ∣ L - Y n i k`. Introduce `i k`. Establish `hC : ∀ m n, m ≤ n → (l : R) ^ m ∣ Y n i k - Y m i k`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Take `⟨Z, hZ⟩` from `hY n`. Establish `e : Y (n + 1) i k - Y m i k = (l : R) ^ n * Z i k + (Y n i k - Y m i k)`. Use `congrFun (congrFun hZ i) k` as an intermediate fact.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow _ hmn) _) ih`.

Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec' (fun n => Y n i k) (fun {m n} hmn => by`. Rewrite using `[smod_iff]`. Use `hC m n hmn` as an intermediate fact. Rewrite using `[← neg_sub]`. Conclude with `this.neg_right)`.

Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Use `(smod_iff l n _ _).1 (hL n)` as an intermediate fact. Rewrite using `[← neg_sub]`. Conclude with `this.neg_right`. Use `choose L hL using hent`.

Use `⟨Matrix.of L, fun j => ?_⟩` and prove the remaining obligations. Use `choose Z hZ using fun i k => hL i k j`. Conclude with `⟨Matrix.of Z, by ext i k; simp [hZ]⟩`.
-/
theorem lim {l : ℕ} (hc : IsAdicComplete (Ideal.span {(l : R)}) R) (Y : ℕ → Matrix (Fin d) (Fin d) R)
    (hY : ∀ j, ∃ Z, Y (j + 1) - Y j = (l : R) ^ j • Z) : ∃ L, ∀ j, ∃ Z, L - Y j = (l : R) ^ j • Z := by
  have hent : ∀ i k, ∃ L : R, ∀ n, (l : R) ^ n ∣ L - Y n i k := by
    intro i k
    have hC : ∀ m n, m ≤ n → (l : R) ^ m ∣ Y n i k - Y m i k := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        obtain ⟨Z, hZ⟩ := hY n
        have e : Y (n + 1) i k - Y m i k = (l : R) ^ n * Z i k + (Y n i k - Y m i k) := by
          have := congrFun (congrFun hZ i) k
          simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
          rw [← this]; ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow _ hmn) _) ih
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' (fun n => Y n i k) (fun {m n} hmn => by
      rw [smod_iff]
      have := hC m n hmn
      rw [← neg_sub]; exact this.neg_right)
    refine ⟨L, fun n => ?_⟩
    have := (smod_iff l n _ _).1 (hL n)
    rw [← neg_sub]; exact this.neg_right
  choose L hL using hent
  refine ⟨Matrix.of L, fun j => ?_⟩
  choose Z hZ using fun i k => hL i k j
  exact ⟨Matrix.of Z, by ext i k; simp [hZ]⟩

/- English proof (translation)
Use `choose H hH using h`. Use `set D : R := (l : R) ^ (2 * N) with hD`. Take `⟨Z, hZ⟩ : ∃ Z : ℕ → Matrix (Fin d) (Fin d) R, Z = fun i => (D ^ n₀ * (l : R) ^ (n₀ + 1)) • H (n₀ + i) (Nat.le_add_right _ _)` from `⟨_, rfl⟩`. Take `⟨Ys, hYsd⟩ : ∃ Ys : ℕ → Matrix (Fin d) (Fin d) R, Ys = fun j => ∑ i ∈ Finset.range j, (l : R) ^ i • Z i` from `⟨_, rfl⟩`. Establish `hYs : ∀ j, Ys (j + 1) - Ys j = (l : R) ^ j • Z j` using `fun j => by`.

Rewrite using `[hYsd]`. Simplify using `only [Finset.sum_range_succ]`. Normalize the expressions using the abelian group laws. Establish `hYs0 : Ys 0 = 0` using `by rw [hYsd]; simp`. Take `⟨L, hL⟩` from `lim hc Ys (fun j => ⟨Z j, hYs j⟩)`.

Use `⟨T n₀ + u • L, fun j => T n₀ + u • Ys j, ?_, fun j => ?_, ⟨L, by simp [hYs0]⟩⟩` and prove the remaining obligations. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp [hYs0]`. Consider the case `succ j ih`.

Simplify using `only at ih ⊢`. Establish `e : T n₀ + u • Ys (j + 1) = (T n₀ + u • Ys j) + (u * (l : R) ^ j) • Z j`. Use `hYs j` as an intermediate fact. Rewrite `this` using `[sub_eq_iff_eq_add]`. Rewrite using `[this, smul_add, smul_smul]`.

Normalize the expressions using the abelian group laws. Establish `hH'` using `hH (n₀ + j) (Nat.le_add_right _ _)`. Rewrite `hH'` using `[sub_eq_iff_eq_add']`. Use `show D ^ (j + 1) • (T n₀ + u • Ys (j + 1)) = T (n₀ + j + 1)`. Rewrite using `[e, smul_add, pow_succ', ← smul_smul, ih, hH', hZ]`.

Use `congr 1`. Simplify using `only [smul_smul]`. Use `congr 1`. Rewrite using `[hD]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨W, hW⟩` from `hL j`. Conclude with `⟨u • W, by rw [add_sub_add_left_eq_sub, ← smul_sub, hW, smul_comm]⟩`.
-/
theorem shift {l : ℕ} (hl : ∀ x : R, (l : R) * x = 0 → x = 0) (hc : IsAdicComplete (Ideal.span {(l : R)}) R)
    (N n₀ : ℕ) (u : R) (T : ℕ → Matrix (Fin d) (Fin d) R)
    (h : ∀ n, n₀ ≤ n → ∃ H, T (n + 1) - (l : R) ^ (2 * N) • T n = ((l : R) ^ ((2 * N + 1) * (n + 1)) * u) • H) :
    ∃ (S : Matrix (Fin d) (Fin d) R) (Sf : ℕ → Matrix (Fin d) (Fin d) R),
      (∀ j, ((l : R) ^ (2 * N)) ^ j • Sf j = T (n₀ + j)) ∧ (∀ j, ∃ Z, S - Sf j = (l : R) ^ j • Z) ∧
      ∃ Y, S - Sf 0 = u • Y := by
  choose H hH using h
  set D : R := (l : R) ^ (2 * N) with hD
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Matrix (Fin d) (Fin d) R,
      Z = fun i => (D ^ n₀ * (l : R) ^ (n₀ + 1)) • H (n₀ + i) (Nat.le_add_right _ _) := ⟨_, rfl⟩
  obtain ⟨Ys, hYsd⟩ : ∃ Ys : ℕ → Matrix (Fin d) (Fin d) R,
      Ys = fun j => ∑ i ∈ Finset.range j, (l : R) ^ i • Z i := ⟨_, rfl⟩
  have hYs : ∀ j, Ys (j + 1) - Ys j = (l : R) ^ j • Z j := fun j => by
    rw [hYsd]; simp only [Finset.sum_range_succ]; abel
  have hYs0 : Ys 0 = 0 := by rw [hYsd]; simp
  obtain ⟨L, hL⟩ := lim hc Ys (fun j => ⟨Z j, hYs j⟩)
  refine ⟨T n₀ + u • L, fun j => T n₀ + u • Ys j, ?_, fun j => ?_, ⟨L, by simp [hYs0]⟩⟩
  · intro j
    induction j with
    | zero => simp [hYs0]
    | succ j ih =>
      simp only at ih ⊢
      have e : T n₀ + u • Ys (j + 1) = (T n₀ + u • Ys j) + (u * (l : R) ^ j) • Z j := by
        have := hYs j
        rw [sub_eq_iff_eq_add] at this
        rw [this, smul_add, smul_smul]; abel
      have hH' := hH (n₀ + j) (Nat.le_add_right _ _)
      rw [sub_eq_iff_eq_add'] at hH'
      show D ^ (j + 1) • (T n₀ + u • Ys (j + 1)) = T (n₀ + j + 1)
      rw [e, smul_add, pow_succ', ← smul_smul, ih, hH', hZ]
      congr 1
      simp only [smul_smul]
      congr 1
      rw [hD]; ring
  · obtain ⟨W, hW⟩ := hL j
    exact ⟨u • W, by rw [add_sub_add_left_eq_sub, ← smul_sub, hW, smul_comm]⟩

/- English proof (translation)
Use `set D : R := (l : R) ^ (2 * N) with hDdef`. Establish `hα' : α' * α = D • 1` using `comm_of_mul hl _ hα`. Establish `hβ' : β' * β = D • 1` using `comm_of_mul hl _ hβ`. Establish `hφl : ∀ m : ℕ, φ ((l : R) ^ m) = (l : R) ^ m` using `fun m => by simp`. Establish `hφD : φ D = D` using `hφl _`.

Establish `hΓ1 : (l : R) • (α * β' - D • 1) = u ^ q • (Γ * β')`. Rewrite using `[← hβ, ← Matrix.sub_mul, ← smul_mul_assoc, hΓ, smul_mul_assoc]`. Establish `hΓ2 : (l : R) • (β * α' - D • 1) = u ^ q • (-Γ * α')`. Establish `e : β * α' - D • 1 = -((α - β) * α')` using `by rw [← hα, Matrix.sub_mul]; abel`. Rewrite using `[e, smul_neg, ← smul_mul_assoc, hΓ, smul_mul_assoc, Matrix.neg_mul, smul_neg]`.

Establish `step : ∀ (x y G0 : Matrix (Fin d) (Fin d) R), (l : R) • (x * y - D • 1) = u ^ q • G0 → ∀ n, n₀ ≤ n → ∃ H, T φ x y (n + 1) - (l : R) ^ (2 * N) • T φ x y n = ((l : R) ^ ((2 * N + 1) * (n + 1)) * u) • H`. Introduce `x y G0 hG n hn`. Take `⟨⟨G, hG'⟩, -⟩` from `tseq l q N φ u hu hq x y G0 hG n`. Take `⟨w, hw⟩` from `hn₀ n hn`. Use `⟨w • G, smul_canc hl 1 ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_one, hG', smul_smul, smul_smul]`. Use `congr 1`. Establish `e : u ^ (q ^ (n + 1)) = u * u ^ (q ^ (n + 1) - 1)`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)]`. Rewrite using `[e, hw]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨S, Sf, hS, hSl, hS0⟩` from `shift hl hc N n₀ u (T φ α β') (step α β' _ hΓ1)`. Take `⟨S', Sf', hS', hSl', hS0'⟩` from `shift hl hc N n₀ u (T φ β α') (step β α' _ hΓ2)`. Establish `hTT : ∀ n, T φ α β' n * T φ β α' n = (D ^ (2 * n)) • (1 : Matrix (Fin d) (Fin d) R)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[T_succ, T_succ]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = D • (α * (T φ α β' n * T φ β α' n).map φ * α') := by`. Rewrite using `[hβ', Matrix.map_mul]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Use `_ = _ := by`.

Rewrite using `[ih, map_one_smul, map_pow, hφD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hα]`. Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hTf : ∀ (x y x' : Matrix (Fin d) (Fin d) R), y * x' = D • 1 → ∀ n, T φ x y (n + 1) * x' = D • (x * (T φ x y n).map φ)`.

Introduce `x y x' h n`. Rewrite using `[T_succ, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]`. Establish `hSf : ∀ (x y x' : Matrix (Fin d) (Fin d) R) (Sf : ℕ → Matrix (Fin d) (Fin d) R), y * x' = D • 1 → (∀ j, D ^ j • Sf j = T φ x y (n₀ + j)) → ∀ j, Sf (j + 1) * x' = x * (Sf j).map φ`. Introduce `x y x' Sf h hS j`. Apply `smul_canc hl (2 * N * (j + 1))` to reduce the goal to its premises.

Rewrite using `[pow_mul, ← smul_mul_assoc, hS (j + 1), ← add_assoc, hTf x y x' h, ← hS j, map_smul', map_pow, hφD, Matrix.mul_smul, smul_smul, pow_succ']`. Establish `hlim : ∀ (x x' : Matrix (Fin d) (Fin d) R) (Sf : ℕ → Matrix (Fin d) (Fin d) R) (S : Matrix (Fin d) (Fin d) R), (∀ j, Sf (j + 1) * x' = x * (Sf j).map φ) → (∀ j, ∃ Z, S - Sf j = (l : R) ^ j • Z) → S * x' = x * S.map φ`. Introduce `x x' Sf S h hSl`. Rewrite using `[← sub_eq_zero]`. Apply `haus hc.toIsHausdorff` to reduce the goal to its premises.

Introduce `j`. Take `⟨Z1, hZ1⟩` from `hSl (j + 1)`. Take `⟨Z2, hZ2⟩` from `hSl j`. Use `⟨((l : R) • Z1) * x' - x * Z2.map φ, ?_⟩` and prove the remaining obligations. Establish `e : S * x' - x * S.map φ = (S - Sf (j + 1)) * x' - x * (S - Sf j).map φ + (Sf (j + 1) * x' - x * (Sf j).map φ)`.

Rewrite using `[map_sub']`. Use `noncomm_ring`. Rewrite using `[e, h j, sub_self, add_zero, hZ1, hZ2, map_smul', hφl, pow_succ]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]`. Establish `hQ` using `hlim α β Sf S (hSf α β' β Sf hβ' hS) hSl`.

Establish `hQ'` using `hlim β α Sf' S' (hSf β α' α Sf' hα' hS') hSl'`. Establish `hSS : ∀ j, Sf j * Sf' j = (D ^ (2 * n₀)) • 1`. Introduce `j`. Apply `smul_canc hl (2 * N * (2 * j))` to reduce the goal to its premises. Establish `h1 : (D ^ j • Sf j) * (D ^ j • Sf' j) = D ^ (2 * (n₀ + j)) • 1` using `by rw [hS, hS', hTT]`.

Rewrite `h1` using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Rewrite using `[pow_mul, smul_smul, show D ^ (2 * j) * D ^ (2 * n₀) = D ^ (2 * (n₀ + j)) by ring, ← h1]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hSS' : S * S' = (D ^ (2 * n₀)) • 1`.

Rewrite using `[← sub_eq_zero]`. Apply `haus hc.toIsHausdorff` to reduce the goal to its premises. Introduce `j`. Take `⟨Z1, hZ1⟩` from `hSl j`. Take `⟨Z2, hZ2⟩` from `hSl' j`.

Use `⟨Z1 * S' + Sf j * Z2, ?_⟩` and prove the remaining obligations. Establish `e : S * S' - D ^ (2 * n₀) • 1 = (S - Sf j) * S' + Sf j * (S' - Sf' j) + (Sf j * Sf' j - D ^ (2 * n₀) • 1)` using `by noncomm_ring`. Rewrite using `[e, hSS j, sub_self, add_zero, hZ1, hZ2, Matrix.smul_mul, Matrix.mul_smul, smul_add]`. Establish `hk : (l : R) ^ (n₀ + 2 * N * n₀) = (l : R) ^ n₀ * D ^ n₀` using `by rw [hDdef, ← pow_mul, ← pow_add]`. Establish `hT0 : Sf 0 = T φ α β' n₀` using `by simpa using hS 0`.

Establish `hT0' : Sf' 0 = T φ β α' n₀` using `by simpa using hS' 0`. Use `⟨n₀ + 2 * N * n₀, (l : R) ^ n₀ • S, (l : R) ^ n₀ • S', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hSS', smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[hDdef]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨Y1, hY1⟩` from `hS0`. Take `⟨-, Y2, hY2⟩` from `tseq l q N φ u hu hq α β' _ hΓ1 n₀`. Use `⟨(l : R) ^ n₀ • Y1 + Y2, ?_⟩` and prove the remaining obligations. Establish `e : (l : R) ^ n₀ • S - ((l : R) ^ n₀ * D ^ n₀) • 1 = (l : R) ^ n₀ • (S - Sf 0) + (l : R) ^ n₀ • (T φ α β' n₀ - D ^ n₀ • 1)`.

Rewrite using `[hT0, ← smul_add, sub_add_sub_cancel, smul_sub, smul_smul]`. Rewrite using `[hk, e, hY1, hY2, smul_add, smul_comm]`. Take `⟨Y1, hY1⟩` from `hS0'`. Take `⟨-, Y2, hY2⟩` from `tseq l q N φ u hu hq β α' _ hΓ2 n₀`. Use `⟨(l : R) ^ n₀ • Y1 + Y2, ?_⟩` and prove the remaining obligations.

Establish `e : (l : R) ^ n₀ • S' - ((l : R) ^ n₀ * D ^ n₀) • 1 = (l : R) ^ n₀ • (S' - Sf' 0) + (l : R) ^ n₀ • (T φ β α' n₀ - D ^ n₀ • 1)`. Rewrite using `[hT0', ← smul_add, sub_add_sub_cancel, smul_sub, smul_smul]`. Rewrite using `[hk, e, hY1, hY2, smul_add, smul_comm]`. Rewrite using `[Matrix.smul_mul, hQ, map_smul', hφl, Matrix.mul_smul]`.
-/
theorem core (l q N : ℕ) (hl : ∀ x : R, (l : R) * x = 0 → x = 0) (hc : IsAdicComplete (Ideal.span {(l : R)}) R)
    (φ : R →+* R) (u : R) (hu : φ u = u ^ q) (hq : 0 < q) (α α' β β' Γ : Matrix (Fin d) (Fin d) R)
    (hα : α * α' = ((l : R) ^ (2 * N)) • 1) (hβ : β * β' = ((l : R) ^ (2 * N)) • 1)
    (hΓ : (l : R) • (α - β) = u ^ q • Γ) (n₀ : ℕ)
    (hn₀ : ∀ n, n₀ ≤ n → (l : R) ^ ((2 * N + 1) * (n + 1) + 1) ∣ u ^ (q ^ (n + 1) - 1)) :
    ∃ (k : ℕ) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = (l : R) ^ (2 * k) • 1 ∧
      (∃ Y, Q - (l : R) ^ k • 1 = u • Y) ∧ (∃ Y, Q' - (l : R) ^ k • 1 = u • Y) ∧ Q * β = α * Q.map φ := by
  set D : R := (l : R) ^ (2 * N) with hDdef
  have hα' : α' * α = D • 1 := comm_of_mul hl _ hα
  have hβ' : β' * β = D • 1 := comm_of_mul hl _ hβ
  have hφl : ∀ m : ℕ, φ ((l : R) ^ m) = (l : R) ^ m := fun m => by simp
  have hφD : φ D = D := hφl _
  have hΓ1 : (l : R) • (α * β' - D • 1) = u ^ q • (Γ * β') := by
    rw [← hβ, ← Matrix.sub_mul, ← smul_mul_assoc, hΓ, smul_mul_assoc]
  have hΓ2 : (l : R) • (β * α' - D • 1) = u ^ q • (-Γ * α') := by
    have e : β * α' - D • 1 = -((α - β) * α') := by rw [← hα, Matrix.sub_mul]; abel
    rw [e, smul_neg, ← smul_mul_assoc, hΓ, smul_mul_assoc, Matrix.neg_mul, smul_neg]
  have step : ∀ (x y G0 : Matrix (Fin d) (Fin d) R), (l : R) • (x * y - D • 1) = u ^ q • G0 →
      ∀ n, n₀ ≤ n → ∃ H, T φ x y (n + 1) - (l : R) ^ (2 * N) • T φ x y n =
        ((l : R) ^ ((2 * N + 1) * (n + 1)) * u) • H := by
    intro x y G0 hG n hn
    obtain ⟨⟨G, hG'⟩, -⟩ := tseq l q N φ u hu hq x y G0 hG n
    obtain ⟨w, hw⟩ := hn₀ n hn
    refine ⟨w • G, smul_canc hl 1 ?_⟩
    rw [pow_one, hG', smul_smul, smul_smul]
    congr 1
    have e : u ^ (q ^ (n + 1)) = u * u ^ (q ^ (n + 1) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)]
    rw [e, hw]; ring
  obtain ⟨S, Sf, hS, hSl, hS0⟩ := shift hl hc N n₀ u (T φ α β') (step α β' _ hΓ1)
  obtain ⟨S', Sf', hS', hSl', hS0'⟩ := shift hl hc N n₀ u (T φ β α') (step β α' _ hΓ2)
  have hTT : ∀ n, T φ α β' n * T φ β α' n = (D ^ (2 * n)) • (1 : Matrix (Fin d) (Fin d) R) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [T_succ, T_succ]
      calc α * (T φ α β' n).map φ * β' * (β * (T φ β α' n).map φ * α')
          = α * ((T φ α β' n).map φ * (β' * β) * (T φ β α' n).map φ) * α' := by
            simp only [Matrix.mul_assoc]
        _ = D • (α * (T φ α β' n * T φ β α' n).map φ * α') := by
          rw [hβ', Matrix.map_mul]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
        _ = _ := by
          rw [ih, map_one_smul, map_pow, hφD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hα]
          simp only [smul_smul]
          congr 1; ring
  have hTf : ∀ (x y x' : Matrix (Fin d) (Fin d) R), y * x' = D • 1 → ∀ n,
      T φ x y (n + 1) * x' = D • (x * (T φ x y n).map φ) := by
    intro x y x' h n
    rw [T_succ, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]
  have hSf : ∀ (x y x' : Matrix (Fin d) (Fin d) R) (Sf : ℕ → Matrix (Fin d) (Fin d) R), y * x' = D • 1 →
      (∀ j, D ^ j • Sf j = T φ x y (n₀ + j)) → ∀ j, Sf (j + 1) * x' = x * (Sf j).map φ := by
    intro x y x' Sf h hS j
    apply smul_canc hl (2 * N * (j + 1))
    rw [pow_mul, ← smul_mul_assoc, hS (j + 1), ← add_assoc, hTf x y x' h, ← hS j, map_smul', map_pow, hφD,
      Matrix.mul_smul, smul_smul, pow_succ']
  have hlim : ∀ (x x' : Matrix (Fin d) (Fin d) R) (Sf : ℕ → Matrix (Fin d) (Fin d) R) (S : Matrix (Fin d) (Fin d) R),
      (∀ j, Sf (j + 1) * x' = x * (Sf j).map φ) → (∀ j, ∃ Z, S - Sf j = (l : R) ^ j • Z) →
      S * x' = x * S.map φ := by
    intro x x' Sf S h hSl
    rw [← sub_eq_zero]
    apply haus hc.toIsHausdorff
    intro j
    obtain ⟨Z1, hZ1⟩ := hSl (j + 1)
    obtain ⟨Z2, hZ2⟩ := hSl j
    refine ⟨((l : R) • Z1) * x' - x * Z2.map φ, ?_⟩
    have e : S * x' - x * S.map φ = (S - Sf (j + 1)) * x' - x * (S - Sf j).map φ +
        (Sf (j + 1) * x' - x * (Sf j).map φ) := by
      rw [map_sub']; noncomm_ring
    rw [e, h j, sub_self, add_zero, hZ1, hZ2, map_smul', hφl, pow_succ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
  have hQ := hlim α β Sf S (hSf α β' β Sf hβ' hS) hSl
  have hQ' := hlim β α Sf' S' (hSf β α' α Sf' hα' hS') hSl'
  have hSS : ∀ j, Sf j * Sf' j = (D ^ (2 * n₀)) • 1 := by
    intro j
    apply smul_canc hl (2 * N * (2 * j))
    have h1 : (D ^ j • Sf j) * (D ^ j • Sf' j) = D ^ (2 * (n₀ + j)) • 1 := by rw [hS, hS', hTT]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h1
    rw [pow_mul, smul_smul, show D ^ (2 * j) * D ^ (2 * n₀) = D ^ (2 * (n₀ + j)) by ring, ← h1]
    congr 1; ring
  have hSS' : S * S' = (D ^ (2 * n₀)) • 1 := by
    rw [← sub_eq_zero]
    apply haus hc.toIsHausdorff
    intro j
    obtain ⟨Z1, hZ1⟩ := hSl j
    obtain ⟨Z2, hZ2⟩ := hSl' j
    refine ⟨Z1 * S' + Sf j * Z2, ?_⟩
    have e : S * S' - D ^ (2 * n₀) • 1 = (S - Sf j) * S' + Sf j * (S' - Sf' j) + (Sf j * Sf' j - D ^ (2 * n₀) • 1) := by
      noncomm_ring
    rw [e, hSS j, sub_self, add_zero, hZ1, hZ2, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  have hk : (l : R) ^ (n₀ + 2 * N * n₀) = (l : R) ^ n₀ * D ^ n₀ := by rw [hDdef, ← pow_mul, ← pow_add]
  have hT0 : Sf 0 = T φ α β' n₀ := by simpa using hS 0
  have hT0' : Sf' 0 = T φ β α' n₀ := by simpa using hS' 0
  refine ⟨n₀ + 2 * N * n₀, (l : R) ^ n₀ • S, (l : R) ^ n₀ • S', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hSS', smul_smul, smul_smul]
    congr 1; rw [hDdef]; ring
  · obtain ⟨Y1, hY1⟩ := hS0
    obtain ⟨-, Y2, hY2⟩ := tseq l q N φ u hu hq α β' _ hΓ1 n₀
    refine ⟨(l : R) ^ n₀ • Y1 + Y2, ?_⟩
    have e : (l : R) ^ n₀ • S - ((l : R) ^ n₀ * D ^ n₀) • 1 =
        (l : R) ^ n₀ • (S - Sf 0) + (l : R) ^ n₀ • (T φ α β' n₀ - D ^ n₀ • 1) := by
      rw [hT0, ← smul_add, sub_add_sub_cancel, smul_sub, smul_smul]
    rw [hk, e, hY1, hY2, smul_add, smul_comm]
  · obtain ⟨Y1, hY1⟩ := hS0'
    obtain ⟨-, Y2, hY2⟩ := tseq l q N φ u hu hq β α' _ hΓ2 n₀
    refine ⟨(l : R) ^ n₀ • Y1 + Y2, ?_⟩
    have e : (l : R) ^ n₀ • S' - ((l : R) ^ n₀ * D ^ n₀) • 1 =
        (l : R) ^ n₀ • (S' - Sf' 0) + (l : R) ^ n₀ • (T φ β α' n₀ - D ^ n₀ • 1) := by
      rw [hT0', ← smul_add, sub_add_sub_cancel, smul_sub, smul_smul]
    rw [hk, e, hY1, hY2, smul_add, smul_comm]
  · rw [Matrix.smul_mul, hQ, map_smul', hφl, Matrix.mul_smul]

end GlobalTheory.CrisSec

open GlobalTheory.CrisSec in

/- English proof (translation)
Introduce `l _ K bk N d A A' hA`. Use `set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ`. Take `⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩` from `GlobalTheory.AcrisFrobE.main l K bk`. Establish `hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s)` using `fun s => by`. Simplify using `only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]`.

Establish `hu : phiA l (ψ X) = ψ X ^ l` using `by rw [hφψ, frobS_X, map_pow]`. Establish `hdiff : ∀ s : bk.S, ∃ t : Per.Acris l, ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t`. Introduce `s`. Take `⟨t, ht⟩` from `(PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)`. Use `⟨ψ (frobS l bk.a t), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]`. Take `⟨w, hw⟩` from `bk.coeff_zero`. Establish `hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0` using `by simp`. Use `set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def`. Establish `hw0u : IsUnit w0` using `((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ`.

Establish `hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0`. Rewrite using `[hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]`. Use `set u : Per.Acris l := ψ X with hudef`. Use `set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef`. Use `set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef`.

Use `set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef`. Establish `hav : a * v = 1` using `Units.inv_mul v`. Establish `hbw : b * w0 = 1` using `by rw [hbdef]; exact hw0u.val_inv_mul`. Use `set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB`. Use `set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0`.

Establish `hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))`. Introduce `f`. Rewrite using `[← Matrix.map_mul, hA]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.

Establish `hfE : fB bk.E = (l : Per.Acris l) * v` using `hv`. Establish `hfE0 : fB0 bk.E = (l : Per.Acris l) * w0` using `hP0`. Establish `hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N)`. Introduce `c y h`. Combine the equalities or inequalities in the displayed calculation.

Establish `hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1`. Rewrite using `[smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]`. Establish `hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1`. Rewrite using `[smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]`. Use `choose G hG using fun i j => hdiff (A i j)`.

Take `⟨z, hz⟩` from `hdiff bk.E`. Take `⟨t, ht⟩` from `sub_dvd_pow_sub_pow w0 v N`. Establish `hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) = u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0)`. Use extensionality with `i j`. Establish `h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j` using `hG i j`.

Establish `h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z` using `by rw [← hfE, ← hfE0]; exact hz`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]`. Establish `h4 : (a * v) ^ N = 1` using `by rw [hav, one_pow]`. Establish `h5 : (b * w0) ^ N = 1` using `by rw [hbw, one_pow]`. Take the linear combination `((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 + ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 + (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5`.

Take `⟨n₀, hn₀⟩` from `GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1`. Take `⟨k, Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩` from `GlobalTheory.CrisSec.core l l N htor hcomp (phiA l) u hu (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))`. Use `⟨k, Q, Q', hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hY]`. Both sides reduce to the same expression.

Rewrite using `[hY']`. Both sides reduce to the same expression. Establish `key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l))`. Rewrite using `[← mul_smul_comm, hQ, smul_mul_assoc]`. Establish `e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N`.

Rewrite using `[mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]`. Establish `e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N`. Rewrite using `[hv]`. Combine the equalities or inequalities in the displayed calculation. Use `show P ^ N • (Q * A.map fB0) = ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))`.

Rewrite using `[hP0, e1, ← smul_smul, key, smul_smul, e2]`.
-/
theorem GlobalTheory.CrisSec.phiSection : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → ∃ (k : ℕ) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) ^ N • (Q * (A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))))) = ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • ((A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a s)) * Q.map (phiA l)) := by
  intro l _ K bk N d A A' hA
  set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ
  obtain ⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩ := GlobalTheory.AcrisFrobE.main l K bk
  have hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s) := fun s => by
    simp only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]
  have hu : phiA l (ψ X) = ψ X ^ l := by rw [hφψ, frobS_X, map_pow]

  have hdiff : ∀ s : bk.S, ∃ t : Per.Acris l,
      ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t := by
    intro s
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    refine ⟨ψ (frobS l bk.a t), ?_⟩
    rw [← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0 := by simp
  set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def
  have hw0u : IsUnit w0 := ((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ
  have hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0 := by
    rw [hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]
  set u : Per.Acris l := ψ X with hudef
  set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef
  set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef
  set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef
  have hav : a * v = 1 := Units.inv_mul v
  have hbw : b * w0 = 1 := by rw [hbdef]; exact hw0u.val_inv_mul
  set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB
  set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0
  have hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    intro f
    rw [← Matrix.map_mul, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfE : fB bk.E = (l : Per.Acris l) * v := hv
  have hfE0 : fB0 bk.E = (l : Per.Acris l) * w0 := hP0
  have hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) := by
    intro c y h
    calc c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) * (c * y) ^ (2 * N) := by ring
      _ = _ := by rw [h, one_pow, mul_one]
  have hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]
  have hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]
  choose G hG using fun i j => hdiff (A i j)
  obtain ⟨z, hz⟩ := hdiff bk.E
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow w0 v N
  have hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) =
      u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0) := by
    ext i j
    have h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j := hG i j
    have h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z := by rw [← hfE, ← hfE0]; exact hz
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    have h4 : (a * v) ^ N = 1 := by rw [hav, one_pow]
    have h5 : (b * w0) ^ N = 1 := by rw [hbw, one_pow]
    linear_combination ((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 +
      ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 +
      (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1
  obtain ⟨k, Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩ := GlobalTheory.CrisSec.core l l N htor hcomp (phiA l) u hu
    (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))
  refine ⟨k, Q, Q', hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩
  · rw [hY]; rfl
  · rw [hY']; rfl
  · have key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l)) := by
      rw [← mul_smul_comm, hQ, smul_mul_assoc]
    have e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N := by
      rw [mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]
    have e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N := by
      rw [hv]
      calc ((l : Per.Acris l) * v) ^ N * w0 ^ N * a ^ N = ((l : Per.Acris l) * w0) ^ N * (a * v) ^ N := by ring
        _ = _ := by rw [hav, one_pow, mul_one]
    show P ^ N • (Q * A.map fB0) =
      ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))
    rw [hP0, e1, ← smul_smul, key, smul_smul, e2]
