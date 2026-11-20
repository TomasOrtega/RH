import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace LineChowForm

variable {F : Type*} [Field F]

variable {F : Type*} [Field F]

def D2 : MvPolynomial (Fin 2 × Fin 2) F := X (0,0) * X (1,1) - X (0,1) * X (1,0)

def substZeroZeroZero : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((0 : Fin 2),(0 : Fin 2)) then 0 else X ij)

def substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((1 : Fin 2),(1 : Fin 2)) then 0 else X ij)

/- English proof (translation)
Establish `key : ∀ q : MvPolynomial (Fin 2 × Fin 2) F, X (0,0) ∣ q - substZeroZeroZero q`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp [substZeroZeroZero]`. Consider the case `add p q hp hq`.

Establish `e : p + q - substZeroZeroZero (p+q) = (p - substZeroZeroZero p) + (q - substZeroZeroZero q)`. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add hp hq`.

Consider the case `mul_X p i hp`. Establish `e : p * X i - substZeroZeroZero (p * X i) = (p - substZeroZeroZero p) * X i + substZeroZeroZero p * (X i - substZeroZeroZero (X i))`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)` and prove the remaining obligations. Distinguish the cases in `hi : i = (0,0)`. Substitute `hi` using the available equality. Simplify using `[substZeroZeroZero]`. Simplify using `[substZeroZeroZero, hi]`.

Simplify `key q` using `[h]`.
-/
lemma X_dvd_of_substZeroZeroZero_eq_zero (q : MvPolynomial (Fin 2 × Fin 2) F) (h : substZeroZeroZero q = 0) : X (0,0) ∣ q := by
  have key : ∀ q : MvPolynomial (Fin 2 × Fin 2) F, X (0,0) ∣ q - substZeroZeroZero q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [substZeroZeroZero]
    | add p q hp hq =>
      have e : p + q - substZeroZeroZero (p+q) = (p - substZeroZeroZero p) + (q - substZeroZeroZero q) := by
        simp only [map_add]; ring
      rw [e]; exact dvd_add hp hq
    | mul_X p i hp =>
      have e : p * X i - substZeroZeroZero (p * X i) =
          (p - substZeroZeroZero p) * X i + substZeroZeroZero p * (X i - substZeroZeroZero (X i)) := by
        simp only [map_mul]; ring
      rw [e]
      refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
      by_cases hi : i = (0,0)
      · subst hi; simp [substZeroZeroZero]
      · simp [substZeroZeroZero, hi]
  simpa [h] using key q

/- English proof (translation)
Simplify using `[substZeroOneOne]`.
-/
lemma substZeroOneOne_X_zero_zero : substZeroOneOne (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = X (0,0) := by
  simp [substZeroOneOne]

/- English proof (translation)
Simplify using `[substZeroOneOne, hi]`.
-/
lemma substZeroOneOne_X_of_ne (i : Fin 2 × Fin 2) (hi : i ≠ (1,1)) :
    substZeroOneOne (X i : MvPolynomial (Fin 2 × Fin 2) F) = X i := by
  simp [substZeroOneOne, hi]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, 0, C a, by simp, by simp [substZeroOneOne]⟩`. Consider the case `add p q hp hq`. Take `⟨N, a, r, h1, h2⟩` from `hp`. Take `⟨M, b, s, h3, h4⟩` from `hq`.

Use `⟨N + M, X (0,0) ^ M * a + X (0,0) ^ N * b, X (0,0) ^ M * r + X (0,0) ^ N * s, ?_, ?_⟩` and prove the remaining obligations. Establish `: X (0,0) ^ (N + M) * (p + q) = X (0,0) ^ M * (X (0,0) ^ N * p) + X (0,0) ^ N * (X (0,0) ^ M * q)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h1, h3]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_add, map_mul, map_pow, substZeroOneOne_X_zero_zero, h2, h4]`. Consider the case `mul_X p i hp`. Take `⟨N, a, r, h1, h2⟩` from `hp`. Distinguish the cases in `hi : i = (1,1)`. Substitute `hi` using the available equality.

Use `⟨N + 1, X (0,0) * X (1,1) * a + r, r * (X (0,1) * X (1,0)), ?_, ?_⟩` and prove the remaining obligations. Establish `: X (0,0) ^ (N + 1) * (p * X (1,1)) = (X (0,0) ^ N * p) * (X (0,0) * X (1,1))` using `by ring`. Rewrite using `[this, h1]`. Simplify using `only [D2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_mul, map_mul, h2, substZeroOneOne_X_of_ne _ (by decide), substZeroOneOne_X_of_ne _ (by decide)]`. Use `⟨N, a * X i, r * X i, ?_, ?_⟩` and prove the remaining obligations. Establish `: X (0,0) ^ N * (p * X i) = (X (0,0) ^ N * p) * X i` using `by ring`. Rewrite using `[this, h1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_mul, h2, substZeroOneOne_X_of_ne _ hi]`.
-/
lemma pseudo (g : MvPolynomial (Fin 2 × Fin 2) F) :
    ∃ (N : ℕ) (q r : MvPolynomial (Fin 2 × Fin 2) F),
      X (0,0) ^ N * g = q * D2 + r ∧ substZeroOneOne r = r := by
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, C a, by simp, by simp [substZeroOneOne]⟩
  | add p q hp hq =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    obtain ⟨M, b, s, h3, h4⟩ := hq
    refine ⟨N + M, X (0,0) ^ M * a + X (0,0) ^ N * b, X (0,0) ^ M * r + X (0,0) ^ N * s, ?_, ?_⟩
    · have : X (0,0) ^ (N + M) * (p + q) = X (0,0) ^ M * (X (0,0) ^ N * p) + X (0,0) ^ N * (X (0,0) ^ M * q) := by
        ring
      rw [this, h1, h3]; ring
    · simp only [map_add, map_mul, map_pow, substZeroOneOne_X_zero_zero, h2, h4]
  | mul_X p i hp =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    by_cases hi : i = (1,1)
    · subst hi
      refine ⟨N + 1, X (0,0) * X (1,1) * a + r, r * (X (0,1) * X (1,0)), ?_, ?_⟩
      · have : X (0,0) ^ (N + 1) * (p * X (1,1)) = (X (0,0) ^ N * p) * (X (0,0) * X (1,1)) := by ring
        rw [this, h1]; simp only [D2]; ring
      · rw [map_mul, map_mul, h2, substZeroOneOne_X_of_ne _ (by decide), substZeroOneOne_X_of_ne _ (by decide)]
    · refine ⟨N, a * X i, r * X i, ?_, ?_⟩
      · have : X (0,0) ^ N * (p * X i) = (X (0,0) ^ N * p) * X i := by ring
        rw [this, h1]; ring
      · rw [map_mul, h2, substZeroOneOne_X_of_ne _ hi]

/- English proof (translation)
Establish `e0` using `congrArg substZeroZeroZero e`. Establish `hz : substZeroZeroZero (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = 0` using `by simp [substZeroZeroZero]`. Establish `hD : substZeroZeroZero (D2 : MvPolynomial (Fin 2 × Fin 2) F) = -(X (0,1) * X (1,0))`. Simplify using `[substZeroZeroZero, D2]`. Rewrite `e0` using `[map_mul, map_mul, hz, hD, zero_mul]`.

Establish `hne : -(X (0,1) * X (1,0)) ≠ (0 : MvPolynomial (Fin 2 × Fin 2) F)` using `neg_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _))`. Establish `hq : substZeroZeroZero q = 0`. Break down `mul_eq_zero.mp e0.symm with h' | h'` into its components or cases. Conclude with `absurd h' hne`. Conclude with `h'`.

Take `⟨q', rfl⟩` from `X_dvd_of_substZeroZeroZero_eq_zero q hq`. Use `⟨q', mul_left_cancel₀ (X_ne_zero ((0 : Fin 2),(0 : Fin 2))) ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma cancel1 (h q : MvPolynomial (Fin 2 × Fin 2) F) (e : X (0,0) * h = D2 * q) : D2 ∣ h := by
  have e0 := congrArg substZeroZeroZero e
  have hz : substZeroZeroZero (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by simp [substZeroZeroZero]
  have hD : substZeroZeroZero (D2 : MvPolynomial (Fin 2 × Fin 2) F) = -(X (0,1) * X (1,0)) := by
    simp [substZeroZeroZero, D2]
  rw [map_mul, map_mul, hz, hD, zero_mul] at e0
  have hne : -(X (0,1) * X (1,0)) ≠ (0 : MvPolynomial (Fin 2 × Fin 2) F) :=
    neg_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  have hq : substZeroZeroZero q = 0 := by
    rcases mul_eq_zero.mp e0.symm with h' | h'
    · exact absurd h' hne
    · exact h'
  obtain ⟨q', rfl⟩ := X_dvd_of_substZeroZeroZero_eq_zero q hq
  refine ⟨q', mul_left_cancel₀ (X_ne_zero ((0 : Fin 2),(0 : Fin 2))) ?_⟩
  rw [e]; ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Take `⟨q, hq⟩` from `h`. Conclude with `ih (cancel1 _ q (by rw [← hq]; ring))`.
-/
lemma cancelN (N : ℕ) (g : MvPolynomial (Fin 2 × Fin 2) F) (h : D2 ∣ X (0,0) ^ N * g) : D2 ∣ g := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    obtain ⟨q, hq⟩ := h
    exact ih (cancel1 _ q (by rw [← hq]; ring))

/- English proof (translation)
Establish `: ((aeval w).comp substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] A) = aeval (Function.update w (1,1) 0)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `hi : i = (1,1)`. Substitute `hi` using the available equality.

Simplify using `[substZeroOneOne]`. Simplify using `[substZeroOneOne, hi, Function.update_of_ne hi]`. Conclude with `DFunLike.congr_fun this r`.
-/
lemma aeval_substZeroOneOne {A : Type*} [CommRing A] [Algebra F A] (w : Fin 2 × Fin 2 → A)
    (r : MvPolynomial (Fin 2 × Fin 2) F) :
    aeval w (substZeroOneOne r) = aeval (Function.update w (1,1) 0) r := by
  have : ((aeval w).comp substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] A) =
      aeval (Function.update w (1,1) 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = (1,1)
    · subst hi; simp [substZeroOneOne]
    · simp [substZeroOneOne, hi, Function.update_of_ne hi]
  exact DFunLike.congr_fun this r

/- English proof (translation)
Introduce `h`. Use `congrArg (eval (fun ij : Fin 2 × Fin 2 => if ij.1 = ij.2 then (1 : F) else 0)) h` as an intermediate fact. Simplify using `[D2] at this`.
-/
theorem det_two_ne_zero : (D2 : MvPolynomial (Fin 2 × Fin 2) F) ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin 2 × Fin 2 => if ij.1 = ij.2 then (1 : F) else 0)) h
  simp [D2] at this

/- English proof (translation)
Use `⟨det_two_ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨N, q, r, h1, h2⟩` from `pseudo g`. Establish `hr : r = 0`. Establish `hz : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (X (0,0) * r) = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `w`. Establish `key : aeval w (X (0,0) * r) = 0`. Distinguish the cases in `hw : w (0,0) = 0`. Simplify using `[hw]`. Set `u : Fin 2 × Fin 2 → AlgebraicClosure F` to `Function.update w (1,1) (w (0,1) * w (1,0) / w (0,0))`.

Establish `u00 : u (0,0) = w (0,0)` using `Function.update_of_ne (by decide) _ _`. Establish `u01 : u (0,1) = w (0,1)` using `Function.update_of_ne (by decide) _ _`. Establish `u10 : u (1,0) = w (1,0)` using `Function.update_of_ne (by decide) _ _`. Establish `u11 : u (1,1) = w (0,1) * w (1,0) / w (0,0)` using `Function.update_self _ _ _`. Establish `hinc : u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2`.

Use `⟨![w (0,1), -w (0,0)], fun h => ?_, fun g' hg' => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun h 1` as an intermediate fact. Simplify using `at this`. Conclude with `hw this`. Rewrite `hg'` using `[Ideal.mem_bot]`.

Simplify using `[hg']`. Use `fin_cases i`. Simplify using `[Fin.sum_univ_two, u00, u01]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Fin.sum_univ_two, u10, u11]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hg'` using `hg u hinc`. Establish `hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0`. Simplify using `only [D2, map_sub, map_mul, aeval_X, u00, u01, u10, u11]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `congrArg (aeval u) h1`. Simplify using `only [map_mul, map_add, map_pow, hg', hD, mul_zero, zero_add] at h3`. Establish `hw' : aeval w r = aeval u r`.

Rewrite using `[← h2, aeval_substZeroOneOne, aeval_substZeroOneOne]`. Use `congr 1`. Simplify using `only [u, Function.update_idem]`. Rewrite using `[map_mul, hw', ← h3, mul_zero]`. Rewrite using `[eval_map, map_zero]`.

Simplify `key` using `[aeval_def]`. Establish `hz' : (X (0,0) * r : MvPolynomial (Fin 2 × Fin 2) F) = 0` using `MvPolynomial.map_injective _ (algebraMap F (AlgebraicClosure F)).injective (by simpa using hz)`. Conclude with `(mul_eq_zero.mp hz').resolve_left (X_ne_zero _)`. Rewrite `h1` using `[hr, add_zero]`. Conclude with `cancelN N g ⟨q, by rw [h1]; ring⟩`.

Introduce and unpack `⟨h, rfl⟩ u ⟨x, hx, -, hu⟩`. Establish `E0` using `hu 0`. Establish `E1` using `hu 1`. Simplify using `only [Fin.sum_univ_two] at E0 E1`. Establish `hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0`.

Simplify using `only [D2, map_sub, map_mul, aeval_X]`. Distinguish the cases in `h0 : x 0 = 0`. Apply the tactic sequence `have h1 : x 1 ≠ 0 := fun h1 => hx (funext fun j => by fin_cases j <;> simpa [*])`. Apply `mul_right_cancel₀ h1` to reduce the goal to its premises. Take the linear combination `(-(u (1,0))) * E0 + u (0,0) * E1`.

Apply `mul_right_cancel₀ h0` to reduce the goal to its premises. Take the linear combination `u (1,1) * E0 - u (0,1) * E1`. Rewrite using `[map_mul, hD, zero_mul]`.
-/
theorem isChowForm_line :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  refine ⟨det_two_ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  ·
    obtain ⟨N, q, r, h1, h2⟩ := pseudo g
    have hr : r = 0 := by
      have hz : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (X (0,0) * r) = 0 := by
        apply MvPolynomial.funext
        intro w
        have key : aeval w (X (0,0) * r) = 0 := by
          by_cases hw : w (0,0) = 0
          · simp [hw]
          · let u : Fin 2 × Fin 2 → AlgebraicClosure F :=
              Function.update w (1,1) (w (0,1) * w (1,0) / w (0,0))
            have u00 : u (0,0) = w (0,0) := Function.update_of_ne (by decide) _ _
            have u01 : u (0,1) = w (0,1) := Function.update_of_ne (by decide) _ _
            have u10 : u (1,0) = w (1,0) := Function.update_of_ne (by decide) _ _
            have u11 : u (1,1) = w (0,1) * w (1,0) / w (0,0) := Function.update_self _ _ _
            have hinc : u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 := by
              refine ⟨![w (0,1), -w (0,0)], fun h => ?_, fun g' hg' => ?_, fun i => ?_⟩
              · have := congrFun h 1
                simp at this
                exact hw this
              · rw [Ideal.mem_bot] at hg'
                simp [hg']
              · fin_cases i
                · simp [Fin.sum_univ_two, u00, u01]; ring
                · simp [Fin.sum_univ_two, u10, u11]; field_simp; ring
            have hg' := hg u hinc
            have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
              simp only [D2, map_sub, map_mul, aeval_X, u00, u01, u10, u11]
              field_simp
              ring
            have h3 := congrArg (aeval u) h1
            simp only [map_mul, map_add, map_pow, hg', hD, mul_zero, zero_add] at h3
            have hw' : aeval w r = aeval u r := by
              rw [← h2, aeval_substZeroOneOne, aeval_substZeroOneOne]
              congr 1
              simp only [u, Function.update_idem]
            rw [map_mul, hw', ← h3, mul_zero]
        rw [eval_map, map_zero]
        simpa [aeval_def] using key
      have hz' : (X (0,0) * r : MvPolynomial (Fin 2 × Fin 2) F) = 0 :=
        MvPolynomial.map_injective _ (algebraMap F (AlgebraicClosure F)).injective (by simpa using hz)
      exact (mul_eq_zero.mp hz').resolve_left (X_ne_zero _)
    rw [hr, add_zero] at h1
    exact cancelN N g ⟨q, by rw [h1]; ring⟩
  · rintro ⟨h, rfl⟩ u ⟨x, hx, -, hu⟩
    have E0 := hu 0
    have E1 := hu 1
    simp only [Fin.sum_univ_two] at E0 E1
    have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
      simp only [D2, map_sub, map_mul, aeval_X]
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := fun h1 => hx (funext fun j => by fin_cases j <;> simpa [*])
        apply mul_right_cancel₀ h1
        linear_combination (-(u (1,0))) * E0 + u (0,0) * E1
      · apply mul_right_cancel₀ h0
        linear_combination u (1,1) * E0 - u (0,1) * E1
    rw [map_mul, hD, zero_mul]

/- English proof (translation)
The claim follows from `Ideal.isPrime_bot isHomog f hf d := by rw [Ideal.mem_bot] at hf ⊢ simp [hf] isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩`.
-/
theorem isProjPrime_line : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) F)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩

/- English proof (translation)
Establish `hX : ∀ i j : Fin 2, IsWeightedHomogeneous (groupWeight 2 2) (X (i, j) : MvPolynomial (Fin 2 × Fin 2) F) (Pi.single i 1)` using `fun i j => isWeightedHomogeneous_X F (groupWeight 2 2) (i, j)`. Establish `hw : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℕ) = fun _ => 1`. Apply the tactic sequence `funext i; fin_cases i <;> simp`. Establish `a` using `(hX 0 0).mul (hX 1 1)`. Establish `b` using `(hX 0 1).mul (hX 1 0)`.

Rewrite `a`, `b` using `[hw]`. Conclude with `(weightedHomogeneousSubmodule F (groupWeight 2 2) (fun _ => 1)).sub_mem a b`.
-/
theorem isMultiHomog_line : IsMultiHomog 1 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  have hX : ∀ i j : Fin 2, IsWeightedHomogeneous (groupWeight 2 2)
      (X (i, j) : MvPolynomial (Fin 2 × Fin 2) F) (Pi.single i 1) :=
    fun i j => isWeightedHomogeneous_X F (groupWeight 2 2) (i, j)
  have hw : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℕ) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  have a := (hX 0 0).mul (hX 1 1)
  have b := (hX 0 1).mul (hX 1 0)
  rw [hw] at a b
  exact (weightedHomogeneousSubmodule F (groupWeight 2 2) (fun _ => 1)).sub_mem a b

/- English proof (translation)
Rewrite using `[Ideal.mem_bot]`. Introduce `h`. Use `congrArg (eval (fun _ : Fin 2 => (1 : F))) h` as an intermediate fact. Simplify using `[linForm, Fin.sum_univ_two] at this`.
-/
theorem linForm_line : linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0) ∉
    (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by
  rw [Ideal.mem_bot]
  intro h
  have := congrArg (eval (fun _ : Fin 2 => (1 : F))) h
  simp [linForm, Fin.sum_univ_two] at this

end LineChowForm

end

end GroundTheory.Heights₂.Heights
