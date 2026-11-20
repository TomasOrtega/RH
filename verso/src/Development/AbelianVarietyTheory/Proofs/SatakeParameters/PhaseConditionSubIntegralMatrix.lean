import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero

noncomputable section

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hQ k j)`.
-/
theorem mul_int {a b c : ℕ} (P : Matrix (Fin a) (Fin b) L) (Q : Matrix (Fin b) (Fin c) L)
    (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) (hQ : ∀ i j, Q i j ∈ Formalism.UG.intL L) :
    ∀ i j, (P * Q) i j ∈ Formalism.UG.intL L := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hQ k j)

/- English proof (translation)
The claim follows from `Subring.sum_mem _ fun i _ => hP i i`.
-/
theorem trace_int {a : ℕ} (P : Matrix (Fin a) (Fin a) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    P.trace ∈ Formalism.UG.intL L :=
  Subring.sum_mem _ fun i _ => hP i i

/- English proof (translation)
Introduce `i j`. Use `show Valued.v (σ (P j i)) ≤ 1`. Rewrite using `[hσ]`. Conclude with `hP j i`.
-/
theorem conjT_int {a b : ℕ} (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (P : Matrix (Fin a) (Fin b) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (P.map σ)) i j ∈ Formalism.UG.intL L := by
  intro i j
  show Valued.v (σ (P j i)) ≤ 1
  rw [hσ]; exact hP j i

/- English proof (translation)
Establish `he : ((u - u') + σ (u - u')) / 2 ∈ Formalism.UG.intL L` using `by show Valued.v (((u - u') + σ (u - u')) / 2) ≤ 1`. Rewrite using `[map_div₀, h2, div_one]`. Use `(Formalism.UG.intL L).add_mem hd ?_` and prove the remaining obligations. Use `show Valued.v (σ (u - u')) ≤ 1`. Rewrite using `[hσ]`.

Conclude with `hd`. Establish `hs : σ (((u - u') + σ (u - u')) / 2) = ((u - u') + σ (u - u')) / 2`. Rewrite using `[map_div₀, map_add, hσσ, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : (u' + σ u') / 2 = (u + σ u) / 2 - ((u - u') + σ (u - u')) / 2`.

Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq, AddChar.map_sub_eq_div, h, hψ _ he hs, div_one]`.
-/
theorem phase_shift (σ : L →+* L) (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h2 : Valued.v (2 : L) = 1) (ψ : AddChar L ℂ) (hψ : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (u u' : L) (hd : u - u' ∈ Formalism.UG.intL L) (h : ψ ((u + σ u) / 2) = 1) :
    ψ ((u' + σ u') / 2) = 1 := by
  have he : ((u - u') + σ (u - u')) / 2 ∈ Formalism.UG.intL L := by
    show Valued.v (((u - u') + σ (u - u')) / 2) ≤ 1
    rw [map_div₀, h2, div_one]
    refine (Formalism.UG.intL L).add_mem hd ?_
    show Valued.v (σ (u - u')) ≤ 1
    rw [hσ]; exact hd
  have hs : σ (((u - u') + σ (u - u')) / 2) = ((u - u') + σ (u - u')) / 2 := by
    rw [map_div₀, map_add, hσσ, map_ofNat]; ring
  have heq : (u' + σ u') / 2 = (u + σ u) / 2 - ((u - u') + σ (u - u')) / 2 := by
    rw [map_sub]; ring
  rw [heq, AddChar.map_sub_eq_div, h, hψ _ he hs, div_one]

end GlobalTheory.Hk3.ShiftPhase

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

/- English proof (translation)
Introduce `j k`. Establish `h : (Matrix.transpose (x.map σ) * C) j k = - σ ((C * x) k j)`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hC, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h]`. Use `(Formalism.UG.intL L).neg_mem ?_` and prove the remaining obligations. Use `show Valued.v (σ _) ≤ 1`. Rewrite using `[hσ]`. Conclude with `hCx k j`.
-/
theorem conjT_mul_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ} (σ : L →+* L)
    (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (C : Matrix (Fin a) (Fin a) L) (hC : ∀ i j, σ (C i j) = - C j i)
    (x : Matrix (Fin a) (Fin b) L) (hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (x.map σ) * C) i j ∈ Formalism.UG.intL L := by
  intro j k
  have h : (Matrix.transpose (x.map σ) * C) j k = - σ ((C * x) k j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hC,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  refine (Formalism.UG.intL L).neg_mem ?_
  show Valued.v (σ _) ≤ 1
  rw [hσ]; exact hCx k j

/- English proof (translation)
Introduce `L _ _ ϖ σ q δ n n' A ψ hU hq hA hδ _ hψ x l hl hx C hC hCv hCxl`. Establish `h2 : Valued.v (2 : L) = 1` using `GlobalTheory.Hk3.Inh.v_two hU hq`. Take `⟨hσσ, hσv, -⟩` from `hU`. Establish `hCi : ∀ i j, C i j ∈ Formalism.UG.intL L` using `fun i j => (hCv i j).le`. Establish `hCl : ∀ i j, (C * l) i j ∈ Formalism.UG.intL L` using `mul_int C l hCi hl`.

Establish `hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L`. Establish `e : C * x = C * (x - l) + C * l` using `by rw [Matrix.mul_sub]; abel`. Introduce `i j`. Rewrite using `[e, Matrix.add_apply]`. Conclude with `(Formalism.UG.intL L).add_mem (hCxl i j) (hCl i j)`.

Establish `hsub : Matrix.transpose ((x - l).map σ) = Matrix.transpose (x.map σ) - Matrix.transpose (l.map σ)`. Use extensionality with `i j`. Simplify using `[map_sub]`. Use `set X := Matrix.transpose (x.map σ) with hX`. Use `set Y := Matrix.transpose (l.map σ) with hY`.

Establish `hYi : ∀ i j, Y i j ∈ Formalism.UG.intL L` using `conjT_int σ hσv l hl`. Establish `hXC : ∀ i j, (X * C) i j ∈ Formalism.UG.intL L` using `conjT_mul_int σ hσσ hσv C hC x hCx`. Establish `hd : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) = Matrix.trace (C * x * A * Y) + Matrix.trace (X * C * l * A) - Matrix.trace (C * l * A * Y)`. Establish `h3 : Matrix.trace (C * (l * A * X)) = Matrix.trace (X * C * l * A)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]`. Rewrite using `[h3]`. Simplify using `only [Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `hdi : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) ∈ Formalism.UG.intL L`.

Rewrite using `[hd]`. Use `(Formalism.UG.intL L).sub_mem ((Formalism.UG.intL L).add_mem ?_ ?_) ?_` and prove the remaining obligations. Conclude with `trace_int _ (mul_int _ _ (mul_int _ _ hCx hA) hYi)`. Conclude with `trace_int _ (mul_int _ _ (mul_int _ _ hXC hl) hA)`. Conclude with `trace_int _ (mul_int _ _ (mul_int _ _ hCl hA) hYi)`.

Rewrite using `[hsub]`. Use `phase_shift σ hσσ hσv h2 ψ hψ (δ * Matrix.trace (C * (x * A * X))) _ ?_ (hx C hC hCv hCx)` and prove the remaining obligations. Rewrite using `[← mul_sub]`. Use `(Formalism.UG.intL L).mul_mem ?_ hdi` and prove the remaining obligations. Use `show Valued.v δ ≤ 1`.

Rewrite using `[hδ]`.
-/
theorem shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  intro L _ _ ϖ σ q δ n n' A ψ hU hq hA hδ _ hψ x l hl hx C hC hCv hCxl
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, -⟩ := hU
  have hCi : ∀ i j, C i j ∈ Formalism.UG.intL L := fun i j => (hCv i j).le
  have hCl : ∀ i j, (C * l) i j ∈ Formalism.UG.intL L := mul_int C l hCi hl
  have hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L := by
    have e : C * x = C * (x - l) + C * l := by rw [Matrix.mul_sub]; abel
    intro i j
    rw [e, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hCxl i j) (hCl i j)
  have hsub : Matrix.transpose ((x - l).map σ) = Matrix.transpose (x.map σ) - Matrix.transpose (l.map σ) := by
    ext i j; simp [map_sub]
  set X := Matrix.transpose (x.map σ) with hX
  set Y := Matrix.transpose (l.map σ) with hY
  have hYi : ∀ i j, Y i j ∈ Formalism.UG.intL L := conjT_int σ hσv l hl
  have hXC : ∀ i j, (X * C) i j ∈ Formalism.UG.intL L := conjT_mul_int σ hσσ hσv C hC x hCx
  have hd : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y)))
      = Matrix.trace (C * x * A * Y) + Matrix.trace (X * C * l * A) - Matrix.trace (C * l * A * Y) := by
    have h3 : Matrix.trace (C * (l * A * X)) = Matrix.trace (X * C * l * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    rw [h3]
    simp only [Matrix.mul_assoc]
    abel
  have hdi : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) ∈ Formalism.UG.intL L := by
    rw [hd]
    refine (Formalism.UG.intL L).sub_mem ((Formalism.UG.intL L).add_mem ?_ ?_) ?_
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCx hA) hYi)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hXC hl) hA)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCl hA) hYi)
  rw [hsub]
  refine phase_shift σ hσσ hσv h2 ψ hψ (δ * Matrix.trace (C * (x * A * X))) _ ?_ (hx C hC hCv hCx)
  rw [← mul_sub]
  refine (Formalism.UG.intL L).mul_mem ?_ hdi
  show Valued.v δ ≤ 1
  rw [hδ]

end GlobalTheory.Hk3.ShiftPhase
