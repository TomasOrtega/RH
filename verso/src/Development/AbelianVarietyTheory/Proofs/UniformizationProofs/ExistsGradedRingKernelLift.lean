import Mathlib

open Polynomial

namespace GlobalTheory

def reesShiftIdeal {R : Type} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    rw [Subalgebra.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' := fun p q hq n => by
    rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    have e' : j + k = n := by simpa using e
    rw [← e', add_assoc, pow_add]
    exact Ideal.mul_mem_mul (p.2 j) (hq k)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_reesShiftIdeal {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := Iff.rfl

/- English proof (translation)
Simplify using `[Polynomial.algebraMap_eq]`.
-/
theorem coeff_sum_algebraMap_mul_rees {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by
  simp [Polynomial.algebraMap_eq]

/- English proof (translation)
Introduce `R _ _ I`. Use `⟨reesAlgebra I ⧸ reesShiftIdeal I, inferInstance, (Ideal.Quotient.mk _).comp (algebraMap R (reesAlgebra I)), inferInstance, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]`. Introduce `n`.

Rewrite using `[Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]`. Use `split_ifs with hn`. Substitute `hn` using the available equality. Simplify using `using hx`. Conclude with `Ideal.zero_mem _`.

Introduce `e g' hg' a b c D₀ D₁ hD hex v' hv'`. Establish `hg'x : ∀ x : R, g' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk (reesShiftIdeal I) (algebraMap R (reesAlgebra I) x)` using `fun x => by`. Use `RingHom.congr_fun hg' x` as an intermediate fact. Simplify `this` using `only [RingHom.comp_apply]`. Take `⟨d₀, rfl⟩ : ∃ d : Matrix (Fin b) (Fin a) R, D₀ = d.map (Ideal.Quotient.mk _)` from `⟨Matrix.of fun j k => (Ideal.Quotient.mk_surjective (D₀ j k)).choose, by`.

Use extensionality with `j k`. Simplify using `[(Ideal.Quotient.mk_surjective (D₀ j k)).choose_spec]⟩`. Take `⟨d₁, rfl⟩ : ∃ d : Matrix (Fin c) (Fin b) R, D₁ = d.map (Ideal.Quotient.mk _)` from `⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (D₁ i j)).choose, by`. Use extensionality with `i j`. Simplify using `[(Ideal.Quotient.mk_surjective (D₁ i j)).choose_spec]⟩`.

Take `⟨r, rfl⟩ : ∃ r : Fin a → R, v' = fun k => Ideal.Quotient.mk _ (r k)` from `⟨fun k => (Ideal.Quotient.mk_surjective (v' k)).choose,`. Use function extensionality and compare the values at `fun k => (Ideal.Quotient.mk_surjective (v' k)).choose_spec.symm⟩`. Establish `hs : ∀ j, ∑ k, d₀ j k * r k ∈ I ^ (e + 1)` using `fun j => by`. Establish `h` using `congrFun hv' j`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Ideal.Quotient.factor_mk, Pi.zero_apply] at h`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Simplify `h` using `only [map_mul]`. Establish `hs2 : ∀ i, ∑ j, d₁ i j * ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1)` using `fun i => by`. Establish `hrow : ∀ k, ∑ j, d₁ i j * d₀ j k ∈ I ^ (e + 1 + 1)` using `fun k => by`. Establish `h` using `congrFun (congrFun hD i) k`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Simplify `h` using `only [map_mul]`. Establish `heq : ∑ j, d₁ i j * ∑ k, d₀ j k * r k = ∑ k, (∑ j, d₁ i j * d₀ j k) * r k`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, mul_assoc]`.

Conclude with `Finset.sum_comm`. Rewrite using `[heq]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hrow k)`. Take `⟨m, hm⟩ : ∃ m : Fin b → reesAlgebra I, ∀ j, (m j : R[X]) = Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k)` from `⟨fun j => ⟨Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k), reesAlgebra.monomial_mem.mpr (hs j)⟩, fun _ => rfl⟩`. Establish `hW : ((d₁.map (Ideal.Quotient.mk _)).map g').mulVec (fun j => Ideal.Quotient.mk (reesShiftIdeal I) (m j)) = 0`.

Use function extensionality and compare the values at `i`. Establish `hmem : (∑ j, algebraMap R (reesAlgebra I) (d₁ i j) * m j) ∈ reesShiftIdeal I`. Rewrite using `[mem_reesShiftIdeal]`. Introduce `n`. Rewrite using `[coeff_sum_algebraMap_mul_rees]`.

Simplify using `only [hm, Polynomial.coeff_monomial]`. Distinguish the cases in `hn : e + 1 = n`. Substitute `hn` using the available equality. Simplify using `using hs2 i`. Simplify using `[hn]`.

Use `Ideal.Quotient.eq_zero_iff_mem.mpr hmem` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify `this` using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, Pi.zero_apply, map_mul]`. Take `⟨V, hV⟩` from `hex _ hW`. Use `choose P hP using fun k => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (V k)`.

Establish `hdiff : ∀ j, ∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1)` using `fun j => by`. Establish `h` using `congrFun hV j`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, ← hP] at h`. Establish `h' : Ideal.Quotient.mk (reesShiftIdeal I) (∑ k, algebraMap R (reesAlgebra I) (d₀ j k) * P k) = Ideal.Quotient.mk (reesShiftIdeal I) (m j)`. Rewrite using `[map_sum]`.

Simplify `h` using `only [map_mul]`. Rewrite `h'` using `[Ideal.Quotient.eq, mem_reesShiftIdeal]`. Establish `h''` using `h' (e + 1)`. Rewrite `h''` using `[Subalgebra.coe_sub, Polynomial.coeff_sub, coeff_sum_algebraMap_mul_rees, hm, Polynomial.coeff_monomial, if_pos rfl]`. Conclude with `h''`.

Use `⟨fun k => Ideal.Quotient.mk _ (r k - (P k : R[X]).coeff (e + 1)), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Establish `hmem : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) ∈ I ^ (e + 1 + 1)`. Establish `heq : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) = -(∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k)`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `neg_mem (hdiff j)`. Use `Ideal.Quotient.eq_zero_iff_mem.mpr hmem` as an intermediate fact. Rewrite `this` using `[map_sum]`.

Simplify `this` using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_mul]`. Introduce `k`. Simplify using `only [Ideal.Quotient.factor_mk]`. Rewrite using `[Ideal.Quotient.eq, sub_sub_cancel_left]`. Conclude with `neg_mem ((P k).2 (e + 1))`.
-/
theorem exists_graded_ring_kernel_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∃ (S : Type) (_ : CommRing S) (g : R →+* S), IsNoetherianRing S ∧ (∀ x ∈ I, g x = 0) ∧ ∀ (e : ℕ) (g' : R ⧸ I ^ (e + 1 + 1) →+* S), g'.comp (Ideal.Quotient.mk _) = g → ∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) (R ⧸ I ^ (e + 1 + 1))) (D₁ : Matrix (Fin c) (Fin b) (R ⧸ I ^ (e + 1 + 1))), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g').mulVec w = 0 → ∃ v, (D₀.map g').mulVec v = w) → ∀ v' : Fin a → R ⧸ I ^ (e + 1), (D₀.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))).mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) (v k) = v' k := by
  intro R _ _ I
  refine ⟨reesAlgebra I ⧸ reesShiftIdeal I, inferInstance,
    (Ideal.Quotient.mk _).comp (algebraMap R (reesAlgebra I)), inferInstance, ?_, ?_⟩
  ·
    intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    split_ifs with hn
    · subst hn
      simpa using hx
    · exact Ideal.zero_mem _
  · intro e g' hg' a b c D₀ D₁ hD hex v' hv'
    have hg'x : ∀ x : R, g' (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk (reesShiftIdeal I) (algebraMap R (reesAlgebra I) x) := fun x => by
      have := RingHom.congr_fun hg' x
      simpa only [RingHom.comp_apply] using this

    obtain ⟨d₀, rfl⟩ : ∃ d : Matrix (Fin b) (Fin a) R, D₀ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun j k => (Ideal.Quotient.mk_surjective (D₀ j k)).choose, by
        ext j k
        simp [(Ideal.Quotient.mk_surjective (D₀ j k)).choose_spec]⟩
    obtain ⟨d₁, rfl⟩ : ∃ d : Matrix (Fin c) (Fin b) R, D₁ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (D₁ i j)).choose, by
        ext i j
        simp [(Ideal.Quotient.mk_surjective (D₁ i j)).choose_spec]⟩
    obtain ⟨r, rfl⟩ : ∃ r : Fin a → R, v' = fun k => Ideal.Quotient.mk _ (r k) :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (v' k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (v' k)).choose_spec.symm⟩

    have hs : ∀ j, ∑ k, d₀ j k * r k ∈ I ^ (e + 1) := fun j => by
      have h := congrFun hv' j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Ideal.Quotient.factor_mk,
        Pi.zero_apply] at h
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_mul] using h

    have hs2 : ∀ i, ∑ j, d₁ i j * ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1) := fun i => by
      have hrow : ∀ k, ∑ j, d₁ i j * d₀ j k ∈ I ^ (e + 1 + 1) := fun k => by
        have h := congrFun (congrFun hD i) k
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simpa only [map_mul] using h
      have heq : ∑ j, d₁ i j * ∑ k, d₀ j k * r k = ∑ k, (∑ j, d₁ i j * d₀ j k) * r k := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [heq]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hrow k)

    obtain ⟨m, hm⟩ : ∃ m : Fin b → reesAlgebra I,
        ∀ j, (m j : R[X]) = Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k) :=
      ⟨fun j => ⟨Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k),
        reesAlgebra.monomial_mem.mpr (hs j)⟩, fun _ => rfl⟩

    have hW : ((d₁.map (Ideal.Quotient.mk _)).map g').mulVec
        (fun j => Ideal.Quotient.mk (reesShiftIdeal I) (m j)) = 0 := by
      funext i
      have hmem : (∑ j, algebraMap R (reesAlgebra I) (d₁ i j) * m j) ∈ reesShiftIdeal I := by
        rw [mem_reesShiftIdeal]
        intro n
        rw [coeff_sum_algebraMap_mul_rees]
        simp only [hm, Polynomial.coeff_monomial]
        by_cases hn : e + 1 = n
        · subst hn
          simpa using hs2 i
        · simp [hn]
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, Pi.zero_apply,
        map_mul] using this

    obtain ⟨V, hV⟩ := hex _ hW
    choose P hP using fun k => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (V k)
    have hdiff : ∀ j, ∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k ∈
        I ^ (e + 1 + 1) := fun j => by
      have h := congrFun hV j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, ← hP] at h
      have h' : Ideal.Quotient.mk (reesShiftIdeal I)
          (∑ k, algebraMap R (reesAlgebra I) (d₀ j k) * P k) =
          Ideal.Quotient.mk (reesShiftIdeal I) (m j) := by
        rw [map_sum]
        simpa only [map_mul] using h
      rw [Ideal.Quotient.eq, mem_reesShiftIdeal] at h'
      have h'' := h' (e + 1)
      rw [Subalgebra.coe_sub, Polynomial.coeff_sub, coeff_sum_algebraMap_mul_rees, hm,
        Polynomial.coeff_monomial, if_pos rfl] at h''
      exact h''
    refine ⟨fun k => Ideal.Quotient.mk _ (r k - (P k : R[X]).coeff (e + 1)), ?_, ?_⟩
    · funext j
      have hmem : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) ∈ I ^ (e + 1 + 1) := by
        have heq : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) =
            -(∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        rw [heq]
        exact neg_mem (hdiff j)
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_mul] using this
    · intro k
      simp only [Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, sub_sub_cancel_left]
      exact neg_mem ((P k).2 (e + 1))

end GlobalTheory
