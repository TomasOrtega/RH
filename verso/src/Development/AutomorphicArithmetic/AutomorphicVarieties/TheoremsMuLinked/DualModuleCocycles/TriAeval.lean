import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `⟨fun a b hab => ?_, fun i => by simp⟩` and prove the remaining obligations. Simplify using `[Matrix.one_apply_ne hab.ne']`. Consider the case `succ k ih`.

Use `⟨fun a b hab => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Break down `lt_or_ge c a with hc | hc` into its components or cases. Rewrite using `[ih.1 a c hc, zero_mul]`.

Rewrite using `[h c b (lt_of_lt_of_le hab hc), mul_zero]`. Rewrite using `[pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[ih.2, hd, pow_succ]`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with hc | hc` into its components or cases.

Rewrite using `[ih.1 i c hc, zero_mul]`. Rewrite using `[h c i hc, mul_zero]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
private theorem tri_pow {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (k : ℕ) :
    (∀ a b, b < a → (u ^ k) a b = 0) ∧ ∀ i, (u ^ k) i i = α i ^ k := by
  induction k with
  | zero =>
    refine ⟨fun a b hab => ?_, fun i => by simp⟩
    simp [Matrix.one_apply_ne hab.ne']
  | succ k ih =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rcases lt_or_ge c a with hc | hc
      · rw [ih.1 a c hc, zero_mul]
      · rw [h c b (lt_of_lt_of_le hab hc), mul_zero]
    · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ih.2, hd, pow_succ]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [ih.1 i c hc, zero_mul]
        · rw [h c i hc, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Use `⟨fun a b hab => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, Matrix.add_apply, hp.1 a b hab, hq.1 a b hab, add_zero]`. Rewrite using `[map_add, Matrix.add_apply, hp.2, hq.2, Polynomial.eval_add]`.

Consider the case `monomial k c`. Establish `hk` using `tri_pow u α h hd k`. Rewrite using `[Polynomial.aeval_monomial, ← Algebra.smul_def]`. Use `⟨fun a b hab => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, hk.1 a b hab, smul_zero]`.

Rewrite using `[Matrix.smul_apply, hk.2, Polynomial.eval_monomial, smul_eq_mul]`.
-/
private theorem tri_aeval {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (p : Polynomial O) :
    (∀ a b, b < a → (Polynomial.aeval u p) a b = 0) ∧ ∀ i, (Polynomial.aeval u p) i i = p.eval (α i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [map_add, Matrix.add_apply, hp.1 a b hab, hq.1 a b hab, add_zero]
    · rw [map_add, Matrix.add_apply, hp.2, hq.2, Polynomial.eval_add]
  | monomial k c =>
    have hk := tri_pow u α h hd k
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [Matrix.smul_apply, hk.1 a b hab, smul_zero]
    · rw [Matrix.smul_apply, hk.2, Polynomial.eval_monomial, smul_eq_mul]

/- English proof (translation)
Introduce `O _ n u α h hd`. Establish `hev : ∀ i k, (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))).eval (α k) = ∏ j ∈ Finset.univ.erase i, (α k - α j)`. Introduce `i k`. Simplify using `[Polynomial.eval_prod]`. Use `⟨fun a b hab => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `(tri_aeval u α h hd _).1 a b hab`. Conclude with `(tri_aeval u α h hd _).1 a b hab`. Use `show kEl u α i i i = _`. Rewrite using `[kEl, (tri_aeval u α h hd _).2 i, hev]`. Use `show kEl u α i i i = _`.

Rewrite using `[kEl, (tri_aeval u α h hd _).2 i, hev]`.
-/
theorem UpperTheory.V.Th.Coc.flagB :
    ∀ {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O), (∀ a b, b < a → u a b = 0) → (∀ i, u i i = α i) → (∀ a b, b < a → kS u α a b = 0 ∧ kT u α a b = 0) ∧ ∀ i, kS u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) ∧ kT u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) := by
  intro O _ n u α h hd
  have hev : ∀ i k, (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))).eval (α k) =
      ∏ j ∈ Finset.univ.erase i, (α k - α j) := by
    intro i k
    simp [Polynomial.eval_prod]
  refine ⟨fun a b hab => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · exact (tri_aeval u α h hd _).1 a b hab
  · exact (tri_aeval u α h hd _).1 a b hab
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
