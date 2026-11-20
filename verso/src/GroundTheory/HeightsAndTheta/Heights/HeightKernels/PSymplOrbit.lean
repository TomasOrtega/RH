import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOrbit

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons]`.
-/
theorem smul_symplCons {R : Type*} [CommRing R] {n : ℕ} (m p q : R) (w : Fin n ⊕ Fin n → R) :
    m • symplCons p q w = symplCons (m * p) (m * q) (m • w) := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>`. Simplify using `[symplCons, Fin.succ_ne_zero]`.
-/
theorem symplCons_one_zero {R : Type*} [CommRing R] {n : ℕ} :
    symplCons (1 : R) 0 (0 : Fin n ⊕ Fin n → R) = Pi.single (Sum.inl 0) 1 := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [symplCons, Fin.succ_ne_zero]

end PSymplOrbit

open PSymplOrbit in

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `v`. Take `⟨c, a', b', x, y, ha, hb, hxy⟩` from `h4 (v (Sum.inl 0)) (v (Sum.inr 0))`.

Establish `hE` using `h1 ℤ 0 a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)`. Use `⟨_, hE, c, ?_⟩` and prove the remaining obligations. Establish `htail : symplTail v = 0` using `funext fun z => z.elim (fun i => i.elim0) (fun i => i.elim0)`. Establish `hrow : symplExt a' b' (-y) x (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℤ) (Sum.inl 0) = symplCons a' b' 0`. Both sides reduce to the same expression.

Rewrite using `[hrow, smul_symplCons, ← ha, ← hb, smul_zero, ← htail]`. Conclude with `((h5 ℤ 0).1 v).symm`. Consider the case `succ n ih`. Introduce `v`. Take `⟨Q, hQ, m', hw⟩` from `ih (symplTail v)`.

Take `⟨c, a', b', x, y, ha, hb, hxy⟩` from `h4 (v (Sum.inl 0)) (v (Sum.inr 0))`. Take `⟨k, c'', d'', x', y', hc, hm, hxy'⟩` from `h4 c m'`. Take `⟨P₂, hP₂, hrow₂⟩` from `h3 n c'' d'' x' y' hxy'`. Establish `hE₁` using `h1 ℤ (n + 1) a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)`. Establish `hE₂` using `h1 ℤ (n + 1) 1 0 0 1 Q (by ring) hQ`.

Use `⟨P₂ * symplExt 1 0 0 1 Q * symplExt a' b' (-y) x 1, Submonoid.mul_mem _ (Submonoid.mul_mem _ hP₂ hE₂) hE₁, k, ?_⟩` and prove the remaining obligations. Establish `e1 : symplCons c 0 (symplTail v) ᵥ* symplExt a' b' (-y) x 1 = v`. Rewrite using `[h2, vecMul_one]`. Simplify using `only [zero_mul, add_zero]`. Rewrite using `[← ha, ← hb]`.

Conclude with `(h5 ℤ (n + 1)).1 v`. Establish `e2 : symplCons c 0 (symplCons m' 0 0) ᵥ* symplExt 1 0 0 1 Q = symplCons c 0 (symplTail v)`. Rewrite using `[h2]`. Simplify using `only [mul_one, mul_zero, add_zero]`. Use `congr 1`.

Establish `hs : symplCons m' 0 (0 : Fin n ⊕ Fin n → ℤ) = m' • symplCons 1 0 0`. Rewrite using `[smul_symplCons]`. Simplify using the standard rewrite rules. Rewrite using `[hs, smul_vecMul, symplCons_one_zero, single_one_vecMul, hw]`. Both sides reduce to the same expression.

Establish `e3 : k • P₂ (Sum.inl 0) = symplCons c 0 (symplCons m' 0 0)`. Rewrite using `[hrow₂, hc, hm, smul_symplCons, smul_symplCons]`. Simplify using the standard rewrite rules. Rewrite using `[mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← smul_vecMul, ← smul_vecMul, e3, e2, e1]`.
-/
theorem SymplOrbit.proof (h1 : SymplExtMem.Statement) (h2 : SymplExtVecMul.Statement)
    (h3 : SymplTwoRow.Statement) (h4 : SymplGcd.Statement) (h5 : SymplCons.Statement) :
    SymplOrbit.Statement := by
  intro n
  induction n with
  | zero =>
    intro v
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    have hE := h1 ℤ 0 a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    refine ⟨_, hE, c, ?_⟩
    have htail : symplTail v = 0 := funext fun z => z.elim (fun i => i.elim0) (fun i => i.elim0)
    have hrow : symplExt a' b' (-y) x (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℤ) (Sum.inl 0) =
        symplCons a' b' 0 :=
      rfl
    rw [hrow, smul_symplCons, ← ha, ← hb, smul_zero, ← htail]
    exact ((h5 ℤ 0).1 v).symm
  | succ n ih =>
    intro v
    obtain ⟨Q, hQ, m', hw⟩ := ih (symplTail v)
    obtain ⟨c, a', b', x, y, ha, hb, hxy⟩ := h4 (v (Sum.inl 0)) (v (Sum.inr 0))
    obtain ⟨k, c'', d'', x', y', hc, hm, hxy'⟩ := h4 c m'
    obtain ⟨P₂, hP₂, hrow₂⟩ := h3 n c'' d'' x' y' hxy'
    have hE₁ := h1 ℤ (n + 1) a' b' (-y) x 1 (by linarith) (Submonoid.one_mem _)
    have hE₂ := h1 ℤ (n + 1) 1 0 0 1 Q (by ring) hQ
    refine ⟨P₂ * symplExt 1 0 0 1 Q * symplExt a' b' (-y) x 1,
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP₂ hE₂) hE₁, k, ?_⟩
    have e1 : symplCons c 0 (symplTail v) ᵥ* symplExt a' b' (-y) x 1 = v := by
      rw [h2, vecMul_one]
      simp only [zero_mul, add_zero]
      rw [← ha, ← hb]
      exact (h5 ℤ (n + 1)).1 v
    have e2 : symplCons c 0 (symplCons m' 0 0) ᵥ* symplExt 1 0 0 1 Q = symplCons c 0 (symplTail v) := by
      rw [h2]
      simp only [mul_one, mul_zero, add_zero]
      congr 1
      have hs : symplCons m' 0 (0 : Fin n ⊕ Fin n → ℤ) = m' • symplCons 1 0 0 := by
        rw [smul_symplCons]; simp
      rw [hs, smul_vecMul, symplCons_one_zero, single_one_vecMul, hw]
      rfl
    have e3 : k • P₂ (Sum.inl 0) = symplCons c 0 (symplCons m' 0 0) := by
      rw [hrow₂, hc, hm, smul_symplCons, smul_symplCons]
      simp
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← smul_vecMul, ← smul_vecMul, e3, e2, e1]

end GroundTheory.Heights₂.Heights
