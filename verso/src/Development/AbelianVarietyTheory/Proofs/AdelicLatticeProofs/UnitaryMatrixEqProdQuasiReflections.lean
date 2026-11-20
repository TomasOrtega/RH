import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLawsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitianStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEqStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Introduce `x y`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]`.
-/
theorem isUnE_mul {a b : Matrix (Fin n) (Fin n) E} (ha : IsUnE c G a) (hb : IsUnE c G b) :
    IsUnE c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro x y`. Simplify using the standard rewrite rules. Consider the case `cons p l ih`. Rewrite using `[List.map_cons, List.prod_cons]`.

Establish `hp` using `hl p List.mem_cons_self`. Conclude with `isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2) (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))`.
-/
theorem isUnE_prod (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    IsUnE c G (l.map fun p => refl c G p.1 p.2).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2)
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨[], by simp, by simp⟩`. Consider the case `cons p l ih`. Take `⟨l', h1, h2⟩` from `ih fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Establish `hp` using `hl p List.mem_cons_self`.

Take `⟨-, r1, r2, -⟩` from `GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1`. Use `⟨l' ++ [(p.1, c p.2)], ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Break down `List.mem_append.1 hq with hq | hq` into its components or cases. Conclude with `h1 q hq`.

Rewrite `hq` using `[List.mem_singleton]`. Substitute `hq` using the available equality. Use `⟨hp.1, ?_⟩` and prove the remaining obligations. Use `show c p.2 * c (c p.2) = 1`. Rewrite using `[hG.1, mul_comm]`.

Conclude with `hp.2`. Rewrite using `[List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc, ← mul_assoc (refl c G p.1 (c p.2)), r2, mul_comm (c p.2), hp.2, r1, one_mul, h2]`.
-/
theorem exists_inv (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      (l'.map fun p => refl c G p.1 p.2).prod * (l.map fun p => refl c G p.1 p.2).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    obtain ⟨-, r1, r2, -⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1
    refine ⟨l' ++ [(p.1, c p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show c p.2 * c (c p.2) = 1
        rw [hG.1, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (refl c G p.1 (c p.2)), r2, mul_comm (c p.2), hp.2, r1, one_mul, h2]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons p l ih`. Establish `hp` using `hl p List.mem_cons_self`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih fun q hq => hl q (List.mem_cons_of_mem _ hq), (GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).1, hp.2]`.

Simplify using the standard rewrite rules.
-/
theorem prod_fix (hG : IsHermForm c G) (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G v p.1 = 0) :
    (l.map fun p => refl c G p.1 p.2).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      (GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).1, hp.2]
    simp

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Take `⟨a, b, rfl⟩` from `Submodule.mem_span_pair.1 hy`. Establish `: hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z`. Simplify using `only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hx, hz]`. Simplify using the standard rewrite rules.
-/
theorem herm_span {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  have : hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z := by
    simp only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_add, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hx, hz]
  simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨[], by simp, by simp⟩`. Consider the case `succ k ih`. Take `⟨l, hl, hfix⟩` from `ih`. Distinguish the cases in `hk : k < n`.

Establish `hU` using `isUnE_mul (isUnE_prod hG l hl) hγ set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ`. Take `⟨m, hm, hmx⟩` from `GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)`. Use `⟨m ++ l, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Break down `List.mem_append.1 hp with hp | hp` into its components or cases.

Conclude with `⟨(hm p hp).1, (hm p hp).2.1⟩`. Conclude with `hl p hp`. Introduce `i hi`. Rewrite using `[List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi` into its components or cases.

Establish `hne : i ≠ ⟨k, hk⟩` using `fun h => by simp [h] at hi`. Rewrite using `[hfix i hi]`. Use `prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩` and prove the remaining obligations. Rewrite using `[← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]`. Establish `: i = ⟨k, hk⟩` using `Fin.ext hi`.

Rewrite using `[this]`. Conclude with `hmx`. Conclude with `⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩`.
-/
theorem exists_fix (hG : IsHermForm c G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hermE c G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      ∀ i : Fin n, i.val < k → ((l.map fun p => refl c G p.1 p.2).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isUnE_mul (isUnE_prod hG l hl) hγ
      set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

end GlobalTheory.UnRep.ReflGen

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G hG γ hγ`. Take `⟨x, h1, h2, h3⟩` from `GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian F E c n G hG`. Take `⟨l, hl, hfix⟩` from `ReflGen.exists_fix hG hγ x h1 h2 n`. Take `⟨l', hl', hinv⟩` from `ReflGen.exists_inv hG l hl`. Use `⟨l', hl', ?_⟩` and prove the remaining obligations.

Establish `hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext_on_range h3 fun i => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]`. Rewrite using `[← one_mul γ, ← hinv, mul_assoc, hone, mul_one]`.
-/
theorem GlobalTheory.UnRep.isUnE_eq_prod_refl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  intro F E _ _ _ _ _ c n G hG γ hγ
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian F E c n G hG
  obtain ⟨l, hl, hfix⟩ := ReflGen.exists_fix hG hγ x h1 h2 n
  obtain ⟨l', hl', hinv⟩ := ReflGen.exists_inv hG l hl
  refine ⟨l', hl', ?_⟩
  have hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range h3 fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
  rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
