import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLListPropertiesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `cons hab _ ih`. Simplify using `only [deg, List.map_cons, List.sum_cons] at ih ⊢`. Rewrite using `[hab.1, ih]`.
-/
theorem deg_of_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    deg L₁ = deg L₂ := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [deg, List.map_cons, List.sum_cons] at ih ⊢
    rw [hab.1, ih]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `@cons a b l₁ l₂ hab hl ih`. Use function extensionality and compare the values at `n`. Take `⟨a1, a2⟩` from `a`.

Take `⟨b1, b2⟩` from `b`. Take `⟨h1, h2⟩` from `hab`. Simplify using `only at h1 h2`. Substitute `h1` using the available equality. Rewrite using `[J_cons, J_cons, ih, deg_of_forall₂ θ hl]`.

Simplify using `only [h2]`.
-/
theorem J_congr_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    J θ L₁ = J θ L₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁ l₂ hab hl ih =>
    funext n
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    rw [J_cons, J_cons, ih, deg_of_forall₂ θ hl]
    simp only [h2]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Simplify using `only [List.flatMap_cons]`. Conclude with `List.rel_append (h a (by simp)) (ih fun p hp => h p (by simp [hp]))`.
-/
theorem forall₂_flatMap_of {α β : Type} (R : β → β → Prop) (L : List α) (f g : α → List β)
    (h : ∀ p ∈ L, List.Forall₂ R (f p) (g p)) : List.Forall₂ R (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun p hp => h p (by simp [hp]))

/- English proof (translation)
Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Use `letI := Fintype.ofFinite F`. Use `letI := Fintype.ofFinite F'`. Use `haveI : CharP F (ringChar F) := ringChar.charP F`. Take `⟨r, hp, hcard⟩` from `FiniteField.card F (ringChar F)`.

Establish `hchar : ringChar F' = ringChar F` using `(Algebra.ringChar_eq F F').symm`. Establish `hq : Nat.card F = ringChar F' ^ (r : ℕ)` using `by rw [Nat.card_eq_fintype_card, hcard, hchar]`. Use function extensionality and compare the values at `x`. Establish `key` using `GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ (RingEquiv.refl F') (r * Module.finrank F F') (fun y => by`. Rewrite using `[pow_mul, ← hq, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, FiniteField.pow_card]`.

Use the proof step `rfl) m K x`. Rewrite using `[hq, ← pow_mul, ← key]`. Use `congr 1`.
-/
theorem cusp_mul_card_pow (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (m K : ℕ) :
    cusp θ m (K * Nat.card F ^ Module.finrank F F') = cusp θ m K := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite F'
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  funext x
  have key := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ (RingEquiv.refl F') (r * Module.finrank F F') (fun y => by
    rw [pow_mul, ← hq, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
    rfl) m K x
  rw [hq, ← pow_mul, ← key]
  congr 1

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Use `haveI : CharP F (ringChar F) := ringChar.charP F`. Take `⟨r, hp, hcard⟩` from `FiniteField.card F (ringChar F)`. Establish `hchar : ringChar F' = ringChar F` using `(Algebra.ringChar_eq F F').symm`. Establish `hq : Nat.card F = ringChar F' ^ (r : ℕ)` using `by rw [Nat.card_eq_fintype_card, hcard, hchar]`. Use `set q := Nat.card F with hqdef`.

Use `set l := Module.finrank F F' with hldef`. Establish `hl : 0 < l` using `Module.finrank_pos`. Take `⟨l', hl'⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Establish `key` using `GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow F' θ (FiniteField.frobeniusAlgEquivOfAlgebraic F F').toRingEquiv r (fun y => by`. Rewrite using `[← hq]`.

Use `show (FiniteField.frobeniusAlgEquivOfAlgebraic F F') y = _`. Rewrite using `[FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hqdef, Nat.card_eq_fintype_card]) (liftL q l L) n x`. Rewrite using `[galAct_apply]`. Use `(key.trans ?_)` and prove the remaining obligations. Rewrite using `[← hq]`.

Use `set R : List (ℕ × ℕ) := L.flatMap fun p => (List.range l').map (fun i => (p.1 / l, p.2 * q ^ (i + 1))) ++ [(p.1 / l, p.2)] with hR`. Establish `hF : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) ((liftL q l L).map fun p => (p.1, p.2 * q)) R`. Rewrite using `[liftL, List.map_flatMap, hR]`. Apply `forall₂_flatMap_of` to reduce the goal to its premises. Introduce `p _`.

Rewrite using `[hl', List.range_succ, List.map_append, List.map_append]`. Simplify using `only [List.map_map, List.map_cons, List.map_nil]`. Use `List.rel_append ?_ ?_` and prove the remaining obligations. Rewrite using `[List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]`. Introduce `z _`.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, pow_succ, mul_assoc]`. Use `List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[mul_assoc, ← pow_succ, ← hl']`.

Conclude with `cusp_mul_card_pow F F' θ _ _`. Establish `hP : R.Perm (liftL q l L)`. Rewrite using `[liftL, hR]`. Apply `List.Perm.flatMap_left` to reduce the goal to its premises. Introduce `p _`.

Rewrite using `[hl', List.range_succ_eq_map]`. Simplify using `only [List.map_cons, List.map_map, pow_zero, mul_one]`. Use `List.perm_append_comm.trans ?_` and prove the remaining obligations. Simplify using `[Function.comp_def, ← hl']`. Establish `hdeg : deg R = deg (liftL q l L)`.

Unfold `deg`. Conclude with `(hP.map Prod.fst).sum_eq`. Rewrite using `[J_congr_forall₂ θ hF]`. Conclude with `((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ).2.2 R (liftL q l L) n (hn.trans hdeg.symm) hP) ▸ rfl`.
-/
theorem J_liftL_galAct_frob (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) [Fintype F] (L : List (ℕ × ℕ)) (n : ℕ)
    (hn : n = deg (liftL (Nat.card F) (Module.finrank F F') L)) (x : GL (Fin n) F') :
    J θ (liftL (Nat.card F) (Module.finrank F F') L) n
      (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F') x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hl : 0 < l := Module.finrank_pos
  obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have key := GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow F' θ (FiniteField.frobeniusAlgEquivOfAlgebraic F F').toRingEquiv r (fun y => by
    rw [← hq]
    show (FiniteField.frobeniusAlgEquivOfAlgebraic F F') y = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hqdef, Nat.card_eq_fintype_card]) (liftL q l L) n x
  rw [galAct_apply]
  refine (key.trans ?_)
  rw [← hq]

  set R : List (ℕ × ℕ) := L.flatMap fun p =>
    (List.range l').map (fun i => (p.1 / l, p.2 * q ^ (i + 1))) ++ [(p.1 / l, p.2)] with hR
  have hF : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2)
      ((liftL q l L).map fun p => (p.1, p.2 * q)) R := by
    rw [liftL, List.map_flatMap, hR]
    apply forall₂_flatMap_of
    intro p _
    rw [hl', List.range_succ, List.map_append, List.map_append]
    simp only [List.map_map, List.map_cons, List.map_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro z _
      refine ⟨rfl, ?_⟩
      simp only [Function.comp_apply, pow_succ, mul_assoc]
    · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      simp only [Function.comp_apply]
      rw [mul_assoc, ← pow_succ, ← hl']
      exact cusp_mul_card_pow F F' θ _ _
  have hP : R.Perm (liftL q l L) := by
    rw [liftL, hR]
    apply List.Perm.flatMap_left
    intro p _
    rw [hl', List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, mul_one]
    refine List.perm_append_comm.trans ?_
    simp [Function.comp_def, ← hl']
  have hdeg : deg R = deg (liftL q l L) := by
    unfold deg
    exact (hP.map Prod.fst).sum_eq
  rw [J_congr_forall₂ θ hF]
  exact ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ).2.2 R (liftL q l L) n (hn.trans hdeg.symm) hP) ▸ rfl

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F F' _ _ _ _ θ t L n hn`. Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Use `letI := Fintype.ofFinite F`. Take `⟨i, rfl⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t`. It suffices to establish `h : ∀ k : ℕ, ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ k) x) = J θ (liftL (Nat.card F) (Module.finrank F F') L) n x from h i.1`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `x`. Rewrite using `[pow_succ, map_mul, MulAut.mul_apply, ih]`. Conclude with `J_liftL_galAct_frob F F' θ L n hn x`.
-/
theorem J_liftL_galAct : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ)
    (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) →
    ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  intro F F' _ _ _ _ θ t L n hn
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  suffices h : ∀ k : ℕ, ∀ x : GL (Fin n) F',
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n
        (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ k) x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x from h i.1
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, map_mul, MulAut.mul_apply, ih]
    exact J_liftL_galAct_frob F F' θ L n hn x

end GlobalTheory.Shin
