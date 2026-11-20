import Mathlib

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev gl (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev U (n : ℕ) := UniversalEnvelopingAlgebra ℂ (gl n)

variable {n : ℕ}

def E (a : Fin n × Fin n) : gl n := Matrix.single a.1 a.2 1

noncomputable def e (a : Fin n × Fin n) : U n := UniversalEnvelopingAlgebra.ι ℂ (E a)

noncomputable def word (w : List (Fin n × Fin n)) : U n := (w.map e).prod

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem word_nil : word ([] : List (Fin n × Fin n)) = 1 := rfl

/- English proof (translation)
Simplify using `[word]`.
-/
@[simp] theorem word_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    word (a :: w) = e a * word w := by
  simp [word]

/- English proof (translation)
Simplify using `[word]`.
-/
@[simp] theorem word_append (v w : List (Fin n × Fin n)) : word (v ++ w) = word v * word w := by
  simp [word]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem word_singleton (a : Fin n × Fin n) : word [a] = e a := by simp

/- English proof (translation)
Take `⟨i, j⟩` from `a`. Take `⟨k, l⟩` from `b`. Simplify using `only [E]`. Use `congr 1`. Distinguish the cases in `h : j = k`.

Substitute `h` using the available equality. Simplify using `[Matrix.single_mul_single_same]`. Simplify using `[h, Matrix.single_mul_single_of_ne (h := h)]`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality.

Simplify using `[Matrix.single_mul_single_same]`. Simplify using `[h, Matrix.single_mul_single_of_ne (h := h)]`.
-/
theorem E_mul_sub_mul (a b : Fin n × Fin n) :
    E a * E b - E b * E a =
      (if a.2 = b.1 then E (a.1, b.2) else 0) - (if b.2 = a.1 then E (b.1, a.2) else 0) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨k, l⟩ := b
  simp only [E]
  congr 1
  · by_cases h : j = k
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]
  · by_cases h : l = i
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]

/- English proof (translation)
Establish `h` using `congrArg (UniversalEnvelopingAlgebra.ι ℂ (L := gl n)) (E_mul_sub_mul a b)`. Rewrite `h` using `[← LieRing.of_associative_ring_bracket, LieHom.map_lie, LieRing.of_associative_ring_bracket]`. Simplify using `only [e] at h ⊢`. Rewrite using `[h, map_sub]`. Apply the tactic sequence `congr 1 <;> split_ifs <;> simp`.
-/
theorem e_mul_sub_mul (a b : Fin n × Fin n) :
    e a * e b - e b * e a =
      (if a.2 = b.1 then e (a.1, b.2) else 0) - (if b.2 = a.1 then e (b.1, a.2) else 0) := by
  have h := congrArg (UniversalEnvelopingAlgebra.ι ℂ (L := gl n)) (E_mul_sub_mul a b)
  rw [← LieRing.of_associative_ring_bracket, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    at h
  simp only [e] at h ⊢
  rw [h, map_sub]
  congr 1 <;> split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [E, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Rewrite using `[Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem eq_sum_E (X : gl n) : X = ∑ a : Fin n × Fin n, X a.1 a.2 • E a := by
  ext i j
  simp only [E, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_E X]`. Simplify using `[e, map_sum, map_smul]`.
-/
theorem ι_eq_sum_e (X : gl n) :
    UniversalEnvelopingAlgebra.ι ℂ X = ∑ a : Fin n × Fin n, X a.1 a.2 • e (n := n) a := by
  conv_lhs => rw [eq_sum_E X]
  simp [e, map_sum, map_smul]

/- English proof (translation)
Take `⟨t, rfl⟩` from `Quotient.exists_rep u`. Use `show C (UniversalEnvelopingAlgebra.mkAlgHom ℂ (gl n) t)`. Proceed by induction on `t using TensorAlgebra.induction with`. Consider the case `algebraMap r => rw [AlgHom.commutes]`. Conclude with `halg r`.

Consider the case `ι x => exact hι x`. Consider the case `mul a b ha hb => rw [map_mul]`. Conclude with `hmul _ _ ha hb`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `hadd _ _ ha hb`.
-/
theorem U.induction {C : U n → Prop}
    (halg : ∀ r : ℂ, C (algebraMap ℂ _ r)) (hι : ∀ x, C (UniversalEnvelopingAlgebra.ι ℂ x))
    (hmul : ∀ a b, C a → C b → C (a * b)) (hadd : ∀ a b, C a → C b → C (a + b))
    (u : U n) : C u := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep u
  show C (UniversalEnvelopingAlgebra.mkAlgHom ℂ (gl n) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

/- English proof (translation)
Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `u`. Proceed by induction on `u using U.induction with`. Consider the case `halg r => exact Algebra.commutes r z`. Consider the case `hι X`.

Rewrite using `[ι_eq_sum_e, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, mul_smul_comm, hz]`. Consider the case `hmul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]`. Consider the case `hadd a b ha hb => rw [add_mul, mul_add, ha, hb]`.
-/
theorem mem_center_of_commute_e {z : U n} (hz : ∀ a, e a * z = z * e a) :
    z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  induction u using U.induction with
  | halg r => exact Algebra.commutes r z
  | hι X =>
    rw [ι_eq_sum_e, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, mul_smul_comm, hz]
  | hmul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]

end GroundTheory.Automorphic.HarishChandra
