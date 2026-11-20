import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset

namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

abbrev Co (r : ℕ) := (Fin r → ℂ) × (Fin r → ℂ) × ℂ × ℂ

def cvec (k : ℕ) {r : ℕ} (z' ν' : Fin (2 * r + k + 1) → ℂ) (c : Co r) : Fin (2 * r + k + 1) → ℂ :=
  (∑ a, c.1 a • ee k r a) + (∑ a, c.2.1 a • es k r a) + c.2.2.1 • z' + c.2.2.2 • ν'

def hco {r : ℕ} (T' : ℝ) (c d : Co r) : ℂ :=
  (∑ a, c.1 a * conj (d.2.1 a)) + (∑ a, c.2.1 a * conj (d.1 a)) - (T' : ℂ) * c.2.2.1 * conj d.2.2.1 +
    c.2.2.2 * conj d.2.2.2

section lin

variable {r : ℕ} (T' : ℝ)

/- English proof (translation)
Simplify using `only [hco, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_add_left (c c' d : Co r) : hco T' (c + c') d = hco T' c d + hco T' c' d := by
  simp only [hco, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

/- English proof (translation)
Simplify using `only [hco, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_add_right (c d d' : Co r) : hco T' c (d + d') = hco T' c d + hco T' c d' := by
  simp only [hco, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

/- English proof (translation)
Simplify using `only [hco, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_sub_left (c c' d : Co r) : hco T' (c - c') d = hco T' c d - hco T' c' d := by
  simp only [hco, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Simplify using `only [hco, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_sub_right (c d d' : Co r) : hco T' c (d - d') = hco T' c d - hco T' c d' := by
  simp only [hco, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Simplify using `only [hco, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]`. Establish `e1 : ∑ a, x * c.1 a * conj (d.2.1 a) = x * ∑ a, c.1 a * conj (d.2.1 a)`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`. Establish `e2 : ∑ a, x * c.2.1 a * conj (d.1 a) = x * ∑ a, c.2.1 a * conj (d.1 a)`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_smul_left (x : ℂ) (c d : Co r) : hco T' (x • c) d = x * hco T' c d := by
  simp only [hco, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ a, x * c.1 a * conj (d.2.1 a) = x * ∑ a, c.1 a * conj (d.2.1 a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ a, x * c.2.1 a * conj (d.1 a) = x * ∑ a, c.2.1 a * conj (d.1 a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  ring

/- English proof (translation)
Simplify using `only [hco, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]`. Establish `e1 : ∑ a, c.1 a * (conj x * conj (d.2.1 a)) = conj x * ∑ a, c.1 a * conj (d.2.1 a)`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`. Establish `e2 : ∑ a, c.2.1 a * (conj x * conj (d.1 a)) = conj x * ∑ a, c.2.1 a * conj (d.1 a)`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_smul_right (x : ℂ) (c d : Co r) : hco T' c (x • d) = conj x * hco T' c d := by
  simp only [hco, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]
  have e1 : ∑ a, c.1 a * (conj x * conj (d.2.1 a)) = conj x * ∑ a, c.1 a * conj (d.2.1 a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ a, c.2.1 a * (conj x * conj (d.1 a)) = conj x * ∑ a, c.2.1 a * conj (d.1 a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  ring

/- English proof (translation)
Use `Finset.induction_on s (by simp [hco]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hco_add_left, ih]`.
-/
theorem hco_sum_left {ι : Type*} (s : Finset ι) (f : ι → Co r) (d : Co r) :
    hco T' (∑ i ∈ s, f i) d = ∑ i ∈ s, hco T' (f i) d := by
  classical
  refine Finset.induction_on s (by simp [hco]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hco_add_left, ih]

/- English proof (translation)
Use `Finset.induction_on s (by simp [hco]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hco_add_right, ih]`.
-/
theorem hco_sum_right {ι : Type*} (s : Finset ι) (c : Co r) (f : ι → Co r) :
    hco T' c (∑ i ∈ s, f i) = ∑ i ∈ s, hco T' c (f i) := by
  classical
  refine Finset.induction_on s (by simp [hco]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hco_add_right, ih]

/- English proof (translation)
Simplify using `only [hco, map_add, map_sub, map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal]`. Establish `e1 : ∑ a, d.1 a * conj (c.2.1 a) = ∑ a, conj (c.2.1 a) * d.1 a` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `e2 : ∑ a, d.2.1 a * conj (c.1 a) = ∑ a, conj (c.1 a) * d.2.1 a` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hco_symm (c d : Co r) : hco T' d c = conj (hco T' c d) := by
  simp only [hco, map_add, map_sub, map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal]
  have e1 : ∑ a, d.1 a * conj (c.2.1 a) = ∑ a, conj (c.2.1 a) * d.1 a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have e2 : ∑ a, d.2.1 a * conj (c.1 a) = ∑ a, conj (c.1 a) * d.2.1 a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e1, e2]
  ring

end lin

section vec

variable {k r : ℕ} {z' ν' : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Simplify using `only [cvec, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem cvec_add (c d : Co r) : cvec k z' ν' (c + d) = cvec k z' ν' c + cvec k z' ν' d := by
  simp only [cvec, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Simplify using `only [cvec, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_add]`.
-/
theorem cvec_smul (x : ℂ) (c : Co r) : cvec k z' ν' (x • c) = x • cvec k z' ν' c := by
  simp only [cvec, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_add]

/- English proof (translation)
Simplify using `only [cvec, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem cvec_sub (c d : Co r) : cvec k z' ν' (c - d) = cvec k z' ν' c - cvec k z' ν' d := by
  simp only [cvec, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  abel

/- English proof (translation)
Use `Finset.induction_on s (by simp [cvec]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, cvec_add, ih]`.
-/
theorem cvec_sum {ι : Type*} (s : Finset ι) (f : ι → Co r) :
    cvec k z' ν' (∑ i ∈ s, f i) = ∑ i ∈ s, cvec k z' ν' (f i) := by
  classical
  refine Finset.induction_on s (by simp [cvec]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, cvec_add, ih]

/- English proof (translation)
Establish `hH : ∀ i j, conj (Hpk k r j i) = Hpk k r i j`. Introduce `i j`. Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`. Establish `hsym : ∀ v w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v w = conj (herm (Hpk k r) w v)`.

Introduce `v w`. Simplify using `only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, Complex.star_def, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hH j i]`.

Expand and normalize the polynomial expressions, which then agree. Establish `a1 : ∀ v v' w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) (v + v') w = herm (Hpk k r) v w + herm (Hpk k r) v' w`. Introduce `v v' w`. Simplify using `only [herm, Matrix.mulVec_add, dotProduct_add]`. Establish `s1 : ∀ (x : ℂ) (v w : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (x • v) w = x * herm (Hpk k r) v w`.

Introduce `x v w`. Simplify using `only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `a2 : ∀ v w w' : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (w + w') = herm (Hpk k r) v w + herm (Hpk k r) v w'`. Introduce `v w w'`. Rewrite using `[hsym, a1, map_add, ← hsym, ← hsym]`.

Establish `s2 : ∀ (x : ℂ) (v w : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) v (x • w) = conj x * herm (Hpk k r) v w`. Introduce `x v w`. Rewrite using `[hsym, s1, map_mul, ← hsym]`. Establish `m1 : ∀ (f : Fin r → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (∑ a, f a) w = ∑ a, herm (Hpk k r) (f a) w` using `fun f w => map_sum (AddMonoidHom.mk' (fun v => herm (Hpk k r) v w) fun v v' => a1 v v' w) f Finset.univ`. Establish `m2 : ∀ (v : Fin (2 * r + k + 1) → ℂ) (f : Fin r → Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) v (∑ a, f a) = ∑ a, herm (Hpk k r) v (f a)` using `fun v f => map_sum (AddMonoidHom.mk' (fun w => herm (Hpk k r) v w) fun w w' => a2 v w w') f Finset.univ`.

Establish `hmv : ∀ p : Fin (2 * r + k + 1), Hpk k r *ᵥ Pi.single p (1 : ℂ) = fun i => Hpk k r i p`. Introduce `p`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hst : ∀ q : Fin (2 * r + k + 1), star (Pi.single q (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = (Pi.single q (1 : ℂ) : Fin (2 * r + k + 1) → ℂ)`.

Apply the tactic sequence `intro q; ext i; by_cases h : i = q <;> simp [Pi.single_apply, h]`. Establish `hsing : ∀ p q : Fin (2 * r + k + 1), herm (Hpk k r) (Pi.single p 1) (Pi.single q 1) = Hpk k r q p`. Introduce `p q`. Simplify using `only [herm, hmv, hst]`. Simplify using `[dotProduct, Pi.single_apply]`.

Establish `hpw : ∀ (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ), (p.val < r ∨ r + k < p.val) → inWb k r w → herm (Hpk k r) (Pi.single p 1) w = 0`. Introduce `p w hp hw`. Simplify using `only [herm, hmv, dotProduct, Pi.star_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`.

Rewrite using `[hw i hi]`. Simplify using the standard rewrite rules. Establish `h0 : Hpk k r i p = 0`. Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`.

Rewrite using `[h0, mul_zero]`. Establish `hpw' : ∀ (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ), (p.val < r ∨ r + k < p.val) → inWb k r w → herm (Hpk k r) w (Pi.single p 1) = 0`. Introduce `p w hp hw`. Rewrite using `[hsym, hpw p w hp hw, map_zero]`. Establish `hEe : ∀ a : Fin r, ee k r a = Pi.single ⟨a.val, by have` using `a.isLt; omega⟩ 1 := fun a => rfl`.

Establish `hEs : ∀ a : Fin r, es k r a = Pi.single ⟨2 * r + k - a.val, by have` using `a.isLt; omega⟩ 1 := fun a => rfl`. Establish `hee : ∀ a b : Fin r, herm (Hpk k r) (ee k r a) (ee k r b) = 0`. Introduce `a b`. Rewrite using `[hEe, hEe, hsing]`. Use `a.isLt` as an intermediate fact.

Use `b.isLt` as an intermediate fact. Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`. Establish `hss : ∀ a b : Fin r, herm (Hpk k r) (es k r a) (es k r b) = 0`. Introduce `a b`.

Rewrite using `[hEs, hEs, hsing]`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`.

Establish `hes : ∀ a b : Fin r, herm (Hpk k r) (ee k r a) (es k r b) = if a = b then 1 else 0`. Introduce `a b`. Rewrite using `[hEe, hEs, hsing]`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact.

Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`. Establish `hse : ∀ a b : Fin r, herm (Hpk k r) (es k r a) (ee k r b) = if a = b then 1 else 0`. Introduce `a b`. Rewrite using `[hEs, hEe, hsing]`.

Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Simplify using `only [Hpk, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp`. Establish `hez : ∀ (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → herm (Hpk k r) (ee k r a) w = 0 ∧ herm (Hpk k r) w (ee k r a) = 0 ∧ herm (Hpk k r) (es k r a) w = 0 ∧ herm (Hpk k r) w (es k r a) = 0`.

Introduce `a w hw`. Establish `ha` using `a.isLt`. Establish `hb : r + k < 2 * r + k - a.val` using `by omega`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hEe]`.

Conclude with `hpw _ w (Or.inl ha) hw`. Rewrite using `[hEe]`. Conclude with `hpw' _ w (Or.inl ha) hw`. Rewrite using `[hEs]`. Conclude with `hpw _ w (Or.inr hb) hw`.

Rewrite using `[hEs]`. Conclude with `hpw' _ w (Or.inr hb) hw`. Establish `hz1 : ∀ a, herm (Hpk k r) (ee k r a) z' = 0` using `fun a => (hez a z' hz').1`. Establish `hz2 : ∀ a, herm (Hpk k r) z' (ee k r a) = 0` using `fun a => (hez a z' hz').2.1`. Establish `hz3 : ∀ a, herm (Hpk k r) (es k r a) z' = 0` using `fun a => (hez a z' hz').2.2.1`.

Establish `hz4 : ∀ a, herm (Hpk k r) z' (es k r a) = 0` using `fun a => (hez a z' hz').2.2.2`. Establish `hn1 : ∀ a, herm (Hpk k r) (ee k r a) ν' = 0` using `fun a => (hez a ν' hν).1`. Establish `hn2 : ∀ a, herm (Hpk k r) ν' (ee k r a) = 0` using `fun a => (hez a ν' hν).2.1`. Establish `hn3 : ∀ a, herm (Hpk k r) (es k r a) ν' = 0` using `fun a => (hez a ν' hν).2.2.1`. Establish `hn4 : ∀ a, herm (Hpk k r) ν' (es k r a) = 0` using `fun a => (hez a ν' hν).2.2.2`.

Establish `hzν : herm (Hpk k r) z' ν' = 0` using `by rw [hsym, hνz, map_zero]`. Take `⟨tz, htz⟩ : ∃ t : ℝ, herm (Hpk k r) z' z' = t` from `⟨(herm (Hpk k r) z' z').re, (Complex.conj_eq_iff_re.mp (hsym z' z').symm).symm⟩`. Simplify using `only [cvec, a1, a2, s1, s2, m1, m2, hee, hss, hes, hse, hz1, hz2, hz3, hz4, hn1, hn2, hn3, hn4, hzν, hνz, hνν, htz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_one, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [hco, Tz, htz, Complex.ofReal_re, Complex.ofReal_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_cvec (hz' : inWb k r z') (hν : inWb k r ν') (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (c d : Co r) :
    herm (Hpk k r) (cvec k z' ν' c) (cvec k z' ν' d) = hco (Tz k r z') c d := by
  have hH : ∀ i j, conj (Hpk k r j i) = Hpk k r i j := by
    intro i j
    simp only [Hpk, Matrix.of_apply]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
  have hsym : ∀ v w : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) v w = conj (herm (Hpk k r) w v) := by
    intro v w
    simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH j i]
    ring
  have a1 : ∀ v v' w : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (v + v') w = herm (Hpk k r) v w + herm (Hpk k r) v' w := by
    intro v v' w; simp only [herm, Matrix.mulVec_add, dotProduct_add]
  have s1 : ∀ (x : ℂ) (v w : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (x • v) w = x * herm (Hpk k r) v w := by
    intro x v w; simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have a2 : ∀ v w w' : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) v (w + w') = herm (Hpk k r) v w + herm (Hpk k r) v w' := by
    intro v w w'; rw [hsym, a1, map_add, ← hsym, ← hsym]
  have s2 : ∀ (x : ℂ) (v w : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (x • w) = conj x * herm (Hpk k r) v w := by
    intro x v w; rw [hsym, s1, map_mul, ← hsym]
  have m1 : ∀ (f : Fin r → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ a, f a) w = ∑ a, herm (Hpk k r) (f a) w := fun f w =>
    map_sum (AddMonoidHom.mk' (fun v => herm (Hpk k r) v w) fun v v' => a1 v v' w) f Finset.univ
  have m2 : ∀ (v : Fin (2 * r + k + 1) → ℂ) (f : Fin r → Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (∑ a, f a) = ∑ a, herm (Hpk k r) v (f a) := fun v f =>
    map_sum (AddMonoidHom.mk' (fun w => herm (Hpk k r) v w) fun w w' => a2 v w w') f Finset.univ
  have hmv : ∀ p : Fin (2 * r + k + 1), Hpk k r *ᵥ Pi.single p (1 : ℂ) = fun i => Hpk k r i p := by
    intro p; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hst : ∀ q : Fin (2 * r + k + 1),
      star (Pi.single q (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = (Pi.single q (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) := by
    intro q; ext i; by_cases h : i = q <;> simp [Pi.single_apply, h]
  have hsing : ∀ p q : Fin (2 * r + k + 1),
      herm (Hpk k r) (Pi.single p 1) (Pi.single q 1) = Hpk k r q p := by
    intro p q; simp only [herm, hmv, hst]; simp [dotProduct, Pi.single_apply]
  have hpw : ∀ (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ), (p.val < r ∨ r + k < p.val) →
      inWb k r w → herm (Hpk k r) (Pi.single p 1) w = 0 := by
    intro p w hp hw
    simp only [herm, hmv, dotProduct, Pi.star_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hw i hi]; simp
    · have h0 : Hpk k r i p = 0 := by
        simp only [Hpk, Matrix.of_apply]
        split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
      rw [h0, mul_zero]
  have hpw' : ∀ (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ), (p.val < r ∨ r + k < p.val) →
      inWb k r w → herm (Hpk k r) w (Pi.single p 1) = 0 := by
    intro p w hp hw; rw [hsym, hpw p w hp hw, map_zero]
  have hEe : ∀ a : Fin r, ee k r a = Pi.single ⟨a.val, by have := a.isLt; omega⟩ 1 := fun a => rfl
  have hEs : ∀ a : Fin r, es k r a = Pi.single ⟨2 * r + k - a.val, by have := a.isLt; omega⟩ 1 :=
    fun a => rfl
  have hee : ∀ a b : Fin r, herm (Hpk k r) (ee k r a) (ee k r b) = 0 := by
    intro a b; rw [hEe, hEe, hsing]; have := a.isLt; have := b.isLt
    simp only [Hpk, Matrix.of_apply]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
  have hss : ∀ a b : Fin r, herm (Hpk k r) (es k r a) (es k r b) = 0 := by
    intro a b; rw [hEs, hEs, hsing]; have := a.isLt; have := b.isLt
    simp only [Hpk, Matrix.of_apply]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
  have hes : ∀ a b : Fin r, herm (Hpk k r) (ee k r a) (es k r b) = if a = b then 1 else 0 := by
    intro a b; rw [hEe, hEs, hsing]; have := a.isLt; have := b.isLt
    simp only [Hpk, Matrix.of_apply]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
  have hse : ∀ a b : Fin r, herm (Hpk k r) (es k r a) (ee k r b) = if a = b then 1 else 0 := by
    intro a b; rw [hEs, hEe, hsing]; have := a.isLt; have := b.isLt
    simp only [Hpk, Matrix.of_apply]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | omega | rfl | simp
  have hez : ∀ (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ), inWb k r w →
      herm (Hpk k r) (ee k r a) w = 0 ∧ herm (Hpk k r) w (ee k r a) = 0 ∧
        herm (Hpk k r) (es k r a) w = 0 ∧ herm (Hpk k r) w (es k r a) = 0 := by
    intro a w hw
    have ha := a.isLt
    have hb : r + k < 2 * r + k - a.val := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEe]; exact hpw _ w (Or.inl ha) hw
    · rw [hEe]; exact hpw' _ w (Or.inl ha) hw
    · rw [hEs]; exact hpw _ w (Or.inr hb) hw
    · rw [hEs]; exact hpw' _ w (Or.inr hb) hw
  have hz1 : ∀ a, herm (Hpk k r) (ee k r a) z' = 0 := fun a => (hez a z' hz').1
  have hz2 : ∀ a, herm (Hpk k r) z' (ee k r a) = 0 := fun a => (hez a z' hz').2.1
  have hz3 : ∀ a, herm (Hpk k r) (es k r a) z' = 0 := fun a => (hez a z' hz').2.2.1
  have hz4 : ∀ a, herm (Hpk k r) z' (es k r a) = 0 := fun a => (hez a z' hz').2.2.2
  have hn1 : ∀ a, herm (Hpk k r) (ee k r a) ν' = 0 := fun a => (hez a ν' hν).1
  have hn2 : ∀ a, herm (Hpk k r) ν' (ee k r a) = 0 := fun a => (hez a ν' hν).2.1
  have hn3 : ∀ a, herm (Hpk k r) (es k r a) ν' = 0 := fun a => (hez a ν' hν).2.2.1
  have hn4 : ∀ a, herm (Hpk k r) ν' (es k r a) = 0 := fun a => (hez a ν' hν).2.2.2
  have hzν : herm (Hpk k r) z' ν' = 0 := by rw [hsym, hνz, map_zero]
  obtain ⟨tz, htz⟩ : ∃ t : ℝ, herm (Hpk k r) z' z' = t :=
    ⟨(herm (Hpk k r) z' z').re, (Complex.conj_eq_iff_re.mp (hsym z' z').symm).symm⟩
  simp only [cvec, a1, a2, s1, s2, m1, m2, hee, hss, hes, hse, hz1, hz2, hz3, hz4, hn1, hn2, hn3, hn4,
    hzν, hνz, hνν, htz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_one, mul_ite,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hco, Tz, htz, Complex.ofReal_re, Complex.ofReal_neg]
  ring

end vec

section formulas

variable {r : ℕ} (T T' : ℝ) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)

def kap : Fin (r + 1) → ℂ := fun b => Zm.adjugate b (Fin.last r)

def nk : ℝ := ∑ b, Complex.normSq (kap Zm b)

def ph : ℂ := Zm.det / ((‖Zm.det‖ : ℝ) : ℂ)

def sGT : ℝ := Real.sqrt (gPoly (T * T') Zm / T)

def sGT' : ℝ := Real.sqrt (gPoly (T * T') Zm / T')

def al (b : Fin (r + 1)) : ℂ := -(Zm (Fin.last r) b) / ((Real.sqrt (T * T') : ℝ) : ℂ)

def be (b : Fin (r + 1)) : ℂ := conj (kap Zm b) / ((nk Zm : ℝ) : ℂ) * ((sGT T T' Zm : ℝ) : ℂ) * ph Zm

def Heta (b c : Fin (r + 1)) : ℂ :=
  -((T' : ℝ) : ℂ) * al T T' Zm b * conj (al T T' Zm c) + be T T' Zm b * conj (be T T' Zm c)

def Ap (b c : Fin (r + 1)) : ℂ := if b = Fin.last r ∧ c = Fin.last r then -((T' : ℝ) : ℂ) else 0

def Rm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun c b => Ap T' b c - Heta T T' Zm b c

def Qm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun c b => kap Zm c * conj (kap Zm b) / ((nk Zm : ℝ) : ℂ)

def Pm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := 1 - Qm Zm

def Km : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (1 / 2 : ℂ) • (Pm Zm * Rm T T' Zm * Pm Zm) + Pm Zm * Rm T T' Zm * Qm Zm

def Mf : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := (Zm⁻¹)ᴴ * Km T T' Zm

def xco (b : Fin (r + 1)) : Co r :=
  (fun a => Mf T T' Zm a.castSucc b, fun a => Zm a.castSucc b, al T T' Zm b, be T T' Zm b)

def fco (a : Fin (r + 1)) : Co r :=
  (fun a' => if a = a'.castSucc then 1 else 0, 0, if a = Fin.last r then ((Real.sqrt (T / T') : ℝ) : ℂ) else 0, 0)

def y0 (b : Fin r) : Co r := ∑ a, (Zm⁻¹)ᴴ a b.castSucc • fco T T' a

def ysco (b : Fin r) : Co r :=
  y0 T T' Zm b - (1 / 2 : ℂ) • ∑ c : Fin r, hco T' (y0 T T' Zm b) (y0 T T' Zm c) • xco T T' Zm c.castSucc

def cofco : Co r := ∑ a, conj (Zm.adjugate (Fin.last r) a) • fco T T' a

def pco : Co r :=
  cofco T T' Zm - (∑ c : Fin r, hco T' (cofco T T' Zm) (ysco T T' Zm c) • xco T T' Zm c.castSucc) -
    (∑ b : Fin r, hco T' (cofco T T' Zm) (xco T T' Zm b.castSucc) • ysco T T' Zm b) +
    (hco T' (cofco T T' Zm) (xco T T' Zm (Fin.last r)) / ((T' : ℝ) : ℂ)) • xco T T' Zm (Fin.last r)

def nco : Co r := (ph Zm / ((sGT' T T' Zm : ℝ) : ℂ)) • pco T T' Zm

end formulas

section images

variable {k r : ℕ}

def Yv (z' ν' : Fin (2 * r + k + 1) → ℂ) (T T' : ℝ) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => cvec k z' ν' (xco T T' Zm b.castSucc)
  | Sum.inl (Sum.inr b) => cvec k z' ν' (ysco T T' Zm b)
  | Sum.inr j => ![cvec k z' ν' (xco T T' Zm (Fin.last r)), cvec k z' ν' (nco T T' Zm)] j

def secM (z' ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (T T' : ℝ)
    (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : B.Mat k r :=
  m₀ * smat (Hpk k r) (uB z' ν') (wB z' ν' (Real.sqrt T')) (Yv z' ν' T T' Zm)

end images

end

end Formalism.FourierDecayAlt.P.PBI
