import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.DepOne

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single (esI k r a)]`. Use `a.isLt` as an intermediate fact. Establish `h1 : (eI k r a).val = a.val` using `rfl`. Establish `h2 : (esI k r a).val = 2 * r + k - a.val` using `rfl`.

Unfold `Hpk`. Rewrite using `[if_pos (by omega), one_mul]`. Introduce `l _ hl`. Establish `hl' : l.val ≠ 2 * r + k - a.val` using `fun h => hl (Fin.ext h)`. Use `a.isLt` as an intermediate fact.

Simplify using `only [Hpk, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`. Simplify using the standard rewrite rules.
-/
theorem Hpk_mulVec_e {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold Hpk
    rw [if_pos (by omega), one_mul]
  · intro l _ hl
    have hl' : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext h)
    have := a.isLt
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Establish `h1 : (eI k r a).val = a.val` using `rfl`. Establish `h2 : (esI k r b).val = 2 * r + k - b.val` using `rfl`. Unfold `Hpk`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos (by omega), if_pos rfl]`. Establish `hab' : a.val ≠ b.val` using `fun h => hab (Fin.ext h)`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]`.
-/
theorem Hpk_e_es {k r : ℕ} (a b : Fin r) :
    Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold Hpk
  by_cases hab : a = b
  · subst hab
    rw [if_pos (by omega), if_pos rfl]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `a han hab`. Establish `hU : xᴴ * Hpk k r * x = Hpk k r` using `hx.1`.

Establish `h` using `congrFun (congrFun hU (eI k r a)) (esI k r b)`. Rewrite `h` using `[Matrix.mul_assoc, Hpk_e_es]`. Establish `hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) = ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Rewrite `h` using `[hs, Finset.sum_eq_single (eI k r a)]`.

Rewrite `h` using `[Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul]`. Conclude with `h`. Introduce `i _ hi`. Distinguish the cases in `hia : a.val ≤ i.val`. Rewrite using `[hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]`.

Establish `ha` using `a.isLt`. Take `⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c` from `⟨⟨i.val, by omega⟩, Fin.ext rfl⟩`. Establish `hca : c.val < a.val` using `by simpa [eI] using not_le.1 hia`. Rewrite using `[Hpk_mulVec_e]`. Establish `hcb : c ≤ b` using `le_trans (le_of_lt (show c < a from hca)) hab`.

Rewrite using `[ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by`. Substitute `h` using the available equality. Conclude with `absurd hab (not_le.2 hca)), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem es_es {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r)
    (b : Fin r) : ∀ (n : ℕ) (a : Fin r), a.val = n → a ≤ b →
      x (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a han hab
  have hU : xᴴ * Hpk k r * x = Hpk k r := hx.1
  have h := congrFun (congrFun hU (eI k r a)) (esI k r b)
  rw [Matrix.mul_assoc, Hpk_e_es] at h
  have hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) =
      ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hs, Finset.sum_eq_single (eI k r a)] at h
  · rw [Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul] at h
    exact h
  · intro i _ hi
    by_cases hia : a.val ≤ i.val
    · rw [hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]
    · have ha := a.isLt
      obtain ⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have hca : c.val < a.val := by simpa [eI] using not_le.1 hia
      rw [Hpk_mulVec_e]
      have hcb : c ≤ b := le_trans (le_of_lt (show c < a from hca)) hab
      rw [ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by
        subst h; exact absurd hab (not_le.2 hca)), mul_zero]
  · simp

/- English proof (translation)
Introduce `k r x hx i j hij`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [pos] at hij`.

Distinguish the cases in `hjr : j.val < r`. Apply the tactic sequence `have hji : j.val ≤ i.val := by split_ifs at hij <;> omega`. Establish `e : j = eI k r ⟨j.val, hjr⟩` using `Fin.ext rfl`. Use `hx.2.1 ⟨j.val, hjr⟩ i hji` as an intermediate fact. Rewrite `this` using `[← e]`.

Conclude with `this`. Distinguish the cases in `hjm : j.val ≤ r + k`. Apply the tactic sequence `have hri : r ≤ i.val := by split_ifs at hij <;> omega`. Conclude with `hx.2.2 i j (by omega) hjm hri`. Apply the tactic sequence `have hji : j.val ≤ i.val := by split_ifs at hij <;> omega`.

Establish `hb : 2 * r + k - j.val < r` using `by omega`. Establish `hc : 2 * r + k - i.val < r` using `by omega`. Establish `ej : j = esI k r ⟨2 * r + k - j.val, hb⟩` using `Fin.ext (by simp [esI]; omega)`. Establish `ei : i = esI k r ⟨2 * r + k - i.val, hc⟩` using `Fin.ext (by simp [esI]; omega)`. Establish `key` using `es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl (by rw [Fin.mk_le_mk]; omega)`.

Rewrite `key` using `[← ei, ← ej]`. Rewrite using `[key]`. Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hij', if_neg]`. Introduce `h`. Apply `hij'` to reduce the goal to its premises. Rewrite using `[ei, ej, h]`.
-/
theorem dep_one : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    x ∈ Nset k r → Dep k r 1 (x - 1) := by
  intro k r x hx i j hij
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos] at hij
  by_cases hjr : j.val < r
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
    have := hx.2.1 ⟨j.val, hjr⟩ i hji
    rw [← e] at this
    exact this
  by_cases hjm : j.val ≤ r + k
  · have hri : r ≤ i.val := by split_ifs at hij <;> omega
    exact hx.2.2 i j (by omega) hjm hri
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have hb : 2 * r + k - j.val < r := by omega
    have hc : 2 * r + k - i.val < r := by omega
    have ej : j = esI k r ⟨2 * r + k - j.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    have ei : i = esI k r ⟨2 * r + k - i.val, hc⟩ := Fin.ext (by simp [esI]; omega)
    have key := es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl
      (by rw [Fin.mk_le_mk]; omega)
    rw [← ei, ← ej] at key
    rw [key]
    by_cases hij' : i = j
    · subst hij'; simp
    · rw [if_neg hij', if_neg]
      intro h
      apply hij'
      rw [ei, ej, h]

end GlobalTheory.SnMass.VolN.DepOne
