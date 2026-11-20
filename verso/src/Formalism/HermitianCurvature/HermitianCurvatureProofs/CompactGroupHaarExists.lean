import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL

namespace Formalism.FourierDecayAlt.P.B2x2

/- English proof (translation)
Establish `hsq : Hpk k r * Hpk k r = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`.

Apply the tactic sequence `let m : Fin (2 * r + k + 1) := ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩`. Establish `hm : m.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val` using `rfl`. Rewrite using `[Finset.sum_eq_single m]`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, hm] split_ifs <;> first | omega | norm_num`. Introduce `l _ hl`.

Establish `hl' : l.val ≠ m.val` using `fun h => hl (Fin.ext h)`. Rewrite `hl'` using `[hm]`. Establish `hl2` using `l.isLt`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs at hl' ⊢ <;> first | omega | norm_num`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ m) h`. Establish `h2` using `congrArg Matrix.det hsq`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_one]`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations.

Rewrite `h2` using `[h0, zero_mul]`. Conclude with `zero_ne_one h2`.
-/
theorem hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have hsq : Hpk k r * Hpk k r = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hi := i.isLt
    have hj := j.isLt
    let m : Fin (2 * r + k + 1) :=
      ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
    have hm : m.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := rfl
    rw [Finset.sum_eq_single m]
    · simp only [Hpk, Fin.ext_iff, hm]
      split_ifs <;> first | omega | norm_num
    · intro l _ hl
      have hl' : l.val ≠ m.val := fun h => hl (Fin.ext h)
      rw [hm] at hl'
      have hl2 := l.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hl' ⊢ <;> first | omega | norm_num
    · intro h
      exact absurd (Finset.mem_univ m) h
  have h2 := congrArg Matrix.det hsq
  rw [Matrix.det_mul, Matrix.det_one] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul] at h2
  exact zero_ne_one h2

/- English proof (translation)
Introduce `k r`. Establish `hH : IsUnit (Hpk k r).det` using `hpk_unit k r`. Establish `hdet : ∀ a : Mat k r, aᴴ * Hpk k r * a = Hpk k r → IsUnit a.det`. Introduce `a ha`. Establish `h2` using `congrArg Matrix.det ha`.

Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Use `isUnit_iff_ne_zero.2 fun h0 => hH.ne_zero ?_` and prove the remaining obligations. Rewrite `h2` using `[h0, mul_zero]`. Conclude with `h2.symm`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules. Introduce `a ha b hb`. Express the relevant statement in the definitionally equal form `aᴴ * Hpk k r * a = Hpk k r at ha`. Express the relevant statement in the definitionally equal form `bᴴ * Hpk k r * b = Hpk k r at hb`.

Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [ha, hb]`.

Introduce `a ha`. Express the relevant statement in the definitionally equal form `aᴴ * Hpk k r * a = Hpk k r at ha`. Establish `hu` using `hdet a ha`. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by`. Rewrite using `[Matrix.mul_nonsing_inv a hu]`. Simplify using the standard rewrite rules.

Introduce `a ha`. Conclude with `hdet a ha`. Use `show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
theorem closedG : ClosedG := by
  intro k r
  have hH : IsUnit (Hpk k r).det := hpk_unit k r
  have hdet : ∀ a : Mat k r, aᴴ * Hpk k r * a = Hpk k r → IsUnit a.det := by
    intro a ha
    have h2 := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH.ne_zero ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  · intro a ha b hb
    change aᴴ * Hpk k r * a = Hpk k r at ha
    change bᴴ * Hpk k r * b = Hpk k r at hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha, hb]
  · intro a ha
    change aᴴ * Hpk k r * a = Hpk k r at ha
    have hu := hdet a ha
    show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
    calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by
          rw [Matrix.mul_nonsing_inv a hu]
          simp
  · intro a ha
    exact hdet a ha
  · show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const

/- English proof (translation)
Introduce `k r`. Establish `hG : IsClosedSubgroup (GV k r)` using `closedG k r`. Establish `memU : ∀ y ∈ Nset k r, y ∈ GV k r` using `fun y hy => by`. Take `⟨h, -, -⟩` from `hy`. Conclude with `h`.

Establish `toQ : ∀ y : Mat k r, y ∈ Nset k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y j c = if j = c then 1 else 0)`. Introduce `y hy c hc j hj`. Take `⟨_, h1, h2⟩` from `hy`. Distinguish the cases in `hcr : c.val < r`. Establish `e : eI k r ⟨c.val, hcr⟩ = c` using `Fin.ext rfl`.

Establish `h3` using `h1 ⟨c.val, hcr⟩ j (by show c.val ≤ j.val; omega)`. Rewrite `h3` using `[e]`. Conclude with `h3`. Conclude with `h2 j c (by omega) hc (by omega)`. Establish `ofQ : ∀ y : Mat k r, y ∈ GV k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y j c = if j = c then 1 else 0) → y ∈ Nset k r`.

Introduce `y hyU hQ`. Use `⟨hyU, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Establish `ha` using `a.isLt`. Establish `e : (eI k r a).val = a.val` using `rfl`.

Conclude with `hQ (eI k r a) (by omega) i (by omega)`. Introduce `i j hj1 hj2 hi`. Conclude with `hQ j hj2 i (by omega)`. Establish `mulQ : ∀ y z : Mat k r, (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → z j c = if j = c then 1 else 0) → (∀ …`. Introduce `y z hy hz c hc j hj`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single c]`. Rewrite using `[hy c hc j hj, hz c hc c (by omega)]`. Simplify using the standard rewrite rules. Introduce `l _ hlc`. Distinguish the cases in `hl : min c.val r ≤ l.val`.

Rewrite using `[hz c hc l hl, if_neg hlc, mul_zero]`. Establish `hjl : j ≠ l` using `fun h => by rw [h] at hj; exact hl hj`. Rewrite using `[hy l (by omega) j (by omega), if_neg hjl, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`.

Establish `invQ : ∀ y : Mat k r, IsUnit y.det → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y⁻¹ j c = if j = c then …`. Introduce `y hu hy`. Establish `hx : y⁻¹ * y = 1` using `Matrix.nonsing_inv_mul y hu`. Establish `main : ∀ m : ℕ, ∀ c : Fin (2 * r + k + 1), c.val = m → c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y⁻¹ j c = if j = c then 1 else 0`. Introduce `m`.

Use `Nat.strong_induction_on m ?_` and prove the remaining obligations. Introduce `m ih c hcm hc j hj`. Establish `h1` using `congrFun (congrFun hx j) c`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single c]`. Rewrite `h1` using `[hy c hc c (by omega)]`.

Simplify using `using h1`. Introduce `l _ hlc`. Distinguish the cases in `hl : min c.val r ≤ l.val`. Rewrite using `[hy c hc l hl, if_neg hlc, mul_zero]`. Establish `hjl : j ≠ l` using `fun h => by rw [h] at hj; exact hl hj`.

Rewrite using `[ih l.val (by omega) l rfl (by omega) j (by omega), if_neg hjl, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Introduce `c hc j hj`. Conclude with `main c.val c rfl hc j hj`.

Establish `hc : ∀ (p : Prop) (i j : Fin (2 * r + k + 1)) (v : ℂ), IsClosed {g : Mat k r | p → g i j = v}`. Introduce `p i j v`. Distinguish the cases in `hp : p`. Simplify using `only [hp, true_implies]`. Conclude with `isClosed_eq (continuous_id.matrix_elem i j) continuous_const`.

Simplify using `only [hp, false_implies, Set.setOf_true]`. Conclude with `isClosed_univ`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ofQ 1 hG.one_mem (fun c _ j _ => Matrix.one_apply)`. Introduce `a ha b hb`.

Conclude with `ofQ _ (hG.mul_mem a (memU a ha) b (memU b hb)) (mulQ a b (toQ a ha) (toQ b hb))`. Introduce `a ha`. Conclude with `ofQ _ (hG.inv_mem a (memU a ha)) (invQ a (hG.unit a (memU a ha)) (toQ a ha))`. Introduce `a ha`. Conclude with `hG.unit a (memU a ha)`.

Establish `e : Nset k r = GV k r ∩ ((⋂ a : Fin r, ⋂ i : Fin (2 * r + k + 1), {g : Mat k r | a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩ (⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1), {g : Mat k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then …`. Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `Iff.rfl`. Rewrite using `[e]`.

Use `hG.closed.inter ((isClosed_iInter fun a => isClosed_iInter fun i => hc _ i _ _).inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_))` and prove the remaining obligations. Simplify `hc (r ≤ j.val ∧ j.val ≤ r + k ∧ r ≤ i.val) i j (if i = j then 1 else 0)` using `only [and_imp]`.
-/
theorem closedN : ClosedN := by
  intro k r
  have hG : IsClosedSubgroup (GV k r) := closedG k r
  have memU : ∀ y ∈ Nset k r, y ∈ GV k r := fun y hy => by
    obtain ⟨h, -, -⟩ := hy
    exact h
  have toQ : ∀ y : Mat k r, y ∈ Nset k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) := by
    intro y hy c hc j hj
    obtain ⟨_, h1, h2⟩ := hy
    by_cases hcr : c.val < r
    · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
      have h3 := h1 ⟨c.val, hcr⟩ j (by show c.val ≤ j.val; omega)
      rw [e] at h3
      exact h3
    · exact h2 j c (by omega) hc (by omega)
  have ofQ : ∀ y : Mat k r, y ∈ GV k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → y ∈ Nset k r := by
    intro y hyU hQ
    refine ⟨hyU, ?_, ?_⟩
    · intro a i hai
      have ha := a.isLt
      have e : (eI k r a).val = a.val := rfl
      exact hQ (eI k r a) (by omega) i (by omega)
    · intro i j hj1 hj2 hi
      exact hQ j hj2 i (by omega)
  have mulQ : ∀ y z : Mat k r, (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        z j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        (y * z) j c = if j = c then 1 else 0) := by
    intro y z hy hz c hc j hj
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [hy c hc j hj, hz c hc c (by omega)]
      simp
    · intro l _ hlc
      by_cases hl : min c.val r ≤ l.val
      · rw [hz c hc l hl, if_neg hlc, mul_zero]
      · have hjl : j ≠ l := fun h => by rw [h] at hj; exact hl hj
        rw [hy l (by omega) j (by omega), if_neg hjl, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have invQ : ∀ y : Mat k r, IsUnit y.det → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y⁻¹ j c = if j = c then 1 else 0) := by
    intro y hu hy
    have hx : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hu
    have main : ∀ m : ℕ, ∀ c : Fin (2 * r + k + 1), c.val = m → c.val ≤ r + k →
        ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y⁻¹ j c = if j = c then 1 else 0 := by
      intro m
      refine Nat.strong_induction_on m ?_
      intro m ih c hcm hc j hj
      have h1 := congrFun (congrFun hx j) c
      rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single c] at h1
      · rw [hy c hc c (by omega)] at h1
        simpa using h1
      · intro l _ hlc
        by_cases hl : min c.val r ≤ l.val
        · rw [hy c hc l hl, if_neg hlc, mul_zero]
        · have hjl : j ≠ l := fun h => by rw [h] at hj; exact hl hj
          rw [ih l.val (by omega) l rfl (by omega) j (by omega), if_neg hjl, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ c) h
    intro c hc j hj
    exact main c.val c rfl hc j hj
  have hc : ∀ (p : Prop) (i j : Fin (2 * r + k + 1)) (v : ℂ), IsClosed {g : Mat k r | p → g i j = v} := by
    intro p i j v
    by_cases hp : p
    · simp only [hp, true_implies]
      exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const
    · simp only [hp, false_implies, Set.setOf_true]
      exact isClosed_univ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ofQ 1 hG.one_mem (fun c _ j _ => Matrix.one_apply)
  · intro a ha b hb
    exact ofQ _ (hG.mul_mem a (memU a ha) b (memU b hb)) (mulQ a b (toQ a ha) (toQ b hb))
  · intro a ha
    exact ofQ _ (hG.inv_mem a (memU a ha)) (invQ a (hG.unit a (memU a ha)) (toQ a ha))
  · intro a ha
    exact hG.unit a (memU a ha)
  · have e : Nset k r = GV k r ∩ ((⋂ a : Fin r, ⋂ i : Fin (2 * r + k + 1),
        {g : Mat k r | a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
        (⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
        {g : Mat k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then 1 else 0})) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact Iff.rfl
    rw [e]
    refine hG.closed.inter ((isClosed_iInter fun a => isClosed_iInter fun i => hc _ i _ _).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => ?_))
    simpa only [and_imp] using hc (r ≤ j.val ∧ j.val ≤ r + k ∧ r ≤ i.val) i j (if i = j then 1 else 0)

/- English proof (translation)
Introduce `X _ μ N C d A hN h1 hd hC hdA`. Establish `hSm : ∀ m : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ m}` using `fun m => measurableSet_le hN measurable_const`. Establish `key : ∀ m : ℕ, ((2:ℝ) ^ m / 2) ^ (-A) * ((2:ℝ) ^ m) ^ d = 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m`. Introduce `m`. Establish `e1 : (2:ℝ) ^ m / 2 = (2:ℝ) ^ ((m:ℝ) - 1)`.

Rewrite using `[Real.rpow_sub_one (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]`. Establish `e2 : ((2:ℝ) ^ (d - A)) ^ m = (2:ℝ) ^ ((d - A) * m)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]`. Rewrite using `[e1, e2, ← Real.rpow_natCast (2:ℝ) m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x` using `by filter_upwards [h1] with x hx classical`. Establish `hex : ∃ n : ℕ, N x ≤ (2:ℝ) ^ n`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (N x) (by norm_num : (1:ℝ) < 2)`. Conclude with `⟨n, hn.le⟩`.

Set `m0` to `Nat.find hex`. Establish `hm0 : N x ≤ (2:ℝ) ^ m0` using `Nat.find_spec hex`. Establish `hlow : (2:ℝ) ^ m0 / 2 ≤ N x`. Break down `Nat.eq_zero_or_pos m0 with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn⟩ : ∃ n, m0 = n + 1` from `⟨m0 - 1, by omega⟩`. Establish `hmin` using `Nat.find_min hex (show n < m0 by omega)`. Use `push_neg at hmin`.

Rewrite using `[hn, pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Real.rpow_neg (by linarith), Real.rpow_neg (by positivity), inv_eq_one_div, inv_eq_one_div]`.

Conclude with `one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow (by positivity) hlow (by linarith))`. Use `_ = {x | N x ≤ (2:ℝ) ^ m0}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m0 / 2) ^ (-A))) x := by`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x | N x ≤ (2:ℝ) ^ m0} from hm0)]`. Use `_ ≤ ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x := ENNReal.le_tsum m0`. Establish `hq0 : 0 ≤ (2:ℝ) ^ (d - A)` using `by positivity`.

Establish `hq1 : (2:ℝ) ^ (d - A) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)`. Establish `hsum : Summable fun m : ℕ => |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m` using `(summable_geometric_of_lt_one hq0 hq1).mul_left _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_tsum fun m => (measurable_const.indicator (hSm m)).aemeasurable]`. Conclude with `tsum_congr fun m => lintegral_indicator_const (hSm m) _`.

Use `_ ≤ ∑' m : ℕ, ENNReal.ofReal (|C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := by`. Use `ENNReal.tsum_le_tsum fun m => ?_` and prove the remaining obligations. Establish `hR : (1:ℝ) ≤ (2:ℝ) ^ m` using `one_le_pow₀ (by norm_num)`. Establish `hp0 : 0 ≤ ((2:ℝ) ^ m / 2) ^ (-A)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ENNReal.ofReal_mul hp0]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ENNReal.ofReal (∑' m : ℕ, |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm`. Use `_ < ∞ := ENNReal.ofReal_lt_top`.
-/
theorem shellInt : ShellInt := by
  intro X _ μ N C d A hN h1 hd hC hdA
  have hSm : ∀ m : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ m} := fun m =>
    measurableSet_le hN measurable_const
  have key : ∀ m : ℕ, ((2:ℝ) ^ m / 2) ^ (-A) * ((2:ℝ) ^ m) ^ d = 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m := by
    intro m
    have e1 : (2:ℝ) ^ m / 2 = (2:ℝ) ^ ((m:ℝ) - 1) := by
      rw [Real.rpow_sub_one (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]
    have e2 : ((2:ℝ) ^ (d - A)) ^ m = (2:ℝ) ^ ((d - A) * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [e1, e2, ← Real.rpow_natCast (2:ℝ) m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤
      ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    classical
    have hex : ∃ n : ℕ, N x ≤ (2:ℝ) ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (N x) (by norm_num : (1:ℝ) < 2)
      exact ⟨n, hn.le⟩
    let m0 := Nat.find hex
    have hm0 : N x ≤ (2:ℝ) ^ m0 := Nat.find_spec hex
    have hlow : (2:ℝ) ^ m0 / 2 ≤ N x := by
      rcases Nat.eq_zero_or_pos m0 with h0 | h0
      · rw [h0]
        norm_num
        linarith
      · obtain ⟨n, hn⟩ : ∃ n, m0 = n + 1 := ⟨m0 - 1, by omega⟩
        have hmin := Nat.find_min hex (show n < m0 by omega)
        push_neg at hmin
        rw [hn, pow_succ]
        linarith
    calc ENNReal.ofReal (N x ^ (-A)) ≤ ENNReal.ofReal (((2:ℝ) ^ m0 / 2) ^ (-A)) :=
          by
            apply ENNReal.ofReal_le_ofReal
            rw [Real.rpow_neg (by linarith), Real.rpow_neg (by positivity), inv_eq_one_div,
              inv_eq_one_div]
            exact one_div_le_one_div_of_le (by positivity)
              (Real.rpow_le_rpow (by positivity) hlow (by linarith))
      _ = {x | N x ≤ (2:ℝ) ^ m0}.indicator (fun _ => ENNReal.ofReal (((2:ℝ) ^ m0 / 2) ^ (-A))) x := by
          rw [Set.indicator_of_mem (show x ∈ {x | N x ≤ (2:ℝ) ^ m0} from hm0)]
      _ ≤ ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator
            (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x := ENNReal.le_tsum m0
  have hq0 : 0 ≤ (2:ℝ) ^ (d - A) := by positivity
  have hq1 : (2:ℝ) ^ (d - A) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : Summable fun m : ℕ => |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' m : ℕ, {x | N x ≤ (2:ℝ) ^ m}.indicator
          (fun _ => ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A))) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' m : ℕ, ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * μ {x | N x ≤ (2:ℝ) ^ m} := by
        rw [lintegral_tsum fun m => (measurable_const.indicator (hSm m)).aemeasurable]
        exact tsum_congr fun m => lintegral_indicator_const (hSm m) _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (|C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        have hR : (1:ℝ) ≤ (2:ℝ) ^ m := one_le_pow₀ (by norm_num)
        have hp0 : 0 ≤ ((2:ℝ) ^ m / 2) ^ (-A) := by positivity
        calc ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * μ {x | N x ≤ (2:ℝ) ^ m}
            ≤ ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * ENNReal.ofReal (C * ((2:ℝ) ^ m) ^ d) :=
              mul_le_mul_of_nonneg_left (hC _ hR) zero_le
          _ ≤ ENNReal.ofReal (((2:ℝ) ^ m / 2) ^ (-A)) * ENNReal.ofReal (|C| * ((2:ℝ) ^ m) ^ d) :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) zero_le
          _ = ENNReal.ofReal (|C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) := by
              rw [← ENNReal.ofReal_mul hp0]
              congr 1
              calc ((2:ℝ) ^ m / 2) ^ (-A) * (|C| * ((2:ℝ) ^ m) ^ d)
                  = |C| * (((2:ℝ) ^ m / 2) ^ (-A) * ((2:ℝ) ^ m) ^ d) := by ring
                _ = |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m := by rw [key m]; ring
    _ = ENNReal.ofReal (∑' m : ℕ, |C| * 2 ^ A * ((2:ℝ) ^ (d - A)) ^ m) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/- English proof (translation)
Establish `hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`. Use `show Continuous (fun x : Mt k r => (a * Matrix.of x * a⁻¹ : Mat k r))`. Conclude with `(continuous_const.matrix_mul hof).matrix_mul continuous_const`.
-/
theorem conjM_cont {k r : ℕ} (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  show Continuous (fun x : Mt k r => (a * Matrix.of x * a⁻¹ : Mat k r))
  exact (continuous_const.matrix_mul hof).matrix_mul continuous_const

/- English proof (translation)
Establish `hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`. Use `show Continuous (fun x : Mt k r => (a * Matrix.of x : Mat k r))`. Conclude with `continuous_const.matrix_mul hof`.
-/
theorem lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  show Continuous (fun x : Mt k r => (a * Matrix.of x : Mat k r))
  exact continuous_const.matrix_mul hof

/- English proof (translation)
Establish `hof : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ))` using `continuous_id`. Use `show Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x * a : Matrix (Fin n) (Fin n) ℂ))`. Conclude with `hof.matrix_mul continuous_const`.
-/
theorem rmulF_cont {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  have hof : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  show Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x * a : Matrix (Fin n) (Fin n) ℂ))
  exact hof.matrix_mul continuous_const

def mid (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : Prop := 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1

/- English proof (translation)
Establish `hs` using `s.isLt`. Use `show 1 ≤ s.val + 1 ∧ s.val + 1 < 2 * r' + k + 1 + 1`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem mid_levPos (k r' : ℕ) (s : Fin (2 * r' + k + 1)) : mid k r' (levPos k 1 r' s) := by
  have hs := s.isLt
  show 1 ≤ s.val + 1 ∧ s.val + 1 < 2 * r' + k + 1 + 1
  constructor <;> omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨h1, h2⟩ : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1` from `h`. Conclude with `⟨⟨p.val - 1, by omega⟩, Fin.ext (show p.val - 1 + 1 = p.val by omega)⟩`. Introduce and unpack `⟨s, rfl⟩`.

Conclude with `mid_levPos k r' s`.
-/
theorem mid_iff (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : mid k r' p ↔ p ∈ Set.range (levPos k 1 r') := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := h
    exact ⟨⟨p.val - 1, by omega⟩, Fin.ext (show p.val - 1 + 1 = p.val by omega)⟩
  · rintro ⟨s, rfl⟩
    exact mid_levPos k r' s

/- English proof (translation)
Introduce `s t h`. Establish `h' : s.val + 1 = t.val + 1` using `congrArg Fin.val h`. Conclude with `Fin.ext (by omega)`.
-/
theorem levPos_inj (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro s t h
  have h' : s.val + 1 = t.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

/- English proof (translation)
Establish `hs : s.val ≤ 2 * r' + k` using `by have := s.isLt; omega`. Establish `ht : t.val ≤ 2 * r' + k` using `by have := t.isLt; omega`. Simplify using `only [ιLev, levPos]`. Apply the tactic sequence `try split_ifs`. Apply the tactic sequence `all_goals first | omega | simp [hs, ht]`.
-/
theorem lev_mm (k r' : ℕ) (g : Mat k r') (s t : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' s) (levPos k 1 r' t) = g s t := by
  have hs : s.val ≤ 2 * r' + k := by have := s.isLt; omega
  have ht : t.val ≤ 2 * r' + k := by have := t.isLt; omega
  simp only [ιLev, levPos]
  try split_ifs
  all_goals first | omega | simp [hs, ht]

/- English proof (translation)
Establish `hp' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1` using `hp`. Establish `hq' : ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1)` using `hq`. Simplify using `only [ιLev]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem lev_mn (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : mid k r' p) (hq : ¬ mid k r' q) :
    ιLev k 1 r' g p q = 0 := by
  have hp' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := hp
  have hq' : ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) := hq
  simp only [ιLev]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hp' : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)` using `hp`. Simplify using `only [ιLev]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem lev_n (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : ¬ mid k r' p) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  have hp' : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := hp
  simp only [ιLev]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use extensionality with `p q`. Distinguish the cases in `hp : mid k r' p`. Distinguish the cases in `hq : mid k r' q`. Take `⟨s, rfl⟩` from `(mid_iff k r' p).1 hp`. Take `⟨t, rfl⟩` from `(mid_iff k r' q).1 hq`.

Rewrite using `[lev_mm, Matrix.one_apply, Matrix.one_apply]`. Simplify using `only [(levPos_inj k r').eq_iff]`. Rewrite using `[lev_mn k r' _ p q hp hq, Matrix.one_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hq hp`.

Rewrite using `[lev_n k r' _ p q hp, Matrix.one_apply]`.
-/
theorem lev_one (k r' : ℕ) : ιLev k 1 r' 1 = 1 := by
  ext p q
  by_cases hp : mid k r' p
  · by_cases hq : mid k r' q
    · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
      obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
      rw [lev_mm, Matrix.one_apply, Matrix.one_apply]
      simp only [(levPos_inj k r').eq_iff]
    · rw [lev_mn k r' _ p q hp hq, Matrix.one_apply, if_neg]
      rintro rfl; exact hq hp
  · rw [lev_n k r' _ p q hp, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hp : mid k r' p`. Take `⟨s, rfl⟩` from `(mid_iff k r' p).1 hp`. Rewrite using `[← Fintype.sum_of_injective (levPos k 1 r') (levPos_inj k r') (fun u => g s u * ιLev k 1 r' h (levPos k 1 r' u) q) (fun l => ιLev k 1 r' g (levPos k 1 r' s) l * ιLev k 1 r' h l q) (fun l hl => by`.

Simplify using `only [lev_mn k r' g _ l (mid_levPos k r' s) (fun hm => hl ((mid_iff k r' l).1 hm)), zero_mul])`. Use the proof step `(fun u => by simp only [lev_mm])]`. Distinguish the cases in `hq : mid k r' q`. Take `⟨t, rfl⟩` from `(mid_iff k r' q).1 hq`. Simplify using `only [lev_mm, Matrix.mul_apply]`.

Establish `hz : ∀ (g' : Mat k r') (u : Fin (2 * r' + k + 1)), ιLev k 1 r' g' (levPos k 1 r' u) q = 0` using `fun g' u => lev_mn k r' g' _ q (mid_levPos k r' u) hq`. Simplify using `only [hz, mul_zero, Finset.sum_const_zero]`. Rewrite using `[lev_n k r' _ p q hp]`. Simplify using `only [lev_n k r' g p _ hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, lev_n k r' h p q hp]`.
-/
theorem lev_mul (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : mid k r' p
  · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
    rw [← Fintype.sum_of_injective (levPos k 1 r') (levPos_inj k r')
      (fun u => g s u * ιLev k 1 r' h (levPos k 1 r' u) q)
      (fun l => ιLev k 1 r' g (levPos k 1 r' s) l * ιLev k 1 r' h l q)
      (fun l hl => by
        simp only [lev_mn k r' g _ l (mid_levPos k r' s) (fun hm => hl ((mid_iff k r' l).1 hm)),
          zero_mul])
      (fun u => by simp only [lev_mm])]
    by_cases hq : mid k r' q
    · obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
      simp only [lev_mm, Matrix.mul_apply]
    · have hz : ∀ (g' : Mat k r') (u : Fin (2 * r' + k + 1)), ιLev k 1 r' g' (levPos k 1 r' u) q = 0 :=
        fun g' u => lev_mn k r' g' _ q (mid_levPos k r' u) hq
      simp only [hz, mul_zero, Finset.sum_const_zero]
  · rw [lev_n k r' _ p q hp]
    simp only [lev_n k r' g p _ hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, lev_n k r' h p q hp]

def blk (k r' : ℕ) (x : Mat k (1 + r')) : Mat k r' := Matrix.of fun s t => x (levPos k 1 r' s) (levPos k 1 r' t)

/- English proof (translation)
The claim follows from `continuous_matrix fun s t => continuous_id.matrix_elem (levPos k 1 r' s) (levPos k 1 r' t)`.
-/
theorem blk_cont (k r' : ℕ) : Continuous (blk k r') := continuous_matrix fun s t => continuous_id.matrix_elem (levPos k 1 r' s) (levPos k 1 r' t)

/- English proof (translation)
Use extensionality with `s t`. Simplify using `only [blk, Matrix.of_apply, lev_mm]`.
-/
theorem blk_lev (k r' : ℕ) (x : Mat k r') : blk k r' (ιLev k 1 r' x) = x := by
  ext s t
  simp only [blk, Matrix.of_apply, lev_mm]

/- English proof (translation)
Use `continuous_matrix fun p q => ?_` and prove the remaining obligations. Distinguish the cases in `hp : mid k r' p`. Distinguish the cases in `hq : mid k r' q`. Take `⟨s, rfl⟩` from `(mid_iff k r' p).1 hp`. Take `⟨t, rfl⟩` from `(mid_iff k r' q).1 hq`.

Simplify using `only [lev_mm]`. Conclude with `continuous_id.matrix_elem s t`. Simplify using `only [lev_mn k r' _ p q hp hq]`. Conclude with `continuous_const`. Simplify using `only [lev_n k r' _ p q hp]`.

Conclude with `continuous_const`.
-/
theorem lev_cont (k r' : ℕ) : Continuous (ιLev k 1 r') := by
  refine continuous_matrix fun p q => ?_
  by_cases hp : mid k r' p
  · by_cases hq : mid k r' q
    · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
      obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
      simp only [lev_mm]
      exact continuous_id.matrix_elem s t
    · simp only [lev_mn k r' _ p q hp hq]
      exact continuous_const
  · simp only [lev_n k r' _ p q hp]
    exact continuous_const

/- English proof (translation)
The claim follows from `lev_cont k r'`.
-/
theorem levM_cont (k r' : ℕ) : Continuous (levM k r') := lev_cont k r'

/- English proof (translation)
Establish `e : ιLev k 1 r' '' U = {y | ιLev k 1 r' (blk k r' y) = y} ∩ blk k r' ⁻¹' U`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show ιLev k 1 r' (blk k r' (ιLev k 1 r' x)) = ιLev k 1 r' x`. Rewrite using `[blk_lev]`. Use `show blk k r' (ιLev k 1 r' x) ∈ U`. Rewrite using `[blk_lev]`. Conclude with `hx`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨blk k r' y, h2, h1⟩`. Rewrite using `[e]`. Conclude with `(isClosed_eq ((lev_cont k r').comp (blk_cont k r')) continuous_id).inter (hU.preimage (blk_cont k r'))`.
-/
theorem lev_closed (k r' : ℕ) (U : Set (Mat k r')) (hU : IsClosed U) : IsClosed (ιLev k 1 r' '' U) := by
  have e : ιLev k 1 r' '' U = {y | ιLev k 1 r' (blk k r' y) = y} ∩ blk k r' ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · show ιLev k 1 r' (blk k r' (ιLev k 1 r' x)) = ιLev k 1 r' x
        rw [blk_lev]
      · show blk k r' (ιLev k 1 r' x) ∈ U
        rw [blk_lev]
        exact hx
    · rintro ⟨h1, h2⟩
      exact ⟨blk k r' y, h2, h1⟩
  rw [e]
  exact (isClosed_eq ((lev_cont k r').comp (blk_cont k r')) continuous_id).inter
    (hU.preimage (blk_cont k r'))

/- English proof (translation)
Establish `hm : MeasurableSet (Vᶜ : Set (Mt k r))` using `(show IsOpen (Vᶜ : Set (Mt k r)) from hV.isOpen_compl).measurableSet`. Rewrite using `[Measure.map_apply hf hm]`. Conclude with `h`.
-/
theorem map_compl_null {X : Type*} [MeasurableSpace X] {k r : ℕ} (V : Set (Mat k r)) (hV : IsClosed V) (μ : Measure X)
    (f : X → Mt k r) (hf : Measurable f) (h : μ {x | f x ∉ V} = 0) : (μ.map f) Vᶜ = 0 := by
  have hm : MeasurableSet (Vᶜ : Set (Mt k r)) :=
    (show IsOpen (Vᶜ : Set (Mt k r)) from hV.isOpen_compl).measurableSet
  rw [Measure.map_apply hf hm]
  exact h

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `h1 : (μ.map f) Set.univ = 0` using `by simp [h0]`. Rewrite `h1` using `[Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]`. Conclude with `Measure.measure_univ_eq_zero.1 h1`.
-/
theorem map_ne_zero {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (h : μ ≠ 0) : μ.map f ≠ 0 := by
  intro h0
  apply h
  have h1 : (μ.map f) Set.univ = 0 := by simp [h0]
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ] at h1
  exact Measure.measure_univ_eq_zero.1 h1

/- English proof (translation)
Introduce `k r' U μ hU hμ`. Establish `hright : ∀ u ∈ U, ιLev k 1 r' u * ιLev k 1 r' u⁻¹ = 1`. Introduce `u hu`. Rewrite using `[← lev_mul, Matrix.mul_nonsing_inv u (hU.unit u hu), lev_one]`. Establish `hinv : ∀ u ∈ U, (ιLev k 1 r' u)⁻¹ = ιLev k 1 r' u⁻¹` using `fun u hu => Matrix.inv_eq_right_inv (hright u hu)`.

Establish `hmeas : Measurable (levM k r')` using `(levM_cont k r').measurable`. Use `⟨⟨⟨1, hU.one_mem, lev_one k r'⟩, ?_, ?_, ?_, lev_closed k r' U hU.closed⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Conclude with `⟨a * b, hU.mul_mem a ha b hb, lev_mul k r' a b⟩`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `⟨a⁻¹, hU.inv_mem a ha, (hinv a ha).symm⟩`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `Matrix.isUnit_det_of_right_inverse (hright a ha)`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `map_compl_null (ιLev k 1 r' '' U) (lev_closed k r' U hU.closed) μ (levM k r') hmeas (measure_mono_null ?_ hμ.conc)` and prove the remaining obligations.

Introduce `x hx hxU`. Conclude with `hx ⟨x, hxU, rfl⟩`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Rewrite using `[Measure.map_map (lmulM_cont _).measurable hmeas]`. Establish `e : lmulM (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ lmulM u`.

Use function extensionality and compare the values at `x`. Use `show ιLev k 1 r' u * ιLev k 1 r' (Matrix.of x) = ιLev k 1 r' (u * Matrix.of x)`. Rewrite using `[lev_mul]`. Rewrite using `[e, ← Measure.map_map hmeas (lmulM_cont u).measurable, hμ.left u hu]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Rewrite using `[Measure.map_map (rmulF_cont _).measurable hmeas]`. Establish `e : rmulF (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ rmulF u`. Use function extensionality and compare the values at `x`. Use `show ιLev k 1 r' (Matrix.of x) * ιLev k 1 r' u = ιLev k 1 r' (Matrix.of x * u)`. Rewrite using `[lev_mul]`.

Rewrite using `[e, ← Measure.map_map hmeas (rmulF_cont u).measurable, hμ.right u hu]`. Introduce `K hK`. Rewrite using `[Measure.map_apply hmeas hK.isClosed.measurableSet]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Formalism.FourierDecayAlt.P.B2x2.map_ne_zero μ (levM k r') hmeas hμ.ne_zero`.
-/
theorem levHaar : LevHaar := by
  intro k r' U μ hU hμ
  have hright : ∀ u ∈ U, ιLev k 1 r' u * ιLev k 1 r' u⁻¹ = 1 := by
    intro u hu
    rw [← lev_mul, Matrix.mul_nonsing_inv u (hU.unit u hu), lev_one]
  have hinv : ∀ u ∈ U, (ιLev k 1 r' u)⁻¹ = ιLev k 1 r' u⁻¹ := fun u hu =>
    Matrix.inv_eq_right_inv (hright u hu)
  have hmeas : Measurable (levM k r') := (levM_cont k r').measurable
  refine ⟨⟨⟨1, hU.one_mem, lev_one k r'⟩, ?_, ?_, ?_, lev_closed k r' U hU.closed⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, hU.mul_mem a ha b hb, lev_mul k r' a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, hU.inv_mem a ha, (hinv a ha).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Matrix.isUnit_det_of_right_inverse (hright a ha)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine map_compl_null (ιLev k 1 r' '' U) (lev_closed k r' U hU.closed) μ (levM k r') hmeas
        (measure_mono_null ?_ hμ.conc)
      intro x hx hxU
      exact hx ⟨x, hxU, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [Measure.map_map (lmulM_cont _).measurable hmeas]
      have e : lmulM (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ lmulM u := by
        funext x
        show ιLev k 1 r' u * ιLev k 1 r' (Matrix.of x) = ιLev k 1 r' (u * Matrix.of x)
        rw [lev_mul]
      rw [e, ← Measure.map_map hmeas (lmulM_cont u).measurable, hμ.left u hu]
    · rintro _ ⟨u, hu, rfl⟩
      rw [Measure.map_map (rmulF_cont _).measurable hmeas]
      have e : rmulF (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ rmulF u := by
        funext x
        show ιLev k 1 r' (Matrix.of x) * ιLev k 1 r' u = ιLev k 1 r' (Matrix.of x * u)
        rw [lev_mul]
      rw [e, ← Measure.map_map hmeas (rmulF_cont u).measurable, hμ.right u hu]
    · intro K hK
      rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
      calc μ (levM k r' ⁻¹' K) ≤ μ (blk k r' '' K) :=
            measure_mono (fun x hx => ⟨levM k r' x, hx, blk_lev k r' x⟩)
        _ < ∞ := hμ.finite_compact _ (hK.image (blk_cont k r'))
    · exact Formalism.FourierDecayAlt.P.B2x2.map_ne_zero μ (levM k r') hmeas hμ.ne_zero

/- English proof (translation)
Establish `h` using `Measure.isMulInvariant_eq_smul_of_compactSpace (μ.map (· * g)) μ`. Establish `hu : (μ.map (· * g)) Set.univ = μ Set.univ`. Rewrite using `[Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]`. Establish `h2 : (μ.map (· * g)) Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ` using `by conv_lhs => rw [h]`. Both sides reduce to the same expression.

Rewrite `h2` using `[hu]`. Establish `hfin : μ Set.univ ≠ ∞` using `(isCompact_univ.measure_lt_top).ne`. Establish `hpos : μ Set.univ ≠ 0` using `(isOpen_univ.measure_pos μ Set.univ_nonempty).ne'`. Establish `h1 : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1`. Establish `: (1 : ℝ≥0∞) * μ Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ`.

Rewrite using `[one_mul]`. Conclude with `h2`. Conclude with `((ENNReal.mul_left_inj hpos hfin).1 this).symm`. Establish `h3 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1` using `by exact_mod_cast h1`. Rewrite using `[h, h3, one_smul]`.
-/
theorem haar_right_of_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (g : G) : μ.map (· * g) = μ := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (μ.map (· * g)) μ
  have hu : (μ.map (· * g)) Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h2 : (μ.map (· * g)) Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ := by
    conv_lhs => rw [h]
    rfl
  rw [hu] at h2
  have hfin : μ Set.univ ≠ ∞ := (isCompact_univ.measure_lt_top).ne
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h1 : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1 := by
    have : (1 : ℝ≥0∞) * μ Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ := by
      rw [one_mul]; exact h2
    exact ((ENNReal.mul_left_inj hpos hfin).1 this).symm
  have h3 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := by exact_mod_cast h1
  rw [h, h3, one_smul]

/- English proof (translation)
Introduce `k r U hU hc`. Set `S : Subgroup (Mat k r)ˣ` to `{ carrier := {u | (u : Mat k r) ∈ U} mul_mem' := fun {a b} ha hb => hU.mul_mem _ ha _ hb one_mem' := hU.one_mem inv_mem' := fun {a} ha => by show ((a⁻¹ : (Mat k r)ˣ) : Mat k r) ∈ U`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `hU.inv_mem _ ha }`. Establish `hcS : IsCompact (S : Set (Mat k r)ˣ)`.

Establish `hK : IsCompact (U ×ˢ (MulOpposite.op '' U))` using `hc.prod (hc.image MulOpposite.continuous_op)`. Establish `h` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage hK`. Establish `e : (S : Set (Mat k r)ˣ) = (Units.embedProduct (Mat k r)) ⁻¹' (U ×ˢ (MulOpposite.op '' U))`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion.

Introduce `hu`. Conclude with `⟨hu, ⟨_, S.inv_mem hu, rfl⟩⟩`. Introduce `hu`. Conclude with `hu.1`. Rewrite using `[e]`.

Conclude with `h`. Establish `: CompactSpace S` using `isCompact_iff_compactSpace.mp hcS`. Set `_ : MeasurableSpace S` to `borel S`. Establish `: BorelSpace S` using `⟨rfl⟩`. Set `μ0 : Measure S` to `Measure.haar`.

Set `j : S → Mt k r` to `fun s => ((s : (Mat k r)ˣ) : Mat k r)`. Establish `hj0 : Continuous (fun s : S => ((s : (Mat k r)ˣ) : Mat k r))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hj : Continuous j` using `hj0`. Establish `hjm : Measurable j` using `hj.measurable`. Establish `lift : ∀ a ∈ U, ∃ s : S, j s = a`.

Introduce `a ha`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det a).2 (hU.unit a ha)`. Conclude with `⟨⟨u, by show (u : Mat k r) ∈ U; rw [hu]; exact ha⟩, hu⟩`. Use `⟨μ0.map j, ⟨?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Use `map_compl_null U hU.closed μ0 j hjm ?_` and prove the remaining obligations.

Establish `: {x : S | j x ∉ U} = ∅`. Use extensionality with `s`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `s.2`. Rewrite using `[this, measure_empty]`.

Introduce `a ha`. Take `⟨s, rfl⟩` from `lift a ha`. Rewrite using `[Measure.map_map (lmulM_cont _).measurable hjm]`. Establish `: (lmulM (j s) ∘ j : S → Mt k r) = j ∘ (fun x => s * x)`. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map hjm (measurable_const_mul s), map_mul_left_eq_self]`. Introduce `a ha`. Take `⟨s, rfl⟩` from `lift a ha`. Rewrite using `[Measure.map_map (rmulF_cont _).measurable hjm]`.

Establish `: (rmulF (j s) ∘ j : S → Mt k r) = j ∘ (fun x => x * s)`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map hjm (measurable_mul_const s), haar_right_of_compact]`. Introduce `K hK`.

Rewrite using `[Measure.map_apply hjm hK.isClosed.measurableSet]`. Conclude with `lt_of_le_of_lt (measure_mono (Set.subset_univ _)) isCompact_univ.measure_lt_top`. Conclude with `map_ne_zero μ0 j hjm (NeZero.ne μ0)`.
-/
theorem compactHaarExists : CompactHaarExists := by
  intro k r U hU hc
  let S : Subgroup (Mat k r)ˣ :=
    { carrier := {u | (u : Mat k r) ∈ U}
      mul_mem' := fun {a b} ha hb => hU.mul_mem _ ha _ hb
      one_mem' := hU.one_mem
      inv_mem' := fun {a} ha => by
        show ((a⁻¹ : (Mat k r)ˣ) : Mat k r) ∈ U
        rw [Matrix.coe_units_inv]; exact hU.inv_mem _ ha }
  have hcS : IsCompact (S : Set (Mat k r)ˣ) := by
    have hK : IsCompact (U ×ˢ (MulOpposite.op '' U)) := hc.prod (hc.image MulOpposite.continuous_op)
    have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage hK
    have e : (S : Set (Mat k r)ˣ) = (Units.embedProduct (Mat k r)) ⁻¹' (U ×ˢ (MulOpposite.op '' U)) := by
      ext u
      constructor
      · intro hu
        exact ⟨hu, ⟨_, S.inv_mem hu, rfl⟩⟩
      · intro hu
        exact hu.1
    rw [e]; exact h
  have : CompactSpace S := isCompact_iff_compactSpace.mp hcS
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩
  let μ0 : Measure S := Measure.haar
  let j : S → Mt k r := fun s => ((s : (Mat k r)ˣ) : Mat k r)
  have hj0 : Continuous (fun s : S => ((s : (Mat k r)ˣ) : Mat k r)) := Units.continuous_val.comp continuous_subtype_val
  have hj : Continuous j := hj0
  have hjm : Measurable j := hj.measurable
  have lift : ∀ a ∈ U, ∃ s : S, j s = a := by
    intro a ha
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det a).2 (hU.unit a ha)
    exact ⟨⟨u, by show (u : Mat k r) ∈ U; rw [hu]; exact ha⟩, hu⟩
  refine ⟨μ0.map j, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · refine map_compl_null U hU.closed μ0 j hjm ?_
    have : {x : S | j x ∉ U} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact s.2
    rw [this, measure_empty]
  · intro a ha
    obtain ⟨s, rfl⟩ := lift a ha
    rw [Measure.map_map (lmulM_cont _).measurable hjm]
    have : (lmulM (j s) ∘ j : S → Mt k r) = j ∘ (fun x => s * x) := by
      funext x; rfl
    rw [this, ← Measure.map_map hjm (measurable_const_mul s), map_mul_left_eq_self]
  · intro a ha
    obtain ⟨s, rfl⟩ := lift a ha
    rw [Measure.map_map (rmulF_cont _).measurable hjm]
    have : (rmulF (j s) ∘ j : S → Mt k r) = j ∘ (fun x => x * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hjm (measurable_mul_const s), haar_right_of_compact]
  · intro K hK
    rw [Measure.map_apply hjm hK.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) isCompact_univ.measure_lt_top
  · exact map_ne_zero μ0 j hjm (NeZero.ne μ0)

/- English proof (translation)
Establish `h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r))` using `continuous_fst`. Establish `h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r))` using `continuous_snd`. Use `show Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r))`. Conclude with `h1.matrix_mul h2`.
-/
theorem mulM_cont {k r : ℕ} : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  have h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  show Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r))
  exact h1.matrix_mul h2

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv]`.
-/
theorem inv_eq {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) : x⁻¹ = (x.det)⁻¹ • x.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

/- English proof (translation)
Simplify using `only [inv_eq]`. Conclude with `(continuous_id.matrix_det.continuousOn.inv₀ (fun x hx => IsUnit.ne_zero hx)).smul continuous_id.matrix_adjugate.continuousOn`.
-/
theorem inv_contOn {n : ℕ} : ContinuousOn (fun x : Matrix (Fin n) (Fin n) ℂ => x⁻¹) {x | IsUnit x.det} := by
  simp only [inv_eq]
  exact (continuous_id.matrix_det.continuousOn.inv₀ (fun x hx => IsUnit.ne_zero hx)).smul
    continuous_id.matrix_adjugate.continuousOn

/- English proof (translation)
Conclude with `inv_contOn (n := 2 * r + k + 1)`.
-/
theorem invM_contOn {k r : ℕ} : ContinuousOn (invM : Mt k r → Mt k r) {x | IsUnit (Matrix.of x : Mat k r).det} := by
  exact inv_contOn (n := 2 * r + k + 1)

/- English proof (translation)
Establish `h : (invM : Mt k r → Mt k r) = fun x i j => ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j`. Use function extensionality and compare the values at `x i j`. Simplify using `only [invM, inv_eq, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[h]`. Establish `hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`.

Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Conclude with `hof.matrix_det.measurable.inv.mul ((hof.matrix_adjugate).matrix_elem i j).measurable`.
-/
theorem invM_meas {k r : ℕ} : Measurable (invM : Mt k r → Mt k r) := by
  have h : (invM : Mt k r → Mt k r) = fun x i j =>
      ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    funext x i j
    simp only [invM, inv_eq, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact hof.matrix_det.measurable.inv.mul ((hof.matrix_adjugate).matrix_elem i j).measurable

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
theorem sfin {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

/- English proof (translation)
Rewrite using `[ae_iff]`. Conclude with `h`.
-/
theorem ae_of_compl {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (h : μ sᶜ = 0) : ∀ᵐ x ∂μ, x ∈ s := by
  rw [ae_iff]
  exact h

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `e : {p : X × Y | ¬ p.1 ∈ s} = sᶜ ×ˢ Set.univ`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[e, Measure.prod_prod, h, zero_mul]`.
-/
theorem ae_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (s : Set X) (h : μ sᶜ = 0) : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ s := by
  rw [ae_iff]
  have e : {p : X × Y | ¬ p.1 ∈ s} = sᶜ ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.prod_prod, h, zero_mul]

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `e : {p : X × Y | ¬ p.2 ∈ s} = Set.univ ×ˢ sᶜ`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[e, Measure.prod_prod, h, mul_zero]`.
-/
theorem ae_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (s : Set Y) (h : ν sᶜ = 0) : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ s := by
  rw [ae_iff]
  have e : {p : X × Y | ¬ p.2 ∈ s} = Set.univ ×ˢ sᶜ := by
    ext p
    simp
  rw [e, Measure.prod_prod, h, mul_zero]

/- English proof (translation)
Use `⟨⟨1, hA.one_mem, 1, hB.one_mem, (mul_one 1).symm⟩, ?_, ?_, ?_, hcl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a1, ha1, b1, hb1, rfl⟩ _ ⟨a2, ha2, b2, hb2, rfl⟩`. Establish `hu : IsUnit b1.det` using `hB.unit b1 hb1`. Use `⟨a1 * (b1 * a2 * b1⁻¹), hA.mul_mem _ ha1 _ (hn b1 hb1 a2 ha2), b1 * b2, hB.mul_mem _ hb1 _ hb2, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]`.

Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Establish `hu : IsUnit b.det` using `hB.unit b hb`. Establish `hbi : b⁻¹ ∈ B` using `hB.inv_mem b hb`. Use `⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hn _ hbi _ (hA.inv_mem a ha), b⁻¹, hbi, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hu, Matrix.mul_assoc (b⁻¹ * a⁻¹) b b⁻¹, Matrix.mul_nonsing_inv b hu, Matrix.mul_one]`.

Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Rewrite using `[Matrix.det_mul]`. Conclude with `(hA.unit a ha).mul (hB.unit b hb)`.
-/
theorem semi_group {k r : ℕ} (A B : Set (Mat k r)) (hA : IsClosedSubgroup A) (hB : IsClosedSubgroup B)
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hcl : IsClosed (mulSet A B)) : IsClosedSubgroup (mulSet A B) := by
  refine ⟨⟨1, hA.one_mem, 1, hB.one_mem, (mul_one 1).symm⟩, ?_, ?_, ?_, hcl⟩
  · rintro _ ⟨a1, ha1, b1, hb1, rfl⟩ _ ⟨a2, ha2, b2, hb2, rfl⟩
    have hu : IsUnit b1.det := hB.unit b1 hb1
    refine ⟨a1 * (b1 * a2 * b1⁻¹), hA.mul_mem _ ha1 _ (hn b1 hb1 a2 ha2), b1 * b2,
      hB.mul_mem _ hb1 _ hb2, ?_⟩
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have hu : IsUnit b.det := hB.unit b hb
    have hbi : b⁻¹ ∈ B := hB.inv_mem b hb
    refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hn _ hbi _ (hA.inv_mem a ha), b⁻¹, hbi, ?_⟩
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hu,
      Matrix.mul_assoc (b⁻¹ * a⁻¹) b b⁻¹, Matrix.mul_nonsing_inv b hu, Matrix.mul_one]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Matrix.det_mul]
    exact (hA.unit a ha).mul (hB.unit b hb)

/- English proof (translation)
Introduce `k r A B μA μB ρ hA hB hn hcl hρ hρ' hμA hμB hconj`. Use `sfin hμA` as an intermediate fact. Use `sfin hμB` as an intermediate fact. Use `⟨semi_group A B hA hB hn hcl, ?_⟩` and prove the remaining obligations. Establish `hm : Measurable (mulM : Mt k r × Mt k r → Mt k r)` using `mulM_cont.measurable`.

Establish `aeA : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.1 : Mat k r) ∈ A` using `ae_fst μA μB (A : Set (Mt k r)) hμA.conc`. Establish `aeB : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.2 : Mat k r) ∈ B` using `ae_snd μA μB (B : Set (Mt k r)) hμB.conc`. Establish `aeB' : ∀ᵐ b ∂μB, (Matrix.of b : Mat k r) ∈ B` using `ae_of_compl μB (B : Set (Mt k r)) hμB.conc`. Establish `leftA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (lmulM a) = (μA.prod μB).map mulM`. Introduce `a ha`.

Rewrite using `[Measure.map_map (lmulM_cont a).measurable hm]`. Establish `: (lmulM a ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (lmulM a) id`. Use function extensionality and compare the values at `p`. Conclude with `(Matrix.mul_assoc a (Matrix.of p.1) (Matrix.of p.2)).symm`. Rewrite using `[this, ← Measure.map_map hm ((lmulM_cont a).measurable.prodMap measurable_id), ← Measure.map_prod_map _ _ (lmulM_cont a).measurable measurable_id, hμA.left a ha, Measure.map_id]`.

Establish `rightB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (rmulF b) = (μA.prod μB).map mulM`. Introduce `b hb`. Rewrite using `[Measure.map_map (rmulF_cont b).measurable hm]`. Establish `: (rmulF b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map id (rmulF b)`. Use function extensionality and compare the values at `p`.

Conclude with `Matrix.mul_assoc (Matrix.of p.1) (Matrix.of p.2) b`. Rewrite using `[this, ← Measure.map_map hm (measurable_id.prodMap (rmulF_cont b).measurable), ← Measure.map_prod_map _ _ measurable_id (rmulF_cont b).measurable, hμB.right b hb, Measure.map_id]`. Establish `leftB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (lmulM b) = (μA.prod μB).map mulM`. Introduce `b hb`. Rewrite using `[Measure.map_map (lmulM_cont b).measurable hm]`.

Establish `: (lmulM b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (conjM b) (lmulM b)`. Use function extensionality and compare the values at `p`. Use `show b * (Matrix.of p.1 * Matrix.of p.2) = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2)`. Establish `h : b⁻¹ * b = 1` using `Matrix.nonsing_inv_mul b (hB.unit b hb)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc, Matrix.one_mul]`. Use `_ = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2) := by rw [← h]; simp only [Matrix.mul_assoc]`. Rewrite using `[this, ← Measure.map_map hm ((conjM_cont b).measurable.prodMap (lmulM_cont b).measurable), ← Measure.map_prod_map _ _ (conjM_cont b).measurable (lmulM_cont b).measurable, hμB.left b hb, hconj b hb]`. Establish `rightA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (rmulF a) = (μA.prod μB).map mulM`. Introduce `a₀ ha₀`.

Rewrite using `[Measure.map_map (rmulF_cont a₀).measurable hm]`. Set `g : Mt k r → Mt k r → Mt k r` to `fun b a => mulM (a, mulM (rmulF a₀ b, invM b))`. Establish `hgm : Measurable (Function.uncurry g)`. Apply `hm.comp` to reduce the goal to its premises. Use `measurable_snd.prodMk (hm.comp ?_)` and prove the remaining obligations.

Conclude with `((rmulF_cont a₀).measurable.comp measurable_fst).prodMk (invM_meas.comp measurable_fst)`. Establish `hg : ∀ᵐ b ∂μB, μA.map (g b) = μA` using `by filter_upwards [aeB'] with b hb`. Conclude with `hμA.right _ (hn b hb a₀ ha₀)`. Establish `hT'` using `MeasurePreserving.skew_product (MeasurePreserving.id μB) hgm hg`. Set `T : Mt k r × Mt k r → Mt k r × Mt k r` to `fun p => (g p.2 p.1, p.2)`.

Establish `hT : MeasurePreserving T (μA.prod μB) (μA.prod μB)` using `(Measure.measurePreserving_swap.comp hT').comp (Measure.measurePreserving_swap (μ := μA) (ν := μB))`. Establish `hae : (rmulF a₀ ∘ mulM : Mt k r × Mt k r → Mt k r) =ᵐ[μA.prod μB] mulM ∘ T` using `by filter_upwards [aeB] with p hp show Matrix.of p.1 * Matrix.of p.2 * a₀ = (Matrix.of p.1 * (Matrix.of p.2 * a₀ * (Matrix.of p.2 : Mat k r)⁻¹)) * Matrix.of p.2`. Establish `h : (Matrix.of p.2 : Mat k r)⁻¹ * Matrix.of p.2 = 1` using `Matrix.nonsing_inv_mul _ (hB.unit _ hp)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h, Matrix.mul_one]`.

Rewrite using `[Measure.map_congr hae, ← Measure.map_map hm hT.measurable, hT.map_eq]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `map_compl_null _ hcl _ _ hm ?_` and prove the remaining obligations. Rewrite using `[← ae_iff (p := fun p : Mt k r × Mt k r => mulM p ∈ mulSet A B)]`. Use `filter_upwards [aeA, aeB] with p h1 h2`.

Conclude with `⟨p.1, h1, p.2, h2, rfl⟩`. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Establish `: (lmulM (a * b) : Mt k r → Mt k r) = lmulM a ∘ lmulM b`. Use function extensionality and compare the values at `x`. Conclude with `Matrix.mul_assoc a b (Matrix.of x)`.

Rewrite using `[this, ← Measure.map_map (lmulM_cont a).measurable (lmulM_cont b).measurable, leftB b hb, leftA a ha]`. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Establish `: (rmulF (a * b) : Mt k r → Mt k r) = rmulF b ∘ rmulF a`. Use function extensionality and compare the values at `x`. Conclude with `(Matrix.mul_assoc (Matrix.of x) a b).symm`.

Rewrite using `[this, ← Measure.map_map (rmulF_cont b).measurable (rmulF_cont a).measurable, rightA a ha, rightB b hb]`. Introduce `K hK`. Rewrite using `[Measure.map_apply hm hK.isClosed.measurableSet]`. Establish `hKB : IsCompact (ρ '' K ∩ (B : Set (Mt k r)))` using `(hK.image hρ).inter_right hB.closed`. Establish `hKI : IsCompact (invM '' (ρ '' K ∩ (B : Set (Mt k r))))` using `hKB.image_of_continuousOn (invM_contOn.mono fun x hx => hB.unit x hx.2)`.

Establish `hKA : IsCompact (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r))))))` using `(hK.prod hKI).image mulM_cont`. Establish `hsub : (mulM ⁻¹' K : Set (Mt k r × Mt k r)) ≤ᵐ[μA.prod μB] (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r)))))) ×ˢ (ρ '' K ∩ (B : Set (Mt k r)))` using `by filter_upwards [aeA, aeB] with p h1 h2 hp`. Establish `hb : p.2 ∈ ρ '' K ∩ (B : Set (Mt k r))` using `⟨⟨mulM p, hp, hρ' p.1 h1 p.2 h2⟩, h2⟩`. Use `⟨⟨(mulM p, invM p.2), ⟨hp, ⟨p.2, hb, rfl⟩⟩, ?_⟩, hb⟩` and prove the remaining obligations. Use `show Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.2 : Mat k r)⁻¹ = Matrix.of p.1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv (Matrix.of p.2 : Mat k r) (hB.unit _ h2), Matrix.mul_one]`. Use `lt_of_le_of_lt (measure_mono_ae hsub) ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod]`. Conclude with `ENNReal.mul_lt_top (hμA.finite_compact _ hKA) (hμB.finite_compact _ hKB)`. Use `map_ne_zero _ _ hm ?_` and prove the remaining obligations.

Introduce `h0`. Establish `h` using `congrArg (fun ν : Measure (Mt k r × Mt k r) => ν Set.univ) h0`. Simplify using `only [Measure.coe_zero, Pi.zero_apply] at h`. Rewrite `h` using `[← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero]`. Break down `h with h | h` into its components or cases.

Conclude with `hμA.ne_zero (Measure.measure_univ_eq_zero.mp h)`. Conclude with `hμB.ne_zero (Measure.measure_univ_eq_zero.mp h)`.
-/
theorem semiHaar : SemiHaar := by
  intro k r A B μA μB ρ hA hB hn hcl hρ hρ' hμA hμB hconj
  have := sfin hμA
  have := sfin hμB
  refine ⟨semi_group A B hA hB hn hcl, ?_⟩
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  have aeA : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.1 : Mat k r) ∈ A := ae_fst μA μB (A : Set (Mt k r)) hμA.conc
  have aeB : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.2 : Mat k r) ∈ B := ae_snd μA μB (B : Set (Mt k r)) hμB.conc
  have aeB' : ∀ᵐ b ∂μB, (Matrix.of b : Mat k r) ∈ B := ae_of_compl μB (B : Set (Mt k r)) hμB.conc

  have leftA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (lmulM a) = (μA.prod μB).map mulM := by
    intro a ha
    rw [Measure.map_map (lmulM_cont a).measurable hm]
    have : (lmulM a ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (lmulM a) id := by
      funext p
      exact (Matrix.mul_assoc a (Matrix.of p.1) (Matrix.of p.2)).symm
    rw [this, ← Measure.map_map hm ((lmulM_cont a).measurable.prodMap measurable_id),
      ← Measure.map_prod_map _ _ (lmulM_cont a).measurable measurable_id, hμA.left a ha, Measure.map_id]
  have rightB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (rmulF b) = (μA.prod μB).map mulM := by
    intro b hb
    rw [Measure.map_map (rmulF_cont b).measurable hm]
    have : (rmulF b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map id (rmulF b) := by
      funext p
      exact Matrix.mul_assoc (Matrix.of p.1) (Matrix.of p.2) b
    rw [this, ← Measure.map_map hm (measurable_id.prodMap (rmulF_cont b).measurable),
      ← Measure.map_prod_map _ _ measurable_id (rmulF_cont b).measurable, hμB.right b hb, Measure.map_id]
  have leftB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (lmulM b) = (μA.prod μB).map mulM := by
    intro b hb
    rw [Measure.map_map (lmulM_cont b).measurable hm]
    have : (lmulM b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (conjM b) (lmulM b) := by
      funext p
      show b * (Matrix.of p.1 * Matrix.of p.2) = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2)
      have h : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b (hB.unit b hb)
      calc b * (Matrix.of p.1 * Matrix.of p.2) = b * Matrix.of p.1 * (1 : Mat k r) * Matrix.of p.2 := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2) := by rw [← h]; simp only [Matrix.mul_assoc]
    rw [this, ← Measure.map_map hm ((conjM_cont b).measurable.prodMap (lmulM_cont b).measurable),
      ← Measure.map_prod_map _ _ (conjM_cont b).measurable (lmulM_cont b).measurable, hμB.left b hb, hconj b hb]
  have rightA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (rmulF a) = (μA.prod μB).map mulM := by
    intro a₀ ha₀
    rw [Measure.map_map (rmulF_cont a₀).measurable hm]
    let g : Mt k r → Mt k r → Mt k r := fun b a => mulM (a, mulM (rmulF a₀ b, invM b))
    have hgm : Measurable (Function.uncurry g) := by
      apply hm.comp
      refine measurable_snd.prodMk (hm.comp ?_)
      exact ((rmulF_cont a₀).measurable.comp measurable_fst).prodMk (invM_meas.comp measurable_fst)
    have hg : ∀ᵐ b ∂μB, μA.map (g b) = μA := by
      filter_upwards [aeB'] with b hb
      exact hμA.right _ (hn b hb a₀ ha₀)
    have hT' := MeasurePreserving.skew_product (MeasurePreserving.id μB) hgm hg
    let T : Mt k r × Mt k r → Mt k r × Mt k r := fun p => (g p.2 p.1, p.2)
    have hT : MeasurePreserving T (μA.prod μB) (μA.prod μB) :=
      (Measure.measurePreserving_swap.comp hT').comp (Measure.measurePreserving_swap (μ := μA) (ν := μB))
    have hae : (rmulF a₀ ∘ mulM : Mt k r × Mt k r → Mt k r) =ᵐ[μA.prod μB] mulM ∘ T := by
      filter_upwards [aeB] with p hp
      show Matrix.of p.1 * Matrix.of p.2 * a₀ =
        (Matrix.of p.1 * (Matrix.of p.2 * a₀ * (Matrix.of p.2 : Mat k r)⁻¹)) * Matrix.of p.2
      have h : (Matrix.of p.2 : Mat k r)⁻¹ * Matrix.of p.2 = 1 := Matrix.nonsing_inv_mul _ (hB.unit _ hp)
      simp only [Matrix.mul_assoc]
      rw [h, Matrix.mul_one]
    rw [Measure.map_congr hae, ← Measure.map_map hm hT.measurable, hT.map_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine map_compl_null _ hcl _ _ hm ?_
    rw [← ae_iff (p := fun p : Mt k r × Mt k r => mulM p ∈ mulSet A B)]
    filter_upwards [aeA, aeB] with p h1 h2
    exact ⟨p.1, h1, p.2, h2, rfl⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have : (lmulM (a * b) : Mt k r → Mt k r) = lmulM a ∘ lmulM b := by
      funext x; exact Matrix.mul_assoc a b (Matrix.of x)
    rw [this, ← Measure.map_map (lmulM_cont a).measurable (lmulM_cont b).measurable, leftB b hb, leftA a ha]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have : (rmulF (a * b) : Mt k r → Mt k r) = rmulF b ∘ rmulF a := by
      funext x; exact (Matrix.mul_assoc (Matrix.of x) a b).symm
    rw [this, ← Measure.map_map (rmulF_cont b).measurable (rmulF_cont a).measurable, rightA a ha, rightB b hb]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    have hKB : IsCompact (ρ '' K ∩ (B : Set (Mt k r))) := (hK.image hρ).inter_right hB.closed
    have hKI : IsCompact (invM '' (ρ '' K ∩ (B : Set (Mt k r)))) :=
      hKB.image_of_continuousOn (invM_contOn.mono fun x hx => hB.unit x hx.2)
    have hKA : IsCompact (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r)))))) := (hK.prod hKI).image mulM_cont
    have hsub : (mulM ⁻¹' K : Set (Mt k r × Mt k r)) ≤ᵐ[μA.prod μB]
        (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r)))))) ×ˢ (ρ '' K ∩ (B : Set (Mt k r))) := by
      filter_upwards [aeA, aeB] with p h1 h2 hp
      have hb : p.2 ∈ ρ '' K ∩ (B : Set (Mt k r)) := ⟨⟨mulM p, hp, hρ' p.1 h1 p.2 h2⟩, h2⟩
      refine ⟨⟨(mulM p, invM p.2), ⟨hp, ⟨p.2, hb, rfl⟩⟩, ?_⟩, hb⟩
      show Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.2 : Mat k r)⁻¹ = Matrix.of p.1
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv (Matrix.of p.2 : Mat k r) (hB.unit _ h2), Matrix.mul_one]
    refine lt_of_le_of_lt (measure_mono_ae hsub) ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hμA.finite_compact _ hKA) (hμB.finite_compact _ hKB)
  · refine map_ne_zero _ _ hm ?_
    intro h0
    have h := congrArg (fun ν : Measure (Mt k r × Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h
    rcases h with h | h
    · exact hμA.ne_zero (Measure.measure_univ_eq_zero.mp h)
    · exact hμB.ne_zero (Measure.measure_univ_eq_zero.mp h)

end Formalism.FourierDecayAlt.P.B2x2

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.semiHaar`.
-/
theorem semidirect_product_haar : Formalism.FourierDecayAlt.B2.SemiHaar := Formalism.FourierDecayAlt.P.B2x2.semiHaar

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.levHaar`.
-/
theorem levi_haar_measure_exists : Formalism.FourierDecayAlt.B2.LevHaar := Formalism.FourierDecayAlt.P.B2x2.levHaar

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.compactHaarExists`.
-/
theorem compact_group_haar_exists : Formalism.FourierDecayAlt.B2.CompactHaarExists := Formalism.FourierDecayAlt.P.B2x2.compactHaarExists

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.shellInt`.
-/
theorem spherical_shell_integral : Formalism.FourierDecayAlt.B2.ShellInt := Formalism.FourierDecayAlt.P.B2x2.shellInt

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.closedG`.
-/
theorem unitary_group_closed : Formalism.FourierDecayAlt.B2.ClosedG := Formalism.FourierDecayAlt.P.B2x2.closedG

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.B2x2.closedN`.
-/
theorem unipotent_radical_closed : Formalism.FourierDecayAlt.B2.ClosedN := Formalism.FourierDecayAlt.P.B2x2.closedN

end Formalism.FourierDecayAlt.P
