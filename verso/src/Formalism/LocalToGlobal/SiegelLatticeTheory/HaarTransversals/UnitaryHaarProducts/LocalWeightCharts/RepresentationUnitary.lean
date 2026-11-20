import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ColOfLeftInv

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace WlocSk.UnitaryRepLocal

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

/- English proof (translation)
The claim follows from `WlocSk.UnitaryGroupBasics.uh_mul ha hb`.
-/
theorem uh_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) :=
  WlocSk.UnitaryGroupBasics.uh_mul ha hb

/- English proof (translation)
Establish `hu` using `WlocSk.UnitaryGroupBasics.isUnit_of_uh ha`. Conclude with `⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, WlocSk.UnitaryGroupBasics.uh_inv ha⟩`.
-/
theorem uh_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have hu := WlocSk.UnitaryGroupBasics.isUnit_of_uh ha
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, WlocSk.UnitaryGroupBasics.uh_inv ha⟩

/- English proof (translation)
The claim follows from `WlocSk.UnitaryGroupBasics.hpk_sq`.
-/
theorem hpk_sq : Hpk k r * Hpk k r = 1 := WlocSk.UnitaryGroupBasics.hpk_sq

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem col_eq (g : Mx k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def inB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (inB k r i) := by unfold inB; infer_instance

def eB (k r : ℕ) (m : Fin k) : Fin (2 * r + k + 1) := ⟨r + m.val, by omega⟩

/- English proof (translation)
Introduce `a b h`. Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[eB] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem eB_inj : Function.Injective (eB k r) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [eB] at this; omega

/- English proof (translation)
Unfold `inB eB`. Simplify using the standard rewrite rules.
-/
theorem eB_inB (m : Fin k) : inB k r (eB k r m) := by unfold inB eB; simp

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Unfold `inB at hi`. Simplify using `[eB]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_eB_of_inB {i : Fin (2 * r + k + 1)} (hi : inB k r i) : i = eB k r ⟨i.val - r, by unfold inB at hi; omega⟩ := by
  apply Fin.ext; unfold inB at hi; simp [eB]; omega

def ub (c : Mx k r) : Matrix (Fin k) (Fin k) ℂ := fun m m' => c (eB k r m) (eB k r m')

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Establish `hj' : r ≤ j.val ∧ j.val < r + k` using `hj`. Unfold `blockW`. Rewrite using `[dif_pos hi', dif_pos hj']`.
-/
theorem blockW_in {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : inB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold inB at hi; omega⟩ ⟨j.val - r, by unfold inB at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  unfold blockW; rw [dif_pos hi', dif_pos hj']

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Establish `hj' : ¬ (r ≤ j.val ∧ j.val < r + k)` using `hj`. Unfold `blockW`. Rewrite using `[dif_pos hi', dif_neg hj']`.
-/
theorem blockW_in_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : ¬ inB k r j) :
    blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  unfold blockW; rw [dif_pos hi', dif_neg hj']

/- English proof (translation)
Establish `hi' : ¬ (r ≤ i.val ∧ i.val < r + k)` using `hi`. Unfold `blockW`. Rewrite using `[dif_neg hi']`.
-/
theorem blockW_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : ¬ inB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  unfold blockW; rw [dif_neg hi']

/- English proof (translation)
Rewrite using `[blockW_in (eB_inB m) (eB_inB m')]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext <;> simp [eB]`.
-/
theorem blockW_eB (h : Matrix (Fin k) (Fin k) ℂ) (m m' : Fin k) : blockW k r h (eB k r m) (eB k r m') = h m m' := by
  rw [blockW_in (eB_inB m) (eB_inB m')]
  congr 1 <;> apply Fin.ext <;> simp [eB]

/- English proof (translation)
Use `symm`. Use `Finset.sum_of_injOn (eB k r) eB_inj.injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun i _ hi => hF i ?_) (fun _ _ => rfl)` and prove the remaining obligations. Introduce `hb`. Conclude with `hi ⟨_, by simp, (eq_eB_of_inB hb).symm⟩`.
-/
theorem sum_block (F : Fin (2 * r + k + 1) → ℂ) (hF : ∀ l, ¬ inB k r l → F l = 0) :
    ∑ l, F l = ∑ m : Fin k, F (eB k r m) := by
  symm
  refine Finset.sum_of_injOn (eB k r) eB_inj.injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun i _ hi => hF i ?_) (fun _ _ => rfl)
  intro hb
  exact hi ⟨_, by simp, (eq_eB_of_inB hb).symm⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : inB k r i`. Rewrite using `[sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]`. Distinguish the cases in `hj : inB k r j`.

Rewrite using `[eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [blockW_eB, blockW_eB]`. Rewrite using `[blockW_in_out hi hj]`. Conclude with `(Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm`. Rewrite using `[blockW_out hi, Finset.sum_eq_single i (fun l _ hl => by rw [blockW_out hi, if_neg (Ne.symm hl), zero_mul]) (fun h => absurd (Finset.mem_univ i) h), blockW_out hi, if_pos rfl, one_mul, blockW_out hi]`.
-/
theorem blockW_mul (h₁ h₂ : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r (h₁ * h₂) = blockW k r h₁ * blockW k r h₂ := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : inB k r i
  · rw [sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]
    by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [blockW_eB, blockW_eB]
    · rw [blockW_in_out hi hj]
      exact (Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm
  · rw [blockW_out hi, Finset.sum_eq_single i (fun l _ hl => by rw [blockW_out hi, if_neg (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), blockW_out hi, if_pos rfl, one_mul, blockW_out hi]

/- English proof (translation)
Unfold `inB at hm`. Unfold `Hpk`. Distinguish the cases in `him : i = m`. Substitute `him` using the available equality. Rewrite using `[if_pos rfl]`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]`. Rewrite using `[if_neg him]`. Establish `: i.val ≠ m.val` using `fun h => him (Fin.ext h)`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by tauto)]`.
-/
theorem hpk_in_col {i m : Fin (2 * r + k + 1)} (hm : inB k r m) : Hpk k r i m = if i = m then 1 else 0 := by
  unfold inB at hm
  unfold Hpk
  by_cases him : i = m
  · subst him; rw [if_pos rfl]
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
  · rw [if_neg him]
    have : i.val ≠ m.val := fun h => him (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by tauto)]

/- English proof (translation)
Establish `hcol : ∀ i l, ¬ inB k r l → c i l = if i = l then 1 else 0`. Introduce `i l hl`. Use `congrFun (hfix l hl) i` as an intermediate fact. Simplify using `only [col_eq] at this`. Rewrite using `[this]`.

Simplify using `[bvec, Pi.single_apply]`. Establish `hHc : ∀ l j, ¬ inB k r l → inB k r j → (Hpk k r * c) l j = 0`. Introduce `l j hl hj`. Establish `hU : cᴴ * Hpk k r * c = Hpk k r` using `hc`. Establish `e1` using `congrFun (congrFun hU l) j`.

Establish `e2 : (cᴴ * Hpk k r * c) l j = (Hpk k r * c) l j`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single l]`. Rewrite using `[Matrix.conjTranspose_apply, hcol l l hl, if_pos rfl, star_one, one_mul]`. Introduce `m _ hm`. Rewrite using `[Matrix.conjTranspose_apply, hcol m l hl, if_neg hm, star_zero, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`. Establish `hne : l ≠ j` using `fun h => hl (h ▸ hj)`. Rewrite using `[← e2, e1, hpk_in_col hj, if_neg hne]`. Establish `hoff : ∀ i j, ¬ inB k r i → inB k r j → c i j = 0`.

Introduce `i j hi hj`. Establish `hsq : Hpk k r * (Hpk k r * c) = c` using `by rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]`. Rewrite using `[← hsq, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : inB k r m`.

Establish `hne : i ≠ m` using `fun h => hi (h ▸ hm)`. Rewrite using `[hpk_in_col hm, if_neg hne, zero_mul]`. Rewrite using `[hHc m j hm hj, mul_zero]`. Use extensionality with `i j`. Distinguish the cases in `hi : inB k r i`.

Distinguish the cases in `hj : inB k r j`. Rewrite using `[eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB]`. Both sides reduce to the same expression. Establish `hne : i ≠ j` using `fun h => hj (h ▸ hi)`. Rewrite using `[blockW_in_out hi hj, hcol i j hj, if_neg hne]`.

Rewrite using `[blockW_out hi]`. Distinguish the cases in `hj : inB k r j`. Establish `hne : i ≠ j` using `fun h => hi (h ▸ hj)`. Rewrite using `[hoff i j hi hj, if_neg hne]`. Conclude with `hcol i j hj`.
-/
theorem eq_blockW {c : Mx k r} (hc : c ∈ UH (Hpk k r))
    (hfix : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l) : c = blockW k r (ub c) := by
  have hcol : ∀ i l, ¬ inB k r l → c i l = if i = l then 1 else 0 := by
    intro i l hl
    have := congrFun (hfix l hl) i
    simp only [col_eq] at this
    rw [this]; simp [bvec, Pi.single_apply]

  have hHc : ∀ l j, ¬ inB k r l → inB k r j → (Hpk k r * c) l j = 0 := by
    intro l j hl hj
    have hU : cᴴ * Hpk k r * c = Hpk k r := hc
    have e1 := congrFun (congrFun hU l) j
    have e2 : (cᴴ * Hpk k r * c) l j = (Hpk k r * c) l j := by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single l]
      · rw [Matrix.conjTranspose_apply, hcol l l hl, if_pos rfl, star_one, one_mul]
      · intro m _ hm
        rw [Matrix.conjTranspose_apply, hcol m l hl, if_neg hm, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ l) h
    have hne : l ≠ j := fun h => hl (h ▸ hj)
    rw [← e2, e1, hpk_in_col hj, if_neg hne]
  have hoff : ∀ i j, ¬ inB k r i → inB k r j → c i j = 0 := by
    intro i j hi hj
    have hsq : Hpk k r * (Hpk k r * c) = c := by rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
    rw [← hsq, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : inB k r m
    · have hne : i ≠ m := fun h => hi (h ▸ hm)
      rw [hpk_in_col hm, if_neg hne, zero_mul]
    · rw [hHc m j hm hj, mul_zero]
  ext i j
  by_cases hi : inB k r i
  · by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB]; rfl
    · have hne : i ≠ j := fun h => hj (h ▸ hi)
      rw [blockW_in_out hi hj, hcol i j hj, if_neg hne]
  · rw [blockW_out hi]
    by_cases hj : inB k r j
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [hoff i j hi hj, if_neg hne]
    · exact hcol i j hj

/- English proof (translation)
Use `show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)`. Establish `hJ : Formalism.REAL.Jm (allPos k) = 1`. Unfold `Formalism.REAL.Jm allPos`. Simplify using the standard rewrite rules. Rewrite using `[hJ, Matrix.mul_one]`.

Establish `hU : cᴴ * Hpk k r * c = Hpk k r` using `hc`. Use extensionality with `m m'`. Establish `e` using `congrFun (congrFun hU (eB k r m)) (eB k r m')`. Rewrite `e` using `[hpk_in_col (eB_inB m')]`. Rewrite using `[Matrix.one_apply]`.

Establish `hin : (eB k r m = eB k r m') ↔ (m = m')` using `eB_inj.eq_iff`. Rewrite `e` using `[Matrix.mul_apply]`. Rewrite using `[sum_block _ (fun l hl => by`. Establish `hne : l ≠ eB k r m'` using `fun h => hl (h ▸ eB_inB m')`. Rewrite `e` using `[hb, blockW_out hl, if_neg hne, mul_zero])]`.

Rewrite using `[Matrix.mul_apply]`. Establish `hterm : ∀ t : Fin k, (cᴴ * Hpk k r) (eB k r m) (eB k r t) * c (eB k r t) (eB k r m') = (ub c)ᴴ m t * ub c t m'`. Introduce `t`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (eB k r t)]`. Rewrite using `[hpk_in_col (eB_inB t), if_pos rfl, mul_one]`.

Both sides reduce to the same expression. Introduce `l _ hl`. Rewrite using `[hpk_in_col (eB_inB t), if_neg hl, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite `e` using `[hterm]`. Rewrite using `[e]`. Distinguish the cases in `h : m = m'`. Rewrite using `[if_pos (hin.mpr h), if_pos h]`. Rewrite using `[if_neg (fun h' => h (hin.mp h')), if_neg h]`.
-/
theorem ub_unitary {c : Mx k r} (hc : c ∈ UH (Hpk k r)) (hb : c = blockW k r (ub c)) :
    ub c ∈ UJset (allPos k) := by
  show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    unfold Formalism.REAL.Jm allPos; simp
  rw [hJ, Matrix.mul_one]
  have hU : cᴴ * Hpk k r * c = Hpk k r := hc
  ext m m'
  have e := congrFun (congrFun hU (eB k r m)) (eB k r m')
  rw [hpk_in_col (eB_inB m')] at e
  rw [Matrix.one_apply]
  have hin : (eB k r m = eB k r m') ↔ (m = m') := eB_inj.eq_iff
  rw [Matrix.mul_apply] at e
  rw [sum_block _ (fun l hl => by
    have hne : l ≠ eB k r m' := fun h => hl (h ▸ eB_inB m')
    rw [hb, blockW_out hl, if_neg hne, mul_zero])] at e
  rw [Matrix.mul_apply]
  have hterm : ∀ t : Fin k, (cᴴ * Hpk k r) (eB k r m) (eB k r t) * c (eB k r t) (eB k r m') =
      (ub c)ᴴ m t * ub c t m' := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single (eB k r t)]
    · rw [hpk_in_col (eB_inB t), if_pos rfl, mul_one]; rfl
    · intro l _ hl; rw [hpk_in_col (eB_inB t), if_neg hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hterm] at e
  rw [e]
  by_cases h : m = m'
  · rw [if_pos (hin.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hin.mp h')), if_neg h]

/- English proof (translation)
Take `⟨g, hg, hπU⟩` from `hπ`. Take `⟨hgU, hgfix, hgz⟩` from `hg`. Take `⟨-, -, ⟨⟨hπ1, hπmul⟩, hπiso, -⟩, -⟩` from `hπU`. Establish `hgi` using `uh_inv hgU`. Establish `hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ inB k r l → a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l`.

Introduce `a ha l hl`. Unfold `inB at hl`. Distinguish the cases in `h1 : l.val < r`. Establish `hl' : l = eI k r ⟨l.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]`.

Distinguish the cases in `h2 : r + k < l.val`. Establish `hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩` using `by apply Fin.ext; simp [esI]; omega`. Rewrite using `[hl', (hgfix _).2, (ha.2.1 _).2]`. Establish `hl' : l = wI k r (Fin.last k)` using `by apply Fin.ext; simp [wI]; omega`. Establish `hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0`.

Use `Real.sqrt_pos.mpr hT` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Take `⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ)` from `⟨_, rfl⟩`. Rewrite `hgz`, `hs` using `[← ht]`. Establish `hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ hs, one_smul]`. Use `_ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]`. Rewrite using `[hl', hgw, Matrix.mulVec_smul, ha.2.2]`. Set `hOf : Mx k r → Matrix (Fin k) (Fin k) ℂ` to `fun a => ub (g⁻¹ * a * g)`.

Establish `hstruct : ∀ a ∈ UWset k r z, g⁻¹ * a * g ∈ UH (Hpk k r) ∧ g⁻¹ * a * g = blockW k r (hOf a) ∧ hOf a ∈ UJset (allPos k) ∧ a = g * blockW k r (hOf a) * g⁻¹`. Introduce `a ha`. Establish `hc : g⁻¹ * a * g ∈ UH (Hpk k r)` using `uh_mul (uh_mul hgi.2.2 ha.1) hgU`. Establish `hb : g⁻¹ * a * g = blockW k r (hOf a)`. Use `eq_blockW hc fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec, hgi.2.1, Matrix.one_mulVec]`. Use `⟨hc, hb, ub_unitary hc hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1`.

Use extensionality with `i j`. Distinguish the cases in `hi : inB k r i`. Distinguish the cases in `hj : inB k r j`. Rewrite using `[blockW_in hi hj, Matrix.one_apply, Matrix.one_apply]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Apply `h` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg Fin.val h'` as an intermediate fact. Unfold `inB at hi hj`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hne : i ≠ j` using `fun h => hj (h ▸ hi)`. Rewrite using `[blockW_in_out hi hj, Matrix.one_apply, if_neg hne]`. Rewrite using `[blockW_out hi, Matrix.one_apply]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `hπ1` as an intermediate fact.

Simplify using `only [hB1, Matrix.mul_one, hgi.1] at this`. Conclude with `this`. Introduce `a ha b hb`. Take `⟨-, hba, hua, ea⟩` from `hstruct a ha`. Take `⟨-, hbb, hub, eb⟩` from `hstruct b hb`.

Establish `hab : a * b = g * blockW k r (hOf a * hOf b) * g⁻¹`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc g⁻¹ g, hgi.2.1, Matrix.one_mul]`. Use `_ = g * blockW k r (hOf a * hOf b) * g⁻¹ := by rw [blockW_mul]`.

Establish `hm` using `hπmul _ hua _ hub`. Simplify using `only at hm`. Rewrite using `[hab, hm, ← ea, ← eb]`. Introduce `a ha x`. Take `⟨-, -, hua, ea⟩` from `hstruct a ha`.

Rewrite using `[ea]`. Conclude with `hπiso _ hua x`.
-/
theorem piAll_loc (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) :
    π 1 = 1 ∧ (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, π (a * b) = (π a).comp (π b)) ∧
      ∀ a ∈ UWset k r z, ∀ x : Wp, ‖π a x‖ = ‖x‖ := by
  obtain ⟨g, hg, hπU⟩ := hπ
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨-, -, ⟨⟨hπ1, hπmul⟩, hπiso, -⟩, -⟩ := hπU
  have hgi := uh_inv hgU

  have hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ inB k r l → a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l := by
    intro a ha l hl
    unfold inB at hl
    by_cases h1 : l.val < r
    · have hl' : l = eI k r ⟨l.val, h1⟩ := Fin.ext rfl
      rw [hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]
    · by_cases h2 : r + k < l.val
      · have hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [hl', (hgfix _).2, (ha.2.1 _).2]
      · have hl' : l = wI k r (Fin.last k) := by apply Fin.ext; simp [wI]; omega
        have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
          have := Real.sqrt_pos.mpr hT; exact_mod_cast this.ne'
        obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := ⟨_, rfl⟩
        rw [← ht] at hgz hs
        have hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z := by
          calc g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • (t • g *ᵥ bvec (wI k r (Fin.last k))) := by
                rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
            _ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]
        rw [hl', hgw, Matrix.mulVec_smul, ha.2.2]
  let hOf : Mx k r → Matrix (Fin k) (Fin k) ℂ := fun a => ub (g⁻¹ * a * g)
  have hstruct : ∀ a ∈ UWset k r z, g⁻¹ * a * g ∈ UH (Hpk k r) ∧
      g⁻¹ * a * g = blockW k r (hOf a) ∧ hOf a ∈ UJset (allPos k) ∧ a = g * blockW k r (hOf a) * g⁻¹ := by
    intro a ha
    have hc : g⁻¹ * a * g ∈ UH (Hpk k r) := uh_mul (uh_mul hgi.2.2 ha.1) hgU
    have hb : g⁻¹ * a * g = blockW k r (hOf a) := by
      refine eq_blockW hc fun l hl => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec, hgi.2.1,
        Matrix.one_mulVec]
    refine ⟨hc, hb, ub_unitary hc hb, ?_⟩
    rw [← hb]
    calc a = (g * g⁻¹) * a * (g * g⁻¹) := by rw [hgi.1, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have hB1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    ext i j
    by_cases hi : inB k r i
    · by_cases hj : inB k r j
      · rw [blockW_in hi hj, Matrix.one_apply, Matrix.one_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [if_neg h, if_neg]; intro h'; apply h; apply Fin.ext
          have := congrArg Fin.val h'; unfold inB at hi hj; simp at this; omega
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        rw [blockW_in_out hi hj, Matrix.one_apply, if_neg hne]
    · rw [blockW_out hi, Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := hπ1
    simp only [hB1, Matrix.mul_one, hgi.1] at this
    exact this
  · intro a ha b hb
    obtain ⟨-, hba, hua, ea⟩ := hstruct a ha
    obtain ⟨-, hbb, hub, eb⟩ := hstruct b hb
    have hab : a * b = g * blockW k r (hOf a * hOf b) * g⁻¹ := by
      calc a * b = (g * blockW k r (hOf a) * g⁻¹) * (g * blockW k r (hOf b) * g⁻¹) := by rw [← ea, ← eb]
        _ = g * (blockW k r (hOf a) * blockW k r (hOf b)) * g⁻¹ := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g⁻¹ g, hgi.2.1, Matrix.one_mul]
        _ = g * blockW k r (hOf a * hOf b) * g⁻¹ := by rw [blockW_mul]
    have hm := hπmul _ hua _ hub
    simp only at hm
    rw [hab, hm, ← ea, ← eb]
  · intro a ha x
    obtain ⟨-, -, hua, ea⟩ := hstruct a ha
    rw [ea]
    exact hπiso _ hua x

end WlocSk.UnitaryRepLocal

open WlocSk.UnitaryRepLocal in
/- English proof (translation)
Introduce `k r z u Vp _ _ π hz hT hπ`. Take `⟨h1, h2, h3⟩` from `piAll_loc z u Vp π hz hT hπ`. Conclude with `⟨⟨h1, h2⟩, h3⟩`.
-/
theorem representation_unitary : WlocSk.PiUnit := by
  intro k r z u Vp _ _ π hz hT hπ
  obtain ⟨h1, h2, h3⟩ := piAll_loc z u Vp π hz hT hπ
  exact ⟨⟨h1, h2⟩, h3⟩
