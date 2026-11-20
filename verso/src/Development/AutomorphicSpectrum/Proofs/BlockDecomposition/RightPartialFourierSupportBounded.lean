import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Supp

section S

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Break down `le_total (ord x) (ord y) with h | h` into its components or cases.

Establish `hmem : x + y ∈ valBall F (ord x)` using `add_mem mem_valBall_ord (valBall_antitone h mem_valBall_ord)`. Establish `h1` using `modulus_le_of_mem_valBall hmem`. Rewrite `h1` using `[← modulus_of_ne_zero hx]`. Establish `h1' : (modulus (x + y) : ℝ) ≤ modulus x` using `by exact_mod_cast h1`. Combine the linear relations using `[(modulus y).coe_nonneg]`.

Establish `hmem : x + y ∈ valBall F (ord y)` using `add_mem (valBall_antitone h mem_valBall_ord) mem_valBall_ord`. Establish `h1` using `modulus_le_of_mem_valBall hmem`. Rewrite `h1` using `[← modulus_of_ne_zero hy]`. Establish `h1' : (modulus (x + y) : ℝ) ≤ modulus y` using `by exact_mod_cast h1`. Combine the linear relations using `[(modulus x).coe_nonneg]`.
-/
theorem modulus_add_le' (x y : F) : (modulus (x + y) : ℝ) ≤ modulus x + modulus y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rcases le_total (ord x) (ord y) with h | h
  · have hmem : x + y ∈ valBall F (ord x) :=
      add_mem mem_valBall_ord (valBall_antitone h mem_valBall_ord)
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hx] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus x := by exact_mod_cast h1
    linarith [(modulus y).coe_nonneg]
  · have hmem : x + y ∈ valBall F (ord y) :=
      add_mem (valBall_antitone h mem_valBall_ord) mem_valBall_ord
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hy] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus y := by exact_mod_cast h1
    linarith [(modulus x).coe_nonneg]

/- English proof (translation)
Distinguish the cases in `t0 : t = 0`. Rewrite using `[t0]`. Conclude with `zero_mem _`. Rewrite using `[mem_valBall_iff_le_ord t0]`. Rewrite `ht` using `[modulus_of_ne_zero t0]`.

Use `(zpow_le_zpow_iff_right₀ one_lt_residueCard_nnreal).1 ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_ball_of_modulus_le (n : ℤ) {t : F} (ht : modulus t ≤ (residueCard F : NNReal) ^ (-n)) :
    t ∈ valBall F n := by
  by_cases t0 : t = 0
  · rw [t0]; exact zero_mem _
  rw [mem_valBall_iff_le_ord t0]
  rw [modulus_of_ne_zero t0] at ht
  have := (zpow_le_zpow_iff_right₀ one_lt_residueCard_nnreal).1 ht
  omega

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hψ (by ext x; simp [hcon x])`. Take `⟨n, -, hn⟩` from `hasBasis_nhds_zero_valBall.mem_iff.1 hU`.

Use `set q : NNReal := (residueCard F : NNReal) with hq`. Establish `hq0 : q ≠ 0` using `residueCard_nnreal_ne_zero`. Use `⟨((modulus a * q ^ n : NNReal) : ℝ), NNReal.coe_nonneg _, fun c hc => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Establish `hlt' : modulus a * q ^ n < modulus c`.

Establish `: ((modulus a * q ^ n : NNReal) : ℝ) < (modulus c : ℝ)` using `not_le.1 hlt`. Conclude with `this` after adjusting the coercions. Establish `hmc : 0 < modulus c` using `lt_of_le_of_lt zero_le hlt'`. Establish `c0 : c ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hmc`. Establish `hb : modulus (a / c) ≤ q ^ (-n)`. Rewrite using `[div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv, div_le_iff₀ hmc, _root_.zpow_neg]`. Establish `hqn : 0 < q ^ n` using `zpow_pos (pos_iff_ne_zero.2 hq0) n`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ hqn]`.

Conclude with `hlt'.le`. Use `hc (a / c) (hn (mem_ball_of_modulus_le n hb))` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ c0]`. Conclude with `ha this`.
-/
theorem scalar_bound (ψ : AddChar F Circle) (hψ : ψ ≠ 1) {U : Set F} (hU : U ∈ 𝓝 (0 : F)) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ c : F, (∀ t ∈ U, ψ (t * c) = 1) → (modulus c : ℝ) ≤ R₀ := by
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hψ (by ext x; simp [hcon x])
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 hU
  set q : NNReal := (residueCard F : NNReal) with hq
  have hq0 : q ≠ 0 := residueCard_nnreal_ne_zero
  refine ⟨((modulus a * q ^ n : NNReal) : ℝ), NNReal.coe_nonneg _, fun c hc => ?_⟩
  by_contra hlt
  have hlt' : modulus a * q ^ n < modulus c := by
    have : ((modulus a * q ^ n : NNReal) : ℝ) < (modulus c : ℝ) := not_le.1 hlt
    exact_mod_cast this
  have hmc : 0 < modulus c := lt_of_le_of_lt zero_le hlt'
  have c0 : c ≠ 0 := by
    rintro rfl
    simp at hmc
  have hb : modulus (a / c) ≤ q ^ (-n) := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv, div_le_iff₀ hmc, _root_.zpow_neg]
    have hqn : 0 < q ^ n := zpow_pos (pos_iff_ne_zero.2 hq0) n
    rw [inv_mul_eq_div, le_div_iff₀ hqn]
    exact hlt'.le
  have := hc (a / c) (hn (mem_ball_of_modulus_le n hb))
  rw [div_mul_cancel₀ _ c0] at this
  exact ha this

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [cat3]`.
-/
theorem concatenation_add_matrix (P l : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) :
    cat3 (P + l) y = cat3 P y + cat3 l 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cat3]

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>`. Apply the tactic sequence `simp [cat3, Matrix.single_apply] <;> first | exact continuous_id | exact continuous_const`.
-/
theorem continuous_concatenate_single_entry (i j : Fin 2) :
    Continuous fun t : F => cat3 (Matrix.single i j t) (0 : Fin 2 → F) := by
  refine continuous_matrix fun a b => ?_
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [cat3, Matrix.single_apply] <;> first | exact continuous_id | exact continuous_const

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] <;> ring`.
-/
theorem entry_sum (Z A : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) (t : F) :
    (Z * Matrix.single i j t * A) 0 1 + (Z * Matrix.single i j t * A) 1 0 =
      t * (Z 0 i * A j 1 + Z 1 i * A j 0) := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] <;> ring

end S

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Unfold `Rpart`. Set `f : (Fin 2 × Fin 2 → F) → ℂ` to `fun X => p (toM X) * (ψ (-(X (0, 1) + X (1, 0))) : ℂ)`. Set `T' : Fin 2 × Fin 2 → F` to `fun q => T q.1 q.2`. Use `haveI : (mM ψ).IsAddRightInvariant := by unfold mM; infer_instance`. Establish `hi : (∫ X, f (X + T') ∂mM ψ) = ∫ X, f X ∂mM ψ` using `integral_add_right_eq_self f T'`.

Express the relevant statement in the definitionally equal form `(∫ X, f X ∂mM ψ) = _ * ∫ X, f X ∂mM ψ`. Rewrite using `[← integral_const_mul]`. Use `conv_lhs => rw [← hi]`. Use `congr 1`. Use function extensionality and compare the values at `X`.

Establish `e1' : toM (X + T') = toM X + T`. Use extensionality with `a b`. Simplify using `[toM, T']`. Establish `e2' : -((X + T') (0, 1) + (X + T') (1, 0)) = -(T 0 1 + T 1 0) + -(X (0, 1) + X (1, 0))`. Simplify using `only [Pi.add_apply, T']`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [f]`. Rewrite using `[e1', hp, e2', AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Rpart_translate (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ)
    (T : Matrix (Fin 2) (Fin 2) F) (hp : ∀ M, p (M + T) = p M) :
    Rpart ψ p = (ψ (-(T 0 1 + T 1 0)) : ℂ) * Rpart ψ p := by
  unfold Rpart
  let f : (Fin 2 × Fin 2 → F) → ℂ := fun X => p (toM X) * (ψ (-(X (0, 1) + X (1, 0))) : ℂ)
  let T' : Fin 2 × Fin 2 → F := fun q => T q.1 q.2
  haveI : (mM ψ).IsAddRightInvariant := by unfold mM; infer_instance
  have hi : (∫ X, f (X + T') ∂mM ψ) = ∫ X, f X ∂mM ψ := integral_add_right_eq_self f T'
  change (∫ X, f X ∂mM ψ) = _ * ∫ X, f X ∂mM ψ
  rw [← integral_const_mul]
  conv_lhs => rw [← hi]
  congr 1
  funext X
  have e1' : toM (X + T') = toM X + T := by
    ext a b
    simp [toM, T']
  have e2' : -((X + T') (0, 1) + (X + T') (1, 0)) = -(T 0 1 + T 1 0) + -(X (0, 1) + X (1, 0)) := by
    simp only [Pi.add_apply, T']
    ring
  simp only [f]
  rw [e1', hp, e2', AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/- English proof (translation)
Establish `h1` using `Rpart_translate ψ p T hp`. Establish `h2 : ((ψ (-(T 0 1 + T 1 0)) : Circle) : ℂ) = 1`. Establish `: (((ψ (-(T 0 1 + T 1 0)) : Circle) : ℂ) - 1) * Rpart ψ p = 0`. Rewrite using `[sub_mul, one_mul, ← h1, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hne`. Establish `h3 : ψ (-(T 0 1 + T 1 0)) = 1` using `Circle.ext (by simpa using h2)`. Rewrite `h3` using `[AddChar.map_neg_eq_inv]`. Conclude with `inv_eq_one.1 h3`.
-/
theorem char_eq_one_of_Rpart_ne (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ)
    (T : Matrix (Fin 2) (Fin 2) F) (hp : ∀ M, p (M + T) = p M) (hne : Rpart ψ p ≠ 0) :
    ψ (T 0 1 + T 1 0) = 1 := by
  have h1 := Rpart_translate ψ p T hp
  have h2 : ((ψ (-(T 0 1 + T 1 0)) : Circle) : ℂ) = 1 := by
    have : (((ψ (-(T 0 1 + T 1 0)) : Circle) : ℂ) - 1) * Rpart ψ p = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne
  have h3 : ψ (-(T 0 1 + T 1 0)) = 1 := Circle.ext (by simpa using h2)
  rw [AddChar.map_neg_eq_inv] at h3
  exact inv_eq_one.1 h3

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hne` to reduce the goal to its premises. Unfold `Rpart`. Simplify using `[hcon]`.
-/
theorem exists_ne_of_Rpart_ne (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ)
    (hne : Rpart ψ p ≠ 0) : ∃ X, p (toM X) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hne
  unfold Rpart
  simp [hcon]

/- English proof (translation)
Unfold `Pf`. Establish `e : (z⁻¹ : GL (Fin 2) F).val * (M + z.val * l * ((tinv h)⁻¹ : GL (Fin 2) F).val) * (tinv h).val = (z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val + l`. Establish `a1 : (z⁻¹ : GL (Fin 2) F).val * z.val = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `a2 : ((tinv h)⁻¹ : GL (Fin 2) F).val * (tinv h).val = 1`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [a1, a2, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[e, concatenation_add_matrix, hinv]`.
-/
theorem Pf_translate (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F)
    (l : Matrix (Fin 2) (Fin 2) F) (hinv : ∀ x, Φ (x + cat3 l 0) = Φ x)
    (M : Matrix (Fin 2) (Fin 2) F) :
    Pf Φ h z (M + z.val * l * ((tinv h)⁻¹ : GL (Fin 2) F).val) = Pf Φ h z M := by
  unfold Pf
  have e : (z⁻¹ : GL (Fin 2) F).val * (M + z.val * l * ((tinv h)⁻¹ : GL (Fin 2) F).val) * (tinv h).val =
      (z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val + l := by
    have a1 : (z⁻¹ : GL (Fin 2) F).val * z.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have a2 : ((tinv h)⁻¹ : GL (Fin 2) F).val * (tinv h).val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc _ = (z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val +
          ((z⁻¹ : GL (Fin 2) F).val * z.val) * l * (((tinv h)⁻¹ : GL (Fin 2) F).val * (tinv h).val) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [a1, a2, Matrix.one_mul, Matrix.mul_one]
  rw [e, concatenation_add_matrix, hinv]

end D

/- English proof (translation)
Establish `h1 : a * c ≤ a * R₀` using `mul_le_mul_of_nonneg_left hc ha`. Establish `h2 : b * d ≤ b * R₀` using `mul_le_mul_of_nonneg_left hd hb`. Establish `h3 : (a + b) * R₀ ≤ S * R₀` using `mul_le_mul_of_nonneg_right hS hR`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bound_of_entries {a b c d S R₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : a + b ≤ S) (hR : 0 ≤ R₀)
    (hc : c ≤ R₀) (hd : d ≤ R₀) : a * c + b * d ≤ S * R₀ := by
  have h1 : a * c ≤ a * R₀ := mul_le_mul_of_nonneg_left hc ha
  have h2 : b * d ≤ b * R₀ := mul_le_mul_of_nonneg_left hd hb
  have h3 : (a + b) * R₀ ≤ S * R₀ := mul_le_mul_of_nonneg_right hS hR
  nlinarith

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ Φ hΦ h`. Establish `hΦ' : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin 2) (Fin 3) F)` using `hΦ`. Establish `hev` using `GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΦ'`. Set `U : Set F` to `{t | ∀ i j : Fin 2, ∀ x, Φ (x + cat3 (Matrix.single i j t) 0) = Φ x}`. Establish `hU : U ∈ 𝓝 (0 : F)`.

Establish `hij : ∀ i j : Fin 2, ∀ᶠ t : F in 𝓝 0, ∀ x, Φ (x + cat3 (Matrix.single i j t) 0) = Φ x`. Introduce `i j`. Apply the tactic sequence `have hc := (continuous_concatenate_single_entry (F := F) i j).tendsto 0`. Establish `h0 : cat3 (Matrix.single i j (0 : F)) (0 : Fin 2 → F) = 0`. Use extensionality with `a b`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [cat3]`. Rewrite `hc` using `[h0]`. Conclude with `hc.eventually hev`. Use `Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)` as an intermediate fact. Conclude with `this`.

Take `⟨R₀, hR₀, hb⟩` from `scalar_bound ψ hψ.2.1 hU`. Set `g : Matrix (Fin 2) (Fin 3) F → ℝ` to `fun m => (modulus (m 0 2) : ℝ) + (modulus (m 1 2) : ℝ)`. Establish `hg : Continuous g`. Establish `hm : Continuous fun x : F => (modulus x : ℝ)` using `NNReal.continuous_coe.comp continuous_modulus`. Conclude with `(hm.comp (continuous_id.matrix_elem 0 2)).add (hm.comp (continuous_id.matrix_elem 1 2))`.

Take `⟨R₂, hR₂⟩` from `((show IsCompact (tsupport Φ) from hΦ.2).image hg).bddAbove`. Set `B : Matrix (Fin 2) (Fin 2) F` to `(tinv h).val`. Set `A : Matrix (Fin 2) (Fin 2) F` to `((tinv h)⁻¹ : GL (Fin 2) F).val`. Establish `hBA : B * A = 1`. Express the relevant statement in the definitionally equal form `(tinv h).val * ((tinv h)⁻¹ : GL (Fin 2) F).val = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Set `S : ℝ` to `∑ r, ∑ s, (modulus (B r s) : ℝ)`. Use `⟨max (S * R₀) R₂, fun z hz => ⟨fun a i => ?_, fun a => ?_⟩⟩` and prove the remaining obligations. Apply `le_max_of_le_left` to reduce the goal to its premises. Set `c : Fin 2 → Fin 2 → F` to `fun i j => z.val 0 i * A j 1 + z.val 1 i * A j 0`.

Establish `hcb : ∀ i j, (modulus (c i j) : ℝ) ≤ R₀`. Introduce `i j`. Use `hb _ fun t ht => ?_` and prove the remaining obligations. Use `char_eq_one_of_Rpart_ne ψ (Pf Φ h z) (z.val * Matrix.single i j t * A) (Pf_translate Φ h z _ (ht i j)) hz` as an intermediate fact. Rewrite `this` using `[entry_sum]`. Then use the resulting hypothesis.

Establish `e : ∀ r s, B r 0 * A 0 s + B r 1 * A 1 s = (1 : Matrix (Fin 2) (Fin 2) F) r s`. Introduce `r s`. Rewrite using `[← hBA, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hz0 : z.val 0 i = B 1 0 * c i 0 + B 1 1 * c i 1`. Establish `e11` using `e 1 1`.

Establish `e10` using `e 1 0`. Simplify using `only [Matrix.one_apply_eq] at e11`. Simplify using `at e10`. Simplify using `only [c]`. Take the linear combination `(-(z.val 0 i)) * e11 - (z.val 1 i) * e10`.

Establish `hz1 : z.val 1 i = B 0 0 * c i 0 + B 0 1 * c i 1`. Establish `e00` using `e 0 0`. Establish `e01` using `e 0 1`. Simplify using `only [Matrix.one_apply_eq] at e00`. Simplify using `at e01`.

Simplify using `only [c]`. Take the linear combination `(-(z.val 1 i)) * e00 - (z.val 0 i) * e01`. Establish `hmod : ∀ r, (modulus (B r 0 * c i 0 + B r 1 * c i 1) : ℝ) ≤ S * R₀`. Introduce `r`. Use `(modulus_add_le' _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul]`. Use `bound_of_entries (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) ?_ hR₀ (hcb i 0) (hcb i 1)` and prove the remaining obligations. Simplify using `only [S, Fin.sum_univ_two]`. Establish `n00` using `(modulus (B 0 0)).coe_nonneg`. Establish `n01` using `(modulus (B 0 1)).coe_nonneg`.

Establish `n10` using `(modulus (B 1 0)).coe_nonneg`. Establish `n11` using `(modulus (B 1 1)).coe_nonneg`. Apply the tactic sequence `fin_cases r <;> simp <;> linarith`. Use `fin_cases a`. Express the relevant statement in the definitionally equal form `(modulus (z.val 0 i) : ℝ) ≤ _`.

Rewrite using `[hz0]`. Conclude with `hmod 1`. Express the relevant statement in the definitionally equal form `(modulus (z.val 1 i) : ℝ) ≤ _`. Rewrite using `[hz1]`. Conclude with `hmod 0`.

Apply `le_max_of_le_right` to reduce the goal to its premises. Take `⟨X, hX⟩` from `exists_ne_of_Rpart_ne ψ _ hz`. Establish `hmem : cat3 ((z⁻¹ : GL (Fin 2) F).val * toM X * (tinv h).val) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) ∈ tsupport Φ` using `subset_tsupport _ (Function.mem_support.2 hX)`. Establish `h1` using `hR₂ (Set.mem_image_of_mem g hmem)`. Establish `h2 : g (cat3 ((z⁻¹ : GL (Fin 2) F).val * toM X * (tinv h).val) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1)) = (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0) : ℝ) + (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1) : ℝ)`.

Simplify using `[g, cat3]`. Rewrite `h1` using `[h2]`. Establish `n0` using `(modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0)).coe_nonneg`. Establish `n1` using `(modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1)).coe_nonneg`. Use `fin_cases a`.

Express the relevant statement in the definitionally equal form `(modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0) : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion. Express the relevant statement in the definitionally equal form `(modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1) : ℝ) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem support_bounded : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F, ∃ R : ℝ, ∀ z : GL (Fin 2) F, Rpart ψ (Pf Φ h z) ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) ∧ (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ h
  have hΦ' : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin 2) (Fin 3) F) := hΦ
  have hev := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΦ'

  let U : Set F := {t | ∀ i j : Fin 2, ∀ x, Φ (x + cat3 (Matrix.single i j t) 0) = Φ x}
  have hU : U ∈ 𝓝 (0 : F) := by
    have hij : ∀ i j : Fin 2, ∀ᶠ t : F in 𝓝 0, ∀ x, Φ (x + cat3 (Matrix.single i j t) 0) = Φ x := by
      intro i j
      have hc := (continuous_concatenate_single_entry (F := F) i j).tendsto 0
      have h0 : cat3 (Matrix.single i j (0 : F)) (0 : Fin 2 → F) = 0 := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [cat3]
      rw [h0] at hc
      exact hc.eventually hev
    have := Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)
    exact this
  obtain ⟨R₀, hR₀, hb⟩ := scalar_bound ψ hψ.2.1 hU

  let g : Matrix (Fin 2) (Fin 3) F → ℝ := fun m => (modulus (m 0 2) : ℝ) + (modulus (m 1 2) : ℝ)
  have hg : Continuous g := by
    have hm : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
    exact (hm.comp (continuous_id.matrix_elem 0 2)).add (hm.comp (continuous_id.matrix_elem 1 2))
  obtain ⟨R₂, hR₂⟩ := ((show IsCompact (tsupport Φ) from hΦ.2).image hg).bddAbove
  let B : Matrix (Fin 2) (Fin 2) F := (tinv h).val
  let A : Matrix (Fin 2) (Fin 2) F := ((tinv h)⁻¹ : GL (Fin 2) F).val
  have hBA : B * A = 1 := by
    change (tinv h).val * ((tinv h)⁻¹ : GL (Fin 2) F).val = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let S : ℝ := ∑ r, ∑ s, (modulus (B r s) : ℝ)
  refine ⟨max (S * R₀) R₂, fun z hz => ⟨fun a i => ?_, fun a => ?_⟩⟩
  · apply le_max_of_le_left

    let c : Fin 2 → Fin 2 → F := fun i j => z.val 0 i * A j 1 + z.val 1 i * A j 0
    have hcb : ∀ i j, (modulus (c i j) : ℝ) ≤ R₀ := by
      intro i j
      refine hb _ fun t ht => ?_
      have := char_eq_one_of_Rpart_ne ψ (Pf Φ h z) (z.val * Matrix.single i j t * A)
        (Pf_translate Φ h z _ (ht i j)) hz
      rwa [entry_sum] at this
    have e : ∀ r s, B r 0 * A 0 s + B r 1 * A 1 s = (1 : Matrix (Fin 2) (Fin 2) F) r s := by
      intro r s
      rw [← hBA, Matrix.mul_apply, Fin.sum_univ_two]
    have hz0 : z.val 0 i = B 1 0 * c i 0 + B 1 1 * c i 1 := by
      have e11 := e 1 1
      have e10 := e 1 0
      simp only [Matrix.one_apply_eq] at e11
      simp at e10
      simp only [c]
      linear_combination (-(z.val 0 i)) * e11 - (z.val 1 i) * e10
    have hz1 : z.val 1 i = B 0 0 * c i 0 + B 0 1 * c i 1 := by
      have e00 := e 0 0
      have e01 := e 0 1
      simp only [Matrix.one_apply_eq] at e00
      simp at e01
      simp only [c]
      linear_combination (-(z.val 1 i)) * e00 - (z.val 0 i) * e01
    have hmod : ∀ r, (modulus (B r 0 * c i 0 + B r 1 * c i 1) : ℝ) ≤ S * R₀ := by
      intro r
      refine (modulus_add_le' _ _).trans ?_
      rw [modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul]
      refine bound_of_entries (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) ?_ hR₀ (hcb i 0) (hcb i 1)
      simp only [S, Fin.sum_univ_two]
      have n00 := (modulus (B 0 0)).coe_nonneg
      have n01 := (modulus (B 0 1)).coe_nonneg
      have n10 := (modulus (B 1 0)).coe_nonneg
      have n11 := (modulus (B 1 1)).coe_nonneg
      fin_cases r <;> simp <;> linarith
    fin_cases a
    · change (modulus (z.val 0 i) : ℝ) ≤ _
      rw [hz0]; exact hmod 1
    · change (modulus (z.val 1 i) : ℝ) ≤ _
      rw [hz1]; exact hmod 0
  · apply le_max_of_le_right
    obtain ⟨X, hX⟩ := exists_ne_of_Rpart_ne ψ _ hz
    have hmem : cat3 ((z⁻¹ : GL (Fin 2) F).val * toM X * (tinv h).val) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) ∈ tsupport Φ :=
      subset_tsupport _ (Function.mem_support.2 hX)
    have h1 := hR₂ (Set.mem_image_of_mem g hmem)
    have h2 : g (cat3 ((z⁻¹ : GL (Fin 2) F).val * toM X * (tinv h).val) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1)) =
        (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0) : ℝ) + (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1) : ℝ) := by
      simp [g, cat3]
    rw [h2] at h1
    have n0 := (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0)).coe_nonneg
    have n1 := (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1)).coe_nonneg
    fin_cases a
    · change (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 0) : ℝ) ≤ _
      linarith
    · change (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) 1) : ℝ) ≤ _
      linarith

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Supp
