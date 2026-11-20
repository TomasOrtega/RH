import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory CongruenceSubgroup Filter Topology ModularGroup
open scoped MatrixGroups ModularForm Modular ENNReal
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.Unfolding

variable {L : ℕ}

/- English proof (translation)
Establish `dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Use `g.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1`. Use `h.det_coe` as an intermediate fact.

Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Use `⟨g 0 1 * h 0 0 - g 0 0 * h 0 1, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.

Rewrite `dg` using `[h10]`. Rewrite `dg` using `[h11]`. Take the linear combination `(h 0 0) * dg - (g 0 0) * dh`. Rewrite `dg` using `[h10]`. Rewrite `dg` using `[h11]`.

Take the linear combination `(h 0 1) * dg - (g 0 1) * dh`. Conclude with `h10`. Conclude with `h11`.
-/
lemma exists_T_zpow (g h : SL(2, ℤ)) (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) :
    ∃ n : ℤ, g = T ^ n * h := by
  have dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe; rwa [Matrix.det_fin_two] at this
  refine ⟨g 0 1 * h 0 0 - g 0 0 * h 0 1, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h10] at dg; rw [h11] at dg; linear_combination (h 0 0) * dg - (g 0 0) * dh
  · rw [h10] at dg; rw [h11] at dg; linear_combination (h 0 1) * dg - (g 0 1) * dh
  · exact h10
  · exact h11

def rep (γ : Idx L → SL(2, ℤ)) (x : Bool × Idx L × ℤ) : SL(2, ℤ) :=
  (if x.1 then -1 else 1) * (T ^ x.2.2 * γ x.2.1)

/- English proof (translation)
The claim follows from `congrFun (T_pow_mul_apply_one n g) 0`.
-/
lemma Tz10 (n : ℤ) (g : SL(2, ℤ)) : (T ^ n * g) 1 0 = g 1 0 :=
  congrFun (T_pow_mul_apply_one n g) 0

/- English proof (translation)
The claim follows from `congrFun (T_pow_mul_apply_one n g) 1`.
-/
lemma Tz11 (n : ℤ) (g : SL(2, ℤ)) : (T ^ n * g) 1 1 = g 1 1 :=
  congrFun (T_pow_mul_apply_one n g) 1

/- English proof (translation)
Take `⟨b, p, n⟩` from `x`. Consider the cases of `b`. Simplify using `only [rep, Bool.false_eq_true, if_false, one_mul]`. Rewrite using `[Tz10]`. Establish `e : rep γ (true, p, n) = -(T ^ n * γ p)` using `by simp [rep]`.

Rewrite using `[e, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Tz10]`. Simplify using the standard rewrite rules.
-/
lemma represents_transfer_one_zero (γ : Idx L → SL(2, ℤ)) (x : Bool × Idx L × ℤ) :
    rep γ x 1 0 = (if x.1 then -1 else 1) * γ x.2.1 1 0 := by
  obtain ⟨b, p, n⟩ := x
  cases b
  · simp only [rep, Bool.false_eq_true, if_false, one_mul]; rw [Tz10]
  · have e : rep γ (true, p, n) = -(T ^ n * γ p) := by simp [rep]
    rw [e, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Tz10]; simp

/- English proof (translation)
Take `⟨b, p, n⟩` from `x`. Consider the cases of `b`. Simplify using `only [rep, Bool.false_eq_true, if_false, one_mul]`. Rewrite using `[Tz11]`. Establish `e : rep γ (true, p, n) = -(T ^ n * γ p)` using `by simp [rep]`.

Rewrite using `[e, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Tz11]`. Simplify using the standard rewrite rules.
-/
lemma represents_transfer_one_one (γ : Idx L → SL(2, ℤ)) (x : Bool × Idx L × ℤ) :
    rep γ x 1 1 = (if x.1 then -1 else 1) * γ x.2.1 1 1 := by
  obtain ⟨b, p, n⟩ := x
  cases b
  · simp only [rep, Bool.false_eq_true, if_false, one_mul]; rw [Tz11]
  · have e : rep γ (true, p, n) = -(T ^ n * γ p) := by simp [rep]
    rw [e, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Tz11]; simp

/- English proof (translation)
Rewrite using `[Gamma0_mem]`. Use `represents_transfer_one_zero γ x` as an intermediate fact. Establish `h2 : rep γ x 1 0 = (L : ℤ) * ((if x.1 then -1 else 1) * x.2.1.1.2)`. Rewrite using `[this, (hγ _).1]`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `((rep γ x 1 0 : ℤ) : ZMod L) = 0`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
lemma rep_mem {γ : Idx L → SL(2, ℤ)} (hγ : ∀ p, γ p 1 0 = L * p.1.2 ∧ γ p 1 1 = p.1.1)
    (x : Bool × Idx L × ℤ) : rep γ x ∈ Gamma0 L := by
  rw [Gamma0_mem]
  have := represents_transfer_one_zero γ x
  have h2 : rep γ x 1 0 = (L : ℤ) * ((if x.1 then -1 else 1) * x.2.1.1.2) := by
    rw [this, (hγ _).1]; ring
  change ((rep γ x 1 0 : ℤ) : ZMod L) = 0
  rw [h2]; simp

/- English proof (translation)
Establish `dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Use `g.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `e : (((g 1 1).toNat : ℕ) : ℤ) = g 1 1` using `Int.toNat_of_nonneg h11.le`. Establish `hcop : IsCoprime ((L : ℤ) * c) (((g 1 1).toNat : ℕ) : ℤ)`.

Rewrite using `[e, ← h10]; exact ⟨-(g 0 1), g 0 0, by linarith⟩`. Set `p : Idx L` to `⟨((g 1 1).toNat, c), by`. Use `⟨?_, hcop⟩` and prove the remaining obligations. Use `show 0 < (g 1 1).toNat`. Use the proof step `omega⟩`.

Take `⟨n, hn⟩` from `exists_T_zpow g (γ p) (by rw [h10, (hγ p).1]) (by rw [(hγ p).2]; exact e.symm)`. Conclude with `⟨p, n, hn⟩`.
-/
lemma exists_idx {γ : Idx L → SL(2, ℤ)} (hγ : ∀ p, γ p 1 0 = L * p.1.2 ∧ γ p 1 1 = p.1.1)
    (g : SL(2, ℤ)) (c : ℤ) (h10 : g 1 0 = L * c) (h11 : 0 < g 1 1) :
    ∃ (p : Idx L) (n : ℤ), g = T ^ n * γ p := by
  have dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have e : (((g 1 1).toNat : ℕ) : ℤ) = g 1 1 := Int.toNat_of_nonneg h11.le
  have hcop : IsCoprime ((L : ℤ) * c) (((g 1 1).toNat : ℕ) : ℤ) := by
    rw [e, ← h10]; exact ⟨-(g 0 1), g 0 0, by linarith⟩
  let p : Idx L := ⟨((g 1 1).toNat, c), by
    refine ⟨?_, hcop⟩
    show 0 < (g 1 1).toNat
    omega⟩
  obtain ⟨n, hn⟩ := exists_T_zpow g (γ p) (by rw [h10, (hγ p).1]) (by rw [(hγ p).2]; exact e.symm)
  exact ⟨p, n, hn⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, p, n⟩ ⟨b', p', n'⟩ h`. Establish `h' : rep γ (b, p, n) = rep γ (b', p', n')` using `congrArg Subtype.val h`. Establish `r0` using `represents_transfer_one_zero γ (b, p, n)`. Establish `r0'` using `represents_transfer_one_zero γ (b', p', n')`.

Establish `r1` using `represents_transfer_one_one γ (b, p, n)`. Establish `r1'` using `represents_transfer_one_one γ (b', p', n')`. Rewrite `r0` using `[h', r0']`. Rewrite `r1` using `[h', r1']`. Simplify using `only at r0 r1`.

Rewrite `r0` using `[(hγ p).1, (hγ p').1]`. Rewrite `r1` using `[(hγ p).2, (hγ p').2]`. Establish `hd : (0 : ℤ) < p.1.1` using `by exact_mod_cast p.2.1`. Establish `hd' : (0 : ℤ) < p'.1.1` using `by exact_mod_cast p'.2.1`. Establish `hL0 : (L : ℤ) ≠ 0`.

Establish `: (2 : ℤ) ≤ L` using `by exact_mod_cast hL`. Use linear arithmetic over natural numbers and integers. Establish `hb : b = b'`. Apply the tactic sequence `cases b <;> cases b' <;> simp at r1 ⊢ <;> omega`. Substitute `hb` using the available equality.

Apply the tactic sequence `have hs : ((if b then -1 else 1 : ℤ)) ≠ 0 := by cases b <;> simp`. Establish `e1 : p'.1.1 = p.1.1`. Use `mul_left_cancel₀ hs r1` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `e2 : p'.1.2 = p.1.2`.

Use `mul_left_cancel₀ hs r0` as an intermediate fact. Conclude with `mul_left_cancel₀ hL0 this`. Establish `hp : p' = p` using `Subtype.ext (Prod.ext e1 e2)`. Substitute `hp` using the available equality. Establish `h3 : T ^ n * γ p' = T ^ n' * γ p'`.

Establish `hu : IsUnit ((if b then -1 else 1 : SL(2, ℤ)))`. Conclude with `Group.isUnit _`. Conclude with `mul_left_cancel (a := (if b then -1 else 1 : SL(2, ℤ))) h'`. Establish `h4 : T ^ n = T ^ n'` using `mul_right_cancel h3`. Establish `h5` using `congrArg (fun m : SL(2, ℤ) => m.1 0 1) h4`.

Simplify using `only [coe_T_zpow] at h5`. Establish `h6 : n = n'` using `by simpa using h5`. Rewrite using `[h6]`. Introduce and unpack `⟨g, hg⟩`. Establish `hLc : (L : ℤ) ∣ g 1 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hg)`.

Take `⟨c, hc⟩` from `hLc`. Establish `dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Use `g.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `hd : g 1 1 ≠ 0`.

Introduce `h0`. Rewrite `dg` using `[h0, hc]`. Establish `h1 : (L : ℤ) ∣ 1` using `⟨-(g 0 1 * c), by linarith⟩`. Use `Int.le_of_dvd one_pos h1` as an intermediate fact. Establish `: (2 : ℤ) ≤ L` using `by exact_mod_cast hL`.

Use linear arithmetic over natural numbers and integers. Break down `lt_or_gt_of_ne hd with hneg | hpos` into its components or cases. Take `⟨p, n, h⟩` from `exists_idx hγ (-g) (-c) (by simp [hc]) (by simpa using hneg)`. Use `⟨(true, p, n), Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [rep, if_true]`.

Rewrite using `[← h]`. Simplify using the standard rewrite rules. Take `⟨p, n, h⟩` from `exists_idx hγ g c hc hpos`. Use `⟨(false, p, n), Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[rep, ← h]`.
-/
theorem rep_bijective (hL : 2 ≤ L) {γ : Idx L → SL(2, ℤ)}
    (hγ : ∀ p, γ p 1 0 = L * p.1.2 ∧ γ p 1 1 = p.1.1) :
    Function.Bijective (fun x => (⟨rep γ x, rep_mem hγ x⟩ : Gamma0 L)) := by
  constructor
  · rintro ⟨b, p, n⟩ ⟨b', p', n'⟩ h
    have h' : rep γ (b, p, n) = rep γ (b', p', n') := congrArg Subtype.val h
    have r0 := represents_transfer_one_zero γ (b, p, n)
    have r0' := represents_transfer_one_zero γ (b', p', n')
    have r1 := represents_transfer_one_one γ (b, p, n)
    have r1' := represents_transfer_one_one γ (b', p', n')
    rw [h', r0'] at r0
    rw [h', r1'] at r1
    simp only at r0 r1
    rw [(hγ p).1, (hγ p').1] at r0
    rw [(hγ p).2, (hγ p').2] at r1
    have hd : (0 : ℤ) < p.1.1 := by exact_mod_cast p.2.1
    have hd' : (0 : ℤ) < p'.1.1 := by exact_mod_cast p'.2.1
    have hL0 : (L : ℤ) ≠ 0 := by
      have : (2 : ℤ) ≤ L := by exact_mod_cast hL
      omega
    have hb : b = b' := by
      cases b <;> cases b' <;> simp at r1 ⊢ <;> omega
    subst hb
    have hs : ((if b then -1 else 1 : ℤ)) ≠ 0 := by cases b <;> simp
    have e1 : p'.1.1 = p.1.1 := by
      have := mul_left_cancel₀ hs r1
      exact_mod_cast this
    have e2 : p'.1.2 = p.1.2 := by
      have := mul_left_cancel₀ hs r0
      exact mul_left_cancel₀ hL0 this
    have hp : p' = p := Subtype.ext (Prod.ext e1 e2)
    subst hp
    have h3 : T ^ n * γ p' = T ^ n' * γ p' := by
      have hu : IsUnit ((if b then -1 else 1 : SL(2, ℤ))) := by
        exact Group.isUnit _
      exact mul_left_cancel (a := (if b then -1 else 1 : SL(2, ℤ))) h'
    have h4 : T ^ n = T ^ n' := mul_right_cancel h3
    have h5 := congrArg (fun m : SL(2, ℤ) => m.1 0 1) h4
    simp only [coe_T_zpow] at h5
    have h6 : n = n' := by simpa using h5
    rw [h6]
  · rintro ⟨g, hg⟩
    have hLc : (L : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hg)
    obtain ⟨c, hc⟩ := hLc
    have dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      have := g.det_coe; rwa [Matrix.det_fin_two] at this
    have hd : g 1 1 ≠ 0 := by
      intro h0
      rw [h0, hc] at dg
      have h1 : (L : ℤ) ∣ 1 := ⟨-(g 0 1 * c), by linarith⟩
      have := Int.le_of_dvd one_pos h1
      have : (2 : ℤ) ≤ L := by exact_mod_cast hL
      omega
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · obtain ⟨p, n, h⟩ := exists_idx hγ (-g) (-c)
        (by simp [hc]) (by simpa using hneg)
      refine ⟨(true, p, n), Subtype.ext ?_⟩
      simp only [rep, if_true]
      rw [← h]; simp
    · obtain ⟨p, n, h⟩ := exists_idx hγ g c hc hpos
      refine ⟨(false, p, n), Subtype.ext ?_⟩
      simp [rep, ← h]

/- English proof (translation)
Conclude with `measurePreserving_smul (g : GL (Fin 2) ℝ) volume`.
-/
lemma mp_smul (g : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => g • z) volume volume := by
  exact measurePreserving_smul (g : GL (Fin 2) ℝ) volume

/- English proof (translation)
Use `MeasurableEquiv.measurableEmbedding (⟨⟨fun z : ℍ => g • z, fun z : ℍ => g⁻¹ • z, fun z => by simp [-sl_moeb], fun z => by simp [-sl_moeb]⟩, (mp_smul g).measurable, (mp_smul g⁻¹).measurable⟩ : ℍ ≃ᵐ ℍ)` and prove the remaining obligations.
-/
lemma me_smul (g : SL(2, ℤ)) : MeasurableEmbedding (fun z : ℍ => g • z) := by
  refine MeasurableEquiv.measurableEmbedding
    (⟨⟨fun z : ℍ => g • z, fun z : ℍ => g⁻¹ • z, fun z => by simp [-sl_moeb], fun z => by simp [-sl_moeb]⟩,
      (mp_smul g).measurable, (mp_smul g⁻¹).measurable⟩ : ℍ ≃ᵐ ℍ)

instance : Countable (Idx L) := by
  unfold Idx; infer_instance

instance : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by unfold Matrix; infer_instance
  exact Function.Injective.countable (f := fun g : SL(2, ℤ) => g.1) Subtype.val_injective

/- English proof (translation)
The claim follows from `(Equiv.inv (Gamma0 L)).hasSum_iff.2 (hβ.2.2 z)`.
-/
lemma hasSum_weight {β : ℍ → ℝ} (hβ : IsWt L β) (z : ℍ) :
    HasSum (fun γ : Gamma0 L => β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) 2 :=
  (Equiv.inv (Gamma0 L)).hasSum_iff.2 (hβ.2.2 z)

/- English proof (translation)
Establish `h` using `hasSum_weight hβ z`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun γ => (hβ.2.1 _).1) h.summable, h.tsum_eq]`. Simplify using the standard rewrite rules.
-/
lemma tsum_weight {β : ℍ → ℝ} (hβ : IsWt L β) (z : ℍ) :
    ∑' γ : Gamma0 L, ENNReal.ofReal (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) = 2 := by
  have h := hasSum_weight hβ z
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun γ => (hβ.2.1 _).1) h.summable, h.tsum_eq]
  simp

/- English proof (translation)
Establish `hm : ∀ γ : Gamma0 L, Measurable fun z : ℍ => ENNReal.ofReal (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) * g z` using `fun γ => (ENNReal.measurable_ofReal.comp (hβ.1.comp (mp_smul _).measurable)).mul hg`. Establish `h1 : ∀ γ : Gamma0 L, ∫⁻ w, ENNReal.ofReal (β w) * g ((γ : SL(2, ℤ)) • w) = ∫⁻ z, ENNReal.ofReal (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) * g z`. Introduce `γ`. Rewrite using `[← (mp_smul (γ : SL(2, ℤ))).lintegral_comp (hm γ)]`. Use `lintegral_congr fun w => ?_` and prove the remaining obligations.

Simplify using `[-sl_moeb]`. Repeatedly rewrite using `[h1]`. Rewrite using `[← lintegral_tsum fun γ => (hm γ).aemeasurable]`. Repeatedly rewrite using `[ENNReal.tsum_mul_right, tsum_weight hβ]`. Rewrite using `[lintegral_const_mul _ hg]`.
-/
lemma lintegral_weight {β : ℍ → ℝ} (hβ : IsWt L β) {g : ℍ → ℝ≥0∞} (hg : Measurable g) :
    ∑' γ : Gamma0 L, ∫⁻ w, ENNReal.ofReal (β w) * g ((γ : SL(2, ℤ)) • w) = 2 * ∫⁻ z, g z := by
  have hm : ∀ γ : Gamma0 L, Measurable fun z : ℍ =>
      ENNReal.ofReal (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) * g z := fun γ =>
    (ENNReal.measurable_ofReal.comp (hβ.1.comp (mp_smul _).measurable)).mul hg
  have h1 : ∀ γ : Gamma0 L, ∫⁻ w, ENNReal.ofReal (β w) * g ((γ : SL(2, ℤ)) • w) =
      ∫⁻ z, ENNReal.ofReal (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z)) * g z := by
    intro γ
    rw [← (mp_smul (γ : SL(2, ℤ))).lintegral_comp (hm γ)]
    refine lintegral_congr fun w => ?_
    simp [-sl_moeb]
  simp_rw [h1]
  rw [← lintegral_tsum fun γ => (hm γ).aemeasurable]
  simp_rw [ENNReal.tsum_mul_right, tsum_weight hβ]
  rw [lintegral_const_mul _ hg]

/- English proof (translation)
Rewrite using `[enorm_mul, ← ofReal_norm_eq_enorm (β w : ℂ), Complex.norm_real, Real.norm_of_nonneg (hβ.2.1 w).1]`.
-/
lemma enorm_wt {β : ℍ → ℝ} (hβ : IsWt L β) (w : ℍ) (x : ℂ) :
    ‖(β w : ℂ) * x‖ₑ = ENNReal.ofReal (β w) * ‖x‖ₑ := by
  rw [enorm_mul, ← ofReal_norm_eq_enorm (β w : ℂ), Complex.norm_real, Real.norm_of_nonneg (hβ.2.1 w).1]

/- English proof (translation)
Establish `hg : Measurable fun z => ‖h z‖ₑ` using `hm.enorm`. Establish `hA` using `lintegral_weight hβ hg`. Establish `hmeas : ∀ γ : Gamma0 L, AEMeasurable fun w : ℍ => ENNReal.ofReal (β w) * ‖h ((γ : SL(2, ℤ)) • w)‖ₑ` using `fun γ => ((ENNReal.measurable_ofReal.comp hβ.1).mul (hg.comp (mp_smul _).measurable)).aemeasurable`. Rewrite `hA` using `[← lintegral_tsum hmeas]`. Establish `hfin : ∫⁻ w, ∑' γ : Gamma0 L, ENNReal.ofReal (β w) * ‖h ((γ : SL(2, ℤ)) • w)‖ₑ ≠ ∞`.

Rewrite using `[hA]`. Conclude with `ENNReal.mul_ne_top (by simp) hi.2.ne`. Establish `hae` using `ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hfin`. Use `filter_upwards [hae] with w hw`. Use `ENNReal.summable_toReal hw.ne` as an intermediate fact.

Use `this.congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[← enorm_wt hβ, toReal_enorm]`.
-/
lemma ae_summable {β : ℍ → ℝ} (hβ : IsWt L β) {h : ℍ → ℂ} (hm : Measurable h) (hi : Integrable h) :
    ∀ᵐ w, Summable fun γ : Gamma0 L => ‖(β w : ℂ) * h ((γ : SL(2, ℤ)) • w)‖ := by
  have hg : Measurable fun z => ‖h z‖ₑ := hm.enorm
  have hA := lintegral_weight hβ hg
  have hmeas : ∀ γ : Gamma0 L, AEMeasurable fun w : ℍ =>
      ENNReal.ofReal (β w) * ‖h ((γ : SL(2, ℤ)) • w)‖ₑ := fun γ =>
    ((ENNReal.measurable_ofReal.comp hβ.1).mul (hg.comp (mp_smul _).measurable)).aemeasurable
  rw [← lintegral_tsum hmeas] at hA
  have hfin : ∫⁻ w, ∑' γ : Gamma0 L, ENNReal.ofReal (β w) * ‖h ((γ : SL(2, ℤ)) • w)‖ₑ ≠ ∞ := by
    rw [hA]
    exact ENNReal.mul_ne_top (by simp) hi.2.ne
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hfin
  filter_upwards [hae] with w hw
  have := ENNReal.summable_toReal hw.ne
  refine this.congr fun γ => ?_
  rw [← enorm_wt hβ, toReal_enorm]

/- English proof (translation)
Use `set f : Gamma0 L → ℍ → ℂ := fun γ w => (β w : ℂ) * h ((γ : SL(2, ℤ)) • w) with hf`. Use `set g : Gamma0 L → ℍ → ℂ := fun γ z => (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z) : ℂ) * h z with hgdef`. Establish `hβc : Measurable fun w => (β w : ℂ)` using `Complex.measurable_ofReal.comp hβ.1`. Establish `hfm : ∀ γ, Measurable (f γ)` using `fun γ => hβc.mul (hm.comp (mp_smul _).measurable)`. Establish `hgm : ∀ γ, Measurable (g γ)` using `fun γ => (hβc.comp (mp_smul _).measurable).mul hm`.

Establish `hle : ∀ w (x : ℂ), ‖(β w : ℂ) * x‖ ≤ ‖x‖` using `fun w x => by`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ.2.1 w).1]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hβ.2.1 w).2`. Establish `hfi : ∀ γ, Integrable (f γ)` using `fun γ => ((mp_smul (γ : SL(2, ℤ))).integrable_comp_of_integrable hi).mono (hfm γ).aestronglyMeasurable (ae_of_all _ fun w => hle _ _)`. Establish `hgi : ∀ γ, Integrable (g γ)` using `fun γ => hi.mono (hgm γ).aestronglyMeasurable (ae_of_all _ fun w => hle _ _)`.

Establish `hfg : ∀ γ, ∫ w, f γ w = ∫ z, g γ z` using `fun γ => by`. Rewrite using `[← (mp_smul (γ : SL(2, ℤ))).integral_comp (me_smul _) (g γ)]`. Use `integral_congr_ae (ae_of_all _ fun w => ?_)` and prove the remaining obligations. Simplify using `[hf, hgdef, -sl_moeb]`. Establish `hfgn : ∀ γ, ∫ w, ‖f γ w‖ = ∫ z, ‖g γ z‖` using `fun γ => by`.

Rewrite using `[← (mp_smul (γ : SL(2, ℤ))).integral_comp (me_smul _) (fun z => ‖g γ z‖)]`. Use `integral_congr_ae (ae_of_all _ fun w => ?_)` and prove the remaining obligations. Simplify using `[hf, hgdef, -sl_moeb]`. Establish `hsum : Summable fun γ => ∫ w, ‖f γ w‖`. Establish `hA` using `lintegral_weight hβ (hm.enorm)`.

Establish `hfin : ∑' γ : Gamma0 L, ∫⁻ w, ‖f γ w‖ₑ ≠ ∞`. Simplify using `only [hf, enorm_wt hβ]`. Rewrite using `[hA]`. Conclude with `ENNReal.mul_ne_top (by simp) hi.2.ne`. Use `(ENNReal.summable_toReal hfin).congr fun γ => ?_` and prove the remaining obligations.

Rewrite using `[integral_norm_eq_lintegral_enorm (hfi γ).1]`. Establish `S1` using `hasSum_integral_of_summable_integral_norm hfi hsum`. Establish `S2` using `hasSum_integral_of_summable_integral_norm hgi (by simpa only [hfgn] using hsum)`. Simplify using `only [← hfg] at S2`. Rewrite using `[S1.unique S2]`.

Establish `h2 : ∀ z, ∑' γ, g γ z = 2 * h z` using `fun z => by`. Use `(Complex.hasSum_ofReal.2 (hasSum_weight hβ z)).mul_right (h z)` as an intermediate fact. Establish `e` using `this.tsum_eq`. Rewrite `e` using `[Complex.ofReal_ofNat]`. Conclude with `e`.

Repeatedly rewrite using `[h2]`. Conclude with `integral_const_mul _ _`.
-/
lemma integral_weight {β : ℍ → ℝ} (hβ : IsWt L β) {h : ℍ → ℂ} (hm : Measurable h) (hi : Integrable h) :
    ∫ w, ∑' γ : Gamma0 L, (β w : ℂ) * h ((γ : SL(2, ℤ)) • w) = 2 * ∫ z, h z := by
  set f : Gamma0 L → ℍ → ℂ := fun γ w => (β w : ℂ) * h ((γ : SL(2, ℤ)) • w) with hf
  set g : Gamma0 L → ℍ → ℂ := fun γ z => (β (((γ⁻¹ : Gamma0 L) : SL(2, ℤ)) • z) : ℂ) * h z with hgdef
  have hβc : Measurable fun w => (β w : ℂ) := Complex.measurable_ofReal.comp hβ.1
  have hfm : ∀ γ, Measurable (f γ) := fun γ => hβc.mul (hm.comp (mp_smul _).measurable)
  have hgm : ∀ γ, Measurable (g γ) := fun γ => (hβc.comp (mp_smul _).measurable).mul hm
  have hle : ∀ w (x : ℂ), ‖(β w : ℂ) * x‖ ≤ ‖x‖ := fun w x => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ.2.1 w).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hβ.2.1 w).2
  have hfi : ∀ γ, Integrable (f γ) := fun γ =>
    ((mp_smul (γ : SL(2, ℤ))).integrable_comp_of_integrable hi).mono (hfm γ).aestronglyMeasurable
      (ae_of_all _ fun w => hle _ _)
  have hgi : ∀ γ, Integrable (g γ) := fun γ =>
    hi.mono (hgm γ).aestronglyMeasurable (ae_of_all _ fun w => hle _ _)
  have hfg : ∀ γ, ∫ w, f γ w = ∫ z, g γ z := fun γ => by
    rw [← (mp_smul (γ : SL(2, ℤ))).integral_comp (me_smul _) (g γ)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [hf, hgdef, -sl_moeb]
  have hfgn : ∀ γ, ∫ w, ‖f γ w‖ = ∫ z, ‖g γ z‖ := fun γ => by
    rw [← (mp_smul (γ : SL(2, ℤ))).integral_comp (me_smul _) (fun z => ‖g γ z‖)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [hf, hgdef, -sl_moeb]
  have hsum : Summable fun γ => ∫ w, ‖f γ w‖ := by
    have hA := lintegral_weight hβ (hm.enorm)
    have hfin : ∑' γ : Gamma0 L, ∫⁻ w, ‖f γ w‖ₑ ≠ ∞ := by
      simp only [hf, enorm_wt hβ]
      rw [hA]
      exact ENNReal.mul_ne_top (by simp) hi.2.ne
    refine (ENNReal.summable_toReal hfin).congr fun γ => ?_
    rw [integral_norm_eq_lintegral_enorm (hfi γ).1]
  have S1 := hasSum_integral_of_summable_integral_norm hfi hsum
  have S2 := hasSum_integral_of_summable_integral_norm hgi (by simpa only [hfgn] using hsum)
  simp only [← hfg] at S2
  rw [S1.unique S2]
  have h2 : ∀ z, ∑' γ, g γ z = 2 * h z := fun z => by
    have := (Complex.hasSum_ofReal.2 (hasSum_weight hβ z)).mul_right (h z)
    have e := this.tsum_eq
    rw [Complex.ofReal_ofNat] at e
    exact e
  simp_rw [h2]
  exact integral_const_mul _ _

/- English proof (translation)
Establish `hT : ∀ z : ℍ, F (T • z) = F z` using `fun z => by rw [modular_T_smul, hF]`. Establish `per : ∀ (n : ℤ) (z : ℍ), F ((T ^ n : SL(2, ℤ)) • z) = F z`. Introduce `n`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simp [-sl_moeb]`.

Consider the case `succ i ih`. Introduce `z`. Rewrite using `[add_comm, zpow_one_add, mul_smul, hT, ih]`. Consider the case `pred i ih`. Introduce `z`.

Establish `e : T • ((T ^ (-(i : ℤ) - 1) : SL(2, ℤ)) • z) = (T ^ (-(i : ℤ)) : SL(2, ℤ)) • z`. Rewrite using `[← mul_smul, ← zpow_one_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hT, e, ih]`.

Establish `hre : ∀ n : ℤ, (((T ^ n : SL(2, ℤ)) • u : ℍ)).re = u.re + n` using `fun n => re_T_zpow_smul u n`. Rewrite using `[tsum_eq_single (-⌊u.re⌋)]`. Rewrite using `[Set.indicator_of_mem, per] show 0 ≤ _ ∧ _ < _`. Rewrite using `[hre]`. Use `push_cast`.

Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[Int.floor_le u.re]`. Combine the linear relations using `[Int.lt_floor_add_one u.re]`. Introduce `n hn`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises.

Introduce and unpack `⟨h0, h1⟩`. Rewrite `h0`, `h1` using `[hre]`. Apply `hn` to reduce the goal to its premises. Establish `: ⌊u.re⌋ = -n`. Apply the tactic sequence `rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith`.

Use linear arithmetic over natural numbers and integers.
-/
lemma T_zpow_smul_strip {F : ℍ → ℂ} (hF : ∀ z, F ((1 : ℝ) +ᵥ z) = F z) (u : ℍ) :
    ∑' n : ℤ, strip.indicator F ((T ^ n : SL(2, ℤ)) • u) = F u := by
  have hT : ∀ z : ℍ, F (T • z) = F z := fun z => by rw [modular_T_smul, hF]
  have per : ∀ (n : ℤ) (z : ℍ), F ((T ^ n : SL(2, ℤ)) • z) = F z := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [-sl_moeb]
    | succ i ih =>
      intro z
      rw [add_comm, zpow_one_add, mul_smul, hT, ih]
    | pred i ih =>
      intro z
      have e : T • ((T ^ (-(i : ℤ) - 1) : SL(2, ℤ)) • z) = (T ^ (-(i : ℤ)) : SL(2, ℤ)) • z := by
        rw [← mul_smul, ← zpow_one_add]; congr 2; ring
      rw [← hT, e, ih]
  have hre : ∀ n : ℤ, (((T ^ n : SL(2, ℤ)) • u : ℍ)).re = u.re + n := fun n => re_T_zpow_smul u n
  rw [tsum_eq_single (-⌊u.re⌋)]
  · rw [Set.indicator_of_mem, per]
    show 0 ≤ _ ∧ _ < _
    rw [hre]
    push_cast
    constructor
    · linarith [Int.floor_le u.re]
    · linarith [Int.lt_floor_add_one u.re]
  · intro n hn
    apply Set.indicator_of_notMem
    rintro ⟨h0, h1⟩
    rw [hre] at h0 h1
    apply hn
    have : ⌊u.re⌋ = -n := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega

/- English proof (translation)
Take `⟨b, p, n⟩` from `x`. Consider the cases of `b`. Simplify using `[rep, mul_smul, -sl_moeb]`. Establish `e : rep γ (true, p, n) = -(T ^ n * γ p)` using `by simp [rep]`. Rewrite using `[e, SL_neg_smul, mul_smul]`.
-/
lemma rep_smul (γ : Idx L → SL(2, ℤ)) (x : Bool × Idx L × ℤ) (w : ℍ) :
    rep γ x • w = (T ^ x.2.2 : SL(2, ℤ)) • (γ x.2.1 • w) := by
  obtain ⟨b, p, n⟩ := x
  cases b
  · simp [rep, mul_smul, -sl_moeb]
  · have e : rep γ (true, p, n) = -(T ^ n * γ p) := by simp [rep]
    rw [e, SL_neg_smul, mul_smul]

/- English proof (translation)
Set `e : Bool × Idx L × ℤ ≃ Gamma0 L` to `Equiv.ofBijective _ (rep_bijective hL hγ)`. Establish `he : ∀ x, ((e x : Gamma0 L) : SL(2, ℤ)) = rep γ x` using `fun x => rfl`. Use `set f : Bool × Idx L × ℤ → ℂ := fun x => strip.indicator F (rep γ x • w) with hf`. Establish `hs' : Summable f`. Use `(e.summable_iff).2 hs` as an intermediate fact.

Use `this.congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, he, hf]`. Establish `hrw : ∑' g : Gamma0 L, strip.indicator F ((g : SL(2, ℤ)) • w) = ∑' x, f x`. Rewrite using `[← e.tsum_eq]`. Simplify using `only [he, hf]`.

Establish `hfb : ∀ (b : Bool) (q : Idx L × ℤ), f (b, q) = strip.indicator F ((T ^ q.2 : SL(2, ℤ)) • (γ q.1 • w))` using `fun b q => by`. Simplify using `only [hf, rep_smul]`. Establish `hq : Summable fun q : Idx L × ℤ => strip.indicator F ((T ^ q.2 : SL(2, ℤ)) • (γ q.1 • w))`. Use `hs'.comp_injective (i := fun q : Idx L × ℤ => (false, q)) (fun a b h => by simpa using h)` as an intermediate fact. Use `this.congr fun q => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp, hfb]`. Rewrite using `[hrw, hs'.tsum_prod, tsum_bool]`. Simplify using `only [hfb]`. Rewrite using `[hq.tsum_prod]`. Simplify using `only [T_zpow_smul_strip hF]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma tsum_cosets (hL : 2 ≤ L) {γ : Idx L → SL(2, ℤ)}
    (hγ : ∀ p, γ p 1 0 = L * p.1.2 ∧ γ p 1 1 = p.1.1) {F : ℍ → ℂ}
    (hF : ∀ z, F ((1 : ℝ) +ᵥ z) = F z) (w : ℍ)
    (hs : Summable fun g : Gamma0 L => strip.indicator F ((g : SL(2, ℤ)) • w)) :
    ∑' g : Gamma0 L, strip.indicator F ((g : SL(2, ℤ)) • w) = 2 * ∑' p, F (γ p • w) := by
  let e : Bool × Idx L × ℤ ≃ Gamma0 L := Equiv.ofBijective _ (rep_bijective hL hγ)
  have he : ∀ x, ((e x : Gamma0 L) : SL(2, ℤ)) = rep γ x := fun x => rfl
  set f : Bool × Idx L × ℤ → ℂ := fun x => strip.indicator F (rep γ x • w) with hf
  have hs' : Summable f := by
    have := (e.summable_iff).2 hs
    refine this.congr fun x => ?_
    simp only [Function.comp, he, hf]
  have hrw : ∑' g : Gamma0 L, strip.indicator F ((g : SL(2, ℤ)) • w) = ∑' x, f x := by
    rw [← e.tsum_eq]
    simp only [he, hf]
  have hfb : ∀ (b : Bool) (q : Idx L × ℤ),
      f (b, q) = strip.indicator F ((T ^ q.2 : SL(2, ℤ)) • (γ q.1 • w)) := fun b q => by
    simp only [hf, rep_smul]
  have hq : Summable fun q : Idx L × ℤ => strip.indicator F ((T ^ q.2 : SL(2, ℤ)) • (γ q.1 • w)) := by
    have := hs'.comp_injective (i := fun q : Idx L × ℤ => (false, q)) (fun a b h => by simpa using h)
    refine this.congr fun q => ?_
    simp only [Function.comp, hfb]
  rw [hrw, hs'.tsum_prod, tsum_bool]
  simp only [hfb]
  rw [hq.tsum_prod]
  simp only [T_zpow_smul_strip hF]
  ring

/- English proof (translation)
Introduce `L hL β hβ γ hγ F hFm hF hFi`. Establish `hstrip : MeasurableSet strip`. Establish `: Measurable fun z : ℍ => z.re` using `UpperHalfPlane.continuous_re.measurable`. Conclude with `(measurableSet_le measurable_const this).inter (measurableSet_lt this measurable_const)`. Use `set H : ℍ → ℂ := strip.indicator F with hH`.

Establish `hHm : Measurable H` using `hFm.indicator hstrip`. Establish `hHi : Integrable H` using `hFi.integrable_indicator hstrip`. Establish `hmain` using `integral_weight hβ hHm hHi`. Establish `hae : (fun w => ∑' g : Gamma0 L, (β w : ℂ) * H ((g : SL(2, ℤ)) • w)) =ᵐ[volume] fun w => 2 * ((β w : ℂ) * ∑' p, F (γ p • w))` using `by filter_upwards [ae_summable hβ hHm hHi] with w hw`. Rewrite using `[tsum_mul_left]`.

Distinguish the cases in `h0 : (β w : ℂ) = 0`. Simplify using `[h0]`. Establish `hs : Summable fun g : Gamma0 L => H ((g : SL(2, ℤ)) • w)`. Use `hw.of_norm` as an intermediate fact. Simplify `(summable_mul_left_iff h0).1 this` using `[h0, -sl_moeb]`.

Rewrite using `[tsum_cosets hL hγ hF w hs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hmain` using `[integral_congr_ae hae, integral_const_mul, integral_indicator hstrip]`. Conclude with `(mul_left_cancel₀ two_ne_zero hmain).symm`.
-/
theorem unfolding_strip : U1 := by
  intro L hL β hβ γ hγ F hFm hF hFi
  have hstrip : MeasurableSet strip := by
    have : Measurable fun z : ℍ => z.re := UpperHalfPlane.continuous_re.measurable
    exact (measurableSet_le measurable_const this).inter (measurableSet_lt this measurable_const)
  set H : ℍ → ℂ := strip.indicator F with hH
  have hHm : Measurable H := hFm.indicator hstrip
  have hHi : Integrable H := hFi.integrable_indicator hstrip
  have hmain := integral_weight hβ hHm hHi
  have hae : (fun w => ∑' g : Gamma0 L, (β w : ℂ) * H ((g : SL(2, ℤ)) • w)) =ᵐ[volume]
      fun w => 2 * ((β w : ℂ) * ∑' p, F (γ p • w)) := by
    filter_upwards [ae_summable hβ hHm hHi] with w hw
    rw [tsum_mul_left]
    by_cases h0 : (β w : ℂ) = 0
    · simp [h0]
    · have hs : Summable fun g : Gamma0 L => H ((g : SL(2, ℤ)) • w) := by
        have := hw.of_norm
        simpa [h0, -sl_moeb] using (summable_mul_left_iff h0).1 this
      rw [tsum_cosets hL hγ hF w hs]
      ring
  rw [integral_congr_ae hae, integral_const_mul, integral_indicator hstrip] at hmain
  exact (mul_left_cancel₀ two_ne_zero hmain).symm

end GlobalTheory.CompanionTheory.Unfolding
