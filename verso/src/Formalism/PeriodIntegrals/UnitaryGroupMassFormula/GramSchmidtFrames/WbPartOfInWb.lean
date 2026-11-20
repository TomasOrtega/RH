import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.PhiMulVec

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca2

variable {k r : ℕ}

/- English proof (translation)
Take `⟨hp1, hp2⟩` from `hp`. Take `⟨hq1, hq2⟩` from `hq`. Use `show inWb k r (p - q) ∧ herm (Hpk k r) (p - q) z = 0`. Use `⟨fun i hi => by simp [hp1 i hi, hq1 i hi], ?_⟩` and prove the remaining obligations. Simplify using `only [herm, Matrix.mulVec_sub, dotProduct_sub] at hp2 hq2 ⊢`.

Rewrite using `[hp2, hq2, sub_zero]`.
-/
lemma Wsp_sub {z p q : Fin (2 * r + k + 1) → ℂ} (hp : p ∈ Wsp k r z) (hq : q ∈ Wsp k r z) : p - q ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  show inWb k r (p - q) ∧ herm (Hpk k r) (p - q) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi, hq1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub] at hp2 hq2 ⊢
  rw [hp2, hq2, sub_zero]

/- English proof (translation)
Take `⟨hp1, hp2⟩` from `hp`. Use `show inWb k r (c • p) ∧ herm (Hpk k r) (c • p) z = 0`. Use `⟨fun i hi => by simp [hp1 i hi], ?_⟩` and prove the remaining obligations. Simplify using `only [herm, Matrix.mulVec_smul, dotProduct_smul] at hp2 ⊢`. Rewrite using `[hp2, smul_zero]`.
-/
lemma Wsp_smul {z p : Fin (2 * r + k + 1) → ℂ} (c : ℂ) (hp : p ∈ Wsp k r z) : c • p ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  show inWb k r (c • p) ∧ herm (Hpk k r) (c • p) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul] at hp2 ⊢
  rw [hp2, smul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `wbPart`. Use `split_ifs with h`. Both sides reduce to the same expression. Use `symm`.

Conclude with `hv i (by omega)`.
-/
lemma wbPart_of_inWb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : wbPart k r v = v := by
  funext i
  unfold wbPart
  split_ifs with h
  · rfl
  · symm
    exact hv i (by omega)

/- English proof (translation)
Take `⟨h1, h2⟩` from `hq`. Unfold `prW`. Rewrite using `[wbPart_of_inWb h1, h2, zero_div, zero_smul, add_zero]`.
-/
lemma prW_of_mem {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) : prW k r z q = q := by
  obtain ⟨h1, h2⟩ := hq
  unfold prW
  rw [wbPart_of_inWb h1, h2, zero_div, zero_smul, add_zero]

/- English proof (translation)
Establish `h0 : wbPart k r v = 0`. Use function extensionality and compare the values at `i`. Unfold `wbPart`. Use `split_ifs with h`. Conclude with `hv i h.1 h.2`.

Both sides reduce to the same expression. Unfold `prW`. Rewrite using `[h0]`. Simplify using `[herm]`.
-/
lemma prW_of_mid {z v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) : prW k r z v = 0 := by
  have h0 : wbPart k r v = 0 := by
    funext i
    unfold wbPart
    split_ifs with h
    · exact hv i h.1 h.2
    · rfl
  unfold prW
  rw [h0]
  simp [herm]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_dotProduct, Matrix.star_mulVec, star_star, hH_ct, Matrix.dotProduct_mulVec]`.
-/
private lemma herm_star_lemma (v w : Fin (2 * r + k + 1) → ℂ) :
    star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, hH_ct, Matrix.dotProduct_mulVec]

/- English proof (translation)
Take `⟨hzw, hT⟩` from `hz`. Establish `hre : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ)`. Establish `h1` using `herm_star_lemma (k := k) (r := r) z z`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Tz]`.

Use `congrArg Complex.im h1` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Simplify using `only [Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT' : (Tz k r z : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`.

Unfold `prW`. Rewrite using `[wbPart_of_inWb hzw, hre, Complex.ofReal_neg, neg_div, div_self hT', neg_one_smul, add_neg_cancel]`.
-/
lemma prW_self {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : prW k r z z = 0 := by
  obtain ⟨hzw, hT⟩ := hz
  have hre : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
    have h1 := herm_star_lemma (k := k) (r := r) z z
    apply Complex.ext
    · simp [Tz]
    · have := congrArg Complex.im h1
      simp only [Complex.star_def, Complex.conj_im] at this
      simp only [Complex.ofReal_im]
      linarith
  have hT' : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold prW
  rw [wbPart_of_inWb hzw, hre, Complex.ofReal_neg, neg_div, div_self hT', neg_one_smul,
    add_neg_cancel]

/- English proof (translation)
Establish `h` using `herm_prW_l hq v`. Unfold `herm at h ⊢`. Rewrite using `[Matrix.mulVec_sub, dotProduct_sub, h, sub_self]`.
-/
lemma perp_l {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v - prW k r z v) q = 0 := by
  have h := herm_prW_l hq v
  unfold herm at h ⊢
  rw [Matrix.mulVec_sub, dotProduct_sub, h, sub_self]

/- English proof (translation)
Establish `h` using `herm_prW_r hq v`. Unfold `herm at h ⊢`. Rewrite using `[star_sub, sub_dotProduct, h, sub_self]`.
-/
lemma perp_r {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) q (v - prW k r z v) = 0 := by
  have h := herm_prW_r hq v
  unfold herm at h ⊢
  rw [star_sub, sub_dotProduct, h, sub_self]

/- English proof (translation)
Introduce `i hi1 _`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Use `a.isLt` as an intermediate fact.

Use `show bvec (eI k r a) i = 0`. Unfold `bvec`. Rewrite using `[Pi.single_apply, if_neg]`. Introduce `h`. Establish `h' : (i : ℕ) = a` using `by simpa [eI] using congrArg Fin.val h`.

Use linear arithmetic over natural numbers and integers. Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
lemma X_mid {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → x i = 0 := by
  intro i hi1 _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := a.isLt
    show bvec (eI k r a) i = 0
    unfold bvec
    rw [Pi.single_apply, if_neg]
    intro h
    have h' : (i : ℕ) = a := by simpa [eI] using congrArg Fin.val h
    omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Take `⟨hzw, -⟩` from `hz`. Establish `hqz : herm (Hpk k r) q z = 0`. Use `hq (Fin.last r)` as an intermediate fact. Simplify `this` using `[fvec]`. Establish `hX : ∀ a : Fin r, q (esI k r a) = 0`.

Introduce `a`. Establish `ha` using `a.isLt`. Establish `h` using `hq ⟨a.val, by omega⟩`. Establish `hf : fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a)`. Simplify using `[fvec, ha]`.

Rewrite `h` using `[hf]`. Establish `hc : herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a)`. Simplify using `only [herm, bvec, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single (eI k r a)]`. Rewrite using `[Finset.sum_eq_single (esI k r a)]`.

Simplify using `only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul] dsimp only [Hpk, eI, esI]`. Rewrite using `[if_pos ⟨ha, by omega⟩, one_mul]`. Introduce `j _ hj`. Establish `hj' : (j : ℕ) ≠ 2 * r + k - a` using `fun h => hj (Fin.ext h)`. Establish `hjl` using `j.isLt`.

Simplify using `only [Hpk, eI]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`.

Simplify using `[Pi.single_apply, hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `h` using `[hc]`. Conclude with `h`.

Establish `hwb : herm (Hpk k r) (wbPart k r q) z = 0`. Establish `h1 : herm (Hpk k r) (q - wbPart k r q) z = 0` using `herm_out_wb (fun i hi1 hi2 => by simp [wbPart, hi1, hi2]) hzw`. Establish `h2 : herm (Hpk k r) (q - wbPart k r q) z = herm (Hpk k r) q z - herm (Hpk k r) (wbPart k r q) z`. Simplify using `[herm, Matrix.mulVec_sub, dotProduct_sub]`. Rewrite `h1` using `[h2, hqz]`.

Take the linear combination `-h1`. Establish `hpr : prW k r z q = wbPart k r q`. Unfold `prW`. Rewrite using `[hwb, zero_div, zero_smul, add_zero]`. Rewrite using `[hpr]`.

Conclude with `sub_wbPart_X hX`.
-/
lemma sub_prW_X {z q : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z)
    (hq : ∀ a, herm (Hpk k r) q (fvec k r z a) = 0) : q - prW k r z q ∈ Xsp k r := by
  obtain ⟨hzw, -⟩ := hz
  have hqz : herm (Hpk k r) q z = 0 := by
    have := hq (Fin.last r)
    simpa [fvec] using this
  have hX : ∀ a : Fin r, q (esI k r a) = 0 := by
    intro a
    have ha := a.isLt
    have h := hq ⟨a.val, by omega⟩
    have hf : fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
      simp [fvec, ha]
    rw [hf] at h
    have hc : herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a) := by
      simp only [herm, bvec, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (eI k r a)]
      · rw [Finset.sum_eq_single (esI k r a)]
        · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
          dsimp only [Hpk, eI, esI]
          rw [if_pos ⟨ha, by omega⟩, one_mul]
        · intro j _ hj
          have hj' : (j : ℕ) ≠ 2 * r + k - a := fun h => hj (Fin.ext h)
          have hjl := j.isLt
          dsimp only [Hpk, eI]
          split_ifs <;> first | (exfalso; omega) | simp
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hc] at h
    exact h
  have hwb : herm (Hpk k r) (wbPart k r q) z = 0 := by
    have h1 : herm (Hpk k r) (q - wbPart k r q) z = 0 :=
      herm_out_wb (fun i hi1 hi2 => by simp [wbPart, hi1, hi2]) hzw
    have h2 : herm (Hpk k r) (q - wbPart k r q) z =
        herm (Hpk k r) q z - herm (Hpk k r) (wbPart k r q) z := by
      simp [herm, Matrix.mulVec_sub, dotProduct_sub]
    rw [h2, hqz] at h1
    linear_combination -h1
  have hpr : prW k r z q = wbPart k r q := by
    unfold prW
    rw [hwb, zero_div, zero_smul, add_zero]
  rw [hpr]
  exact sub_wbPart_X hX

/- English proof (translation)
Establish `h0 : herm (Hpk k r) 0 nu = 0` using `by simp [herm]`. Rewrite using `[Am_mulVec, hv]`. Simplify using `[h0]`.
-/
lemma Am_fix (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : prW k r z v = 0) : Am k r z z' nu M *ᵥ v = v := by
  have h0 : herm (Hpk k r) 0 nu = 0 := by simp [herm]
  rw [Am_mulVec, hv]
  simp [h0]

/- English proof (translation)
Establish `h1 : y * y⁻¹ = 1`. Use extensionality with `i j`. Use `congrFun (ginv_cancel hy (Pi.single j 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Matrix.one_apply, eq_comm]`. Establish `h2 : y⁻¹ * y = 1` using `by first`.

Consider the case `exact mul_eq_one_comm.mp h1`. Consider the case `exact Matrix.mul_eq_one_comm.1 h1`. Consider the case `exact Matrix.nonsing_inv_mul y (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, h1, Matrix.det_one]))`. Establish `h3 : yᴴ * Hpk k r = Hpk k r * y⁻¹`. Rewrite using `[inv_uh hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH_sq, Matrix.one_mul]`.

Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
private lemma herm_GV_lemma {y : B.Mat k r} (hy : y ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (y *ᵥ v) (y *ᵥ w) = herm (Hpk k r) v w := by
  have h1 : y * y⁻¹ = 1 := by
    ext i j
    have := congrFun (ginv_cancel hy (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
      using this
  have h2 : y⁻¹ * y = 1 := by
    first
      | exact mul_eq_one_comm.mp h1
      | exact Matrix.mul_eq_one_comm.1 h1
      | exact Matrix.nonsing_inv_mul y
          (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, h1, Matrix.det_one]))
  have h3 : yᴴ * Hpk k r = Hpk k r * y⁻¹ := by
    rw [inv_uh hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH_sq, Matrix.one_mul]
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3,
    Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Establish `hu'` using `(D0.isotropic_subspace_eq_primed u).1 hu`. Establish `hgl : gam k r z z' y u (Fin.last r) = 0`. Establish `hsum : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a = herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y)`. Simplify using `only [xcofL, wv, herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, star_star, smul_eq_mul]`. Establish `hun` using `herm_GV_lemma hy u (y⁻¹ *ᵥ xcofL k r z z' y)`.

Rewrite `hun` using `[ginv_cancel hy]`. Establish `hpr` using `herm_prW_r hu'.1 (y⁻¹ *ᵥ xcofL k r z z' y)`. Establish `hom : herm (Hpk k r) u (omW' k r z z' y) = 0`. Establish `h0` using `hu'.2`. Rewrite using `[hom']`.

Unfold `herm at h0 ⊢`. Rewrite using `[star_smul, smul_dotProduct, h0, smul_zero]`. Establish `hmv : ((Zhat k r z z' y).adjugate *ᵥ wv k r z y u) (Fin.last r) = 0`. Express the relevant statement in the definitionally equal form `∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a = 0`. Rewrite using `[hsum, hun, ← hpr]`.

Conclude with `hom`. Simplify using `[gam, hmv]`. Rewrite using `[Lm_mulVec, add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c = Fin.last r`.

Substitute `hc` using the available equality. Rewrite using `[hgl, zero_smul]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (fv_X z' c hc)`.
-/
lemma lift_X {z z' : Fin (2 * r + k + 1) → ℂ} (D0 : GfBaseD k r z z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) {t : ℝ} (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u : Fin (2 * r + k + 1) → ℂ}
    (hu : u ∈ D0.U0) : Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have hu' := (D0.isotropic_subspace_eq_primed u).1 hu
  have hgl : gam k r z z' y u (Fin.last r) = 0 := by
    have hsum : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      simp only [xcofL, wv, herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, star_star,
        smul_eq_mul]
    have hun := herm_GV_lemma hy u (y⁻¹ *ᵥ xcofL k r z z' y)
    rw [ginv_cancel hy] at hun
    have hpr := herm_prW_r hu'.1 (y⁻¹ *ᵥ xcofL k r z z' y)
    have hom : herm (Hpk k r) u (omW' k r z z' y) = 0 := by
      have h0 := hu'.2
      rw [hom']
      unfold herm at h0 ⊢
      rw [star_smul, smul_dotProduct, h0, smul_zero]
    have hmv : ((Zhat k r z z' y).adjugate *ᵥ wv k r z y u) (Fin.last r) = 0 := by
      change ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a = 0
      rw [hsum, hun, ← hpr]
      exact hom
    simp [gam, hmv]
  rw [Lm_mulVec, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · subst hc
    rw [hgl, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

/- English proof (translation)
Establish `hadd : ∀ v w f : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) (v + w) f = herm (Hpk k r) v f + herm (Hpk k r) w f`. Introduce `v w f`. Simplify using `[herm, Matrix.mulVec_add, dotProduct_add]`. Establish `hsmul : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f`. Introduce `c v f`.

Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`. Establish `hsum : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f`. Introduce `g f`. Simplify using `[herm, Matrix.mulVec_sum, dotProduct_sum]`. Rewrite using `[Lm_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, hadd, hsum]`.

Simplify using `only [Matrix.mulVec_smul, hsmul]`. Express the relevant statement in the definitionally equal form `wv k r z y u a + ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = 0`. Establish `hZg : Zhat k r z z' y *ᵥ gam k r z z' y u = -wv k r z y u`. Unfold `gam`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, neg_mul, inv_mul_cancel₀ hd, neg_smul, one_smul]`.

Rewrite using `[show ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = (Zhat k r z z' y *ᵥ gam k r z z' y u) a by`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm], hZg]`. Simplify using the standard rewrite rules.
-/
lemma lift_orth {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hd : (Zhat k r z z' y).det ≠ 0)
    (u : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    herm (Hpk k r) (y *ᵥ (Lm k r z z' y *ᵥ u)) (fvec k r z a) = 0 := by
  have hadd : ∀ v w f : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (v + w) f = herm (Hpk k r) v f + herm (Hpk k r) w f := by
    intro v w f
    simp [herm, Matrix.mulVec_add, dotProduct_add]
  have hsmul : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hsum : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f := by
    intro g f
    simp [herm, Matrix.mulVec_sum, dotProduct_sum]
  rw [Lm_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, hadd, hsum]
  simp only [Matrix.mulVec_smul, hsmul]
  change wv k r z y u a + ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = 0
  have hZg : Zhat k r z z' y *ᵥ gam k r z z' y u = -wv k r z y u := by
    unfold gam
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, neg_mul, inv_mul_cancel₀ hd, neg_smul, one_smul]
  rw [show ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = (Zhat k r z z' y *ᵥ gam k r z z' y u) a by
    simp [Matrix.mulVec, dotProduct, mul_comm], hZg]
  simp

/- English proof (translation)
Establish `hX : ∀ v ∈ D0.U0, (y *ᵥ (Lm k r z z' y *ᵥ v)) - Phi k r z z' y *ᵥ v ∈ Xsp k r`. Introduce `v _`. Rewrite using `[Phi_mulVec]`. Conclude with `sub_prW_X hz (fun a => lift_orth hd v a)`. Establish `hinW : ∀ v, inWb k r (Phi k r z z' y *ᵥ v)`.

Introduce `v`. Rewrite using `[Phi_mulVec]`. Conclude with `(prW_mem hz _).1`. Establish `hL : ∀ v ∈ D0.U0, Lm k r z z' y *ᵥ v - v ∈ Xsp k r` using `fun v hv => lift_X D0 hy hom' hv`. Establish `hUw : ∀ v ∈ D0.U0, inWb k r v` using `fun v hv => ((D0.isotropic_subspace_eq v).1 hv).1.1`.

Establish `e1` using `herm_add_X (hinW u) (hinW u') (hX u hu) (hX u' hu')`. Establish `e2` using `herm_add_X (hUw u hu) (hUw u' hu') (hL u hu) (hL u' hu')`. Rewrite `e1`, `e2` using `[add_sub_cancel, add_sub_cancel]`. Rewrite using `[← e1, herm_GV_lemma hy, e2]`.
-/
lemma phi_iso {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (D0 : GfBaseD k r z z')
    {y : B.Mat k r} (hy : y ∈ B.GV k r) (hd : (Zhat k r z z' y).det ≠ 0) {t : ℝ}
    (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u u' : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ D0.U0)
    (hu' : u' ∈ D0.U0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u') = herm (Hpk k r) u u' := by
  have hX : ∀ v ∈ D0.U0, (y *ᵥ (Lm k r z z' y *ᵥ v)) - Phi k r z z' y *ᵥ v ∈ Xsp k r := by
    intro v _
    rw [Phi_mulVec]
    exact sub_prW_X hz (fun a => lift_orth hd v a)
  have hinW : ∀ v, inWb k r (Phi k r z z' y *ᵥ v) := by
    intro v
    rw [Phi_mulVec]
    exact (prW_mem hz _).1
  have hL : ∀ v ∈ D0.U0, Lm k r z z' y *ᵥ v - v ∈ Xsp k r := fun v hv => lift_X D0 hy hom' hv
  have hUw : ∀ v ∈ D0.U0, inWb k r v := fun v hv => ((D0.isotropic_subspace_eq v).1 hv).1.1
  have e1 := herm_add_X (hinW u) (hinW u') (hX u hu) (hX u' hu')
  have e2 := herm_add_X (hUw u hu) (hUw u' hu') (hL u hu) (hL u' hu')
  rw [add_sub_cancel, add_sub_cancel] at e1 e2
  rw [← e1, herm_GV_lemma hy, e2]

/- English proof (translation)
Establish `ha` using `a.isLt`. Simplify using `only [herm, bvec, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single (eI k r a)]`. Rewrite using `[Finset.sum_eq_single (esI k r a)]`. Simplify using `only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul] dsimp only [Hpk, eI, esI]`.

Rewrite using `[if_pos ⟨ha, by omega⟩, one_mul]`. Introduce `j _ hj`. Establish `hj' : (j : ℕ) ≠ 2 * r + k - a` using `fun h => hj (Fin.ext h)`. Establish `hjl` using `j.isLt`. Simplify using `only [Hpk, eI]`.

Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`. Simplify using `[Pi.single_apply, hi]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma herm_bvec_lemma (q : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a) := by
  have ha := a.isLt
  simp only [herm, bvec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (eI k r a)]
  · rw [Finset.sum_eq_single (esI k r a)]
    · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
      dsimp only [Hpk, eI, esI]
      rw [if_pos ⟨ha, by omega⟩, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 2 * r + k - a := fun h => hj (Fin.ext h)
      have hjl := j.isLt
      dsimp only [Hpk, eI]
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hsum1 : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f`. Introduce `g f`. Simplify using `[herm, Matrix.mulVec_sum, dotProduct_sum]`. Establish `hsmul1 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f`. Introduce `c v f`.

Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`. Establish `hsum2 : ∀ (v : Fin (2 * r + k + 1) → ℂ) (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) v (∑ c, g c) = ∑ c, herm (Hpk k r) v (g c)`. Introduce `v g`. Simplify using `[herm, star_sum, sum_dotProduct]`. Establish `hsmul2 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) v (c • f) = star c * herm (Hpk k r) v f`.

Introduce `c v f`. Simplify using `[herm, star_smul, smul_dotProduct]`. Use `set w := y *ᵥ (Lm k r z z' y *ᵥ u) with hw`. Establish `hu'` using `(D0.isotropic_subspace_eq_primed u).1 hu`. Establish `hLf : ∀ b, herm (Hpk k r) (Lm k r z z' y *ᵥ u) (fvec k r z' b) = 0`.

Introduce `b`. Establish `hx0` using `lift_X D0 hy hom' hu`. Establish `hsplit : Lm k r z z' y *ᵥ u = u + (Lm k r z z' y *ᵥ u - u)` using `by abel`. Rewrite using `[hsplit]`. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Establish `hf : fvec k r z' (Fin.last r) = z' + 0` using `by simp [fvec]`. Rewrite using `[hf, herm_add_X hu'.1.1 hz'.1 hx0 (Submodule.zero_mem _)]`. Conclude with `hu'.1.2`. Establish `hf : fvec k r z' b = 0 + fvec k r z' b` using `by simp`.

Rewrite using `[hf, herm_add_X (q := (0 : Fin (2 * r + k + 1) → ℂ)) hu'.1.1 (fun i _ => rfl) hx0 (fv_X z' b hb)]`. Simplify using `[herm]`. Establish `hwx : herm (Hpk k r) w (xcof k r z z' y) = 0`. Establish `hb : ∀ b, herm (Hpk k r) w (y *ᵥ fvec k r z' b) = 0` using `fun b => by`. Rewrite using `[hw, herm_GV_lemma hy]`.

Conclude with `hLf b`. Unfold `xcof`. Rewrite using `[hsum2]`. Simplify using `only [hsmul2, hb, mul_zero, Finset.sum_const_zero]`. Establish `hxl : ∀ a : Fin r, xcof k r z z' y (esI k r a) = 0`.

Introduce `a`. Establish `ha` using `a.isLt`. Use `set a' : Fin (r + 1) := ⟨a.val, by omega⟩ with ha'`. Establish `hne : a' ≠ Fin.last r` using `fun h => by`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[a'] at this`. Use linear arithmetic over natural numbers and integers. Establish `hf : bvec (eI k r a) = fvec k r z a'` using `by simp [fvec, a', ha]`. Rewrite using `[← herm_bvec_lemma (xcof k r z z' y) a, hf]`. Establish `hZ : herm (Hpk k r) (xcof k r z z' y) (fvec k r z a') = ((Zhat k r z z' y) * (Zhat k r z z' y).adjugate) a' (Fin.last r)`.

Unfold `xcof`. Rewrite using `[hsum1, Matrix.mul_apply]`. Simplify using `only [hsmul1]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Rewrite using `[hZ, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero]`.

Establish `hxw : w - prW k r z w ∈ Xsp k r` using `sub_prW_X hz (fun a => lift_orth hd u a)`. Establish `hxc : xcof k r z z' y - wbPart k r (xcof k r z z' y) ∈ Xsp k r` using `sub_wbPart_X hxl`. Establish `hwbI : inWb k r (wbPart k r (xcof k r z z' y))` using `fun i hi => by`. Unfold `wbPart`. Rewrite using `[if_neg (by omega)]`.

Establish `hpm` using `prW_mem hz w`. Establish `e1 : herm (Hpk k r) w (xcof k r z z' y) = herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y))`. Use `herm_add_X hpm.1 hwbI hxw hxc` as an intermediate fact. Rewrite `this` using `[add_sub_cancel, add_sub_cancel]`. Then use the resulting hypothesis. Establish `e2 : herm (Hpk k r) (prW k r z w) (xcof k r z z' y) = herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y))`.

Use `herm_add_X hpm.1 hwbI (Submodule.zero_mem _) hxc` as an intermediate fact. Rewrite `this` using `[add_zero, add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[Phi_mulVec, ← hw]`. Unfold `omW`. Rewrite using `[herm_prW_r hpm, e2, ← e1, hwx]`.
-/
lemma phi_perp {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (D0 : GfBaseD k r z z') {y : B.Mat k r} (hy : y ∈ B.GV k r) (hd : (Zhat k r z z' y).det ≠ 0) {t : ℝ}
    (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ D0.U0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (omW k r z z' y) = 0 := by
  have hsum1 : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f := by
    intro g f
    simp [herm, Matrix.mulVec_sum, dotProduct_sum]
  have hsmul1 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hsum2 : ∀ (v : Fin (2 * r + k + 1) → ℂ) (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (∑ c, g c) = ∑ c, herm (Hpk k r) v (g c) := by
    intro v g
    simp [herm, star_sum, sum_dotProduct]
  have hsmul2 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (c • f) = star c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, star_smul, smul_dotProduct]
  set w := y *ᵥ (Lm k r z z' y *ᵥ u) with hw
  have hu' := (D0.isotropic_subspace_eq_primed u).1 hu
  have hLf : ∀ b, herm (Hpk k r) (Lm k r z z' y *ᵥ u) (fvec k r z' b) = 0 := by
    intro b
    have hx0 := lift_X D0 hy hom' hu
    have hsplit : Lm k r z z' y *ᵥ u = u + (Lm k r z z' y *ᵥ u - u) := by abel
    rw [hsplit]
    by_cases hb : b = Fin.last r
    · subst hb
      have hf : fvec k r z' (Fin.last r) = z' + 0 := by simp [fvec]
      rw [hf, herm_add_X hu'.1.1 hz'.1 hx0 (Submodule.zero_mem _)]
      exact hu'.1.2
    · have hf : fvec k r z' b = 0 + fvec k r z' b := by simp
      rw [hf, herm_add_X (q := (0 : Fin (2 * r + k + 1) → ℂ)) hu'.1.1 (fun i _ => rfl) hx0 (fv_X z' b hb)]
      simp [herm]
  have hwx : herm (Hpk k r) w (xcof k r z z' y) = 0 := by
    have hb : ∀ b, herm (Hpk k r) w (y *ᵥ fvec k r z' b) = 0 := fun b => by
      rw [hw, herm_GV_lemma hy]
      exact hLf b
    unfold xcof
    rw [hsum2]
    simp only [hsmul2, hb, mul_zero, Finset.sum_const_zero]
  have hxl : ∀ a : Fin r, xcof k r z z' y (esI k r a) = 0 := by
    intro a
    have ha := a.isLt
    set a' : Fin (r + 1) := ⟨a.val, by omega⟩ with ha'
    have hne : a' ≠ Fin.last r := fun h => by
      have := congrArg Fin.val h
      simp [a'] at this
      omega
    have hf : bvec (eI k r a) = fvec k r z a' := by simp [fvec, a', ha]
    rw [← herm_bvec_lemma (xcof k r z z' y) a, hf]
    have hZ : herm (Hpk k r) (xcof k r z z' y) (fvec k r z a') =
        ((Zhat k r z z' y) * (Zhat k r z z' y).adjugate) a' (Fin.last r) := by
      unfold xcof
      rw [hsum1, Matrix.mul_apply]
      simp only [hsmul1]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [hZ, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero]
  have hxw : w - prW k r z w ∈ Xsp k r := sub_prW_X hz (fun a => lift_orth hd u a)
  have hxc : xcof k r z z' y - wbPart k r (xcof k r z z' y) ∈ Xsp k r := sub_wbPart_X hxl
  have hwbI : inWb k r (wbPart k r (xcof k r z z' y)) := fun i hi => by
    unfold wbPart
    rw [if_neg (by omega)]
  have hpm := prW_mem hz w
  have e1 : herm (Hpk k r) w (xcof k r z z' y) =
      herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y)) := by
    have := herm_add_X hpm.1 hwbI hxw hxc
    rwa [add_sub_cancel, add_sub_cancel] at this
  have e2 : herm (Hpk k r) (prW k r z w) (xcof k r z z' y) =
      herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y)) := by
    have := herm_add_X hpm.1 hwbI (Submodule.zero_mem _) hxc
    rwa [add_zero, add_sub_cancel] at this
  rw [Phi_mulVec, ← hw]
  unfold omW
  rw [herm_prW_r hpm, e2, ← e1, hwx]

end loca2

end PI.UnitaryGroupMassFormula.GsFr
