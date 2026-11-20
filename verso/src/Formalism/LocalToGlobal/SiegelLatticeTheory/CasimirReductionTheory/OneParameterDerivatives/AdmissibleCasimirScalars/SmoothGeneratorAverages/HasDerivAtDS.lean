import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AdmissibleVectors

section Lie

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Unfold `inG`. Simplify using the standard rewrite rules.
-/
theorem inG_zero : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inG; simp

/- English proof (translation)
Unfold `inG at *`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Use `_ = 0 := by rw [hX, hY, add_zero]`.
-/
theorem inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  unfold inG at *
  calc (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by
        rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
    _ = 0 := by rw [hX, hY, add_zero]

/- English proof (translation)
Unfold `inG at *`. Rewrite using `[conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]`.
-/
theorem inG_rsmul (r : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε ((r : ℂ) • X) := by
  unfold inG at *
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
    smul_zero]

/- English proof (translation)
Unfold `inG Jm`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Introduce `h`. Use extensionality with `i j`. Simplify `h i j` using `[Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem inG_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    ext i j
    simpa [Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

/- English proof (translation)
Rewrite using `[inG_iff]`. Introduce `i j`. Take `⟨a, b⟩` from `p`. Simplify using `only [gen, sg]`. Distinguish the cases in `h1 : a = b`.

Substitute `h1` using the available equality. Simplify using `only [if_true, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Apply the tactic sequence `by_cases hi : a = i <;> by_cases hj : a = j`. Apply the tactic sequence `subst hi; subst hj; cases ε a <;> simp`. Substitute `hi` using the available equality.

Simplify using `[hj]`. Substitute `hj` using the available equality. Simplify using `[hi]`. Simplify using `[hi, hj]`. Rewrite using `[if_neg h1]`.

Establish `hne : b ≠ a` using `fun h => h1 h.symm`. Distinguish the cases in `h2 : a < b`. Rewrite using `[if_pos h2]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Apply the tactic sequence `by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>`.

Apply the tactic sequence `simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>`. Apply the tactic sequence `subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all`. Rewrite using `[if_neg h2]`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Apply the tactic sequence `by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>`.

Apply the tactic sequence `simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>`. Apply the tactic sequence `subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all`.
-/
theorem inG_gen (p : Fin n × Fin n) : inG ε (gen ε p) := by
  rw [inG_iff]
  intro i j
  obtain ⟨a, b⟩ := p
  simp only [gen, sg]
  by_cases h1 : a = b
  · subst h1
    simp only [if_true, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hi : a = i <;> by_cases hj : a = j
    · subst hi; subst hj; cases ε a <;> simp
    · subst hi; simp [hj]
    · subst hj; simp [hi]
    · simp [hi, hj]
  · rw [if_neg h1]
    have hne : b ≠ a := fun h => h1 h.symm
    by_cases h2 : a < b
    · rw [if_pos h2]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>
        simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>
        subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all
    · rw [if_neg h2]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>
        simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>
        subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (inG ε) (fun _ _ h1 h2 => inG_add h1 h2) inG_zero (fun p _ => inG_rsmul (z p) (inG_gen p))`.
-/
theorem inG_comb (z : Fin n × Fin n → ℝ) : inG ε (∑ p, ((z p : ℝ) : ℂ) • gen ε p) :=
  Finset.sum_induction _ (inG ε) (fun _ _ h1 h2 => inG_add h1 h2) inG_zero
    (fun p _ => inG_rsmul (z p) (inG_gen p))

end Lie

section Vec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold `Formalism.MainNotions.BridgeCPX.vec`. Rewrite using `[← integral_smul]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `[smul_smul]`.
-/
theorem vec_smul' (w : H) (c : ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.MainNotions.BridgeCPX.vec ε σ w (c • Φ) = c • Formalism.MainNotions.BridgeCPX.vec ε σ w Φ := by
  unfold Formalism.MainNotions.BridgeCPX.vec
  rw [← integral_smul]
  congr 1
  funext y
  simp [smul_smul]

/- English proof (translation)
Unfold `Formalism.MainNotions.BridgeCPX.vec`. Rewrite using `[← integral_finsetSum s (fun i _ => vec_integrable hσ w (hΦ i))]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_apply, Finset.sum_smul]`.
-/
theorem vec_sum' (hσ : IsURepOn (UJset ε) σ) (w : H) {ι : Type} (s : Finset ι)
    (Φ : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : ∀ i, IsTest (Φ i)) :
    Formalism.MainNotions.BridgeCPX.vec ε σ w (∑ i ∈ s, Φ i) = ∑ i ∈ s, Formalism.MainNotions.BridgeCPX.vec ε σ w (Φ i) := by
  unfold Formalism.MainNotions.BridgeCPX.vec
  rw [← integral_finsetSum s (fun i _ => vec_integrable hσ w (hΦ i))]
  congr 1
  funext y
  simp [Finset.sum_apply, Finset.sum_smul]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [der, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Establish `e : -(∑ p, ((z p : ℝ) : ℂ) • G p) * m = ∑ p, (z p) • (-(G p) * m)`. Rewrite using `[Matrix.neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mul, Matrix.neg_mul, smul_neg, RCLike.real_smul_eq_coe_smul (K := ℂ)]`. Both sides reduce to the same expression. Rewrite using `[e, map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Complex.real_smul]`.
-/
theorem der_comb (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (z : Fin n × Fin n → ℝ)
    (G : Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ) :
    der (-(∑ p, ((z p : ℝ) : ℂ) • G p)) Φ = ∑ p, ((z p : ℝ) : ℂ) • der (-(G p)) Φ := by
  funext m
  simp only [der, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e : -(∑ p, ((z p : ℝ) : ℂ) • G p) * m = ∑ p, (z p) • (-(G p) * m) := by
    rw [Matrix.neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.smul_mul, Matrix.neg_mul, smul_neg, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Complex.real_smul]

/- English proof (translation)
Take `⟨x', -, hx'⟩` from `Vsub_deriv hσ w hv hX`. Unfold `dS`. Rewrite using `[hx'.deriv]`. Conclude with `hx'`.
-/
theorem hasDerivAt_dS (hσ : IsURepOn (UJset ε) σ) (w : H) {v : H} (hv : v ∈ Vsub ε hσ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dS σ X v) 0 := by
  obtain ⟨x', -, hx'⟩ := Vsub_deriv hσ w hv hX
  unfold dS
  rw [hx'.deriv]
  exact hx'

/- English proof (translation)
Take `⟨x', hm, hx'⟩` from `Vsub_deriv hσ w hv hX`. Unfold `dS`. Rewrite using `[hx'.deriv]`. Conclude with `hm`.
-/
theorem dS_mem (hσ : IsURepOn (UJset ε) σ) (w : H) {v : H} (hv : v ∈ Vsub ε hσ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : dS σ X v ∈ Vsub ε hσ w := by
  obtain ⟨x', hm, hx'⟩ := Vsub_deriv hσ w hv hX
  unfold dS
  rw [hx'.deriv]
  exact hm

/- English proof (translation)
Establish `h` using `hasDerivAt_vec hσ w hΦ (inG_neg hX)`. Establish `h' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ)) (Formalism.MainNotions.BridgeCPX.vec ε σ w (der (-X) Φ)) 0`. Use `h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ) = Formalism.MainNotions.BridgeCPX.vec ε σ w (ltr (NormedSpace.exp ((t : ℂ) • (-X))) Φ)`. Rewrite using `[← umat_expG (inG_neg hX) t, ← rep_vec hσ w hΦ, expG_neg_inv hX, umat_expG hX]`.

Unfold `dS`. Conclude with `h'.deriv`.
-/
theorem dS_vec (hσ : IsURepOn (UJset ε) σ) (w : H) {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    dS σ X (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ) = Formalism.MainNotions.BridgeCPX.vec ε σ w (der (-X) Φ) := by
  have h := hasDerivAt_vec hσ w hΦ (inG_neg hX)
  have h' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ)) (Formalism.MainNotions.BridgeCPX.vec ε σ w (der (-X) Φ)) 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ) = Formalism.MainNotions.BridgeCPX.vec ε σ w (ltr (NormedSpace.exp ((t : ℂ) • (-X))) Φ)
    rw [← umat_expG (inG_neg hX) t, ← rep_vec hσ w hΦ, expG_neg_inv hX, umat_expG hX]
  unfold dS
  exact h'.deriv

/- English proof (translation)
Take `⟨Φ, hΦ, rfl⟩` from `hv`. Rewrite using `[dS_vec hσ w hΦ (inG_comb z), der_comb, vec_sum' hσ w _ _ (fun p => test_smul _ (test_der hΦ _))]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[vec_smul', dS_vec hσ w hΦ (inG_gen p)]`.
-/
theorem dS_lin (hσ : IsURepOn (UJset ε) σ) (w : H) (z : Fin n × Fin n → ℝ) {v : H} (hv : v ∈ Vsub ε hσ w) :
    dS σ (∑ p, ((z p : ℝ) : ℂ) • gen ε p) v = ∑ p, ((z p : ℝ) : ℂ) • dS σ (gen ε p) v := by
  obtain ⟨Φ, hΦ, rfl⟩ := hv
  rw [dS_vec hσ w hΦ (inG_comb z), der_comb, vec_sum' hσ w _ _ (fun p => test_smul _ (test_der hΦ _))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vec_smul', dS_vec hσ w hΦ (inG_gen p)]

/- English proof (translation)
Establish `h` using `(hasDerivAt_dS hσ w hu hX).inner ℂ (hasDerivAt_dS hσ w hv hX)`. Establish `hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u, σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ`. Use function extensionality and compare the values at `t`. Rewrite using `[← umat_expG hX t, rep_inner hσ]`. Rewrite `h` using `[hc]`.

Establish `h0` using `h.unique (hasDerivAt_const (0 : ℝ) ⟪u, v⟫_ℂ)`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1] at h0`. Conclude with `eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h0)`.
-/
theorem dS_skew (hσ : IsURepOn (UJset ε) σ) (w : H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {u v : H} (hu : u ∈ Vsub ε hσ w) (hv : v ∈ Vsub ε hσ w) :
    ⟪dS σ X u, v⟫_ℂ = - ⟪u, dS σ X v⟫_ℂ := by
  have h := (hasDerivAt_dS hσ w hu hX).inner ℂ (hasDerivAt_dS hσ w hv hX)
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u, σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) =
      fun _ => ⟪u, v⟫_ℂ := by
    funext t
    rw [← umat_expG hX t, rep_inner hσ]
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) ⟪u, v⟫_ℂ)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1] at h0
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h0)

/- English proof (translation)
Establish `hd` using `hasDerivAt_dS hσ w hv hX`. Establish `h2 : HasDerivAt (fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ (umat g) (dS σ X v)) 0` using `((σ (umat g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd`. Establish `he : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹))) (σ (umat g) v)) = fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v)`. Use function extensionality and compare the values at `t`. Establish `hinv : umat g⁻¹ = (umat g)⁻¹` using `Matrix.coe_units_inv _`.

Establish `h1 : NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹)) = umat (g * expG ε X t * g⁻¹)`. Rewrite using `[show umat (g * expG ε X t * g⁻¹) = umat g * umat (expG ε X t) * umat g⁻¹ from rfl, umat_expG hX, hinv, ← Matrix.exp_conj _ _ (Units.isUnit _), Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[h1, rep_mul hσ, rep_inv_apply hσ, rep_mul hσ, umat_expG hX]`. Unfold `dS`. Rewrite using `[he]`.

Conclude with `h2.deriv.symm`.
-/
theorem dS_conj (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {v : H} (hv : v ∈ Vsub ε hσ w) :
    σ (umat g) (dS σ X v) = dS σ (umat g * X * umat g⁻¹) (σ (umat g) v) := by
  have hd := hasDerivAt_dS hσ w hv hX
  have h2 : HasDerivAt (fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ (umat g) (dS σ X v)) 0 :=
    ((σ (umat g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  have he : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹))) (σ (umat g) v)) =
      fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    have hinv : umat g⁻¹ = (umat g)⁻¹ := Matrix.coe_units_inv _
    have h1 : NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹)) = umat (g * expG ε X t * g⁻¹) := by
      rw [show umat (g * expG ε X t * g⁻¹) = umat g * umat (expG ε X t) * umat g⁻¹ from rfl, umat_expG hX, hinv,
        ← Matrix.exp_conj _ _ (Units.isUnit _), Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, rep_mul hσ, rep_inv_apply hσ, rep_mul hσ, umat_expG hX]
  unfold dS
  rw [he]
  exact h2.deriv.symm

/- English proof (translation)
Establish `hd` using `hasDerivAt_dS hσ w hv hX`. Establish `hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v) (σ (NormedSpace.exp ((t : ℂ) • X)) (dS σ X v)) t`. Introduce `t`. Establish `h1` using `((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t - t) (by rw [sub_self]; exact hd)`. Establish `h2` using `HasDerivAt.comp_sub_const t t h1`.

Use `h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show σ (NormedSpace.exp ((s : ℂ) • X)) v = σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) v)`. Rewrite using `[← umat_expG hX t, ← umat_expG hX (s - t), ← rep_mul hσ, show umat (expG ε X t * expG ε X (s - t)) = umat (expG ε X t) * umat (expG ε X (s - t)) from rfl, umat_expG hX, umat_expG hX, ← one_parameter_subgroup_holds n X t (s - t), add_sub_cancel]`. Establish `key` using `norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v) (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hσ.2.1 _ ((umat_expG hX t) ▸ umat_mem _) _))`. Simplify `key` using `[hσ.1.1]`.
-/
theorem dS_mv (hσ : IsURepOn (UJset ε) σ) (w : H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {v : H} (hv : v ∈ Vsub ε hσ w) : ‖σ (NormedSpace.exp X) v - v‖ ≤ ‖dS σ X v‖ := by
  have hd := hasDerivAt_dS hσ w hv hX
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v)
      (σ (NormedSpace.exp ((t : ℂ) • X)) (dS σ X v)) t := by
    intro t
    have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t - t) (by rw [sub_self]; exact hd)
    have h2 := HasDerivAt.comp_sub_const t t h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp ((s : ℂ) • X)) v =
      σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) v)
    rw [← umat_expG hX t, ← umat_expG hX (s - t), ← rep_mul hσ,
      show umat (expG ε X t * expG ε X (s - t)) = umat (expG ε X t) * umat (expG ε X (s - t)) from rfl,
      umat_expG hX, umat_expG hX, ← one_parameter_subgroup_holds n X t (s - t), add_sub_cancel]
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v)
    (fun t _ => (hder t).hasDerivWithinAt)
    (fun t _ => le_of_eq (hσ.2.1 _ ((umat_expG hX t) ▸ umat_mem _) _))
  simpa [hσ.1.1] using key

end Vec

end AdmissibleVectors

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ w`. Conclude with `{ der := fun X hX v hv => AdmissibleVectors.hasDerivAt_dS hσ w hv hX mem := fun X hX v hv => AdmissibleVectors.dS_mem hσ w hv hX lin := fun z v hv => AdmissibleVectors.dS_lin hσ w z hv skew := fun X hX u hu v hv => AdmissibleVectors.dS_skew hσ w hX hu hv conj := fun g X hX v hv = …`.
-/
theorem c1 : CalculusOnSmoothVectors := by
  intro n ε H _ _ _ σ hσ w
  exact
    { der := fun X hX v hv => AdmissibleVectors.hasDerivAt_dS hσ w hv hX
      mem := fun X hX v hv => AdmissibleVectors.dS_mem hσ w hv hX
      lin := fun z v hv => AdmissibleVectors.dS_lin hσ w z hv
      skew := fun X hX u hu v hv => AdmissibleVectors.dS_skew hσ w hX hu hv
      conj := fun g X hX v hv => AdmissibleVectors.dS_conj hσ w g hX hv
      mv := fun X hX v hv => AdmissibleVectors.dS_mv hσ w hX hv }

end Formalism.L2.SG.Pf.admitted
