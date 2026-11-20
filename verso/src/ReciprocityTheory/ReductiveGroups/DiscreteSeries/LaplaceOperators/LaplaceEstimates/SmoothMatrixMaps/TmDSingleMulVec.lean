import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmAContDiffMulLeft

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section Good

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

def TmGood (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (a : ℝ)
    (m : H) : Prop :=
  Formalism.REAL.SmoothOnG ε (coefX σ x₀ w m) ∧
    ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g‖ ≤ C * frob g ^ (-a)

/- English proof (translation)
Establish `e : coefX σ x₀ w (m + c • m') = fun g => coefX σ x₀ w m g + c * coefX σ x₀ w m' g`. Use function extensionality and compare the values at `g`. Simplify using `[coefX, inner_add_right, inner_smul_right]`. Use `⟨?_, fun wd => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `Formalism.REAL.smooth_on_group_add hm.1 (Formalism.REAL.smooth_on_group_const_mul c hm'.1)`. Take `⟨C₁, h₁⟩` from `hm.2 wd`. Take `⟨C₂, h₂⟩` from `hm'.2 wd`. Use `⟨C₁ + ‖c‖ * C₂, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[e, tmA_eword_lin hm.1 hm'.1 c wd g hg]`.

Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `_ ≤ C₁ * frob g ^ (-a) + ‖c‖ * (C₂ * frob g ^ (-a)) := add_le_add (h₁ g hg) (mul_le_mul_of_nonneg_left (h₂ g hg) (norm_nonneg c))`. Use `_ = (C₁ + ‖c‖ * C₂) * frob g ^ (-a) := by ring`.
-/
theorem tmC_good_add {x₀ : Mat k r} {w : H} {a : ℝ} {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (c : ℂ) : TmGood ε σ x₀ w a (m + c • m') := by
  have e : coefX σ x₀ w (m + c • m') = fun g => coefX σ x₀ w m g + c * coefX σ x₀ w m' g := by
    funext g; simp [coefX, inner_add_right, inner_smul_right]
  refine ⟨?_, fun wd => ?_⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_add hm.1 (Formalism.REAL.smooth_on_group_const_mul c hm'.1)
  · obtain ⟨C₁, h₁⟩ := hm.2 wd
    obtain ⟨C₂, h₂⟩ := hm'.2 wd
    refine ⟨C₁ + ‖c‖ * C₂, fun g hg => ?_⟩
    rw [e, tmA_eword_lin hm.1 hm'.1 c wd g hg]
    calc ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g + c * Formalism.REAL.Eword ε wd (coefX σ x₀ w m') g‖
        ≤ ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g‖ + ‖c‖ * ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m') g‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ C₁ * frob g ^ (-a) + ‖c‖ * (C₂ * frob g ^ (-a)) :=
          add_le_add (h₁ g hg) (mul_le_mul_of_nonneg_left (h₂ g hg) (norm_nonneg c))
      _ = (C₁ + ‖c‖ * C₂) * frob g ^ (-a) := by ring

/- English proof (translation)
Establish `e : coefX σ x₀ w 0 = fun _ => (0 : ℂ)` using `by funext g; simp [coefX]`. Use `⟨?_, fun wd => ⟨0, fun g hg => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Formalism.REAL.smooth_on_group_const_fun 0`. Rewrite using `[e, tmA_eword_zero wd g hg]`.

Simplify using the standard rewrite rules.
-/
theorem tmC_good_zero (x₀ : Mat k r) (w : H) (a : ℝ) : TmGood ε σ x₀ w a 0 := by
  have e : coefX σ x₀ w 0 = fun _ => (0 : ℂ) := by funext g; simp [coefX]
  refine ⟨?_, fun wd => ⟨0, fun g hg => ?_⟩⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_const_fun 0
  · rw [e, tmA_eword_zero wd g hg]; simp

def tmGoodSub (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H) (x₀ : Mat k r)
    (w : H) (a : ℝ) : Submodule ℂ D where
  carrier := {m | TmGood ε σ x₀ w a ((m : D) : H)}
  zero_mem' := by simpa using tmC_good_zero (ε := ε) (σ := σ) x₀ w a
  add_mem' := fun {m m'} hm hm' => by
    have := tmC_good_add hm hm' 1
    simpa using this
  smul_mem' := fun c m hm => by
    have := tmC_good_add (tmC_good_zero x₀ w a) hm c
    simpa using this

/- English proof (translation)
Establish `e : ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a' b' (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a' b' m : D) : H) g` using `fun g hg => tmB_eab_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) w m a' b'`. Use `⟨Formalism.REAL.smooth_on_group_congr (Formalism.REAL.smooth_lie_derivative a' b' hm.1) e, fun wd => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hm.2 (wd ++ [(a', b')])`. Use `⟨C, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h3` using `eword_append_Eab ε (coefX σ x₀ w (m : H)) (a', b') wd`.

Rewrite using `[← tmA_eword_congr e wd g hg, h3]`. Conclude with `hC g hg`.
-/
theorem tmC_good_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (w : H) {a : ℝ} {m : D} (hm : TmGood ε σ x₀ w a (m : H))
    (a' b' : Fin (2 * r + k + 1)) : TmGood ε σ x₀ w a ((E a' b' m : D) : H) := by
  have e : ∀ g, Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eab ε a' b' (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a' b' m : D) : H) g :=
    fun g hg => tmB_eab_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) w m a' b'
  refine ⟨Formalism.REAL.smooth_on_group_congr (Formalism.REAL.smooth_lie_derivative a' b' hm.1) e, fun wd => ?_⟩
  obtain ⟨C, hC⟩ := hm.2 (wd ++ [(a', b')])
  refine ⟨C, fun g hg => ?_⟩
  have h3 := eword_append_Eab ε (coefX σ x₀ w (m : H)) (a', b') wd
  rw [← tmA_eword_congr e wd g hg, h3]
  exact hC g hg

/- English proof (translation)
Use `set ψ : Mat k r → ℂ := fun y => ⟪ι w, S7.PsiM T μ y (ι v)⟫_ℂ with hψdef`. Establish `e : ∀ g, Formalism.REAL.inUJ ε g → coefX σ x₀ ((w : D) : H) ((v : D) : H) g = ψ (x₀⁻¹ * g)` using `fun g hg => hcoef _ (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) v w`. Establish `hψ : Formalism.REAL.SmoothOnG ε ψ`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `S7.psiM_smooth T μ hμ g₀ hg₀`.

Use `set Lc : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ (ι w)).comp (ContinuousLinearMap.apply ℂ T.V (ι v))`. Use `⟨U, fun z => Lc (F z), hU, hgU, (Lc.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩` and prove the remaining obligations. Introduce `g hg hgJ`. Simplify using `[hψdef, Lc, hfF g hg hgJ, innerSL_apply_apply]`. Use `⟨Formalism.REAL.smooth_on_group_congr (tmA_sm_left hψ (tmA_inUJ_inv hx₀)) (fun g hg => (e g hg).symm), fun wd => ?_⟩` and prove the remaining obligations.

Take `⟨C, hC⟩` from `hdec wd (ι v) (ι w)`. Take `⟨a₀⟩ : Nonempty (Fin (2 * r + k + 1))` from `⟨0⟩`. Use `⟨max C 0 * frob x₀ ^ a, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hy : x₀⁻¹ * g ∈ UJset ε` using `tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg`. Rewrite using `[tmA_eword_congr (h := fun g => ψ (x₀⁻¹ * g)) e wd g hg, congrFun (tmA_eword_left x₀⁻¹ ψ wd) g]`.

Establish `h1` using `hC _ hy`. Establish `h2` using `tmA_frob_trans hx₀ hg a₀ ha`. Establish `h3 : 0 ≤ frob (x₀⁻¹ * g) ^ (-a)` using `Real.rpow_nonneg (le_trans zero_le_one (tmA_one_le_frob hy a₀)) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tmC_good_V {lam : Fin (2 * r + k + 1) → ℝ} {V : Submodule ℂ D} {T : S7.KType ε (lowK ε lam)}
    {μ : Fin (2 * r + k + 1) → ℤ} {ι : V ≃ₗ[ℂ] T.V} (hμ : S7.IsMu lam μ)
    (hcoef : ∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ)
    {a : ℝ} (ha : 0 ≤ a)
    (hdec : ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (v₁ v₂ : T.V), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g‖ ≤ C * frob g ^ (-a))
    {x₀ : Mat k r} (hx₀ : x₀ ∈ UJset ε) (w v : V) : TmGood ε σ x₀ ((w : D) : H) a ((v : D) : H) := by
  set ψ : Mat k r → ℂ := fun y => ⟪ι w, S7.PsiM T μ y (ι v)⟫_ℂ with hψdef
  have e : ∀ g, Formalism.REAL.inUJ ε g → coefX σ x₀ ((w : D) : H) ((v : D) : H) g = ψ (x₀⁻¹ * g) :=
    fun g hg => hcoef _ (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) v w
  have hψ : Formalism.REAL.SmoothOnG ε ψ := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := S7.psiM_smooth T μ hμ g₀ hg₀
    set Lc : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ (ι w)).comp (ContinuousLinearMap.apply ℂ T.V (ι v))
    refine ⟨U, fun z => Lc (F z), hU, hgU, (Lc.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hg hgJ
    simp [hψdef, Lc, hfF g hg hgJ, innerSL_apply_apply]
  refine ⟨Formalism.REAL.smooth_on_group_congr (tmA_sm_left hψ (tmA_inUJ_inv hx₀)) (fun g hg => (e g hg).symm),
    fun wd => ?_⟩
  obtain ⟨C, hC⟩ := hdec wd (ι v) (ι w)
  obtain ⟨a₀⟩ : Nonempty (Fin (2 * r + k + 1)) := ⟨0⟩
  refine ⟨max C 0 * frob x₀ ^ a, fun g hg => ?_⟩
  have hy : x₀⁻¹ * g ∈ UJset ε := tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg
  rw [tmA_eword_congr (h := fun g => ψ (x₀⁻¹ * g)) e wd g hg,
    congrFun (tmA_eword_left x₀⁻¹ ψ wd) g]
  have h1 := hC _ hy
  have h2 := tmA_frob_trans hx₀ hg a₀ ha
  have h3 : 0 ≤ frob (x₀⁻¹ * g) ^ (-a) := Real.rpow_nonneg (le_trans zero_le_one (tmA_one_le_frob hy a₀)) _
  calc ‖Formalism.REAL.Eword ε wd ψ (x₀⁻¹ * g)‖ ≤ max C 0 * frob (x₀⁻¹ * g) ^ (-a) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
    _ ≤ max C 0 * (frob x₀ ^ a * frob g ^ (-a)) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 * frob x₀ ^ a * frob g ^ (-a) := by ring

/- English proof (translation)
Establish `hle : genSub E V ≤ tmGoodSub ε σ D x₀ ((w : D) : H) a` using `sInf_le ⟨fun v hv => tmC_good_V hμ hcoef ha hdec hx₀ w ⟨v, hv⟩, fun a' b' m hm => tmC_good_E hσ hD hx₀ _ hm a' b'⟩`. Conclude with `hle hf`.
-/
theorem tmC_good_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {lam : Fin (2 * r + k + 1) → ℝ}
    {V : Submodule ℂ D} {T : S7.KType ε (lowK ε lam)}
    {μ : Fin (2 * r + k + 1) → ℤ} {ι : V ≃ₗ[ℂ] T.V} (hμ : S7.IsMu lam μ)
    (hcoef : ∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ)
    {a : ℝ} (ha : 0 ≤ a)
    (hdec : ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (v₁ v₂ : T.V), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g‖ ≤ C * frob g ^ (-a))
    {x₀ : Mat k r} (hx₀ : x₀ ∈ UJset ε) (w : V) {f : D} (hf : f ∈ genSub E V) :
    TmGood ε σ x₀ ((w : D) : H) a ((f : D) : H) := by
  have hle : genSub E V ≤ tmGoodSub ε σ D x₀ ((w : D) : H) a :=
    sInf_le ⟨fun v hv => tmC_good_V hμ hcoef ha hdec hx₀ w ⟨v, hv⟩,
      fun a' b' m hm => tmC_good_E hσ hD hx₀ _ hm a' b'⟩
  exact hle hf

end Good

section Mult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

/- English proof (translation)
Simplify using `[cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]`.
-/
theorem tmD_cJ_lin (x₁ y y' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) :
    cJ ε x₁ (y + c • y') g = cJ ε x₁ y g + c * cJ ε x₁ y' g := by
  simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]

/- English proof (translation)
Simplify using `[cJ, Formalism.QuantumDeterminants.herm]`.
-/
theorem tmD_cJ_zero (x₁ : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : cJ ε x₁ 0 g = 0 := by
  simp [cJ, Formalism.QuantumDeterminants.herm]

def tmD_cJL (ε : Fin (2 * r + k + 1) → Bool) (x₁ y : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => cJ ε x₁ y g
      map_add' := fun A B => by
        simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c A => by
        simp only [cJ, Formalism.QuantumDeterminants.herm, RingHom.id_apply, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
          Complex.real_smul] }

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [tmD_cJL, LinearMap.coe_toContinuousLinearMap']`. Both sides reduce to the same expression.
-/
theorem tmD_cJL_coe (x₁ y : Fin (2 * r + k + 1) → ℂ) : ⇑(tmD_cJL ε x₁ y) = cJ ε x₁ y := by
  ext g
  simp only [tmD_cJL, LinearMap.coe_toContinuousLinearMap']
  rfl

/- English proof (translation)
Introduce `g₀ _`. Use `⟨Set.univ, ⇑(tmD_cJL ε x₁ y), isOpen_univ, Set.mem_univ _, (tmD_cJL ε x₁ y).contDiff.contDiffOn, fun g _ _ => by rw [tmD_cJL_coe]⟩` and prove the remaining obligations.
-/
theorem tmD_cJ_smooth (x₁ y : Fin (2 * r + k + 1) → ℂ) : Formalism.REAL.SmoothOnG ε (cJ ε x₁ y) := by
  intro g₀ _
  refine ⟨Set.univ, ⇑(tmD_cJL ε x₁ y), isOpen_univ, Set.mem_univ _,
    (tmD_cJL ε x₁ y).contDiff.contDiffOn, fun g _ _ => by rw [tmD_cJL_coe]⟩

/- English proof (translation)
Rewrite using `[Formalism.REAL.right_derivative_extends _ ε (cJ ε x₁ y) (⇑(tmD_cJL ε x₁ y)) Set.univ g X isOpen_univ (Set.mem_univ g) hg (tmD_cJL ε x₁ y).contDiff.contDiffOn (fun h _ _ => by rw [tmD_cJL_coe]) hX, ContinuousLinearMap.fderiv, tmD_cJL_coe]`. Simplify using `[cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_mulVec]`.
-/
theorem tmD_rd_cJ (x₁ y : Fin (2 * r + k + 1) → ℂ) {X g : Mat k r} (hX : Formalism.REAL.inG ε X)
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Rd X (cJ ε x₁ y) g = cJ ε x₁ (X *ᵥ y) g := by
  rw [Formalism.REAL.right_derivative_extends _ ε (cJ ε x₁ y) (⇑(tmD_cJL ε x₁ y)) Set.univ g X isOpen_univ (Set.mem_univ g) hg
    (tmD_cJL ε x₁ y).contDiff.contDiffOn (fun h _ _ => by rw [tmD_cJL_coe]) hX,
    ContinuousLinearMap.fderiv, tmD_cJL_coe]
  simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[Formalism.REAL.lie_derivative_def, tmD_rd_cJ x₁ y (Formalism.REAL.real_part_single_mem ε a b) hg, tmD_rd_cJ x₁ y (Formalism.REAL.imaginary_part_single_mem ε a b) hg, ← tmD_cJ_lin]`. Use `congr 1`. Establish `hZ` using `(Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b 1)).2.2.1`. Rewrite using `[← Matrix.smul_mulVec, ← Matrix.add_mulVec, ← hZ]`.
-/
theorem tmD_eab_cJ (x₁ y : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) {g : Mat k r}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b (cJ ε x₁ y) g = cJ ε x₁ (Matrix.single a b 1 *ᵥ y) g := by
  rw [Formalism.REAL.lie_derivative_def, tmD_rd_cJ x₁ y (Formalism.REAL.real_part_single_mem ε a b) hg, tmD_rd_cJ x₁ y (Formalism.REAL.imaginary_part_single_mem ε a b) hg,
    ← tmD_cJ_lin]
  congr 1
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b 1)).2.2.1
  rw [← Matrix.smul_mulVec, ← Matrix.add_mulVec, ← hZ]

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `hc : c = b`. Substitute `hc` using the available equality. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hc, Ne.symm hc]`.
-/
theorem tmD_single_mulVec (a b c : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) *ᵥ Pi.single c 1 = if c = b then Pi.single a 1 else 0 := by
  ext i
  by_cases hc : c = b
  · subst hc
    by_cases h : i = a
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hc, Ne.symm hc]

/- English proof (translation)
Unfold `cJ Formalism.QuantumDeterminants.herm`. Rewrite using `[dotProduct, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Pi.star_apply, norm_star]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Establish `e : (Jm ε *ᵥ (g *ᵥ Pi.single c 1)) i = (if ε i then 1 else -1) * g i c`. Rewrite using `[Jm, Matrix.mulVec_diagonal]`. Use `congr 1`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[e, norm_mul]`.

Use `tmA_entry_le_frob g i c` as an intermediate fact. Apply the tactic sequence `split_ifs <;> simpa using this`.
-/
theorem tmD_cJ_bound (x₁ : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * r + k + 1)) (g : Mat k r) :
    ‖cJ ε x₁ (Pi.single c 1) g‖ ≤ (∑ i, ‖x₁ i‖) * frob g := by
  unfold cJ Formalism.QuantumDeterminants.herm
  rw [dotProduct, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Pi.star_apply, norm_star]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e : (Jm ε *ᵥ (g *ᵥ Pi.single c 1)) i = (if ε i then 1 else -1) * g i c := by
    rw [Jm, Matrix.mulVec_diagonal]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, norm_mul]
  have := tmA_entry_le_frob g i c
  split_ifs <;> simpa using this

end Mult

end ReciprocityTheory.ChartRestriction.DS.Lap
