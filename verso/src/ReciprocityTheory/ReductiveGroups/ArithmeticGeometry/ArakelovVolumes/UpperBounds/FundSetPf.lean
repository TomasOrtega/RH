import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
import Lemmata.GeneralBFactTer.Imports

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((↑(δ * δ') : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = (δ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)`. Rewrite using `[Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (δ δ' : GL (Fin r) E) (y : Frame Ψ r) :
    lact (δ * δ') y = lact δ (lact δ' y) := by
  funext τ
  show ((↑(δ * δ') : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem lact_one {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat y τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) = (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ * mat b τ`. Rewrite using `[Matrix.mul_assoc]`.
-/
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact δ (rmul y b) = rmul (lact δ y) b := by
  funext τ
  show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat y τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ * mat b τ
  rw [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← lact_mul, inv_mul_cancel, lact_one]`.
-/
theorem lact_inv {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) (y : Frame Ψ r) : lact δ⁻¹ (lact δ y) = y := by
  rw [← lact_mul, inv_mul_cancel, lact_one]

/- English proof (translation)
Conclude with `Bl.general_b_fact_ter.goal1 hN hN1 hN' hN'1 hB hB' hBd h`.
-/
theorem nb_uniq {N N' B B' : Matrix (Fin r) (Fin r) ℂ} (hN : ∀ a c : Fin r, a < c → N a c = 0)
    (hN1 : ∀ a, N a a = 1) (hN' : ∀ a c : Fin r, a < c → N' a c = 0) (hN'1 : ∀ a, N' a a = 1)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) (hB' : ∀ a c : Fin r, c < a → B' a c = 0) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by
  exact Bl.general_b_fact_ter.goal1 hN hN1 hN' hN'1 hB hB' hBd h

/- English proof (translation)
Establish `hτ : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ`. Introduce `τ`. Establish `h1 : mat x0 τ * ExF.nM X z τ * mat b τ = mat x0 τ * ExF.nM X z' τ * mat b' τ` using `congrFun h τ`. Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)`. Establish `h2 : ExF.nM X z τ * mat b τ = ExF.nM X z' τ * mat b' τ`.

Use `congrArg (fun M => (mat x0 τ)⁻¹ * M) h1` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Conclude with `nb_uniq (fun a c hac => ExF.nM_upper X z τ hac) (ExF.nM_diag X z τ) (fun a c hac => ExF.nM_upper X z' τ hac) (ExF.nM_diag X z' τ) (fun a c h => (hb τ).2 a c h) (fun a c h => (hb' τ).2 a c h) (hb τ).1 h2`. Use extensionality with `e`. Take `⟨p, rfl⟩` from `(Fintype.equivFin (Ent X)).surjective e`.

Break down `p with ⟨τ, ⟨⟨a, c⟩, hac⟩⟩` into its components or cases. Use `congrFun (congrFun (hτ τ) a) c` as an intermediate fact. Simplify `this` using `[ExF.nM, mat, nmat, hac]`.
-/
theorem cpt_uniq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z z' : V (nd X)}
    {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') : z = z' := by
  have hτ : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ := by
    intro τ
    have h1 : mat x0 τ * ExF.nM X z τ * mat b τ = mat x0 τ * ExF.nM X z' τ * mat b' τ := congrFun h τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
    have h2 : ExF.nM X z τ * mat b τ = ExF.nM X z' τ * mat b' τ := by
      have := congrArg (fun M => (mat x0 τ)⁻¹ * M) h1
      simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
    exact nb_uniq (fun a c hac => ExF.nM_upper X z τ hac) (ExF.nM_diag X z τ)
      (fun a c hac => ExF.nM_upper X z' τ hac) (ExF.nM_diag X z' τ) (fun a c h => (hb τ).2 a c h)
      (fun a c h => (hb' τ).2 a c h) (hb τ).1 h2
  ext e
  obtain ⟨p, rfl⟩ := (Fintype.equivFin (Ent X)).surjective e
  rcases p with ⟨τ, ⟨⟨a, c⟩, hac⟩⟩
  have := congrFun (congrFun (hτ τ) a) c
  simpa [ExF.nM, mat, nmat, hac] using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, h⟩ τ a c hca`. Establish `h1 : (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y' τ * mat b τ` using `congrFun h τ`. Rewrite using `[Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[show mat b τ a c = b τ a c from rfl, (hb τ).2 a c hca, mul_zero]`.

Introduce `h`. Use `⟨fun τ => (mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ), fun τ => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hd : ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0`. Rewrite using `[show ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (δ : Matrix (Fin r) (Fin r) E).det from (RingHom.map_det τ.1 _).symm]`. Conclude with `(map_ne_zero τ.1).mpr (Matrix.isUnits_det_units δ).ne_zero`.

Use `show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)).det ≠ 0`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (inv_ne_zero (hy' τ)) (mul_ne_zero hd (hy τ))`. Introduce `a c hca show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)) a c = 0`. Rewrite using `[Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, ← Matrix.mul_assoc, h τ a c hca, smul_zero]`.

Use function extensionality and compare the values at `τ show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = mat y' τ * ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ))`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hy' τ))]`.
-/
theorem charB {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) {y y' : Frame Ψ r}
    (hy : ∀ τ, (mat y τ).det ≠ 0) (hy' : ∀ τ, (mat y' τ).det ≠ 0) :
    (∃ b ∈ Bor Ψ r, lact δ y = rmul y' b) ↔ ∀ τ : Ψ, ∀ a c : Fin r, c < a →
      ((mat y' τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ) a c = 0 := by
  constructor
  · rintro ⟨b, hb, h⟩ τ a c hca
    have h1 : (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y' τ * mat b τ := congrFun h τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    rw [show mat b τ a c = b τ a c from rfl, (hb τ).2 a c hca, mul_zero]
  · intro h
    refine ⟨fun τ => (mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ), fun τ => ⟨?_, ?_⟩, ?_⟩
    · have hd : ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
        rw [show ((δ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (δ : Matrix (Fin r) (Fin r) E).det from
          (RingHom.map_det τ.1 _).symm]
        exact (map_ne_zero τ.1).mpr (Matrix.isUnits_det_units δ).ne_zero
      show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero (hy' τ)) (mul_ne_zero hd (hy τ))
    · intro a c hca
      show ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)) a c = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, ← Matrix.mul_assoc, h τ a c hca, smul_zero]
    · funext τ
      show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) =
        mat y' τ * ((mat y' τ)⁻¹ * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ))
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hy' τ))]

variable (X : Data E r) (x0 : Frame X.Ψ r)

def R (z z' : V (nd X)) : Prop :=
  ∃ δ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact δ (cpt X x0 z) = rmul (cpt X x0 z') b

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by rw [lact_one, ExtFPf.rmul_oneF]⟩`.
-/
theorem R_refl (z : V (nd X)) : R X x0 z z :=
  ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by rw [lact_one, ExtFPf.rmul_oneF]⟩

/- English proof (translation)
Take `⟨δ, hδ, b, hb, h⟩` from `h`. Use `⟨δ⁻¹, X.Γ.inv_mem hδ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]`. Use `_ = _ := lact_inv _ _`.
-/
theorem R_symm {z z' : V (nd X)} (h : R X x0 z z') : R X x0 z' z := by
  obtain ⟨δ, hδ, b, hb, h⟩ := h
  refine ⟨δ⁻¹, X.Γ.inv_mem hδ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
  calc lact δ⁻¹ (cpt X x0 z') = lact δ⁻¹ (lact δ (rmul (cpt X x0 z) (ExtFPf.invF X b))) := by
        rw [lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
    _ = _ := lact_inv _ _

/- English proof (translation)
Take `⟨δ1, hδ1, b1, hb1, h1⟩` from `h1`. Take `⟨δ2, hδ2, b2, hb2, h2⟩` from `h2`. Conclude with `⟨δ2 * δ1, X.Γ.mul_mem hδ2 hδ1, rmul b2 b1, ExtFPf.mul_mem X hb2 hb1, by`. Rewrite using `[lact_mul, h1, lact_rmul, h2, ExtFPf.rmul_assoc]⟩`.
-/
theorem R_trans {z z' z'' : V (nd X)} (h1 : R X x0 z z') (h2 : R X x0 z' z'') : R X x0 z z'' := by
  obtain ⟨δ1, hδ1, b1, hb1, h1⟩ := h1
  obtain ⟨δ2, hδ2, b2, hb2, h2⟩ := h2
  exact ⟨δ2 * δ1, X.Γ.mul_mem hδ2 hδ1, rmul b2 b1, ExtFPf.mul_mem X hb2 hb1, by
    rw [lact_mul, h1, lact_rmul, h2, ExtFPf.rmul_assoc]⟩

/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply, nmat]`. Use `continuous_finsetSum _ fun k _ => continuous_const.mul ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem cont_cpt : Continuous (cpt X x0) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply, nmat]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  split_ifs <;> fun_prop

/- English proof (translation)
The claim follows from `(hz τ).1`.
-/
theorem det_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) : (mat (cpt X x0 z) τ).det ≠ 0 := (hz τ).1

/- English proof (translation)
Establish `hM : Continuous fun z : V (nd X) => mat (cpt X x0 z) τ` using `(continuous_apply τ).comp (cont_cpt X x0)`. Conclude with `((((hM.comp continuous_snd).matrix_adjugate).matrix_mul continuous_const).matrix_mul (hM.comp continuous_fst)).matrix_elem a c`.
-/
theorem cont_ent (δ : GL (Fin r) E) (τ : X.Ψ) (a c : Fin r) :
    Continuous fun p : V (nd X) × V (nd X) =>
      ((mat (cpt X x0 p.2) τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 p.1) τ) a c := by
  have hM : Continuous fun z : V (nd X) => mat (cpt X x0 z) τ := (continuous_apply τ).comp (cont_cpt X x0)
  exact ((((hM.comp continuous_snd).matrix_adjugate).matrix_mul continuous_const).matrix_mul
    (hM.comp continuous_fst)).matrix_elem a c

/- English proof (translation)
Take `⟨U, hU, U', hU', hfin⟩` from `hP _ hz0 _ hz0`. Establish `hc` using `cont_cpt X x0`. Establish `hev : ∀ᶠ p in 𝓝 (z0, z0), cpt X x0 p.1 ∈ U ∧ cpt X x0 p.2 ∈ U' ∧ ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b}, δ ≠ 1 → ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ ((mat (cpt X x0 p.2) τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * m …`. Use `Eventually.and ((hc.comp continuous_fst).continuousAt.preimage_mem_nhds hU) (Eventually.and ((hc.comp continuous_snd).continuousAt.preimage_mem_nhds hU') ((eventually_all_finite hfin).mpr ?_))` and prove the remaining obligations. Introduce `δ hδ`.

Distinguish the cases in `h1 : δ = 1`. Conclude with `Eventually.of_forall fun _ h => absurd h1 h`. Establish `: ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ ((mat (cpt X x0 z0) τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 z0) τ) a c ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`.

Take `⟨b, hb, hbe⟩` from `(charB δ (det_cpt X x0 hz0) (det_cpt X x0 hz0)).mpr hall`. Conclude with `h1 (X.Γ_free δ hδ.1 _ hz0 b hb hbe)`. Take `⟨τ, a, c, hca, hne⟩` from `this`. Conclude with `Filter.mem_of_superset ((isOpen_ne_fun (cont_ent X x0 δ τ a c) continuous_const).mem_nhds hne) fun p hp _ => ⟨τ, a, c, hca, hp⟩`. Rewrite `hev` using `[nhds_prod_eq]`.

Take `⟨t, ht, hts⟩` from `Filter.mem_prod_self_iff.mp hev`. Take `⟨O, hOt, hOo, hz0O⟩` from `mem_nhds_iff.mp ht`. Use `⟨O, hOo, hz0O, fun z hz z' hz' hR => ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ, b, hb, h⟩` from `hR`. Take `⟨hu, hu', hall⟩` from `hts (mk_mem_prod (hOt hz.1) (hOt hz'.1))`.

Distinguish the cases in `h1 : δ = 1`. Substitute `h1` using the available equality. Rewrite `h` using `[lact_one, ← ExtFPf.rmul_oneF X (cpt X x0 z)]`. Conclude with `cpt_uniq X ho (ExtFPf.oneF_mem X) hb h`. Take `⟨τ, a, c, hca, hne⟩` from `hall δ ⟨hδ, _, hu, _, hu', b, hb, h⟩ h1`.

Conclude with `absurd ((charB δ (det_cpt X x0 hz.2) (det_cpt X x0 hz'.2)).mp ⟨b, hb, h⟩ τ a c hca) hne`.
-/
theorem small (ho : IsOrth X x0) (hP : PropDisc X) {z0 : V (nd X)} (hz0 : z0 ∈ OmF X x0) :
    ∃ O : Set (V (nd X)), IsOpen O ∧ z0 ∈ O ∧
      ∀ z ∈ O ∩ OmF X x0, ∀ z' ∈ O ∩ OmF X x0, R X x0 z z' → z = z' := by
  obtain ⟨U, hU, U', hU', hfin⟩ := hP _ hz0 _ hz0
  have hc := cont_cpt X x0
  have hev : ∀ᶠ p in 𝓝 (z0, z0), cpt X x0 p.1 ∈ U ∧ cpt X x0 p.2 ∈ U' ∧
      ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
        δ ≠ 1 → ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧
          ((mat (cpt X x0 p.2) τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat (cpt X x0 p.1) τ) a c ≠ 0 := by
    refine Eventually.and ((hc.comp continuous_fst).continuousAt.preimage_mem_nhds hU)
      (Eventually.and ((hc.comp continuous_snd).continuousAt.preimage_mem_nhds hU') ((eventually_all_finite hfin).mpr ?_))
    intro δ hδ
    by_cases h1 : δ = 1
    · exact Eventually.of_forall fun _ h => absurd h1 h
    · have : ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧
          ((mat (cpt X x0 z0) τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat (cpt X x0 z0) τ) a c ≠ 0 := by
        by_contra hall
        push Not at hall
        obtain ⟨b, hb, hbe⟩ := (charB δ (det_cpt X x0 hz0) (det_cpt X x0 hz0)).mpr hall
        exact h1 (X.Γ_free δ hδ.1 _ hz0 b hb hbe)
      obtain ⟨τ, a, c, hca, hne⟩ := this
      exact Filter.mem_of_superset ((isOpen_ne_fun (cont_ent X x0 δ τ a c) continuous_const).mem_nhds hne)
        fun p hp _ => ⟨τ, a, c, hca, hp⟩
  rw [nhds_prod_eq] at hev
  obtain ⟨t, ht, hts⟩ := Filter.mem_prod_self_iff.mp hev
  obtain ⟨O, hOt, hOo, hz0O⟩ := mem_nhds_iff.mp ht
  refine ⟨O, hOo, hz0O, fun z hz z' hz' hR => ?_⟩
  obtain ⟨δ, hδ, b, hb, h⟩ := hR
  obtain ⟨hu, hu', hall⟩ := hts (mk_mem_prod (hOt hz.1) (hOt hz'.1))
  by_cases h1 : δ = 1
  · subst h1
    rw [lact_one, ← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    exact cpt_uniq X ho (ExtFPf.oneF_mem X) hb h
  · obtain ⟨τ, a, c, hca, hne⟩ := hall δ ⟨hδ, _, hu, _, hu', b, hb, h⟩ h1
    exact absurd ((charB δ (det_cpt X x0 hz.2) (det_cpt X x0 hz'.2)).mp ⟨b, hb, h⟩ τ a c hca) hne

def Sat (A : Set (V (nd X))) : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ ∃ z' ∈ A, R X x0 z z'}

/- English proof (translation)
Establish `: Countable E` using `Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective`. Establish `: Countable (Matrix (Fin r) (Fin r) E)` using `inferInstanceAs (Countable (Fin r → Fin r → E))`. Conclude with `Function.Injective.countable fun a b h => Units.ext h`.
-/
theorem countable_GL : Countable (GL (Fin r) E) := by
  have : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable fun a b h => Units.ext h

/- English proof (translation)
Use `countable_GL (E := E) (r := r)` as an intermediate fact. Establish `hO : MeasurableSet (OmF X x0)` using `(ExF.isOpen_OmF X x0).measurableSet`. Set `T : X.Γ → Set (V (nd X) × V (nd X))` to `fun δ => {p | p.1 ∈ OmF X x0 ∧ p.2 ∈ A ∧ ∀ τ : X.Ψ, ∀ a c : Fin r, c < a → ((mat (cpt X x0 p.2) τ).adjugate * ((δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 p.1) τ) a c = 0}`. Establish `heq : Sat X x0 A = ⋃ δ : X.Γ, Prod.fst '' T δ`. Use extensionality with `z`.

Simplify using `only [Sat, R, mem_ofPred_eq, mem_iUnion, mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, z', hz', δ, hδ, b, hb, h⟩`. Conclude with `⟨⟨δ, hδ⟩, (z, z'), ⟨hz, hz', (charB δ (det_cpt X x0 hz) (det_cpt X x0 (hAO hz'))).mp ⟨b, hb, h⟩⟩, rfl⟩`. Introduce and unpack `⟨δ, ⟨p1, p2⟩, ⟨h1, h2, h3⟩, rfl⟩`.

Conclude with `⟨h1, p2, h2, δ.1, δ.2, (charB δ.1 (det_cpt X x0 h1) (det_cpt X x0 (hAO h2))).mpr h3⟩`. Rewrite using `[heq]`. Use `MeasurableSet.iUnion fun δ => ?_` and prove the remaining obligations. Establish `hcl : IsClosed {p : V (nd X) × V (nd X) | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a → ((mat (cpt X x0 p.2) τ).adjugate * ((δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 p.1) τ) a c = 0}`. Simplify using `only [ofPred_forall]`.

Conclude with `isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (cont_ent X x0 δ τ a c) continuous_const`. Establish `hTm : MeasurableSet (T δ)` using `(measurable_fst hO).inter ((measurable_snd hA).inter hcl.measurableSet)`. Use `MeasurableSet.image_of_continuousOn_injOn hTm continuous_fst.continuousOn ?_` and prove the remaining obligations. Introduce and unpack `⟨z, z1⟩ ⟨hz, hz1, h1⟩ ⟨z', z2⟩ ⟨-, hz2, h2⟩ hzz`. Take `rfl : z = z'` from `hzz`.

Take `⟨b1, hb1, e1⟩` from `(charB δ.1 (det_cpt X x0 hz) (det_cpt X x0 (hAO hz1))).mpr h1`. Take `⟨b2, hb2, e2⟩` from `(charB δ.1 (det_cpt X x0 hz) (det_cpt X x0 (hAO hz2))).mpr h2`. Conclude with `Prod.ext rfl (cpt_uniq X ho hb1 hb2 (e1.symm.trans e2))`.
-/
theorem meas_Sat (ho : IsOrth X x0) {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (Sat X x0 A) := by
  have := countable_GL (E := E) (r := r)
  have hO : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  let T : X.Γ → Set (V (nd X) × V (nd X)) := fun δ => {p | p.1 ∈ OmF X x0 ∧ p.2 ∈ A ∧
    ∀ τ : X.Ψ, ∀ a c : Fin r, c < a → ((mat (cpt X x0 p.2) τ).adjugate *
      ((δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 p.1) τ) a c = 0}
  have heq : Sat X x0 A = ⋃ δ : X.Γ, Prod.fst '' T δ := by
    ext z
    simp only [Sat, R, mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨hz, z', hz', δ, hδ, b, hb, h⟩
      exact ⟨⟨δ, hδ⟩, (z, z'), ⟨hz, hz', (charB δ (det_cpt X x0 hz) (det_cpt X x0 (hAO hz'))).mp ⟨b, hb, h⟩⟩, rfl⟩
    · rintro ⟨δ, ⟨p1, p2⟩, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨h1, p2, h2, δ.1, δ.2, (charB δ.1 (det_cpt X x0 h1) (det_cpt X x0 (hAO h2))).mpr h3⟩
  rw [heq]
  refine MeasurableSet.iUnion fun δ => ?_
  have hcl : IsClosed {p : V (nd X) × V (nd X) | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a → ((mat (cpt X x0 p.2) τ).adjugate *
      ((δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x0 p.1) τ) a c = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (cont_ent X x0 δ τ a c) continuous_const
  have hTm : MeasurableSet (T δ) := (measurable_fst hO).inter ((measurable_snd hA).inter hcl.measurableSet)
  refine MeasurableSet.image_of_continuousOn_injOn hTm continuous_fst.continuousOn ?_
  rintro ⟨z, z1⟩ ⟨hz, hz1, h1⟩ ⟨z', z2⟩ ⟨-, hz2, h2⟩ hzz
  obtain rfl : z = z' := hzz
  obtain ⟨b1, hb1, e1⟩ := (charB δ.1 (det_cpt X x0 hz) (det_cpt X x0 (hAO hz1))).mpr h1
  obtain ⟨b2, hb2, e2⟩ := (charB δ.1 (det_cpt X x0 hz) (det_cpt X x0 (hAO hz2))).mpr h2
  exact Prod.ext rfl (cpt_uniq X ho hb1 hb2 (e1.symm.trans e2))

/- English proof (translation)
Unfold `muF`. Conclude with `(withDensity_absolutelyContinuous _ _) (ae_restrict_mem (ExF.isOpen_OmF X x0).measurableSet)`.
-/
theorem ae_OmF' : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
  unfold muF
  exact (withDensity_absolutelyContinuous _ _) (ae_restrict_mem (ExF.isOpen_OmF X x0).measurableSet)

/- English proof (translation)
Introduce `r X x0 ho hP`. Establish `hO : MeasurableSet (OmF X x0)` using `(ExF.isOpen_OmF X x0).measurableSet`. Establish `hsm : ∀ z, z ∈ OmF X x0 → ∃ O : Set (V (nd X)), IsOpen O ∧ z ∈ O ∧ ∀ z ∈ O ∩ OmF X x0, ∀ z' ∈ O ∩ OmF X x0, R X x0 z z' → z = z'` using `fun z hz => small X x0 ho hP hz`. Use `choose! O hOo hzO hOs using hsm`. Take `⟨t, htO, htc, hcov⟩` from `TopologicalSpace.countable_cover_nhdsWithin (s := OmF X x0) (f := O) fun z hz => mem_nhdsWithin_of_mem_nhds ((hOo z hz).mem_nhds (hzO z hz))`.

Break down `t.eq_empty_or_nonempty with hte | hne` into its components or cases. Establish `hE : OmF X x0 = ∅` using `by rw [hte] at hcov; simpa using hcov`. Use `⟨∅, MeasurableSet.empty, empty_subset _, fun z hz => absurd hz (notMem_empty z), ?_⟩` and prove the remaining obligations. Use `filter_upwards [ae_OmF' X x0] with z hz`. Rewrite `hz` using `[hE]`.

Conclude with `absurd hz (notMem_empty z)`. Take `⟨e, he⟩` from `htc.exists_eq_range hne`. Establish `het : ∀ k, e k ∈ OmF X x0` using `fun k => htO (by rw [he]; exact mem_range_self k)`. Set `W : ℕ → Set (V (nd X))` to `fun k => O (e k) ∩ OmF X x0`. Establish `hWm : ∀ k, MeasurableSet (W k)` using `fun k => (hOo (e k) (het k)).measurableSet.inter hO`.

Establish `hWO : ∀ k, W k ⊆ OmF X x0` using `fun k => inter_subset_right`. Use `⟨⋃ k, W k \ ⋃ j, ⋃ (_ : j < k), Sat X x0 (W j), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `MeasurableSet.iUnion fun k => (hWm k).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => meas_Sat X x0 ho (hWm j) (hWO j))`. Conclude with `iUnion_subset fun k => sdiff_subset.trans (hWO k)`. Introduce `z hz z' hz' γ hγ b hb h`.

Take `⟨k, hzk, hzk'⟩` from `mem_iUnion.mp hz`. Take `⟨k', hzk2, hzk2'⟩` from `mem_iUnion.mp hz'`. Establish `hR : R X x0 z' z` using `⟨γ⁻¹, X.Γ.inv_mem hγ, b, hb, by rw [h, lact_inv]⟩`. Break down `lt_trichotomy k k' with hkk | rfl | hkk` into its components or cases. Conclude with `(hzk2' (mem_iUnion₂.mpr ⟨k, hkk, hzk2.2, z, hzk, hR⟩)).elim`.

Conclude with `hOs (e k) (het k) z hzk z' hzk2 (R_symm X x0 hR)`. Conclude with `(hzk' (mem_iUnion₂.mpr ⟨k', hkk, hzk.2, z', hzk2, R_symm X x0 hR⟩)).elim`. Use `filter_upwards [ae_OmF' X x0] with z hz`. Establish `hex : ∃ k, ∃ z' ∈ W k, R X x0 z z'`. Take `⟨x, hxt, hzx⟩` from `mem_iUnion₂.mp (hcov hz)`.

Rewrite `hxt` using `[he]`. Take `⟨k, rfl⟩` from `hxt`. Conclude with `⟨k, z, ⟨hzx, hz⟩, R_refl X x0 z⟩`. Take `⟨z', hz'W, hR⟩` from `Nat.find_spec hex`. Take `⟨δ, hδ, b, hb, h⟩` from `hR`.

Use `⟨z', mem_iUnion.mpr ⟨Nat.find hex, hz'W, fun hin => ?_⟩, δ⁻¹, X.Γ.inv_mem hδ, b, hb, by rw [← h, lact_inv]⟩` and prove the remaining obligations. Take `⟨j, hj, hz'S⟩` from `mem_iUnion₂.mp hin`. Take `⟨-, z'', hz'', hR'⟩` from `hz'S`. Conclude with `Nat.find_min hex hj ⟨z'', hz'', R_trans X x0 ⟨δ, hδ, b, hb, h⟩ hR'⟩`.
-/
theorem fundSet_main : FundSetStatement (E := E) := by
  intro r X x0 ho hP
  classical
  have hO : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  have hsm : ∀ z, z ∈ OmF X x0 → ∃ O : Set (V (nd X)), IsOpen O ∧ z ∈ O ∧
      ∀ z ∈ O ∩ OmF X x0, ∀ z' ∈ O ∩ OmF X x0, R X x0 z z' → z = z' := fun z hz => small X x0 ho hP hz
  choose! O hOo hzO hOs using hsm
  obtain ⟨t, htO, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := OmF X x0) (f := O)
    fun z hz => mem_nhdsWithin_of_mem_nhds ((hOo z hz).mem_nhds (hzO z hz))
  rcases t.eq_empty_or_nonempty with hte | hne
  · have hE : OmF X x0 = ∅ := by rw [hte] at hcov; simpa using hcov
    refine ⟨∅, MeasurableSet.empty, empty_subset _, fun z hz => absurd hz (notMem_empty z), ?_⟩
    filter_upwards [ae_OmF' X x0] with z hz
    rw [hE] at hz; exact absurd hz (notMem_empty z)
  obtain ⟨e, he⟩ := htc.exists_eq_range hne
  have het : ∀ k, e k ∈ OmF X x0 := fun k => htO (by rw [he]; exact mem_range_self k)
  let W : ℕ → Set (V (nd X)) := fun k => O (e k) ∩ OmF X x0
  have hWm : ∀ k, MeasurableSet (W k) := fun k => (hOo (e k) (het k)).measurableSet.inter hO
  have hWO : ∀ k, W k ⊆ OmF X x0 := fun k => inter_subset_right
  refine ⟨⋃ k, W k \ ⋃ j, ⋃ (_ : j < k), Sat X x0 (W j), ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun k => (hWm k).diff
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => meas_Sat X x0 ho (hWm j) (hWO j))
  · exact iUnion_subset fun k => sdiff_subset.trans (hWO k)
  · intro z hz z' hz' γ hγ b hb h
    obtain ⟨k, hzk, hzk'⟩ := mem_iUnion.mp hz
    obtain ⟨k', hzk2, hzk2'⟩ := mem_iUnion.mp hz'
    have hR : R X x0 z' z := ⟨γ⁻¹, X.Γ.inv_mem hγ, b, hb, by rw [h, lact_inv]⟩
    rcases lt_trichotomy k k' with hkk | rfl | hkk
    · exact (hzk2' (mem_iUnion₂.mpr ⟨k, hkk, hzk2.2, z, hzk, hR⟩)).elim
    · exact hOs (e k) (het k) z hzk z' hzk2 (R_symm X x0 hR)
    · exact (hzk' (mem_iUnion₂.mpr ⟨k', hkk, hzk.2, z', hzk2, R_symm X x0 hR⟩)).elim
  · filter_upwards [ae_OmF' X x0] with z hz
    have hex : ∃ k, ∃ z' ∈ W k, R X x0 z z' := by
      obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcov hz)
      rw [he] at hxt
      obtain ⟨k, rfl⟩ := hxt
      exact ⟨k, z, ⟨hzx, hz⟩, R_refl X x0 z⟩
    obtain ⟨z', hz'W, hR⟩ := Nat.find_spec hex
    obtain ⟨δ, hδ, b, hb, h⟩ := hR
    refine ⟨z', mem_iUnion.mpr ⟨Nat.find hex, hz'W, fun hin => ?_⟩, δ⁻¹, X.Γ.inv_mem hδ, b, hb, by rw [← h, lact_inv]⟩
    obtain ⟨j, hj, hz'S⟩ := mem_iUnion₂.mp hin
    obtain ⟨-, z'', hz'', hR'⟩ := hz'S
    exact Nat.find_min hex hj ⟨z'', hz'', R_trans X x0 ⟨δ, hδ, b, hb, h⟩ hR'⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `FundSetPf.fundSet_main`.
-/
theorem fundSet_holds : FundSetStatement (E := E) := FundSetPf.fundSet_main

end ReciprocityTheory.ChartRestriction.G.AR.Up
