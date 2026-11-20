import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
private theorem emb_val (γ : Gm L N) (w : InfinitePlace L) :
    ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
private theorem act_inj (γ : Gm L N) : Function.Injective (actL (emb L N γ) : HS L N → HS L N) := by
  intro a b hab
  have e := congrArg (actL (emb L N γ)⁻¹) hab
  rwa [← actL_mul, ← actL_mul, inv_mul_cancel, actL_one, actL_one] at e

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem inj_finsum {ι : Type} (f : HS L N →L[ℝ] HS L N) (hf : Function.Injective f)
    (g : ι → HS L N) : f (∑ᶠ i, g i) = ∑ᶠ i, f (g i) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum f h
  · have e : (Function.support fun i => f (g i)) = Function.support g := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff f hf]
    have h' : ¬ (Function.support fun i => f (g i)).Finite := by rwa [e]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mat_rk (h : HS L N) (v : Lat L N) (w : InfinitePlace L) :
    mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem rk_act (γ : Gm L N) (h : HS L N) (v : Lat L N) :
    rk (actL (emb L N γ) h) (γ • v) = actL (emb L N γ) (rk h v) := by
  refine HS_ext fun w => ?_
  have hv : toR (γ • v) w = ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ toR v w := by
    rw [smul_lat, toR_mulVec, emb_val]
  have hPA : (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mat_rk, mat_actL, mat_actL, mat_rk, hv]
  set P := (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hP
  set A := ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hA
  have e1 : (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ toR v w) := by
    calc (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ ((P * A) *ᵥ toR v w)) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by rw [hPA, one_mulVec]
  rw [e1, star_mulVec, conjTranspose_conjTranspose, mul_vecMulVec, vecMulVec_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
private theorem zed_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : zed s (actL (emb L N γ) h) = zed s h := by
  unfold zed
  rw [← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
    (f := fun v => rho (q (actL (emb L N γ) h) v / s))]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
private theorem sum_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) :
    ∑ᶠ v : Lat L N, rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v =
      actL (emb L N γ) (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) := by
  rw [inj_finsum _ (act_inj γ),
    ← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
      (f := fun v => rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v)]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul, rk_act, map_smul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem term_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : term s (actL (emb L N γ) h) = actL (emb L N γ) (term s h) := by
  unfold term
  rw [zed_act hq, sum_act hq, map_smul]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private theorem ret_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (μ : HS L N → ℝ) (hμ : Smoothing lamD μ) (γ : Gm L N) {h : HS L N} (hh : h ∈ Pos L N) :
    ret μ (actL (emb L N γ) h) = actL (emb L N γ) (ret μ h) := by
  have hi : μ (actL (emb L N γ) h) = μ h := hμ.inv γ h hh
  unfold ret
  rw [hi, map_add, map_smul, inj_finsum _ (act_inj γ)]
  congr 1
  exact finsum_congr fun k => by rw [term_act hq, map_smul]

private def Psd (h : HS L N) : Prop := ∀ w, (mat h w).PosSemidef

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem psd_rk (h : HS L N) (v : Lat L N) : Psd (rk h v) := fun w => by
  rw [mat_rk]
  exact posSemidef_vecMulVec_self_star _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem psd_add {a b : HS L N} (ha : Psd a) (hb : Psd b) : Psd (a + b) := fun w => by
  rw [mat_add]; exact (ha w).add (hb w)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem psd_smul {a : HS L N} (ha : Psd a) {c : ℝ} (hc : 0 ≤ c) : Psd (c • a) := fun w => by
  rw [mat_smul]; exact (ha w).smul hc

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem psd_zero : Psd (0 : HS L N) := fun w => by
  rw [mat_zero]; exact PosSemidef.zero

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem psd_finsum {ι : Type} (g : ι → HS L N) (hg : ∀ i, Psd (g i)) : Psd (∑ᶠ i, g i) :=
  finsum_induction Psd psd_zero (fun _ _ => psd_add) hg

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem psd_term (s : ℝ) (h : HS L N) : Psd (term s h) := by
  unfold term
  refine psd_smul (psd_finsum _ fun v => psd_smul (psd_rk h v) (rho_nonneg _)) ?_
  exact inv_nonneg.2 (mul_nonneg (sq_nonneg s) (finsum_nonneg fun v => rho_nonneg _))

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem psd_qR {a : HS L N} (ha : Psd a) (z : VR L N) : 0 ≤ qR a z :=
  Finset.sum_nonneg fun w _ => (Complex.le_def.1 ((ha w).dotProduct_mulVec_nonneg (z w))).1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem pf_GREqv : GREqv := by
  intro hB L _ _ N hN μ hμ h hh
  have hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v) :=
    (hB L N hN).2.1
  obtain ⟨c, C, hc, hcmp⟩ := hμ.cmp
  have hD : 0 < lamD h := ((hB L N hN).1 _ ((hB L N hN).1 h hh).2.2.2.1).1
  have hμp : 0 < μ h := lt_of_lt_of_le (mul_pos hc hD) (hcmp h hh).1
  set S := ∑ᶠ k : ℤ, rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h with hSdef
  have hS : Psd S := psd_finsum _ fun k => psd_smul (psd_term _ _) (rho_nonneg _)
  have hr : ret μ h = μ h • h + S := rfl
  refine ⟨fun γ => ret_act hq μ hμ γ hh, fun w => ?_, fun z => ?_⟩
  · rw [hr, mat_add, mat_smul]
    exact ((hh w).smul hμp).add_posSemidef (hS w)
  · have e : qR (μ h • h + S) z = μ h * qR h z + qR S z := by
      simp only [← evR_apply, map_add, map_smul, smul_eq_mul]
    rw [hr, e]
    linarith [psd_qR hS z]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
