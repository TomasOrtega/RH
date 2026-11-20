import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma weight_add_shift {e k : ℕ} {w' : WeightFamilies.Wt D j} (hw : wadd wF w' = wsmul e wL) :
    wadd (addL wF wL k) w' = addL (wt0 D j) wL (k + e) := by
  have h1 := congrArg WeightFamilies.Wt.aP hw
  have h2 := congrArg WeightFamilies.Wt.aM hw
  have h3 := congrArg WeightFamilies.Wt.n hw
  simp only [wadd, wsmul] at h1 h2 h3
  unfold addL wadd wsmul wt0 wscalar
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i
    have := congrFun (congrFun h1 τ) i
    linarith
  · funext τ i
    have := congrFun (congrFun h2 τ) i
    linarith
  · linarith

variable (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma product_cusp_forms_mem_weight {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ) ∈
      Vw (xplus X E hM) la G.N (addL (wt0 D j) wL e) := by
  have := mul_mem_Vw (xplus X E hM) la G.N (emb_mem_Vw (xplus X E hM) la G.N wF g0)
    (emb_mem_Vw (xplus X E hM) la G.N w' θ)
  have hw' : addL (wt0 D j) wL e = wadd wF w' := by rw [hw]; exact zero_weight_add _
  rw [hw']
  exact this

def u0 {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w e (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ)),
    Algebra.subset_adjoin (frac_mem_Hfr _ _ _ (product_cusp_forms_mem_weight G la g0 θ hw))⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma top_span_mem {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    (⟨z, Algebra.mem_top⟩ : ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ :
          ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)))) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Ideal.subset_span ⟨i, rfl⟩
  | zero => exact Ideal.zero_mem _
  | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
  | smul a b _ hb =>
    have : (⟨a • b, Algebra.mem_top⟩ :
        ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) =
        ⟨a, Algebra.mem_top⟩ * ⟨b, Algebra.mem_top⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hb

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem curveModel_of_fr
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w))
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hu0 : IsUnit (toOsK (xplus X E hM) la G.w (u0 G la g0 θ hw)))
    (hinj : ∀ b : ↥(Frac0 (xplus X E hM) la G.w),
      (b : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 →
        b = 0) :
    Nonempty (CurveModel G la g0) := by
  obtain ⟨v, hv⟩ := hu0
  obtain ⟨c, hc⟩ := toOsK_surjective (xplus X E hM) la G.w (↑v⁻¹)
  set A : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w) := ⊤ with hA
  have hJh : c * u0 G la g0 θ hw - 1 ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_mul, map_one, hc, ← hv, Units.inv_mul, sub_self]

  have hspan : Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ : ↥A)) =
      (Jid (xplus X E hM) la G.w).map (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N)).symm := by
    rw [Jid, Ideal.map_span, ← Set.range_comp]
    rfl
  let qe := Ideal.quotientEquivAlg (R₁ := Kp (xplus X E hM) la G.N) (Jid (xplus X E hM) la G.w) _
    (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N) (A := ↥(Frac0 (xplus X E hM) la G.w))).symm hspan
  have hfd' : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) :=
    hfd
  have hred' : IsReduced (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) := hred
  refine ⟨{ A' := A
            sA := fun _ => Algebra.mem_top
            h := ⟨c * u0 G la g0 θ hw, Algebra.mem_top⟩
            h_one := ?_
            fin := ?_
            red := ?_
            loc := fun b => ⟨0, ⟨b, Algebra.mem_top⟩, by rw [pow_zero, one_mul]⟩
            base_form_injective := ?_
            base_form_local := ?_ }⟩
  · have := top_span_mem G la hJh
    convert this using 1
    exact Subtype.ext (by simp)
  · exact LinearEquiv.finiteDimensional qe.toLinearEquiv
  · exact isReduced_of_injective qe.symm.toRingEquiv.toRingHom qe.symm.injective
  · intro a₁ a₂ h12
    apply Subtype.ext
    have h0 : (((a₁ : ↥(Frac0 (xplus X E hM) la G.w)) - (a₂ : ↥(Frac0 (xplus X E hM) la G.w)) :
        ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
          (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 := by
      rw [Subalgebra.coe_sub, sub_mul, sub_eq_zero]
      exact h12
    exact sub_eq_zero.1 (hinj _ h0)
  · intro x
    obtain ⟨k, g, hg, hx⟩ := (mem_Hfr (xplus X E hM) la G.w).1 ((mem_HK (xplus X E hM) la G.w).1 x.2)
    have hgθ : g * emb (xplus X E hM) la G.N (X.inc w' θ) ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL (k + e)) := by
      rw [← weight_add_shift (k := k) hw]
      exact mul_mem_Vw _ _ _ hg (emb_mem_Vw _ _ _ w' θ)
    let b : ↥(Frac0 (xplus X E hM) la G.w) :=
      ⟨frac (xplus X E hM) la G.w (k + e) (g * emb (xplus X E hM) la G.N (X.inc w' θ)),
        Algebra.subset_adjoin (frac_mem_Hfr _ _ _ hgθ)⟩
    refine ⟨1, ⟨c * b, Algebra.mem_top⟩, ?_⟩
    show ((c * u0 G la g0 θ hw : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ 1 *
        (x : Lw (xplus X E hM) la G.w) =
      ((c * b : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0))
    rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_mul, hx, ← frac_zero, mul_assoc, mul_assoc]
    congr 1
    show frac _ _ _ e _ * frac _ _ _ k g = frac _ _ _ (k + e) _ * frac _ _ _ 0 _
    rw [frac_mul, frac_mul, add_zero, add_comm e k]
    congr 1
    ring

end Formalism.L2.Pj
