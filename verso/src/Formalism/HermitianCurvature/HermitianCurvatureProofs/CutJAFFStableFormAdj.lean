import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjIntCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.FormalDegreeBessel.FinalG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `x hx`. Use `show h x = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hx (subset_tsupport _ hne)`. Consider the case `cons X w ih`. Introduce `x hx`. Use `show RdV X (B.Rw w h) x = 0`.

Establish `hO : IsOpen (tsupport h)ᶜ` using `(isClosed_tsupport h).isOpen_compl`. Establish `hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X))` using `(Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous`. Establish `h0 : (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ (tsupport h)ᶜ` using `by show x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ _`. Rewrite using `[Formalism.FourierDecayAlt.P.B5.curve_zero]`. Conclude with `hx`.

Establish `hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ (tsupport h)ᶜ` using `hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)`. Establish `heq : (fun t : ℝ => B.Rw w h (x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => (0 : E)` using `hev.mono fun t ht => ih _ ht`. Unfold `RdV`. Rewrite using `[heq.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem rw_eq_zero_of_not_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : B.Mat k r → E) :
    ∀ (w : List (B.Mat k r)) (x : B.Mat k r), x ∉ tsupport h → B.Rw w h x = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx
    show h x = 0
    by_contra hne
    exact hx (subset_tsupport _ hne)
  | cons X w ih =>
    intro x hx
    show RdV X (B.Rw w h) x = 0
    have hO : IsOpen (tsupport h)ᶜ := (isClosed_tsupport h).isOpen_compl
    have hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous
    have h0 : (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ (tsupport h)ᶜ := by
      show x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ _
      rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
      exact hx
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ (tsupport h)ᶜ :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have heq : (fun t : ℝ => B.Rw w h (x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => (0 : E) :=
      hev.mono fun t ht => ih _ ht
    unfold RdV
    rw [heq.deriv_eq]
    simp

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts μ` using `⟨hμ.finite_compact⟩`. Establish `hu : ContinuousOn (fun x => ‖A x‖ * ‖C x‖) (B.GV k r)` using `(continuous_norm.comp_continuousOn hA).mul (continuous_norm.comp_continuousOn hC)`. Establish `hKG : IsCompact (K ∩ B.GV k r)` using `hK.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed`. Take `⟨M, hM⟩` from `hKG.exists_bound_of_continuousOn (hu.mono Set.inter_subset_right)`. Establish `hmeas : AEStronglyMeasurable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ`.

Establish `h1` using `Formalism.FourierDecayAlt.P.B5.aesm_of_continuousOn hμ (f := fun x => ((‖A x‖ * ‖C x‖ : ℝ) : ℂ)) (Complex.continuous_ofReal.comp_continuousOn hu)`. Conclude with `(Complex.continuous_re.comp_aestronglyMeasurable h1).congr (Eventually.of_forall fun g => by simp)`. Establish `hKm : IsCompact (Matrix.of ⁻¹' K : Set (Mt k r))` using `hK`. Use `Integrable.mono' ((integrableOn_const hKm.measure_lt_top.ne).integrable_indicator hKm.isClosed.measurableSet) hmeas ?_` and prove the remaining obligations. Use `filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with g hg`.

Distinguish the cases in `hgK : Matrix.of g ∈ K`. Establish `hg' : g ∈ (Matrix.of ⁻¹' K : Set (Mt k r))` using `hgK`. Rewrite using `[Set.indicator_of_mem hg']`. Conclude with `hM _ ⟨hgK, hg⟩`. Establish `hg' : g ∉ (Matrix.of ⁻¹' K : Set (Mt k r))` using `hgK`.

Simplify using `only [Set.indicator, hg', if_false, hAz _ hgK, norm_zero, zero_mul, le_refl]`.
-/
theorem integrable_nn {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    {A : B.Mat k r → E₁} {C : B.Mat k r → E₂} (hA : ContinuousOn A (B.GV k r)) (hC : ContinuousOn C (B.GV k r))
    {K : Set (B.Mat k r)} (hK : IsCompact K) (hAz : ∀ x, x ∉ K → A x = 0) :
    Integrable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hu : ContinuousOn (fun x => ‖A x‖ * ‖C x‖) (B.GV k r) :=
    (continuous_norm.comp_continuousOn hA).mul (continuous_norm.comp_continuousOn hC)
  have hKG : IsCompact (K ∩ B.GV k r) := hK.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  obtain ⟨M, hM⟩ := hKG.exists_bound_of_continuousOn (hu.mono Set.inter_subset_right)
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => ‖A (Matrix.of g)‖ * ‖C (Matrix.of g)‖) μ := by
    have h1 := Formalism.FourierDecayAlt.P.B5.aesm_of_continuousOn hμ (f := fun x => ((‖A x‖ * ‖C x‖ : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn hu)
    exact (Complex.continuous_re.comp_aestronglyMeasurable h1).congr (Eventually.of_forall fun g => by simp)
  have hKm : IsCompact (Matrix.of ⁻¹' K : Set (Mt k r)) := hK
  refine Integrable.mono' ((integrableOn_const hKm.measure_lt_top.ne).integrable_indicator
    hKm.isClosed.measurableSet) hmeas ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with g hg
  by_cases hgK : Matrix.of g ∈ K
  · have hg' : g ∈ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    rw [Set.indicator_of_mem hg']
    exact hM _ ⟨hgK, hg⟩
  · have hg' : g ∉ (Matrix.of ⁻¹' K : Set (Mt k r)) := hgK
    simp only [Set.indicator, hg', if_false, hAz _ hgK, norm_zero, zero_mul, le_refl]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D Θ hs hc F F' hF hFc hFs hF' hF'c hF's`. Establish `e1 : (Matrix.of (Matrix.of.symm (1 : B.Mat k r)) : B.Mat k r) = 1` using `Equiv.apply_symm_apply _ _`. Establish `hp0 : D.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1))`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1]`. Conclude with `Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z`.

Conclude with `(Formalism.QuantumDeterminants.nSubgroup k r).1`. Conclude with `Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'`. Conclude with `(Formalism.QuantumDeterminants.nSubgroup k r).1`. Establish `hrho : ∀ A : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) A = A`. Introduce `A`.

Use function extensionality and compare the values at `g`. Simplify using `only [B.rho, B.sgs, e1, inv_one, mul_one, one_mul, D.π_rep.1, D.π'_rep.1]`. Use extensionality with `v`. Simplify using the standard rewrite rules. Establish `hI : B.IntClause D Θ F F'`.

Introduce `p hp T hT i j _ _`. Establish `hcA : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (F' x))` using `Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF' hF's`. Establish `hK : IsCompact (tsupport (fun x => T.coefAdj x (F' x)))` using `IsCompact.of_isClosed_subset hF'c (isClosed_tsupport _) (closure_mono fun x hx h0 => hx (by show T.coefAdj x (F' x) = 0; rw [h0, map_zero]))`. Conclude with `integrable_nn D.haarG (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' hcA _ fun X hX => T.word_lie X (List.mem_of_mem_take (List.mem_reverse.1 hX)))) (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JF …`. Establish `key` using `Formalism.FourierDecayAlt.P.phase_function_adjoint k r Wp Wq D (B.GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hs hc F F' (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF') hFs hF's hI _ hp0`.

Unfold `B.Ph at key`. Rewrite `key` using `[hrho, hrho]`. Then use the resulting hypothesis.
-/
theorem form_adjoint_holds : FormAdj := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc F F' hF hFc hFs hF' hF'c hF's
  have e1 : (Matrix.of (Matrix.of.symm (1 : B.Mat k r)) : B.Mat k r) = 1 := Equiv.apply_symm_apply _ _
  have hp0 : D.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1]
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
    · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
    · exact (Formalism.QuantumDeterminants.nSubgroup k r).1
  have hrho : ∀ A : B.Mat k r → (Wq →L[ℂ] Wp),
      B.rho D ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm 1)) A = A := by
    intro A
    funext g
    simp only [B.rho, B.sgs, e1, inv_one, mul_one, one_mul, D.π_rep.1, D.π'_rep.1]
    ext v
    simp
  have hI : B.IntClause D Θ F F' := by
    intro p hp T hT i j _ _
    have hcA : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (F' x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF' hF's
    have hK : IsCompact (tsupport (fun x => T.coefAdj x (F' x))) :=
      IsCompact.of_isClosed_subset hF'c (isClosed_tsupport _)
        (closure_mono fun x hx h0 => hx (by show T.coefAdj x (F' x) = 0; rw [h0, map_zero]))
    exact integrable_nn D.haarG
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' hcA _ fun X hX =>
        T.word_lie X (List.mem_of_mem_take (List.mem_reverse.1 hX))))
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _
        fun X hX => T.word_lie X (List.mem_of_mem_drop hX)))
      hK (fun x hx => rw_eq_zero_of_not_mem _ _ x hx)
  have key := Formalism.FourierDecayAlt.P.phase_function_adjoint k r Wp Wq D (B.GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hs hc F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF') hFs hF's hI _ hp0
  unfold B.Ph at key
  rwa [hrho, hrho] at key

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
