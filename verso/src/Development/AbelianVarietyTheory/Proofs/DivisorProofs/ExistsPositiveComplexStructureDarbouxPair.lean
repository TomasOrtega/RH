import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSympNegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositiveStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockPair

open GlobalTheory.GaussFockJ

def tensC {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)

/- English proof (translation)
Simplify using `[tensC]`.
-/
theorem tensC_zero_left {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (y : Matrix (Fin n) (Fin d) ℂ) :
    tensC JX JW 0 y = 0 := by
  simp [tensC]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite using `[M.co.form u v, ← evIHom_apply, map_sub, map_sub]`. Simplify using `only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]`.
-/
theorem pair_Psi {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M u).1 (Psi M v).2 -
                 GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M v).1 (Psi M u).2 =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u v)) := by
  rw [M.co.form u v, ← evIHom_apply, map_sub, map_sub]
  simp only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP`. Establish `hcm` using `hP.base.cm`. Use `choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) => exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))`. Establish `hRadd : ∀ u v, R (u + v) = R u + R v`. Introduce `u v`.

Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]`. Simplify using `only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]`. Establish `hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u`. Introduce `c u`.

Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, map_smul_piInf, map_smul_piInf, hRmap]`. Simplify using `only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]`. Establish `hRR : ∀ u, At (evI F) u → R (R u) = -u`. Introduce `u hu`.

Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, Matrix.map_neg _ (map_neg _), hRmap]`. Establish `hV` using `(hP.herm.cartan w).1`. Establish `hW` using `(hP.skew.cartan w).1`. Establish `hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]`.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]`. Establish `hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j`. Introduce `w i j`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]`.

Establish `hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j`. Introduce `w i j`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]`. Establish `hloc` using `fun w => GlobalTheory.T.tensorCartanInvolution_invariant_and_positive n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w) (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)`. Establish `key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E), Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a b)) = ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w))) (b.map (piInf (B.emb w)))).re := by`.

Introduce `a b`. Rewrite using `[GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b]`. Both sides reduce to the same expression. Establish `hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w))) ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w))) (b.map (piInf (B.emb w)))`. Introduce `a b w`.

Rewrite using `[hRmap, hRmap]`. Conclude with `(hloc w _ _).1`. Establish `hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re`. Introduce `a w ha`. Rewrite using `[hRmap]`.

Conclude with `(hloc w _ (a.map (piInf (B.emb w)))).2 ha`. Set `J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `fun w => Psi M (R (Phi M w))`. Establish `hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v`. Introduce `t v hv`. Rewrite using `[← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]`.

Set `J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `{ toFun := J map_add' := fun w w' => by show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))`. Rewrite using `[Phi_add, hRadd, Psi_add]`. Use the proof step `map_smul' := fun t w => by show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))`. Rewrite using `[Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }`. Establish `hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0`.

Establish `h` using `Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0`. Rewrite `h` using `[add_zero]`. Conclude with `add_left_cancel (h.symm.trans (add_zero _).symm)`. Use `⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩` and prove the remaining obligations. Use `show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w`.

Rewrite using `[Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]`. Use `show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _ conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']`. Rewrite using `[pair_Psi, pair_Psi, key, key]`. Conclude with `Finset.sum_congr rfl fun v _ => by rw [hinv]`. Establish `hw'` using `Psi_Phi M w`.

Establish `hat` using `at_Phi M w`. Use `show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2`. Generalize the expression as in `Phi M w = a at hw' hat ⊢`. Substitute `hw'` using the available equality. Rewrite using `[pair_Psi, key]`.

Establish `hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `ha0 : a = 0` using `eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c) fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]`. Conclude with `hw (by rw [ha0, hPsi0])`.

Take `⟨v, hv⟩` from `hex`. Use `Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩` and prove the remaining obligations. Distinguish the cases in `h0 : a.map (piInf (B.emb v')) = 0`. Rewrite using `[h0, tensC_zero_left, Complex.zero_re, mul_zero]`. Use `hpos a v' h0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Express the relevant statement in the definitionally equal form `Psi M u' = Psi M (R (Phi M (Psi M u)))`. Rewrite using `[Phi_Psi M hu]`. Use `congr 1`. Conclude with `eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]`.
-/
theorem exists_pos_complex_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) =>
    exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, map_smul_piInf, hRmap]
    simp only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _), hRmap]
    have hV := (hP.herm.cartan w).1
    have hW := (hP.skew.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]

  have hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]
  have hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]
  have hloc := fun w => GlobalTheory.T.tensorCartanInvolution_invariant_and_positive n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w)
    (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)
  have key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a b)) =
        ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
          (b.map (piInf (B.emb w)))).re := by
    intro a b
    rw [GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b]
    rfl
  have hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w)))
      ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
      (b.map (piInf (B.emb w))) := by
    intro a b w
    rw [hRmap, hRmap]
    exact (hloc w _ _).1
  have hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re := by
    intro a w ha
    rw [hRmap]
    exact (hloc w _ (a.map (piInf (B.emb w)))).2 ha
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  have hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0 := by
    have h := Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _
    conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']
    rw [pair_Psi, pair_Psi, key, key]
    exact Finset.sum_congr rfl fun v _ => by rw [hinv]
  · have hw' := Psi_Phi M w
    have hat := at_Phi M w
    show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2
    generalize Phi M w = a at hw' hat ⊢
    subst hw'
    rw [pair_Psi, key]
    have hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c)
        fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]
      exact hw (by rw [ha0, hPsi0])
    obtain ⟨v, hv⟩ := hex
    refine Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩
    by_cases h0 : a.map (piInf (B.emb v')) = 0
    · rw [h0, tensC_zero_left, Complex.zero_re, mul_zero]
    · have := hpos a v' h0; linarith
  · change Psi M u' = Psi M (R (Phi M (Psi M u)))
    rw [Phi_Psi M hu]
    congr 1
    exact eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]

end GlobalTheory.GaussFockPair
