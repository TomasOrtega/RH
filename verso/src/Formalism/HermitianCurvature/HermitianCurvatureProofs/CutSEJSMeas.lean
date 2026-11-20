import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MeasJ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapS (l : Fin r) (c : Fin r → ℂ) (q : (ℂ × Cf r l.succ) × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue l.succ (Function.update c l q.1.1) q.1.2, Matrix.of q.2)

/- English proof (translation)
Unfold `glueMapS`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Use `continuous_pi fun m => ?_` and prove the remaining obligations. Distinguish the cases in `h : (l.succ : Fin (r + 1)).val ≤ m.val`. Simplify using `only [glue, h, dif_pos]`.

Conclude with `(continuous_apply _).comp (continuous_snd.comp continuous_fst)`. Simplify using `only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]`. Distinguish the cases in `hm : m = l`. Apply the tactic sequence `simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop`. Apply the tactic sequence `simp only [hm, if_false, ite_false] <;> fun_prop`.

Conclude with `continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop`.
-/
theorem glueMapS_continuous (l : Fin r) (c : Fin r → ℂ) : Continuous (glueMapS (k := k) l c) := by
  unfold glueMapS
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun m => ?_
    by_cases h : (l.succ : Fin (r + 1)).val ≤ m.val
    · simp only [glue, h, dif_pos]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · simp only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]
      by_cases hm : m = l
      · simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop
      · simp only [hm, if_false, ite_false] <;> fun_prop
  · exact continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop

/- English proof (translation)
Rewrite using `[DomR_eq, Set.preimage_inter]`. Conclude with `((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (glueMapS_continuous l c)).measurableSet`.
-/
theorem measurableSet_glueMapS_DomR (l : Fin r) (c : Fin r → ℂ) :
    MeasurableSet (glueMapS (k := k) l c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapS_continuous l c)).measurableSet

end MeasJ

/- English proof (translation)
Introduce `k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ`. Establish `hmaps : Set.MapsTo (glueMapS (k` using `k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') := fun q hq => hq`. Establish `hΦc` using `(radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps`. Establish `hΨc` using `(radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps`. Use `measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c) ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_` and prove the remaining obligations.

Introduce `q hq`. Establish `h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0` using `radSp_zero_off Φ hq`. Use `show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0`. Rewrite using `[h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]`. Simplify using the standard rewrite rules.
-/
theorem spectral_measurability : JSMeas := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ
  have hmaps : Set.MapsTo (glueMapS (k := k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0 :=
    radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Formalism.FourierDecayAlt.P.CutSE
