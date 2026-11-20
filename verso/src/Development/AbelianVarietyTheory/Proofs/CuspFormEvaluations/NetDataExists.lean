import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetDataFromHalfConjugateEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsScalarEvaluationsCuspFormsFiniteNetStatement
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn.NetAtRecord

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Establish `e : (starRingEnd ℂ) H.rt0 = H.rt0`. Establish `h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0` using `h1`. Rewrite `h3` using `[show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2]`. Then use the resulting hypothesis.

Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.mp e`. Establish `hre` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Simplify using `only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.

Introduce `h`. Use `goodEmb_goodOf c σ` as an intermediate fact. Unfold `goodOf at this`. Rewrite `this` using `[if_neg h]`. Then use the resulting hypothesis.
-/
theorem good_conj_iff (c : Coeff l) (σ : c.F →+* ℂ) :
    GoodEmb c (ComplexEmbedding.conjugate σ) ↔ ¬ GoodEmb c σ := by
  constructor
  · intro h1 h2
    have e : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h1
      rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2] at h3
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp e
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  · intro h
    have := goodEmb_goodOf c σ
    unfold goodOf at this
    rwa [if_neg h] at this

/- English proof (translation)
Unfold `goodOf`. Distinguish the cases in `h : GoodEmb c σ`. Rewrite using `[if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate]`.

Rewrite using `[if_pos ((good_conj_iff c σ).2 h), if_neg h]`. Both sides reduce to the same expression.
-/
theorem goodOf_conj (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (ComplexEmbedding.conjugate σ) = goodOf c σ := by
  unfold goodOf
  by_cases h : GoodEmb c σ
  · rw [if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]
    ext x; simp [ComplexEmbedding.conjugate]
  · rw [if_pos ((good_conj_iff c σ).2 h), if_neg h]; rfl

end

/- English proof (translation)
Establish `e : T.Ns j w (ComplexEmbedding.conjugate σ) = T.Ns j w σ`. Use function extensionality and compare the values at `f`. Unfold `Core.Ns`. Rewrite using `[goodOf_conj]`. Express the relevant statement in the definitionally equal form `cutN T.C T.Ns j w (ComplexEmbedding.conjugate σ) F = cutN T.C T.Ns j w σ F`.

Unfold `cutN`. Rewrite using `[e]`.
-/
theorem supN_conj {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (F : (recB h.toLawsCore).Cusp j w) :
    (recB h.toLawsCore).supN j w (ComplexEmbedding.conjugate σ) F = (recB h.toLawsCore).supN j w σ F := by
  have e : T.Ns j w (ComplexEmbedding.conjugate σ) = T.Ns j w σ := by
    funext f
    unfold Core.Ns
    rw [goodOf_conj]
  change cutN T.C T.Ns j w (ComplexEmbedding.conjugate σ) F = cutN T.C T.Ns j w σ F
  unfold cutN
  rw [e]

/- English proof (translation)
Introduce `D T h hG large₂ j hj w hP hL hr hf`. Establish `key` using `GlobalTheory.T.exists_scalar_evaluations_cusp_forms_finite_net D T h hG large₂ j hj w hP hL hr hf`. Establish `key2 : ∀ σ : T.Q.c.F →+* ℂ, ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), GoodEmb T.Q.c σ → (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ …`. Introduce `σ`. Distinguish the cases in `hσ : GoodEmb T.Q.c σ`.

Take `⟨n, ev, H⟩` from `key σ hσ`. Conclude with `⟨n, ev, fun _ => H⟩`. Conclude with `⟨0, Fin.elim0, fun h' => absurd h' hσ⟩`. Use `choose n ev H using key2`. Conclude with `GlobalTheory.T.exists_netData_from_half_conjugate_embeddings D (recB h.toLawsCore) j w (GoodEmb T.Q.c) (fun σ => by rw [good_conj_iff]; exact not_not.symm) (supN_conj h j w) n ev _ H`.
-/
theorem netData_exists : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∃ Nt : NetData (recB h.toLawsCore) j w, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt (1041 * Zb D large₂ ^ 3) ∧ ∀ σ, NetInj Nt σ := by
  intro D T h hG large₂ j hj w hP hL hr hf
  classical
  have key := GlobalTheory.T.exists_scalar_evaluations_cusp_forms_finite_net D T h hG large₂ j hj w hP hL hr hf
  have key2 : ∀ σ : T.Q.c.F →+* ℂ, ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)),
      GoodEmb T.Q.c σ → (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧
        (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧
        ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F →
          LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
    intro σ
    by_cases hσ : GoodEmb T.Q.c σ
    · obtain ⟨n, ev, H⟩ := key σ hσ
      exact ⟨n, ev, fun _ => H⟩
    · exact ⟨0, Fin.elim0, fun h' => absurd h' hσ⟩
  choose n ev H using key2
  exact GlobalTheory.T.exists_netData_from_half_conjugate_embeddings D (recB h.toLawsCore) j w (GoodEmb T.Q.c)
    (fun σ => by rw [good_conj_iff]; exact not_not.symm) (supN_conj h j w) n ev _ H

end GlobalTheory.RunIn.NetAtRecord
