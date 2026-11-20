import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspOfReading

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T h j hj w hw hn f hf hfh`. Use `set S := T.cuspA j (wtA w) w.n with hS`. Use `haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)`. Use `haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _`. Set `b` to `Module.finBasis T.Q.c.F S`.

Set `b' : Fin (Module.finrank T.Q.c.F S) → T.R j` to `fun i => (b i : T.R j)`. Establish `hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(b i).2`.

Establish `hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b')`. Introduce `x hx`. Establish `h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b)` using `by rw [b.span_eq]; trivial`. Establish `h2` using `Submodule.mem_map_of_mem (f := S.subtype) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`.

Conclude with `h2`. Assume the negation of the conclusion as `hfS`. Establish `hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j)`. Rewrite using `[linearIndependent_fin_cons]`. Conclude with `⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩`.

Establish `hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n`. Introduce `i`. Use `Fin.cases hf (fun i => ?_) i` and prove the remaining obligations. Conclude with `cusp_le_sec _ _ _ _ _ (b i).2`. Establish `hC` using `GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli`.

Establish `hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) : Fin (Module.finrank T.Q.c.F S + 1) → _)`. Use `hC using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `Fin.cases rfl (fun i => rfl) i` and prove the remaining obligations. Rewrite `hC'` using `[linearIndependent_fin_cons]`.

Apply `hC'.2` to reduce the goal to its premises. Establish `hspan` using `GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh`. Use `(Submodule.span_le.2 ?_) hspan` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx'` using `hSb' hx`.

Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨i, rfl⟩ := hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul a y _ hy => rw [map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw hn f hf hfh
  classical
  set S := T.cuspA j (wtA w) w.n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  let b' : Fin (Module.finrank T.Q.c.F S) → T.R j := fun i => (b i : T.R j)
  have hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b i).2
  have hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b') := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := S.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  by_contra hfS
  have hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) := by
    rw [linearIndependent_fin_cons]
    exact ⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩
  have hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := by
    intro i
    refine Fin.cases hf (fun i => ?_) i
    exact cusp_le_sec _ _ _ _ _ (b i).2
  have hC := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli
  have hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) :
      Fin (Module.finrank T.Q.c.F S + 1) → _) := by
    convert hC using 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  rw [linearIndependent_fin_cons] at hC'
  apply hC'.2
  have hspan := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hSb' hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.CuspOfReading
