import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HasOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocDataT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OpOpOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Introduce `hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q`. Use `⟨2 * n.factorial, ?_⟩` and prove the remaining obligations. Introduce `N`. Establish `hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal`. Introduce `j hj`.

Apply `Q.v_not N j` to reduce the goal to its premises. Use `left`. Establish `h1` using `(Q.B_w N j (l : 𝓞 L)).2 hj`. Use `(Q.B_v N j (l : 𝓞 (Lp L))).1 ?_` and prove the remaining obligations. Simplify using `using h1`.

Take `⟨A, ι, hι⟩` from `hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N) (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)`. Establish `hd` using `fun j => _root_.UpperTheory.V.Z.Win.locDataT_alt hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j) (Q.fr_frob N j) (Q.τ_gen N j)`. Use `choose hq x δ hx hδ hrel using hd`. Establish `hNq : T.Nq N = qj (Q.w N)` using `funext fun j => (Q.Nq N j).trans (hq j).symm`. Establish `hok : _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j))` using `⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩`.

Take `⟨A1, h1⟩` from `_root_.UpperTheory.V.Th.opOfX_alt hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok (fun j => by rw [← hNq]; exact T.Nq_mod N j)`. Take `⟨A2, h2⟩` from `opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1`. Establish `e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j))` using `funext (Q.ph N)`. Establish `e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j))` using `funext (Q.ta N)`. Rewrite using `[hNq, e1, e2]`.

Conclude with `⟨A2, h2⟩`.
-/
theorem UpperTheory.V.Th.has_operator_statement :
    _root_.UpperTheory.V.Th.HasHeckeOperatorDense := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q
  refine ⟨2 * n.factorial, ?_⟩
  · skip
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => _root_.UpperTheory.V.Z.Win.locDataT_alt hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := _root_.UpperTheory.V.Th.opOfX_alt hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact ⟨A2, h2⟩
end
