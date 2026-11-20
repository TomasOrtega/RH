import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.EtaSignReal
open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB η hη a ha`. Establish `hcm` using `hB.cm`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩`. Use `haveI := hcm.1`. Rewrite using `[eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]`.

Rewrite using `[show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) = ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from map_prod Circle.coeHom _ _]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`. Rewrite using `[piInf_idFF hw]`. Use `set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)`.

Establish `hx` using `mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)`. Establish `hr0 : r ≠ 0` using `(map_ne_zero _).2 (infComp a w).ne_zero`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Distinguish the cases in `hpos : 0 < r`. Rewrite using `[eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]`.

Both sides reduce to the same expression. Establish `hneg : r < 0` using `lt_of_le_of_ne (not_lt.1 hpos) hr0`. Rewrite using `[eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]`. Express the relevant statement in the definitionally equal form `((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _`. Rewrite using `[if_neg (by decide)]`.

Use `push_cast`. Rewrite using `[div_neg, div_self (by exact_mod_cast hr0)]`.
-/
theorem eta_eq_prod_sign_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
end GlobalTheory.EtaSignReal
end
end
