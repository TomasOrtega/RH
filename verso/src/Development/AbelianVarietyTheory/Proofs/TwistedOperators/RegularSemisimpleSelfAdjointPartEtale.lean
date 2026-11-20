import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ hreg hA hbij`. Establish `: Nontrivial E` using `quad_nontrivial hreg.quad`. Establish `: Module.Finite F E` using `quad_finite hreg.quad`. Take `⟨b⟩` from `hA.2.2.1`. Establish `: Module.Free E (genAlg (γ : Matrix n n E))` using `Module.Free.of_basis b`.

Establish `: Module.Finite E (genAlg (γ : Matrix n n E))` using `Module.Finite.of_basis b`. Establish `: Module.Finite F (genAlg (γ : Matrix n n E))` using `Module.Finite.trans E _`. Establish `: Module.Finite F (plusAlg σ J (γ : Matrix n n E))` using `Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap Subtype.val_injective`. Establish `: IsReduced (genAlg (γ : Matrix n n E))` using `genAlg_isReduced hreg hA`. Establish `: IsReduced (plusAlg σ J (γ : Matrix n n E))` using `isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective`.

Use `⟨etale_of_isReduced _, ?_, hbij⟩` and prove the remaining obligations. Establish `hdim` using `(AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq`. Rewrite `hdim` using `[Module.finrank_tensorProduct, hreg.quad.finrank_eq, ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b]`. Establish `hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n` using `by omega`. Conclude with `⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩`.
-/
theorem plusEtale : PlusEtale := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hA hbij
  have : Nontrivial E := quad_nontrivial hreg.quad
  have : Module.Finite F E := quad_finite hreg.quad
  obtain ⟨b⟩ := hA.2.2.1
  have : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  have : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  have : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) :=
    Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap
      Subtype.val_injective
  have : IsReduced (genAlg (γ : Matrix n n E)) := genAlg_isReduced hreg hA
  have : IsReduced (plusAlg σ J (γ : Matrix n n E)) :=
    isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective
  refine ⟨etale_of_isReduced _, ?_, hbij⟩
  have hdim := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hreg.quad.finrank_eq,
    ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b] at hdim
  have hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n := by omega
  exact ⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩

end GlobalTheory.RegSS
