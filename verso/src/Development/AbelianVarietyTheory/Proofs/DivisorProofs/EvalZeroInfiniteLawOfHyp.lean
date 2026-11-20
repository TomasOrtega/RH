import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.EvZeroInf

noncomputable section

namespace GlobalTheory.ThK.LemF

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pure_smul_inf {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply]
  ring

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hAd hPair₁ e hev ei ev hloc g hg t h₁ m hL hm hh₁ u hu huI f`. Establish `hM` using `hPair.good`. Establish `hM₁` using `hPair₁.good`. Establish `hSB : ∀ v, M.vac v ∈ SB _` using `fun v => (hM.vac v).1`. Establish `hSB₁ : ∀ v, M₁.vac v ∈ SB _` using `fun v => (hM₁.vac v).1`.

Establish `hpure : ∀ f, pure f M.vac ∈ schA F _` using `fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std`. Establish `hpure₁ : ∀ f, pure f M₁.vac ∈ schA F _` using `fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB₁ hM₁.std`. Establish `hrest : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) (⇑f) (finPart M.vac)` using `fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure f⟩`. Establish `hrest₁ : ∀ f : SInf F (Fin n × Fin d₁), Rest (evI F) (⇑f) (finPart M₁.vac)` using `fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure₁ f⟩`. Establish `he : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac`.

Introduce `f`. Rewrite using `[hloc.2.2 f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl)]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hloc.2.1 v).1`.

Establish `hcancel : ∀ g g' : SInf F (Fin n × Fin d₁), pure g M₁.vac = pure g' M₁.vac → g = g'` using `eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std`. Establish `hx2 : u * m ∈ UAt σ W (evI F)` using `(UAtSub σ W (evI F)).mul_mem huI hm`. Take `⟨T, hT⟩` from `GlobalTheory.FockCompactW.exists_op_of_UAt hPair.base.std hPair.weil (g, u * m) hg hx2`. Take `⟨T₁, hT₁⟩` from `GlobalTheory.FockCompactW.exists_op_of_UAt hPair₁.base.std hPair₁.weil (g, h₁) hg hh₁`. Establish `hA : om (g, u * m) (pure f M.vac) = pure (locOpInf (om (g, u * m)) f) M.vac` using `acts_locOpInf ⟨T f, hT f⟩ _ (hrest f)`.

Establish `hA₁ : om₁ (g, h₁) (pure (ei f) M₁.vac) = pure (locOpInf (om₁ (g, h₁)) (ei f)) M₁.vac` using `acts_locOpInf ⟨T₁ (ei f), hT₁ (ei f)⟩ _ (hrest₁ (ei f))`. Establish `hK` using `GlobalTheory.T.adapted_plane_second_variable hP F E σ B n d X W M χX χW om r s r' s' hPair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hAd hPair₁ e hev g t h₁ m hL u hu (pure f M.vac) (hpure f)`. Apply `hcancel` to reduce the goal to its premises. Rewrite using `[pure_smul_inf, ← he, ← hA, hK, he, hA₁]`. Both sides reduce to the same expression.
-/
theorem evZeroInfLaw : GlobalTheory.FunPr.Hypotheses₂ → EvZeroInfLaw := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hAd hPair₁ e hev ei ev hloc
    g hg t h₁ m hL hm hh₁ u hu huI f
  have hM := hPair.good
  have hM₁ := hPair₁.good
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hSB₁ : ∀ v, M₁.vac v ∈ SB _ := fun v => (hM₁.vac v).1
  have hpure : ∀ f, pure f M.vac ∈ schA F _ := fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hpure₁ : ∀ f, pure f M₁.vac ∈ schA F _ := fun f => GlobalTheory.TensUniq.pure_mem_schA f _ hSB₁ hM₁.std
  have hrest : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) (⇑f) (finPart M.vac) :=
    fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure f⟩
  have hrest₁ : ∀ f : SInf F (Fin n × Fin d₁), Rest (evI F) (⇑f) (finPart M₁.vac) :=
    fun f => ⟨fun x z hz => finPart_add _ x z hz, hpure₁ f⟩
  have he : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac := by
    intro f
    rw [hloc.2.2 f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl)]
    congr 1
    funext v
    exact (hloc.2.1 v).1
  have hcancel : ∀ g g' : SInf F (Fin n × Fin d₁), pure g M₁.vac = pure g' M₁.vac → g = g' :=
    eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std
  have hx2 : u * m ∈ UAt σ W (evI F) := (UAtSub σ W (evI F)).mul_mem huI hm
  obtain ⟨T, hT⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hPair.base.std hPair.weil (g, u * m) hg hx2
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hPair₁.base.std hPair₁.weil (g, h₁) hg hh₁
  have hA : om (g, u * m) (pure f M.vac) = pure (locOpInf (om (g, u * m)) f) M.vac :=
    acts_locOpInf ⟨T f, hT f⟩ _ (hrest f)
  have hA₁ : om₁ (g, h₁) (pure (ei f) M₁.vac) = pure (locOpInf (om₁ (g, h₁)) (ei f)) M₁.vac :=
    acts_locOpInf ⟨T₁ (ei f), hT₁ (ei f)⟩ _ (hrest₁ (ei f))
  have hK := GlobalTheory.T.adapted_plane_second_variable hP F E σ B n d X W M χX χW om r s r' s' hPair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hAd hPair₁ e hev
    g t h₁ m hL u hu (pure f M.vac) (hpure f)
  apply hcancel
  rw [pure_smul_inf, ← he, ← hA, hK, he, hA₁]
  rfl

end GlobalTheory.ThK.LemF

end
