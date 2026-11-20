import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnitaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosureStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.BackForm

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

/- English proof (translation)
Use function extensionality and compare the values at `ρ`. Distinguish the cases in `h : ρ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem coe_update (y : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun ρ => ((Function.update y τ w ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (y ρ : M.H ρ)) τ (w : M.H τ) := by
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨y, rfl⟩`. Consider the case `cons p l ih`. Take `⟨y', h⟩` from `ih fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Establish `hp` using `hl p List.mem_cons_self`.

Conclude with `⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩`.
-/
theorem word_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
  induction l with
  | nil => exact ⟨y, rfl⟩
  | cons p l ih =>
    obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.SmoothAutCheck.parts_mem V τ Z`. Use `⟨⟨_, hsm τ _ h1 w⟩ + Complex.I • ⟨_, hsm τ _ h2 w⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[T.map_update_add, T.map_update_smul, RderC, hT (Function.update y τ w) τ _ h1 ⟨_, hsm τ _ h1 w⟩ (by simp), hT (Function.update y τ w) τ _ h2 ⟨_, hsm τ _ h2 w⟩ (by simp), Function.update_idem, Function.update_idem]`.
-/
theorem rderC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z w ∧
      RderC θ V τ Z (T (Function.update y τ w)) = T (Function.update y τ w') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨⟨_, hsm τ _ h1 w⟩ + Complex.I • ⟨_, hsm τ _ h2 w⟩, rfl, ?_⟩
  rw [T.map_update_add, T.map_update_smul, RderC,
    hT (Function.update y τ w) τ _ h1 ⟨_, hsm τ _ h1 w⟩ (by simp),
    hT (Function.update y τ w) τ _ h2 ⟨_, hsm τ _ h2 w⟩ (by simp), Function.update_idem, Function.update_idem]

/- English proof (translation)
Proceed by induction on `Zs with`. Consider the case `nil => exact ⟨w, rfl, rfl⟩`. Consider the case `cons Z Zs ih`. Take `⟨w', h1, h2⟩` from `ih`. Take `⟨w'', h3, h4⟩` from `rderC_value T hsm hT y τ Z w'`.

Use `⟨w'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.foldr_cons, ← h1, h3]`. Rewrite using `[List.map_cons, List.foldr_cons, h2, h4]`.
-/
theorem wordC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Zs : List (Mt V.rank)) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = (Zs.map (dRepC (gramAt D V τ) (M.rep τ))).foldr (fun f acc => f acc) (w : M.H τ) ∧
      (Zs.map (RderC θ V τ)).foldr (fun f acc => f acc) (T (Function.update y τ w)) = T (Function.update y τ w') := by
  induction Zs with
  | nil => exact ⟨w, rfl, rfl⟩
  | cons Z Zs ih =>
    obtain ⟨w', h1, h2⟩ := ih
    obtain ⟨w'', h3, h4⟩ := rderC_value T hsm hT y τ Z w'
    refine ⟨w'', ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1, h3]
    · rw [List.map_cons, List.foldr_cons, h2, h4]

/- English proof (translation)
Use `choose W h1 h2 using fun idx : Fin (k + 1) → Fin V.rank => wordC_value T hsm hT y τ (List.ofFn fun a : Fin (k + 1) => (Matrix.single (idx a) (idx (a + 1)) 1 : Mt V.rank)) w`. Simplify using `only [List.map_ofFn] at h1 h2`. Establish `e : ∑ idx, W idx = c • w`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum, Submodule.coe_smul, ← hc, gelfRep]`.

Conclude with `Finset.sum_congr rfl fun idx _ => h1 idx`. Rewrite using `[← T.map_update_smul, ← e, T.map_update_sum, gelf]`. Conclude with `Finset.sum_congr rfl fun idx _ => h2 idx`.
-/
theorem gelf_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) (w : M.sm τ)
    (hc : gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ)) :
    gelf θ V τ k (T (Function.update y τ w)) = c • T (Function.update y τ w) := by
  choose W h1 h2 using fun idx : Fin (k + 1) → Fin V.rank =>
    wordC_value T hsm hT y τ (List.ofFn fun a : Fin (k + 1) => (Matrix.single (idx a) (idx (a + 1)) 1 : Mt V.rank)) w
  simp only [List.map_ofFn] at h1 h2
  have e : ∑ idx, W idx = c • w := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul, ← hc, gelfRep]
    exact Finset.sum_congr rfl fun idx _ => h1 idx
  rw [← T.map_update_smul, ← e, T.map_update_sum, gelf]
  exact Finset.sum_congr rfl fun idx _ => h2 idx

/- English proof (translation)
Use `⟨Submodule.span ℂ {T y}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hf`. Take `⟨c, hc⟩` from `hc τ k`. Establish `e : a • T y = T (Function.update y τ (a • y τ))` using `by rw [T.map_update_smul, Function.update_eq_self]`. Use `gelf_value T hsm hT y τ k c (a • y τ) (hc _)` as an intermediate fact.

Rewrite `this` using `[← e]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hf`.
-/
theorem zfin_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (hc : ∀ τ k, ∃ c : ℂ, ∀ w : M.sm τ, gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ))
    (y : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T y ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {T y}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := hc τ k
  have e : a • T y = T (Function.update y τ (a • y τ)) := by rw [T.map_update_smul, Function.update_eq_self]
  have := gelf_value T hsm hT y τ k c (a • y τ) (hc _)
  rw [← e] at this
  rw [this]
  exact Submodule.smul_mem _ _ hf

def lettersAt (τ : D.what₂.Tau) (l : List (D.what₂.Tau × Mt V.rank)) : List (Mt V.rank) :=
  (l.filter fun p => p.1 = τ).map Prod.snd

/- English proof (translation)
Introduce `X hX`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hX`. Take `⟨h1, h2⟩` from `List.mem_filter.1 hp`. Establish `h3 : p.1 = τ` using `by simpa using h2`. Conclude with `h3 ▸ hl p h1`.
-/
theorem lettersAt_mem {τ : D.what₂.Tau} {l : List (D.what₂.Tau × Mt V.rank)} (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∀ X ∈ lettersAt τ l, X ∈ lieAt V τ := by
  intro X hX
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hp
  have h3 : p.1 = τ := by simpa using h2
  exact h3 ▸ hl p h1

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact w.2`. Consider the case `cons X l ih => exact hsm τ X (hl X List.mem_cons_self) ⟨_, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)⟩`.
-/
theorem word_mem (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    {τ : D.what₂.Tau} (l : List (Mt V.rank)) (hl : ∀ X ∈ l, X ∈ lieAt V τ) (w : M.sm τ) :
    l.foldr (dRep (M.rep τ)) (w : M.H τ) ∈ M.sm τ := by
  induction l with
  | nil => exact w.2
  | cons X l ih => exact hsm τ X (hl X List.mem_cons_self) ⟨_, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih`. Establish `hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1` using `fun q hq => hl q (List.mem_cons_of_mem _ hq)`. Rewrite using `[List.foldr_cons, ih hl']`.

Use `hΦ (fun τ => ⟨_, word_mem hsm _ (lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = p.1`.

Substitute `h` using the available equality. Simplify using `[lettersAt]`. Establish `h' : ¬ p.1 = τ` using `fun e => h e.symm`. Simplify using `[lettersAt, Function.update_of_ne h, List.filter_cons, h']`.
-/
theorem word_map {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ)) =
      Φ fun τ => (lettersAt τ l).foldr (dRep (M.rep τ)) (y τ : M.H τ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, ih hl']
    have := hΦ (fun τ => ⟨_, word_mem hsm _ (lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)
    refine this.trans ?_
    congr 1
    funext τ
    by_cases h : τ = p.1
    · subst h; simp [lettersAt]
    · have h' : ¬ p.1 = τ := fun e => h e.symm
      simp [lettersAt, Function.update_of_ne h, List.filter_cons, h']

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨0, le_rfl, by simp⟩`. Consider the case `cons l L ih`. Take `⟨C, hC, ih⟩` from `ih fun q hq => h q (List.mem_cons_of_mem _ hq)`. Take `⟨c, hc⟩` from `h l List.mem_cons_self`.

Use `⟨max c C, le_max_of_le_right hC, fun w => ?_⟩` and prove the remaining obligations. Establish `h0 : 0 ≤ (L.map fun l => b l w).sum` using `List.sum_nonneg (by`. Introduce `x hx`. Take `⟨q, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hb q w)`.

Simplify using `only [List.map_cons, List.sum_cons, mul_add]`. Conclude with `add_le_add ((hc w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb l w))) ((ih w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0))`.
-/
theorem sum_bound {α β : Type} (a b : α → β → ℝ) (hb : ∀ l w, 0 ≤ b l w) (L : List α)
    (h : ∀ l ∈ L, ∃ c, ∀ w, a l w ≤ c * b l w) :
    ∃ C, 0 ≤ C ∧ ∀ w, (L.map fun l => a l w).sum ≤ C * (L.map fun l => b l w).sum := by
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons l L ih =>
    obtain ⟨C, hC, ih⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := h l List.mem_cons_self
    refine ⟨max c C, le_max_of_le_right hC, fun w => ?_⟩
    have h0 : 0 ≤ (L.map fun l => b l w).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact hb q w)
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add ((hc w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb l w)))
      ((ih w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0))

/- English proof (translation)
Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)`. Establish `hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x` using `fun w => LinearMap.congr_fun hℓ w`. Use `⟨ℓ, ?_, hℓ'⟩` and prove the remaining obligations. Take `⟨C', hC', hb⟩` from `sum_bound (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖) (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by`. Introduce `l hl`.

Use `⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)` and prove the remaining obligations. Rewrite using `[word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]`. Use `congr 2`. Use function extensionality and compare the values at `σ`.

Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h])`. Use `⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Introduce `l hl`. Take `⟨l', h', rfl⟩` from `List.mem_map.1 hl`. Conclude with `lettersAt_mem (hL l' h')`. Establish `hw' : w ∈ M.sm τ` using `Submodule.subset_span hw`. Establish `h1` using `hℓ' ⟨w, hw'⟩`.

Establish `h2` using `hb ⟨w, hw'⟩`. Establish `h3` using `hC (Function.update v τ ⟨w, hw'⟩)`. Rewrite using `[List.map_map, mul_assoc]`. Simplify using `only at h1`. Rewrite using `[h1]`.

Use `h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))` and prove the remaining obligations. Introduce `x hx`. Take `⟨q, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`.
-/
theorem cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
    (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
  have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
  refine ⟨ℓ, ?_, hℓ'⟩
  obtain ⟨C', hC', hb⟩ := sum_bound
    (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
    (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
      intro l hl
      refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
      refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
      rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
      congr 2
      funext σ
      by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h])
  refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
  · intro l hl
    obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
    exact lettersAt_mem (hL l' h')
  · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    have h1 := hℓ' ⟨w, hw'⟩
    have h2 := hb ⟨w, hw'⟩
    have h3 := hC (Function.update v τ ⟨w, hw'⟩)
    rw [List.map_map, mul_assoc]
    simp only at h1
    rw [h1]
    refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

/- English proof (translation)
Use `haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`. Conclude with `hf.comp (continuous_mul_const k)`.
-/
theorem continuous_rTr (k : GA D V) {f : GA D V → ℂ} (hf : Continuous f) : Continuous (rTr V k f) := by
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact hf.comp (continuous_mul_const k)

section L2

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))}

/- English proof (translation)
Simplify using `using (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F' ψ ψ' 1 h h'`.
-/
theorem repr_add (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {F F' ψ ψ'} (h : Repr V μ 𝓕 F ψ) (h' : Repr V μ 𝓕 F' ψ') :
    Repr V μ 𝓕 (F + F') (ψ + ψ') := by
  simpa using (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F' ψ ψ' 1 h h'

/- English proof (translation)
Use `(GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F ψ ψ (a - 1) h h` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem repr_smul (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) (a : ℂ) {F ψ} (h : Repr V μ 𝓕 F ψ) :
    Repr V μ 𝓕 (a • F) (a • ψ) := by
  have := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F ψ ψ (a - 1) h h
  rwa [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this

/- English proof (translation)
Establish `h1 : (Submodule.span ℂ A : Set K) ⊆ {z | ρ k z = c • z}`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact hA x hx`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[map_add, hx, hy, smul_add]`. Consider the case `smul a x _ hx`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`.

Rewrite using `[map_smul, hx, smul_comm]`. Conclude with `closure_minimal h1 (isClosed_eq (ρ k).continuous (continuous_const_smul c)) hF`.
-/
theorem eig_closure {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (A : Set K) (k : GA D V) (c : ℂ) (hA : ∀ z ∈ A, ρ k z = c • z) {F : K}
    (hF : F ∈ closure (Submodule.span ℂ A : Set K)) : ρ k F = c • F := by
  have h1 : (Submodule.span ℂ A : Set K) ⊆ {z | ρ k z = c • z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hA x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add, hx, hy, smul_add]
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_comm]
  exact closure_minimal h1 (isClosed_eq (ρ k).continuous (continuous_const_smul c)) hF

/- English proof (translation)
Take `⟨L, hL1, hL2, -, -, -, hL3, -, hL4, hL5⟩` from `GlobalTheory.RealLift.exists_real_lift D θ V hθ`. Use `haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1`. Establish `h1 : (1 : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V)` using `fun τ => by simp [Formalism.QuantumDeterminants.UH]`. Establish `hone : L 1 = 1`. Use `hL2 1 h1 1 h1` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Conclude with `mul_eq_left.1 this.symm`. Establish `a1 : ρ (L 1) = 1` using `by rw [hone, map_one]`. Establish `a2 : ∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), ρ (L (u * u')) = ρ (L u) * ρ (L u')` using `fun u hu u' hu' => by rw [hL2 u hu u' hu', map_mul]`. Establish `a3 : ∀ u ∈ UG (gramAt D V), ⟪F₀, ρ (L u) F₀⟫_ℂ = ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ` using `fun u hu => by`.

Rewrite using `[hco (L u) (hL1 u hu).1]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun τ _ => by rw [(hL1 u hu).2 τ]`. Take `⟨Φ, e1, e2, e3⟩` from `GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct V.rank D.what₂.Tau (gramAt D V) M.H M.rep K (fun u => ρ (L u)) (fun τ => (v τ : M.H τ)) F₀ (fun τ => ⟨(hL5 τ).2, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1, (Glo …`. Use `⟨Φ, e1, fun τ g hg y => ?_, fun y => ?_, fun k hk c h0 y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hL3 τ g hg]`. Conclude with `e2 τ g hg y`. Use `closure_mono (Submodule.span_mono ?_) (e3 y)` and prove the remaining obligations. Introduce and unpack `z ⟨u, -, hz⟩`. Conclude with `⟨_, hz⟩`.

Use `eig_closure ρ _ k c ?_ (e3 y)` and prove the remaining obligations. Introduce and unpack `z ⟨u, hu, hz⟩`. Establish `: ρ k (ρ (L u) F₀) = ρ (L u) (ρ k F₀)`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, hL4 k hk _ (hL1 u hu).1, map_mul, ContinuousLinearMap.mul_apply]`. Rewrite using `[hz, this, h0, map_smul]`.
-/
theorem exists_map_abs {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : GA D V →* (K →L[ℂ] K)) {v : M.Vec} (hθ : IsInfFam θ) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1)
    (hiso : ∀ g F, ‖ρ g F‖ = ‖F‖) (F₀ : K)
    (hco : ∀ u ∈ GinfC V, ⟪F₀, ρ u F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H K, (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set K)) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, ρ k F₀ = c • F₀ → ∀ y, ρ k (Φ y) = c • Φ y := by
  obtain ⟨L, hL1, hL2, -, -, -, hL3, -, hL4, hL5⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have h1 : (1 : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hone : L 1 = 1 := by
    have := hL2 1 h1 1 h1
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have a1 : ρ (L 1) = 1 := by rw [hone, map_one]
  have a2 : ∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), ρ (L (u * u')) = ρ (L u) * ρ (L u') :=
    fun u hu u' hu' => by rw [hL2 u hu u' hu', map_mul]
  have a3 : ∀ u ∈ UG (gramAt D V), ⟪F₀, ρ (L u) F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := fun u hu => by
    rw [hco (L u) (hL1 u hu).1]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [(hL1 u hu).2 τ]
  obtain ⟨Φ, e1, e2, e3⟩ := GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct V.rank D.what₂.Tau (gramAt D V) M.H M.rep K
    (fun u => ρ (L u)) (fun τ => (v τ : M.H τ)) F₀
    (fun τ => ⟨(hL5 τ).2, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.1, hv τ⟩)
    a1 a2 (fun u _ y => hiso _ y) a3
  refine ⟨Φ, e1, fun τ g hg y => ?_, fun y => ?_, fun k hk c h0 y => ?_⟩
  · rw [hL3 τ g hg]; exact e2 τ g hg y
  · refine closure_mono (Submodule.span_mono ?_) (e3 y)
    rintro z ⟨u, -, hz⟩
    exact ⟨_, hz⟩
  · refine eig_closure ρ _ k c ?_ (e3 y)
    rintro z ⟨u, hu, hz⟩
    have : ρ k (ρ (L u) F₀) = ρ (L u) (ρ k F₀) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hL4 k hk _ (hL1 u hu).1, map_mul, ContinuousLinearMap.mul_apply]
    rw [hz, this, h0, map_smul]

/- English proof (translation)
Establish `hr` using `GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ`. Establish `h` using `hr.2.2.2.1 F₀ φ k hF`. Establish `e : rTr V k φ = c • φ` using `funext hc`. Rewrite `h` using `[e]`. Establish `h3` using `hr.2.2.1 _ _ _ h (repr_smul hp hρ c hF)`.

Conclude with `h3`.
-/
theorem eig_class (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {φ : GA D V → ℂ}
    {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) (k : GA D V) (c : ℂ) (hc : ∀ g, φ (g * k) = c * φ g) :
    ρ k F₀ = c • F₀ := by
  have hr := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h := hr.2.2.2.1 F₀ φ k hF
  have e : rTr V k φ = c • φ := funext hc
  rw [e] at h
  have h3 := hr.2.2.1 _ _ _ h (repr_smul hp hρ c hF)
  exact h3

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm D θ V S M w v hθ hs hw hv μ 𝓕 ρ hp hρ J χ φ F₀ hφ hF`. Establish `h2` using `exists_map_abs (K := Lp ℂ 2 (nuQ V μ 𝓕)) (M := M) (v := v) ρ hθ (fun τ => (hv τ).1) hρ.iso F₀`. Establish `h3` using `h2 h1`. Use `h3.imp fun Φ h => ⟨h.1, h.2.1, h.2.2.1, fun k hk c hc => ?_⟩` and prove the remaining obligations. Establish `h4` using `eig_class hp hρ hF k c hc`.

Conclude with `h.2.2.2 k hk c h4`.
-/
theorem exists_map {w : D.what₂.Tau → Fin V.rank → ℤ} {v : M.Vec} (hθ : IsInfFam θ) (hs : HolShape M) (hw : WtIs M w)
    (hv : IsExtVec M v) (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {J : Set (GA D V)} {χ φ : GA D V → ℂ}
    (hφ : HolForm θ M w J χ φ) {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕)))) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, (∀ g, φ (g * k) = c * φ g) → ∀ y, ρ k (Φ y) = c • Φ y := by
  have h1 := GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm D θ V S M w v hθ hs hw hv μ 𝓕 ρ hp hρ J χ φ F₀ hφ hF
  have h2 := exists_map_abs (K := Lp ℂ 2 (nuQ V μ 𝓕)) (M := M) (v := v) ρ hθ (fun τ => (hv τ).1) hρ.iso F₀
  have h3 := h2 h1
  refine h3.imp fun Φ h => ⟨h.1, h.2.1, h.2.2.1, fun k hk c hc => ?_⟩
  have h4 := eig_class hp hρ hF k c hc
  exact h.2.2.2 k hk c h4

end L2

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce and unpack `D θ V S M w v hθ hs hw hv ⟨μ, 𝓕, hp⟩ J χ φ hJ hφ hZ`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.regular_representation_of_finite_pair D V μ 𝓕 hp`. Take `⟨r1, r2, -, r4, -, -⟩` from `GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ`. Take `⟨F₀, hF⟩` from `r1 φ hφ.aut.cont hφ.aut.left hφ.bdd`. Take `⟨Φ, e1, e2, e3, e4⟩` from `exists_map hθ hs hw hv hp hρ hφ hF`.

Take `⟨U, hU, hUφ⟩` from `hφ.aut.level`. Establish `hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y` using `fun y k hk hk' => by`. Simplify using `using e4 k hk' 1 (fun g => by rw [hUφ k hk hk', one_mul]) y`. Establish `hsmM` using `GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ e2`. Use `choose ψ p1 p2 p3 p4 using fun y : M.Vec => GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)`.

Use `haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1`. Establish `hH : ∀ τ, (gramAt D V τ).IsHermitian` using `GlobalTheory.SmoothAutCheck.gramAt_herm V`. Establish `hdet : ∀ τ, (gramAt D V τ).det ≠ 0` using `fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero`. Establish `hsv` using `fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1`. Establish `hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ` using `fun τ X hX w => Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1`.

Establish `uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ fun τ => (y τ : M.H τ)) f → ψ y = f` using `fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h`. Set `T : MMap M` to `MultilinearMap.mk' ψ (fun y τ a b => by`. Use `uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_` and prove the remaining obligations. Use `repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))` as an intermediate fact. Rewrite `this` using `[coe_update, coe_update, ← Φ.map_update_add]`.

Rewrite using `[coe_update]`. Conclude with `this)`. Use the proof step `(fun y τ c a => by`. Use `uniq _ _ ((p2 _).cont.const_smul c) ?_` and prove the remaining obligations. Use `repr_smul hp hρ c (p1 (Function.update y τ a))` as an intermediate fact.

Rewrite `this` using `[coe_update, ← Φ.map_update_smul]`. Rewrite using `[coe_update]`. Conclude with `this)`. Establish `hTψ : ∀ y, T y = ψ y` using `fun _ => rfl`. Establish `hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) → Rder θ V τ X (T y) = T (Function.update y τ w)`.

Introduce `y τ X hX w hw`. Take `⟨q1, q2⟩` from `p4 y [(τ, X)] (by simpa using hX)`. Simplify using `only [List.foldr_cons, List.foldr_nil] at q1 q2`. Use `(uniq _ _ q1 ?_).symm` and prove the remaining obligations. Rewrite using `[coe_update, hw, ← (hsmM y).2 τ X hX]`.

Conclude with `q2`. Take `⟨N, L, hL, hgr⟩` from `GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU`. Use `⟨T, ⟨fun y => ⟨p2 y, p3 y, ?_, N, fun l hl x => ?_⟩, fun y => ?_, fun y k hk g => ?_, fun τ g hg y z hz => ?_, fun τ y x => ?_⟩, uniq v φ hφ.aut.cont (e1 ▸ hF)⟩` and prove the remaining obligations. Use `zfin_value T hsm hT (fun τ k => ?_) y` and prove the remaining obligations. Take `⟨-, m1, m2, m3⟩` from `GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ`.

Take `⟨k1, k2⟩` from `GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hs hw hv τ`. Take `⟨c, hc⟩` from `GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight V.rank (gramAt D V τ) _ _ (w τ) (M.H τ) (M.rep τ) (m3 hs).1 m1 m2 (v τ) (by rw [← norm_ne_zero_iff, (hv τ).1]; exact one_ne_zero) k1 k2 k`. Conclude with `⟨c, fun z => hc z ((hsv τ).1 z z.2)⟩`. Take `⟨y', hy'⟩` from `word_value T hsm hT l hl y`. Take `⟨C, hC⟩` from `hgr x`.

Use `⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[hy', mul_right_comm]`. Conclude with `hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg`. Conclude with `GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (p2 y) (GlobalTheory.T.cuspidality_preserved_in_closure D θ V hθ μ 𝓕 ρ hp hρ φ (ψ y) F₀ _ hφ.aut hZ hF (p2 y) (p1 y) (e3 _))`. Establish `h1` using `r4 _ _ k (p1 y)`.

Rewrite `h1` using `[e4 k (hJ hk) (χ k) (hφ.lev k hk)]`. Establish `h2` using `r2 _ _ _ (continuous_rTr k (p2 y).cont) ((p2 y).cont.const_smul (χ k)) h1 (repr_smul hp hρ (χ k) (p1 y))`. Conclude with `congrFun h2 g`. Use `uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_` and prove the remaining obligations. Rewrite using `[coe_update, hz, e2 τ g hg]`.

Conclude with `r4 _ _ _ (p1 y)`. Take `⟨C, hC⟩` from `hgr x`. Use `cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y` and prove the remaining obligations. Use `hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_multMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  rintro D θ V S M w v hθ hs hw hv ⟨μ, 𝓕, hp⟩ J χ φ hJ hφ hZ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.regular_representation_of_finite_pair D V μ 𝓕 hp
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  obtain ⟨F₀, hF⟩ := r1 φ hφ.aut.cont hφ.aut.left hφ.bdd
  obtain ⟨Φ, e1, e2, e3, e4⟩ := exists_map hθ hs hw hv hp hρ hφ hF
  obtain ⟨U, hU, hUφ⟩ := hφ.aut.level
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y := fun y k hk hk' => by
    simpa using e4 k hk' 1 (fun g => by rw [hUφ k hk hk', one_mul]) y
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hTψ : ∀ y, T y = ψ y := fun _ => rfl
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  refine ⟨T, ⟨fun y => ⟨p2 y, p3 y, ?_, N, fun l hl x => ?_⟩, fun y => ?_, fun y k hk g => ?_, fun τ g hg y z hz => ?_,
    fun τ y x => ?_⟩, uniq v φ hφ.aut.cont (e1 ▸ hF)⟩
  · refine zfin_value T hsm hT (fun τ k => ?_) y
    obtain ⟨-, m1, m2, m3⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
    obtain ⟨k1, k2⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hs hw hv τ
    obtain ⟨c, hc⟩ := GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight V.rank (gramAt D V τ) _ _ (w τ) (M.H τ) (M.rep τ) (m3 hs).1 m1 m2 (v τ)
      (by rw [← norm_ne_zero_iff, (hv τ).1]; exact one_ne_zero) k1 k2 k
    exact ⟨c, fun z => hc z ((hsv τ).1 z z.2)⟩
  · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
    obtain ⟨C, hC⟩ := hgr x
    refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
    rw [hy', mul_right_comm]
    exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
  · exact GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (p2 y)
      (GlobalTheory.T.cuspidality_preserved_in_closure D θ V hθ μ 𝓕 ρ hp hρ φ (ψ y) F₀ _ hφ.aut hZ hF (p2 y) (p1 y) (e3 _))
  · have h1 := r4 _ _ k (p1 y)
    rw [e4 k (hJ hk) (χ k) (hφ.lev k hk)] at h1
    have h2 := r2 _ _ _ (continuous_rTr k (p2 y).cont) ((p2 y).cont.const_smul (χ k)) h1
      (repr_smul hp hρ (χ k) (p1 y))
    exact congrFun h2 g
  · refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  · obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this

end GlobalTheory.BackForm
