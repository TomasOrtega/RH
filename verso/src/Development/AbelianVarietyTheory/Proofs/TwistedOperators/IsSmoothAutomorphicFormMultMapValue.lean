import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar

noncomputable section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S GlobalTheory.SmVec GlobalTheory.MultGelf Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivValues

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def IsEquivMap (θ : InfFam D) (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)

def IsSobValued (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ : InfFam D} {M : DSModel V S} {T : MMap M}

/- English proof (translation)
Use `haveI : CompleteSpace (M.H τ) := (M.ds τ).1`. Establish `hG` using `gram_unit (M.fr_unit τ) (M.fr_gram τ)`. Use function extensionality and compare the values at `x`. Take `⟨ℓ, hℓ, hℓT⟩` from `hC τ v x`. Take `⟨m, ls, a, hls, ha⟩` from `GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ`.

Establish `hu` using `(mem_sm M τ).1 u.2`. Establish `hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ))` using `fun t => rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)`. Establish `h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ => ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ`. Use function extensionality and compare the values at `t`. Rewrite using `[← ha _ (hmem t)]`.

Establish `h2` using `hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩ (by rw [Function.update_self]; rfl)`. Rewrite `h2` using `[Function.update_idem]`. Establish `h3` using `hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩`. Rewrite `h3` using `[h2]`. Conclude with `h3.symm`.

Establish `h4 : HasDerivAt (fun t : ℝ => ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ) (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0`. Use `HasDerivAt.fun_sum fun i _ => ?_` and prove the remaining obligations. Establish `h5` using `(hasDerivAt_const (0 : ℝ) (a i)).inner ℂ (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)`. Simplify using `using h5`. Unfold `Rder`.

Rewrite using `[h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]`.
-/
theorem rder_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hC τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

/- English proof (translation)
Establish `hG` using `gram_unit (M.fr_unit τ) (M.fr_gram τ)`. Establish `hp` using `parts_mem hG (gram_herm (M.fr_gram τ)) Z`. Establish `hu` using `(mem_sm M τ).1 u.2`. Establish `h1` using `rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl`. Establish `h2` using `rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl`.

Establish `h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ + Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩` using `Subtype.ext hw`. Rewrite using `[h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]`. Both sides reduce to the same expression.
-/
theorem rderC_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨u, rfl, rfl⟩`. Consider the case `cons Z l ih`. Take `⟨w, h1, h2⟩` from `ih`. Use `⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ)) (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[List.map_cons, List.foldr_cons, ← h1]`. Rewrite using `[List.map_cons, List.foldr_cons, h2]`. Conclude with `rderC_apply hE hC τ v Z w _ rfl`.
-/
theorem foldr_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hE hC τ v Z w _ rfl

/- English proof (translation)
Use `choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank => foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)`. Simplify using `only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2`. Establish `h1 : w = ∑ idx, f idx`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hw, Submodule.coe_sum]`.

Conclude with `Finset.sum_congr rfl fun idx _ => (hf1 idx).symm`. Rewrite using `[h1]`. Use `Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun idx _ => hf2 idx`.
-/
theorem gelf_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ)) :
    gelf θ V τ k (T v) = T (Function.update v τ w) := by
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

/- English proof (translation)
Use `haveI : CompleteSpace (M.H τ) := (M.ds τ).1`. Take `⟨c, hc⟩` from `GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hv` using `hc _ ((mem_sm M τ).1 (v τ).2)`. Rewrite using `[gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]`.

Use `T.map_update_smul v τ c (v τ)` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Conclude with `this`.
-/
theorem gelf_eigen (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) :
    ∃ c : ℂ, gelf θ V τ k (T v) = c • T v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ)
    (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k
  refine ⟨c, ?_⟩
  have hv := hc _ ((mem_sm M τ).1 (v τ).2)
  rw [gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]
  have := T.map_update_smul v τ c (v τ)
  rw [Function.update_eq_self] at this
  exact this

/- English proof (translation)
Use `⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hf`. Take `⟨c, hc⟩` from `gelf_eigen hE hC τ k v`. Rewrite using `[(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))`.
-/
theorem zfin (hθ : IsInfFam θ) (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (v : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T v ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_eigen hE hC τ k v
  rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/- English proof (translation)
Introduce `_ D θ hθ V S M T U N hU hT hE hC v`. Take `⟨h1, h2, h3, h4, h5⟩` from `hT v`. Conclude with `GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩) ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)`.
-/
theorem isAutFunSm : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  intro _ D θ hθ V S M T U N hU hT hE hC v
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT v
  exact GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩)
    ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)

end GlobalTheory.EquivValues

end
