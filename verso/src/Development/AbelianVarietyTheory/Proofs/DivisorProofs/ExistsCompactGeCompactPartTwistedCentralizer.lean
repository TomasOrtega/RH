import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.CptTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hinv : ∀ x, thL n w (thL n w x) = x` using `(GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1`. Establish `hg' : g * y = y * thL n w g` using `hg`. Unfold `nrmL`. Use `split_ifs with hs`. Establish `ht : thL n w = MonoidHom.id _` using `by unfold thL; rw [if_pos hs]`.

Rewrite `hg'` using `[ht]`. Conclude with `hg'`. Establish `ht : thL n w = thetaGL n (cj w)` using `by unfold thL; rw [if_neg hs]`. Rewrite `hg'`, `hinv` using `[ht]`. Use `show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem twCent_commute (hE : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) {g : GLw n w}
    (hg : g ∈ twCent (thL n w) y) : Commute g (nrmL n w y) := by
  have hinv : ∀ x, thL n w (thL n w x) = x := (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1
  have hg' : g * y = y * thL n w g := hg
  unfold nrmL
  split_ifs with hs
  · have ht : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    rw [ht] at hg'
    exact hg'
  · have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
    rw [ht] at hg' hinv
    show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g
    calc g * (y * thetaGL n (cj w) y) = (g * y) * thetaGL n (cj w) y := by rw [mul_assoc]
      _ = y * (thetaGL n (cj w) g * thetaGL n (cj w) y) := by rw [hg', mul_assoc]
      _ = y * thetaGL n (cj w) (g * y) := by rw [map_mul]
      _ = y * thetaGL n (cj w) (y * thetaGL n (cj w) g) := by rw [hg']
      _ = (y * thetaGL n (cj w) y) * g := by rw [map_mul, hinv, mul_assoc]

/- English proof (translation)
Introduce `E _ _ _ hE n w y hs`. Use `set M := nrmL n w y with hM`. Use `set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN`. Establish `hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g`. Introduce `g hg`.

Use `congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq` as an intermediate fact. Simplify `this` using `[Units.val_mul]`. Establish `hadj : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N}` using `fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)`. Establish `hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h`. Introduce `g h hg hh`.

Establish `h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_` and prove the remaining obligations. Introduce `b hb`. Rewrite `hb` using `[Set.mem_singleton_iff]`. Rewrite using `[hb]`.

Conclude with `hval g hg`. Conclude with `Units.ext (by simpa [Units.val_mul] using h1.eq)`. Set `S : Set (GLw n w)` to `{g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}`. Set `H0 : Subgroup (GLw n w)` to `{ carrier := S one_mem' := by`. Use `⟨Commute.one_left M, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]`. Conclude with `isCompact_singleton`. Use the proof step `mul_mem' := by`. Introduce `g h hg hh`. Use `⟨hg.1.mul_left hh.1, ?_⟩` and prove the remaining obligations.

Establish `hK` using `hg.2.mul hh.2`. Use `hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)` and prove the remaining obligations. Introduce and unpack `x ⟨k, rfl⟩`. Simplify using `only`. Rewrite using `[(hcomm g h hg.1 hh.1).mul_zpow]`.

Conclude with `Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)`. Use the proof step `inv_mem' := by`. Introduce `g hg`. Use `⟨hg.1.inv_left, ?_⟩` and prove the remaining obligations. Use `show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))`.

Rewrite using `[Subgroup.zpowers_inv]`. Conclude with `hg.2 }`. Take `⟨c, hc⟩` from `GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs`. Establish `hB` using `GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c`. Establish `hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c}`.

Introduce `g hg`. Establish `hg' : g⁻¹ ∈ H0` using `H0.inv_mem hg`. Introduce `i j`. Conclude with `⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j, hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩`. Use `⟨H0.topologicalClosure, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.topologicalClosure_coe]`. Conclude with `hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)`. Use `le_trans ?_ (Subgroup.le_topologicalClosure H0)` and prove the remaining obligations. Rewrite using `[cptPart, Subgroup.closure_le]`. Introduce and unpack `t ⟨ht, htc⟩`.

Conclude with `⟨twCent_commute hE n w y ht, htc⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w),
    (nrmL n w y).val.charpoly.Separable →
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  intro E _ _ _ hE n w y hs
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨twCent_commute hE n w y ht, htc⟩

end GlobalTheory.CptTorus
