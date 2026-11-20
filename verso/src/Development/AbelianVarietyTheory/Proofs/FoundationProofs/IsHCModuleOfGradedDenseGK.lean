import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalStableLeISupEigen
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedKFin

variable {p q : ℕ}

/- English proof (translation)
Introduce `a b hab`. Establish `: a ≠ b`. Introduce and unpack `rfl`. Apply the tactic sequence `cases a <;> simp [sameBlock] at hab`. Simplify using `[Matrix.one_apply, this]`.
-/
theorem kset_one (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    cases a <;> simp [sameBlock] at hab
  simp [Matrix.one_apply, this]

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hac : sameBlock a c`. Establish `hcb : ¬ sameBlock c b`.

Apply the tactic sequence `cases a <;> cases b <;> cases c <;> simp_all [sameBlock]`. Rewrite using `[hh c b hcb, mul_zero]`. Rewrite using `[hg a c hac, zero_mul]`.
-/
theorem kset_mul (T : GrpData p q) {g h : T.G} (hg : g ∈ T.Kset) (hh : h ∈ T.Kset) :
    g * h ∈ T.Kset := by
  intro a b hab
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := by
      cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
    rw [hh c b hcb, mul_zero]
  · rw [hg a c hac, zero_mul]

/- English proof (translation)
Establish `hcl` using `GlobalTheory.CoverKGen.kset_gen p q hpq T g hg`. It suffices to establish `h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1`. Use `clear hg`. Proceed by induction on `hcl using Subgroup.closure_induction with`. Consider the case `mem g hg`.

Take `⟨Y, ⟨hY, hKC⟩, rfl⟩` from `hg`. Establish `hf` using `GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y))) (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)`. Establish `hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y)`. Use `T.expt_add Y hY 1 (-1)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, zero_smul, T.expt_zero, one_smul]`.

Conclude with `(eq_inv_of_mul_eq_one_right this.symm).symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hf 1` as an intermediate fact. Simplify `this` using `only [one_smul]`. Rewrite using `[hinv]`.

Conclude with `hf (-1)`. Consider the case `one => simp`. Consider the case `mul a b _ _ ha hb`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `ha.1 _ (hb.1 x hx)`. Rewrite using `[mul_inv_rev, map_mul]`. Conclude with `hb.2 _ (ha.2 x hx)`. Consider the case `inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩`.
-/
theorem map_stable (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q)
    (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    {g : T.G} (hg : g ∈ T.Kset) : ∀ x ∈ W.map j, σ.π g x ∈ W.map j := by
  have hcl := GlobalTheory.CoverKGen.kset_gen p q hpq T g hg
  suffices h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1
  clear hg
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨Y, ⟨hY, hKC⟩, rfl⟩ := hg
    have hf := GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)
    have hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY 1 (-1)
      rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at this
      exact (eq_inv_of_mul_eq_one_right this.symm).symm
    refine ⟨?_, ?_⟩
    · have := hf 1
      simpa only [one_smul] using this
    · rw [hinv]; exact hf (-1)
  | one => simp
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul]; exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 x hx)
  | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

/- English proof (translation)
Introduce `p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig`. Use `⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩` and prove the remaining obligations. Introduce and unpack `⟨v, rfl⟩`. Take `⟨W, hWf, hv, hW⟩` from `M.kfin v`. Establish `hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`. Establish `hsup : (⨆ m, (N m).map j) = LinearMap.range j`.

Rewrite using `[← Submodule.map_iSup, htop, Submodule.map_top]`. Establish `hle` using `GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k) (fun m => (N m).map j) lam hlam (fun m => inferInstance) (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy) (by rw [hsup]; exact hd) (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨g, rfl⟩` from `hw`. Use `Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Both sides reduce to the same expression. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c ha)`. Rewrite `hle` using `[hsup]`.

Conclude with `hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)`.
-/
theorem isHCMod_of_graded : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  intro p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig
  refine ⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨W, hWf, hv, hW⟩ := M.kfin v
    have hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · have hsup : (⨆ m, (N m).map j) = LinearMap.range j := by
      rw [← Submodule.map_iSup, htop, Submodule.map_top]
    have hle := GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k)
      (fun m => (N m).map j) lam hlam (fun m => inferInstance)
      (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy)
      (by rw [hsup]; exact hd)
      (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨g, rfl⟩ := hw
          refine Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩
          simp only [map_mul]
          rfl
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
    rw [hsup] at hle
    exact hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)

end GlobalTheory.GradedKFin
