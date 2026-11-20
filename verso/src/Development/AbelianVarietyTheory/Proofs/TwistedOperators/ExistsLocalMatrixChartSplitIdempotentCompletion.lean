import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HatLocalChart

open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem a' ha'`. Take `⟨b, hb, x, rfl⟩` from `ha'`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨c, hc, w, hw, rfl⟩` from `hz`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨b * c, fun v => ?_, x • w, L.smul_mem x hw, ?_⟩` and prove the remaining obligations. Establish `hbv` using `hb v`. Simplify using `only [Formalism.MainNotions.StandardLattice.intAf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Set.mem_setOf_eq] at hbv`.

Conclude with `mul_mem hbv (hc v)`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.

Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`. Consider the case `add a₁ a₂ _ _ h₁ h₂ => rw [add_smul]`. Conclude with `add_mem h₁ h₂`. Consider the case `neg a _ h => rw [neg_smul]`.

Conclude with `neg_mem h`.
-/
theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨b, hb, x, rfl⟩ := ha'
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, w, hw, rfl⟩ := hz
      apply AddSubgroup.subset_closure
      refine ⟨b * c, fun v => ?_, x • w, L.smul_mem x hw, ?_⟩
      · have hbv := hb v
        simp only [Formalism.MainNotions.StandardLattice.intAf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Set.mem_setOf_eq] at hbv
        exact mul_mem hbv (hc v)
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a₁ a₂ _ _ h₁ h₂ => rw [add_smul]; exact add_mem h₁ h₂
  | neg a _ h => rw [neg_smul]; exact neg_mem h

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D e v π s n L he h1 h2 h3 hfg hspan`. Establish `hπ1 : π (finPart D e) = 1`. Establish `h` using `h2 1`. Rewrite `h` using `[map_one, mul_one]`. Rewrite using `[← h, h1 1]`.

Establish `heint : finPart D e ∈ intAE D`. Establish `h` using `(h3 1).2 (by rw [map_one]; exact one_mem _)`. Rewrite `h` using `[mul_one]`. Then use the resulting hypothesis. Establish `hπint : ∀ x ∈ intAE D, π x ∈ Formalism.UG.Ov D.host.F v` using `fun x hx => (h3 x).1 (GlobalTheory.SplitLatBasis.mul_mem_intAE D heint hx)`. Establish `hone : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) w ∈ w.adicCompletionIntegers D.host.F` using `fun w => one_mem (w.adicCompletionIntegers D.host.F)`.

Take `⟨g, hg⟩` from `hfg`. Set `O` to `v.adicCompletionIntegers D.host.F`. Set `gen : ↥(g : Set (Fin n → D.host.E)) → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E` to `fun j i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (j : Fin n → D.host.E) i`. Set `N : Submodule O (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)` to `Submodule.span O (Set.range fun j i => π (gen j i))`. Establish `hL : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, a w ∈ w.adicCompletionIntegers D.host.F) → ∀ x ∈ L, (fun i => π (a ⊗ₜ[D.host.F] x i)) ∈ N`.

Introduce `a ha x hx`. Establish `haE : a ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D` using `AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, by simp⟩`. Rewrite `hx` using `[← hg]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Establish `hx' : (fun i => π (a ⊗ₜ[D.host.F] x i)) = (⟨π (a ⊗ₜ[D.host.F] (1 : D.host.E)), hπint _ haE⟩ : O) • (fun i => π (gen ⟨x, hx⟩ i))`. Use function extensionality and compare the values at `i`. Use `show π (a ⊗ₜ[D.host.F] x i) = π (a ⊗ₜ[D.host.F] (1 : D.host.E)) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hx']`.

Conclude with `N.smul_mem _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)`. Consider the case `zero`. Use `N.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Use `N.add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[TensorProduct.tmul_add]`. Consider the case `smul c x _ hx`.

Establish `hc : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) ∈ intAE D` using `AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩`. Use `N.smul_mem (⟨π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)), hπint _ hc⟩ : O) hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `show π (a ⊗ₜ[D.host.F] ((c : D.host.E) * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * π (a ⊗ₜ[D.host.F] x i)`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.

Establish `hz : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), (fun i => π (z i)) ∈ N`. Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`.

Conclude with `hL a ha x hx`. Consider the case `zero`. Use `N.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `add z₁ z₂ _ _ h₁ h₂`. Use `N.add_mem h₁ h₂ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `neg z _ h`.

Use `N.neg_mem h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hgen : ∀ j, gen j ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))` using `fun j => AddSubgroup.subset_closure ⟨1, hone, j, hg ▸ Submodule.subset_span j.2, rfl⟩`. Establish `hiff : ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔ (fun j => π (y j)) ∈ N`.

Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `hz _ hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Use `show π (y j) = π (finPart D e * y j)`. Rewrite using `[map_mul, hπ1, one_mul]`. Introduce `hy`. Establish `hs` using `GlobalTheory.SplitLatBasis.section_mem O π (fun a => finPart D (s a)) (finPart D e) (intAE D) (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) h1 h2 (fun x hx => (h3 x).2 hx) (fun a ha y hy => smul_mem_hat D L ha hy) gen hgen _ hy`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Conclude with `(h2 (y j)).symm`. Establish `hfin : N.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `htop : Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)) = ⊤` using `by set S := Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))`. Establish `hΦ : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)), (fun i => π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈ S`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (hL 1 hone x hx)`. Consider the case `zero`. Use `S.zero_mem using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `S.add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `[TensorProduct.tmul_add]`. Consider the case `smul c x _ hx`. Use `S.smul_mem (π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c)) hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `show π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.ho …`.

Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[Submodule.eq_top_iff']`. Introduce `w`. Rewrite using `[pi_eq_sum_univ w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Use `hΦ (fun j => if i = j then 1 else 0) (by rw [hspan]; trivial) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Use `split_ifs`. Rewrite using `[← Algebra.TensorProduct.one_def, map_one]`. Rewrite using `[TensorProduct.tmul_zero, map_zero]`.

Use `haveI : Submodule.IsLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := ⟨hfin, htop⟩`. Take `⟨B, hB⟩` from `GlobalTheory.SplitLatBasis.exists_matrix_of_isLattice (R := O) N`. Use `⟨B, fun y => (hiff y).trans ((hB _).trans (forall_congr' fun i => ?_))⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`.

Rewrite using `[← hr]`. Conclude with `r.2`. Introduce `h`. Conclude with `⟨⟨_, h⟩, rfl⟩`.
-/
theorem exists_chart : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D e v π s n L he h1 h2 h3 hfg hspan
  have hπ1 : π (finPart D e) = 1 := by
    have h := h2 1
    rw [map_one, mul_one] at h
    rw [← h, h1 1]
  have heint : finPart D e ∈ intAE D := by
    have h := (h3 1).2 (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at h
  have hπint : ∀ x ∈ intAE D, π x ∈ Formalism.UG.Ov D.host.F v := fun x hx =>
    (h3 x).1 (GlobalTheory.SplitLatBasis.mul_mem_intAE D heint hx)
  have hone : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) w ∈ w.adicCompletionIntegers D.host.F :=
    fun w => one_mem (w.adicCompletionIntegers D.host.F)
  obtain ⟨g, hg⟩ := hfg
  let O := v.adicCompletionIntegers D.host.F
  let gen : ↥(g : Set (Fin n → D.host.E)) → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (j : Fin n → D.host.E) i
  let N : Submodule O (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    Submodule.span O (Set.range fun j i => π (gen j i))

  have hL : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, a w ∈ w.adicCompletionIntegers D.host.F) →
      ∀ x ∈ L, (fun i => π (a ⊗ₜ[D.host.F] x i)) ∈ N := by
    intro a ha x hx
    have haE : a ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, by simp⟩
    rw [← hg] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hx' : (fun i => π (a ⊗ₜ[D.host.F] x i)) =
          (⟨π (a ⊗ₜ[D.host.F] (1 : D.host.E)), hπint _ haE⟩ : O) • (fun i => π (gen ⟨x, hx⟩ i)) := by
        funext i
        show π (a ⊗ₜ[D.host.F] x i) = π (a ⊗ₜ[D.host.F] (1 : D.host.E)) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx']
      exact N.smul_mem _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    | zero =>
      convert N.zero_mem using 1
      funext i
      simp
    | add x y _ _ hx hy =>
      convert N.add_mem hx hy using 1
      funext i
      simp [TensorProduct.tmul_add]
    | smul c x _ hx =>
      have hc : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      convert N.smul_mem (⟨π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)), hπint _ hc⟩ : O) hx using 1
      funext i
      show π (a ⊗ₜ[D.host.F] ((c : D.host.E) * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * π (a ⊗ₜ[D.host.F] x i)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hz : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), (fun i => π (z i)) ∈ N := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact hL a ha x hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      simp
    | add z₁ z₂ _ _ h₁ h₂ =>
      convert N.add_mem h₁ h₂ using 1
      funext i
      simp
    | neg z _ h =>
      convert N.neg_mem h using 1
      funext i
      simp
  have hgen : ∀ j, gen j ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := fun j =>
    AddSubgroup.subset_closure ⟨1, hone, j, hg ▸ Submodule.subset_span j.2, rfl⟩
  have hiff : ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔ (fun j => π (y j)) ∈ N := by
    intro y
    constructor
    · intro hy
      convert hz _ hy using 1
      funext j
      show π (y j) = π (finPart D e * y j)
      rw [map_mul, hπ1, one_mul]
    · intro hy
      have hs := GlobalTheory.SplitLatBasis.section_mem O π (fun a => finPart D (s a)) (finPart D e) (intAE D)
        (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) h1 h2 (fun x hx => (h3 x).2 hx)
        (fun a ha y hy => smul_mem_hat D L ha hy) gen hgen _ hy
      convert hs using 1
      funext j
      exact (h2 (y j)).symm
  have hfin : N.FG := Submodule.fg_span (Set.finite_range _)
  have htop : Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
      (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)) = ⊤ := by
    set S := Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    have hΦ : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)),
        (fun i => π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL 1 hone x hx)
      | zero =>
        convert S.zero_mem using 1
        funext i
        simp
      | add x y _ _ hx hy =>
        convert S.add_mem hx hy using 1
        funext i
        simp [TensorProduct.tmul_add]
      | smul c x _ hx =>
        convert S.smul_mem (π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c)) hx using 1
        funext i
        show π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [Submodule.eq_top_iff']
    intro w
    rw [pi_eq_sum_univ w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    convert hΦ (fun j => if i = j then 1 else 0) (by rw [hspan]; trivial) using 1
    funext j
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [TensorProduct.tmul_zero, map_zero]
  haveI : Submodule.IsLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := ⟨hfin, htop⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_matrix_of_isLattice (R := O) N
  refine ⟨B, fun y => (hiff y).trans ((hB _).trans (forall_congr' fun i => ?_))⟩
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact r.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end GlobalTheory.HatLocalChart
