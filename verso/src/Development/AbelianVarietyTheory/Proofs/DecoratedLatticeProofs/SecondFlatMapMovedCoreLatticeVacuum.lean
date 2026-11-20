import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.MovedVac

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨β, hβi, hβ, c, hc, x, hx, rfl⟩` from `hz`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Use `AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add z z' _ _ hz hz' => rw [smul_add]`. Conclude with `add_mem hz hz'`. Consider the case `neg z _ hz => rw [smul_neg]`. Conclude with `neg_mem hz`.
-/
theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨β, hβi, hβ, a, ha, x, hx, rfl⟩` from `hy`. Use `set y' : Fin S₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'`. Establish `hy'm : y' ∈ latV S₀ L₀ (· = v)` using `AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩`.

Establish `hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y'`. Use function extensionality and compare the values at `i`. Simplify using `only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[hsplit, Matrix.mulVec_smul]`. Use `smul_mem_latA ha ((hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩)` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]`. Establish `: colMul d.jX i ((0 : Fin ρ → AE D) i) = 0` using `by funext k; simp [colMul]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Rewrite using `[Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]`.

Establish `: colMul d.jY i ((0 : Fin ρ → AE D) i) = 0` using `by funext k; simp [colMul]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Rewrite using `[Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]`. Conclude with `hy'm`.

Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz' => rw [Matrix.mulVec_add]`. Conclude with `add_mem hz hz'`. Consider the case `neg z _ hz => rw [Matrix.mulVec_neg]`.

Conclude with `neg_mem hz`.
-/
theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin S₀.rank → AE D} (hz : z ∈ latA S₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    refine smul_mem_latA ha ((hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩)
    · rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
      have : colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
      have : colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      exact hy'm
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wittExt_wittInc_core_hom_eq {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (u : WO J.W₀ B.V₀) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) = B.d.j0 * u * J.d.p0 := rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.FinPl.LatMem.mem_latO_iff D J.W B.V LV L hV hL (· = v)]`. Establish `hmx` using `GlobalTheory.FinPl.LatMem.latO_mxAt hu`. Use `⟨fun i j => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[wittExt_wittInc_core_hom_eq, Matrix.mul_apply]`. Use `sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)`. Express the relevant statement in the definitionally equal form `(B.d.j0 * u * J.d.p0) *ᵥ y ∈ _`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hmW (GlobalTheory.FinPl.LatMem.latO_maps hV₀ hu ((hmV y).1 hy).2.2)`.
-/
theorem wittExt_wittInc_mem_completed_hom_lattice {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {LV : Lat J.W} {LV₀ : Lat J.W₀} {L : Lat B.V}
    {M : Lat B.V₀} {v : Pl D} (hV : IsSelfDualC J.W LV) (hV₀ : IsSelfDualC J.W₀ LV₀) (hL : IsSelfDualC B.V L)
    (hmV : MonoAt J.d LV LV₀ v) (hmW : MonoAt B.d L M v) {u : WO J.W₀ B.V₀}
    (hu : u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v)) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) ∈ latO J.W B.V (LV : Set _) (L : Set _) (· = v) := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D J.W B.V LV L hV hL (· = v)]
  have hmx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [wittExt_wittInc_core_hom_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (B.d.j0 * u * J.d.p0) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hmW (GlobalTheory.FinPl.LatMem.latO_maps hV₀ hu ((hmV y).1 hy).2.2)

/- English proof (translation)
Introduce `i j`. Rewrite using `[wittExt_wittInc_core_hom_eq]`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Take the linear combination `(B.d.j0 i k * J.d.p0 l j) * hu k l`.
-/
theorem wittExt_wittInc_isHalf {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {e : AE D} {u : WO J.W₀ B.V₀}
    (hu : IsHalf e u) : IsHalf e (J.d.ext0 B.V (B.d.inc0 J.W₀ u)) := by
  intro i j
  rw [wittExt_wittInc_core_hom_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (B.d.j0 i k * J.d.p0 l j) * hu k l

end GlobalTheory.FinPl.MovedVac

open GlobalTheory.FinPl.MovedVac in

/- English proof (translation)
Introduce `D ψ σ J B s LV LV₀ LW LW₀ v hA _ f hf γ _`. Establish `hflat : IsFlatFB s (· = v) (flatFB s)` using `(GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s`. Take `⟨M, hM, hMv⟩` from `(GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V₀ LW₀ hA.sdW₀).1 γ`. Take `⟨L', hL', hL'v⟩` from `(GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).1 (B.d.emb0 γ)`. Establish `hmono : MonoAt B.d L' M v` using `(GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).2 B.V₀ σ B.d LW₀ M L' γ v hA.monoW (hMv _) (hL'v _)`.

Establish `h1 : Moves J.W 1 LV LV (· = v)` using `fun y _ => by`. Rewrite using `[show mt J.W 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.one_mulVec]`. Establish `hf' : Vac ψ J.W B.V LV L' (· = v) (s.om (1, B.d.emb0 γ) f)` using `((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v) (fun w hw => hw ▸ hA.tame) f).2.2 hf 1 (B.d.emb0 γ) LV L' hA.sdV hL' h1 (hL'v _))`. Use `⟨M, hM, hMv _, hflat.Heisenberg₂.theta _ hf'.1, fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Establish `hu2 : 2 • u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v)` using `nsmul_mem hu 2`.

Rewrite using `[← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu2), map_nsmul, map_nsmul]`. Rewrite using `[hf'.2.1 _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu)]`. Rewrite using `[← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)]`. Rewrite using `[hf'.2.2 e he _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu) (wittExt_wittInc_isHalf J B hh)]`.
-/
theorem GlobalTheory.FinPl.movedVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ v hA _ f hf γ _
  have hflat : IsFlatFB s (· = v) (flatFB s) := (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V₀ LW₀ hA.sdW₀).1 γ
  obtain ⟨L', hL', hL'v⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).1 (B.d.emb0 γ)
  have hmono : MonoAt B.d L' M v :=
    (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).2 B.V₀ σ B.d LW₀ M L' γ v hA.monoW (hMv _) (hL'v _)
  have h1 : Moves J.W 1 LV LV (· = v) := fun y _ => by
    rw [show mt J.W 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.one_mulVec]
  have hf' : Vac ψ J.W B.V LV L' (· = v) (s.om (1, B.d.emb0 γ) f) :=
    ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v)
      (fun w hw => hw ▸ hA.tame) f).2.2 hf 1 (B.d.emb0 γ) LV L' hA.sdV hL' h1 (hL'v _))
  refine ⟨M, hM, hMv _, hflat.Heisenberg₂.theta _ hf'.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu2 : 2 • u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v) := nsmul_mem hu 2
    rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu2), map_nsmul, map_nsmul]
    rw [hf'.2.1 _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu)]
  · rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)]
    rw [hf'.2.2 e he _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu) (wittExt_wittInc_isHalf J B hh)]

end
