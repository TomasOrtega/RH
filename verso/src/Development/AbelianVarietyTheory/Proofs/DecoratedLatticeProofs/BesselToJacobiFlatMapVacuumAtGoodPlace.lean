import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨β, hβi, hβ, c, hc, x, hx, rfl⟩` from `hz`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Use `AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero`. Establish `: (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz'`.

Establish `: (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) = (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i)`. Use function extensionality and compare the values at `i`. Simplify using `[mul_add]`. Rewrite using `[this]`. Conclude with `add_mem hz hz'`.

Consider the case `neg z _ hz`. Establish `: (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) = -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `neg_mem hz`.
-/
theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

/- English proof (translation)
Use `(hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : (d.pX *ᵥ (d.j0 *ᵥ u)) i = 0`. Rewrite using `[Matrix.mulVec_mulVec, HypDec.pX_j0, Matrix.zero_mulVec]`. Both sides reduce to the same expression. Establish `: colMul d.jX i ((d.pX *ᵥ (d.j0 *ᵥ u)) i) = 0`.

Use function extensionality and compare the values at `k`. Simplify using `[colMul, h0]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `h0 : (d.pY *ᵥ (d.j0 *ᵥ u)) i = 0`.

Rewrite using `[Matrix.mulVec_mulVec, HypDec.pY_j0, Matrix.zero_mulVec]`. Both sides reduce to the same expression. Establish `: colMul d.jY i ((d.pY *ᵥ (d.j0 *ᵥ u)) i) = 0`. Use function extensionality and compare the values at `k`. Simplify using `[colMul, h0]`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Rewrite using `[Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec]`. Conclude with `hu`.
-/
theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T₀.rank → AE D} (hu : u ∈ latV T₀ L₀ (· = v)) :
    d.j0 *ᵥ u ∈ latV T L (· = v) := by
  refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h0 : (d.pX *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jX i ((d.pX *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · have h0 : (d.pY *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jY i ((d.pY *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec]; exact hu

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨β, hβi, hβ, a, ha, x, hx, rfl⟩` from `hz`. Use `set u : Fin T₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu`. Establish `hu' : u ∈ latV T₀ L₀ (· = v)` using `AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩`.

Establish `heq : d.j0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.j0 *ᵥ u) k`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i))`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `smul_mem_latA ha (wittCoreInclusion_mem_latticeCompletionAtPlace d hm hu')`.

Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz' => rw [Matrix.mulVec_add]`. Conclude with `add_mem hz hz'`. Consider the case `neg z _ hz => rw [Matrix.mulVec_neg]`.

Conclude with `neg_mem hz`.
-/
theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T₀.rank → AE D} (hz : z ∈ latA T₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.j0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.j0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (wittCoreInclusion_mem_latticeCompletionAtPlace d hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

/- English proof (translation)
Establish `hx` using `GlobalTheory.FinPl.LatMem.latO_mxAt hw`. Use `(GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨fun i j => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply]`. Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`.

Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))`. Express the relevant statement in the definitionally equal form `(dT.j0 * w * dS.p0) *ᵥ y ∈ latA T LT (· = v)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.

Establish `h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v)` using `((hmS y).1 hy).2.2`. Conclude with `wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)`.
-/
theorem wittExt_wittInc_mem_completed_hom_lattice {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T₀}
    (hw : w ∈ latO S₀ T₀ (LS₀ : Set _) (LT₀ : Set _) (· = v)) :
    dS.ext0 T (dT.inc0 S₀ w) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · change (dT.j0 * w * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

/- English proof (translation)
Introduce `i j`. Rewrite using `[HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `conv_rhs => rw [← hw k l]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wittExt_wittInc_isHalf {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {e : AE D}
    {w : WO S₀ T₀} (hw : IsHalf e w) : IsHalf e (dS.ext0 T (dT.inc0 S₀ w)) := by
  intro i j
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hw k l]
  ring

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

/- English proof (translation)
Introduce `D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf`. Take `⟨hθ, h2, hh⟩` from `hf`. Establish `hmem : ∀ w ∈ latO B.V₀ J.W₀ (LV₀ : Set _) (LW₀ : Set _) (· = v), B.d.ext0 J.W (J.d.inc0 B.V₀ w) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v)` using `fun w hw => wittExt_wittInc_mem_completed_hom_lattice B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hw`. Use `⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩` and prove the remaining obligations. Establish `hx : MxAt (· = v) (2 • w)` using `fun i j => by`.

Rewrite using `[Matrix.smul_apply]`. Conclude with `nsmul_mem (GlobalTheory.FinPl.LatMem.latO_mxAt hw i j) 2`. Rewrite using `[← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]`. Rewrite using `[← h𝔉.Heisenberg₂.core f hθ w (GlobalTheory.FinPl.LatMem.latO_mxAt hw), hh e he _ (hmem w hw) (wittExt_wittInc_isHalf B.d J.d hwe)]`.
-/
theorem flat_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf
  obtain ⟨hθ, h2, hh⟩ := hf
  have hmem : ∀ w ∈ latO B.V₀ J.W₀ (LV₀ : Set _) (LW₀ : Set _) (· = v),
      B.d.ext0 J.W (J.d.inc0 B.V₀ w) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) := fun w hw =>
    wittExt_wittInc_mem_completed_hom_lattice B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hw
  refine ⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩
  · have hx : MxAt (· = v) (2 • w) := fun i j => by
      rw [Matrix.smul_apply]
      exact nsmul_mem (GlobalTheory.FinPl.LatMem.latO_mxAt hw i j) 2
    rw [← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]
  · rw [← h𝔉.Heisenberg₂.core f hθ w (GlobalTheory.FinPl.LatMem.latO_mxAt hw),
      hh e he _ (hmem w hw) (wittExt_wittInc_isHalf B.d J.d hwe)]

end GlobalTheory.FinPl.VacFlat
