import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RestScalar
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphRank
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
The claim follows from `map_smul (π γ) d x`.
-/
private theorem rep_smul (π : UnitaryRep G H) (γ : G) (d : ℂ) (x : H) : π γ (d • x) = d • π γ x :=
  map_smul (π γ) d x

/- English proof (translation)
Rewrite using `[UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, h₁, h₂, e₂, h₃, rep_smul, map_smul, e₃, rep_smul, rep_smul, smul_smul]`.
-/
private theorem cut_abs (π : UnitaryRep G H) (P T : H →L[ℂ] H) {x y z : G} {q : H} {c c' : ℂ}
    (h₁ : ∀ v, P (π x v) = π x (P v)) (h₂ : ∀ v, P (π y v) = π y (P v)) (h₃ : ∀ v, T (π x v) = π x (T v))
    (e₂ : P (π z q) = c • q) (e₃ : T (π y q) = c' • q) : T (P (π (x * (y * z)) q)) = (c * c') • π x q := by
  rw [UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, h₁, h₂, e₂, h₃, rep_smul, map_smul, e₃, rep_smul, rep_smul, smul_smul]

/- English proof (translation)
Establish `hcl` using `hA.submodule_topologicalClosure_eq`. Establish `hP : prj A x ∈ A`. Establish `: prj A x ∈ A.topologicalClosure` using `Submodule.starProjection_apply_mem _ x`. Rewrite `this` using `[hcl]`. Then use the resulting hypothesis. Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_` and prove the remaining obligations.

Rewrite using `[hcl]`. Conclude with `h₁ _ hP`. Introduce `f hf`. Rewrite `hf` using `[hcl]`. Establish `e : f = π γ (π γ⁻¹ f)`.

Rewrite using `[← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply]`. Rewrite using `[e, ← map_sub, UnitaryRep.inner_map_map]`. Conclude with `Submodule.starProjection_inner_eq_zero (K := A.topologicalClosure) x _ (by rw [hcl]; exact h₂ f hf)`.
-/
private theorem prj_comm (π : UnitaryRep G H) {A : Submodule ℂ H} (hA : IsClosed (A : Set H)) (γ : G)
    (h₁ : ∀ v ∈ A, π γ v ∈ A) (h₂ : ∀ v ∈ A, π γ⁻¹ v ∈ A) (x : H) : prj A (π γ x) = π γ (prj A x) := by
  have hcl := hA.submodule_topologicalClosure_eq
  have hP : prj A x ∈ A := by
    have : prj A x ∈ A.topologicalClosure := Submodule.starProjection_apply_mem _ x
    rwa [hcl] at this
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [hcl]
    exact h₁ _ hP
  · intro f hf
    rw [hcl] at hf
    have e : f = π γ (π γ⁻¹ f) := by
      rw [← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply]
    rw [e, ← map_sub, UnitaryRep.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero (K := A.topologicalClosure) x _ (by rw [hcl]; exact h₂ f hf)

/- English proof (translation)
Set `S : Submodule ℂ H` to `Submodule.span ℂ (Set.range fun γ => π γ q)`. Establish `hSinv : π.IsInvariant S`. Introduce `g v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨γ, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `S.add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `S.smul_mem a hx`. Establish `hSτ : S ≤ τ` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨γ, rfl⟩`. Conclude with `hτi _ _ hqτ)`. Establish `hclτ : S.topologicalClosure ≤ τ` using `Submodule.topologicalClosure_minimal _ hSτ hτc`. Establish `hqS : q ∈ S.topologicalClosure` using `S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)`. Establish `hSeq : S.topologicalClosure = τ`.

Break down `hirr _ hclτ S.isClosed_topologicalClosure (fun g v hv => hSinv.topologicalClosure g v hv) with h0 | h1` into its components or cases. It suffices to derive a contradiction. Rewrite `hqS` using `[h0]`. Conclude with `hq0 (by simpa using hqS)`. Conclude with `h1`.

Establish `hES : ∀ x ∈ S, E x ∈ Q`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨γ, rfl⟩` from `hx`.

Conclude with `key γ`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Q.add_mem hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[map_smul]`. Conclude with `Q.smul_mem a hx`. Establish `hvc : v ∈ closure (S : Set H)`. Establish `: v ∈ S.topologicalClosure` using `by rw [hSeq]; exact hv`.

Conclude with `this`. Establish `hm` using `map_mem_closure E.continuous hvc (t := (Q : Set H)) (fun x hx => hES x hx)`. Rewrite `hm` using `[hQc.closure_eq, hE]`. Conclude with `hm`.
-/
private theorem mem_of_translates (π : UnitaryRep G H) {τ Q : Submodule ℂ H} (hτc : IsClosed (τ : Set H))
    (hτi : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hQc : IsClosed (Q : Set H)) (E : H →L[ℂ] H) {q : H} (hqτ : q ∈ τ) (hq0 : q ≠ 0) (key : ∀ γ, E (π γ q) ∈ Q)
    {v : H} (hv : v ∈ τ) (hE : E v = v) : v ∈ Q := by
  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ q)
  have hSinv : π.IsInvariant S := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact S.smul_mem a hx
  have hSτ : S ≤ τ := Submodule.span_le.2 (by
    rintro _ ⟨γ, rfl⟩
    exact hτi _ _ hqτ)
  have hclτ : S.topologicalClosure ≤ τ := Submodule.topologicalClosure_minimal _ hSτ hτc
  have hqS : q ∈ S.topologicalClosure :=
    S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
  have hSeq : S.topologicalClosure = τ := by
    rcases hirr _ hclτ S.isClosed_topologicalClosure (fun g v hv => hSinv.topologicalClosure g v hv) with h0 | h1
    · exfalso
      rw [h0] at hqS
      exact hq0 (by simpa using hqS)
    · exact h1
  have hES : ∀ x ∈ S, E x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      exact key γ
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Q.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Q.smul_mem a hx
  have hvc : v ∈ closure (S : Set H) := by
    have : v ∈ S.topologicalClosure := by rw [hSeq]; exact hv
    exact this
  have hm := map_mem_closure E.continuous hvc (t := (Q : Set H)) (fun x hx => hES x hx)
  rw [hQc.closure_eq, hE] at hm
  exact hm

end Abs

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

/- English proof (translation)
Use `haveI := hI.haar.prob`. Use `haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1`. Establish `hc : Continuous fun k : archCompact K n => e k • rightRegularRep (Gam K n) μ (arc1 k) v` using `hI.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp (levLaws (K := K) n ∅).2.2.2.1)`. Conclude with `hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
private theorem integrable_orbit {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) (v : L2 μ) :
    Integrable (fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) κ := by
  haveI := hI.haar.prob
  haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1
  have hc : Continuous fun k : archCompact K n => e k • rightRegularRep (Gam K n) μ (arc1 k) v :=
    hI.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp (levLaws (K := K) n ∅).2.2.2.1)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Use `haveI := hI.haar.prob`. Use `haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hI.cont.continuousOn`. Set `T : L2 μ →ₗ[ℂ] L2 μ` to `{ toFun := pOp μ κ e map_add' := fun x y => by`. Unfold `pOp`.

Rewrite using `[← integral_add (integrable_orbit μ hI x) (integrable_orbit μ hI y)]`. Simplify using `only [map_add, smul_add]`. Use the proof step `map_smul' := fun c x => by`. Unfold `pOp`. Rewrite using `[RingHom.id_apply, ← integral_smul]`.

Simplify using `only [map_smul, smul_comm c] }`. Use `⟨T.mkContinuous C fun v => ?_, fun v => rfl⟩` and prove the remaining obligations. Establish `h` using `norm_integral_le_of_norm_le_const (μ := κ) (C := C * ‖v‖) (f := fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) (Eventually.of_forall fun k => by`. Rewrite using `[norm_smul]`. Establish `h1 : ‖rightRegularRep (Gam K n) μ (arc1 k) v‖ = ‖v‖` using `by simp`.

Rewrite using `[h1]`. Conclude with `mul_le_mul_of_nonneg_right (hC k (Set.mem_univ k)) (norm_nonneg v))`. Simplify `h` using `[pOp, T]`.
-/
private theorem exists_clm {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) :
    ∃ T : L2 μ →L[ℂ] L2 μ, ∀ v, T v = pOp μ κ e v := by
  haveI := hI.haar.prob
  haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hI.cont.continuousOn
  let T : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := pOp μ κ e
      map_add' := fun x y => by
        unfold pOp
        rw [← integral_add (integrable_orbit μ hI x) (integrable_orbit μ hI y)]
        simp only [map_add, smul_add]
      map_smul' := fun c x => by
        unfold pOp
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm c] }
  refine ⟨T.mkContinuous C fun v => ?_, fun v => rfl⟩
  have h := norm_integral_le_of_norm_le_const (μ := κ) (C := C * ‖v‖)
    (f := fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) (Eventually.of_forall fun k => by
      rw [norm_smul]
      have h1 : ‖rightRegularRep (Gam K n) μ (arc1 k) v‖ = ‖v‖ := by simp
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hC k (Set.mem_univ k)) (norm_nonneg v))
  simpa [pOp, T] using h

/- English proof (translation)
Unfold `pOp`. Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ (integrable_orbit μ hI v)]`. Use `integral_congr_ae (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only [map_smul]`. Rewrite using `[← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ((levLaws (K := K) n ∅).2.2.1 k h).eq]`.
-/
private theorem pOp_fin {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) (h : FA K n) (v : L2 μ) :
    pOp μ κ e (rightRegularRep (Gam K n) μ (fin1 h) v) = rightRegularRep (Gam K n) μ (fin1 h) (pOp μ κ e v) := by
  unfold pOp
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_orbit μ hI v)]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [map_smul]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ((levLaws (K := K) n ∅).2.2.1 k h).eq]

/- English proof (translation)
Simplify using `only [sphOff, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply, Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]`.
-/
private theorem mem_sph {P : Finset (Pl K)} {v : L2 μ} :
    v ∈ sphOff μ P ↔ ∀ u ∉ P, ∀ x ∈ GLnLocal.integralGL (u.adicCompletion K) n, rhoL μ u x v = v := by
  simp only [sphOff, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

/- English proof (translation)
Establish `h : (sphOff μ P : Set (L2 μ)) = ⋂ u ∈ {u | u ∉ P}, ⋂ x ∈ (GLnLocal.integralGL (u.adicCompletion K) n : Set _), {v | rhoL μ u x v = v}`. Use extensionality with `v`. Simplify using `[mem_sph]`. Rewrite using `[h]`. Conclude with `isClosed_biInter fun u _ => isClosed_biInter fun x _ => isClosed_eq (rhoL μ u x).continuous continuous_id`.
-/
private theorem closed_sph (P : Finset (Pl K)) : IsClosed (sphOff μ P : Set (L2 μ)) := by
  have h : (sphOff μ P : Set (L2 μ)) =
      ⋂ u ∈ {u | u ∉ P}, ⋂ x ∈ (GLnLocal.integralGL (u.adicCompletion K) n : Set _), {v | rhoL μ u x v = v} := by
    ext v
    simp [mem_sph]
  rw [h]
  exact isClosed_biInter fun u _ => isClosed_biInter fun x _ => isClosed_eq (rhoL μ u x).continuous continuous_id

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_sph]`. Introduce `u hu x hx`. Establish `h` using `hv u hu x hx`. Use `show rightRegularRep (Gam K n) μ (fin1 (AdelicGLn.localEmbedding u x)) _ = _`. Rewrite using `[← UnitaryRep.map_mul_apply, ← (hγ u hu x).eq, UnitaryRep.map_mul_apply]`.

Conclude with `congrArg _ h`.
-/
private theorem sph_stable {P : Finset (Pl K)} (γ : G1 K n)
    (hγ : ∀ u ∉ P, ∀ x : Gw n u, Commute γ (fin1 (AdelicGLn.localEmbedding u x))) {v : L2 μ} (hv : v ∈ sphOff μ P) :
    rightRegularRep (Gam K n) μ γ v ∈ sphOff μ P := by
  rw [mem_sph] at hv ⊢
  intro u hu x hx
  have h := hv u hu x hx
  show rightRegularRep (Gam K n) μ (fin1 (AdelicGLn.localEmbedding u x)) _ = _
  rw [← UnitaryRep.map_mul_apply, ← (hγ u hu x).eq, UnitaryRep.map_mul_apply]
  exact congrArg _ h

/- English proof (translation)
Assemble the required witnesses or components as `⟨hτ.le, hτ.closed, fun g v hv => hτ.inv g v hv, hτ.ne, fun V' hle hc hi => hτ.irr V' hle hc fun g v hv => hi g v hv⟩`.
-/
private theorem summand_of {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) : IsSummand μ τ :=
  ⟨hτ.le, hτ.closed, fun g v hv => hτ.inv g v hv, hτ.ne, fun V' hle hc hi => hτ.irr V' hle hc fun g v hv => hi g v hv⟩

/- English proof (translation)
Establish `hCO : ∀ u : Pl K, CO (GLnLocal.integralGL (u.adicCompletion K) n)` using `fun u => ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩`. Establish `hChr : ∀ u : Pl K, UpperTheory.ConvolutionTheory.L1.IsChr (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ)` using `fun u => ⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ _ => by simp⟩`. Establish `hA : (⨅ u ∉ (P : Set (Pl K)), UpperTheory.ConvolutionTheory.L1.eigL μ u (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ)) = sphOff μ P`. Unfold `sphOff`. Simplify using `only [Finset.mem_coe]`.

Conclude with `iInf_congr fun u => iInf_congr fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic K n μ u _ 1 (hCO u) (hChr u)).2.1`. Take `⟨c, hc⟩` from `UpperTheory.ConvolutionTheory.L1.restScalar K n μ τ (summand_of μ hτ) (fun u => GLnLocal.integralGL (u.adicCompletion K) n) (fun u => (1 : Gw n u → ℂ)) (fun u => ⟨hCO u, hChr u⟩) (Eventually.of_forall fun _ => ⟨rfl, rfl⟩) (P : Set (Pl K)) (fun u _ => UpperTheory.ConvolutionTheory …`. Simplify using `only [hA] at hc`. Conclude with `⟨c, fun v hv hs => hc v ⟨hv, hs⟩⟩`.
-/
private theorem rest_sph {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) (P : Finset (Pl K)) (h : FA K n)
    (hh : ∀ u ∈ P, GM.cf u h = 1) :
    ∃ c : ℂ, ∀ v ∈ τ, v ∈ sphOff μ P → prj (sphOff μ P) (rhoF μ h v) = c • v := by
  have hCO : ∀ u : Pl K, CO (GLnLocal.integralGL (u.adicCompletion K) n) := fun u =>
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
  have hChr : ∀ u : Pl K, UpperTheory.ConvolutionTheory.L1.IsChr (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ) := fun u =>
    ⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ _ => by simp⟩
  have hA : (⨅ u ∉ (P : Set (Pl K)), UpperTheory.ConvolutionTheory.L1.eigL μ u (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ)) =
      sphOff μ P := by
    unfold sphOff
    simp only [Finset.mem_coe]
    exact iInf_congr fun u => iInf_congr fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic K n μ u _ 1 (hCO u) (hChr u)).2.1
  obtain ⟨c, hc⟩ := UpperTheory.ConvolutionTheory.L1.restScalar K n μ τ (summand_of μ hτ) (fun u => GLnLocal.integralGL (u.adicCompletion K) n)
    (fun u => (1 : Gw n u → ℂ)) (fun u => ⟨hCO u, hChr u⟩) (Eventually.of_forall fun _ => ⟨rfl, rfl⟩) (P : Set (Pl K))
    (fun u _ => UpperTheory.ConvolutionTheory.L1.sphRank K n μ τ (summand_of μ hτ) u) h (fun u hu => hh u hu)
  simp only [hA] at hc
  exact ⟨c, fun v hv hs => hc v ⟨hv, hs⟩⟩

/- English proof (translation)
The claim follows from `(MultiplicityOne.finProj_mul_archProj_comm h (a : ArchUnits K n)).symm`.
-/
private theorem comm_arch (a : archGroup K n) (h : FA K n) : Commute (archP K n a) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h (a : ArchUnits K n)).symm

/- English proof (translation)
Establish `h : fin1 (x * y) = fin1 x * fin1 y` using `map_mul (MultiplicityOne.finProj K n) x y`. Rewrite using `[h, ← mul_assoc, ← mul_assoc, (comm_arch a x).eq]`.
-/
private theorem grp_split (a : archGroup K n) (x y : FA K n) :
    archP K n a * fin1 (x * y) = fin1 x * (archP K n a * fin1 y) := by
  have h : fin1 (x * y) = fin1 x * fin1 y := map_mul (MultiplicityOne.finProj K n) x y
  rw [h, ← mul_assoc, ← mul_assoc, (comm_arch a x).eq]

/- English proof (translation)
Establish `h1 : Commute (ι g) (AdelicGLn.localEmbedding u x)` using `((embEx (K := K) n w hw).2 ι hι).2.2.2.2.1 g _ fun i => by`. Use `(UpperTheory.ConvolutionTheory.Tf.locEmb K n u).2.2.1 (w i) (fun e => hu ?_) x` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨i, Finset.mem_univ _, e⟩`. Conclude with `h1.map (MultiplicityOne.finProj K n)`.
-/
private theorem comm_emb {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι)
    (g : GS n w) {u : Pl K} (hu : u ∉ im w) (x : Gw n u) : Commute (fin1 (ι g)) (fin1 (AdelicGLn.localEmbedding u x)) := by
  have h1 : Commute (ι g) (AdelicGLn.localEmbedding u x) :=
    ((embEx (K := K) n w hw).2 ι hι).2.2.2.2.1 g _ fun i => by
      refine (UpperTheory.ConvolutionTheory.Tf.locEmb K n u).2.2.1 (w i) (fun e => hu ?_) x
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, e⟩
  exact h1.map (MultiplicityOne.finProj K n)

/- English proof (translation)
The claim follows from `prj_comm _ (closed_sph μ P) _ (fun _ hv => sph_stable μ _ (fun _ _ _ => comm_arch _ _) hv) (fun _ hv => sph_stable μ _ (fun _ _ _ => (comm_arch _ _).inv_left) hv) x`.
-/
private theorem prj_arch (P : Finset (Pl K)) (a : archGroup K n) (x : L2 μ) :
    prj (sphOff μ P) (rightRegularRep (Gam K n) μ (archP K n a) x) =
      rightRegularRep (Gam K n) μ (archP K n a) (prj (sphOff μ P) x) :=
  prj_comm _ (closed_sph μ P) _ (fun _ hv => sph_stable μ _ (fun _ _ _ => comm_arch _ _) hv)
    (fun _ hv => sph_stable μ _ (fun _ _ _ => (comm_arch _ _).inv_left) hv) x

/- English proof (translation)
The claim follows from `prj_comm _ (closed_sph μ _) _ (fun _ hv => sph_stable μ _ (fun _ hu _ => comm_emb hw hι g hu _) hv) (fun _ hv => sph_stable μ _ (fun _ hu _ => (comm_emb hw hι g hu _).inv_left) hv) x`.
-/
private theorem prj_emb {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι)
    (g : GS n w) (x : L2 μ) :
    prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 (ι g)) x) =
      rightRegularRep (Gam K n) μ (fin1 (ι g)) (prj (sphOff μ (im w)) x) :=
  prj_comm _ (closed_sph μ _) _ (fun _ hv => sph_stable μ _ (fun _ hu _ => comm_emb hw hι g hu _) hv)
    (fun _ hv => sph_stable μ _ (fun _ hu _ => (comm_emb hw hι g hu _).inv_left) hv) x

/- English proof (translation)
The claim follows from `cut_abs (rightRegularRep (Gam K n) μ) (prj (sphOff μ (im w))) T (prj_emb μ hw hι g) (prj_arch μ _ a) (fun v => by rw [hT, hT, pOp_fin μ hI]) e2 ((hT _).trans e3)`.
-/
private theorem cut_step {κ : Measure (archCompact K n)} {p : archCompact K n → ℂ} (hI : IdemA κ p) {r : ℕ} {w : Fin r → Pl K}
    {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι) (T : L2 μ →L[ℂ] L2 μ) (hT : ∀ v, T v = pOp μ κ p v)
    {q : L2 μ} (g : GS n w) (a : archGroup K n) (h' : FA K n) (c c' : ℂ)
    (e2 : prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 h') q) = c • q)
    (e3 : pOp μ κ p (rightRegularRep (Gam K n) μ (archP K n a) q) = c' • q) :
    T (prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 (ι g) * (archP K n a * fin1 h')) q)) =
      (c * c') • rhoF μ (ι g) q :=
  cut_abs (rightRegularRep (Gam K n) μ) (prj (sphOff μ (im w))) T (prj_emb μ hw hι g) (prj_arch μ _ a)
    (fun v => by rw [hT, hT, pOp_fin μ hI]) e2 ((hT _).trans e3)

/- English proof (translation)
Take `⟨A₀, u, hγ⟩` from `MultiplicityOne.exists_archProj_mul_finProj γ`. Take `⟨g, h', hu, hh'⟩` from `((embEx (K := K) n w hw).2 ι hι).2.2.2.1 u`. Take `⟨c, hc⟩` from `rest_sph μ hτ (im w) h' (fun v hv => by`. Take `⟨i, -, hi⟩` from `Finset.mem_image.1 hv`. Rewrite using `[← hi]`.

Conclude with `hh' i)`. Take `⟨c', hc'⟩` from `hR.2.2 ⟨A₀, trivial⟩`. Establish `e1 : γ = fin1 (ι g) * (archP K n ⟨A₀, trivial⟩ * fin1 h')`. Rewrite using `[← grp_split, ← hu]`. Conclude with `hγ.symm`.

Use `⟨g, c * c', ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `cut_step μ hR.1 hw hι T hT g _ h' c c' (hc q hq.1 hq.2.2) (hc' q hq.1 hq.2.1)`.
-/
private theorem cut_translate {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) {κ : Measure (archCompact K n)}
    {p : archCompact K n → ℂ} (hR : RankInf μ τ κ p) {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n}
    (hw : Function.Injective w) (hι : IsEmb w ι) (T : L2 μ →L[ℂ] L2 μ) (hT : ∀ v, T v = pOp μ κ p v) {q : L2 μ}
    (hq : InH μ τ κ p (im w) q) (γ : G1 K n) :
    ∃ (g : GS n w) (c : ℂ), T (prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ γ q)) = c • rhoF μ (ι g) q := by
  obtain ⟨A₀, u, hγ⟩ := MultiplicityOne.exists_archProj_mul_finProj γ
  obtain ⟨g, h', hu, hh'⟩ := ((embEx (K := K) n w hw).2 ι hι).2.2.2.1 u
  obtain ⟨c, hc⟩ := rest_sph μ hτ (im w) h' (fun v hv => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    rw [← hi]
    exact hh' i)
  obtain ⟨c', hc'⟩ := hR.2.2 ⟨A₀, trivial⟩
  have e1 : γ = fin1 (ι g) * (archP K n ⟨A₀, trivial⟩ * fin1 h') := by
    rw [← grp_split, ← hu]
    exact hγ.symm
  refine ⟨g, c * c', ?_⟩
  rw [e1]
  exact cut_step μ hR.1 hw hι T hT g _ h' c c' (hc q hq.1 hq.2.2) (hc' q hq.1 hq.2.1)

end SlopeTestRemainingChoices

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

/- English proof (translation)
Introduce `K _ _ _ μ _ τ κ p hτ hR r w ι hw hι Q hQc hQ hQι`. Distinguish the cases in `hbot : Q = ⊥`. Conclude with `Or.inl hbot`. Use `right`. Take `⟨q, hqQ, hq0⟩` from `Q.ne_bot_iff.1 hbot`.

Take `⟨T, hT⟩` from `exists_clm μ hR.1`. Introduce `v hv`. Use `mem_of_translates (rightRegularRep (Gam K 2) μ) hτ.closed hτ.inv hτ.irr hQc (T ∘L prj (sphOff μ (im w))) (hQ q hqQ).1 hq0 (fun γ => ?_) hv.1 ?_` and prove the remaining obligations. Take `⟨g, c, h⟩` from `cut_translate μ hτ hR hw hι T hT (hQ q hqQ) γ`. Rewrite using `[ContinuousLinearMap.comp_apply, h]`.

Conclude with `Q.smul_mem c (hQι g q hqQ)`. Establish `hfix : prj (sphOff μ (im w)) v = v` using `Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2.2)`. Rewrite using `[ContinuousLinearMap.comp_apply, hfix, hT, hv.2.1]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xTop :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → RankInf μ τ κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → ∀ Q : Submodule ℂ (L2 μ), IsClosed (Q : Set (L2 μ)) →
      (∀ v ∈ Q, InH μ τ κ p (im w) v) → (∀ g, ∀ v ∈ Q, rhoF μ (ι g) v ∈ Q) → Q = ⊥ ∨ ∀ v, InH μ τ κ p (im w) v → v ∈ Q := by
  intro K _ _ _ μ _ τ κ p hτ hR r w ι hw hι Q hQc hQ hQι
  by_cases hbot : Q = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨q, hqQ, hq0⟩ := Q.ne_bot_iff.1 hbot
  obtain ⟨T, hT⟩ := exists_clm μ hR.1
  intro v hv
  refine mem_of_translates (rightRegularRep (Gam K 2) μ) hτ.closed hτ.inv hτ.irr hQc (T ∘L prj (sphOff μ (im w)))
    (hQ q hqQ).1 hq0 (fun γ => ?_) hv.1 ?_
  · obtain ⟨g, c, h⟩ := cut_translate μ hτ hR hw hι T hT (hQ q hqQ) γ
    rw [ContinuousLinearMap.comp_apply, h]
    exact Q.smul_mem c (hQι g q hqQ)
  · have hfix : prj (sphOff μ (im w)) v = v :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2.2)
    rw [ContinuousLinearMap.comp_apply, hfix, hT, hv.2.1]
