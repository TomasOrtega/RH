import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep

open MeasureTheory GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

/- English proof (translation)
Set `T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ)` to `LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w)) (fun ℓ₁ ℓ₂ w => by funext k; simp) (fun a ℓ w => by funext k; simp) (fun ℓ w₁ w₂ => by funext k; simp) (fun a ℓ w => by funext k; simp)`. Establish `hle : coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T)`. Unfold `coeffSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `f ⟨ℓ, w, rfl⟩`.

Conclude with `⟨ℓ ⊗ₜ w, by simp [T]⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_coeffs {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  let T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w))
      (fun ℓ₁ ℓ₂ w => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
      (fun ℓ w₁ w₂ => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
  have hle : coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T) := by
    unfold coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, by simp [T]⟩
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Set `E : K → Module.Dual ℂ A` to `fun k => (LinearMap.proj k).comp A.subtype`. Establish `htop : Submodule.span ℂ (Set.range E) = ⊤`. Establish `h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `f hf`.

Rewrite `hf` using `[Submodule.mem_dualCoannihilator]`. Rewrite using `[Submodule.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Establish `h` using `hf (E k) (Submodule.subset_span ⟨k, rfl⟩)`.

Simplify `h` using `[E]`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0, Submodule.dualAnnihilator_bot]`. Take `⟨b, hbsub, hbspan, hbli⟩` from `exists_linearIndependent ℂ (Set.range E)`. Establish `hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A))`. Rewrite using `[Subtype.range_coe, hbspan, htop]`.

Set `B : Module.Basis b ℂ (Module.Dual ℂ A)` to `Module.Basis.mk hbli hbtop`. Use `haveI : Finite b := hbli.finite`. Use `letI : Fintype b := Fintype.ofFinite b`. Establish `hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A)` using `fun i => hbsub i.2`. Use `choose p hpE using hp`.

Set `a : b → A` to `fun i => (Module.evalEquiv ℂ A).symm (B.coord i)`. Use `⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩` and prove the remaining obligations. Introduce `f hf k`. Establish `key` using `B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)`. Establish `key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i`.

Apply `(Module.evalEquiv ℂ A).injective` to reduce the goal to its premises. Use `conv_lhs => rw [← key]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]`. Establish `hk` using `congrArg (fun g : A => (g : K → ℂ) k) key2`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk`. Rewrite using `[hk]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hBi : B i = (i : Module.Dual ℂ A)` using `by simp [B]`. Rewrite using `[hBi, ← hpE i]`.

Both sides reduce to the same expression.
-/
theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → K) (a : ι → K → ℂ), (∀ i, a i ∈ A) ∧
      ∀ f ∈ A, ∀ k, f k = ∑ i, f (p i) * a i k := by
  classical
  let E : K → Module.Dual ℂ A := fun k => (LinearMap.proj k).comp A.subtype
  have htop : Submodule.span ℂ (Set.range E) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      funext k
      have h := hf (E k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [E] using h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range E)
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A)) := by
    rw [Subtype.range_coe, hbspan, htop]
  let B : Module.Basis b ℂ (Module.Dual ℂ A) := Module.Basis.mk hbli hbtop
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A) := fun i => hbsub i.2
  choose p hpE using hp
  let a : b → A := fun i => (Module.evalEquiv ℂ A).symm (B.coord i)
  refine ⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩
  intro f hf k
  have key := B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)
  have key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i := by
    apply (Module.evalEquiv ℂ A).injective
    conv_lhs => rw [← key]
    rw [map_sum]
    simp only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hk := congrArg (fun g : A => (g : K → ℂ) k) key2
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  rw [hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBi : B i = (i : Module.Dual ℂ A) := by simp [B]
  rw [hBi, ← hpE i]
  rfl

/- English proof (translation)
Introduce `D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc`. Establish `hst` using `GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V) hW`. Take `⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩` from `hst.1 T`. Use `haveI := hμ`. Establish `hcI` using `hc μ 𝓕 hμ h𝓕 h1`.

Use `haveI := finiteDimensional_coeffs ρ`. Take `⟨ι, _, p, a, ha, hrep⟩` from `exists_interp (coeffSpan ρ)`. Establish `hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T)`. Take `⟨K, hK, hKc⟩` from `hcoc`. Use `⟨K, hK, fun n => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hγK⟩` from `hKc n`. Use `⟨γ, ?_, hγK⟩` and prove the remaining obligations. Rewrite using `[Subgroup.inf_subgroupOf_right]`. Conclude with `hγ`. Establish `h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf (unip D.sp.cm.sig V.gram X T)) 𝓕 μ`.

Rewrite using `[Subgroup.inf_subgroupOf_right]`. Conclude with `h𝓕`. Use `haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance`. Use `haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) := DiscreteTopology.of_subset hdQ (fun y hy => hy.1)`. Establish `hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ`.

Introduce `g`. Conclude with `GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕' (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g`. Introduce `x`. Establish `hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i`. Use function extensionality and compare the values at `k`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hcI (x * kAt θ V τ e P k)]`. Establish `hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) = ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k`. Introduce `u`.

Establish `h` using `hrep _ (hty ((u : GA D V) * x)) k`. Simplify `h` using `[mul_assoc]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_mul_const, hcI]`. Rewrite using `[hfun]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)`.
-/
theorem hasTypeAt_of_isConstAlong : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  intro D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc
  classical
  have hst := GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) hW
  obtain ⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩ := hst.1 T
  haveI := hμ
  have hcI := hc μ 𝓕 hμ h𝓕 h1
  haveI := finiteDimensional_coeffs ρ
  obtain ⟨ι, _, p, a, ha, hrep⟩ := exists_interp (coeffSpan ρ)
  have hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T) := by
    obtain ⟨K, hK, hKc⟩ := hcoc
    refine ⟨K, hK, fun n => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKc n
    refine ⟨γ, ?_, hγK⟩
    rw [Subgroup.inf_subgroupOf_right]
    exact hγ
  have h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf
      (unip D.sp.cm.sig V.gram X T)) 𝓕 μ := by
    rw [Subgroup.inf_subgroupOf_right]
    exact h𝓕
  haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance
  haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) :=
    DiscreteTopology.of_subset hdQ (fun y hy => hy.1)
  have hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ := by
    intro g
    exact GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕'
      (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g
  intro x
  have hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcI (x * kAt θ V τ e P k)]
    have hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) =
        ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k := by
      intro u
      have h := hrep _ (hty ((u : GA D V) * x)) k
      simpa [mul_assoc] using h
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, hcI]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep
