import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `(UpperTheory.Zero.LLC.Pr.adm k N V π hs hi).2 (KOne k (Fin N)) ?_ ?_` and prove the remaining obligations. Rewrite using `[← levelPre_bot]`. Conclude with `isOpen_levelPre _`. Rewrite using `[← levelPre_bot]`. Conclude with `isCompact_levelPre _`.
-/
private theorem fd_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
  refine (UpperTheory.Zero.LLC.Pr.adm k N V π hs hi).2 (KOne k (Fin N)) ?_ ?_
  · rw [← levelPre_bot]
    exact isOpen_levelPre _
  · rw [← levelPre_bot]
    exact isCompact_levelPre _

/- English proof (translation)
Introduce `x y`. Use `show LinearMap.trace ℂ _ (η (y⁻¹ * x * y)) = LinearMap.trace ℂ _ (η x)`. Rewrite using `[map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
private theorem isCl_trace {G : Type} [Group G] {r : ℕ} (η : Representation ℂ G (Fin r → ℂ)) :
    IsCl (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) := by
  intro x y
  show LinearMap.trace ℂ _ (η (y⁻¹ * x * y)) = LinearMap.trace ℂ _ (η x)
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]

/- English proof (translation)
Take `⟨c, hc, hcY⟩` from `hF F s d N hd`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[hcY Y (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) (isCl_trace η), h0, mul_zero]`.
-/
private theorem frob_step (hF : FrobL) {F : Type} [Field F] [Finite F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) (Y : ∀ i, GL (Fin (d i)) F → ℂ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ g, star (hcL (List.ofFn fun i => ⟨d i, Y i⟩) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0) :
    ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0 := by
  obtain ⟨c, hc, hcY⟩ := hF F s d N hd
  intro h0
  apply h
  rw [hcY Y (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) (isCl_trace η), h0, mul_zero]

/- English proof (translation)
Establish `key : ∀ p : parab F (stdBlocks d hd), LinearMap.trace ℂ (PiTensorProduct ℂ fun a => W a) (piTensor σ (leviProj F (stdBlocks d hd) p)) = ∏ i, Y i (leviProj F (stdBlocks d hd) p i)`. Introduce `p`. Rewrite using `[(hT s _ W σ).2]`. Conclude with `Finset.prod_congr rfl fun a _ => hY a _`. Unfold `Meets`.

Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype, key]`. Conclude with `h`.
-/
private theorem meets_parab (hT : TensTr) {F : Type} [Field F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) {W : Fin s → Type} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    [∀ a, FiniteDimensional ℂ (W a)] (σ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (W a))
    (Y : ∀ i, GL (Fin (d i)) F → ℂ) (hY : ∀ a γ, LinearMap.trace ℂ (W a) (σ a γ) = Y a γ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0) :
    Meets (η.comp (parab F (stdBlocks d hd)).subtype)
      (fun p => LinearMap.trace ℂ _ (((piTensor σ).comp (leviProj F (stdBlocks d hd))) p)) := by
  have key : ∀ p : parab F (stdBlocks d hd),
      LinearMap.trace ℂ (PiTensorProduct ℂ fun a => W a) (piTensor σ (leviProj F (stdBlocks d hd) p)) =
        ∏ i, Y i (leviProj F (stdBlocks d hd) p i) := by
    intro p
    rw [(hT s _ W σ).2]
    exact Finset.prod_congr rfl fun a _ => hY a _
  unfold Meets
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, key]
  exact h

/- English proof (translation)
Use `⟨f.toLinearMap ∘ₗ Ψ, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hΨ0` to reduce the goal to its premises. Use `LinearMap.ext fun x => hf ?_` and prove the remaining obligations. Use `LinearMap.congr_fun h0 x` as an intermediate fact.

Simplify using `using this`. Introduce `g x`. Use `LinearMap.congr_fun (f.isIntertwining' g) (Ψ x)` as an intermediate fact. Simplify `this` using `[hΨ]`.
-/
private theorem compose_map {G X U U' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] {ρ : Representation ℂ G U} {ρ' : Representation ℂ G U'}
    {η : Representation ℂ G X} (Ψ : X →ₗ[ℂ] U) (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f)
    (hΨ0 : Ψ ≠ 0) (hΨ : ∀ g x, Ψ (η g x) = ρ g (Ψ x)) :
    ∃ F : X →ₗ[ℂ] U', F ≠ 0 ∧ ∀ g x, F (η g x) = ρ' g (F x) := by
  refine ⟨f.toLinearMap ∘ₗ Ψ, ?_, ?_⟩
  · intro h0
    apply hΨ0
    refine LinearMap.ext fun x => hf ?_
    have := LinearMap.congr_fun h0 x
    simpa using this
  · intro g x
    have := LinearMap.congr_fun (f.isIntertwining' g) (Ψ x)
    simpa [hΨ] using this

/- English proof (translation)
Introduce `hMI hF hJD hTT hAvg hInd hTI`. Introduce `k _ _ _ _ _ θ N V _ _ π hs hi s x c hd hE hx T hT hP`. Take `⟨e⟩` from `hE`. Take `⟨r, η, hη⟩` from `hT`. Establish `hTη : T = fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)`.

Use function extensionality and compare the values at `g`. Rewrite using `[hη g]`. Both sides reduce to the same expression. Substitute `hTη` using the available equality. Establish `hJ : J θ (List.ofFn fun a => ((x a).fst, c a)) N = hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N`.

Rewrite using `[← JD_nil, (hJD 𝓀[k] θ).1]`. Simplify using `[List.map_ofFn, Function.comp_def]`. Establish `h1 : ∑ᶠ g, star (hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0`. Rewrite using `[← hJ]`. Conclude with `hP`.

Establish `h2` using `frob_step hF (d := fun a => (x a).fst) hd (fun i => cusp θ (x i).fst (c i)) η h1`. Use `haveI hfd : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) := fun a => fd_fixed _ (x a).snd.rep.smooth (x a).snd.rep.irr`. Establish `h3` using `meets_parab hTT hd (fun a => levelZero (x a).rep) (fun i => cusp θ (x i).fst (c i)) hx η h2`. Use `haveI := (hTT s _ _ (fun a => levelZero (x a).rep)).1`. Take `⟨ψ, hψ0, hψ⟩` from `((hMI _ _ _ _ _).1).1 h3`.

Take `⟨j, hj, hjx⟩` from `hTI k s (fun a => (x a).fst) _ (fun a => (x a).rep)`. Take `⟨Φ, ev, hΦ1, hΦ2, hΦ3⟩` from `hInd k N s (fun a => (x a).fst) hd _ _ _ _ j hj hjx`. Take `⟨Ψ, hΨ0, hΨ⟩` from `hAvg _ (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _ _ _ _ _ η Φ ev ψ hΦ1 hΦ2 hΦ3 hψ hψ0`. Establish `hinj : Function.Injective (levelZeroMap e.symm.toIntertwiningMap)`. Apply `levelZeroMap_injective` to reduce the goal to its premises.

Introduce `a b hab`. Use `congrArg e hab` as an intermediate fact. Simplify using `using this`. Take `⟨F', hF0, hF'⟩` from `compose_map Ψ (levelZeroMap e.symm.toIntertwiningMap) hinj hΨ0 hΨ`. Use `haveI := fd_fixed π hs hi`.

Conclude with `((hMI _ _ _ (levelZero π) η).2).2 ⟨F', hF0, hF'⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.lblFull :
    MeetsIff → FrobL → JDEq → TensTr → AvgMap → IndMap → TensInc → UpperTheory.Gal.InertialTypesAlt.LblFull := by
  intro hMI hF hJD hTT hAvg hInd hTI
  intro k _ _ _ _ _ θ N V _ _ π hs hi s x c hd hE hx T hT hP
  obtain ⟨e⟩ := hE
  obtain ⟨r, η, hη⟩ := hT
  have hTη : T = fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g) := by
    funext g
    rw [hη g]
    rfl
  subst hTη
  have hJ : J θ (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [← JD_nil, (hJD 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  have h1 : ∑ᶠ g, star (hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
      (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0 := by
    rw [← hJ]
    exact hP
  have h2 := frob_step hF (d := fun a => (x a).fst) hd (fun i => cusp θ (x i).fst (c i)) η h1
  haveI hfd : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) :=
    fun a => fd_fixed _ (x a).snd.rep.smooth (x a).snd.rep.irr
  have h3 := meets_parab hTT hd (fun a => levelZero (x a).rep) (fun i => cusp θ (x i).fst (c i)) hx η h2
  haveI := (hTT s _ _ (fun a => levelZero (x a).rep)).1
  obtain ⟨ψ, hψ0, hψ⟩ := ((hMI _ _ _ _ _).1).1 h3
  obtain ⟨j, hj, hjx⟩ := hTI k s (fun a => (x a).fst) _ (fun a => (x a).rep)
  obtain ⟨Φ, ev, hΦ1, hΦ2, hΦ3⟩ := hInd k N s (fun a => (x a).fst) hd _ _ _ _ j hj hjx
  obtain ⟨Ψ, hΨ0, hΨ⟩ := hAvg _ (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _ _ _ _ _ η Φ ev ψ
    hΦ1 hΦ2 hΦ3 hψ hψ0
  have hinj : Function.Injective (levelZeroMap e.symm.toIntertwiningMap) := by
    apply levelZeroMap_injective
    intro a b hab
    have := congrArg e hab
    simpa using this
  obtain ⟨F', hF0, hF'⟩ := compose_map Ψ (levelZeroMap e.symm.toIntertwiningMap) hinj hΨ0 hΨ
  haveI := fd_fixed π hs hi
  exact ((hMI _ _ _ (levelZero π) η).2).2 ⟨F', hF0, hF'⟩
