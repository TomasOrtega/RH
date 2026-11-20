import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `haveI : NeZero M := ⟨by omega⟩`. Take `⟨m, hm⟩` from `MonoidHom.map_cyclic ((σ.toMulEquiv.restrictRootsOfUnity M).toMonoidHom)`. Use `⟨m, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Simplify using `[zero_pow (by omega : M ≠ 0)] at hx`. Set `g : rootsOfUnity M K` to `⟨Units.mk0 x hx0, by rw [mem_rootsOfUnity]; ext; simp [hx]⟩`. Use `congrArg (fun y : rootsOfUnity M K => ((y : Kˣ) : K)) (hm g)` as an intermediate fact. Simplify `this` using `[g]`.
-/
private theorem exists_zpow_eq_ringEquiv_on_roots_of_unity {K : Type*} [Field K] (M : ℕ) (hM : 1 ≤ M) (σ : K ≃+* K) :
    ∃ m : ℤ, ∀ x : K, x ^ M = 1 → σ x = x ^ m := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((σ.toMulEquiv.restrictRootsOfUnity M).toMonoidHom)
  refine ⟨m, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : M ≠ 0)] at hx
  let g : rootsOfUnity M K := ⟨Units.mk0 x hx0, by rw [mem_rootsOfUnity]; ext; simp [hx]⟩
  have := congrArg (fun y : rootsOfUnity M K => ((y : Kˣ) : K)) (hm g)
  simpa [g] using this

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_zpow_eq_ringEquiv_on_roots_of_unity M hM σ.toRingEquiv`. Take `⟨b, hb⟩` from `exists_zpow_eq_ringEquiv_on_roots_of_unity M hM τ.toRingEquiv`. Establish `ha' : ∀ x : Ω, x ^ M = 1 → σ x = x ^ a` using `ha`. Establish `hb' : ∀ x : Ω, x ^ M = 1 → τ x = x ^ b` using `hb`. Establish `hμ : ∀ (ρ : Ω ≃ₐ[F] Ω) (x : Ω), x ^ M = 1 → (ρ x) ^ M = 1` using `fun ρ x hx => by`.

Rewrite using `[← map_pow, hx, map_one]`. Establish `hz : (σ⁻¹ (τ⁻¹ ζ)) ^ M = 1` using `hμ _ _ (hμ _ _ hζ)`. Establish `key : σ (τ (σ⁻¹ (τ⁻¹ ζ))) = τ (σ (σ⁻¹ (τ⁻¹ ζ)))`. Rewrite using `[ha' _ (hμ τ _ hz), hb' _ hz, hb' _ (hμ σ _ hz), ha' _ hz, ← zpow_mul, ← zpow_mul, mul_comm]`. Simplify using `only [AlgEquiv.mul_apply]`.

Rewrite using `[key]`. Simplify using the standard rewrite rules.
-/
private theorem commutator_fixes_root_of_unity {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) (hM : 1 ≤ M)
    (σ τ : Ω ≃ₐ[F] Ω) (ζ : Ω) (hζ : ζ ^ M = 1) : (σ * τ * σ⁻¹ * τ⁻¹) ζ = ζ := by
  obtain ⟨a, ha⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM σ.toRingEquiv
  obtain ⟨b, hb⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM τ.toRingEquiv
  have ha' : ∀ x : Ω, x ^ M = 1 → σ x = x ^ a := ha
  have hb' : ∀ x : Ω, x ^ M = 1 → τ x = x ^ b := hb
  have hμ : ∀ (ρ : Ω ≃ₐ[F] Ω) (x : Ω), x ^ M = 1 → (ρ x) ^ M = 1 := fun ρ x hx => by
    rw [← map_pow, hx, map_one]
  have hz : (σ⁻¹ (τ⁻¹ ζ)) ^ M = 1 := hμ _ _ (hμ _ _ hζ)
  have key : σ (τ (σ⁻¹ (τ⁻¹ ζ))) = τ (σ (σ⁻¹ (τ⁻¹ ζ))) := by
    rw [ha' _ (hμ τ _ hz), hb' _ hz, hb' _ (hμ σ _ hz), ha' _ hz, ← zpow_mul, ← zpow_mul, mul_comm]
  simp only [AlgEquiv.mul_apply]
  rw [key]
  simp

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ w A h M hM m b hirr hine`. Use `haveI := hirr`. Establish `hcomm : ∀ σ τ : Weil h, b.ρ σ * b.ρ τ = b.ρ τ * b.ρ σ`. Introduce `σ τ`. Establish `hdeg : deg (σ * τ * σ⁻¹ * τ⁻¹) = 0`.

Simplify using `only [deg_mul, deg_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ∈ Ine A` using `deg_eq_zero_iff.1 hdeg`. Establish `hρc : b.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1`. Establish `e : ineIncl h ⟨_, hc⟩ = σ * τ * σ⁻¹ * τ⁻¹` using `rfl`.

Rewrite using `[← e]`. Apply `hine` to reduce the goal to its premises. Introduce `ζ hζ`. Use `show ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ζ = ζ`. Simplify `commutator_fixes_root_of_unity M hM (σ : G F Ω) τ ζ hζ` using `only [Subgroup.coe_mul, Subgroup.coe_inv]`.

Establish `hst : σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ)` using `by group`. Rewrite using `[← map_mul, hst, map_mul, hρc, one_mul, map_mul]`. Establish `hnt : Nontrivial (Fin m → ℂ)`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`.

Conclude with `(bot_ne_top : (⊥ : Subrepresentation b.ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))`. Establish `hscal : ∀ τ : Weil h, ∃ c : ℂ, ∀ v, b.ρ τ v = c • v`. Introduce `τ`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (b.ρ τ)`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Set `S : Subrepresentation b.ρ` to `⟨Module.End.eigenspace (b.ρ τ) c, fun g v hv => by`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Use `congrArg (fun f => f v) (hcomm τ g)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hv, map_smul]⟩`.

Break down `eq_bot_or_eq_top S with hS | hS` into its components or cases. It suffices to derive a contradiction. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `hvS : v ∈ S.toSubmodule` using `hv.1`. Rewrite `hvS` using `[hS]`.

Conclude with `hv.2 ((Submodule.mem_bot ℂ).1 hvS)`. Introduce `v`. Establish `hvS : v ∈ S.toSubmodule`. Rewrite using `[hS]`. Conclude with `Submodule.mem_top`.

Conclude with `Module.End.mem_eigenspace_iff.1 hvS`. Take `⟨v0, hv0⟩` from `exists_ne (0 : Fin m → ℂ)`. Establish `hspan : Submodule.span ℂ {v0} = ⊤`. Set `S : Subrepresentation b.ρ` to `⟨Submodule.span ℂ {v0}, fun g v hv => by`. Take `⟨c, hc⟩` from `hscal g`.

Rewrite using `[hc]`. Conclude with `Submodule.smul_mem _ _ hv⟩`. Break down `eq_bot_or_eq_top S with hS | hS` into its components or cases. It suffices to derive a contradiction. Establish `hvS : v0 ∈ S.toSubmodule` using `Submodule.subset_span rfl`.

Rewrite `hvS` using `[hS]`. Conclude with `hv0 ((Submodule.mem_bot ℂ).1 hvS)`. Conclude with `congrArg Subrepresentation.toSubmodule hS`. Establish `hm1 : m = 1`. Establish `h1` using `finrank_span_singleton (K := ℂ) hv0`.

Rewrite `h1` using `[hspan, finrank_top, Module.finrank_fin_fun]`. Conclude with `h1`. Substitute `hm1` using the available equality. Set `v1 : Fin 1 → ℂ` to `fun _ => 1`. Establish `hEnd : ∀ (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ), f v = f v1 0 • v`.

Introduce `f v`. Establish `hv : v = v 0 • v1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[v1]`.

Rewrite using `[hv, map_smul]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[v1, mul_comm]`. Establish `hne : ∀ σ : Weil h, b.ρ σ v1 0 ≠ 0`.

Introduce `σ h0`. Establish `hinv : b.ρ σ⁻¹ (b.ρ σ v1) = v1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Rewrite `hinv` using `[hEnd (b.ρ σ) v1, h0, zero_smul, map_zero]`.

Use `congrFun hinv 0` as an intermediate fact. Simplify using `[v1] at this`. Set `ξ : Weil h →* ℂˣ` to `{ toFun := fun σ => Units.mk0 _ (hne σ) map_one' := by`. Use `ext`. Simplify using `[v1]`.

Use the proof step `map_mul' := by`. Introduce `σ τ`. Use `ext`. Simplify using `only [Units.val_mk0, Units.val_mul, map_mul, Module.End.mul_apply]`. Rewrite using `[hEnd (b.ρ σ) (b.ρ τ v1)]`.

Simplify using `}`. Establish `hξ1 : ∀ σ, ξ σ = 1 ↔ b.ρ σ = 1`. Introduce `σ`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`.

Establish `h1 : b.ρ σ v1 0 = 1` using `by simpa [ξ] using congrArg Units.val hσ`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[hEnd, h1, one_smul]`. Both sides reduce to the same expression.

Introduce `hσ`. Use `ext`. Simplify using `[ξ, hσ, v1]`. Establish `hsm : IsSmooth ξ`. Simplify `b.smooth` using `only [IsSmooth, hξ1]`.

Establish `hN : b.N = 0`. Take `⟨k, hk⟩` from `b.nilpotent`. Use `set c := b.N v1 0 with hc`. Establish `hNv : b.N v1 = c • v1` using `hEnd b.N v1`. Establish `hp : ∀ n : ℕ, (b.N ^ n) v1 = c ^ n • v1`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, pow_succ]`. Establish `hck : c ^ k = 0`.

Use `congrFun (hp k) 0` as an intermediate fact. Rewrite `this` using `[hk]`. Simplify `this.symm` using `[v1]`. Establish `hc0 : c = 0` using `pow_eq_zero_iff'.1 hck |>.1`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[hEnd, ← hc, hc0, zero_smul]`. Both sides reduce to the same expression. Use `⟨ξ, hsm, ?_, fun σ hσ => (hξ1 σ).2 hσ⟩` and prove the remaining obligations. Unfold `WD.lpOfChar`.

Apply `WD.sound` to reduce the goal to its premises. Use `⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i fin_cases i`. Rewrite using `[LinearEquiv.refl_apply, LinearEquiv.refl_apply, hEnd (b.ρ σ) v]`. Simplify using `[WDRep.ofChars, diagEnd, ξ]`.

Simplify using `[hN, WDRep.ofChars]`.
-/
theorem UpperTheory.irreducible_weilDeligne_tame_level_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M : ℕ), 1 ≤ M →
    ∀ (m : ℕ) (b : WDRep h (Fin m → ℂ)), b.ρ.IsIrreducible →
    (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → b.ρ (ineIncl h s) = 1) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), WD.mk b = WD.lpOfChar h ξ hξ ∧ ∀ σ, b.ρ σ = 1 → ξ σ = 1 := by
  intro F Ω _ _ _ _ _ w A h M hM m b hirr hine
  haveI := hirr
  have hcomm : ∀ σ τ : Weil h, b.ρ σ * b.ρ τ = b.ρ τ * b.ρ σ := by
    intro σ τ
    have hdeg : deg (σ * τ * σ⁻¹ * τ⁻¹) = 0 := by
      simp only [deg_mul, deg_inv]
      ring
    have hc : ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ∈ Ine A := deg_eq_zero_iff.1 hdeg
    have hρc : b.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
      have e : ineIncl h ⟨_, hc⟩ = σ * τ * σ⁻¹ * τ⁻¹ := rfl
      rw [← e]
      apply hine
      intro ζ hζ
      show ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ζ = ζ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using commutator_fixes_root_of_unity M hM (σ : G F Ω) τ ζ hζ
    have hst : σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
    rw [← map_mul, hst, map_mul, hρc, one_mul, map_mul]
  have hnt : Nontrivial (Fin m → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation b.ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  have hscal : ∀ τ : Weil h, ∃ c : ℂ, ∀ v, b.ρ τ v = c • v := by
    intro τ
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.ρ τ)
    refine ⟨c, ?_⟩
    let S : Subrepresentation b.ρ := ⟨Module.End.eigenspace (b.ρ τ) c, fun g v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have := congrArg (fun f => f v) (hcomm τ g)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hvS : v ∈ S.toSubmodule := hv.1
      rw [hS] at hvS
      exact hv.2 ((Submodule.mem_bot ℂ).1 hvS)
    · intro v
      have hvS : v ∈ S.toSubmodule := by
        rw [hS]
        exact Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 hvS
  obtain ⟨v0, hv0⟩ := exists_ne (0 : Fin m → ℂ)
  have hspan : Submodule.span ℂ {v0} = ⊤ := by
    let S : Subrepresentation b.ρ := ⟨Submodule.span ℂ {v0}, fun g v hv => by
      obtain ⟨c, hc⟩ := hscal g
      rw [hc]
      exact Submodule.smul_mem _ _ hv⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      have hvS : v0 ∈ S.toSubmodule := Submodule.subset_span rfl
      rw [hS] at hvS
      exact hv0 ((Submodule.mem_bot ℂ).1 hvS)
    · exact congrArg Subrepresentation.toSubmodule hS
  have hm1 : m = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  subst hm1
  let v1 : Fin 1 → ℂ := fun _ => 1
  have hEnd : ∀ (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ), f v = f v1 0 • v := by
    intro f v
    have hv : v = v 0 • v1 := by
      funext i
      fin_cases i
      simp [v1]
    rw [hv, map_smul]
    funext i
    fin_cases i
    simp [v1, mul_comm]
  have hne : ∀ σ : Weil h, b.ρ σ v1 0 ≠ 0 := by
    intro σ h0
    have hinv : b.ρ σ⁻¹ (b.ρ σ v1) = v1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hEnd (b.ρ σ) v1, h0, zero_smul, map_zero] at hinv
    have := congrFun hinv 0
    simp [v1] at this
  let ξ : Weil h →* ℂˣ :=
    { toFun := fun σ => Units.mk0 _ (hne σ)
      map_one' := by
        ext
        simp [v1]
      map_mul' := by
        intro σ τ
        ext
        simp only [Units.val_mk0, Units.val_mul, map_mul, Module.End.mul_apply]
        rw [hEnd (b.ρ σ) (b.ρ τ v1)]
        simp }
  have hξ1 : ∀ σ, ξ σ = 1 ↔ b.ρ σ = 1 := by
    intro σ
    constructor
    · intro hσ
      have h1 : b.ρ σ v1 0 = 1 := by simpa [ξ] using congrArg Units.val hσ
      apply LinearMap.ext
      intro v
      rw [hEnd, h1, one_smul]
      rfl
    · intro hσ
      ext
      simp [ξ, hσ, v1]
  have hsm : IsSmooth ξ := by
    simpa only [IsSmooth, hξ1] using b.smooth
  have hN : b.N = 0 := by
    obtain ⟨k, hk⟩ := b.nilpotent
    set c := b.N v1 0 with hc
    have hNv : b.N v1 = c • v1 := hEnd b.N v1
    have hp : ∀ n : ℕ, (b.N ^ n) v1 = c ^ n • v1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, pow_succ]
    have hck : c ^ k = 0 := by
      have := congrFun (hp k) 0
      rw [hk] at this
      simpa [v1] using this.symm
    have hc0 : c = 0 := pow_eq_zero_iff'.1 hck |>.1
    apply LinearMap.ext
    intro v
    rw [hEnd, ← hc, hc0, zero_smul]
    rfl
  refine ⟨ξ, hsm, ?_, fun σ hσ => (hξ1 σ).2 hσ⟩
  unfold WD.lpOfChar
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    fin_cases i
    rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, hEnd (b.ρ σ) v]
    simp [WDRep.ofChars, diagEnd, ξ]
  · simp [hN, WDRep.ofChars]
