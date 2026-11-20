import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist

section Twist

variable {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O}

variable {X : Type} [AddCommGroup X] [Module O X]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun a y z => ?_⟩` and prove the remaining obligations. Use `show β (τ a • y) z = β y (τ (bar a) • z)`. Rewrite using `[h2, hb.comm]`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun a y z => ?_⟩` and prove the remaining obligations. Use `h2 (τ.symm a) y z` as an intermediate fact. Express the relevant statement in the definitionally equal form `β (τ (τ.symm a) • y) z = β y (τ (bar (τ.symm a)) • z) at this`. Rewrite `this` using `[hb.comm, τ.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem mem_balForms_twist (hb : CMOrd O bar) (τ : O ≃+* O) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (bar a) • z)
    rw [h2, hb.comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (bar (τ.symm a)) • z) at this
    rwa [hb.comm, τ.apply_symm_apply] at this

/- English proof (translation)
Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' O X`. Rewrite using `[φ.eval_eq hr, ← hφ τ hτ]`. Set `g : (Fin n → O) →+ X` to `r.toAddMonoidHom.comp ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩`. Establish `hg : ∀ (c : O) a, g (c • a) = τ c • g a` using `fun c a => by`. Express the relevant statement in the definitionally equal form `r _ = τ c • r _`.

Rewrite using `[← map_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hs : Function.Surjective g` using `hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩`.

Use `letI : Module O X := Module.compHom _ τ.toRingHom`. Use `letI := hf`. Conclude with `(φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm`.
-/
theorem eval_twist_of_isTwG {φ : InvFun O} (hφ : IsTwG w0 φ) (τ : O ≃+* O) (hτ : τ w0 = w0)
    [Module.Finite O X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite O X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → O) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module O X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm

omit [Module O X] in

/- English proof (translation)
Introduce and unpack `t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩`. Use `set τ := σ.symm with hτdef`. Establish `hτ : τ w0 = w0` using `(σ.symm_apply_eq).2 hσ.symm`. Set `g : (Fin n → O) →+ X₁` to `r.toAddMonoidHom.comp ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩`. Establish `hg : ∀ (c : O) a, g (c • a) = τ c • g a` using `fun c a => by`.

Express the relevant statement in the definitionally equal form `r _ = τ c • r _`. Rewrite using `[← map_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Establish `hs : Function.Surjective g` using `hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩`. Establish `hgB : ∀ a b, B a b = B₁ (g a) (g b)` using `fun a b => by`. Use `hB (fun i => τ (a i)) (fun i => τ (b i))` as an intermediate fact. Simplify using `only [hτdef, RingEquiv.apply_symm_apply] at this`. Conclude with `this`.

Establish `hf' : letI` using `Module.compHom X₁ τ.toRingHom; Module.Finite O X₁ := by`. Use `letI := Module.compHom X₁ τ.toRingHom`. Conclude with `Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → O) →ₗ[O] X₁) hs`. Establish `hd'` using `isStarDepth_transfer bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist hb τ) (eval_twist_of_isTwG hψ τ hτ hf') (eval_twist_of_isTwG hw τ hτ hf') hd`. Use `letI := Module.compHom X₁ τ.toRingHom`.

Conclude with `⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩`.
-/
theorem depthSet_twist_subset (hb : CMOrd O bar) {ψ w : InvFun O} (hψ : IsTwG w0 ψ) (hw : IsTwG w0 w) (σ : O ≃+* O)
    (hσ : σ w0 = w0) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    depthSet bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ w0 = w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → O) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite O X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → O) →ₗ[O] X₁) hs
  have hd' := isStarDepth_transfer bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist hb τ)
    (eval_twist_of_isTwG hψ τ hτ hf') (eval_twist_of_isTwG hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

end Twist

/- English proof (translation)
Introduce `O _ _ _ _ bar w0 hb ψ w hψ hw σ hσ n B`. Use `show sSup _ = sSup _`. Use `congr 1`. Use `Set.Subset.antisymm (depthSet_twist_subset hb hψ hw σ hσ n B) ?_` and prove the remaining obligations. Establish `h` using `depthSet_twist_subset hb hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))`.

Simplify `h` using `only [RingEquiv.apply_symm_apply]`.
-/
theorem isTwG_starDepth : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ w : InvFun O), IsTwG w0 ψ → IsTwG w0 w → IsTwG w0 (starDepth bar ψ w) := by
  intro O _ _ _ _ bar w0 hb ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset hb hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset hb hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist
