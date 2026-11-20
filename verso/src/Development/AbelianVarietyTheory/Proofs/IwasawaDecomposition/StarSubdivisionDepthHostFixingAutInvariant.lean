import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Transfer

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X]

/- English proof (translation)
Take `⟨hm, hn, hl, hs⟩` from `h`. Establish `hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI` using `m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) := fun β => hφ _`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hs`. Use `letI := m2`. Use `letI := f2`.

Use `⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ]`. Simplify using `only [← hZ]`. Conclude with `hl c hc`. Rewrite using `[← hZ]`.

Conclude with `h1 i`. Rewrite using `[← hZ]`. Conclude with `h2 β ((hbal β).2 hβ) hp`. Conclude with `h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)`.
-/
theorem isCell_transfer {φ : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hφ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; φ.eval X B) = (letI := m2; letI := f2; φ.eval X B))
    {k : ℕ} {γ : Fin k → LinearMap.BilinForm ℤ X} (h : letI := m1; letI := f1; IsCell bar φ γ) :
    letI := m2; letI := f2; IsCell bar φ γ := by
  obtain ⟨hm, hn, hl, hs⟩ := h
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI := m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) :=
    fun β => hφ _
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hs
  letI := m2
  letI := f2
  refine ⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← hφ]
    simp only [← hZ]
    exact hl c hc
  · rw [← hZ]; exact h1 i
  · rw [← hZ]; exact h2 β ((hbal β).2 hβ) hp
  · exact h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)

/- English proof (translation)
Take `⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩` from `h`. Conclude with `⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB, hBt⟩`.
-/
theorem isStarDepth_transfer {ψ w : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hψ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; ψ.eval X B) = (letI := m2; letI := f2; ψ.eval X B))
    (hw : ∀ B : X → X → ℝ, (letI := m1; letI := f1; w.eval X B) = (letI := m2; letI := f2; w.eval X B))
    {B₁ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {t : ℝ} (h : letI := m1; letI := f1; IsStarDepth bar ψ w B₁ t) :
    letI := m2; letI := f2; IsStarDepth bar ψ w B₁ t := by
  obtain ⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩ := h
  exact ⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB,
    hBt⟩

end Transfer

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Set `s : E ≃+* E` to `IsFractionRing.ringEquivOfRingEquiv σ`. Establish `hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x` using `fun x => (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]`. Conclude with `IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _`.
-/
theorem host_bar_map_comm (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun a y z => ?_⟩` and prove the remaining obligations. Use `show β (τ a • y) z = β y (τ (H.bar a) • z)`. Rewrite using `[h2, host_bar_map_comm]`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun a y z => ?_⟩` and prove the remaining obligations. Use `h2 (τ.symm a) y z` as an intermediate fact. Express the relevant statement in the definitionally equal form `β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this`. Rewrite `this` using `[host_bar_map_comm, τ.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem mem_balForms_twist (τ : 𝓞 E ≃+* 𝓞 E) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms H.bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms H.bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (H.bar a) • z)
    rw [h2, host_bar_map_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this
    rwa [host_bar_map_comm, τ.apply_symm_apply] at this

/- English proof (translation)
Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' (𝓞 E) X`. Rewrite using `[φ.eval_eq hr, ← hφ τ hτ]`. Set `g : (Fin n → 𝓞 E) →+ X` to `r.toAddMonoidHom.comp ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩`. Establish `hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a` using `fun c a => by`. Express the relevant statement in the definitionally equal form `r _ = τ c • r _`.

Rewrite using `[← map_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hs : Function.Surjective g` using `hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩`.

Use `letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom`. Use `letI := hf`. Conclude with `(φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm`.
-/
theorem eval_twist_of_isTwInv {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0)
    [Module.Finite (𝓞 E) X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite (𝓞 E) X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm

omit [Module (𝓞 E) X] in

/- English proof (translation)
Introduce and unpack `t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩`. Use `set τ := σ.symm with hτdef`. Establish `hτ : τ H.w0 = H.w0` using `(σ.symm_apply_eq).2 hσ.symm`. Set `g : (Fin n → 𝓞 E) →+ X₁` to `r.toAddMonoidHom.comp ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩`. Establish `hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a` using `fun c a => by`.

Express the relevant statement in the definitionally equal form `r _ = τ c • r _`. Rewrite using `[← map_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Establish `hs : Function.Surjective g` using `hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩`. Establish `hgB : ∀ a b, B a b = B₁ (g a) (g b)` using `fun a b => by`. Use `hB (fun i => τ (a i)) (fun i => τ (b i))` as an intermediate fact. Simplify using `only [hτdef, RingEquiv.apply_symm_apply] at this`. Conclude with `this`.

Establish `hf' : letI` using `Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by`. Use `letI := Module.compHom X₁ τ.toRingHom`. Conclude with `Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs`. Establish `hd'` using `isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ) (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd`. Use `letI := Module.compHom X₁ τ.toRingHom`.

Conclude with `⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩`.
-/
theorem depthSet_twist_subset {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hw : IsTwInv H w) (σ : 𝓞 E ≃+* 𝓞 E)
    (hσ : σ H.w0 = H.w0) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    depthSet H.bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet H.bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ H.w0 = H.w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → 𝓞 E) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
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
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs
  have hd' := isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ)
    (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

/- English proof (translation)
Introduce `E _ _ _ H ψ w hψ hw σ hσ n B`. Use `show sSup _ = sSup _`. Use `congr 1`. Use `Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_` and prove the remaining obligations. Establish `h` using `depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))`.

Simplify `h` using `only [RingEquiv.apply_symm_apply]`.
-/
theorem isTwInv_starDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  intro E _ _ _ H ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end Twist

/- English proof (translation)
The claim follows from `isTwInv_starDepth E H ψ _ hψ fun σ _ n B => by simp [zeroFun]`.
-/
example {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (hψ : IsTwInv H ψ) :
    IsTwInv H (starDepth H.bar ψ (zeroFun (𝓞 E))) :=
  isTwInv_starDepth E H ψ _ hψ fun σ _ n B => by simp [zeroFun]

end GlobalTheory.PolFan
