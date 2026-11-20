import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

/- English proof (translation)
Rewrite using `[← hab]`. Conclude with `hh.continuousAt.tendsto`.
-/
theorem tendsto_nhds_of_analyticAt_eq {σ τ : Type} [Fintype σ] [Fintype τ] {h : (σ → ℂ) → (τ → ℂ)} {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : Tendsto h (𝓝 a) (𝓝 b) := by
  rw [← hab]; exact hh.continuousAt.tendsto

def germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : holGerms b →+* holGerms a where
  toFun φ := ⟨(φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab), by
      obtain ⟨f, hf, hφ⟩ := φ.2
      exact ⟨f ∘ h, hf.comp_of_eq hh hab, by rw [← hφ]; rfl⟩⟩
  map_one' := rfl
  map_mul' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ * ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) *
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_mul, ← hf, ← hg]; rfl
  map_zero' := rfl
  map_add' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ + ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) +
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_add, ← hf, ← hg]; rfl

/- English proof (translation)
Use `show (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) = _`. Rewrite using `[← hφ]`. Both sides reduce to the same expression.
-/
theorem germPull_coe {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) (φ : holGerms b) (f : (τ → ℂ) → ℂ)
    (hφ : (f : Germ (𝓝 b) ℂ) = φ) : ((germPull h hh hab φ : holGerms a) : Germ (𝓝 a) ℂ) = ↑(f ∘ h) := by
  show (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) = _
  rw [← hφ]; rfl

/- English proof (translation)
Take `⟨f, hf, hφ⟩` from `φ.2`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1` using `germPull_coe h₁ hh₁ hab φ f hφ`. Rewrite using `[germPull_coe h₂ hh₂ hba _ (f ∘ h₁) e1.symm, ← hφ]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `[h₁₂]`.
-/
theorem germPull_germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h₁ : (σ → ℂ) → (τ → ℂ))
    (h₂ : (τ → ℂ) → (σ → ℂ)) {a : σ → ℂ} {b : τ → ℂ} (hh₁ : AnalyticAt ℂ h₁ a) (hab : h₁ a = b)
    (hh₂ : AnalyticAt ℂ h₂ b) (hba : h₂ b = a) (h₁₂ : ∀ y, h₁ (h₂ y) = y) (φ : holGerms b) :
    germPull h₂ hh₂ hba (germPull h₁ hh₁ hab φ) = φ := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 := germPull_coe h₁ hh₁ hab φ f hφ
  rw [germPull_coe h₂ hh₂ hba _ (f ∘ h₁) e1.symm, ← hφ]
  congr 1
  funext y
  simp [h₁₂]

def germAffineEquiv {σ τ : Type} [Fintype σ] [Fintype τ] (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) :
    holGerms c ≃+* holGerms (0 : σ → ℂ) :=
  have h1 : AnalyticAt ℂ (fun z : σ → ℂ => e z + c) 0 := (e.analyticAt 0).add analyticAt_const
  have h1e : (fun z : σ → ℂ => e z + c) 0 = c := by simp
  have h2 : AnalyticAt ℂ (fun y : τ → ℂ => e.symm (y - c)) c :=
    (e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have h2e : (fun y : τ → ℂ => e.symm (y - c)) c = 0 := by simp
  RingEquiv.ofRingHom (germPull _ h1 h1e) (germPull _ h2 h2e)
    (RingHom.ext fun φ => germPull_germPull _ _ h2 h2e h1 h1e (fun z => by simp) φ)
    (RingHom.ext fun φ => germPull_germPull _ _ h1 h1e h2 h2e (fun y => by simp) φ)

/- English proof (translation)
The claim follows from `isNoetherianRing_of_ringEquiv _ (germAffineEquiv e c).symm`.
-/
theorem isNoetherianRing_holGerms_transfer {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) (h : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms c) :=
  isNoetherianRing_of_ringEquiv _ (germAffineEquiv e c).symm

/- English proof (translation)
Use `⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {φ} hφ => ?_⟩` and prove the remaining obligations. Conclude with `one_ne_zero (congrArg Subtype.val h).symm`. Take `⟨f, hf, hfφ⟩` from `φ.2`. Establish `hall : ∀ x : Fin 0 → ℂ, f x = f 0` using `fun x => by rw [Subsingleton.elim x 0]`. Establish `h0 : f 0 ≠ 0`.

Introduce `h0`. Apply `hφ` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hfφ]`. Conclude with `Germ.coe_eq.2 (Eventually.of_forall fun x => by rw [hall x, h0])`.

Use `⟨⟨↑(fun x => (f x)⁻¹), fun x => (f x)⁻¹, hf.inv h0, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(φ : Germ (𝓝 (0 : Fin 0 → ℂ)) ℂ) * ↑(fun x => (f x)⁻¹) = 1`. Rewrite using `[← hfφ]`. Conclude with `Germ.coe_eq.2 (Eventually.of_forall fun x => by show f x * (f x)⁻¹ = 1`.

Rewrite using `[hall x]`. Conclude with `mul_inv_cancel₀ h0)`.
-/
theorem isField_holGerms_fin_zero : IsField (holGerms (0 : Fin 0 → ℂ)) := by
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {φ} hφ => ?_⟩
  · exact one_ne_zero (congrArg Subtype.val h).symm
  · obtain ⟨f, hf, hfφ⟩ := φ.2
    have hall : ∀ x : Fin 0 → ℂ, f x = f 0 := fun x => by rw [Subsingleton.elim x 0]
    have h0 : f 0 ≠ 0 := by
      intro h0
      apply hφ
      apply Subtype.ext
      rw [← hfφ]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by rw [hall x, h0])
    refine ⟨⟨↑(fun x => (f x)⁻¹), fun x => (f x)⁻¹, hf.inv h0, rfl⟩, ?_⟩
    apply Subtype.ext
    change (φ : Germ (𝓝 (0 : Fin 0 → ℂ)) ℂ) * ↑(fun x => (f x)⁻¹) = 1
    rw [← hfφ]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => by
      show f x * (f x)⁻¹ = 1
      rw [hall x]
      exact mul_inv_cancel₀ h0)

/- English proof (translation)
Use `⟨fun I => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hI : I = ⊥`. Rewrite using `[hI]`. Conclude with `Submodule.fg_bot`. Take `⟨φ, hφI, hφ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`.

Take `⟨f, hf, hfφ⟩` from `φ.2`. Establish `hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0`. Introduce `h`. Apply `hφ0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hfφ]`. Conclude with `Germ.coe_eq.2 h`. Take `⟨A, d, hAd⟩` from `hG σ f hf hnz`. Set `Pl : (Option σ → ℂ) →L[ℂ] (σ → ℂ)` to `(ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)).comp (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))`. Set `Tl : (Option σ → ℂ) →L[ℂ] ℂ` to `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))`.

Set `ι : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ)` to `germPull Pl (Pl.analyticAt 0) (map_zero Pl)`. Set `τ : holGerms (0 : Option σ → ℂ)` to `⟨↑(Tl : (Option σ → ℂ) → ℂ), Tl, Tl.analyticAt 0, rfl⟩`. Set `Φ : (Fin d → holGerms (0 : σ → ℂ)) → holGerms (0 : Option σ → ℂ)` to `fun a => ∑ j : Fin d, ι (a j) * τ ^ (j : ℕ)`. Establish `Φ_add : ∀ a b, Φ (a + b) = Φ a + Φ b` using `fun a b => by`. Simplify using `only [Φ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.

Establish `Φ_smul : ∀ (r : holGerms (0 : σ → ℂ)) a, Φ (r • a) = ι r * Φ a` using `fun r a => by`. Simplify using `only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]`. Establish `Φ_zero : Φ 0 = 0` using `by simp [Φ]`. Set `N : Submodule (holGerms (0 : σ → ℂ)) (Fin d → holGerms (0 : σ → ℂ))` to `{ carrier := {a | Φ a ∈ I} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `Φ (a + b) ∈ I`.

Rewrite using `[Φ_add]`. Conclude with `I.add_mem ha hb`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `Φ 0 ∈ I`. Rewrite using `[Φ_zero]`.

Conclude with `I.zero_mem`. Use the proof step `smul_mem' := fun r a ha => by`. Express the relevant statement in the definitionally equal form `Φ (r • a) ∈ I`. Rewrite using `[Φ_smul]`. Conclude with `Ideal.mul_mem_left I _ ha }`.

Take `⟨s, hs⟩ : N.FG` from `IsNoetherian.noetherian N`. Use `⟨insert φ (s.image Φ), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `ψ hψ`. Rewrite `hψ` using `[Finset.coe_insert, Set.mem_insert_iff]`.

Break down `hψ with rfl | hψ` into its components or cases. Conclude with `hφI`. Rewrite `hψ` using `[Finset.coe_image]`. Take `⟨a, ha, rfl⟩` from `hψ`. Establish `: a ∈ N` using `hs ▸ Submodule.subset_span ha`.

Conclude with `this`. Introduce `ψ hψ`. Take `⟨g, hg, hgψ⟩` from `ψ.2`. Establish `hfA : AnalyticAt ℂ (f ∘ A) 0` using `hf.comp_of_eq (A.analyticAt 0) (map_zero A)`. Establish `hgA : AnalyticAt ℂ (g ∘ A) 0` using `hg.comp_of_eq (A.analyticAt 0) (map_zero A)`.

Take `⟨q, a, hq, ha, hev⟩` from `hD σ d (f ∘ A) (g ∘ A) hfA hgA hAd`. Establish `hqB : AnalyticAt ℂ (q ∘ A.symm) 0` using `hq.comp_of_eq (A.symm.analyticAt 0) (map_zero _)`. Set `Q : holGerms (0 : Option σ → ℂ)` to `⟨↑(q ∘ A.symm), q ∘ A.symm, hqB, rfl⟩`. Set `a' : Fin d → holGerms (0 : σ → ℂ)` to `fun j => ⟨↑(a j), a j, ha j, rfl⟩`. Establish `hev' : ∀ᶠ y in 𝓝 (0 : Option σ → ℂ), g y = q (A.symm y) * f y + ∑ j : Fin d, a j (Pl y) * Tl y ^ (j : ℕ)`.

Establish `hB : Tendsto A.symm (𝓝 0) (𝓝 0)`. Simplify using `using A.symm.continuous.tendsto (0 : Option σ → ℂ)`. Use `filter_upwards [hB.eventually hev] with y hy`. Simplify `hy` using `[Pl, Tl]`. Establish `key : ψ = Q * φ + Φ a'`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hι : ∀ j, ((ι (a' j) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(a j ∘ Pl)` using `fun j => germPull_coe _ _ _ (a' j) (a j) rfl`. Simplify using `only [Φ, Subring.coe_add, Subring.coe_mul, ← hfφ, ← hgψ]`. Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Simplify using `only [Subring.coe_mul, Subring.coe_pow, hι]`.

Express the relevant statement in the definitionally equal form `(↑g : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = Germ.coeRingHom _ (q ∘ A.symm) * Germ.coeRingHom _ f + ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ Pl) * Germ.coeRingHom _ (Tl : (Option σ → ℂ) → ℂ) ^ (j : ℕ)`. Simplify using `only [← map_mul, ← map_pow, ← map_sum, ← map_add]`. Use `Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [hev'] with y hy`. Simplify using `[hy, Finset.sum_apply]`.

Establish `hΦ : Φ a' ∈ I`. Establish `: Φ a' = ψ - Q * φ` using `by rw [key]; ring`. Rewrite using `[this]`. Conclude with `I.sub_mem hψ (Ideal.mul_mem_left I _ hφI)`. Establish `ha'N : a' ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ)))`.

Rewrite using `[hs]`. Conclude with `hΦ`. Establish `hgen : ∀ x ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))), Φ x ∈ Ideal.span (↑(insert φ (s.image Φ)) : Set (holGerms (0 : Option σ → ℂ)))`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Conclude with `Ideal.subset_span (by`. Rewrite using `[Finset.coe_insert, Finset.coe_image]`. Conclude with `Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)`. Consider the case `zero => rw [Φ_zero]`.

Conclude with `Ideal.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Φ_add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [Φ_smul]`. Conclude with `Ideal.mul_mem_left _ _ hx`.

Establish `hspan` using `hgen a' ha'N`. Rewrite using `[key]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) hspan`.
-/
theorem isNoetherianRing_holGerms_option (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) (σ : Type) [Fintype σ]
    (hR : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms (0 : Option σ → ℂ)) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  obtain ⟨φ, hφI, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := by
    intro h
    apply hφ0
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 h
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz

  let Pl : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let Tl : (Option σ → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let ι : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) := germPull Pl (Pl.analyticAt 0) (map_zero Pl)
  let τ : holGerms (0 : Option σ → ℂ) := ⟨↑(Tl : (Option σ → ℂ) → ℂ), Tl, Tl.analyticAt 0, rfl⟩
  let Φ : (Fin d → holGerms (0 : σ → ℂ)) → holGerms (0 : Option σ → ℂ) :=
    fun a => ∑ j : Fin d, ι (a j) * τ ^ (j : ℕ)
  have Φ_add : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
    simp only [Φ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have Φ_smul : ∀ (r : holGerms (0 : σ → ℂ)) a, Φ (r • a) = ι r * Φ a := fun r a => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  have Φ_zero : Φ 0 = 0 := by simp [Φ]
  let N : Submodule (holGerms (0 : σ → ℂ)) (Fin d → holGerms (0 : σ → ℂ)) :=
    { carrier := {a | Φ a ∈ I}
      add_mem' := fun {a b} ha hb => by
        change Φ (a + b) ∈ I
        rw [Φ_add]; exact I.add_mem ha hb
      zero_mem' := by
        change Φ 0 ∈ I
        rw [Φ_zero]; exact I.zero_mem
      smul_mem' := fun r a ha => by
        change Φ (r • a) ∈ I
        rw [Φ_smul]; exact Ideal.mul_mem_left I _ ha }
  obtain ⟨s, hs⟩ : N.FG := IsNoetherian.noetherian N
  refine ⟨insert φ (s.image Φ), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro ψ hψ
    rw [Finset.coe_insert, Set.mem_insert_iff] at hψ
    rcases hψ with rfl | hψ
    · exact hφI
    · rw [Finset.coe_image] at hψ
      obtain ⟨a, ha, rfl⟩ := hψ
      have : a ∈ N := hs ▸ Submodule.subset_span ha
      exact this
  · intro ψ hψ
    obtain ⟨g, hg, hgψ⟩ := ψ.2
    have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)
    have hgA : AnalyticAt ℂ (g ∘ A) 0 := hg.comp_of_eq (A.analyticAt 0) (map_zero A)
    obtain ⟨q, a, hq, ha, hev⟩ := hD σ d (f ∘ A) (g ∘ A) hfA hgA hAd
    have hqB : AnalyticAt ℂ (q ∘ A.symm) 0 := hq.comp_of_eq (A.symm.analyticAt 0) (map_zero _)
    let Q : holGerms (0 : Option σ → ℂ) := ⟨↑(q ∘ A.symm), q ∘ A.symm, hqB, rfl⟩
    let a' : Fin d → holGerms (0 : σ → ℂ) := fun j => ⟨↑(a j), a j, ha j, rfl⟩
    have hev' : ∀ᶠ y in 𝓝 (0 : Option σ → ℂ),
        g y = q (A.symm y) * f y + ∑ j : Fin d, a j (Pl y) * Tl y ^ (j : ℕ) := by
      have hB : Tendsto A.symm (𝓝 0) (𝓝 0) := by
        simpa using A.symm.continuous.tendsto (0 : Option σ → ℂ)
      filter_upwards [hB.eventually hev] with y hy
      simpa [Pl, Tl] using hy
    have key : ψ = Q * φ + Φ a' := by
      apply Subtype.ext
      have hι : ∀ j, ((ι (a' j) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
          ↑(a j ∘ Pl) := fun j => germPull_coe _ _ _ (a' j) (a j) rfl
      simp only [Φ, Subring.coe_add, Subring.coe_mul, ← hfφ, ← hgψ]
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [Subring.coe_mul, Subring.coe_pow, hι]
      change (↑g : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = Germ.coeRingHom _ (q ∘ A.symm) * Germ.coeRingHom _ f +
        ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ Pl) * Germ.coeRingHom _ (Tl : (Option σ → ℂ) → ℂ) ^ (j : ℕ)
      simp only [← map_mul, ← map_pow, ← map_sum, ← map_add]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev'] with y hy
      simp [hy, Finset.sum_apply]
    have hΦ : Φ a' ∈ I := by
      have : Φ a' = ψ - Q * φ := by rw [key]; ring
      rw [this]; exact I.sub_mem hψ (Ideal.mul_mem_left I _ hφI)
    have ha'N : a' ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))) := by
      rw [hs]; exact hΦ
    have hgen : ∀ x ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))),
        Φ x ∈ Ideal.span (↑(insert φ (s.image Φ)) : Set (holGerms (0 : Option σ → ℂ))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Ideal.subset_span (by
          rw [Finset.coe_insert, Finset.coe_image]
          exact Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
      | zero => rw [Φ_zero]; exact Ideal.zero_mem _
      | add x y _ _ hx hy => rw [Φ_add]; exact Ideal.add_mem _ hx hy
      | smul r x _ hx => rw [Φ_smul]; exact Ideal.mul_mem_left _ _ hx
    have hspan := hgen a' ha'N
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) hspan

/- English proof (translation)
Establish `hfin : ∀ n : ℕ, IsNoetherianRing (holGerms (0 : Fin n → ℂ))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Set `_` to `(isField_holGerms_fin_zero).toField`.

Use `infer_instance`. Consider the case `succ n ih`. Establish `h` using `isNoetherianRing_holGerms_option hD hG (Fin n) ih`. Conclude with `isNoetherianRing_holGerms_transfer (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv 0 h`. Introduce `σ _ w`.

Conclude with `isNoetherianRing_holGerms_transfer (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w (hfin _)`.
-/
theorem AnalyticGermsNoetherian.proof (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : AnalyticGermsNoetherian.Statement := by
  have hfin : ∀ n : ℕ, IsNoetherianRing (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := (isField_holGerms_fin_zero).toField
      infer_instance
    | succ n ih =>
      have h := isNoetherianRing_holGerms_option hD hG (Fin n) ih
      exact isNoetherianRing_holGerms_transfer
        (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv 0 h
  intro σ _ w
  exact isNoetherianRing_holGerms_transfer
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
