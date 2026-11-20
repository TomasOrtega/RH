import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKTypeDatum

noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsHeckeTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ J W) (q : ℕ) (T : ℕ → Module.End ℂ (indSpace J τ)) : Prop :=
  2 ≤ q ∧ FiniteDimensional ℂ (indSpace J τ) ∧
    (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ i, i + 1 < t → ∀ κ : KO k (Fin N), T i * ind J τ κ = ind J τ κ * T i) ∧
    (∀ i, i + 1 < t → (T i - (q : ℂ) • 1) * (T i + 1) = 0) ∧
    (∀ i j, j + 1 < t → i + 2 ≤ j → T i * T j = T j * T i) ∧
    (∀ i, i + 2 < t → T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1)) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ F, IsKMap (KO k (Fin N)) (ind J τ) (prodIrr y hd) F →
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (F : indSpace J τ →ₗ[ℂ] _), F ≠ 0 ∧
      IsKMap (KO k (Fin N)) (ind J τ) (prodIrr (fun _ : Fin t => π₀) hN) F ∧
      ∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

section Generic

variable {G : Type} [Group G] {K : Subgroup G} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
  [Module ℂ V] {σ : Representation ℂ K U} {ρ : Representation ℂ G V} {e : Module.End ℂ U}

/- English proof (translation)
Introduce and unpack `κ _ ⟨x, rfl⟩`. Use `⟨σ κ x, ?_⟩` and prove the remaining obligations. Use `congrArg (fun L : Module.End ℂ U => L x) (hc κ)` as an intermediate fact. Simplify `this.symm` using `[Module.End.mul_apply]`.
-/
theorem range_stable (hc : ∀ κ : K, σ κ * e = e * σ κ) :
    ∀ κ : K, ∀ f ∈ LinearMap.range e, σ κ f ∈ LinearMap.range e := by
  rintro κ _ ⟨x, rfl⟩
  refine ⟨σ κ x, ?_⟩
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [Module.End.mul_apply] using this.symm

/- English proof (translation)
Introduce `κ`. Use extensionality with `x`. Use `congrArg (fun L => L (e.rangeRestrict x)) (hf κ)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this ⊢`. Rewrite using `[← this]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun L : Module.End ℂ U => L x) (hc κ)` as an intermediate fact. Simplify `this.symm` using `[sub, Module.End.mul_apply]`.
-/
theorem isKMap_comp_rangeRestrict (hc : ∀ κ : K, σ κ * e = e * σ κ) {f : LinearMap.range e →ₗ[ℂ] V}
    (hf : IsKMap K (sub σ (LinearMap.range e) (range_stable hc)) ρ f) : IsKMap K σ ρ (f ∘ₗ e.rangeRestrict) := by
  intro κ
  ext x
  have := congrArg (fun L => L (e.rangeRestrict x)) (hf κ)
  simp only [LinearMap.comp_apply] at this ⊢
  rw [← this]
  congr 1
  apply Subtype.ext
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [sub, Module.End.mul_apply] using this.symm

/- English proof (translation)
Introduce `κ`. Use extensionality with `⟨y, hy⟩`. Use `congrArg (fun L => L y) (hF κ)` as an intermediate fact. Simplify `this` using `[sub]`.
-/
theorem isKMap_comp_subtype (hc : ∀ κ : K, σ κ * e = e * σ κ) {F : U →ₗ[ℂ] V} (hF : IsKMap K σ ρ F) :
    IsKMap K (sub σ (LinearMap.range e) (range_stable hc)) ρ (F ∘ₗ (LinearMap.range e).subtype) := by
  intro κ
  ext ⟨y, hy⟩
  have := congrArg (fun L => L y) (hF κ)
  simpa [sub] using this

/- English proof (translation)
Use extensionality with `⟨_, x, rfl⟩`. Use `congrArg (fun L => L x) h0` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply] at this`. Conclude with `this`.
-/
theorem eq_zero_of_comp_rangeRestrict (he : e * e = e) {f : LinearMap.range e →ₗ[ℂ] V}
    (h0 : f ∘ₗ e.rangeRestrict = 0) : f = 0 := by
  ext ⟨_, x, rfl⟩
  have := congrArg (fun L => L x) h0
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
  exact this

/- English proof (translation)
Introduce `h0`. Apply `hF` to reduce the goal to its premises. Rewrite using `[← hfix]`. Use extensionality with `x`. Use `congrArg (fun L => L ⟨e x, x, rfl⟩) h0` as an intermediate fact.

Simplify using `using this`.
-/
theorem comp_subtype_ne_zero {F : U →ₗ[ℂ] V} (hF : F ≠ 0) (hfix : F ∘ₗ e = F) :
    F ∘ₗ (LinearMap.range e).subtype ≠ 0 := by
  intro h0
  apply hF
  rw [← hfix]
  ext x
  have := congrArg (fun L => L ⟨e x, x, rfl⟩) h0
  simpa using this

/- English proof (translation)
Use extensionality with `x`. Establish `h2` using `congrArg (fun L : Module.End ℂ U => L x) heT`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at h2`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply]`. Rewrite using `[← map_smul]`.

Use `congr 1`. Conclude with `Subtype.ext (by simpa using h2)`.
-/
theorem comp_rangeRestrict_comp {f : LinearMap.range e →ₗ[ℂ] V} {T : Module.End ℂ U} {c : ℂ}
    (heT : e * T = c • e) : (f ∘ₗ e.rangeRestrict) ∘ₗ T = c • (f ∘ₗ e.rangeRestrict) := by
  ext x
  have h2 := congrArg (fun L : Module.End ℂ U => L x) heT
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h2
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [← map_smul]
  congr 1
  exact Subtype.ext (by simpa using h2)

end Generic

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨-, hfd, h1, h3, -, -, -, -, h4, hN, F5, hF5, hK5, hT5⟩` from `h`. Use `⟨h1, ?_, h3, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hfd`. Use `infer_instance`. Introduce `r y hd hs hin hn f hf`.

Conclude with `eq_zero_of_comp_rangeRestrict he (h4 r y hd hs hin hn _ (isKMap_comp_rangeRestrict hc hf) fun i hi => comp_rangeRestrict_comp (heT i hi))`. Conclude with `⟨hN, _, comp_subtype_ne_zero hF5 (hfix _ F5 hT5), isKMap_comp_subtype hc hK5⟩`.
-/
theorem isKTypeDatum_range {π₀ : IrrGL k} {t N : ℕ} {J : Subgroup (KO k (Fin N))} {W : Type} [AddCommGroup W]
    [Module ℂ W] {τ : Representation ℂ J W} {q : ℕ} {T : ℕ → Module.End ℂ (indSpace J τ)}
    (h : IsHeckeTypeDatum π₀ t J τ q T) (e : Module.End ℂ (indSpace J τ)) (he : e * e = e)
    (heT : ∀ i, i + 1 < t → e * T i = (q : ℂ) • e)
    (hc : ∀ κ : KO k (Fin N), ind J τ κ * e = e * ind J τ κ)
    (hfix : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (F : indSpace J τ →ₗ[ℂ] V),
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F ∘ₗ e = F) :
    IsKTypeDatum π₀ t J τ (LinearMap.range e) (range_stable hc) := by
  obtain ⟨-, hfd, h1, h3, -, -, -, -, h4, hN, F5, hF5, hK5, hT5⟩ := h
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · haveI := hfd; infer_instance
  · intro r y hd hs hin hn f hf
    exact eq_zero_of_comp_rangeRestrict he (h4 r y hd hs hin hn _ (isKMap_comp_rangeRestrict hc hf)
      fun i hi => comp_rangeRestrict_comp (heT i hi))
  · exact ⟨hN, _, comp_subtype_ne_zero hF5 (hfix _ F5 hT5), isKMap_comp_subtype hc hK5⟩

end GlobalTheory.KTypeDatum
