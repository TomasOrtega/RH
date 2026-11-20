import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.CoinvExact

/- English proof (translation)
Set `f'` to `Representation.IntertwiningMap.equivLinearMapAsModule α β f`. Set `g'` to `Representation.IntertwiningMap.equivLinearMapAsModule β γ g`. Establish `hg' : Function.Surjective g'` using `hg`. Establish `hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range f')` using `IsFiniteLength.of_surjective hA f'.surjective_rangeRestrict`. Establish `hex : Function.Exact (LinearMap.range f').subtype g'`.

Introduce `y`. Establish `h1 : g' y = 0 ↔ g y = 0` using `Iff.rfl`. Establish `h2 : y ∈ Set.range (LinearMap.range f').subtype ↔ y ∈ Set.range f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩`.

Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨⟨f' a, ⟨a, rfl⟩⟩, rfl⟩`. Rewrite using `[h1, h2]`. Conclude with `hfg y`.

Establish `hlen` using `Module.length_eq_add_of_exact (LinearMap.range f').subtype g' (LinearMap.range f').injective_subtype hg' hex`. Rewrite using `[HasFiniteLength, ← Module.length_ne_top_iff, hlen]`. Conclude with `WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hr, Module.length_ne_top_iff.2 hC⟩`.
-/
theorem hasFiniteLength_of_exact {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
    (f : α.IntertwiningMap β) (g : β.IntertwiningMap γ)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength β := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α β f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule β γ g
  have hg' : Function.Surjective g' := hg
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range f') :=
    IsFiniteLength.of_surjective hA f'.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.range f').subtype g' := by
    intro y
    have h1 : g' y = 0 ↔ g y = 0 := Iff.rfl
    have h2 : y ∈ Set.range (LinearMap.range f').subtype ↔ y ∈ Set.range f := by
      constructor
      · rintro ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨f' a, ⟨a, rfl⟩⟩, rfl⟩
    rw [h1, h2]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact (LinearMap.range f').subtype g'
    (LinearMap.range f').injective_subtype hg' hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hr, Module.length_ne_top_iff.2 hC⟩

section Coinv

variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, v, rfl⟩`. Use `Submodule.subset_span ⟨γ, φ v, ?_⟩` and prove the remaining obligations. Establish `e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v)` using `φ.isIntertwining _ _ _ _`. Use `show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v`.

Rewrite using `[map_sub, e, map_smul]`.
-/
theorem twRel_le_comap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ).comap φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, v, rfl⟩
  refine Submodule.subset_span ⟨γ, φ v, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

def coinvMap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    (coinv τ₁ ψ).IntertwiningMap (coinv τ₂ ψ) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (twRel_le_comap φ ψ)
  isIntertwining' := fun g => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    exact congrArg (Submodule.Quotient.mk (p := twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ))
      (φ.isIntertwining _ _ (1, g) v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coinvMap_mk (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, u, rfl⟩`. Take `⟨v, rfl⟩` from `hφ u`. Use `⟨τ₁ (γ, 1) v - (ψ γ : ℂ) • v, Submodule.subset_span ⟨γ, v, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v)` using `φ.isIntertwining _ _ _ _`.

Use `show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v`. Rewrite using `[map_sub, e, map_smul]`.
-/
theorem twRel_le_map (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ).map φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, u, rfl⟩
  obtain ⟨v, rfl⟩ := hφ u
  refine ⟨τ₁ (γ, 1) v - (ψ γ : ℂ) • v, Submodule.subset_span ⟨γ, v, rfl⟩, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

/- English proof (translation)
Introduce `y`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨v, rfl⟩` from `hφ u`. Conclude with `⟨Submodule.Quotient.mk v, rfl⟩`.
-/
theorem coinvMap_surjective (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    Function.Surjective (coinvMap φ ψ) := by
  intro y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨Submodule.Quotient.mk v, rfl⟩

end Coinv

/- English proof (translation)
Introduce `x`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hv : f v ∈ twRel (τU.comp (MonoidHom.inl Γ G)) ψ` using `(Submodule.Quotient.mk_eq_zero _).1 h`.

Take `⟨r, hr, hrv⟩` from `twRel_le_map f hf ψ hv`. Establish `hrv' : f r = f v` using `hrv`. Establish `hz : f (v - r) = 0` using `by rw [map_sub, hrv', sub_self]`. Take `⟨w, hw⟩` from `(hif (v - r)).1 hz`. Use `⟨Submodule.Quotient.mk w, ?_⟩` and prove the remaining obligations.

Rewrite using `[coinvMap_mk, hw]`. Conclude with `(Submodule.Quotient.eq _).2 (by simpa using (Submodule.neg_mem _ hr))`. Introduce and unpack `⟨y, hy⟩`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Establish `h0 : f (i w) = 0` using `(hif (i w)).2 ⟨w, rfl⟩`.

Rewrite using `[← hy, coinvMap_mk, coinvMap_mk, h0]`. Both sides reduce to the same expression.
-/
theorem coinvMap_exact {Γ G W V U : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τW : Representation ℂ (Γ × G) W} {τ : Representation ℂ (Γ × G) V}
    {τU : Representation ℂ (Γ × G) U} (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU)
    (hf : Function.Surjective f) (hif : Function.Exact i f) (ψ : Γ →* ℂˣ) :
    Function.Exact (coinvMap i ψ) (coinvMap f ψ) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have hv : f v ∈ twRel (τU.comp (MonoidHom.inl Γ G)) ψ :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨r, hr, hrv⟩ := twRel_le_map f hf ψ hv
    have hrv' : f r = f v := hrv
    have hz : f (v - r) = 0 := by rw [map_sub, hrv', sub_self]
    obtain ⟨w, hw⟩ := (hif (v - r)).1 hz
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [coinvMap_mk, hw]
    exact (Submodule.Quotient.eq _).2 (by simpa using (Submodule.neg_mem _ hr))
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : f (i w) = 0 := (hif (i w)).2 ⟨w, rfl⟩
    rw [← hy, coinvMap_mk, coinvMap_mk, h0]
    rfl

/- English proof (translation)
Introduce `Γ G W V U _ _ _ _ _ _ _ _ τW τ τU i f hf hif ψ hW hU`. Conclude with `hasFiniteLength_of_exact _ _ _ (coinvMap i ψ) (coinvMap f ψ) (coinvMap_surjective f hf ψ) (coinvMap_exact i f hf hif ψ) hW hU`.
-/
theorem main : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  intro Γ G W V U _ _ _ _ _ _ _ _ τW τ τU i f hf hif ψ hW hU
  exact hasFiniteLength_of_exact _ _ _ (coinvMap i ψ) (coinvMap f ψ)
    (coinvMap_surjective f hf ψ) (coinvMap_exact i f hf hif ψ) hW hU

end GlobalTheory.CompanionTheory.CoinvExact
