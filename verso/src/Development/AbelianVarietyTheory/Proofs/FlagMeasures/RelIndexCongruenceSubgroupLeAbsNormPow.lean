import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongIndex

open scoped TensorProduct in

/- English proof (translation)
Establish `: IsArtinianRing (R ⧸ I)` using `isArtinian_of_finite`. Take `⟨b⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N) (fun P => by`. Use `P.isMaximal` as an intermediate fact. Set `: Field ((R ⧸ I) ⧸ P.asIdeal)` to `Ideal.Quotient.field _`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥`. Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]`. Conclude with `h1)`. Use `⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : Submodule.span R (Set.range b) = ⊤`.

Rewrite using `[← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq, Submodule.restrictScalars_top]`. Establish `h2` using `congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1`. Rewrite `h2` using `[Submodule.map_span, Submodule.map_top, LinearEquiv.range]`. Rewrite using `[Set.range_comp]`. Conclude with `h2`.

Rewrite using `[← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]`.
-/
theorem quot_smul_top_span_card {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    (∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N), Submodule.span R (Set.range v) = ⊤) ∧
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩
  · have h1 : Submodule.span R (Set.range b) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
        Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    rw [Set.range_comp]
    exact h2
  · rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
      Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

/- English proof (translation)
Take `⟨⟨v, hv⟩, hc⟩` from `quot_smul_top_span_card (R := R) (N := N) I`. Establish `: Finite (N ⧸ (I • ⊤ : Submodule R N))` using `Submodule.finite_quotient_smul I Module.Finite.fg_top`. Establish `hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f`. Introduce `f`. Use `Submodule.smul_le.2 fun a ha x _ => ?_` and prove the remaining obligations.

Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (f x)`. Rewrite using `[LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul ha Submodule.mem_top`. Set `Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N))` to `fun f i => Submodule.liftQ _ f (hk f) (v i)`. Establish `hΦ : Function.Injective Φ`.

Introduce `f g hfg`. Establish `: Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g)` using `LinearMap.ext_on_range hv fun i => congrFun hfg i`. Use extensionality with `x`. Simplify using `using LinearMap.congr_fun this (Submodule.Quotient.mk x)`. Use `⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]`.
-/
theorem card_hom_quot_smul_top {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by
  obtain ⟨⟨v, hv⟩, hc⟩ := quot_smul_top_span_card (R := R) (N := N) I
  have : Finite (N ⧸ (I • ⊤ : Submodule R N)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x)
    rw [LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  let Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N)) :=
    fun f i => Submodule.liftQ _ f (hk f) (v i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
      LinearMap.ext_on_range hv fun i => congrFun hfg i
    ext x
    simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)
  refine ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩
  rw [Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl`. Establish `h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f)` using `hf.map' _ (Submodule.ker_subtype M)`. Establish `h2 : LinearIndependent K (M.subtype ∘ f)` using `(LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1`. Set `g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V)` to `fun i => ⟨f i, Submodule.subset_span (f i).2⟩`. Establish `h3 : LinearIndependent K g` using `LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2`.

Simplify using `using h3.fintype_card_le_finrank`.
-/
theorem finrank_le_finrank_span {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) M ≤ Module.finrank K (Submodule.span K (M : Set V)) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl
  have h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f) := hf.map' _ (Submodule.ker_subtype M)
  have h2 : LinearIndependent K (M.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1
  let g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V) :=
    fun i => ⟨f i, Submodule.subset_span (f i).2⟩
  have h3 : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2
  simpa using h3.fintype_card_le_finrank

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB`. Establish `: Module.Finite (𝓞 K) M` using `Module.Finite.iff_fg.2 hM`. Establish `: Module.IsTorsionFree (𝓞 K) V` using `Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V`. Establish `: Module.Flat (𝓞 K) M` using `inferInstance`. Establish `: Module.FinitePresentation (𝓞 K) M` using `Module.finitePresentation_of_finite _ _`.

Establish `: Module.Projective (𝓞 K) M` using `Module.Flat.projective_of_finitePresentation`. Establish `: Finite (𝓞 K ⧸ 𝔪)` using `Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪`. Take `⟨hfin, hcard⟩` from `card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪`. Establish `hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M`. Introduce `s hs x hx`.

Rewrite using `[← hG s hs]`. Conclude with `Submodule.smul_mem_pointwise_smul x s M hx`. Establish `hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M`. Introduce `s hs x hx`. Use `Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations.

Rewrite using `[LinearMapClass.map_smul_of_tower]`. Conclude with `Submodule.smul_mem_smul ha (hmem s hs y hy)`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Set `ρ : G → (M →ₗ[𝓞 K] M)` to `fun s => (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)`.

Set `Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M))` to `fun s => (Submodule.mkQ _).comp (ρ s)`. Establish `hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G`. Introduce `s t hst`. Use `hB _ (s⁻¹ * t).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M)` using `(Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm`.

Establish `h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M`. Use `Submodule.mem_map_of_mem (f := M.subtype) h1` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]`. Conclude with `this`. Establish `h3` using `hmem' _ (s⁻¹).2 _ h2`.

Simplify using `using h3`. Set `Ψ : G ⧸ B.subgroupOf G → _` to `fun q => Φ q.out`. Establish `hΨ : Function.Injective Ψ`. Introduce `q q' h`. Rewrite using `[← q.out_eq, ← q'.out_eq]`.

Conclude with `QuotientGroup.eq.2 (hΦ _ _ h)`. Establish `: Finite (G ⧸ B.subgroupOf G)` using `Finite.of_injective Ψ hΨ`. Use `⟨Subgroup.index_ne_zero_of_finite, ?_⟩` and prove the remaining obligations. Use `(Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)` and prove the remaining obligations. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Conclude with `Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)`.
-/
theorem relIndex_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  intro K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  obtain ⟨hfin, hcard⟩ := card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪
  have hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M := by
    intro s hs x hx
    rw [← hG s hs]
    exact Submodule.smul_mem_pointwise_smul x s M hx
  have hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M := by
    intro s hs x hx
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)
    · rw [LinearMapClass.map_smul_of_tower]
      exact Submodule.smul_mem_smul ha (hmem s hs y hy)
    · rw [map_add]; exact Submodule.add_mem _ hy hz
  let ρ : G → (M →ₗ[𝓞 K] M) := fun s =>
    (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)
  let Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M)) := fun s => (Submodule.mkQ _).comp (ρ s)
  have hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G := by
    intro s t hst
    refine hB _ (s⁻¹ * t).2 fun x hx => ?_
    have h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M) :=
      (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm
    have h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M := by
      have := Submodule.mem_map_of_mem (f := M.subtype) h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
      exact this
    have h3 := hmem' _ (s⁻¹).2 _ h2
    simpa using h3
  let Ψ : G ⧸ B.subgroupOf G → _ := fun q => Φ q.out
  have hΨ : Function.Injective Ψ := by
    intro q q' h
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientGroup.eq.2 (hΦ _ _ h)
  have : Finite (G ⧸ B.subgroupOf G) := Finite.of_injective Ψ hΨ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  refine (Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)

end GlobalTheory.CongIndex
