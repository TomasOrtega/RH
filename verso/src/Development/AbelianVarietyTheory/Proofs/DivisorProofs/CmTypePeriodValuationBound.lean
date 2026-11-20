import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : Function.Injective ((Algebra.linearMap O K).rTensor H)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)`. Introduce `x y hxy`. Apply `(TensorProduct.lid O H).symm.injective` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises. Simplify `hxy` using `[inK]`.
-/
theorem inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have h1 : Function.Injective ((Algebra.linearMap O K).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)
  intro x y hxy
  apply (TensorProduct.lid O H).symm.injective
  apply h1
  simpa [inK] using hxy

/- English proof (translation)
Establish `hspan : ∀ x ∈ W τ, ∃ c : K, c • v = x`. Introduce `x hx`. Establish `hu : (⟨v, hv⟩ : W τ) ≠ 0` using `by simpa using hv0`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : W τ) hu).1 h1 ⟨x, hx⟩`. Conclude with `⟨c, by simpa using congrArg Subtype.val hc⟩`.

Establish `hind` using `hW.submodule_iSupIndep`. Establish `htop` using `hW.submodule_iSup_eq_top`. Use `set C : Submodule K V := ⨆ j, ⨆ (_ : j ≠ τ), W j with hC`. Establish `hmemC : ∀ σ, σ ≠ τ → ∀ x ∈ W σ, x ∈ C` using `fun σ hσ x hx => (le_iSup₂_of_le σ hσ le_rfl : W σ ≤ C) hx`. Establish `hc : IsCompl (W τ) C`.

Use `⟨hind τ, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩` and prove the remaining obligations. Rewrite using `[← htop]`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = τ`. Substitute `hj` using the available equality.

Conclude with `le_sup_left`. Conclude with `le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)`. Establish `huniq : ∀ N₁ N₂ : Module.End K V, (N₁ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₁ x = 0) → (N₂ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₂ x = 0) → N₁ = N₂`. Introduce `N₁ N₂ h₁ h₂`. Establish `hle : ∀ σ, W σ ≤ LinearMap.eqLocus N₁ N₂`.

Introduce `σ x hx`. Use `show N₁ x = N₂ x`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Take `⟨c, rfl⟩` from `hspan x hx`.

Rewrite using `[map_smul, map_smul, h₁.1, h₂.1]`. Rewrite using `[h₁.2 σ hσ x hx, h₂.2 σ hσ x hx]`. Establish `: (⊤ : Submodule K V) ≤ LinearMap.eqLocus N₁ N₂` using `htop ▸ iSup_le hle`. Conclude with `LinearMap.ext fun x => this (Submodule.mem_top)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K V v) (LinearMap.ker_toSpanSingleton K hv0)`.

Set `p` to `Submodule.linearProjOfIsCompl (W τ) C hc`. Establish `hN0 : ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) x = 0`. Prove the components needed by the constructor for the conclusion. Establish `hpv : p v = ⟨v, hv⟩` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩`. Establish `hgv : g v = 1` using `by simpa using LinearMap.congr_fun hg 1`.

Simplify using `[hpv, hgv]`. Introduce `σ hσ x hx`. Establish `: p x = 0` using `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (hmemC σ hσ x hx)`. Simplify using `[this]`. Conclude with `⟨_, hN0, fun N hN => huniq _ _ hN hN0⟩`.
-/
theorem existsUnique_endo_line {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : ι → Submodule K V) (hW : DirectSum.IsInternal W) (τ : ι) (v w : V) (hv : v ∈ W τ) (hv0 : v ≠ 0)
    (h1 : Module.finrank K (W τ) = 1) :
    ∃! N : Module.End K V, N v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N x = 0 := by
  have hspan : ∀ x ∈ W τ, ∃ c : K, c • v = x := by
    intro x hx
    have hu : (⟨v, hv⟩ : W τ) ≠ 0 := by simpa using hv0
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : W τ) hu).1 h1 ⟨x, hx⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  have hind := hW.submodule_iSupIndep
  have htop := hW.submodule_iSup_eq_top
  set C : Submodule K V := ⨆ j, ⨆ (_ : j ≠ τ), W j with hC
  have hmemC : ∀ σ, σ ≠ τ → ∀ x ∈ W σ, x ∈ C := fun σ hσ x hx =>
    (le_iSup₂_of_le σ hσ le_rfl : W σ ≤ C) hx
  have hc : IsCompl (W τ) C := by
    refine ⟨hind τ, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine iSup_le fun j => ?_
    by_cases hj : j = τ
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  have huniq : ∀ N₁ N₂ : Module.End K V, (N₁ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₁ x = 0) →
      (N₂ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₂ x = 0) → N₁ = N₂ := by
    intro N₁ N₂ h₁ h₂
    have hle : ∀ σ, W σ ≤ LinearMap.eqLocus N₁ N₂ := by
      intro σ x hx
      show N₁ x = N₂ x
      by_cases hσ : σ = τ
      · subst hσ
        obtain ⟨c, rfl⟩ := hspan x hx
        rw [map_smul, map_smul, h₁.1, h₂.1]
      · rw [h₁.2 σ hσ x hx, h₂.2 σ hσ x hx]
    have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus N₁ N₂ := htop ▸ iSup_le hle
    exact LinearMap.ext fun x => this (Submodule.mem_top)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K V v)
    (LinearMap.ker_toSpanSingleton K hv0)
  let p := Submodule.linearProjOfIsCompl (W τ) C hc
  have hN0 : ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) v = w ∧
      ∀ σ, σ ≠ τ → ∀ x ∈ W σ, ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) x = 0 := by
    constructor
    · have hpv : p v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩
      have hgv : g v = 1 := by simpa using LinearMap.congr_fun hg 1
      simp [hpv, hgv]
    · intro σ hσ x hx
      have : p x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (hmemC σ hσ x hx)
      simp [this]
  exact ⟨_, hN0, fun N hN => huniq _ _ hN hN0⟩
end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i`. Use `haveI : Module.Free O H := hLat.1`. Establish `hmem : e i ∈ eigLat ρ (φ i)` using `by rw [(hGen i).1]; exact Submodule.mem_span_singleton_self _`. Establish `hv : inK (O` using `O) K H (e i) ∈ eigK ρ (φ i) := hmem`. Establish `he0 : e i ≠ 0`.

Take `⟨g, hg0, hgs⟩` from `(hEig.2.1 (φ i)).2.1`. Introduce `h`. Apply `hg0` to reduce the goal to its premises. Establish `: g ∈ eigLat ρ (φ i)` using `hgs ▸ Submodule.mem_span_singleton_self g`. Rewrite `this` using `[(hGen i).1, h]`.

Simplify using `using this`. Establish `hv0 : inK (O` using `O) K H (e i) ≠ 0 := fun h => he0 (inK_injective_of_free (O := O) K H (h.trans (map_zero (inK (O := O) K H)).symm))`. Establish `key` using `existsUnique_endo_line (eigK ρ) hEig.1 (φ i) (inK K H (e i)) (inK K H (f i)) hv hv0 (hLat.2.2.2.1 (φ i))`. Unfold `IsLower`. Conclude with `key`.
-/
theorem lowerOp_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  haveI : Module.Free O H := hLat.1
  have hmem : e i ∈ eigLat ρ (φ i) := by rw [(hGen i).1]; exact Submodule.mem_span_singleton_self _
  have hv : inK (O := O) K H (e i) ∈ eigK ρ (φ i) := hmem
  have he0 : e i ≠ 0 := by
    obtain ⟨g, hg0, hgs⟩ := (hEig.2.1 (φ i)).2.1
    intro h
    apply hg0
    have : g ∈ eigLat ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self g
    rw [(hGen i).1, h] at this
    simpa using this
  have hv0 : inK (O := O) K H (e i) ≠ 0 := fun h => he0 (inK_injective_of_free (O := O) K H (h.trans (map_zero (inK (O := O) K H)).symm))
  have key := existsUnique_endo_line (eigK ρ) hEig.1 (φ i) (inK K H (e i)) (inK K H (f i)) hv hv0 (hLat.2.2.2.1 (φ i))
  unfold IsLower
  exact key

end GlobalTheory
