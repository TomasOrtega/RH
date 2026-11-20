import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames

variable {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' g : ℕ}

/- English proof (translation)
Establish `hmem : ∀ x : Fin g → ℂ, x ∈ eigSp B s ↔ ∀ a, B a x = s a • x`. Introduce `x`. Simplify using `[eigSp, Submodule.mem_iInf, sub_eq_zero]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `(hmem _).2 fun a => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[hB]`. Distinguish the cases in `hk : k = f i`.

Substitute `hk` using the available equality. Simplify using `[h1 i]`. Simplify using `[Pi.single_eq_of_ne hk]`. Introduce `x hx`. Establish `hx'` using `(hmem x).1 hx`.

Establish `hsum : x = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ)`. Use function extensionality and compare the values at `m`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : x k = 0`. Simplify using `[hk]`. Establish `hs : emb σ (e.symm k) = s`. Use extensionality with `a`. Establish `h` using `congrFun (hx' a) k`.

Rewrite `h` using `[hB, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hk h`. Take `⟨i, rfl⟩` from `h2 k hs`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_single_eq_eigSp {ι : Type} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k)
    (s : 𝓞 E →+* ℂ) (f : ι → Fin g) (h1 : ∀ i, emb σ (e.symm (f i)) = s)
    (h2 : ∀ k, emb σ (e.symm k) = s → ∃ i, f i = k) :
    Submodule.span ℂ (Set.range fun i : ι => (Pi.single (f i) 1 : Fin g → ℂ)) = eigSp B s := by
  have hmem : ∀ x : Fin g → ℂ, x ∈ eigSp B s ↔ ∀ a, B a x = s a • x := by
    intro x
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (hmem _).2 fun a => ?_
    funext k
    rw [hB]
    by_cases hk : k = f i
    · subst hk
      simp [h1 i]
    · simp [Pi.single_eq_of_ne hk]
  · intro x hx
    have hx' := (hmem x).1 hx
    have hsum : x = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ) := by
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : x k = 0
    · simp [hk]
    · have hs : emb σ (e.symm k) = s := by
        ext a
        have h := congrFun (hx' a) k
        rw [hB, Pi.smul_apply, smul_eq_mul] at h
        exact mul_right_cancel₀ hk h
      obtain ⟨i, rfl⟩ := h2 k hs
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [NumberField E] in

/- English proof (translation)
Introduce `hc` and use `((h.2 (σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hc⟩`.
-/
theorem conj_ne (σ : Ψ → (𝓞 E →+* ℂ)) (h : IsCMFam σ) (τ τ' : Ψ) : σ τ' ≠ (starRingEnd ℂ).comp (σ τ) :=
  fun hc => ((h.2 (σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hc⟩

omit [NumberField E] in

/- English proof (translation)
Use extensionality with `a`. Use `congrArg (starRingEnd ℂ) (RingHom.congr_fun h a)` as an intermediate fact. Simplify using `using this`.
-/
theorem conj_comp_inj {s t : 𝓞 E →+* ℂ} (h : (starRingEnd ℂ).comp s = (starRingEnd ℂ).comp t) : s = t := by
  ext a
  have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h a)
  simpa using this

omit [NumberField E] in

/- English proof (translation)
Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem conj_conj_comp (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `span_single_eq_eigSp σ e B hB (σ τ) (fun i : Fin j' => e (Sum.inl i, τ)) (fun i => ?_) fun k hk => ?_` and prove the remaining obligations. Simplify using `[emb]`. Take `⟨⟨u, τ'⟩, rfl⟩` from `e.surjective k`. Rewrite `hk` using `[Equiv.symm_apply_apply]`.

Break down `u with b | b` into its components or cases. Establish `h : σ τ' = σ τ` using `hk`. Take `rfl` from `hcm.1 h`. Conclude with `⟨b, rfl⟩`. Establish `h : (starRingEnd ℂ).comp (σ τ') = σ τ` using `hk`.

Use `absurd ?_ (conj_ne σ hcm τ τ')` and prove the remaining obligations. Rewrite using `[← h, conj_conj_comp]`. Use `span_single_eq_eigSp σ e B hB _ (fun i : Fin j => e (Sum.inr i, τ)) (fun i => ?_) fun k hk => ?_` and prove the remaining obligations. Simplify using `[emb]`. Take `⟨⟨u, τ'⟩, rfl⟩` from `e.surjective k`.

Rewrite `hk` using `[Equiv.symm_apply_apply]`. Break down `u with b | b` into its components or cases. Conclude with `absurd (show σ τ' = (starRingEnd ℂ).comp (σ τ) from hk) (conj_ne σ hcm τ τ')`. Establish `h : (starRingEnd ℂ).comp (σ τ') = (starRingEnd ℂ).comp (σ τ)` using `hk`. Take `rfl` from `hcm.1 (conj_comp_inj h)`.

Conclude with `⟨b, rfl⟩`.
-/
theorem span_single_eigenspace [IsCMField E] [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hcm : IsCMFam σ) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k) (τ : Ψ) :
    Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧
      Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) =
        eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  constructor
  · refine span_single_eq_eigSp σ e B hB (σ τ) (fun i : Fin j' => e (Sum.inl i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · have h : σ τ' = σ τ := hk
        obtain rfl := hcm.1 h
        exact ⟨b, rfl⟩
      · have h : (starRingEnd ℂ).comp (σ τ') = σ τ := hk
        refine absurd ?_ (conj_ne σ hcm τ τ')
        rw [← h, conj_conj_comp]
  · refine span_single_eq_eigSp σ e B hB _ (fun i : Fin j => e (Sum.inr i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · exact absurd (show σ τ' = (starRingEnd ℂ).comp (σ τ) from hk) (conj_ne σ hcm τ τ')
      · have h : (starRingEnd ℂ).comp (σ τ') = (starRingEnd ℂ).comp (σ τ) := hk
        obtain rfl := hcm.1 (conj_comp_inj h)
        exact ⟨b, rfl⟩

/- English proof (translation)
Introduce `σ e B h hB τ` and use `span_single_eigenspace σ e B h hB τ`.
-/
theorem span_single_eigSp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) :=
  fun σ e B h hB τ => span_single_eigenspace σ e B h hB τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames
