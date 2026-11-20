import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

/- English proof (translation)
Establish `hz : z = z.re • (1 : ℂ) + z.im • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Use `conv_lhs => rw [hz]`. Rewrite using `[map_add, map_smul, map_smul]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem apply_eq_re (l : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    l z = (((l 1 : ℂ) - Complex.I * (l Complex.I : ℂ)) * z).re := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]
  simp
  ring

/- English proof (translation)
Set `m : Ψ ⊕ Ψ → (E →* ℂ)` to `Sum.elim (fun τ => (s τ : E →* ℂ)) (fun τ => (((starRingEnd ℂ).comp (s τ) : E →+* ℂ) : E →* ℂ))`. Establish `hm : Function.Injective m`. Introduce and unpack `(a | a) (b | b) hab`. Establish `: s a = s b` using `RingHom.ext fun x => DFunLike.congr_fun hab x`. Rewrite using `[hs this]`.

Conclude with `absurd (RingHom.ext fun x => DFunLike.congr_fun hab x) (hc a b)`. Conclude with `absurd (RingHom.ext fun x => (DFunLike.congr_fun hab x).symm) (hc b a)`. Establish `h1 : (starRingEnd ℂ).comp (s a) = (starRingEnd ℂ).comp (s b)` using `RingHom.ext fun x => DFunLike.congr_fun hab x`. Establish `: s a = s b`. Use extensionality with `x`.

Conclude with `RingHom.injective (starRingEnd ℂ) (DFunLike.congr_fun h1 x)`. Rewrite using `[hs this]`. Establish `hli` using `(linearIndependent_monoidHom E ℂ).comp m hm`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Establish `key` using `hli (Sum.elim c (fun τ => (starRingEnd ℂ) (c τ))) (by`.

Use function extensionality and compare the values at `x`. Rewrite using `[Fintype.sum_sum_type]`. Establish `h2 : ∑ τ, ((c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x)) = 0`. Establish `: ∀ τ, (c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x) = 2 * (((c τ * s τ x).re : ℝ) : ℂ)`. Introduce `τ`.

Rewrite using `[Complex.add_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`. Rewrite using `[← Finset.mul_sum, ← Complex.ofReal_sum, h x]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[Finset.sum_add_distrib]`. Simplify `h2)` using `[m, Finset.sum_apply, map_mul]`. Simplify using `using key (Sum.inl τ)`.
-/
theorem coeff_eq_zero {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (c : Ψ → ℂ) (h : ∀ x, ∑ τ, (c τ * s τ x).re = 0) (τ : Ψ) : c τ = 0 := by
  classical
  let m : Ψ ⊕ Ψ → (E →* ℂ) := Sum.elim (fun τ => (s τ : E →* ℂ))
    (fun τ => (((starRingEnd ℂ).comp (s τ) : E →+* ℂ) : E →* ℂ))
  have hm : Function.Injective m := by
    rintro (a | a) (b | b) hab
    · have : s a = s b := RingHom.ext fun x => DFunLike.congr_fun hab x
      rw [hs this]
    · exact absurd (RingHom.ext fun x => DFunLike.congr_fun hab x) (hc a b)
    · exact absurd (RingHom.ext fun x => (DFunLike.congr_fun hab x).symm) (hc b a)
    · have h1 : (starRingEnd ℂ).comp (s a) = (starRingEnd ℂ).comp (s b) :=
        RingHom.ext fun x => DFunLike.congr_fun hab x
      have : s a = s b := by
        ext x
        exact RingHom.injective (starRingEnd ℂ) (DFunLike.congr_fun h1 x)
      rw [hs this]
  have hli := (linearIndependent_monoidHom E ℂ).comp m hm
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (Sum.elim c (fun τ => (starRingEnd ℂ) (c τ))) (by
    funext x
    rw [Fintype.sum_sum_type]
    have h2 : ∑ τ, ((c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x)) = 0 := by
      have : ∀ τ, (c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x) = 2 * (((c τ * s τ x).re : ℝ) : ℂ) := by
        intro τ
        rw [Complex.add_conj]
        push_cast
        ring
      simp_rw [this]
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, h x]
      simp
    rw [Finset.sum_add_distrib] at h2
    simpa [m, Finset.sum_apply, map_mul] using h2)
  simpa using key (Sum.inl τ)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨L, hL0, hL⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Apply `hL0` to reduce the goal to its premises. Set `l : Fin N → Ψ → (ℂ →ₗ[ℝ] ℝ)` to `fun i τ => L ∘ₗ LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ ∘ₗ LinearMap.single ℝ (fun _ : Fin N => ℂ) i`. Establish `hl : ∀ i τ, l i τ = 0`.

Introduce `i τ`. Establish `hc0` using `coeff_eq_zero s hs hc (fun τ => ((l i τ 1 : ℝ) : ℂ) - Complex.I * ((l i τ Complex.I : ℝ) : ℂ)) (by`. Introduce `x`. Repeatedly rewrite using `[← apply_eq_re]`. Establish `hmem : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) ∈ LinearMap.ker L` using `hL (Submodule.subset_span ⟨_, rfl⟩)`.

Establish `hsum : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) = ∑ τ, LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ (LinearMap.single ℝ (fun _ : Fin N => ℂ) i (s τ x))`. Use function extensionality and compare the values at `τ' j`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single τ' (fun b _ hb => by simp [Pi.single_apply, hb.symm]) (by simp)]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Rewrite `hmem` using `[LinearMap.mem_ker, hsum, map_sum]`. Conclude with `hmem) τ`. Establish `h1 : l i τ 1 = 0`.

Use `congrArg Complex.re hc0` as an intermediate fact. Simplify using `using this`. Establish `h2 : l i τ Complex.I = 0`. Use `congrArg Complex.im hc0` as an intermediate fact. Simplify using `using this`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[apply_eq_re, h1, h2]`. Simplify using the standard rewrite rules. Use `LinearMap.pi_ext' fun τ => LinearMap.pi_ext' fun i => ?_` and prove the remaining obligations.

Conclude with `hl i τ`.
-/
theorem span_eq_top {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (N : ℕ) (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ')) :
    Submodule.span ℝ (Set.range fun (v : Fin N → E) => (fun τ i => s τ (v i) : Ψ → Fin N → ℂ)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨L, hL0, hL⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hL0
  let l : Fin N → Ψ → (ℂ →ₗ[ℝ] ℝ) := fun i τ =>
    L ∘ₗ LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ ∘ₗ LinearMap.single ℝ (fun _ : Fin N => ℂ) i
  have hl : ∀ i τ, l i τ = 0 := by
    intro i τ
    have hc0 := coeff_eq_zero s hs hc (fun τ => ((l i τ 1 : ℝ) : ℂ) - Complex.I * ((l i τ Complex.I : ℝ) : ℂ)) (by
      intro x
      simp_rw [← apply_eq_re]
      have hmem : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) ∈ LinearMap.ker L :=
        hL (Submodule.subset_span ⟨_, rfl⟩)
      have hsum : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) =
          ∑ τ, LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ
            (LinearMap.single ℝ (fun _ : Fin N => ℂ) i (s τ x)) := by
        funext τ' j
        rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single τ'
          (fun b _ hb => by simp [Pi.single_apply, hb.symm]) (by simp)]
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_apply, hj]
      rw [LinearMap.mem_ker, hsum, map_sum] at hmem
      exact hmem) τ
    have h1 : l i τ 1 = 0 := by
      have := congrArg Complex.re hc0
      simpa using this
    have h2 : l i τ Complex.I = 0 := by
      have := congrArg Complex.im hc0
      simpa using this
    apply LinearMap.ext
    intro z
    rw [apply_eq_re, h1, h2]
    simp
  refine LinearMap.pi_ext' fun τ => LinearMap.pi_ext' fun i => ?_
  exact hl i τ

def vecOf {E : Type} [Field E] {Ψ : Type} (N : ℕ) (s : Ψ → (E →+* ℂ)) :
    (Fin N → E) →+ (Ψ → Fin N → ℂ) where
  toFun v τ i := s τ (v i)
  map_zero' := by funext τ i; simp
  map_add' a b := by funext τ i; simp

/- English proof (translation)
Establish `hlat : ∀ x : Λ, vecOf N s (e x) ∈ Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k)))`. Introduce `x`. Rewrite using `[← lam.sum_repr x, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Establish `hall : ∀ v, vecOf N s v ∈ Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k)))`. Introduce `v`. Take `⟨k, x, hk, hx⟩` from `hspan v`. Establish `h2` using `hlat x`.

Rewrite `h2` using `[hx, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]`. Conclude with `(Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hk)).1 h2`. Establish `htop : (⊤ : Submodule ℝ (Ψ → Fin N → ℂ)) ≤ Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k)))`. Rewrite using `[← span_eq_top N s hs hc]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hall v`. Establish `hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Ψ → Fin N → ℂ)`. Rewrite using `[Fintype.card_fin, Module.finrank_pi_fintype]`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex, hg]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨basisOfTopLeSpanOfCardEqFinrank _ htop hcard, fun k τ i => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfTopLeSpanOfCardEqFinrank]`. Both sides reduce to the same expression.
-/
theorem exists_basis {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] {g N : ℕ} (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (hg : g = Fintype.card Ψ * N) {Λ : Type} [AddCommGroup Λ] (e : Λ →+ (Fin N → E))
    (hspan : ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (lam : Module.Basis (Fin (2 * g)) ℤ Λ) :
    ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = s τ (e (lam k) i) := by
  classical
  have hlat : ∀ x : Λ, vecOf N s (e x) ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro x
    rw [← lam.sum_repr x, map_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hall : ∀ v, vecOf N s v ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro v
    obtain ⟨k, x, hk, hx⟩ := hspan v
    have h2 := hlat x
    rw [hx, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hk)).1 h2
  have htop : (⊤ : Submodule ℝ (Ψ → Fin N → ℂ)) ≤
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    rw [← span_eq_top N s hs hc]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hall v
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Ψ → Fin N → ℂ) := by
    rw [Fintype.card_fin, Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, hg]
    ring
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ htop hcard, fun k τ i => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

/- English proof (translation)
Introduce `E _ _ _ Ψ _ g N σ hσ hg Λ _ e hspan lam`. Establish `hres : ∀ τ a, embOf (σ τ) (algebraMap (𝓞 E) E a) = σ τ a` using `fun τ a => IsFractionRing.lift_algebraMap (intEmb_injective (σ τ)) a`. Establish `hs : Function.Injective fun τ => embOf (σ τ)`. Introduce `a b hab`. Apply `hσ.1` to reduce the goal to its premises.

Use extensionality with `x`. Rewrite using `[← hres a x, ← hres b x]`. Conclude with `DFunLike.congr_fun hab _`. Establish `hc : ∀ τ τ', embOf (σ τ) ≠ (starRingEnd ℂ).comp (embOf (σ τ'))`. Introduce `τ τ' h`.

Establish `h1 : σ τ = (starRingEnd ℂ).comp (σ τ')`. Use extensionality with `x`. Rewrite using `[RingHom.comp_apply, ← hres τ x, ← hres τ' x]`. Conclude with `DFunLike.congr_fun h _`. Conclude with `((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩`.

Conclude with `LatBas.exists_basis (fun τ => embOf (σ τ)) hs hc hg e hspan lam`.
-/
theorem exists_realBasis_of_latBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g N : ℕ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → g = Fintype.card Ψ * N → ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin N → E)), (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ lam : Module.Basis (Fin (2 * g)) ℤ Λ, ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = embOf (σ τ) (e (lam k) i) := by
  intro E _ _ _ Ψ _ g N σ hσ hg Λ _ e hspan lam
  have hres : ∀ τ a, embOf (σ τ) (algebraMap (𝓞 E) E a) = σ τ a := fun τ a =>
    IsFractionRing.lift_algebraMap (intEmb_injective (σ τ)) a
  have hs : Function.Injective fun τ => embOf (σ τ) := by
    intro a b hab
    apply hσ.1
    ext x
    rw [← hres a x, ← hres b x]
    exact DFunLike.congr_fun hab _
  have hc : ∀ τ τ', embOf (σ τ) ≠ (starRingEnd ℂ).comp (embOf (σ τ')) := by
    intro τ τ' h
    have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := by
      ext x
      rw [RingHom.comp_apply, ← hres τ x, ← hres τ' x]
      exact DFunLike.congr_fun h _
    exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩
  exact LatBas.exists_basis (fun τ => embOf (σ τ)) hs hc hg e hspan lam

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
