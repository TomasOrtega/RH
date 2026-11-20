import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

noncomputable section

namespace GlobalTheory.HerrClass

section Algebra

variable {O G Γ M D : Type} [CommRing O] [Group G] [CommGroup Γ] [AddCommGroup M] [Module O M]
  [AddCommGroup D] [Module O D]

/- English proof (translation)
Establish `key : ∀ (b : M) (y : D), φ b - b = j y → (∀ g, r g = 1 → c g + (a g b - b) = 0) → (∀ g g', r g = r g' → c g + (a g b - b) = c g' + (a g' b - b)) ∧ (∀ g, ∃ e, j e = c g + (a g b - b))`. Introduce `b y hb h0`. Establish `h1 : ∀ g g', r g = r g' → c g + (a g b - b) = c g' + (a g' b - b)`. Introduce `g g' h`. Establish `e : g' = g * (g⁻¹ * g')` using `by group`.

Establish `h2` using `h0 (g⁻¹ * g') (by rw [map_mul, map_inv, h, inv_mul_cancel])`. Establish `h3` using `congrArg (a g) h2`. Rewrite `h3` using `[map_add, map_sub, map_zero]`. Rewrite using `[e, hc, hmul]`. Take the linear combination `(norm := abel) -h3`.

Use `⟨h1, fun g => decb _ (fun h hh => ?_) ⟨γD (r g) y - y, ?_⟩⟩` and prove the remaining obligations. Establish `h2` using `h1 (h * g) g (by rw [map_mul, hh, one_mul])`. Establish `h3` using `h0 h hh`. Rewrite `h2` using `[hc, hmul]`. Rewrite using `[map_add, map_sub]`.

Take the linear combination `(norm := abel) h2 - h3`. Rewrite using `[map_sub, hjγ, ← hb]`. Simplify using `only [map_add, map_sub, hφ, hcφ]`. Normalize the expressions using the abelian group laws. Take `⟨d, hd, y₁, hy₁⟩` from `deca (φ (-b₀) - (-b₀)) (fun g hg => by`.

Establish `h1` using `hcφ g`. Rewrite `h1` using `[hb₀ g hg, map_sub, hφ]`. Simplify using `only [map_sub, map_neg]`. Take the linear combination `(norm := abel) -h1)`. Establish `hb₁ : φ (-b₀ - d) - (-b₀ - d) = j y₁`.

Rewrite using `[hy₁, map_sub]`. Normalize the expressions using the abelian group laws. Establish `h₁ : ∀ g, r g = 1 → c g + (a g (-b₀ - d) - (-b₀ - d)) = 0`. Introduce `g hg`. Rewrite using `[hb₀ g hg, map_sub, map_neg, hd g hg]`.

Normalize the expressions using the abelian group laws. Generalize the expression as in `-b₀ - d = b₁ at hb₁ h₁`. Take `⟨k1, k2⟩` from `key b₁ y₁ hb₁ h₁`. Use `choose e he using k2`. Use `choose! s hs using hl`.

Take `⟨u, hu⟩` from `hu.exists_left_inv`. Use `set m : D := u • ∑ δ ∈ Δ, e (s δ) with hm`. Establish `hcoc : ∀ g h, j (e (g * h)) = j (e g) + a g (j (e h))`. Introduce `g h`. Rewrite using `[he, he, he, hc, hmul, map_add, map_sub]`.

Normalize the expressions using the abelian group laws. Establish `hav : ∀ g, r g ∈ Δ → a g (j m) - j m = -j (e g)`. Introduce `g hg`. Establish `h1 : ∑ δ ∈ Δ, j (e (g * s δ)) = ∑ δ ∈ Δ, j (e (s δ))`. Use `Finset.sum_nbij' (fun δ => r g * δ) (fun δ => (r g)⁻¹ * δ) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `δ hδ`. Conclude with `hΔm _ hg _ hδ`. Introduce `δ hδ`. Conclude with `hΔm _ (hΔi _ hg) _ hδ`. Introduce `δ _`.

Simplify using the standard rewrite rules. Introduce `δ _`. Simplify using the standard rewrite rules. Introduce `δ hδ`. Rewrite using `[he, he]`.

Conclude with `k1 _ _ (by rw [map_mul, hs δ hδ, hs _ (hΔm _ hg _ hδ)])`. Simplify using `only [hcoc, Finset.sum_add_distrib, Finset.sum_const] at h1`. Rewrite using `[hm, map_smul, map_smul, map_sum, map_sum, ← smul_sub, show ∑ δ ∈ Δ, a g (j (e (s δ))) - ∑ δ ∈ Δ, j (e (s δ)) = -(Δ.card • j (e g)) by`. Rewrite using `[← h1]`. Use the proof step `abel,`.

Use the proof step `smul_neg, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu, one_smul]`. Establish `hz : ∀ g, r g ∈ Δ → c g + (a g (b₁ + j m) - (b₁ + j m)) = 0`. Introduce `g hg`. Establish `h1` using `hav g hg`. Rewrite `h1` using `[he]`.

Rewrite using `[map_add]`. Take the linear combination `(norm := abel) h1`. Establish `hb₂ : φ (b₁ + j m) - (b₁ + j m) = j (y₁ + (φD m - m))`. Rewrite using `[map_add, map_add, map_sub, hjφ, ← hb₁]`. Normalize the expressions using the abelian group laws.

Establish `hker : ∀ g, r g = 1 → c g + (a g (b₁ + j m) - (b₁ + j m)) = 0`. Introduce `g hg`. Establish `h1` using `hjγ g m`. Establish `h2` using `hjγ 1 m`. Establish `h3 : a g (j m) = a 1 (j m)` using `by rw [← h1, ← h2, hg, map_one]`.

Distinguish the cases in `hne : Δ.Nonempty`. Take `⟨δ, hδ⟩` from `hne`. Conclude with `hz g (by rw [hg, ← mul_inv_cancel δ]; exact hΔm _ hδ _ (hΔi _ hδ))`. Establish `h4 : m = 0` using `by rw [hm, Finset.not_nonempty_iff_eq_empty.1 hne]; simp`. Rewrite using `[h4, map_zero, add_zero]`.

Conclude with `h₁ g hg`. Generalize the expression as in `b₁ + j m = b at hz hb₂ hker`. Generalize the expression as in `y₁ + (φD m - m) = y at hb₂`. Take `⟨k3, k4⟩` from `key b y hb₂ hker`. Take `⟨g₀, hg₀⟩` from `hγ`.

Take `⟨z, hzz⟩` from `k4 g₀`. Use `⟨y, z, b, hb₂, hj ?_, fun δ hδ => ⟨hj ?_, hj ?_⟩, fun g hg => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, ← hg₀, hjγ, hjφ, hzz, ← hb₂]`. Simplify using `only [map_add, map_sub, hφ, hcφ]`. Normalize the expressions using the abelian group laws.

Establish `h1` using `hz (s δ) (by rw [hs δ hδ]; exact hδ)`. Establish `h2` using `congrArg φ h1`. Rewrite using `[← hs δ hδ, hjγ, ← hb₂]`. Simplify using `only [map_add, map_sub, hφ, hcφ, map_zero] at h2 ⊢`. Take the linear combination `(norm := abel) h2 - h1`.

Establish `h1` using `hz (s δ) (by rw [hs δ hδ]; exact hδ)`. Establish `h2` using `congrArg (a g₀) h1`. Establish `h3` using `k3 (s δ * g₀) (g₀ * s δ) (by rw [map_mul, map_mul, mul_comm])`. Rewrite `h3` using `[hc, hc, hmul, hmul]`. Rewrite using `[← hs δ hδ, hjγ, hzz]`.

Simplify using `only [map_add, map_sub, map_zero] at h2 ⊢`. Take the linear combination `(norm := abel) h3 + h2 - h1`. Take the linear combination `(norm := abel) hz g hg`. Rewrite using `[hzz, ← k3 g g₀ (by rw [hg, hg₀])]; abel`.
-/
theorem exists_pair (a : G → M →ₗ[O] M) (hmul : ∀ g h x, a (g * h) x = a g (a h x))
    (φ : M →ₗ[O] M) (hφ : ∀ g x, φ (a g x) = a g (φ x))
    (r : G →* Γ) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (φD : D →ₗ[O] D) (γD : Γ → D →ₗ[O] D) (hjφ : ∀ x, j (φD x) = φ (j x))
    (hjγ : ∀ g x, j (γD (r g) x) = a g (j x))
    (deca : ∀ y, (∀ g, r g = 1 → a g y = y) → ∃ d, (∀ g, r g = 1 → a g d = d) ∧
      y - (φ d - d) ∈ LinearMap.range j)
    (decb : ∀ z, (∀ g, r g = 1 → a g z = z) → φ z - z ∈ LinearMap.range j → z ∈ LinearMap.range j)
    (Δ : Finset Γ) (hΔm : ∀ x ∈ Δ, ∀ y ∈ Δ, x * y ∈ Δ) (hΔi : ∀ x ∈ Δ, x⁻¹ ∈ Δ)
    (hl : ∀ δ ∈ Δ, ∃ g, r g = δ) (hu : IsUnit (Δ.card : O)) (γ : Γ) (hγ : ∃ g, r g = γ)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + a g (c h)) (hcφ : ∀ g, φ (c g) = c g)
    (b₀ : M) (hb₀ : ∀ g, r g = 1 → c g = a g b₀ - b₀) :
    ∃ (y z : D) (b : M), φ b - b = j y ∧ γD γ y - y = φD z - z ∧
      (∀ δ ∈ Δ, γD δ y = y ∧ γD δ z = z) ∧
      (∀ g, r g ∈ Δ → c g = -(a g b - b)) ∧ (∀ g, r g = γ → c g = j z - (a g b - b)) := by
  classical

  have key : ∀ (b : M) (y : D), φ b - b = j y → (∀ g, r g = 1 → c g + (a g b - b) = 0) →
      (∀ g g', r g = r g' → c g + (a g b - b) = c g' + (a g' b - b)) ∧
      (∀ g, ∃ e, j e = c g + (a g b - b)) := by
    intro b y hb h0
    have h1 : ∀ g g', r g = r g' → c g + (a g b - b) = c g' + (a g' b - b) := by
      intro g g' h
      have e : g' = g * (g⁻¹ * g') := by group
      have h2 := h0 (g⁻¹ * g') (by rw [map_mul, map_inv, h, inv_mul_cancel])
      have h3 := congrArg (a g) h2
      rw [map_add, map_sub, map_zero] at h3
      rw [e, hc, hmul]
      linear_combination (norm := abel) -h3
    refine ⟨h1, fun g => decb _ (fun h hh => ?_) ⟨γD (r g) y - y, ?_⟩⟩
    · have h2 := h1 (h * g) g (by rw [map_mul, hh, one_mul])
      have h3 := h0 h hh
      rw [hc, hmul] at h2
      rw [map_add, map_sub]
      linear_combination (norm := abel) h2 - h3
    · rw [map_sub, hjγ, ← hb]
      simp only [map_add, map_sub, hφ, hcφ]
      abel
  obtain ⟨d, hd, y₁, hy₁⟩ := deca (φ (-b₀) - (-b₀)) (fun g hg => by
    have h1 := hcφ g
    rw [hb₀ g hg, map_sub, hφ] at h1
    simp only [map_sub, map_neg]
    linear_combination (norm := abel) -h1)
  have hb₁ : φ (-b₀ - d) - (-b₀ - d) = j y₁ := by
    rw [hy₁, map_sub]; abel
  have h₁ : ∀ g, r g = 1 → c g + (a g (-b₀ - d) - (-b₀ - d)) = 0 := by
    intro g hg
    rw [hb₀ g hg, map_sub, map_neg, hd g hg]; abel
  generalize -b₀ - d = b₁ at hb₁ h₁
  obtain ⟨k1, k2⟩ := key b₁ y₁ hb₁ h₁
  choose e he using k2
  choose! s hs using hl
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  set m : D := u • ∑ δ ∈ Δ, e (s δ) with hm
  have hcoc : ∀ g h, j (e (g * h)) = j (e g) + a g (j (e h)) := by
    intro g h
    rw [he, he, he, hc, hmul, map_add, map_sub]; abel
  have hav : ∀ g, r g ∈ Δ → a g (j m) - j m = -j (e g) := by
    intro g hg
    have h1 : ∑ δ ∈ Δ, j (e (g * s δ)) = ∑ δ ∈ Δ, j (e (s δ)) := by
      refine Finset.sum_nbij' (fun δ => r g * δ) (fun δ => (r g)⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
      · intro δ hδ; exact hΔm _ hg _ hδ
      · intro δ hδ; exact hΔm _ (hΔi _ hg) _ hδ
      · intro δ _; simp
      · intro δ _; simp
      · intro δ hδ
        rw [he, he]
        exact k1 _ _ (by rw [map_mul, hs δ hδ, hs _ (hΔm _ hg _ hδ)])
    simp only [hcoc, Finset.sum_add_distrib, Finset.sum_const] at h1
    rw [hm, map_smul, map_smul, map_sum, map_sum, ← smul_sub,
      show ∑ δ ∈ Δ, a g (j (e (s δ))) - ∑ δ ∈ Δ, j (e (s δ)) = -(Δ.card • j (e g)) by
        rw [← h1]; abel,
      smul_neg, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu, one_smul]
  have hz : ∀ g, r g ∈ Δ → c g + (a g (b₁ + j m) - (b₁ + j m)) = 0 := by
    intro g hg
    have h1 := hav g hg
    rw [he] at h1
    rw [map_add]
    linear_combination (norm := abel) h1
  have hb₂ : φ (b₁ + j m) - (b₁ + j m) = j (y₁ + (φD m - m)) := by
    rw [map_add, map_add, map_sub, hjφ, ← hb₁]; abel
  have hker : ∀ g, r g = 1 → c g + (a g (b₁ + j m) - (b₁ + j m)) = 0 := by
    intro g hg
    have h1 := hjγ g m
    have h2 := hjγ 1 m
    have h3 : a g (j m) = a 1 (j m) := by rw [← h1, ← h2, hg, map_one]
    by_cases hne : Δ.Nonempty
    · obtain ⟨δ, hδ⟩ := hne
      exact hz g (by rw [hg, ← mul_inv_cancel δ]; exact hΔm _ hδ _ (hΔi _ hδ))
    · have h4 : m = 0 := by rw [hm, Finset.not_nonempty_iff_eq_empty.1 hne]; simp
      rw [h4, map_zero, add_zero]; exact h₁ g hg
  generalize b₁ + j m = b at hz hb₂ hker
  generalize y₁ + (φD m - m) = y at hb₂
  obtain ⟨k3, k4⟩ := key b y hb₂ hker
  obtain ⟨g₀, hg₀⟩ := hγ
  obtain ⟨z, hzz⟩ := k4 g₀
  refine ⟨y, z, b, hb₂, hj ?_, fun δ hδ => ⟨hj ?_, hj ?_⟩, fun g hg => ?_, fun g hg => ?_⟩
  · rw [map_sub, map_sub, ← hg₀, hjγ, hjφ, hzz, ← hb₂]
    simp only [map_add, map_sub, hφ, hcφ]
    abel
  · have h1 := hz (s δ) (by rw [hs δ hδ]; exact hδ)
    have h2 := congrArg φ h1
    rw [← hs δ hδ, hjγ, ← hb₂]
    simp only [map_add, map_sub, hφ, hcφ, map_zero] at h2 ⊢
    linear_combination (norm := abel) h2 - h1
  · have h1 := hz (s δ) (by rw [hs δ hδ]; exact hδ)
    have h2 := congrArg (a g₀) h1
    have h3 := k3 (s δ * g₀) (g₀ * s δ) (by rw [map_mul, map_mul, mul_comm])
    rw [hc, hc, hmul, hmul] at h3
    rw [← hs δ hδ, hjγ, hzz]
    simp only [map_add, map_sub, map_zero] at h2 ⊢
    linear_combination (norm := abel) h3 + h2 - h1
  · linear_combination (norm := abel) hz g hg
  · rw [hzz, ← k3 g g₀ (by rw [hg, hg₀])]; abel

/- English proof (translation)
Establish `hf : ∀ g, r g ∈ Δ → a g (b + t) = b + t`. Introduce `g hg`. Rewrite using `[map_add]`. Take the linear combination `(norm := abel) h1 g hg`. Establish `hy : φ (b + t) - (b + t) = j y` using `by rw [map_add, ht, ← hb]; abel`.

Take `⟨m, hm⟩` from `decb (b + t) (fun g hg => hf g (hg ▸ h1Δ)) ⟨y, hy.symm⟩`. Take `⟨g₀, hg₀⟩` from `hγ`. Use `⟨m, fun δ hδ => hj ?_, hj ?_, hj ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `hl δ hδ`. Rewrite using `[hjγ, hm, hf g hδ]`.

Rewrite using `[map_sub, hjφ, hm, hy]`. Rewrite using `[map_sub, ← hg₀, hjγ, hm, map_add]`. Take the linear combination `(norm := abel) -(h2 g₀ hg₀)`.
-/
theorem exists_of_coboundary (a : G → M →ₗ[O] M) (φ : M →ₗ[O] M)
    (r : G →* Γ) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (φD : D →ₗ[O] D) (γD : Γ → D →ₗ[O] D) (hjφ : ∀ x, j (φD x) = φ (j x))
    (hjγ : ∀ g x, j (γD (r g) x) = a g (j x))
    (decb : ∀ z, (∀ g, r g = 1 → a g z = z) → φ z - z ∈ LinearMap.range j → z ∈ LinearMap.range j)
    (Δ : Finset Γ) (h1Δ : (1 : Γ) ∈ Δ) (hl : ∀ δ ∈ Δ, ∃ g, r g = δ) (γ : Γ) (hγ : ∃ g, r g = γ)
    (y z : D) (b t : M) (hb : φ b - b = j y) (ht : φ t = t)
    (h1 : ∀ g, r g ∈ Δ → a g t - t = -(a g b - b))
    (h2 : ∀ g, r g = γ → a g t - t = j z - (a g b - b)) :
    ∃ m, (∀ δ ∈ Δ, γD δ m = m) ∧ y = φD m - m ∧ z = γD γ m - m := by
  have hf : ∀ g, r g ∈ Δ → a g (b + t) = b + t := by
    intro g hg
    rw [map_add]
    linear_combination (norm := abel) h1 g hg
  have hy : φ (b + t) - (b + t) = j y := by rw [map_add, ht, ← hb]; abel
  obtain ⟨m, hm⟩ := decb (b + t) (fun g hg => hf g (hg ▸ h1Δ)) ⟨y, hy.symm⟩
  obtain ⟨g₀, hg₀⟩ := hγ
  refine ⟨m, fun δ hδ => hj ?_, hj ?_, hj ?_⟩
  · obtain ⟨g, rfl⟩ := hl δ hδ
    rw [hjγ, hm, hf g hδ]
  · rw [map_sub, hjφ, hm, hy]
  · rw [map_sub, ← hg₀, hjγ, hm, map_add]
    linear_combination (norm := abel) -(h2 g₀ hg₀)

end Algebra

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

section Situation

variable {S : Sit}

/- English proof (translation)
Establish `h1 : ∀ f ∈ continuousCocycles ρ', f 1 = 0`. Introduce `f hf`. Use `hf.2 1 1` as an intermediate fact. Rewrite `this` using `[mul_one, map_one]`. Simplify using `using this`.

Establish `h2 : ∀ f ∈ continuousCocycles ρ', ∀ g, f g⁻¹ = -ρ' g⁻¹ (f g)`. Introduce `f hf g`. Use `hf.2 g⁻¹ g` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, h1 f hf]`. Conclude with `eq_neg_of_add_eq_zero_left this.symm`.

Set `U : Subgroup G'` to `{ carrier := {g | c g = c' g} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[hc.2, hc'.2, ha, hb]`. Use the proof step `one_mem' := by`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[h1 c hc, h1 c' hc']`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Rewrite using `[h2 c hc, h2 c' hc', ha] }`. Use function extensionality and compare the values at `g`. Conclude with `hden U (isClosed_eq hc.1 hc'.1) h g`.
-/
theorem coc_ext (T : LocLat S.G S.Qp S.LL S.O) [T2Space T.V] {G' : Type} [Group G']
    [TopologicalSpace G'] (ρ' : Representation S.LL G' T.V) (p : G' → Prop)
    (hden : ∀ U : Subgroup G', IsClosed (U : Set G') → (∀ g, p g → g ∈ U) → ∀ g, g ∈ U)
    (c c' : G' → T.V) (hc : c ∈ continuousCocycles ρ') (hc' : c' ∈ continuousCocycles ρ') (h : ∀ g, p g → c g = c' g) :
    c = c' := by
  have h1 : ∀ f ∈ continuousCocycles ρ', f 1 = 0 := by
    intro f hf
    have := hf.2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have h2 : ∀ f ∈ continuousCocycles ρ', ∀ g, f g⁻¹ = -ρ' g⁻¹ (f g) := by
    intro f hf g
    have := hf.2 g⁻¹ g
    rw [inv_mul_cancel, h1 f hf] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let U : Subgroup G' :=
    { carrier := {g | c g = c' g}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hc.2, hc'.2, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [h1 c hc, h1 c' hc']
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [h2 c hc, h2 c' hc', ha] }
  funext g
  exact hden U (isClosed_eq hc.1 hc'.1) h g

/- English proof (translation)
Simplify using `[TWact]`.
-/
theorem act_one_tmul (T : LocLat S.G S.Qp S.LL S.O) (g : S.G) (t : ↥T.L.T) :
    TWact (S.gR g) T g ((1 : S.RW) ⊗ₜ[S.O] t) = (1 : S.RW) ⊗ₜ[S.O] (T.actT g t) := by
  simp [TWact]

/- English proof (translation)
Simplify using `[TWmap]`.
-/
theorem phi_one_tmul (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) :
    TWmap S.φR T ((1 : S.RW) ⊗ₜ[S.O] t) = (1 : S.RW) ⊗ₜ[S.O] t := by
  simp [TWmap]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul w t`. Simplify using `only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hmul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `T.ρ (g * h) (t : T.V) = T.ρ g (T.ρ h (t : T.V))`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem act_mul (hmul : ∀ g h x, S.gR (g * h) x = S.gR g (S.gR h x))
    (T : LocLat S.G S.Qp S.LL S.O) (g h : S.G) (x : TW S.RW T) :
    TWact (S.gR (g * h)) T (g * h) x = TWact (S.gR g) T g (TWact (S.gR h) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w t =>
    simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hmul]
    congr 1
    apply Subtype.ext
    change T.ρ (g * h) (t : T.V) = T.ρ g (T.ρ h (t : T.V))
    rw [map_mul]; rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul w t => simp [TWact, TWmap, hφ]`.
-/
theorem phi_act (hφ : ∀ g x, S.φR (S.gR g x) = S.gR g (S.φR x))
    (T : LocLat S.G S.Qp S.LL S.O) (g : S.G) (x : TW S.RW T) :
    TWmap S.φR T (TWact (S.gR g) T g x) = TWact (S.gR g) T g (TWmap S.φR T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w t => simp [TWact, TWmap, hφ]

/- English proof (translation)
Use `haveI := T.L.free`. Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) (Algebra.linearMap S.O S.RW) hinj`. Introduce `t t' e`. Establish `: (1 : S.O) ⊗ₜ[S.O] t = (1 : S.O) ⊗ₜ[S.O] t'` using `h (by simpa using e)`. Simplify using `using congrArg (TensorProduct.lid S.O ↥T.L.T) this`.
-/
theorem one_tmul_inj (hinj : Function.Injective (algebraMap S.O S.RW))
    (T : LocLat S.G S.Qp S.LL S.O) :
    Function.Injective fun t : ↥T.L.T => (1 : S.RW) ⊗ₜ[S.O] t := by
  haveI := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap S.O S.RW) hinj
  intro t t' e
  have : (1 : S.O) ⊗ₜ[S.O] t = (1 : S.O) ⊗ₜ[S.O] t' := h (by simpa using e)
  simpa using congrArg (TensorProduct.lid S.O ↥T.L.T) this

/- English proof (translation)
Establish `hi` using `one_tmul_inj hinj T`. Establish `hmem : ∀ (c : ↥(latticeCocycles L')) g, (c : G' → T.V) g ∈ T.L.T` using `fun c g => hL ▸ c.2.2 g (Set.mem_univ g)`. Establish `hfix : ∀ x : TW S.RW T, (∀ g, (S.W.resΓ.comp ι) g = 1 → TWact (S.gR (ι g)) T (ι g) x = x) ↔ x ∈ Htl S T`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `h g hg`. Use `h (κ ⟨g, hg⟩) (by rw [MonoidHom.comp_apply, hικ]; exact hg)` as an intermediate fact. Rewrite `this` using `[hικ]`. Then use the resulting hypothesis. Introduce `h g hg`. Conclude with `h (ι g) hg`.

Establish `decb : ∀ z : TW S.RW T, (∀ g, (S.W.resΓ.comp ι) g = 1 → TWact (S.gR (ι g)) T (ι g) z = z) → TWmap S.φR T z - z ∈ LinearMap.range (E.jD T) → z ∈ LinearMap.range (E.jD T)` using `fun z hz => (hD T).2 z ((hfix z).1 hz)`. Use `⟨fun q => ?_, fun pr => ⟨fun h0 => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨b₀, -, hb₀⟩` from `(hF T).2.2 ⟨fun h => (c : G' → T.V) (κ h), ⟨c.2.1.1.comp hκ, fun g h => by beta_reduce`. Rewrite using `[map_mul, c.2.1.2, hρ, hικ]`.

Use the proof step `rfl⟩, fun h _ => hmem c _⟩`. Take `⟨y, z, b, hb, h1, h2, h3, h4⟩` from `exists_pair (fun g => TWact (S.gR (ι g)) T (ι g)) (fun g h x => by rw [map_mul, act_mul hmul]) (TWmap S.φR T) (fun g x => phi_act hφ T _ x) (S.W.resΓ.comp ι) (E.jD T) (E.jD_inj T) (S.W.φD T) (S.W.γD T) (E.jD_φ T) (fun g x => E.jD_act T (ι g) x) (fun y hy => by`. Take `⟨d, hd, hd'⟩` from `(hD T).1 y ((hfix y).1 hy)`. Conclude with `⟨d, (hfix d).2 hd, hd'⟩)`. Use `decb Δ hΔm hΔi hl hu γ hγ`.

Use the proof step `(fun g => (1 : S.RW) ⊗ₜ[S.O] (⟨(c : G' → T.V) g, hmem c g⟩ : ↥T.L.T))`. Use the proof step `(fun g h => by`. Rewrite using `[act_one_tmul, ← tmul_add]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(c : G' → T.V) (g * h) = (c : G' → T.V) g + T.ρ (ι g) ((c : G' → T.V) h)`. Rewrite using `[c.2.1.2, hρ])`. Use the proof step `(fun g => phi_one_tmul T _) b₀`. Use the proof step `(fun g hg => by`. Use `hb₀ ⟨ι g, hg⟩ _ ?_` and prove the remaining obligations.

Establish `: κ ⟨ι g, hg⟩ = g` using `hι (hικ _)`. Express the relevant statement in the definitionally equal form `_ = (c : G' → T.V) (κ ⟨ι g, hg⟩)`. Rewrite using `[this])`. Take `⟨c', hc', hc''⟩` from `hcl ⟨(y, z), hZ y z h1 h2⟩ b hb`. Use `⟨⟨(y, z), hZ y z h1 h2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc']`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `coc_ext T ρ' _ hden _ _ c'.2.1 c.2.1 fun g hg => ?_` and prove the remaining obligations. Establish `h5` using `hc'' g ⟨_, hmem c' g⟩ rfl`.

Establish `h6 : (⟨_, hmem c' g⟩ : ↥T.L.T) = ⟨_, hmem c g⟩`. Apply `hi` to reduce the goal to its premises. Break down `hg with hg | hg` into its components or cases. Conclude with `(h5.1 hg).trans (h3 g hg).symm`. Conclude with `(h5.2 hg).trans (h4 g hg).symm`.

Conclude with `congrArg Subtype.val h6`. Take `⟨b, -, hb⟩` from `(hF T).1 (E.jD T (pr : S.W.DD T × S.W.DD T).1) trivial`. Take `⟨c, hc, hc'⟩` from `hcl pr b hb`. Rewrite `hc` using `[h0, Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht, htc⟩` from `hc`.

Establish `ht' : t ∈ T.L.T` using `hL ▸ ht`. Establish `h5 : ∀ g, TWact (S.gR (ι g)) T (ι g) ((1 : S.RW) ⊗ₜ[S.O] (⟨t, ht'⟩ : ↥T.L.T)) - (1 : S.RW) ⊗ₜ[S.O] (⟨t, ht'⟩ : ↥T.L.T) = (1 : S.RW) ⊗ₜ[S.O] (⟨_, hmem c g⟩ : ↥T.L.T)`. Introduce `g`. Rewrite using `[act_one_tmul, ← tmul_sub]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h6 : ρ' g t - t = (c : G' → T.V) g` using `congrFun htc g`. Rewrite `h6` using `[hρ]`. Conclude with `h6`. Take `⟨m, hm, hy, hz⟩` from `exists_of_coboundary (fun g => TWact (S.gR (ι g)) T (ι g)) (TWmap S.φR T) (S.W.resΓ.comp ι) (E.jD T) (E.jD_inj T) (S.W.φD T) (S.W.γD T) (E.jD_φ T) (fun g x => E.jD_act T (ι g) x) decb Δ h1Δ hl γ hγ _ (pr : S.W.DD T × S.W.DD T).2 b _ hb (phi_one_tmul T ⟨t, ht'⟩) (fun g hg => (h5 g …`.

Conclude with `⟨m, hm, Prod.ext hy hz⟩`. Introduce and unpack `⟨m, hm, hpr⟩`. Take `⟨c, hc, hc'⟩` from `hcl pr (E.jD T m) (by rw [hpr, map_sub, E.jD_φ])`. Establish `: c = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `coc_ext T ρ' _ hden _ _ c.2.1 (Submodule.zero_mem _) fun g hg => ?_` and prove the remaining obligations. Establish `h5` using `hc' g ⟨_, hmem c g⟩ rfl`. Establish `h6 : (⟨_, hmem c g⟩ : ↥T.L.T) = 0`. Apply `hi` to reduce the goal to its premises. Break down `hg with hg | hg` into its components or cases.

Use `(h5.1 hg).trans ?_` and prove the remaining obligations. Rewrite using `[← E.jD_act, hm _ hg]`. Simplify using the standard rewrite rules. Use `(h5.2 hg).trans ?_` and prove the remaining obligations. Rewrite using `[← E.jD_act, hg, hpr]`.

Simplify using the standard rewrite rules. Conclude with `congrArg Subtype.val h6`. Rewrite using `[← hc, this]`. Both sides reduce to the same expression.
-/
theorem onto_and_kernel (E : S.Comparison₂) (hmul : ∀ g h x, S.gR (g * h) x = S.gR g (S.gR h x))
    (hφ : ∀ g x, S.φR (S.gR g x) = S.gR g (S.φR x))
    (hinj : Function.Injective (algebraMap S.O S.RW)) (hF : FNatW S) (hD : DecW S E)
    (T : LocLat S.G S.Qp S.LL S.O) [T2Space T.V] {G' : Type} [Group G'] [TopologicalSpace G']
    (ι : G' →* S.G) (κ : ↥(Hker S) →* G') (hκ : Continuous κ) (hικ : ∀ h, ι (κ h) = (h : S.G))
    (hι : Function.Injective ι)
    (ρ' : Representation S.LL G' T.V) (hρ : ∀ g x, ρ' g x = T.ρ (ι g) x)
    (L' : Lattice (O := S.O) ρ') (hL : L'.T = T.L.T)
    (Δ : Finset S.W.Gam) (h1Δ : (1 : S.W.Gam) ∈ Δ) (hΔm : ∀ x ∈ Δ, ∀ y ∈ Δ, x * y ∈ Δ)
    (hΔi : ∀ x ∈ Δ, x⁻¹ ∈ Δ) (hl : ∀ δ ∈ Δ, ∃ g, S.W.resΓ (ι g) = δ)
    (hu : IsUnit (Δ.card : S.O)) (γ : S.W.Gam) (hγ : ∃ g, S.W.resΓ (ι g) = γ)
    (hden : ∀ U : Subgroup G', IsClosed (U : Set G') →
      (∀ g, (S.W.resΓ (ι g) ∈ Δ ∨ S.W.resΓ (ι g) = γ) → g ∈ U) → ∀ g, g ∈ U)
    (Z : Submodule S.O (S.W.DD T × S.W.DD T))
    (hZ : ∀ y z, S.W.γD T γ y - y = S.W.φD T z - z →
      (∀ δ ∈ Δ, S.W.γD T δ y = y ∧ S.W.γD T δ z = z) → (y, z) ∈ Z)
    (cl : ↥Z →ₗ[S.O] LatticeCohomology L')
    (hcl : ∀ (pr : ↥Z) (b : TW S.RW T),
      TWmap S.φR T b - b = E.jD T (pr : S.W.DD T × S.W.DD T).1 →
      ∃ c : ↥(latticeCocycles L'), Submodule.Quotient.mk c = cl pr ∧
        ∀ (g : G') (t : ↥T.L.T), (t : T.V) = (c : G' → T.V) g →
          (S.W.resΓ (ι g) ∈ Δ → (1 : S.RW) ⊗ₜ[S.O] t = -(TWact (S.gR (ι g)) T (ι g) b - b)) ∧
          (S.W.resΓ (ι g) = γ → (1 : S.RW) ⊗ₜ[S.O] t =
            E.jD T (pr : S.W.DD T × S.W.DD T).2 - (TWact (S.gR (ι g)) T (ι g) b - b))) :
    Function.Surjective cl ∧ ∀ pr : ↥Z, cl pr = 0 ↔ ∃ m, (∀ δ ∈ Δ, S.W.γD T δ m = m) ∧
      (pr : S.W.DD T × S.W.DD T) = (S.W.φD T m - m, S.W.γD T γ m - m) := by
  have hi := one_tmul_inj hinj T
  have hmem : ∀ (c : ↥(latticeCocycles L')) g, (c : G' → T.V) g ∈ T.L.T := fun c g =>
    hL ▸ c.2.2 g (Set.mem_univ g)
  have hfix : ∀ x : TW S.RW T, (∀ g, (S.W.resΓ.comp ι) g = 1 → TWact (S.gR (ι g)) T (ι g) x = x) ↔
      x ∈ Htl S T := by
    intro x
    constructor
    · intro h g hg
      have := h (κ ⟨g, hg⟩) (by rw [MonoidHom.comp_apply, hικ]; exact hg)
      rwa [hικ] at this
    · intro h g hg
      exact h (ι g) hg
  have decb : ∀ z : TW S.RW T,
      (∀ g, (S.W.resΓ.comp ι) g = 1 → TWact (S.gR (ι g)) T (ι g) z = z) →
      TWmap S.φR T z - z ∈ LinearMap.range (E.jD T) → z ∈ LinearMap.range (E.jD T) :=
    fun z hz => (hD T).2 z ((hfix z).1 hz)
  refine ⟨fun q => ?_, fun pr => ⟨fun h0 => ?_, ?_⟩⟩
  · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨b₀, -, hb₀⟩ := (hF T).2.2 ⟨fun h => (c : G' → T.V) (κ h),
      ⟨c.2.1.1.comp hκ, fun g h => by
        beta_reduce
        rw [map_mul, c.2.1.2, hρ, hικ]; rfl⟩, fun h _ => hmem c _⟩
    obtain ⟨y, z, b, hb, h1, h2, h3, h4⟩ := exists_pair
      (fun g => TWact (S.gR (ι g)) T (ι g)) (fun g h x => by rw [map_mul, act_mul hmul])
      (TWmap S.φR T) (fun g x => phi_act hφ T _ x) (S.W.resΓ.comp ι) (E.jD T) (E.jD_inj T)
      (S.W.φD T) (S.W.γD T) (E.jD_φ T) (fun g x => E.jD_act T (ι g) x)
      (fun y hy => by
        obtain ⟨d, hd, hd'⟩ := (hD T).1 y ((hfix y).1 hy)
        exact ⟨d, (hfix d).2 hd, hd'⟩)
      decb Δ hΔm hΔi hl hu γ hγ
      (fun g => (1 : S.RW) ⊗ₜ[S.O] (⟨(c : G' → T.V) g, hmem c g⟩ : ↥T.L.T))
      (fun g h => by
        rw [act_one_tmul, ← tmul_add]
        congr 1
        apply Subtype.ext
        change (c : G' → T.V) (g * h) = (c : G' → T.V) g + T.ρ (ι g) ((c : G' → T.V) h)
        rw [c.2.1.2, hρ])
      (fun g => phi_one_tmul T _) b₀
      (fun g hg => by
        refine hb₀ ⟨ι g, hg⟩ _ ?_
        have : κ ⟨ι g, hg⟩ = g := hι (hικ _)
        change _ = (c : G' → T.V) (κ ⟨ι g, hg⟩)
        rw [this])
    obtain ⟨c', hc', hc''⟩ := hcl ⟨(y, z), hZ y z h1 h2⟩ b hb
    refine ⟨⟨(y, z), hZ y z h1 h2⟩, ?_⟩
    rw [← hc']
    congr 1
    apply Subtype.ext
    refine coc_ext T ρ' _ hden _ _ c'.2.1 c.2.1 fun g hg => ?_
    have h5 := hc'' g ⟨_, hmem c' g⟩ rfl
    have h6 : (⟨_, hmem c' g⟩ : ↥T.L.T) = ⟨_, hmem c g⟩ := by
      apply hi
      rcases hg with hg | hg
      · exact (h5.1 hg).trans (h3 g hg).symm
      · exact (h5.2 hg).trans (h4 g hg).symm
    exact congrArg Subtype.val h6
  · obtain ⟨b, -, hb⟩ := (hF T).1 (E.jD T (pr : S.W.DD T × S.W.DD T).1) trivial
    obtain ⟨c, hc, hc'⟩ := hcl pr b hb
    rw [h0, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨t, ht, htc⟩ := hc
    have ht' : t ∈ T.L.T := hL ▸ ht
    have h5 : ∀ g, TWact (S.gR (ι g)) T (ι g) ((1 : S.RW) ⊗ₜ[S.O] (⟨t, ht'⟩ : ↥T.L.T)) -
        (1 : S.RW) ⊗ₜ[S.O] (⟨t, ht'⟩ : ↥T.L.T) =
        (1 : S.RW) ⊗ₜ[S.O] (⟨_, hmem c g⟩ : ↥T.L.T) := by
      intro g
      rw [act_one_tmul, ← tmul_sub]
      congr 1
      apply Subtype.ext
      have h6 : ρ' g t - t = (c : G' → T.V) g := congrFun htc g
      rw [hρ] at h6
      exact h6
    obtain ⟨m, hm, hy, hz⟩ := exists_of_coboundary (fun g => TWact (S.gR (ι g)) T (ι g))
      (TWmap S.φR T) (S.W.resΓ.comp ι) (E.jD T) (E.jD_inj T)
      (S.W.φD T) (S.W.γD T) (E.jD_φ T) (fun g x => E.jD_act T (ι g) x) decb Δ h1Δ hl γ hγ
      _ (pr : S.W.DD T × S.W.DD T).2 b _ hb (phi_one_tmul T ⟨t, ht'⟩)
      (fun g hg => (h5 g).trans ((hc' g ⟨_, hmem c g⟩ rfl).1 hg))
      (fun g hg => (h5 g).trans ((hc' g ⟨_, hmem c g⟩ rfl).2 hg))
    exact ⟨m, hm, Prod.ext hy hz⟩
  · rintro ⟨m, hm, hpr⟩
    obtain ⟨c, hc, hc'⟩ := hcl pr (E.jD T m) (by rw [hpr, map_sub, E.jD_φ])
    have : c = 0 := by
      apply Subtype.ext
      refine coc_ext T ρ' _ hden _ _ c.2.1 (Submodule.zero_mem _) fun g hg => ?_
      have h5 := hc' g ⟨_, hmem c g⟩ rfl
      have h6 : (⟨_, hmem c g⟩ : ↥T.L.T) = 0 := by
        apply hi
        rcases hg with hg | hg
        · refine (h5.1 hg).trans ?_
          rw [← E.jD_act, hm _ hg]; simp
        · refine (h5.2 hg).trans ?_
          rw [← E.jD_act, hg, hpr]; simp
      exact congrArg Subtype.val h6
    rw [← hc, this]; rfl

/- English proof (translation)
Establish `hi` using `one_tmul_inj hinj T'`. Use `set F : TW S.RW T →ₗ[S.O] TW S.RW T' := TensorProduct.map (LinearMap.id : S.RW →ₗ[S.O] S.RW) ((f.f.restrictScalars S.O).restrict f.T_le) with hFd`. Establish `hFφ : ∀ x, TWmap S.φR T' (F x) = F (TWmap S.φR T x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul w t => simp [hFd, TWmap]`. Establish `hFg : ∀ g x, TWact (S.gR g) T' g (F x) = F (TWact (S.gR g) T g x)`. Introduce `g x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul w t`. Simplify using `only [hFd, TWact, TensorProduct.map_tmul, LinearMap.id_apply]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(f.equiv g t).symm`. Take `⟨b, -, hb⟩` from `(hF T).1 (E.jD T (pr : S.W.DD T × S.W.DD T).1) trivial`. Take `⟨c, hc, hc'⟩` from `E.clK_def h2 T pr b hb`.

Take `⟨d, hd, hd'⟩` from `E.clK_def h2 T' pr' (F b) (by`. Rewrite using `[hFφ, ← map_sub, hb, h, E.jD_map])`. Rewrite using `[← hc, ← hd]`. Establish `: d = ⟨f.post c, f.post_Z1T c c.2⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `coc_ext T' T'.ρ _ hden _ _ d.2.1 (f.post_Z1T c c.2).1 fun g hg => ?_` and prove the remaining obligations. Establish `h5` using `hc' g ⟨_, c.2.2 g (Set.mem_univ g)⟩ rfl`. Establish `h6` using `hd' g ⟨_, d.2.2 g (Set.mem_univ g)⟩ rfl`. Establish `h7 : (⟨_, d.2.2 g (Set.mem_univ g)⟩ : ↥T'.L.T) = (f.f.restrictScalars S.O).restrict f.T_le ⟨_, c.2.2 g (Set.mem_univ g)⟩`. Apply `hi` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `_ = F ((1 : S.RW) ⊗ₜ[S.O] _)`. Break down `hg with hg | hg` into its components or cases. Rewrite using `[h5.1 hg, map_neg, map_sub, ← hFg]`. Conclude with `h6.1 hg`. Rewrite using `[h5.2 hg, map_sub, map_sub, ← hFg, ← E.jD_map]`.

Use `(h6.2 hg).trans ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `congrArg Subtype.val h7`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem clK_natural (E : S.Comparison₂) (hinj : Function.Injective (algebraMap S.O S.RW)) (hF : FNatW S)
    (h2 : S.PD.p = 2 → S.W.DelF = {1})
    (hden : ∀ U : Subgroup S.G, IsClosed (U : Set S.G) →
      (∀ g, (S.W.resΓ g ∈ S.W.DelF ∨ S.W.resΓ g = S.W.gamK) → g ∈ U) → ∀ g, g ∈ U)
    (T T' : LocLat S.G S.Qp S.LL S.O) [T2Space T'.V] (f : LatHom T.L T'.L) (pr : S.W.wachCocyclesDelta T)
    (pr' : S.W.wachCocyclesDelta T')
    (h : (pr' : S.W.DD T' × S.W.DD T') = (S.W.map f (pr : S.W.DD T × S.W.DD T).1,
        S.W.map f (pr : S.W.DD T × S.W.DD T).2)) :
    S.W.clK T' pr' = f.H1map (S.W.clK T pr) := by
  have hi := one_tmul_inj hinj T'
  set F : TW S.RW T →ₗ[S.O] TW S.RW T' := TensorProduct.map (LinearMap.id : S.RW →ₗ[S.O] S.RW)
      ((f.f.restrictScalars S.O).restrict f.T_le) with hFd
  have hFφ : ∀ x, TWmap S.φR T' (F x) = F (TWmap S.φR T x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul w t => simp [hFd, TWmap]
  have hFg : ∀ g x, TWact (S.gR g) T' g (F x) = F (TWact (S.gR g) T g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul w t =>
      simp only [hFd, TWact, TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      exact (f.equiv g t).symm
  obtain ⟨b, -, hb⟩ := (hF T).1 (E.jD T (pr : S.W.DD T × S.W.DD T).1) trivial
  obtain ⟨c, hc, hc'⟩ := E.clK_def h2 T pr b hb
  obtain ⟨d, hd, hd'⟩ := E.clK_def h2 T' pr' (F b) (by
    rw [hFφ, ← map_sub, hb, h, E.jD_map])
  rw [← hc, ← hd]
  have : d = ⟨f.post c, f.post_Z1T c c.2⟩ := by
    apply Subtype.ext
    refine coc_ext T' T'.ρ _ hden _ _ d.2.1 (f.post_Z1T c c.2).1 fun g hg => ?_
    have h5 := hc' g ⟨_, c.2.2 g (Set.mem_univ g)⟩ rfl
    have h6 := hd' g ⟨_, d.2.2 g (Set.mem_univ g)⟩ rfl
    have h7 : (⟨_, d.2.2 g (Set.mem_univ g)⟩ : ↥T'.L.T) =
        (f.f.restrictScalars S.O).restrict f.T_le ⟨_, c.2.2 g (Set.mem_univ g)⟩ := by
      apply hi
      change _ = F ((1 : S.RW) ⊗ₜ[S.O] _)
      rcases hg with hg | hg
      · rw [h5.1 hg, map_neg, map_sub, ← hFg]; exact h6.1 hg
      · rw [h5.2 hg, map_sub, map_sub, ← hFg, ← E.jD_map]
        refine (h6.2 hg).trans ?_
        rw [h]
    exact congrArg Subtype.val h7
  rw [this]; rfl

end Situation

section Galois

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `h1` using `Padic.norm_eq_zpow_neg_valuation hx`. Rewrite `h` using `[h1, zpow_le_zpow_iff_right₀ hl1]`. Use `⟨x.valuation.toNat, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, Int.toNat_of_nonneg (by omega)]`.
-/
theorem exists_norm_eq {x : ℚ_[l]} (hx : x ≠ 0) {j₀ : ℕ} (h : ‖x‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))) :
    ∃ j : ℕ, j₀ ≤ j ∧ ‖x‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h1 := Padic.norm_eq_zpow_neg_valuation hx
  rw [h1, zpow_le_zpow_iff_right₀ hl1] at h
  refine ⟨x.valuation.toNat, by omega, ?_⟩
  rw [h1, Int.toNat_of_nonneg (by omega)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.trans hj, fun e => (h.2 e).trans hj⟩`.
-/
theorem lev_mono {j₀ j : ℕ} (h : Lev l j₀) (hj : j₀ ≤ j) : Lev l j :=
  ⟨h.1.trans hj, fun e => (h.2 e).trans hj⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨j, hjj, e⟩` from `exists_norm_eq (sub_ne_zero.2 hne) hu`. Establish `h1` using `GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j (lev_mono hj hjj) u e k (by exact_mod_cast hk)`. Rewrite `h1` using `[zpow_natCast, h, sub_self, norm_zero]`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`.

Conclude with `absurd h1 (zpow_pos hl0 _).ne`.
-/
theorem eq_one_of_pow {j₀ : ℕ} (hj : Lev l j₀) {u : ℚ_[l]} (hu : ‖u - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)))
    {k : ℕ} (hk : k ≠ 0) (h : u ^ k = 1) : u = 1 := by
  by_contra hne
  obtain ⟨j, hjj, e⟩ := exists_norm_eq (sub_ne_zero.2 hne) hu
  have h1 := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j (lev_mono hj hjj) u e k (by exact_mod_cast hk)
  rw [zpow_natCast, h, sub_self, norm_zero] at h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  exact absurd h1 (zpow_pos hl0 _).ne

/- English proof (translation)
Distinguish the cases in `hne : u = 1`. Simplify using `[hne]`. Take `⟨j, hjj, e⟩` from `exists_norm_eq (sub_ne_zero.2 hne) hu`. Establish `hk0 : k ≠ 0` using `by rintro rfl; exact hk (dvd_zero _)`. Establish `h1` using `GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j (lev_mono hj hjj) u e k (by exact_mod_cast hk0)`.

Rewrite `h1` using `[zpow_natCast, padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd hk]`. Rewrite using `[h1, e]`. Simplify using the standard rewrite rules.
-/
theorem norm_pow_sub_one {j₀ : ℕ} (hj : Lev l j₀) {u : ℚ_[l]}
    (hu : ‖u - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))) {k : ℕ} (hk : ¬ l ∣ k) : ‖u ^ k - 1‖ = ‖u - 1‖ := by
  by_cases hne : u = 1
  · simp [hne]
  obtain ⟨j, hjj, e⟩ := exists_norm_eq (sub_ne_zero.2 hne) hu
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero _)
  have h1 := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j (lev_mono hj hjj) u e k (by exact_mod_cast hk0)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd hk] at h1
  rw [h1, e]; simp

/- English proof (translation)
Establish `h1` using `((gen_dense l act χ ha hχ K j hj).2 _ hg).2.2 hσ`. Establish `h2 : e σ ∈ closure (e '' (U : Set G'))`. Use `closure_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, a, rfl⟩`. Take `⟨u, hu, rfl⟩` from `hH h hh`.

Conclude with `⟨u * g ^ a, mul_mem hu (pow_mem hgU a), by rw [map_mul, map_pow]⟩`. Establish `h3 : σ ∈ closure (U : Set G')`. Rewrite using `[he.closure_eq_preimage_closure_image]`. Conclude with `h2`. Rewrite `h3` using `[hU.closure_eq]`. Then use the resulting hypothesis.
-/
theorem mem_of_gen {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {G' : Type} [Group G'] [TopologicalSpace G'] (e : G' →* GQ l) (he : Topology.IsInducing e)
    (U : Subgroup G') (hU : IsClosed (U : Set G')) (hH : ∀ h ∈ Hinf K, ∃ u ∈ U, e u = h)
    (g : G') (hgU : g ∈ U) (hg : IsGen χ K j (e g)) (σ : G') (hσ : e σ ∈ Gj K j) : σ ∈ U := by
  have h1 := ((gen_dense l act χ ha hχ K j hj).2 _ hg).2.2 hσ
  have h2 : e σ ∈ closure (e '' (U : Set G')) := by
    refine closure_mono ?_ h1
    rintro _ ⟨h, hh, a, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hH h hh
    exact ⟨u * g ^ a, mul_mem hu (pow_mem hgU a), by rw [map_mul, map_pow]⟩
  have h3 : σ ∈ closure (U : Set G') := by
    rw [he.closure_eq_preimage_closure_image]; exact h2
  rwa [hU.closure_eq] at h3

/- English proof (translation)
Introduce `_ hg x` and use `hg ⟨x.1, x.2.1⟩`.
-/
theorem GK_le_fix (K : FinExt l) : GK K ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, x.2.1⟩

/- English proof (translation)
Take `⟨-, hcont, hG⟩` from `cyc_basic l χ hχ`. Distinguish the cases in `h1 : (χ g : ℚ_[l]) ^ N = 1`. Use `⟨1, one_mem _, ?_, by simp [h1]⟩` and prove the remaining obligations. Simplify using `only [map_one, Units.val_one, sub_self, norm_zero]`. Check the signs of the components of the expression.

Take `⟨j, hjj, e⟩` from `exists_norm_eq (sub_ne_zero.2 h1) (hpow g hg)`. Establish `hcl : IsClosed {y : GQ l | y ∈ GK K ∧ ‖(χ y : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))}` using `(InfiniteGalois.fixingSubgroup_isClosed K.1).inter (isClosed_le (hcont.sub continuous_const).norm continuous_const)`. Establish `hA` using `(hcl.isCompact.image (f := fun y => (χ y : ℚ_[l]) ^ N) (by fun_prop)).isClosed`. Establish `hxK : g ^ N ∈ GK K` using `pow_mem hg N`. Establish `hx : ‖(χ (g ^ N) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ))`.

Rewrite using `[map_pow, Units.val_pow_eq_pow_val, e]`. Establish `hxG : g ^ N ∈ Gj K j` using `((hG K _ (GK_le_fix K hxK)).1 j).2 hx.le`. Establish `hxG₀ : g ^ N ∈ Gj K j₀` using `((hG K _ (GK_le_fix K hxK)).1 j₀).2 (by`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val]`. Conclude with `hpow g hg)`.

Establish `hgen : IsGen χ K j ((g ^ N) ^ N)` using `⟨pow_mem hxG N, by`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, norm_pow_sub_one (lev_mono hj hjj) hx.le hN, hx]⟩`. Establish `h2` using `((gen_dense l act χ ha hχ K j (lev_mono hj hjj)).2 _ hgen).2.2 hxG`. Establish `h3` using `image_closure_subset_closure_image hcont ⟨_, h2, rfl⟩`. Establish `h4` using `closure_mono (t := (fun y => (χ y : ℚ_[l]) ^ N) '' {y : GQ l | y ∈ GK K ∧ ‖(χ y : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))}) (by`.

Introduce and unpack `_ ⟨_, ⟨h, hh, a, rfl⟩, rfl⟩`. Use `⟨(g ^ N) ^ a, ⟨pow_mem hxK a, ((hG K _ (GK_le_fix K (pow_mem hxK a))).1 j₀).1 (pow_mem hxG₀ a)⟩, ?_⟩` and prove the remaining obligations. Establish `h5` using `(hG K h (GK_le_fix K (hH hh))).2.1 hh`. Simplify using `only [map_mul, h5, one_mul, map_pow, Units.val_pow_eq_pow_val]`. Use the proof step `ring) h3`.

Rewrite `h4` using `[hA.closure_eq]`. Take `⟨g', ⟨h5, h6⟩, h7⟩` from `h4`. Use `⟨g', h5, h6, ?_⟩` and prove the remaining obligations. Simplify using `using h7`.
-/
theorem exists_principal {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (hH : Hinf K ≤ GK K) {j₀ N : ℕ}
    (hj : Lev l j₀) (hN : ¬ l ∣ N)
    (hpow : ∀ g ∈ GK K, ‖(χ g : ℚ_[l]) ^ N - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))) (g : GQ l)
    (hg : g ∈ GK K) :
    ∃ g' ∈ GK K, ‖(χ g' : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)) ∧
      (χ g' : ℚ_[l]) ^ N = (χ g : ℚ_[l]) ^ N := by
  obtain ⟨-, hcont, hG⟩ := cyc_basic l χ hχ
  by_cases h1 : (χ g : ℚ_[l]) ^ N = 1
  · refine ⟨1, one_mem _, ?_, by simp [h1]⟩
    simp only [map_one, Units.val_one, sub_self, norm_zero]
    positivity
  obtain ⟨j, hjj, e⟩ := exists_norm_eq (sub_ne_zero.2 h1) (hpow g hg)
  have hcl : IsClosed {y : GQ l | y ∈ GK K ∧ ‖(χ y : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))} :=
    (InfiniteGalois.fixingSubgroup_isClosed K.1).inter
      (isClosed_le (hcont.sub continuous_const).norm continuous_const)
  have hA := (hcl.isCompact.image (f := fun y => (χ y : ℚ_[l]) ^ N) (by fun_prop)).isClosed
  have hxK : g ^ N ∈ GK K := pow_mem hg N
  have hx : ‖(χ (g ^ N) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
    rw [map_pow, Units.val_pow_eq_pow_val, e]
  have hxG : g ^ N ∈ Gj K j := ((hG K _ (GK_le_fix K hxK)).1 j).2 hx.le
  have hxG₀ : g ^ N ∈ Gj K j₀ := ((hG K _ (GK_le_fix K hxK)).1 j₀).2 (by
    rw [map_pow, Units.val_pow_eq_pow_val]; exact hpow g hg)
  have hgen : IsGen χ K j ((g ^ N) ^ N) := ⟨pow_mem hxG N, by
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow_sub_one (lev_mono hj hjj) hx.le hN, hx]⟩
  have h2 := ((gen_dense l act χ ha hχ K j (lev_mono hj hjj)).2 _ hgen).2.2 hxG
  have h3 := image_closure_subset_closure_image hcont ⟨_, h2, rfl⟩
  have h4 := closure_mono (t := (fun y => (χ y : ℚ_[l]) ^ N) ''
      {y : GQ l | y ∈ GK K ∧ ‖(χ y : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ))}) (by
    rintro _ ⟨_, ⟨h, hh, a, rfl⟩, rfl⟩
    refine ⟨(g ^ N) ^ a, ⟨pow_mem hxK a,
      ((hG K _ (GK_le_fix K (pow_mem hxK a))).1 j₀).1 (pow_mem hxG₀ a)⟩, ?_⟩
    have h5 := (hG K h (GK_le_fix K (hH hh))).2.1 hh
    simp only [map_mul, h5, one_mul, map_pow, Units.val_pow_eq_pow_val]
    ring) h3
  rw [hA.closure_eq] at h4
  obtain ⟨g', ⟨h5, h6⟩, h7⟩ := h4
  refine ⟨g', h5, h6, ?_⟩
  simpa using h7

/- English proof (translation)
Take `⟨-, -, hG⟩` from `cyc_basic l χ hχ`. Establish `dec : ∀ x : ↥(GK K), ∃ x' : ↥(GK K), ‖(χ x' : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)) ∧ x * x'⁻¹ ∈ U ∧ ‖(χ x : ℚ_[l]) ^ d - 1‖ = ‖(χ x' : ℚ_[l]) - 1‖`. Introduce `x`. Take `⟨x', hx', h1, h2⟩` from `exists_principal ha hχ K hH hj hN hpow x x.2`. Establish `h2' : χ x' ^ N = χ x ^ N` using `Units.ext (by simpa using h2)`.

Establish `h3 : χ ((x * (⟨x', hx'⟩ : ↥(GK K))⁻¹ : ↥(GK K)) : GQ l) ^ N = 1`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_pow, inv_pow, h2', mul_inv_cancel]`. Use `⟨⟨x', hx'⟩, h1, htor _ h3, ?_⟩` and prove the remaining obligations. Establish `h4` using `hNd _ (x * (⟨x', hx'⟩ : ↥(GK K))⁻¹).2 h3`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_pow, inv_pow, mul_inv_eq_one] at h4`.

Rewrite using `[← Units.val_pow_eq_pow_val, h4, Units.val_pow_eq_pow_val, norm_pow_sub_one hj h1 hd]`. Take `⟨g', h1, h2, h3⟩` from `dec g`. Take `⟨γ', k1, k2, k3⟩` from `dec γ`. Establish `hγ' : γ' ∈ U` using `by simpa using mul_mem (inv_mem k2) hγU`. Establish `hle` using `hγ g`.

Rewrite `hle` using `[h3, k3]`. It suffices to establish `g' ∈ U by simpa using mul_mem h2 this`. Distinguish the cases in `h0 : (χ γ' : ℚ_[l]) - 1 = 0`. Rewrite `hle` using `[h0, norm_zero, norm_le_zero_iff, sub_eq_zero]`. Establish `: χ g' = 1` using `Units.ext hle`.

Conclude with `htor _ (by rw [this, one_pow])`. Take `⟨j, hjj, e⟩` from `exists_norm_eq h0 k1`. Use `mem_of_gen ha hχ K (lev_mono hj hjj) (GK K).subtype Topology.IsInducing.subtypeVal U hU (fun h hh => ⟨⟨h, hH hh⟩, htor _ ?_, rfl⟩) γ' hγ' ⟨((hG K _ (GK_le_fix K γ'.2)).1 j).2 e.le, e⟩ g' (((hG K _ (GK_le_fix K g'.2)).1 j).2 (hle.trans e.le))` and prove the remaining obligations. Rewrite using `[(hG K h (GK_le_fix K (hH hh))).2.1 hh, one_pow]`.
-/
theorem mem_of_tors_gen {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (hH : Hinf K ≤ GK K) {j₀ N d : ℕ}
    (hj : Lev l j₀) (hN : ¬ l ∣ N) (hd : ¬ l ∣ d)
    (hpow : ∀ g ∈ GK K, ‖(χ g : ℚ_[l]) ^ N - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)))
    (hNd : ∀ g ∈ GK K, χ g ^ N = 1 → χ g ^ d = 1)
    (U : Subgroup ↥(GK K)) (hU : IsClosed (U : Set ↥(GK K)))
    (htor : ∀ g : ↥(GK K), χ g ^ N = 1 → g ∈ U) (γ : ↥(GK K)) (hγU : γ ∈ U)
    (hγ : ∀ g : ↥(GK K), ‖(χ g : ℚ_[l]) ^ d - 1‖ ≤ ‖(χ γ : ℚ_[l]) ^ d - 1‖) (g : ↥(GK K)) :
    g ∈ U := by
  obtain ⟨-, -, hG⟩ := cyc_basic l χ hχ
  have dec : ∀ x : ↥(GK K), ∃ x' : ↥(GK K), ‖(χ x' : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)) ∧
      x * x'⁻¹ ∈ U ∧ ‖(χ x : ℚ_[l]) ^ d - 1‖ = ‖(χ x' : ℚ_[l]) - 1‖ := by
    intro x
    obtain ⟨x', hx', h1, h2⟩ := exists_principal ha hχ K hH hj hN hpow x x.2
    have h2' : χ x' ^ N = χ x ^ N := Units.ext (by simpa using h2)
    have h3 : χ ((x * (⟨x', hx'⟩ : ↥(GK K))⁻¹ : ↥(GK K)) : GQ l) ^ N = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_pow, inv_pow, h2',
        mul_inv_cancel]
    refine ⟨⟨x', hx'⟩, h1, htor _ h3, ?_⟩
    have h4 := hNd _ (x * (⟨x', hx'⟩ : ↥(GK K))⁻¹).2 h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_pow, inv_pow,
      mul_inv_eq_one] at h4
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_pow_eq_pow_val, norm_pow_sub_one hj h1 hd]
  obtain ⟨g', h1, h2, h3⟩ := dec g
  obtain ⟨γ', k1, k2, k3⟩ := dec γ
  have hγ' : γ' ∈ U := by simpa using mul_mem (inv_mem k2) hγU
  have hle := hγ g
  rw [h3, k3] at hle
  suffices g' ∈ U by simpa using mul_mem h2 this
  by_cases h0 : (χ γ' : ℚ_[l]) - 1 = 0
  · rw [h0, norm_zero, norm_le_zero_iff, sub_eq_zero] at hle
    have : χ g' = 1 := Units.ext hle
    exact htor _ (by rw [this, one_pow])
  obtain ⟨j, hjj, e⟩ := exists_norm_eq h0 k1
  refine mem_of_gen ha hχ K (lev_mono hj hjj) (GK K).subtype Topology.IsInducing.subtypeVal U hU
    (fun h hh => ⟨⟨h, hH hh⟩, htor _ ?_, rfl⟩) γ' hγ'
    ⟨((hG K _ (GK_le_fix K γ'.2)).1 j).2 e.le, e⟩ g'
    (((hG K _ (GK_le_fix K g'.2)).1 j).2 (hle.trans e.le))
  rw [(hG K h (GK_le_fix K (hH hh))).2.1 hh, one_pow]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Distinguish the cases in `h2 : l = 2`. Take `⟨i, hi⟩` from `hi h2`. Use `⟨2, 1, ⟨by norm_num, fun _ => le_rfl⟩, hl.not_dvd_one, fun _ => rfl, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hi' : (i : Om l) ^ 2 = -1` using `by exact_mod_cast congrArg Subtype.val hi`.

Establish `hp : IsPrimitiveRoot (i : Om l) (l ^ 2)`. Establish `h3 : ¬ (i : Om l) ^ l ^ 1 = 1`. Rewrite using `[pow_one, show (i : Om l) ^ l = (i : Om l) ^ 2 by rw [← h2], hi']`. Evaluate the numerical expressions. Establish `h4 : (i : Om l) ^ l ^ (1 + 1) = 1`.

Rewrite using `[show l ^ (1 + 1) = 2 * 2 by rw [h2]; norm_num, pow_mul, hi']`. Evaluate the numerical expressions. Rewrite using `[show l ^ 2 = l ^ (1 + 1) from rfl, ← orderOf_eq_prime_pow h3 h4]`. Conclude with `IsPrimitiveRoot.orderOf _`. Rewrite using `[pow_one]`.

Conclude with `hχ.norm_sub_one_le_of_prim g 2 hp (hg i)`. Use `⟨1, l - 1, ⟨le_rfl, fun e => absurd e h2⟩, ?_, fun e => absurd e h2, fun g _ => ?_⟩` and prove the remaining obligations. Use `hl.two_le` as an intermediate fact. Conclude with `Nat.not_dvd_of_pos_of_lt (by omega) (by omega)`. Set `u : ℤ_[l]` to `⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩`.

Establish `hu : IsUnit u` using `PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)`. Establish `h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0`. Rewrite using `[map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]`. Establish `h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1}`. Rewrite using `[pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]`.

Conclude with `h3`. Establish `h5` using `(PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4`. Rewrite `h5` using `[PadicInt.norm_def]`. Conclude with `h5`.
-/
theorem exists_level {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l)
    (hi : l = 2 → ∃ i : ↥K.1, i ^ 2 = -1) :
    ∃ j₀ N : ℕ, Lev l j₀ ∧ ¬ l ∣ N ∧ (l = 2 → N = 1) ∧
      ∀ g ∈ GK K, ‖(χ g : ℚ_[l]) ^ N - 1‖ ≤ (l : ℝ) ^ (-(j₀ : ℤ)) := by
  have hl : l.Prime := Fact.out
  by_cases h2 : l = 2
  · obtain ⟨i, hi⟩ := hi h2
    refine ⟨2, 1, ⟨by norm_num, fun _ => le_rfl⟩, hl.not_dvd_one, fun _ => rfl, fun g hg => ?_⟩
    have hi' : (i : Om l) ^ 2 = -1 := by exact_mod_cast congrArg Subtype.val hi
    have hp : IsPrimitiveRoot (i : Om l) (l ^ 2) := by
      have h3 : ¬ (i : Om l) ^ l ^ 1 = 1 := by
        rw [pow_one, show (i : Om l) ^ l = (i : Om l) ^ 2 by rw [← h2], hi']
        norm_num
      have h4 : (i : Om l) ^ l ^ (1 + 1) = 1 := by
        rw [show l ^ (1 + 1) = 2 * 2 by rw [h2]; norm_num, pow_mul, hi']
        norm_num
      rw [show l ^ 2 = l ^ (1 + 1) from rfl, ← orderOf_eq_prime_pow h3 h4]
      exact IsPrimitiveRoot.orderOf _
    rw [pow_one]
    exact hχ.norm_sub_one_le_of_prim g 2 hp (hg i)
  · refine ⟨1, l - 1, ⟨le_rfl, fun e => absurd e h2⟩, ?_, fun e => absurd e h2, fun g _ => ?_⟩
    · have := hl.two_le
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    · let u : ℤ_[l] := ⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩
      have hu : IsUnit u := PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)
      have h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0 := by
        rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]
      have h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
        rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
        exact h3
      have h5 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4
      rw [PadicInt.norm_def] at h5
      exact h5

/- English proof (translation)
Establish `h0 : ∀ z : ℚ_[l], 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 z) ↔ ‖z‖ ≤ 1`. Introduce `z`. Rewrite using `[P.v_O]`. Express the relevant statement in the definitionally equal form `IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 z) ↔ _`. Rewrite using `[isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective, IsIntegrallyClosed.isIntegral_iff]`.

Conclude with `⟨fun ⟨w, hw⟩ => hw ▸ w.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ≠ ⊤` using `by simpa using hx`. Establish `e : y = x * (y / x)` using `by field_simp`.

Establish `h1 : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) = P.v LL (algebraMap ℚ_[l] ↥LL.1 x) + P.v LL (algebraMap ℚ_[l] ↥LL.1 (y / x))`. Rewrite using `[← AddValuation.map_mul, ← map_mul, ← e]`. Rewrite using `[h1]`. Use `conv_lhs => lhs`. Rewrite using `[← add_zero (P.v LL (algebraMap ℚ_[l] ↥LL.1 x))]`.

Rewrite using `[WithTop.add_le_add_iff_left hv, h0, norm_div, div_le_one (norm_pos_iff.2 hx)]`.
-/
theorem v_le_iff (P : LocPrime l) (LL : FinExt l) (x y : ℚ_[l]) :
    P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔ ‖y‖ ≤ ‖x‖ := by
  have h0 : ∀ z : ℚ_[l], 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 z) ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [P.v_O]
    change IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 z) ↔ _
    rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective,
      IsIntegrallyClosed.isIntegral_iff]
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  by_cases hx : x = 0
  · simp [hx]
  have hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ≠ ⊤ := by simpa using hx
  have e : y = x * (y / x) := by field_simp
  have h1 : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) =
      P.v LL (algebraMap ℚ_[l] ↥LL.1 x) + P.v LL (algebraMap ℚ_[l] ↥LL.1 (y / x)) := by
    rw [← AddValuation.map_mul, ← map_mul, ← e]
  rw [h1]
  conv_lhs => lhs; rw [← add_zero (P.v LL (algebraMap ℚ_[l] ↥LL.1 x))]
  rw [WithTop.add_le_add_iff_left hv, h0, norm_div, div_le_one (norm_pos_iff.2 hx)]

/- English proof (translation)
Rewrite using `[map_pow, map_natCast, AddValuation.map_pow, P.v_l]`. Simplify using the standard rewrite rules.
-/
theorem v_pow (P : LocPrime l) (LL : FinExt l) (s : ℕ) :
    P.v LL (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ s)) = (s : WithTop ℚ) := by
  rw [map_pow, map_natCast, AddValuation.map_pow, P.v_l]
  simp

/- English proof (translation)
Rewrite using `[norm_pow, Padic.norm_p]`. Simplify using the standard rewrite rules.
-/
theorem norm_l_pow (s : ℕ) : ‖(l : ℚ_[l]) ^ s‖ = (l : ℝ) ^ (-(s : ℤ)) := by
  rw [norm_pow, Padic.norm_p]; simp

/- English proof (translation)
Use `haveI : Module.Flat ℤ_[l] ↥(OL LL) := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `x ⟨⟨a, ha⟩, hx⟩`. Establish `h1 : algebraMap ℤ_[l] ↥(OL LL) a * x = 0` using `by rw [← Algebra.smul_def]; exact hx`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases.

It suffices to derive a contradiction. Apply `nonZeroDivisors.ne_zero ha` to reduce the goal to its premises. Establish `h2 : algebraMap ℚ_[l] ↥LL.1 (a : ℚ_[l]) = 0` using `congrArg Subtype.val h`. Conclude with `PadicInt.coe_eq_zero.1 ((map_eq_zero _).1 h2)`. Conclude with `h`.

Establish `h : Function.Injective (algebraMap ℤ_[l] (WCb l))` using `(WittVector.map_injective _ (ZMod.castHom (dvd_refl l) (Cb l)).injective).comp (WittVector.equiv l).symm.injective`. Conclude with `Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) h`.
-/
theorem algebraMap_RW_injective (LL : FinExt l) :
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h1 : algebraMap ℤ_[l] ↥(OL LL) a * x = 0 := by rw [← Algebra.smul_def]; exact hx
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      apply nonZeroDivisors.ne_zero ha
      have h2 : algebraMap ℚ_[l] ↥LL.1 (a : ℚ_[l]) = 0 := congrArg Subtype.val h
      exact PadicInt.coe_eq_zero.1 ((map_eq_zero _).1 h2)
    · exact h
  have h : Function.Injective (algebraMap ℤ_[l] (WCb l)) :=
    (WittVector.map_injective _ (ZMod.castHom (dvd_refl l) (Cb l)).injective).comp
      (WittVector.equiv l).symm.injective
  exact Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) h

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a w => simp [h]`.
-/
theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g f' g' : W →ₐ[Z] W) (h : ∀ w, f (g w) = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a w => simp [h]`.
-/
theorem map_id_comp {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f f' g' : W →ₐ[Z] W) (h : ∀ w, f w = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f x =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w => simp [h]

/- English proof (translation)
The claim follows from `map_id_comp _ _ _ (fun w => by simp) x`.
-/
theorem gRW_mul {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g h : GQ l) (x : RW LL) :
    AI.gRW LL (g * h) x = AI.gRW LL g (AI.gRW LL h x) :=
  map_id_comp _ _ _ (fun w => by simp) x

/- English proof (translation)
Use `map_id_comm _ _ _ _ (fun w => ?_) x` and prove the remaining obligations. Use extensionality with `n`. Express the relevant statement in the definitionally equal form `(WittVector.map (frobenius (Cb l) l) (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n = (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n`. Simplify using `[WittVector.map_coeff, frobenius_def]`.
-/
theorem phi_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (x : RW LL) :
    φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

/- English proof (translation)
Use `haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubalgebra.toSubring)`. Set `b` to `Module.finBasis ↥LL.1 T.V`. Conclude with `T2Space.of_injective_continuous b.equivFun.injective (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)`.
-/
theorem t2Space_localLattice_representationSpace {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : T2Space T.V := by
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubalgebra.toSubring)
  let b := Module.finBasis ↥LL.1 T.V
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

end Galois

section Wach

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))

/- English proof (translation)
Rewrite using `[W.χΓ_res, P.PD_χ]`.
-/
theorem chi_res (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (W.χΓ (W.resΓ g) : ↥(OL LL)) =
      algebraMap ℚ_[l] ↥LL.1 (P.χQ g : ℚ_[l]) := by
  rw [W.χΓ_res, P.PD_χ]

/- English proof (translation)
Establish `h1 : algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g ^ k) : ↥(OL LL))) = algebraMap ℚ_[l] ↥LL.1 ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l])`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, chi_res]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h1` using `[h, map_one, Units.val_one, map_one]`.

Conclude with `Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (by rw [← h1]; simp))`. Introduce `h`. Rewrite `h1` using `[h, Units.val_one, map_one]`. Apply `W.χΓ_inj` to reduce the goal to its premises. Rewrite using `[map_one]`.

Conclude with `Units.ext (Subtype.ext h1)`.
-/
theorem res_pow_eq_one_iff (g : ↥(GK K)) (k : ℕ) : W.resΓ g ^ k = 1 ↔ P.χQ g ^ k = 1 := by
  have h1 : algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g ^ k) : ↥(OL LL))) =
      algebraMap ℚ_[l] ↥LL.1 ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, chi_res]
  constructor
  · intro h
    rw [h, map_one, Units.val_one, map_one] at h1
    exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (by rw [← h1]; simp))
  · intro h
    rw [h, Units.val_one, map_one] at h1
    apply W.χΓ_inj
    rw [map_one]
    exact Units.ext (Subtype.ext h1)

/- English proof (translation)
Rewrite using `[W.GKs_def, P.PD_χ, ← norm_l_pow, ← v_le_iff P LL, v_pow, (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]`.
-/
theorem mem_GKs_iff (g : ↥(GK K)) :
    g ∈ W.GKs ↔ ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(W.s : ℤ)) := by
  rw [W.GKs_def, P.PD_χ, ← norm_l_pow, ← v_le_iff P LL, v_pow,
    (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]

/- English proof (translation)
Establish `h` using `W.gam_gen`. Rewrite `h` using `[← hg, chi_res, ← v_pow P LL, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]`. Rewrite using `[← norm_l_pow]`. Conclude with `le_antisymm ((v_le_iff P LL _ _).1 h.ge) ((v_le_iff P LL _ _).1 h.le)`.
-/
theorem norm_of_res_gam (g : ↥(GK K)) (hg : W.resΓ g = W.gam) :
    ‖(P.χQ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(W.s : ℤ)) := by
  have h := W.gam_gen
  rw [← hg, chi_res, ← v_pow P LL, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub] at h
  rw [← norm_l_pow]
  exact le_antisymm ((v_le_iff P LL _ _).1 h.ge) ((v_le_iff P LL _ _).1 h.le)

/- English proof (translation)
Establish `h` using `W.gamK_gen (W.resΓ g)`. Rewrite `h` using `[← hγ, map_pow, map_pow, chi_res, chi_res]`. Rewrite using `[← v_le_iff P LL]`. Simplify `h` using `only [map_sub, map_pow, map_one]`.
-/
theorem norm_of_res_gamK (γ g : ↥(GK K)) (hγ : W.resΓ γ = W.gamK) :
    ‖(P.χQ g : ℚ_[l]) ^ W.DelF.card - 1‖ ≤ ‖(P.χQ γ : ℚ_[l]) ^ W.DelF.card - 1‖ := by
  have h := W.gamK_gen (W.resΓ g)
  rw [← hγ, map_pow, map_pow, chi_res, chi_res] at h
  rw [← v_le_iff P LL]
  simpa only [map_sub, map_pow, map_one] using h

/- English proof (translation)
Rewrite using `[W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`.
-/
theorem mem_DelF_iff (x : W.Gam) : x ∈ W.DelF ↔ x ∈ CommGroup.torsion W.Gam := by
  rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]

/- English proof (translation)
The claim follows from `Nat.subtype_card _ (mem_DelF_iff W)`.
-/
theorem card_torsion : Nat.card ↥(CommGroup.torsion W.Gam) = W.DelF.card :=
  Nat.subtype_card _ (mem_DelF_iff W)

/- English proof (translation)
Introduce `g hg`. Use `(res_pow_eq_one_iff W g 1).1 (by rw [pow_one]; exact hg)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Rewrite using `[mem_GKs_iff, this, Units.val_one, sub_self, norm_zero]`. Check the signs of the components of the expression.
-/
theorem ker_le_GKs : W.resΓ.ker ≤ W.GKs := by
  intro g hg
  have := (res_pow_eq_one_iff W g 1).1 (by rw [pow_one]; exact hg)
  rw [pow_one] at this
  rw [mem_GKs_iff, this, Units.val_one, sub_self, norm_zero]
  positivity

end Wach

/- English proof (translation)
Simplify using `[herrCocycles, h]`.
-/
theorem mem_herrCocycles_of_eq {O D : Type} [CommRing O] [AddCommGroup D] [Module O D] (γ φ : D →ₗ[O] D)
    (y z : D) (h : γ y - y = φ z - z) : (y, z) ∈ herrCocycles γ φ := by
  simp [herrCocycles, h]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW F h9 l _ K s LL h S E`. Take `⟨hF, hD⟩` from `h9 l K s LL h`. Establish `hl : l.Prime` using `Fact.out`. Set `P` to `D.loc l`. Set `W` to `(HW l).W K s LL h`.

Establish `hWs : W.s = s` using `(HW l).W_s K s LL h`. Establish `hχ : IsCyc P.χQ` using `P.χQ_cyc`. Establish `ha : IsActC (D.locA l).actC` using `⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩`. Take `⟨-, -, hG⟩` from `cyc_basic l P.χQ hχ`. Establish `hmul : ∀ g h x, S.gR (g * h) x = S.gR g (S.gR h x)` using `fun g h x => gRW_mul (D.locA l) LL _ _ x`.

Establish `hφ : ∀ g x, S.φR (S.gR g x) = S.gR g (S.φR x)` using `fun g x => phi_gRW (D.locA l) LL _ x`. Establish `hinj : Function.Injective (algebraMap S.O S.RW)` using `algebraMap_RW_injective LL`. Establish `hT : ∀ T : LocLat S.G S.Qp S.LL S.O, T2Space T.V` using `fun T => t2Space_localLattice_representationSpace LL T`. Establish `hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup` using `fun x hx y => hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩`. Establish `hH : Hinf K ≤ GK K`.

Introduce `x hx`. Establish `h1 : x ∈ Gj K s` using `((hG K x (hH0 x hx)).1 s).2 (by`. Rewrite using `[(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]`. Use the proof step `positivity)`. Conclude with `fun y => h1 ⟨y.1, h.2.2.1 y.2⟩`.

Use `⟨fun hi T => ?_, fun T => ?_⟩` and prove the remaining obligations. Take `⟨j₀, N, hj, hN, hN2, hpow⟩` from `exists_level hχ K (fun e => hi ((P.PD_p K).trans e))`. Establish `hN0 : N ≠ 0` using `by rintro rfl; exact hN (dvd_zero _)`. Establish `htor : ∀ δ ∈ W.DelF, δ ^ N = 1`. Introduce `δ hδ`.

Take `⟨g, rfl⟩` from `W.resΓ_onto δ`. Take `⟨k, hk, hk'⟩` from `(W.DelF_def _).1 hδ`. Rewrite `hk'`, the goal using `[res_pow_eq_one_iff]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one]`.

Use `eq_one_of_pow hj (hpow g g.2) hk.ne' ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]`. Establish `h1Δ : (1 : W.Gam) ∈ W.DelF` using `(mem_DelF_iff W _).2 (one_mem _)`. Establish `hd : ¬ l ∣ W.DelF.card`. Introduce `hdv`.

Use `haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by`. Rewrite using `[card_torsion]`. Conclude with `Finset.card_ne_zero.2 ⟨1, h1Δ⟩)`. Rewrite `hdv` using `[← card_torsion]`. Take `⟨x, hx⟩` from `exists_prime_orderOf_dvd_card' l hdv`.

Apply `hN` to reduce the goal to its premises. Rewrite using `[← hx, orderOf_dvd_iff_pow_eq_one]`. Conclude with `Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2))`. Establish `hu : IsUnit (W.DelF.card : ↥(OL LL))`. Establish `h1 : IsUnit (W.DelF.card : ℤ_[l])`.

Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl).2 hd`. Simplify using `using h1.map (algebraMap ℤ_[l] ↥(OL LL))`. Establish `h2 : S.PD.p = 2 → W.DelF = {1}`. Introduce `e`.

Rewrite using `[Finset.eq_singleton_iff_unique_mem]`. Use `⟨h1Δ, fun x hx => ?_⟩` and prove the remaining obligations. Use `htor x hx` as an intermediate fact. Rewrite `this` using `[hN2 ((P.PD_p K).symm.trans e), pow_one]`. Then use the resulting hypothesis. Establish `hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ N = 1 → W.resΓ g ∈ W.DelF` using `fun g hg => (W.DelF_def _).2 ⟨N, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g N).2 hg⟩`.

Establish `hden : ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) → (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = W.gamK) → g ∈ U) → ∀ g, g ∈ U`. Introduce `U hU hp g`. Take `⟨γ, hγ⟩` from `W.resΓ_onto W.gamK`. Use `mem_of_tors_gen ha hχ K hH hj hN hd hpow (fun x hx hx' => ?_) U hU (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ (hp γ (Or.inr hγ)) (fun x => norm_of_res_gamK W γ x hγ) g` and prove the remaining obligations. Use `(res_pow_eq_one_iff W ⟨x, hx⟩ _).1 ?_` and prove the remaining obligations.

Establish `h3` using `pow_card_eq_one' (x := (⟨_, (mem_DelF_iff W _).1 (hmemΔ ⟨x, hx⟩ hx')⟩ : ↥(CommGroup.torsion W.Gam)))`. Rewrite `h3` using `[card_torsion]`. Conclude with `congrArg Subtype.val h3`. Use `haveI := hT T`. Take `⟨k1, k2⟩` from `onto_and_kernel E hmul hφ hinj hF hD T (MonoidHom.id S.G) (Hker S).subtype continuous_subtype_val (fun _ => rfl) (fun _ _ e => e) T.ρ (fun _ _ => rfl) T.L rfl S.W.DelF h1Δ (fun x hx y hy => (mem_DelF_iff W _).2 (mul_mem ((mem_DelF_iff W _).1 hx) ((mem_DelF_iff W _).1 hy))) (fun x …`.

Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `δ hδ`. Simplify using `[h3 δ hδ]⟩)`. Use the proof step `(S.W.clK T) (E.clK_def h2 T)`. Use `⟨k1, k2, fun T' f pr pr' e => ?_⟩` and prove the remaining obligations.

Use `haveI := hT T'`. Conclude with `clK_natural E hinj hF h2 hden T T' f pr pr' e`. Use `haveI := hT T`. Take `⟨γ, hγ⟩` from `W.resΓ_onto W.gam`. Establish `hγs : γ ∈ W.GKs` using `(mem_GKs_iff W γ).2 (norm_of_res_gam W γ hγ).le`.

Establish `hden : ∀ U : Subgroup ↥W.GKs, IsClosed (U : Set ↥W.GKs) → (∀ g : ↥W.GKs, (W.resΓ g ∈ ({1} : Finset W.Gam) ∨ W.resΓ g = W.gam) → g ∈ U) → ∀ g, g ∈ U`. Introduce `U hU hp g`. Use `mem_of_gen (j := W.s) ha hχ K (hWs ▸ ⟨h.1, h.2.1⟩) ((GK K).subtype.comp W.GKs.subtype) (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal) U hU (fun x hx => ?_) ⟨γ, hγs⟩ (hp _ (Or.inr hγ)) ⟨((hG K _ (GK_le_fix K γ.2)).1 _).2 (norm_of_res_gam W γ hγ).le, norm_of_r …` and prove the remaining obligations. Establish `h1 : W.resΓ ⟨x, hH hx⟩ = 1`. Use `(res_pow_eq_one_iff W ⟨x, hH hx⟩ 1).2 (by` as an intermediate fact.

Rewrite using `[pow_one]`. Conclude with `(hG K x (hH0 x hx)).2.1 hx)`. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Conclude with `⟨⟨⟨x, hH hx⟩, ker_le_GKs W h1⟩, hp _ (Or.inl (Finset.mem_singleton.2 h1)), rfl⟩`. Take `⟨k1, k2⟩` from `onto_and_kernel E hmul hφ hinj hF hD T S.W.GKs.subtype (Subgroup.inclusion (ker_le_GKs W)) (continuous_inclusion (ker_le_GKs W)) (fun _ => rfl) Subtype.val_injective (T.ρ.comp S.W.GKs.subtype) (fun _ _ => rfl) (resLat T S.W.GKs) rfl {1} (Finset.mem_singleton_self _) (by simp) (by …`.

Take `⟨c, hc, hc'⟩` from `E.cl_def T pr b hb`. Conclude with `⟨c, hc, fun g t ht => ⟨fun hg => (hc' g t ht).1 (Finset.mem_singleton.1 hg), (hc' g t ht).2⟩⟩)`. Use `⟨k1, fun w => (k2 w).trans ⟨fun ⟨m, _, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, ?_, hm⟩⟩⟩` and prove the remaining obligations. Introduce `δ hδ`. Rewrite using `[Finset.mem_singleton.1 hδ, S.W.γD_one]`.
-/
theorem herr_a : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; HerrAat S ∧ HerrAsat S := by
  intro D HW F h9 l _ K s LL h S E
  obtain ⟨hF, hD⟩ := h9 l K s LL h
  have hl : l.Prime := Fact.out
  let P := D.loc l
  let W := (HW l).W K s LL h
  have hWs : W.s = s := (HW l).W_s K s LL h
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have ha : IsActC (D.locA l).actC := ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩
  obtain ⟨-, -, hG⟩ := cyc_basic l P.χQ hχ
  have hmul : ∀ g h x, S.gR (g * h) x = S.gR g (S.gR h x) := fun g h x =>
    gRW_mul (D.locA l) LL _ _ x
  have hφ : ∀ g x, S.φR (S.gR g x) = S.gR g (S.φR x) := fun g x => phi_gRW (D.locA l) LL _ x
  have hinj : Function.Injective (algebraMap S.O S.RW) := algebraMap_RW_injective LL
  have hT : ∀ T : LocLat S.G S.Qp S.LL S.O, T2Space T.V := fun T => t2Space_localLattice_representationSpace LL T
  have hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup := fun x hx y =>
    hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩
  have hH : Hinf K ≤ GK K := by
    intro x hx
    have h1 : x ∈ Gj K s := ((hG K x (hH0 x hx)).1 s).2 (by
      rw [(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]
      positivity)
    exact fun y => h1 ⟨y.1, h.2.2.1 y.2⟩
  refine ⟨fun hi T => ?_, fun T => ?_⟩
  · obtain ⟨j₀, N, hj, hN, hN2, hpow⟩ := exists_level hχ K (fun e => hi ((P.PD_p K).trans e))
    have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
    have htor : ∀ δ ∈ W.DelF, δ ^ N = 1 := by
      intro δ hδ
      obtain ⟨g, rfl⟩ := W.resΓ_onto δ
      obtain ⟨k, hk, hk'⟩ := (W.DelF_def _).1 hδ
      rw [res_pow_eq_one_iff] at hk' ⊢
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      refine eq_one_of_pow hj (hpow g g.2) hk.ne' ?_
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]
    have h1Δ : (1 : W.Gam) ∈ W.DelF := (mem_DelF_iff W _).2 (one_mem _)
    have hd : ¬ l ∣ W.DelF.card := by
      intro hdv
      haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by
        rw [card_torsion]; exact Finset.card_ne_zero.2 ⟨1, h1Δ⟩)
      rw [← card_torsion] at hdv
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdv
      apply hN
      rw [← hx, orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2))
    have hu : IsUnit (W.DelF.card : ↥(OL LL)) := by
      have h1 : IsUnit (W.DelF.card : ℤ_[l]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd hl).2 hd
      simpa using h1.map (algebraMap ℤ_[l] ↥(OL LL))
    have h2 : S.PD.p = 2 → W.DelF = {1} := by
      intro e
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨h1Δ, fun x hx => ?_⟩
      have := htor x hx
      rwa [hN2 ((P.PD_p K).symm.trans e), pow_one] at this
    have hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ N = 1 → W.resΓ g ∈ W.DelF := fun g hg =>
      (W.DelF_def _).2 ⟨N, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g N).2 hg⟩
    have hden : ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) →
        (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = W.gamK) → g ∈ U) → ∀ g, g ∈ U := by
      intro U hU hp g
      obtain ⟨γ, hγ⟩ := W.resΓ_onto W.gamK
      refine mem_of_tors_gen ha hχ K hH hj hN hd hpow (fun x hx hx' => ?_) U hU
        (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ (hp γ (Or.inr hγ))
        (fun x => norm_of_res_gamK W γ x hγ) g
      refine (res_pow_eq_one_iff W ⟨x, hx⟩ _).1 ?_
      have h3 := pow_card_eq_one' (x := (⟨_, (mem_DelF_iff W _).1 (hmemΔ ⟨x, hx⟩ hx')⟩ :
        ↥(CommGroup.torsion W.Gam)))
      rw [card_torsion] at h3
      exact congrArg Subtype.val h3
    haveI := hT T
    obtain ⟨k1, k2⟩ := onto_and_kernel E hmul hφ hinj hF hD T (MonoidHom.id S.G) (Hker S).subtype
      continuous_subtype_val (fun _ => rfl) (fun _ _ e => e) T.ρ (fun _ _ => rfl) T.L rfl
      S.W.DelF h1Δ
      (fun x hx y hy => (mem_DelF_iff W _).2
        (mul_mem ((mem_DelF_iff W _).1 hx) ((mem_DelF_iff W _).1 hy)))
      (fun x hx => (mem_DelF_iff W _).2 (inv_mem ((mem_DelF_iff W _).1 hx)))
      (fun δ _ => S.W.resΓ_onto δ) hu S.W.gamK (S.W.resΓ_onto _) hden (S.W.wachCocyclesDelta T)
      (fun y z h1 h3 => ⟨mem_herrCocycles_of_eq _ _ y z h1, by
        simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
        intro δ hδ
        simp [h3 δ hδ]⟩)
      (S.W.clK T) (E.clK_def h2 T)
    refine ⟨k1, k2, fun T' f pr pr' e => ?_⟩
    haveI := hT T'
    exact clK_natural E hinj hF h2 hden T T' f pr pr' e
  · haveI := hT T
    obtain ⟨γ, hγ⟩ := W.resΓ_onto W.gam
    have hγs : γ ∈ W.GKs := (mem_GKs_iff W γ).2 (norm_of_res_gam W γ hγ).le
    have hden : ∀ U : Subgroup ↥W.GKs, IsClosed (U : Set ↥W.GKs) →
        (∀ g : ↥W.GKs, (W.resΓ g ∈ ({1} : Finset W.Gam) ∨ W.resΓ g = W.gam) → g ∈ U) →
        ∀ g, g ∈ U := by
      intro U hU hp g
      refine mem_of_gen (j := W.s) ha hχ K (hWs ▸ ⟨h.1, h.2.1⟩)
        ((GK K).subtype.comp W.GKs.subtype)
        (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal) U hU
        (fun x hx => ?_) ⟨γ, hγs⟩ (hp _ (Or.inr hγ))
        ⟨((hG K _ (GK_le_fix K γ.2)).1 _).2 (norm_of_res_gam W γ hγ).le, norm_of_res_gam W γ hγ⟩ g
        (((hG K _ (GK_le_fix K g.1.2)).1 _).2 ((mem_GKs_iff W g.1).1 g.2))
      have h1 : W.resΓ ⟨x, hH hx⟩ = 1 := by
        have := (res_pow_eq_one_iff W ⟨x, hH hx⟩ 1).2 (by
          rw [pow_one]; exact (hG K x (hH0 x hx)).2.1 hx)
        rwa [pow_one] at this
      exact ⟨⟨⟨x, hH hx⟩, ker_le_GKs W h1⟩, hp _ (Or.inl (Finset.mem_singleton.2 h1)), rfl⟩
    obtain ⟨k1, k2⟩ := onto_and_kernel E hmul hφ hinj hF hD T S.W.GKs.subtype
      (Subgroup.inclusion (ker_le_GKs W)) (continuous_inclusion (ker_le_GKs W)) (fun _ => rfl)
      Subtype.val_injective (T.ρ.comp S.W.GKs.subtype) (fun _ _ => rfl) (resLat T S.W.GKs) rfl
      {1} (Finset.mem_singleton_self _) (by simp) (by simp)
      (fun δ hδ => ⟨1, by rw [Finset.mem_singleton.1 hδ, map_one, map_one]⟩) (by simp) S.W.gam
      ⟨⟨γ, hγs⟩, hγ⟩ hden (S.W.divisibleCocycles T) (fun y z h1 _ => mem_herrCocycles_of_eq _ _ y z h1) (S.W.cl T)
      (fun pr b hb => by
        obtain ⟨c, hc, hc'⟩ := E.cl_def T pr b hb
        exact ⟨c, hc, fun g t ht =>
          ⟨fun hg => (hc' g t ht).1 (Finset.mem_singleton.1 hg), (hc' g t ht).2⟩⟩)
    refine ⟨k1, fun w => (k2 w).trans ⟨fun ⟨m, _, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, ?_, hm⟩⟩⟩
    intro δ hδ
    rw [Finset.mem_singleton.1 hδ, S.W.γD_one]

end GlobalTheory.HerrClass
