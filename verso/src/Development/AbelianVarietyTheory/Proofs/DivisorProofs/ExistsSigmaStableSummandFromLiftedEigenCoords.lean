import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory.HTSummand

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `C _ I hI A _ H _ _ σ hproj a χ π hπ hσπ F hIF n κ ℓ y hℓ hF hy hδ`. Establish `hl : ∀ k, ∃ l : H →ₗ[C] C, (∀ c x, l (σ c x) = χ (κ k) c * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = ℓ k x` using `fun k => GlobalTheory.T.exists_equivariantLift_functional_quotient_projective I σ hproj (χ (κ k)) (ℓ k) (hℓ k)`. Use `choose l hlσ hlℓ using hl`. Establish `hII : ∀ u v : C, u ∈ I → v ∈ I → u * v = 0`. Introduce `u v hu hv`.

Establish `h` using `Ideal.mul_mem_mul hu hv`. Rewrite `h` using `[← sq, hI]`. Simplify using `using h`. Establish `hσQ : ∀ c, ∀ x ∈ LinearMap.range π, σ c x ∈ LinearMap.range π`. Introduce and unpack `c _ ⟨z, rfl⟩`.

Use `⟨σ c z, ?_⟩` and prove the remaining obligations. Use `show (π * σ c) z = (σ c * π) z`. Rewrite using `[hσπ]`. Set `e : Fin n → Fin n → C` to `fun j m => l j (y m) - if j = m then 1 else 0`. Establish `he : ∀ j m, e j m ∈ I`.

Introduce `j m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `only [e, map_sub, hlℓ, hδ]`. Apply the tactic sequence `split_ifs <;> simp`. Set `x : Fin n → H` to `fun k => y k - ∑ m, e m k • y m`.

Establish `hxQ : ∀ k, x k ∈ LinearMap.range π` using `fun k => Submodule.sub_mem _ (hy k) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy m))`. Establish `hlx : ∀ j k, l j (x k) = if j = k then 1 else 0`. Introduce `j k`. Establish `h1 : ∀ m, e m k * l j (y m) = if j = m then e m k else 0`. Introduce `m`.

Establish `h0` using `hII _ _ (he m k) (he j m)`. Rewrite using `[show l j (y m) = e j m + (if j = m then 1 else 0) by simp [e], mul_add, h0]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [x, map_sub, map_sum, map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_ite_eq]`.

Simplify using `[e]`. Set `G₀ : Submodule C H` to `LinearMap.range π ⊓ ⨅ k, LinearMap.ker (l k)`. Establish `hG : ∀ z, z ∈ G₀ ↔ z ∈ LinearMap.range π ∧ ∀ k, l k z = 0`. Introduce `z`. Simplify using `only [G₀, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`.

Establish `key : ∀ q ∈ LinearMap.range π, q - ∑ k, l k q • x k ∈ G₀`. Introduce `q hq`. Use `(hG _).2 ⟨Submodule.sub_mem _ hq (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩` and prove the remaining obligations. Simplify using `[map_sum, hlx]`. Use `⟨G₀, Submodule.span C (Set.range x), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `z ⟨hzG, hzM⟩`. Rewrite using `[Submodule.mem_bot]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun C).1 hzM`. Establish `hc : ∀ j, c j = 0` using `fun j => by`.

Establish `h` using `((hG _).1 hzG).2 j`. Simplify `h` using `[map_sum, hlx]`. Simplify using `[hc]`. Use `le_antisymm (sup_le inf_le_left (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hxQ k))) ?_` and prove the remaining obligations. Introduce `q hq`.

Rewrite using `[← sub_add_cancel q (∑ k, l k q • x k)]`. Conclude with `Submodule.add_mem_sup (key q hq) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))`. Introduce `c z hz`. Rewrite `hz`, the goal using `[hG]`. Conclude with `⟨hσQ c z hz.1, fun k => by rw [hlσ, hz.2, mul_zero]⟩`.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ (le_inf ((Submodule.smul_mono le_rfl le_top).trans hIF) Submodule.smul_le_right)` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz` using `[hG]`. Conclude with `⟨(hF z hz.1).2 (fun k => by rw [← hlℓ, hz.2 k, map_zero]), hz.1⟩`.

Introduce and unpack `z ⟨hzF, hzQ⟩`. Establish `hlI : ∀ k, l k z ∈ I` using `fun k => by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hlℓ]`. Conclude with `(hF z hzQ).1 hzF k`. Rewrite using `[← sub_add_cancel z (∑ k, l k z • x k)]`.

Conclude with `Submodule.add_mem_sup (key z hzQ) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hlI k) (hxQ k))`. Introduce `d hd`. Establish `hv : ∀ c k, σ c (x k) - χ (κ k) c • x k ∈ G₀`. Introduce `c k`. Use `(hG _).2 ⟨Submodule.sub_mem _ (hσQ c _ (hxQ k)) (Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, hlσ, map_smul, hlx, smul_eq_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Use `⟨fun i => ∑ k ∈ Finset.univ.filter (fun k => κ k = i), l k d • x k, ?_, ?_⟩` and prove the remaining obligations. Introduce `i c`. Simplify using `only [map_sum, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `k hk`.

Rewrite `hk` using `[Finset.mem_filter]`. Rewrite using `[← hk.2, smul_comm, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ (hv c k)`. Rewrite using `[Finset.sum_fiberwise]`. Conclude with `key d hd`.
-/
theorem summand_of_liftedCoords : ∀ {C : Type} [CommRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F →
  ∀ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) →
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) →
    (∀ k, y k ∈ LinearMap.range π) → (∀ j k, ℓ j (y k) = if j = k then 1 else 0) →
  ∃ G₀ M₀ : Submodule C H, G₀ ⊓ M₀ = ⊥ ∧ G₀ ⊔ M₀ = LinearMap.range π ∧ (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) ∧
    G₀ ⊔ I • LinearMap.range π = F ⊓ LinearMap.range π ∧
    ∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀ := by
  intro C _ I hI A _ H _ _ σ hproj a χ π hπ hσπ F hIF n κ ℓ y hℓ hF hy hδ
  have hl : ∀ k, ∃ l : H →ₗ[C] C, (∀ c x, l (σ c x) = χ (κ k) c * l x) ∧
      ∀ x, Ideal.Quotient.mk I (l x) = ℓ k x :=
    fun k => GlobalTheory.T.exists_equivariantLift_functional_quotient_projective I σ hproj (χ (κ k)) (ℓ k) (hℓ k)
  choose l hlσ hlℓ using hl
  have hII : ∀ u v : C, u ∈ I → v ∈ I → u * v = 0 := by
    intro u v hu hv
    have h := Ideal.mul_mem_mul hu hv
    rw [← sq, hI] at h
    simpa using h
  have hσQ : ∀ c, ∀ x ∈ LinearMap.range π, σ c x ∈ LinearMap.range π := by
    rintro c _ ⟨z, rfl⟩
    refine ⟨σ c z, ?_⟩
    show (π * σ c) z = (σ c * π) z
    rw [hσπ]
  let e : Fin n → Fin n → C := fun j m => l j (y m) - if j = m then 1 else 0
  have he : ∀ j m, e j m ∈ I := by
    intro j m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [e, map_sub, hlℓ, hδ]
    split_ifs <;> simp
  let x : Fin n → H := fun k => y k - ∑ m, e m k • y m
  have hxQ : ∀ k, x k ∈ LinearMap.range π := fun k =>
    Submodule.sub_mem _ (hy k) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hy m))
  have hlx : ∀ j k, l j (x k) = if j = k then 1 else 0 := by
    intro j k
    have h1 : ∀ m, e m k * l j (y m) = if j = m then e m k else 0 := by
      intro m
      have h0 := hII _ _ (he m k) (he j m)
      rw [show l j (y m) = e j m + (if j = m then 1 else 0) by simp [e], mul_add, h0]
      split_ifs <;> simp
    simp only [x, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_ite_eq]
    simp [e]
  let G₀ : Submodule C H := LinearMap.range π ⊓ ⨅ k, LinearMap.ker (l k)
  have hG : ∀ z, z ∈ G₀ ↔ z ∈ LinearMap.range π ∧ ∀ k, l k z = 0 := by
    intro z
    simp only [G₀, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  have key : ∀ q ∈ LinearMap.range π, q - ∑ k, l k q • x k ∈ G₀ := by
    intro q hq
    refine (hG _).2 ⟨Submodule.sub_mem _ hq (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (hxQ k)), fun j => ?_⟩
    simp [map_sum, hlx]
  refine ⟨G₀, Submodule.span C (Set.range x), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzG, hzM⟩
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hzM
    have hc : ∀ j, c j = 0 := fun j => by
      have h := ((hG _).1 hzG).2 j
      simpa [map_sum, hlx] using h
    simp [hc]
  · refine le_antisymm (sup_le inf_le_left
      (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hxQ k))) ?_
    intro q hq
    rw [← sub_add_cancel q (∑ k, l k q • x k)]
    exact Submodule.add_mem_sup (key q hq) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · intro c z hz
    rw [hG] at hz ⊢
    exact ⟨hσQ c z hz.1, fun k => by rw [hlσ, hz.2, mul_zero]⟩
  · apply le_antisymm
    · refine sup_le ?_ (le_inf ((Submodule.smul_mono le_rfl le_top).trans hIF)
        Submodule.smul_le_right)
      intro z hz
      rw [hG] at hz
      exact ⟨(hF z hz.1).2 (fun k => by rw [← hlℓ, hz.2 k, map_zero]), hz.1⟩
    · rintro z ⟨hzF, hzQ⟩
      have hlI : ∀ k, l k z ∈ I := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hlℓ]
        exact (hF z hzQ).1 hzF k
      rw [← sub_add_cancel z (∑ k, l k z • x k)]
      exact Submodule.add_mem_sup (key z hzQ) (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem_smul (hlI k) (hxQ k))
  · intro d hd
    have hv : ∀ c k, σ c (x k) - χ (κ k) c • x k ∈ G₀ := by
      intro c k
      refine (hG _).2 ⟨Submodule.sub_mem _ (hσQ c _ (hxQ k)) (Submodule.smul_mem _ _ (hxQ k)),
        fun j => ?_⟩
      rw [map_sub, hlσ, map_smul, hlx, smul_eq_mul]
      split_ifs with h
      · subst h; ring
      · simp
    refine ⟨fun i => ∑ k ∈ Finset.univ.filter (fun k => κ k = i), l k d • x k, ?_, ?_⟩
    · intro i c
      simp only [map_sum, map_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Submodule.sum_mem
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [← hk.2, smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ (hv c k)
    · rw [Finset.sum_fiberwise]
      exact key d hd

end GlobalTheory.HTSummand
