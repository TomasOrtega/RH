import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Gd

section Pt

variable {C : Type} [Field C] {O : Type} [CommRing O] [Algebra O C]
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {κ : O} {N : ℕ}
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

/- English proof (translation)
Establish `h` using `P.alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h`. Take the linear combination `h`.
-/
theorem e_swap (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[P.free.2.2]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨⟨j, k⟩, rfl⟩` from `hy`.

Take `⟨b, hb⟩` from `(RingOfIntegers.mapRingEquiv c).surjective (RingOfIntegers.basis E k)`. Take `⟨z, hz⟩` from `h j`. Take `⟨s, hs⟩` from `hσ b`. Use `⟨s * z, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← hb, ← P.adj, LatBasic.mem_eigSp.1 hu b, map_smul, LinearMap.smul_apply, hz, ← hs, smul_eq_mul, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [map_add, ha, hb, mul_add, map_add]⟩`. Consider the case `smul a x _ hx`. Take `⟨b, hb⟩` from `hx`.

Use `⟨a * b, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C a x, map_smul, hb, smul_eq_mul, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torusExtensionPair_correction_eq_value_quotient {σ : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) {u : V}
    (hu : u ∈ eigSp P.ρ σ) (π : O) (h : ∀ j, ∃ z : O, P.e u (P.t j) = algebraMap O C (π * z)) :
    ∀ y ∈ P.T, ∃ z : O, P.e u y = algebraMap O C (π * z) := by
  intro y hy
  rw [P.free.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hy
    obtain ⟨b, hb⟩ := (RingOfIntegers.mapRingEquiv c).surjective (RingOfIntegers.basis E k)
    obtain ⟨z, hz⟩ := h j
    obtain ⟨s, hs⟩ := hσ b
    refine ⟨s * z, ?_⟩
    simp only
    rw [← hb, ← P.adj, LatBasic.mem_eigSp.1 hu b, map_smul, LinearMap.smul_apply, hz, ← hs,
      smul_eq_mul, ← map_mul]
    congr 1
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, mul_add, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    rw [← algebraMap_smul C a x, map_smul, hb, smul_eq_mul, ← map_mul]
    congr 1
    ring

end Pt

/- English proof (translation)
Introduce `C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ d π x w hd hw hx`. Establish `hσ` using `(exists_diff_generator C v O hv E σ).1`. Establish `hinj` using `hv.hom_inj`. Take `⟨-, -, -, hcomm, -, hom, hdual, -⟩` from `htPoint_basic C v O hv E c hc κ N V Ω P`. Establish `hd0` using `(different_generator_dualInt O C E σ d hinj hσ hd).1`.

Establish `hq` using `(SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d hinj hσ hd P.free).1`. Use `set s : V := ∑ l, x l • eigProj P.ρ σ (P.t l) with hs`. Establish `hsE : s ∈ eigSp P.ρ σ` using `Submodule.sum_mem _ fun l _ => by`. Rewrite using `[← algebraMap_smul C (x l)]`. Conclude with `Submodule.smul_mem _ _ (LatBasic.eigProj_mem _ _ _)`.

Use `set u : V := d • s - w with hu`. Establish `huE : u ∈ eigSp P.ρ σ`. Use `Submodule.sub_mem _ ?_ hw.2.2` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C d]`. Conclude with `Submodule.smul_mem _ _ hsE`.

Establish `hut : ∀ j, ∃ z : O, P.e u (P.t j) = algebraMap O C (π * z)` using `fun j => by`. Take `⟨z, hz⟩` from `hx j`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, map_sub, LinearMap.sub_apply, sub_eq_iff_eq_add', ← hz, hs, Finset.smul_sum, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm d (x l), ← algebraMap_smul C (x l), map_smul, LinearMap.smul_apply, smul_eq_mul]`. Establish `huT` using `torusExtensionPair_correction_eq_value_quotient P hσ huE π hut`. Choose the witnesses or unpack the hypotheses as in `⟨u', hu'T, hu'E, hu'⟩ : ∃ u' ∈ P.T, u' ∈ eigSp P.ρ σ ∧ u = π • u' := by`. Distinguish the cases in `hπ : algebraMap O C π = 0`. Use `⟨0, P.T.zero_mem, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_zero]`. Use `P.nondeg u fun y => ?_` and prove the remaining obligations. Rewrite using `[e_swap, neg_eq_zero]`. Establish `hy : y ∈ Submodule.span C (P.T : Set V)` using `by rw [P.free.2.1]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨z, hz⟩` from `huT y hy`. Rewrite using `[hz, map_mul, hπ, zero_mul]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]`.

Consider the case `smul a b _ hb => rw [map_smul, hb, smul_zero]`. Use `⟨(algebraMap O C π)⁻¹ • u, ?_, Submodule.smul_mem _ _ huE, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdual]`. Introduce `y hy`. Take `⟨z, hz⟩` from `huT y hy`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.flip_apply, map_smul, LinearMap.smul_apply, hz, map_mul, smul_eq_mul, inv_mul_cancel_left₀ hπ]`. Rewrite using `[← algebraMap_smul C π, smul_smul, mul_inv_cancel₀ hπ, one_smul]`. Establish `hy : (algebraMap O C d)⁻¹ • u' ∈ eigQuot P.ρ σ P.T`. Rewrite using `[hq, ← algebraMap_smul C d, smul_smul, mul_inv_cancel₀ hd0, one_smul]`.

Conclude with `⟨hu'T, hu'E⟩`. Use `⟨P.ht ((algebraMap O C d)⁻¹ • u'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hom]`. Conclude with `⟨_, hy, rfl⟩`. Establish `hw0 : P.ht w = 0` using `hw.1`.

Establish `h1 : P.ht s = ∑ l, x l • eigProj P.ρΩ σ (P.ht (P.t l))`. Rewrite using `[hs, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, hcomm]`. Establish `h2 : algebraMap O C d • P.ht s = algebraMap O C π • P.ht u'`.

Use `congrArg P.ht hu'` as an intermediate fact. Rewrite `this` using `[hu, map_sub, hw0, sub_zero, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]`. Rewrite using `[algebraMap_smul, algebraMap_smul, this]`. Rewrite using `[← h1, map_smul, ← algebraMap_smul C π, smul_comm, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]`.
-/
theorem pt_comp_zero : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C) (d π : O) (x : Fin N → O) (w : V), Submodule.span O {algebraMap O C d} = Submodule.span O {y : C | ∃ z ∈ differentIdeal ℤ (𝓞 E), y = σ (z : E)} → w ∈ P.W' σ → (∀ j, ∃ z : O, ∑ l, algebraMap O C (x l) * P.e (d • eigProj P.ρ σ (P.t l)) (P.t j) = P.e w (P.t j) + algebraMap O C (π * z)) → ∃ y ∈ P.omHT σ, ∑ l, x l • eigProj P.ρΩ σ (P.ht (P.t l)) = π • y := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ d π x w hd hw hx
  have hσ := (exists_diff_generator C v O hv E σ).1
  have hinj := hv.hom_inj
  obtain ⟨-, -, -, hcomm, -, hom, hdual, -⟩ := htPoint_basic C v O hv E c hc κ N V Ω P
  have hd0 := (different_generator_dualInt O C E σ d hinj hσ hd).1
  have hq := (SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d hinj hσ hd
    P.free).1
  set s : V := ∑ l, x l • eigProj P.ρ σ (P.t l) with hs
  have hsE : s ∈ eigSp P.ρ σ := Submodule.sum_mem _ fun l _ => by
    rw [← algebraMap_smul C (x l)]
    exact Submodule.smul_mem _ _ (LatBasic.eigProj_mem _ _ _)
  set u : V := d • s - w with hu
  have huE : u ∈ eigSp P.ρ σ := by
    refine Submodule.sub_mem _ ?_ hw.2.2
    rw [← algebraMap_smul C d]
    exact Submodule.smul_mem _ _ hsE
  have hut : ∀ j, ∃ z : O, P.e u (P.t j) = algebraMap O C (π * z) := fun j => by
    obtain ⟨z, hz⟩ := hx j
    refine ⟨z, ?_⟩
    rw [hu, map_sub, LinearMap.sub_apply, sub_eq_iff_eq_add', ← hz, hs, Finset.smul_sum, map_sum,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm d (x l), ← algebraMap_smul C (x l), map_smul, LinearMap.smul_apply, smul_eq_mul]
  have huT := torusExtensionPair_correction_eq_value_quotient P hσ huE π hut
  obtain ⟨u', hu'T, hu'E, hu'⟩ : ∃ u' ∈ P.T, u' ∈ eigSp P.ρ σ ∧ u = π • u' := by
    by_cases hπ : algebraMap O C π = 0
    · refine ⟨0, P.T.zero_mem, Submodule.zero_mem _, ?_⟩
      rw [smul_zero]
      refine P.nondeg u fun y => ?_
      rw [e_swap, neg_eq_zero]
      have hy : y ∈ Submodule.span C (P.T : Set V) := by rw [P.free.2.1]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨z, hz⟩ := huT y hy
        rw [hz, map_mul, hπ, zero_mul]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul a b _ hb => rw [map_smul, hb, smul_zero]
    · refine ⟨(algebraMap O C π)⁻¹ • u, ?_, Submodule.smul_mem _ _ huE, ?_⟩
      · rw [← hdual]
        intro y hy
        obtain ⟨z, hz⟩ := huT y hy
        refine ⟨z, ?_⟩
        rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, hz, map_mul, smul_eq_mul,
          inv_mul_cancel_left₀ hπ]
      · rw [← algebraMap_smul C π, smul_smul, mul_inv_cancel₀ hπ, one_smul]
  have hy : (algebraMap O C d)⁻¹ • u' ∈ eigQuot P.ρ σ P.T := by
    rw [hq, ← algebraMap_smul C d, smul_smul, mul_inv_cancel₀ hd0, one_smul]
    exact ⟨hu'T, hu'E⟩
  refine ⟨P.ht ((algebraMap O C d)⁻¹ • u'), ?_, ?_⟩
  · rw [hom]
    exact ⟨_, hy, rfl⟩
  · have hw0 : P.ht w = 0 := hw.1
    have h1 : P.ht s = ∑ l, x l • eigProj P.ρΩ σ (P.ht (P.t l)) := by
      rw [hs, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.map_smul_of_tower, hcomm]
    have h2 : algebraMap O C d • P.ht s = algebraMap O C π • P.ht u' := by
      have := congrArg P.ht hu'
      rw [hu, map_sub, hw0, sub_zero, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower] at this
      rw [algebraMap_smul, algebraMap_smul, this]
    rw [← h1, map_smul, ← algebraMap_smul C π, smul_comm, ← h2, smul_smul, inv_mul_cancel₀ hd0,
      one_smul]

end PositivityTheory.HtPt.Gd
