import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L`. Use `haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'`. Use `set b := Module.Free.chooseBasis ℤ L`. Use `set f : Module.Free.ChooseBasisIndex ℤ L → (Fin r → K) := fun j => (b j : Fin r → K) with hf`.

Establish `hfZ : LinearIndependent ℤ f` using `b.linearIndependent.map' (L.subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)`. Establish `hfQ : LinearIndependent ℚ f` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hfZ`. Establish `hrep : ∀ v ∈ L, ∃ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, v = ∑ j, (c j : ℚ) • f j`. Introduce `v hv`. Use `⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩` and prove the remaining obligations.

Establish `h'` using `congrArg (fun z : L => (z : Fin r → K)) (b.sum_repr ⟨v, hv⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h'`. Use `conv_lhs => rw [← h']`. Conclude with `Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm`. Establish `hS : ∀ v ∈ L, v ∈ Submodule.span ℚ (Set.range f)`.

Introduce `v hv`. Take `⟨c, hc⟩` from `hrep v hv`. Rewrite using `[hc]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hKL : ∀ v ∈ L, ∀ k : K, k • v ∈ Submodule.span ℚ (Set.range f)`.

Introduce `v hv k`. Establish `halg : IsAlgebraic ℤ k` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)`. Take `⟨y, hy0, hyi⟩` from `halg.exists_integral_multiple`. Establish `hmem : ((⟨y • k, hyi⟩ : 𝓞 K)) • v ∈ L` using `L.smul_mem _ hv`. Establish `hyK : (y : K) ≠ 0` using `by exact_mod_cast hy0`.

Establish `heq : k • v = ((y : ℚ)⁻¹) • ((⟨y • k, hyi⟩ : 𝓞 K) • v)`. Rewrite using `[algebra_compatible_smul K ((y : ℚ)⁻¹), algebra_compatible_smul K (⟨y • k, hyi⟩ : 𝓞 K), smul_smul]`. Use `congr 1`. Simplify using `only [map_inv₀, map_intCast, zsmul_eq_mul]`. Use `show k = (y : K)⁻¹ * ((y : K) * k)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ _ (hS _ hmem)`. Establish `htop : ⊤ ≤ Submodule.span ℚ (Set.range f)`. Introduce `x _`.

Establish `hx : x ∈ Submodule.span K (L : Set (Fin r → K))` using `hspan ▸ Submodule.mem_top`. Establish `key : ∀ z ∈ Submodule.span K (L : Set (Fin r → K)), ∀ k : K, k • z ∈ Submodule.span ℚ (Set.range f)`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem v hv => exact hKL v hv`.

Consider the case `zero => intro k`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a c _ _ ha hc => intro k`. Rewrite using `[smul_add]`.

Conclude with `Submodule.add_mem _ (ha k) (hc k)`. Consider the case `smul c a _ ha => intro k`. Rewrite using `[smul_smul]`. Conclude with `ha (k * c)`. Simplify using `using key x hx 1`.

Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ K * r`. Rewrite using `[← Module.finrank_eq_card_basis (Module.Basis.mk hfQ htop), Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`. Set `eqv` to `Fintype.equivFinOfCardEq hcard`. Use `⟨f ∘ eqv.symm, fun j => (b (eqv.symm j)).2, hfQ.comp _ eqv.symm.injective, fun v hv => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hrep v hv`. Use `⟨c ∘ eqv.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `(Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)).symm`.
-/
theorem lattice_zbasis {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hfg : L.FG) (hspan : Submodule.span K (L : Set (Fin r → K)) = ⊤) :
    ∃ e : Fin (Module.finrank ℚ K * r) → (Fin r → K), (∀ j, e j ∈ L) ∧ LinearIndependent ℚ e ∧
      ∀ v ∈ L, ∃ n : Fin (Module.finrank ℚ K * r) → ℤ, v = ∑ j, (n j : ℚ) • e j := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ L
  set f : Module.Free.ChooseBasisIndex ℤ L → (Fin r → K) := fun j => (b j : Fin r → K) with hf
  have hfZ : LinearIndependent ℤ f :=
    b.linearIndependent.map' (L.subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfQ : LinearIndependent ℚ f := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hfZ
  have hrep : ∀ v ∈ L, ∃ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, v = ∑ j, (c j : ℚ) • f j := by
    intro v hv
    refine ⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩
    have h' := congrArg (fun z : L => (z : Fin r → K)) (b.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    conv_lhs => rw [← h']
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hS : ∀ v ∈ L, v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv
    obtain ⟨c, hc⟩ := hrep v hv
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hKL : ∀ v ∈ L, ∀ k : K, k • v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv k
    have halg : IsAlgebraic ℤ k :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    have hmem : ((⟨y • k, hyi⟩ : 𝓞 K)) • v ∈ L := L.smul_mem _ hv
    have hyK : (y : K) ≠ 0 := by exact_mod_cast hy0
    have heq : k • v = ((y : ℚ)⁻¹) • ((⟨y • k, hyi⟩ : 𝓞 K) • v) := by
      rw [algebra_compatible_smul K ((y : ℚ)⁻¹), algebra_compatible_smul K (⟨y • k, hyi⟩ : 𝓞 K), smul_smul]
      congr 1
      simp only [map_inv₀, map_intCast, zsmul_eq_mul]
      show k = (y : K)⁻¹ * ((y : K) * k)
      field_simp
    rw [heq]
    exact Submodule.smul_mem _ _ (hS _ hmem)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range f) := by
    intro x _
    have hx : x ∈ Submodule.span K (L : Set (Fin r → K)) := hspan ▸ Submodule.mem_top
    have key : ∀ z ∈ Submodule.span K (L : Set (Fin r → K)), ∀ k : K, k • z ∈ Submodule.span ℚ (Set.range f) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem v hv => exact hKL v hv
      | zero => intro k; rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => intro k; rw [smul_add]; exact Submodule.add_mem _ (ha k) (hc k)
      | smul c a _ ha => intro k; rw [smul_smul]; exact ha (k * c)
    simpa using key x hx 1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ K * r := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hfQ htop), Module.finrank_pi_fintype]
    simp [mul_comm]
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, fun j => (b (eqv.symm j)).2, hfQ.comp _ eqv.symm.injective, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hrep v hv
  refine ⟨c ∘ eqv.symm, ?_⟩
  rw [hc]
  exact (Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)).symm

end Formalism.L2.Pj.FundamentalDomainD5
