import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

set_option maxHeartbeats 1000000 in
open TensorProduct in

/- English proof (translation)
Use `haveI : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)`. Establish `hinj : Function.Injective (algebraMap B K)` using `IsFractionRing.injective B K`. Use `haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hinj`. Establish `hrk : Module.finrank B Ω[B⁄k] = d`. Rewrite using `[← hd, (KaehlerDifferential.isBaseChange_of_formallyEtale k B K).finrank_eq]`.

Establish `hfib : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) = d`. Rewrite using `[← hrk]`. Conclude with `Ideal.finrank_fiber_eq_finrank P`. Set `g : B → P.ResidueField ⊗[B] Ω[B⁄k]` to `fun v => (1 : P.ResidueField) ⊗ₜ D k B v`. Establish `hg : Submodule.span P.ResidueField (Set.range g) = ⊤`.

Rewrite using `[Submodule.eq_top_iff']`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y hx hy => exact add_mem hx hy`.

Consider the case `tmul a m`. Establish `h1 : (1 : P.ResidueField) ⊗ₜ[B] m ∈ Submodule.span P.ResidueField (Set.range g)`. Establish `hm : m ∈ Submodule.span B (Set.range (D k B))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨v, rfl⟩`. Consider the case `zero => rw [tmul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [tmul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy`. Rewrite using `[tmul_smul, ← algebraMap_smul P.ResidueField r]`.

Conclude with `Submodule.smul_mem _ _ hy`. Establish `: a ⊗ₜ[B] m = a • ((1 : P.ResidueField) ⊗ₜ[B] m)`. Rewrite using `[smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ h1`.

Take `⟨s, hs, hspan, hli⟩` from `exists_linearIndependent P.ResidueField (Set.range g)`. Set `bs : Module.Basis s P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k])` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hg])`. Use `haveI : Finite s := Module.Finite.finite_basis bs`. Use `letI : Fintype s := Fintype.ofFinite s`. Establish `hcard : Fintype.card s = d` using `by rw [← Module.finrank_eq_card_basis bs, hfib]`.

Set `bF` to `bs.reindex (Fintype.equivFinOfCardEq hcard)`. Establish `hu : ∀ j, ∃ v, g v = bF j`. Introduce `j`. Establish `: bF j ∈ s`. Rewrite using `[Module.Basis.reindex_apply, Module.Basis.mk_apply]`.

Conclude with `Subtype.prop _`. Conclude with `hs this`. Use `choose u hu using hu`. Set `N : Submodule B Ω[B⁄k]` to `Submodule.span B (Set.range fun j => D k B (u j))`. Set `φ` to `(N.mkQ).baseChange P.ResidueField`.

Establish `hφ : φ = 0`. Use `bF.ext fun j => ?_` and prove the remaining obligations. Rewrite using `[← hu j]`. Simplify using `only [φ, g, LinearMap.baseChange_tmul, LinearMap.zero_apply]`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)]`.

Conclude with `TensorProduct.tmul_zero _ _`. Establish `hsub : Subsingleton (P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N))`. Establish `h0 : ∀ x : P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N), x = 0`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => rfl`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Consider the case `tmul a q`. Take `⟨m, rfl⟩` from `N.mkQ_surjective q`. Use `LinearMap.congr_fun hφ (a ⊗ₜ m)` as an intermediate fact.

Simplify `this` using `only [φ, LinearMap.baseChange_tmul, LinearMap.zero_apply]`. Conclude with `⟨fun x y => by rw [h0 x, h0 y]⟩`. Establish `hnot : (⟨P, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (Ω[B⁄k] ⧸ N)`. Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]`. Conclude with `hsub`.

Rewrite `hnot` using `[Module.mem_support_iff_of_finite]`. Take `⟨f, hf, hfP⟩` from `Set.not_subset.1 hnot`. Establish `hfN : ∀ v : B, f • D k B v ∈ N` using `fun v => by`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]`. Conclude with `Module.mem_annihilator.1 hf _`.

Conclude with `⟨f, u, hfP, hfN⟩`.
-/
theorem exists_notMem_smul_D_mem_span (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B), f ∉ P ∧
      ∀ v : B, f • D k B v ∈ Submodule.span B (Set.range fun j => D k B (u j)) := by
  haveI : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hinj
  have hrk : Module.finrank B Ω[B⁄k] = d := by
    rw [← hd, (KaehlerDifferential.isBaseChange_of_formallyEtale k B K).finrank_eq]
  have hfib : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) = d := by
    rw [← hrk]; exact Ideal.finrank_fiber_eq_finrank P

  let g : B → P.ResidueField ⊗[B] Ω[B⁄k] := fun v => (1 : P.ResidueField) ⊗ₜ D k B v
  have hg : Submodule.span P.ResidueField (Set.range g) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a m =>
      have h1 : (1 : P.ResidueField) ⊗ₜ[B] m ∈ Submodule.span P.ResidueField (Set.range g) := by
        have hm : m ∈ Submodule.span B (Set.range (D k B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          exact Submodule.subset_span ⟨v, rfl⟩
        | zero => rw [tmul_zero]; exact zero_mem _
        | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
        | smul r y _ hy =>
          rw [tmul_smul, ← algebraMap_smul P.ResidueField r]
          exact Submodule.smul_mem _ _ hy
      have : a ⊗ₜ[B] m = a • ((1 : P.ResidueField) ⊗ₜ[B] m) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent P.ResidueField (Set.range g)
  let bs : Module.Basis s P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hg])
  haveI : Finite s := Module.Finite.finite_basis bs
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = d := by rw [← Module.finrank_eq_card_basis bs, hfib]
  let bF := bs.reindex (Fintype.equivFinOfCardEq hcard)
  have hu : ∀ j, ∃ v, g v = bF j := by
    intro j
    have : bF j ∈ s := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]; exact Subtype.prop _
    exact hs this
  choose u hu using hu

  let N : Submodule B Ω[B⁄k] := Submodule.span B (Set.range fun j => D k B (u j))
  let φ := (N.mkQ).baseChange P.ResidueField
  have hφ : φ = 0 := by
    refine bF.ext fun j => ?_
    rw [← hu j]
    simp only [φ, g, LinearMap.baseChange_tmul, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)]
    exact TensorProduct.tmul_zero _ _
  have hsub : Subsingleton (P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N)) := by
    have h0 : ∀ x : P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N), x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy => rw [hx, hy, add_zero]
      | tmul a q =>
        obtain ⟨m, rfl⟩ := N.mkQ_surjective q
        have := LinearMap.congr_fun hφ (a ⊗ₜ m)
        simpa only [φ, LinearMap.baseChange_tmul, LinearMap.zero_apply] using this
    exact ⟨fun x y => by rw [h0 x, h0 y]⟩
  have hnot : (⟨P, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (Ω[B⁄k] ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfP⟩ := Set.not_subset.1 hnot
  have hfN : ∀ v : B, f • D k B v ∈ N := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hf _
  exact ⟨f, u, hfP, hfN⟩

end GlobalTheory.PD

namespace GlobalTheory.PD

/- English proof (translation)
Take `⟨f, u, hfP, hfN⟩` from `exists_notMem_smul_D_mem_span k K B d hd P`. Establish `hinj : Function.Injective (algebraMap B K)` using `IsFractionRing.injective B K`. Establish `hf0 : (f : K) ≠ 0`. Introduce `h`. Apply `hfP` to reduce the goal to its premises.

Establish `: f = 0` using `hinj (by rw [map_zero]; exact h)`. Rewrite using `[this]`. Conclude with `P.zero_mem`. Establish `hcoef : ∀ v : B, ∃ c : Fin d → B, (f : K) • D k K (v : K) = ∑ j, (c j : K) • D k K (u j : K)`. Introduce `v`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun B).1 (hfN v)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg (KaehlerDifferential.map k k B K) hc` as an intermediate fact. Simplify using `only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, Subalgebra.smul_def] at this`. Conclude with `this.symm`.

Set `W : Submodule K Ω[K⁄k]` to `Submodule.span K (Set.range fun j => D k K (u j : K))`. Establish `hB : ∀ v : B, D k K (v : K) ∈ W`. Introduce `v`. Take `⟨c, hc⟩` from `hcoef v`. Establish `h1 : (f : K) • D k K (v : K) ∈ W`.

Rewrite using `[hc]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `Submodule.smul_mem W (f : K)⁻¹ h1` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hf0, one_smul]`. Then use the resulting hypothesis. Establish `hK : ∀ w : K, D k K w ∈ W`.

Introduce `w`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := B) w`. Establish `hy0 : algebraMap B K y ≠ 0` using `(map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hy)`. Establish `hx : D k K (algebraMap B K x) = (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y) + algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y)` using `by conv_lhs => rw [show algebraMap B K x = algebraMap B K x / algebraMap B K y * algebraMap B K y by`. Rewrite using `[div_mul_cancel₀ _ hy0]]`.

Rewrite using `[Derivation.leibniz, add_comm]`. Establish `h2 : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) ∈ W`. Establish `e : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) = D k K (algebraMap B K x) - (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y)`. Rewrite using `[hx]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `sub_mem (hB x) (Submodule.smul_mem _ _ (hB y))`. Use `Submodule.smul_mem W (algebraMap B K y)⁻¹ h2` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hy0, one_smul]`. Then use the resulting hypothesis. Establish `htop : ⊤ ≤ W`.

Rewrite using `[← KaehlerDifferential.span_range_derivation k K]`. Conclude with `Submodule.span_le.2 (Set.range_subset_iff.2 hK)`. Set `b` to `basisOfTopLeSpanOfCardEqFinrank (fun j => D k K (u j : K)) htop (by rw [Fintype.card_fin, hd])`. Establish `hb : ∀ j, b j = D k K (u j : K)` using `fun j => by`. Simplify using `only [b, coe_basisOfTopLeSpanOfCardEqFinrank]`.

Use `⟨f, u, b, hfP, hb, fun v j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hcoef v`. Use `⟨c j, ?_⟩` and prove the remaining obligations. Establish `h3 : b.repr ((f : K) • D k K (v : K)) j = (c j : K)`. Rewrite using `[hc]`.

Repeatedly rewrite using `[← hb]`. Rewrite using `[b.repr_sum_self (fun j => (c j : K))]`. Rewrite using `[← h3, map_smul, Finsupp.smul_apply, smul_eq_mul]`.
-/
theorem exists_local_dbasis (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧
      ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  obtain ⟨f, u, hfP, hfN⟩ := exists_notMem_smul_D_mem_span k K B d hd P
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hf0 : (f : K) ≠ 0 := by
    intro h
    apply hfP
    have : f = 0 := hinj (by rw [map_zero]; exact h)
    rw [this]; exact P.zero_mem
  have hcoef : ∀ v : B, ∃ c : Fin d → B,
      (f : K) • D k K (v : K) = ∑ j, (c j : K) • D k K (u j : K) := by
    intro v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 (hfN v)
    refine ⟨c, ?_⟩
    have := congrArg (KaehlerDifferential.map k k B K) hc
    simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, Subalgebra.smul_def] at this
    exact this.symm
  let W : Submodule K Ω[K⁄k] := Submodule.span K (Set.range fun j => D k K (u j : K))
  have hB : ∀ v : B, D k K (v : K) ∈ W := by
    intro v
    obtain ⟨c, hc⟩ := hcoef v
    have h1 : (f : K) • D k K (v : K) ∈ W := by
      rw [hc]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := Submodule.smul_mem W (f : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hf0, one_smul] at this
  have hK : ∀ w : K, D k K w ∈ W := by
    intro w
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) w
    have hy0 : algebraMap B K y ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hy)
    have hx : D k K (algebraMap B K x) = (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y)
        + algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) := by
      conv_lhs => rw [show algebraMap B K x = algebraMap B K x / algebraMap B K y * algebraMap B K y by
        rw [div_mul_cancel₀ _ hy0]]
      rw [Derivation.leibniz, add_comm]
    have h2 : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) ∈ W := by
      have e : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) =
          D k K (algebraMap B K x) - (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y) := by
        rw [hx]; abel
      rw [e]
      exact sub_mem (hB x) (Submodule.smul_mem _ _ (hB y))
    have := Submodule.smul_mem W (algebraMap B K y)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hy0, one_smul] at this
  have htop : ⊤ ≤ W := by
    rw [← KaehlerDifferential.span_range_derivation k K]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hK)
  let b := basisOfTopLeSpanOfCardEqFinrank (fun j => D k K (u j : K)) htop (by rw [Fintype.card_fin, hd])
  have hb : ∀ j, b j = D k K (u j : K) := fun j => by
    simp only [b, coe_basisOfTopLeSpanOfCardEqFinrank]
  refine ⟨f, u, b, hfP, hb, fun v j => ?_⟩
  obtain ⟨c, hc⟩ := hcoef v
  refine ⟨c j, ?_⟩
  have h3 : b.repr ((f : K) • D k K (v : K)) j = (c j : K) := by
    rw [hc]
    simp_rw [← hb]
    rw [b.repr_sum_self (fun j => (c j : K))]
  rw [← h3, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.PD
