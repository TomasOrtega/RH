import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.FinUniq

/- English proof (translation)
Use `set 𝓑 := TopologicalSpace.countableBasis X`. Establish `hB` using `TopologicalSpace.isBasis_countableBasis X`. Use `haveI : Countable 𝓑 := (TopologicalSpace.countable_countableBasis X).to_subtype`. Use `set S : Set (X → ℂ) := Set.range fun s : Finset 𝓑 => Set.indicator (⋃ b ∈ s, (b : Set X)) (1 : X → ℂ)`. Establish `hS : S.Countable` using `Set.countable_range _`.

Establish `hco : ∀ U : Set X, IsOpen U → IsCompact U → Set.indicator U (1 : X → ℂ) ∈ S`. Introduce `U hU hK`. Establish `hcov : U ⊆ ⋃ i : {b : 𝓑 // (b : Set X) ⊆ U}, (i.1 : Set X)`. Introduce `x hx`. Take `⟨b, hb, hxb, hbU⟩` from `hB.exists_subset_of_mem_open hx hU`.

Conclude with `Set.mem_iUnion.2 ⟨⟨⟨b, hb⟩, hbU⟩, hxb⟩`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun i : {b : 𝓑 // (b : Set X) ⊆ U} => (i.1 : Set X)) (fun i => hB.isOpen i.1.2) hcov`. Use `⟨t.image Subtype.val, ?_⟩` and prove the remaining obligations. Use `show Set.indicator _ 1 = _`. Use `congr 1`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Set.mem_iUnion, Finset.mem_image] at hx`. Take `⟨b, ⟨i, -, rfl⟩, hxb⟩` from `hx`. Conclude with `i.2 hxb`.

Introduce `x hx`. Use `ht hx` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this ⊢`. Take `⟨i, hi, hxi⟩` from `this`. Conclude with `⟨i.1, Finset.mem_image_of_mem _ hi, hxi⟩`.

Establish `hle : SB X ≤ Submodule.span ℂ S`. Introduce `f hf`. Take `⟨hlc, hcs⟩` from `hf`. Establish `hK : IsCompact (tsupport f)` using `hcs`. Use `haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK`.

Establish `hfin0 : (Set.range fun x : tsupport f => f x).Finite` using `(hlc.comp_continuous continuous_subtype_val).range_finite`. Establish `hfin : (Set.range f).Finite`. Use `(hfin0.insert 0).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Distinguish the cases in `hx : f x = 0`.

Conclude with `Or.inl hx`. Conclude with `Or.inr ⟨⟨x, subset_tsupport _ hx⟩, rfl⟩`. Establish `heq : f = ∑ c ∈ hfin.toFinset.filter (· ≠ 0), c • Set.indicator (f ⁻¹' {c}) (1 : X → ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`.

Distinguish the cases in `hx : f x = 0`. Rewrite using `[hx]`. Use `(Finset.sum_eq_zero fun c hc => ?_).symm` and prove the remaining obligations. Establish `hc0 : c ≠ 0` using `(Finset.mem_filter.1 hc).2`. Simplify using `[Set.indicator, hx, Ne.symm hc0]`.

Rewrite using `[Finset.sum_eq_single (f x)]`. Simplify using `[Set.indicator]`. Introduce `c _ hcx`. Simplify using `[Set.indicator, Ne.symm hcx]`. Introduce `h`.

Conclude with `absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, hx⟩) h`. Rewrite using `[heq]`. Use `Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span (hco _ ?_ ?_))` and prove the remaining obligations. Conclude with `hlc.isOpen_fiber c`. Establish `hc0 : c ≠ 0` using `(Finset.mem_filter.1 hc).2`.

Use `hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `subset_tsupport _ (by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [Function.mem_support, hx]; exact hc0)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (SB X) ≤ Cardinal.aleph0 := by
  classical
  set 𝓑 := TopologicalSpace.countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  haveI : Countable 𝓑 := (TopologicalSpace.countable_countableBasis X).to_subtype
  set S : Set (X → ℂ) := Set.range fun s : Finset 𝓑 => Set.indicator (⋃ b ∈ s, (b : Set X)) (1 : X → ℂ)
  have hS : S.Countable := Set.countable_range _

  have hco : ∀ U : Set X, IsOpen U → IsCompact U → Set.indicator U (1 : X → ℂ) ∈ S := by
    intro U hU hK
    have hcov : U ⊆ ⋃ i : {b : 𝓑 // (b : Set X) ⊆ U}, (i.1 : Set X) := by
      intro x hx
      obtain ⟨b, hb, hxb, hbU⟩ := hB.exists_subset_of_mem_open hx hU
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hb⟩, hbU⟩, hxb⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : {b : 𝓑 // (b : Set X) ⊆ U} => (i.1 : Set X))
      (fun i => hB.isOpen i.1.2) hcov
    refine ⟨t.image Subtype.val, ?_⟩
    show Set.indicator _ 1 = _
    congr 1
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion, Finset.mem_image] at hx
      obtain ⟨b, ⟨i, -, rfl⟩, hxb⟩ := hx
      exact i.2 hxb
    · intro x hx
      have := ht hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨i, hi, hxi⟩ := this
      exact ⟨i.1, Finset.mem_image_of_mem _ hi, hxi⟩
  have hle : SB X ≤ Submodule.span ℂ S := by
    intro f hf
    obtain ⟨hlc, hcs⟩ := hf
    have hK : IsCompact (tsupport f) := hcs
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
      (hlc.comp_continuous continuous_subtype_val).range_finite
    have hfin : (Set.range f).Finite := by
      refine (hfin0.insert 0).subset ?_
      rintro _ ⟨x, rfl⟩
      by_cases hx : f x = 0
      · exact Or.inl hx
      · exact Or.inr ⟨⟨x, subset_tsupport _ hx⟩, rfl⟩
    have heq : f = ∑ c ∈ hfin.toFinset.filter (· ≠ 0), c • Set.indicator (f ⁻¹' {c}) (1 : X → ℂ) := by
      funext x
      rw [Finset.sum_apply]
      by_cases hx : f x = 0
      · rw [hx]
        refine (Finset.sum_eq_zero fun c hc => ?_).symm
        have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
        simp [Set.indicator, hx, Ne.symm hc0]
      · rw [Finset.sum_eq_single (f x)]
        · simp [Set.indicator]
        · intro c _ hcx
          simp [Set.indicator, Ne.symm hcx]
        · intro h
          exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, hx⟩) h
    rw [heq]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span (hco _ ?_ ?_))
    · exact hlc.isOpen_fiber c
    · have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      refine hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_
      intro x hx
      exact subset_tsupport _ (by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [Function.mem_support, hx]; exact hc0)
  calc Module.rank ℂ (SB X) ≤ Module.rank ℂ (Submodule.span ℂ S) := Submodule.rank_mono hle
    _ ≤ Cardinal.mk S := rank_span_le S
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 hS.to_subtype

/- English proof (translation)
Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: TopologicalSpace.SeparableSpace (v.adicCompletion F)` using `⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩`. Use `infer_instance`.
-/
theorem sc_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  infer_instance

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Break down `hirr _ (hker c) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)`. Establish `hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V))`. Introduce `c`. Rewrite using `[← LinearMap.range_eq_top]`.

Break down `hirr _ (hran c) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1)` using `LinearMap.mem_range_self _ _`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hv₀ (hinj c (by rw [h1, map_zero]))`.

Conclude with `h`. Establish `hrep : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p)`. Introduce `p hp`. Establish `hs` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree`. Establish `hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1`.

Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `key : ∀ m : Multiset ℂ, Function.Injective (Polynomial.aeval T (m.map fun a => Polynomial.X - Polynomial.C a).prod)`. Introduce `m`. Proceed by induction on `m using Multiset.induction_on with`.

Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]`. Conclude with `Function.injective_id`. Consider the case `cons a m ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`.

Use `Function.Injective.comp ?_ ih` and prove the remaining obligations. Rewrite using `[hlin]`. Conclude with `hinj a`. Rewrite using `[← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]`. Use `Function.Injective.comp ?_ (key _)` and prove the remaining obligations.

Rewrite using `[Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]`. Introduce `x y hxy`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply] at hxy`. Conclude with `smul_right_injective V (Polynomial.leadingCoeff_ne_zero.mpr hp) hxy`. Set `S : ℂ → V ≃ₗ[ℂ] V` to `fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩`.

Set `w : ℂ → V` to `fun c => (S c).symm v₀`. Establish `hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀` using `fun c => (S c).apply_symm_apply v₀`. Establish `hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1`. Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Establish `hli : LinearIndependent ℂ w`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`. Set `q : ℂ → Polynomial ℂ` to `fun c => ∏ d ∈ s.erase c, (Polynomial.X - Polynomial.C d)`. Establish `hq : ∀ c ∈ s, Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d)) (w c) = Polynomial.aeval T (q c) v₀`.

Introduce `c hc`. Rewrite using `[← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]`. Establish `h0 : Polynomial.aeval T (∑ c ∈ s, g c • q c) v₀ = 0`. Establish `h2` using `congrArg (Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d))) hsum`. Rewrite `h2` using `[map_zero, map_sum]`.

Rewrite using `[map_sum, LinearMap.sum_apply, ← h2]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]`. Establish `hp0 : ∑ c ∈ s, g c • q c = 0`. Assume the negation of the conclusion as `hp`.

Conclude with `hv₀ (hrep _ hp (by rw [h0, map_zero]))`. Establish `h3` using `congrArg (Polynomial.eval i) hp0`. Rewrite `h3` using `[Polynomial.eval_finset_sum, Finset.sum_eq_single i]`. Simplify using `only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Polynomial.eval_zero] at h3`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[Finset.prod_eq_zero_iff]`. Take `⟨d, hd, hd0⟩` from `h`. Conclude with `(Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm`.

Introduce `c hc hci`. Simplify using `only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]`. Introduce `h`. Conclude with `absurd hi h`.

Establish `h4` using `hli.cardinal_le_rank`. Rewrite `h4` using `[Cardinal.mk_complex]`. Conclude with `absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)`.
-/
theorem scalar_of_irred {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V → Prop)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (hirr : ∀ N, P N → N = ⊥ ∨ N = ⊤) (T : Module.End ℂ V)
    (hker : ∀ c : ℂ, P (LinearMap.ker (T - c • 1))) (hran : ∀ c : ℂ, P (LinearMap.range (T - c • 1))) :
    ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr _ (hker c) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr _ (hran c) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  have hrep : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p) := by
    intro p hp
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
    have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
      intro a; simp [Algebra.algebraMap_eq_smul_one]
    have key : ∀ m : Multiset ℂ,
        Function.Injective (Polynomial.aeval T (m.map fun a => Polynomial.X - Polynomial.C a).prod) := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
        simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
        exact Function.injective_id
      | cons a m ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
        refine Function.Injective.comp ?_ ih
        rw [hlin]; exact hinj a
    rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
    refine Function.Injective.comp ?_ (key _)
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    intro x y hxy
    simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
    exact smul_right_injective V (Polynomial.leadingCoeff_ne_zero.mpr hp) hxy
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → Polynomial ℂ := fun c => ∏ d ∈ s.erase c, (Polynomial.X - Polynomial.C d)
    have hq : ∀ c ∈ s, Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d)) (w c) =
        Polynomial.aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : Polynomial.aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (hrep _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul, Polynomial.eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

/- English proof (translation)
Use `⟨(f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans (g.quotKerEquivOfSurjective hg)), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.quotKerEquivOfSurjective_apply_mk f hf, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]`.
-/
theorem exists_equiv_of_ker_eq {M P Q : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] (f : M →ₗ[ℂ] P) (g : M →ₗ[ℂ] Q) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : LinearMap.ker f = LinearMap.ker g) : ∃ e : P ≃ₗ[ℂ] Q, ∀ x, g x = e (f x) := by
  refine ⟨(f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
    (g.quotKerEquivOfSurjective hg)), fun x => ?_⟩
  rw [← LinearMap.quotKerEquivOfSurjective_apply_mk f hf, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `r _`. Establish `e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0` using `by funext x; simp [tens]`. Rewrite using `[e, map_zero]`.
-/
theorem acts_zero_zero {κ : Type} [Fintype κ] (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evFin F v) T (0 : (κ → Fv F v) → ℂ) 0 := by
  intro r _
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 := by funext x; simp [tens]
  rw [e, map_zero]

/- English proof (translation)
Establish `haug : augAt om v ≤ SB (Fin n × Fin d → Fv F v)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩`. Conclude with `sub_mem hφ₁ hφ`. Establish `hfill : ∀ Q : Submodule ℂ _, LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v) ≤ Q → Q ≤ SB (Fin n × Fin d → Fv F v) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ ψ ∈ Q, p ψ = p φ → φ ∈ Q`.

Introduce `Q hNQ hQ φ hφ ψ hψ e`. Establish `h1 : φ - ψ ∈ Q` using `hNQ ⟨LinearMap.mem_ker.2 (by rw [map_sub, e, sub_self]), sub_mem hφ (hQ hψ)⟩`. Simplify using `using add_mem h1 hψ`. Use `⟨⟨⟨le_inf inv haug, inf_le_right, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `h hh φ hφ φ₁ hφ₁ hact`.

Conclude with `⟨stab h hh φ hφ.2 φ₁ hφ₁ hact hφ.1, hφ₁⟩`. Introduce `hN`. Take `⟨y, hy⟩` from `exists_ne (0 : P)`. Establish `hy' : y ∈ (SB (Fin n × Fin d → Fv F v)).map p` using `by rw [onto]; trivial`. Take `⟨x, hx, rfl⟩` from `hy'`.

Establish `: x ∈ LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v)` using `by rw [hN]; exact hx`. Conclude with `hy this.1`. Introduce and unpack `Q ⟨⟨-, hQ, hQs⟩, hQne⟩ hNQ`. Break down `irred (Q.map p) (fun h hh φ hφ φ₁ hφ₁ hact hmem => by` into its components or cases. Take `⟨ψ, hψ, e⟩` from `hmem`.

Conclude with `⟨φ₁, hQs h hh φ (hfill Q hNQ hQ φ hφ ψ hψ e) φ₁ hφ₁ hact, rfl⟩) with h0 | h1`. Introduce `x hx`. Use `⟨?_, hQ hx⟩` and prove the remaining obligations. Establish `: p x ∈ Q.map p` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h0, Submodule.mem_bot]`.

Conclude with `this`. It suffices to derive a contradiction. Use `hQne (le_antisymm hQ fun φ hφ => ?_)` and prove the remaining obligations. Establish `: p φ ∈ Q.map p` using `by rw [h1]; trivial`. Take `⟨ψ, hψ, e⟩` from `this`.

Conclude with `hfill Q hNQ hQ φ hφ ψ hψ e`.
-/
theorem ker_maximal {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (om : Rep σ Y Z) (v : Pl F) {P : Type} [AddCommGroup P]
    [Module ℂ P] [Nontrivial P] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (onto : (SB (Fin n × Fin d → Fv F v)).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (stab : ∀ h ∈ UAt σ Z (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → p φ = 0 → p φ₁ = 0)
    (irred : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ Z (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → p φ ∈ N → p φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) :
    Maximal (fun N => GlobalTheory.Published.ThetaSub om v N ∧ N ≠ SB (Fin n × Fin d → Fv F v))
      (LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v)) := by
  have haug : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ

  have hfill : ∀ Q : Submodule ℂ _, LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v) ≤ Q →
      Q ≤ SB (Fin n × Fin d → Fv F v) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ ψ ∈ Q, p ψ = p φ → φ ∈ Q := by
    intro Q hNQ hQ φ hφ ψ hψ e
    have h1 : φ - ψ ∈ Q := hNQ ⟨LinearMap.mem_ker.2 (by rw [map_sub, e, sub_self]), sub_mem hφ (hQ hψ)⟩
    simpa using add_mem h1 hψ
  refine ⟨⟨⟨le_inf inv haug, inf_le_right, ?_⟩, ?_⟩, ?_⟩
  · intro h hh φ hφ φ₁ hφ₁ hact
    exact ⟨stab h hh φ hφ.2 φ₁ hφ₁ hact hφ.1, hφ₁⟩
  · intro hN
    obtain ⟨y, hy⟩ := exists_ne (0 : P)
    have hy' : y ∈ (SB (Fin n × Fin d → Fv F v)).map p := by rw [onto]; trivial
    obtain ⟨x, hx, rfl⟩ := hy'
    have : x ∈ LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v) := by rw [hN]; exact hx
    exact hy this.1
  · rintro Q ⟨⟨-, hQ, hQs⟩, hQne⟩ hNQ
    rcases irred (Q.map p) (fun h hh φ hφ φ₁ hφ₁ hact hmem => by
      obtain ⟨ψ, hψ, e⟩ := hmem
      exact ⟨φ₁, hQs h hh φ (hfill Q hNQ hQ φ hφ ψ hψ e) φ₁ hφ₁ hact, rfl⟩) with h0 | h1
    · intro x hx
      refine ⟨?_, hQ hx⟩
      have : p x ∈ Q.map p := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact this
    · exfalso
      refine hQne (le_antisymm hQ fun φ hφ => ?_)
      have : p φ ∈ Q.map p := by rw [h1]; trivial
      obtain ⟨ψ, hψ, e⟩ := this
      exact hfill Q hNQ hQ φ hφ ψ hψ e

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`.
-/
theorem det_ne_zero_herm {B : Base F E} {n : ℕ} {Y : Spc F E n} {r s : ℕ} (h : Y.IsHerm σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)` to reduce the goal to its premises. Rewrite using `[Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]`.
-/
theorem det_ne_zero_skew {B : Base F E} {n : ℕ} {Y : Spc F E n} {r s : ℕ} (h : Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

/- English proof (translation)
Establish `sp : Function.Surjective (p.comp (SB κ).subtype)` using `fun y => by`. Establish `: y ∈ (SB κ).map p` using `by rw [hp]; trivial`. Take `⟨x, hx, rfl⟩` from `this`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `sq : Function.Surjective (q.comp (SB κ).subtype)` using `fun y => by`.

Establish `: y ∈ (SB κ).map q` using `by rw [hq]; trivial`. Take `⟨x, hx, rfl⟩` from `this`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hk : LinearMap.ker (p.comp (SB κ).subtype) = LinearMap.ker (q.comp (SB κ).subtype)`. Use extensionality with `x`.

Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `: (x : κ → ℂ) ∈ LinearMap.ker p ⊓ SB κ` using `⟨e, x.2⟩`. Rewrite `this` using `[h]`.

Conclude with `this.1`. Introduce `e`. Establish `: (x : κ → ℂ) ∈ LinearMap.ker q ⊓ SB κ` using `⟨e, x.2⟩`. Rewrite `this` using `[← h]`. Conclude with `this.1`.

Take `⟨e, he⟩` from `exists_equiv_of_ker_eq _ _ sp sq hk`. Conclude with `⟨e, fun φ hφ => he ⟨φ, hφ⟩⟩`.
-/
theorem equiv_of_ker_eq' {κ : Type} [TopologicalSpace κ] {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] (p : (κ → ℂ) →ₗ[ℂ] P) (q : (κ → ℂ) →ₗ[ℂ] Q) (hp : (SB κ).map p = ⊤) (hq : (SB κ).map q = ⊤)
    (h : LinearMap.ker p ⊓ SB κ = LinearMap.ker q ⊓ SB κ) : ∃ e : P ≃ₗ[ℂ] Q, ∀ φ ∈ SB κ, q φ = e (p φ) := by
  have sp : Function.Surjective (p.comp (SB κ).subtype) := fun y => by
    have : y ∈ (SB κ).map p := by rw [hp]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have sq : Function.Surjective (q.comp (SB κ).subtype) := fun y => by
    have : y ∈ (SB κ).map q := by rw [hq]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : LinearMap.ker (p.comp (SB κ).subtype) = LinearMap.ker (q.comp (SB κ).subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype]
    constructor
    · intro e
      have : (x : κ → ℂ) ∈ LinearMap.ker p ⊓ SB κ := ⟨e, x.2⟩
      rw [h] at this
      exact this.1
    · intro e
      have : (x : κ → ℂ) ∈ LinearMap.ker q ⊓ SB κ := ⟨e, x.2⟩
      rw [← h] at this
      exact this.1
  obtain ⟨e, he⟩ := exists_equiv_of_ker_eq _ _ sp sq hk
  exact ⟨e, fun φ hφ => he ⟨φ, hφ⟩⟩

end Ker

section Main

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v`. Establish `hT` using `hM.triple`. Establish `hf` using `hM.fin`. Establish `hP` using `GlobalTheory.ThK.Inhab.pairV hT`. Establish `hP'` using `GlobalTheory.ThK.Inhab.pairV' hT`.

Establish `hAE` using `GlobalTheory.ThK.LocalOps.actsEx hK.base`. Establish `h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v)` using `fun u _ => by show u • ((1 : UA σ G.V.J).1.1 - 1) = 0`. Rewrite using `[show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]`. Establish `h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)` using `fun u _ => by show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0`. Rewrite using `[show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]`.

Establish `exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ`. Conclude with `⟨φ₁, h1, h2⟩`. Establish `exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ`.

Conclude with `⟨φ₁, h1, h2⟩`. Establish `props : ∀ Q : FinMaps F a a', (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ → (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') …`. Introduce `Q onto' eqv irr`. Use `⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩` and prove the remaining obligations. Rewrite using `[eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]`.

Rewrite using `[← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]`. Introduce `h hh φ hφ φ₁ hφ₁ hact hmem`. Choose the witnesses or unpack the hypotheses as in `⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by`. Establish `: Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v)` using `by rw [onto']; trivial`. Conclude with `this`.

Take `⟨φ₁', hφ₁', hact'⟩` from `exV' h hh φ' hφ'`. Rewrite using `[eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]`. Conclude with `hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)`. Take `⟨sV, sV', iV'⟩` from `props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)`. Take `⟨tV, tV', jV'⟩` from `props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)`.

Use `haveI := hf.nontriv v`. Use `haveI := h₃.nontriv v`. Establish `mV` using `ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)`. Establish `mV₃` using `ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)`. Establish `mV'` using `ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'`.

Establish `mV₃'` using `ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'`. Establish `howe` using `GlobalTheory.T.weil_representation_cm_extension hK.base hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm`. Establish `eV` using `howe a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std hP.herm.herm (det_ne_zero_herm hP.herm) hP.skew.skew (det_ne_zero_skew hP.skew) hP.resX hP.resW hP.hX hP.hW hP.weil v _ _ mV mV₃`. Establish `eV'` using `howe a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std hP'.herm.herm (det_ne_zero_herm hP'.herm) hP'.skew.skew (det_ne_zero_skew hP'.skew) hP'.resX hP'.resW hP'.hX hP'.hW hP'.weil v _ _ mV' mV₃'`. Take `⟨ψ, hψ⟩` from `equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV`.

Take `⟨ψ', hψ'⟩` from `equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'`. Use `set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef`. Establish `hTapp : ∀ x, T x = ψ.symm (ψ' x)` using `fun x => rfl`. Establish `comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf …`. Introduce `h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e`.

Choose the witnesses or unpack the hypotheses as in `⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by`. Establish `: Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v)` using `by rw [hf.onto' v]; trivial`. Conclude with `this`. Take `⟨χ₁', hχ₁', hc'⟩` from `exV' h hh χ' hχ'`. Establish `e2 : Rf.p v χ₁ = Rf.p' v χ₁'` using `hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm`.

Establish `e3 : Rf₃.p v φ = Rf₃.p' v χ'`. Rewrite using `[hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']`. Establish `e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁'` using `h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3`. Rewrite using `[hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]`. Establish `hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0` using `by haveI := sc_Fv v`.

Establish `sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype)` using `fun y => by`. Establish `: y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v)` using `by rw [hf.onto v]; trivial`. Take `⟨x, hx, rfl⟩` from `this`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Conclude with `(LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)`.

Establish `hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) → Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1)`. Introduce `c h hh φ hφ φ₁ hφ₁ hact hmem`. Rewrite `hmem`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢`. Establish `hsc` using `GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0`.

Rewrite `hsc` using `[zero_smul, zero_smul, add_zero, add_zero]`. Establish `e : Rf.p v (c • φ) = T (Rf.p v φ)` using `by rw [map_smul, hmem]`. Use `comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e` as an intermediate fact. Rewrite using `[← this, map_smul]`. Establish `hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) → Rf.p v φ₁ ∈ LinearMap.range (T - c • 1)`.

Introduce `c h hh φ hφ φ₁ hφ₁ hact hmem`. Take `⟨y, hy⟩` from `hmem`. Choose the witnesses or unpack the hypotheses as in `⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by`. Establish `: y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v)` using `by rw [hf.onto v]; trivial`. Conclude with `this`.

Take `⟨χ₁, hχ₁, hc⟩` from `exV h hh χ hχ`. Establish `hsum` using `GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c`. Rewrite `hsum` using `[one_smul, one_smul]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy`. Establish `e : Rf.p v (φ + c • χ) = T (Rf.p v χ)`.

Rewrite using `[map_add, map_smul, ← hy]`. Normalize the expressions using the abelian group laws. Use `comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁) (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e` as an intermediate fact. Use `⟨Rf.p v χ₁, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Rewrite using `[← this, map_add, map_smul]`. Normalize the expressions using the abelian group laws. Take `⟨l, hl⟩` from `scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N) hrank (hf.irred v) T hker hran`. Establish `hTl : ∀ x, ψ' x = l • ψ x` using `fun x => by`. Use `congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl` as an intermediate fact.

Simplify using `only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this`. Rewrite using `[← map_smul, ← this, LinearEquiv.apply_symm_apply]`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`. Take `⟨x, hx⟩` from `exists_ne (0 : Rf.Pi v)`.

Use `hTl x` as an intermediate fact. Rewrite `this` using `[zero_smul, LinearEquiv.map_eq_zero_iff]`. Conclude with `hx this`. Use `⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩` and prove the remaining obligations. Take `⟨s1, s2⟩` from `hf.sph v hv`.

Take `⟨s3, -⟩` from `h₃.sph v hv`. Establish `hvac` using `(hT.geo.hM.vac v).1`. Establish `hvac'` using `(hT.geo.hM'.vac v).1`. Express the relevant statement in the definitionally equal form `Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3`. Establish `e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v)`.

Rewrite using `[hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]`. Establish `hne : Rf₃.p v (G.M.vac v) ≠ 0`. Rewrite using `[hψ _ hvac]`. Conclude with `(LinearEquiv.map_ne_zero_iff ψ).2 s2`. Rewrite `e1` using `[← s3]`.

Establish `: (l - 1) • Rf₃.p v (G.M.vac v) = 0` using `by rw [sub_smul, one_smul, ← e1, sub_self]`. Break down `smul_eq_zero.1 this with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hne`.
-/
theorem finMaps_unique : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := GlobalTheory.ThK.LocalOps.actsEx hK.base
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩

  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := GlobalTheory.T.weil_representation_cm_extension hK.base hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm
  have eV := howe a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std hP.herm.herm (det_ne_zero_herm hP.herm)
    hP.skew.skew (det_ne_zero_skew hP.skew) hP.resX hP.resW hP.hX hP.hW hP.weil v _ _ mV mV₃
  have eV' := howe a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std hP'.herm.herm (det_ne_zero_herm hP'.herm)
    hP'.skew.skew (det_ne_zero_skew hP'.skew) hP'.resX hP'.resW hP'.hX hP'.hW hP'.weil v _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add, map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add, map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne

end Main

end GlobalTheory.FinUniq
