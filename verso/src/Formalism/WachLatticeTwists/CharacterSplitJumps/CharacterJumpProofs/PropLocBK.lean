import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.HodgeTateChains.CorrectedHypothesisWConsequences
import Formalism.WachLatticeTwists.LatticeDualFibres.PropLocContOfLattices

open Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Introduce `O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h2 h3 h4`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Rewrite using `[mem_annih]`.

Introduce `t ht`. Rewrite using `[h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]`. Introduce `hx`. Rewrite `hx` using `[mem_annih]`. Set `ψ : HT' →ₗ[O] HV' ⧸ HfV'` to `(HfV'.mkQ.restrictScalars O) ∘ₗ j'`.

Establish `hle : LinearMap.ker ψ ≤ LinearMap.ker (pr x)`. Introduce `t ht`. Rewrite `ht`, the goal using `[LinearMap.mem_ker]`. Apply `hx t` to reduce the goal to its premises. Use `show j' t ∈ HfV'`.

Conclude with `(Submodule.Quotient.mk_eq_zero HfV' (x := j' t)).1 ht`. Set `φ0` to `(LinearMap.ker ψ).liftQ (pr x) hle`. Set `e` to `ψ.quotKerEquivRange`. Set `φbar : LinearMap.range ψ →ₗ[O] KO O` to `φ0 ∘ₗ e.symm.toLinearMap`. Establish `hφ : ∀ t, φbar ⟨ψ t, LinearMap.mem_range_self ψ t⟩ = pr x t`.

Introduce `t`. Use `show φ0 (e.symm ⟨ψ t, LinearMap.mem_range_self ψ t⟩) = pr x t`. Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image]`. Apply the tactic sequence `try rfl`. Use `haveI hnz : NoZeroSMulDivisors O (HV' ⧸ HfV') := by`.

Use `⟨fun {c v} hcv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : c = 0`. Conclude with `Or.inl hc`. Use `right`. Establish `hc' : algebraMap O (FractionRing O) c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hc`.

Establish `h' : algebraMap O (FractionRing O) c • v = 0`. Rewrite using `[algebraMap_smul]`. Conclude with `hcv`. Conclude with `(smul_eq_zero.1 h').resolve_left hc'`. Use `haveI : Module.Free O (LinearMap.range ψ) := Module.free_of_finite_type_torsion_free'`.

Set `b` to `Module.Free.chooseBasis O (LinearMap.range ψ)`. Establish `hcex : ∀ i, ∃ y : FractionRing O, Formalism.RepresentationBoundsCohomology.LOC.toKO O y = φbar (b i)` using `fun i => Submodule.mkQ_surjective _ _`. Use `choose c hc using hcex`. Establish `hli0 : LinearIndependent O (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV'))` using `b.linearIndependent.map' (LinearMap.range ψ).subtype (Submodule.ker_subtype _)`. Establish `hli : LinearIndependent (FractionRing O) (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV'))` using `by first`.

Consider the case `exact (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hli0`. Consider the case `exact (LinearIndependent.iff_fractionRing (R := O) (K := FractionRing O)).1 hli0`. Choose the witnesses or unpack the hypotheses as in `⟨G, hG⟩ : ∃ G : (HV' ⧸ HfV') →ₗ[FractionRing O] FractionRing O, ∀ i, G ((b i : LinearMap.range ψ) : HV' ⧸ HfV') = c i := by`. Take `⟨G, hG⟩` from `LinearMap.exists_extend ((Finsupp.linearCombination (FractionRing O) c) ∘ₗ hli.repr)`. Use `⟨G, fun i => ?_⟩` and prove the remaining obligations.

Establish `h` using `LinearMap.congr_fun hG ⟨_, Submodule.subset_span ⟨i, rfl⟩⟩`. Rewrite `h` using `[LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single i _ rfl, Finsupp.linearCombination_single, one_smul]`. Conclude with `h`. Take `⟨a, ha⟩` from `h2 (G ∘ₗ HfV'.mkQ)`. Establish `haV : a ∈ HfV` using `(h1 a).2 fun bb hbb => by`.

Rewrite using `[ha, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero HfV').2 hbb, map_zero]`. Establish `key : (Formalism.RepresentationBoundsCohomology.LOC.toKO O) ∘ₗ (G.restrictScalars O) ∘ₗ (LinearMap.range ψ).subtype = φbar` using `b.ext fun i => by show Formalism.RepresentationBoundsCohomology.LOC.toKO O (G ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) = φbar (b i)`. Rewrite using `[hG i, hc i]`. Establish `hpr : ∀ t, pr (q a) t = pr x t`. Introduce `t`.

Rewrite using `[h3, ha, ← hφ t]`. Conclude with `LinearMap.congr_fun key ⟨ψ t, LinearMap.mem_range_self ψ t⟩`. Use `⟨a, haV, ?_⟩` and prove the remaining obligations. Establish `hz` using `h4 (q a - x) (fun t => by rw [map_sub, LinearMap.sub_apply, hpr t, sub_self])`. Conclude with `sub_eq_zero.1 hz`.
-/
theorem bkbConv : StatBKbConv := by
  intro O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h2 h3 h4
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_annih]
    intro t ht
    rw [h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]
  · intro hx
    rw [mem_annih] at hx
    let ψ : HT' →ₗ[O] HV' ⧸ HfV' := (HfV'.mkQ.restrictScalars O) ∘ₗ j'
    have hle : LinearMap.ker ψ ≤ LinearMap.ker (pr x) := by
      intro t ht
      rw [LinearMap.mem_ker] at ht ⊢
      apply hx t
      show j' t ∈ HfV'
      exact (Submodule.Quotient.mk_eq_zero HfV' (x := j' t)).1 ht
    let φ0 := (LinearMap.ker ψ).liftQ (pr x) hle
    let e := ψ.quotKerEquivRange
    let φbar : LinearMap.range ψ →ₗ[O] KO O := φ0 ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φbar ⟨ψ t, LinearMap.mem_range_self ψ t⟩ = pr x t := by
      intro t
      show φ0 (e.symm ⟨ψ t, LinearMap.mem_range_self ψ t⟩) = pr x t
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      try rfl
    haveI hnz : NoZeroSMulDivisors O (HV' ⧸ HfV') := by
      refine ⟨fun {c v} hcv => ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hc' : algebraMap O (FractionRing O) c ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hc
        have h' : algebraMap O (FractionRing O) c • v = 0 := by
          rw [algebraMap_smul]
          exact hcv
        exact (smul_eq_zero.1 h').resolve_left hc'
    haveI : Module.Free O (LinearMap.range ψ) := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O (LinearMap.range ψ)
    have hcex : ∀ i, ∃ y : FractionRing O, Formalism.RepresentationBoundsCohomology.LOC.toKO O y = φbar (b i) :=
      fun i => Submodule.mkQ_surjective _ _
    choose c hc using hcex
    have hli0 : LinearIndependent O (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) :=
      b.linearIndependent.map' (LinearMap.range ψ).subtype (Submodule.ker_subtype _)
    have hli : LinearIndependent (FractionRing O)
        (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) := by
      first
      | exact (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hli0
      | exact (LinearIndependent.iff_fractionRing (R := O) (K := FractionRing O)).1 hli0
    obtain ⟨G, hG⟩ : ∃ G : (HV' ⧸ HfV') →ₗ[FractionRing O] FractionRing O,
        ∀ i, G ((b i : LinearMap.range ψ) : HV' ⧸ HfV') = c i := by
      obtain ⟨G, hG⟩ :=
        LinearMap.exists_extend ((Finsupp.linearCombination (FractionRing O) c) ∘ₗ hli.repr)
      refine ⟨G, fun i => ?_⟩
      have h := LinearMap.congr_fun hG ⟨_, Submodule.subset_span ⟨i, rfl⟩⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single i _ rfl,
        Finsupp.linearCombination_single, one_smul] at h
      exact h
    obtain ⟨a, ha⟩ := h2 (G ∘ₗ HfV'.mkQ)
    have haV : a ∈ HfV := (h1 a).2 fun bb hbb => by
      rw [ha, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero HfV').2 hbb, map_zero]
    have key : (Formalism.RepresentationBoundsCohomology.LOC.toKO O) ∘ₗ (G.restrictScalars O) ∘ₗ (LinearMap.range ψ).subtype = φbar :=
      b.ext fun i => by
        show Formalism.RepresentationBoundsCohomology.LOC.toKO O (G ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) = φbar (b i)
        rw [hG i, hc i]
    have hpr : ∀ t, pr (q a) t = pr x t := by
      intro t
      rw [h3, ha, ← hφ t]
      exact LinearMap.congr_fun key ⟨ψ t, LinearMap.mem_range_self ψ t⟩
    refine ⟨a, haV, ?_⟩
    have hz := h4 (q a - x) (fun t => by rw [map_sub, LinearMap.sub_apply, hpr t, sub_self])
    exact sub_eq_zero.1 hz

/- English proof (translation)
Introduce `O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h1' h2 h3 h4`. Use `⟨?_, bkbConv O A HV HT' HV' q j' pr pair HfV HfV' h1 h2 h3 h4⟩` and prove the remaining obligations. Use extensionality with `t`. Rewrite using `[mem_annih]`. Prove the components needed by the constructor for the conclusion.

Introduce `ht y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Rewrite using `[LinearMap.flip_apply, h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]`. Introduce `ht show j' t ∈ HfV'`. Rewrite using `[h1' (j' t)]`.

Introduce `a ha`. Assume the negation of the conclusion as `hne`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hmem : ((algebraMap O (FractionRing O) ϖ)⁻¹ * (pair a (j' t))⁻¹) • a ∈ HfV` using `HfV.smul_mem _ ha`. Establish `h0` using `ht _ ⟨_, hmem, rfl⟩`.

Rewrite `h0` using `[LinearMap.flip_apply, h3, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Take `⟨y, hy⟩` from `h0`. Establish `hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero`. Establish `h5 : algebraMap O (FractionRing O) (ϖ * y) = algebraMap O (FractionRing O) 1`. Rewrite using `[map_mul, hy, mul_inv_cancel₀ hϖ0, map_one]`.

Establish `h6 : ϖ * y = 1` using `IsFractionRing.injective O _ h5`. Conclude with `hϖ.not_isUnit ⟨⟨ϖ, y, h6, by rw [mul_comm]; exact h6⟩, rfl⟩`.
-/
theorem bkbBoth : StatBKbBoth := by
  intro O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h1' h2 h3 h4
  refine ⟨?_, bkbConv O A HV HT' HV' q j' pr pair HfV HfV' h1 h2 h3 h4⟩
  ext t
  rw [mem_annih]
  constructor
  · intro ht y hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [LinearMap.flip_apply, h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]
  · intro ht
    show j' t ∈ HfV'
    rw [h1' (j' t)]
    intro a ha
    by_contra hne
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hmem : ((algebraMap O (FractionRing O) ϖ)⁻¹ * (pair a (j' t))⁻¹) • a ∈ HfV :=
      HfV.smul_mem _ ha
    have h0 := ht _ ⟨_, hmem, rfl⟩
    rw [LinearMap.flip_apply, h3, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc,
      inv_mul_cancel₀ hne, mul_one, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
    obtain ⟨y, hy⟩ := h0
    have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
    have h5 : algebraMap O (FractionRing O) (ϖ * y) = algebraMap O (FractionRing O) 1 := by
      rw [map_mul, hy, mul_inv_cancel₀ hϖ0, map_one]
    have h6 : ϖ * y = 1 := IsFractionRing.injective O _ h5
    exact hϖ.not_isUnit ⟨⟨ϖ, y, h6, by rw [mul_comm]; exact h6⟩, rfl⟩

/- English proof (translation)
Introduce `O _ _ _ X _ _ Hc HV Cs HV' _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' F Fs h1 h2 h3 h4 hF hFs`. Rewrite using `[hF, hFs, bkbConv O Hc HV Cs HV' q j' pr pair HfV HfV' h1 h2 h3 h4]`.
-/
theorem rowBK : StatRowBK := by
  intro O _ _ _ X _ _ Hc HV Cs HV' _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' F Fs h1 h2 h3 h4 hF hFs
  rw [hF, hFs, bkbConv O Hc HV Cs HV' q j' pr pair HfV HfV' h1 h2 h3 h4]

/- English proof (translation)
Introduce `O A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' ℓ e' d N δ ι₁ ι₂ P Q hA hP hC hN hδ h1 h2`. Establish `: Module.IsTorsionFree O HV'` using `Module.IsTorsionFree.trans (R := FractionRing O)`. Conclude with `LOC.propLoc O A HV HT' HV' q j' pr (HfV.restrictScalars O) (HfV'.restrictScalars O) ℓ e' d N δ ι₁ ι₂ P Q (bkbConv O A HV HT' HV' q j' pr pair HfV HfV' hA hP hC hN) hδ h1 h2`.
-/
theorem propLocBK : StatPropLocBK := by
  intro O A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' ℓ e' d N δ ι₁ ι₂ P Q hA hP
    hC hN hδ h1 h2
  have : Module.IsTorsionFree O HV' := Module.IsTorsionFree.trans (R := FractionRing O)
  exact LOC.propLoc O A HV HT' HV' q j' pr (HfV.restrictScalars O) (HfV'.restrictScalars O) ℓ e' d
    N δ ι₁ ι₂ P Q (bkbConv O A HV HT' HV' q j' pr pair HfV HfV' hA hP hC hN) hδ h1 h2

end Formalism.RepresentationBoundsCohomology.JT
