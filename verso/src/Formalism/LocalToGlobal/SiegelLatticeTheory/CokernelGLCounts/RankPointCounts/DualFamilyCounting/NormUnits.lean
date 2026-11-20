import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetUnitOfSelfdual
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj`. Use `haveI : 𝔭.IsPrime := h𝔭.isPrime`. Take `⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩` from `hG`. Take `⟨hbU, hbloc, hbo, hbn, ha0⟩` from `hJ`. Take `⟨Λ₀, hΛlat, hΛu⟩` from `hΛ`.

Establish `hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0` using `fun i => by`. Rewrite using `[map_ne_zero]`. Conclude with `ha0 i` after adjusting the coercions. Establish `hC0 : ∀ k, algebraMap F K (c k) ≠ 0` using `fun k => by`. Rewrite using `[map_ne_zero]`.

Conclude with `(hwn k).2`. Establish `hπ0 : π ≠ 0` using `fun e => hU0.notMem (e ▸ Submodule.zero_mem _)`. Establish `hP0 : algebraMap F K (π : F) ≠ 0`. Rewrite using `[map_ne_zero]`. Conclude with `hπ0` after adjusting the coercions.

Establish `hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭`. Use `mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))` as an intermediate fact. Simplify using `using this`. Establish `hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V`. Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]`.

Use `haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩`. Set `g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V` to `Sum.elim b w`. Establish `horth : ∀ s t, s ≠ t → h (g s) (g t) = 0`. Introduce and unpack `(i|i) (k|k) hst`. Conclude with `hbo i k (fun e => hst (congrArg Sum.inl e))`.

Conclude with `form_U_orth (hbU i) (hwU k)`. Conclude with `form_orth_U hS (hbU k) (hwU i)`. Conclude with `hwo i k (fun e => hst (congrArg Sum.inr e))`. Establish `hnorm : ∀ s, h (g s) (g s) ≠ 0`. Introduce and unpack `(i|i)`.

Use `show h (b i) (b i) ≠ 0`. Rewrite using `[hbn i]`. Conclude with `hA0 i`. Use `show h (w i) (w i) ≠ 0`. Rewrite using `[(hwn i).1]`.

Conclude with `hC0 i`. Establish `hli : LinearIndependent K g` using `linInd_orth g horth hnorm`. Set `γ` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hγ : ∀ s, γ s = g s` using `fun s => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s`. Establish `hdetγ : (gramK h γ).det = (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k)`.

Rewrite using `[gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)`. Conclude with `Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)`. Take `⟨β, -, hβ⟩` from `LocalSpans.exists_basis_locF hΛlat h𝔭`.

Set `e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))` to `Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])`. Set `β'` to `β.reindex e`. Establish `hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β)` using `by show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _`. Rewrite using `[Basis.range_reindex]`. Establish `hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β')`.

Rewrite using `[hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]`. Take `⟨hu1, hu2⟩` from `det_unit_of_selfdual hFix hS hN β' hsd`. Establish `hd : (β'.toMatrix γ).det ≠ 0` using `Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)`. Establish `hNUγ : NU 𝔭 (gramK h γ).det`. Rewrite using `[gram_det_change h β' γ]`.

Conclude with `NU.norm_mul hu1 hu2 hd`. Establish `hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F))`. Introduce `i hv`. Apply `NU.of_unit` to reduce the goal to its premises. Use `mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))` as an intermediate fact.

Rewrite `this` using `[hv]`. Simplify using `using this`. Use `unit_part hCM hFix h𝔭 hU0 (ha0 i)` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `using this`.

Establish `hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) → (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k))`. Introduce `k hk hk'`. Take `⟨h1, h2⟩` from `hfree k hk hk'`. Apply `NU.of_unit` to reduce the goal to its premises. Simplify using `using mem_SP_of_inP (K := K) hU0 h1`.

Simplify using `using mem_SP_of_inP (K := K) hU0 h2`. Establish `hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 → NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i)))`. Introduce `i hv`. Take `⟨-, hCu⟩` from `unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)`. Establish `hAu` using `unit_part hCM hFix h𝔭 hU0 (ha0 i)`.

Establish `hAd` using `mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))`. Establish `hs` using `mem_SP_of_inP (K := K) hU0 (hpair i hv)`. Rewrite `hs` using `[map_add]`. Use `set A := algebraMap F K (a i : F)`. Use `set C := algebraMap F K (c (τ i))`.

Use `set P := algebraMap F K (π : F)`. Use `set v := vF 𝔭 (a i)`. Establish `e1 : P ^ v * P⁻¹ ^ v = 1` using `by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]`. Establish `hCd : P⁻¹ ^ v * C ∈ SP K 𝔭`. Establish `e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A`.

Rewrite using `[two_mul, pow_add]`. Take the linear combination `(-(P⁻¹ ^ v * (A + C))) * e1`. Rewrite using `[e2]`. Conclude with `sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd`. Apply `NU.pair (hA0 i) (star_fix hFix _)` to reduce the goal to its premises.

Establish `e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v)`. Take the linear combination `(-(C * A⁻¹)) * e1`. Rewrite using `[e3]`. Conclude with `mul_mem hCd hAu`. Establish `e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v)`.

Take the linear combination `(-(A * C⁻¹)) * e1`. Rewrite using `[e3]`. Conclude with `mul_mem hAd hCu`. Set `T` to `Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)`. Set `S` to `T.image τ`.

Establish `hSj : S ⊆ Finset.univ.erase j`. Introduce `k hk`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.mp hk`. Use `Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩` and prove the remaining obligations. Introduce `e`.

Use `hτlt i (Finset.mem_filter.mp hi).2` as an intermediate fact. Rewrite `this` using `[e]`. Use linear arithmetic over natural numbers and integers. Establish `hinjT : Set.InjOn τ T` using `fun i hi k hk e => hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e`. Establish `hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) * ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k))`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j), ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) * ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)` using `(Finset.prod_filter_mul_prod_filter_not _ _ _).symm`. Establish `htot : (gramK h γ).det = algebraMap F K (c j) * ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) * (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k))`. Rewrite using `[hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) * (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k))`. Use `NU.mul (NU.mul ?_ ?_) ?_` and prove the remaining obligations. Conclude with `NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2`. Conclude with `NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)`.

Use `NU.prod _ _ fun k hk => ?_` and prove the remaining obligations. Take `⟨hk1, hk2⟩` from `Finset.mem_sdiff.mp hk`. Establish `hkj : k ≠ j` using `(Finset.mem_erase.mp hk1).1`. Apply `hunitC k` to reduce the goal to its premises. Establish `h1` using `k.isLt`.

Establish `h2` using `Fin.val_ne_of_ne hkj`. Use linear arithmetic over natural numbers and integers. Introduce `i hi e`. Conclude with `hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)`. Establish `hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) * (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0`.

Apply the tactic sequence `refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_`. Conclude with `mul_ne_zero (hA0 i) (hC0 _)`. Conclude with `hA0 i`. Conclude with `hC0 i`. Rewrite `hNUγ` using `[htot]`.

Conclude with `NU.of_mul_left hNUγ hX hX0`.
-/
theorem last_unit_holds : LastUnit := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩ := hG
  obtain ⟨hbU, hbloc, hbo, hbn, ha0⟩ := hJ
  obtain ⟨Λ₀, hΛlat, hΛu⟩ := hΛ
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast ha0 i
  have hC0 : ∀ k, algebraMap F K (c k) ≠ 0 := fun k => by
    rw [map_ne_zero]
    exact (hwn k).2
  have hπ0 : π ≠ 0 := fun e => hU0.notMem (e ▸ Submodule.zero_mem _)
  have hP0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))
    simpa using this
  have hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]
  haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩
  let g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V := Sum.elim b w
  have horth : ∀ s t, s ≠ t → h (g s) (g t) = 0 := by
    rintro (i|i) (k|k) hst
    · exact hbo i k (fun e => hst (congrArg Sum.inl e))
    · exact form_U_orth (hbU i) (hwU k)
    · exact form_orth_U hS (hbU k) (hwU i)
    · exact hwo i k (fun e => hst (congrArg Sum.inr e))
  have hnorm : ∀ s, h (g s) (g s) ≠ 0 := by
    rintro (i|i)
    · show h (b i) (b i) ≠ 0
      rw [hbn i]
      exact hA0 i
    · show h (w i) (w i) ≠ 0
      rw [(hwn i).1]
      exact hC0 i
  have hli : LinearIndependent K g := linInd_orth g horth hnorm
  let γ := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hγ : ∀ s, γ s = g s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s
  have hdetγ : (gramK h γ).det =
      (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k) := by
    rw [gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)
    · exact Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)
  obtain ⟨β, -, hβ⟩ := LocalSpans.exists_basis_locF hΛlat h𝔭
  let e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let β' := β.reindex e
  have hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β) := by
    show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _
    rw [Basis.range_reindex]
  have hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β') := by
    rw [hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]
  obtain ⟨hu1, hu2⟩ := det_unit_of_selfdual hFix hS hN β' hsd
  have hd : (β'.toMatrix γ).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)
  have hNUγ : NU 𝔭 (gramK h γ).det := by
    rw [gram_det_change h β' γ]
    exact NU.norm_mul hu1 hu2 hd
  have hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F)) := by
    intro i hv
    apply NU.of_unit
    · have := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
      rw [hv] at this
      simpa using this
    · have := unit_part hCM hFix h𝔭 hU0 (ha0 i)
      rw [hv] at this
      simpa using this
  have hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) →
      (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k)) := by
    intro k hk hk'
    obtain ⟨h1, h2⟩ := hfree k hk hk'
    apply NU.of_unit
    · simpa using mem_SP_of_inP (K := K) hU0 h1
    · simpa using mem_SP_of_inP (K := K) hU0 h2
  have hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 →
      NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i))) := by
    intro i hv
    obtain ⟨-, hCu⟩ := unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)
    have hAu := unit_part hCM hFix h𝔭 hU0 (ha0 i)
    have hAd := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
    have hs := mem_SP_of_inP (K := K) hU0 (hpair i hv)
    rw [map_add] at hs
    set A := algebraMap F K (a i : F)
    set C := algebraMap F K (c (τ i))
    set P := algebraMap F K (π : F)
    set v := vF 𝔭 (a i)
    have e1 : P ^ v * P⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]
    have hCd : P⁻¹ ^ v * C ∈ SP K 𝔭 := by
      have e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A := by
        rw [two_mul, pow_add]
        linear_combination (-(P⁻¹ ^ v * (A + C))) * e1
      rw [e2]
      exact sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd
    apply NU.pair (hA0 i) (star_fix hFix _)
    · have e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v) := by
        linear_combination (-(C * A⁻¹)) * e1
      rw [e3]
      exact mul_mem hCd hAu
    · have e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v) := by
        linear_combination (-(A * C⁻¹)) * e1
      rw [e3]
      exact mul_mem hAd hCu
  let T := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)
  let S := T.image τ
  have hSj : S ⊆ Finset.univ.erase j := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro e
    have := hτlt i (Finset.mem_filter.mp hi).2
    rw [e] at this
    omega
  have hinjT : Set.InjOn τ T := fun i hi k hk e =>
    hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e
  have hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j),
      ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]
    ring
  have hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have htot : (gramK h γ).det = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]
    ring
  have hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    refine NU.mul (NU.mul ?_ ?_) ?_
    · exact NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2
    · exact NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)
    · refine NU.prod _ _ fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk1).1
      apply hunitC k
      · have h1 := k.isLt
        have h2 := Fin.val_ne_of_ne hkj
        omega
      · intro i hi e
        exact hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)
  have hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    · exact mul_ne_zero (hA0 i) (hC0 _)
    · exact hA0 i
    · exact hC0 i
  rw [htot] at hNUγ
  exact NU.of_mul_left hNUγ hX hX0

end Formalism.L2.SG.Pf.Cnt
