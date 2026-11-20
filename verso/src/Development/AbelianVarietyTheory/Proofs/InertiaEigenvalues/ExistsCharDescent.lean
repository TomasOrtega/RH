import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.TwistChoice

/- English proof (translation)
Use `set N := Submodule.span O (Set.range x) with hN`. Establish `hex : ∃ n : ℕ, ∃ S : Finset ι, S.card = n ∧ Submodule.span O (x '' (S : Set ι)) = N`. Take `⟨T, hT⟩` from `hfg`. Establish `hc : ∀ t : T, ∃ c : ι →₀ O, (c.sum fun i a => a • x i) = (t : W)`. Introduce `t`.

Establish `ht : (t : W) ∈ N` using `by rw [← hT]; exact Submodule.subset_span t.2`. Conclude with `(Finsupp.mem_span_range_iff_exists_finsupp).mp ht`. Use `choose c hc using hc`. Use `⟨_, Finset.univ.biUnion (fun t => (c t).support), rfl, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Conclude with `Submodule.span_mono (Set.image_subset_range _ _)`.

Rewrite using `[← hT, Submodule.span_le]`. Introduce `t ht`. Rewrite using `[show t = ((c ⟨t, ht⟩).sum fun i a => a • x i) from (hc ⟨t, ht⟩).symm, Finsupp.sum]`. Use `Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `⟨i, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, hi⟩), rfl⟩`.

Take `⟨S, hSc, hS⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ S' : Finset ι, S'.card < S.card → Submodule.span O (x '' (S' : Set ι)) ≠ N`. Introduce `S' hlt heq`. Rewrite `hlt` using `[hSc]`. Conclude with `Nat.find_min hex hlt ⟨S', rfl, heq⟩`.

Use `⟨S, ?_, hS⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Take `⟨i, hi⟩` from `hne`. Take `⟨b, -, hb⟩` from `Finset.exists_min_image Finset.univ (fun a => IsDiscreteValuationRing.addVal O (g a)) ⟨i, Finset.mem_univ _⟩`. Establish `hb0 : g b ≠ 0`. Introduce `h0`. Use `hb i (Finset.mem_univ _)` as an intermediate fact.

Rewrite `this` using `[h0, (IsDiscreteValuationRing.addVal_eq_top_iff).mpr rfl, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `hi this`. Establish `hd : ∀ a, ∃ d : O, g a = g b * d` using `fun a => (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hb a (Finset.mem_univ _))`. Use `choose d hd using hd`. Establish `hsum : (∑ a, d a • x a) = 0`.

Apply `htf (g b) _ hb0` to reduce the goal to its premises. Rewrite using `[Finset.smul_sum]`. Repeatedly rewrite using `[smul_smul, ← hd]`. Conclude with `hg`. Establish `hdb : d b = 1`.

Establish `h1 : g b * 1 = g b * d b` using `by rw [mul_one, ← hd]`. Conclude with `(mul_left_cancel₀ hb0 h1).symm`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdb, one_smul]`. Establish `hxb : x b ∈ Submodule.span O (x '' ((S.erase b : Finset ι) : Set ι))`. Rewrite using `[eq_neg_of_add_eq_zero_left hsum]`.

Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ?_))` and prove the remaining obligations. Use `⟨a, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]`. Use `⟨a.2, fun h => (Finset.mem_erase.mp ha).1 (Subtype.ext h)⟩` and prove the remaining obligations. Apply `hmin (S.erase b) (Finset.card_erase_lt_of_mem b.2)` to reduce the goal to its premises.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hS]`. Conclude with `Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))`. Rewrite using `[← hS, Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Distinguish the cases in `hab : a = b`. Rewrite using `[hab]`. Conclude with `hxb`. Conclude with `Submodule.subset_span ⟨a, by simp [hab, ha], rfl⟩`.
-/
theorem exists_subbasis (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W ι : Type) [AddCommGroup W]
    [Module O W] (x : ι → W) (htf : ∀ (c : O) (w : W), c ≠ 0 → c • w = 0 → w = 0)
    (hfg : (Submodule.span O (Set.range x)).FG) :
    ∃ S : Finset ι, LinearIndependent O (fun a : S => x a) ∧
      Submodule.span O (x '' S) = Submodule.span O (Set.range x) := by
  classical
  set N := Submodule.span O (Set.range x) with hN
  have hex : ∃ n : ℕ, ∃ S : Finset ι, S.card = n ∧ Submodule.span O (x '' (S : Set ι)) = N := by
    obtain ⟨T, hT⟩ := hfg
    have hc : ∀ t : T, ∃ c : ι →₀ O, (c.sum fun i a => a • x i) = (t : W) := by
      intro t
      have ht : (t : W) ∈ N := by rw [← hT]; exact Submodule.subset_span t.2
      exact (Finsupp.mem_span_range_iff_exists_finsupp).mp ht
    choose c hc using hc
    refine ⟨_, Finset.univ.biUnion (fun t => (c t).support), rfl, le_antisymm ?_ ?_⟩
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [← hT, Submodule.span_le]
      intro t ht
      rw [show t = ((c ⟨t, ht⟩).sum fun i a => a • x i) from (hc ⟨t, ht⟩).symm, Finsupp.sum]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, hi⟩), rfl⟩
  obtain ⟨S, hSc, hS⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Finset ι, S'.card < S.card → Submodule.span O (x '' (S' : Set ι)) ≠ N := by
    intro S' hlt heq
    rw [hSc] at hlt
    exact Nat.find_min hex hlt ⟨S', rfl, heq⟩
  refine ⟨S, ?_, hS⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ (fun a => IsDiscreteValuationRing.addVal O (g a)) ⟨i, Finset.mem_univ _⟩
  have hb0 : g b ≠ 0 := by
    intro h0
    have := hb i (Finset.mem_univ _)
    rw [h0, (IsDiscreteValuationRing.addVal_eq_top_iff).mpr rfl, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at this
    exact hi this
  have hd : ∀ a, ∃ d : O, g a = g b * d := fun a =>
    (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hb a (Finset.mem_univ _))
  choose d hd using hd
  have hsum : (∑ a, d a • x a) = 0 := by
    apply htf (g b) _ hb0
    rw [Finset.smul_sum]
    simp_rw [smul_smul, ← hd]
    exact hg
  have hdb : d b = 1 := by
    have h1 : g b * 1 = g b * d b := by rw [mul_one, ← hd]
    exact (mul_left_cancel₀ hb0 h1).symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdb, one_smul] at hsum
  have hxb : x b ∈ Submodule.span O (x '' ((S.erase b : Finset ι) : Set ι)) := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    refine ⟨a, ?_, rfl⟩
    rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨a.2, fun h => (Finset.mem_erase.mp ha).1 (Subtype.ext h)⟩
  apply hmin (S.erase b) (Finset.card_erase_lt_of_mem b.2)
  apply le_antisymm
  · rw [← hS]
    exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))
  · rw [← hS, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    by_cases hab : a = b
    · rw [hab]; exact hxb
    · exact Submodule.subset_span ⟨a, by simp [hab, ha], rfl⟩

section Place

variable {L : Type} [Field L] [NumberField L] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 L, ∃ y : O, algebraMap O (FractionRing O) y = e (x : L)`. Introduce `x`. Establish `h2 : IsIntegral O (e (x : L))` using `IsIntegral.map_of_comp_eq (Int.castRingHom O) e (RingHom.ext_int _ _) (NumberField.RingOfIntegers.isIntegral_coe x)`. Conclude with `IsIntegrallyClosed.isIntegral_iff.mp h2`. Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O (FractionRing O)`.

Use `choose f hf using hint`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩` and prove the remaining obligations. Conclude with `hinj (by simp [hf])`. Introduce `a b`. Conclude with `hinj (by simp [hf])`.

Conclude with `hinj (by simp [hf])`. Introduce `a b`. Conclude with `hinj (by simp [hf])`.
-/
theorem exists_intMap (e : L →+* FractionRing O) :
    ∃ φ : 𝓞 L →+* O, ∀ x : 𝓞 L, algebraMap O (FractionRing O) (φ x) = e (x : L) := by
  have hint : ∀ x : 𝓞 L, ∃ y : O, algebraMap O (FractionRing O) y = e (x : L) := by
    intro x
    have h2 : IsIntegral O (e (x : L)) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom O) e (RingHom.ext_int _ _) (NumberField.RingOfIntegers.isIntegral_coe x)
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  choose f hf using hint
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact hinj (by simp [hf])
  · intro a b
    exact hinj (by simp [hf])
  · exact hinj (by simp [hf])
  · intro a b
    exact hinj (by simp [hf])

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_intMap e`. Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O (FractionRing O)`. Establish `hm : ∀ a : 𝓞 L, a ∈ v.asIdeal ↔ φ a ∈ IsLocalRing.maximalIdeal O`. Introduce `a`. Rewrite using `[h a]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hye⟩`. Rewrite using `[← hinj (hye.trans (hφ a).symm)]` and apply the resulting hypothesis. Introduce `ha`. Conclude with `⟨φ a, ha, hφ a⟩`.

Establish `he : ∀ a : 𝓞 L, e (algebraMap (𝓞 L) L a) = algebraMap O (FractionRing O) (φ a)` using `fun a => (hφ a).symm`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := L) v x hx`. Establish `hdv : (d : 𝓞 L) ∉ v.asIdeal` using `d.2`.

Establish `hd : IsUnit (φ d)`. Assume the negation of the conclusion as `hd`. Conclude with `hdv ((hm d).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hd)))`. Use `⟨φ n * ((hd.unit⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg e hnd`.

Rewrite `h1` using `[map_mul, he, he]`. Rewrite using `[map_mul, ← h1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]`. Introduce and unpack `⟨y, hy⟩`. Assume the negation of the conclusion as `hx`. Take `⟨n, d, hnd | hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := L) v x`.

Establish `hdv : (d : 𝓞 L) ∉ v.asIdeal` using `d.2`. Apply `hx` to reduce the goal to its premises. Establish `h1` using `congrArg (v.valuation L) hnd`. Rewrite `h1` using `[map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one]`. Rewrite using `[h1]`.

Conclude with `HeightOneSpectrum.valuation_le_one (K := L) v n`. Establish `hdv : (d : 𝓞 L) ∉ v.asIdeal` using `d.2`. Establish `hn : n ∈ v.asIdeal`. Assume the negation of the conclusion as `hn`. Apply `hx` to reduce the goal to its premises.

Establish `h1` using `congrArg (v.valuation L) hnd`. Rewrite `h1` using `[map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hn, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one]`. Conclude with `h1.le`. Establish `h2` using `congrArg e hnd`. Rewrite `h2` using `[map_mul, he, he, ← hy, ← map_mul]`.

Establish `h3` using `hinj h2`. Apply `hdv` to reduce the goal to its premises. Rewrite using `[hm, ← h3]`. Conclude with `Ideal.mul_mem_left _ y ((hm n).mp hn)`.
-/
theorem induces_of_ideal (e : L →+* FractionRing O) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ∈ v.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (x : L))
    (x : L) : v.valuation L x ≤ 1 ↔ e x ∈ (algebraMap O (FractionRing O)).range := by
  obtain ⟨φ, hφ⟩ := exists_intMap e
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hm : ∀ a : 𝓞 L, a ∈ v.asIdeal ↔ φ a ∈ IsLocalRing.maximalIdeal O := by
    intro a
    rw [h a]
    constructor
    · rintro ⟨y, hy, hye⟩
      rwa [← hinj (hye.trans (hφ a).symm)]
    · intro ha
      exact ⟨φ a, ha, hφ a⟩
  have he : ∀ a : 𝓞 L, e (algebraMap (𝓞 L) L a) = algebraMap O (FractionRing O) (φ a) := fun a => (hφ a).symm
  constructor
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := L) v x hx
    have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
    have hd : IsUnit (φ d) := by
      by_contra hd
      exact hdv ((hm d).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hd)))
    refine ⟨φ n * ((hd.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 := congrArg e hnd
    rw [map_mul, he, he] at h1
    rw [map_mul, ← h1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  · rintro ⟨y, hy⟩
    by_contra hx
    obtain ⟨n, d, hnd | hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := L) v x
    · have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
      apply hx
      have h1 := congrArg (v.valuation L) hnd
      rw [map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one] at h1
      rw [h1]
      exact HeightOneSpectrum.valuation_le_one (K := L) v n
    · have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
      have hn : n ∈ v.asIdeal := by
        by_contra hn
        apply hx
        have h1 := congrArg (v.valuation L) hnd
        rw [map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hn,
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one] at h1
        exact h1.le
      have h2 := congrArg e hnd
      rw [map_mul, he, he, ← hy, ← map_mul] at h2
      have h3 := hinj h2
      apply hdv
      rw [hm, ← h3]
      exact Ideal.mul_mem_left _ y ((hm n).mp hn)

end Place

/- English proof (translation)
Take `⟨O, Kf, _, _, _, _, _, ι, j, w, eK, hfr, hcomp, hfin, -, -, hext⟩` from `GlobalTheory.exists_complete_dvr_ext_numberField_sqrt W (FractionRing W) L₀ L i (algebraMap L₀ L) 1`. Set `_ : Algebra W O` to `j.toAlgebra`. Establish `: IsFractionRing O Kf` using `hfr`. Set `τ : Kf ≃ₐ[O] FractionRing O` to `IsLocalization.algEquiv (nonZeroDivisors O) Kf (FractionRing O)`. Establish `hτ : ∀ y : O, τ (algebraMap O Kf y) = algebraMap O (FractionRing O) y` using `fun y => τ.commutes y`.

Set `e1 : L →+* FractionRing O` to `(τ : Kf →+* FractionRing O).comp eK`. Establish `hWinj : Function.Injective (algebraMap W (FractionRing W))` using `IsFractionRing.injective W (FractionRing W)`. Establish `hOinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O (FractionRing O)`. Establish `hjinj : Function.Injective j`. Introduce `a b hab`.

Apply `hWinj` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[hcomp, hcomp, hab]`. Establish `hjfin : Module.Finite W O` using `hfin`. Establish `hjint : Algebra.IsIntegral W O` using `inferInstance`.

Establish `: FaithfulSMul W O` using `(faithfulSMul_iff_algebraMap_injective W O).mpr hjinj`. Establish `hjloc : IsLocalHom (algebraMap W O)` using `inferInstance`. Establish `hjmem : ∀ a : W, j a ∈ IsLocalRing.maximalIdeal O ↔ a ∈ IsLocalRing.maximalIdeal W`. Introduce `a`. Rewrite using `[IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]`.

Conclude with `not_congr (isUnit_map_iff (algebraMap W O) a)`. Take `⟨ψ, hψ⟩` from `exists_intMap (L := L₀) (O := W) i`. Take `⟨φ1, hφ1⟩` from `exists_intMap (L := L) (O := O) e1`. Establish `hφψ : ∀ x : 𝓞 L₀, φ1 (algebraMap (𝓞 L₀) (𝓞 L) x) = j (ψ x)`. Introduce `x`.

Apply `hOinj` to reduce the goal to its premises. Rewrite using `[hφ1]`. Establish `hc : (((algebraMap (𝓞 L₀) (𝓞 L) x : 𝓞 L) : L)) = algebraMap L₀ L (x : L₀)` using `rfl`. Use `show τ (eK _) = _`. Rewrite using `[hc, hext, ← hψ, hcomp, hτ]`.

Set `P' : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal O).comap φ1`. Establish `hP'prime : P'.IsPrime` using `Ideal.comap_isPrime _ _`. Set `p : Ideal (𝓞 L₀)` to `v.asIdeal.comap (algebraMap (𝓞 L₀) (𝓞 L))`. Establish `hover : P'.comap (algebraMap (𝓞 L₀) (𝓞 L)) = p`. Use extensionality with `x`.

Simplify using `only [Ideal.mem_comap, P', p]`. Rewrite using `[hφψ, hjmem, h x]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨ψ x, hx, hψ x⟩`.

Introduce and unpack `⟨y, hy, hyx⟩`. Rewrite using `[← hWinj (hyx.trans (hψ x).symm)]` and apply the resulting hypothesis. Establish `hv1 : v.asIdeal ∈ Ideal.primesOver p (𝓞 L)` using `⟨v.isPrime, ⟨rfl⟩⟩`. Establish `hP1 : P' ∈ Ideal.primesOver p (𝓞 L)` using `⟨hP'prime, ⟨hover.symm⟩⟩`. Take `⟨σ, hσ⟩` from `Ideal.exists_comap_galRestrict_eq (𝓞 L₀) L₀ L (𝓞 L) hP1 hv1`.

Set `e : L →+* FractionRing O` to `e1.comp (σ : L ≃ₐ[L₀] L).toRingHom`. Establish `he_int : ∀ x : 𝓞 L, e (x : L) = algebraMap O (FractionRing O) (φ1 (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x))`. Introduce `x`. Rewrite using `[hφ1]`. Use `show e1 (σ (algebraMap (𝓞 L) L x)) = e1 (algebraMap (𝓞 L) L (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x))`.

Rewrite using `[algebraMap_galRestrict_apply]`. Establish `hv' : ∀ x : 𝓞 L, x ∈ v.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (x : L)`. Introduce `x`. Rewrite using `[← hσ]`. Simplify using `only [P', Ideal.mem_comap]`.

Rewrite using `[he_int]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`.

Rewrite using `[← hOinj hyx]` and apply the resulting hypothesis. Use `⟨O, inferInstance, inferInstance, inferInstance, j.toAlgebra, e, hjinj, hjfin, hjloc, fun x => induces_of_ideal e v hv' x, ?_⟩` and prove the remaining obligations. Introduce `x y z hxyz`. Establish `hσx : σ (algebraMap L₀ L x) = algebraMap L₀ L x` using `σ.commutes x`. Establish `key : ι (i x) * algebraMap O Kf (j z) = algebraMap O Kf (j y)`.

Rewrite using `[← hcomp, ← hcomp, ← map_mul, hxyz]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, hτ]`. Use `show τ (eK (σ (algebraMap L₀ L x))) * _ = _`. Rewrite using `[hσx, hext]`.

Apply the tactic sequence `try rfl`. Use `_ = algebraMap O (FractionRing O) (algebraMap W O y) := by`. Rewrite using `[key, hτ]`. Apply the tactic sequence `try rfl`.
-/
theorem exists_coeff_ext (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (L₀ : IntermediateField ℚ L)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (i : L₀ →+* FractionRing W) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L₀, algebraMap (𝓞 L₀) (𝓞 L) x ∈ v.asIdeal ↔
      ∃ y ∈ IsLocalRing.maximalIdeal W, algebraMap W (FractionRing W) y = i (x : L₀)) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra W O)
      (e : L →+* FractionRing O), Function.Injective (algebraMap W O) ∧ Module.Finite W O ∧ IsLocalHom (algebraMap W O) ∧
      (∀ x : L, v.valuation L x ≤ 1 ↔ e x ∈ (algebraMap O (FractionRing O)).range) ∧
      ∀ (x : L₀) (y z : W), i x * algebraMap W (FractionRing W) z = algebraMap W (FractionRing W) y →
        e x * algebraMap O (FractionRing O) (algebraMap W O z) = algebraMap O (FractionRing O) (algebraMap W O y) := by
  classical
  obtain ⟨O, Kf, _, _, _, _, _, ι, j, w, eK, hfr, hcomp, hfin, -, -, hext⟩ :=
    GlobalTheory.exists_complete_dvr_ext_numberField_sqrt W (FractionRing W) L₀ L i (algebraMap L₀ L) 1
  let _ : Algebra W O := j.toAlgebra
  have : IsFractionRing O Kf := hfr
  let τ : Kf ≃ₐ[O] FractionRing O := IsLocalization.algEquiv (nonZeroDivisors O) Kf (FractionRing O)
  have hτ : ∀ y : O, τ (algebraMap O Kf y) = algebraMap O (FractionRing O) y := fun y => τ.commutes y
  let e1 : L →+* FractionRing O := (τ : Kf →+* FractionRing O).comp eK
  have hWinj : Function.Injective (algebraMap W (FractionRing W)) := IsFractionRing.injective W (FractionRing W)
  have hOinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hjinj : Function.Injective j := by
    intro a b hab
    apply hWinj
    apply ι.injective
    rw [hcomp, hcomp, hab]
  have hjfin : Module.Finite W O := hfin
  have hjint : Algebra.IsIntegral W O := inferInstance
  have : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective W O).mpr hjinj
  have hjloc : IsLocalHom (algebraMap W O) := inferInstance
  have hjmem : ∀ a : W, j a ∈ IsLocalRing.maximalIdeal O ↔ a ∈ IsLocalRing.maximalIdeal W := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (algebraMap W O) a)
  obtain ⟨ψ, hψ⟩ := exists_intMap (L := L₀) (O := W) i
  obtain ⟨φ1, hφ1⟩ := exists_intMap (L := L) (O := O) e1
  have hφψ : ∀ x : 𝓞 L₀, φ1 (algebraMap (𝓞 L₀) (𝓞 L) x) = j (ψ x) := by
    intro x
    apply hOinj
    rw [hφ1]
    have hc : (((algebraMap (𝓞 L₀) (𝓞 L) x : 𝓞 L) : L)) = algebraMap L₀ L (x : L₀) := rfl
    show τ (eK _) = _
    rw [hc, hext, ← hψ, hcomp, hτ]
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal O).comap φ1
  have hP'prime : P'.IsPrime := Ideal.comap_isPrime _ _
  let p : Ideal (𝓞 L₀) := v.asIdeal.comap (algebraMap (𝓞 L₀) (𝓞 L))
  have hover : P'.comap (algebraMap (𝓞 L₀) (𝓞 L)) = p := by
    ext x
    simp only [Ideal.mem_comap, P', p]
    rw [hφψ, hjmem, h x]
    constructor
    · intro hx
      exact ⟨ψ x, hx, hψ x⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← hWinj (hyx.trans (hψ x).symm)]
  have hv1 : v.asIdeal ∈ Ideal.primesOver p (𝓞 L) := ⟨v.isPrime, ⟨rfl⟩⟩
  have hP1 : P' ∈ Ideal.primesOver p (𝓞 L) := ⟨hP'prime, ⟨hover.symm⟩⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 L₀) L₀ L (𝓞 L) hP1 hv1
  let e : L →+* FractionRing O := e1.comp (σ : L ≃ₐ[L₀] L).toRingHom
  have he_int : ∀ x : 𝓞 L, e (x : L) =
      algebraMap O (FractionRing O) (φ1 (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x)) := by
    intro x
    rw [hφ1]
    show e1 (σ (algebraMap (𝓞 L) L x)) = e1 (algebraMap (𝓞 L) L (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x))
    rw [algebraMap_galRestrict_apply]
  have hv' : ∀ x : 𝓞 L, x ∈ v.asIdeal ↔
      ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (x : L) := by
    intro x
    rw [← hσ]
    simp only [P', Ideal.mem_comap]
    rw [he_int]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← hOinj hyx]
  refine ⟨O, inferInstance, inferInstance, inferInstance, j.toAlgebra, e, hjinj, hjfin, hjloc,
    fun x => induces_of_ideal e v hv' x, ?_⟩
  intro x y z hxyz
  have hσx : σ (algebraMap L₀ L x) = algebraMap L₀ L x := σ.commutes x
  have key : ι (i x) * algebraMap O Kf (j z) = algebraMap O Kf (j y) := by
    rw [← hcomp, ← hcomp, ← map_mul, hxyz]
  calc e ↑x * algebraMap O (FractionRing O) (algebraMap W O z)
      = τ (ι (i x) * algebraMap O Kf (j z)) := by
        rw [map_mul, hτ]
        show τ (eK (σ (algebraMap L₀ L x))) * _ = _
        rw [hσx, hext]
        try rfl
    _ = algebraMap O (FractionRing O) (algebraMap W O y) := by
        rw [key, hτ]
        try rfl

/- English proof (translation)
Establish `hinj : Function.Injective e` using `e.injective`. Establish `: NeZero n` using `⟨hn.ne'⟩`. Establish `hez : IsPrimitiveRoot (e z) n` using `hz.map_of_injective hinj`. Establish `key : ∀ g, ∃ u : Lˣ, e (u : L) = (χ g : K)`. Introduce `g`.

Establish `h1 : (χ g : K) ^ n = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, hχ g, Units.val_one]`. Take `⟨i, -, hi⟩` from `hez.eq_pow_of_pow_eq_one h1`. Use `⟨Units.mk0 (z ^ i) (pow_ne_zero _ (hz.ne_zero hn.ne')), ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, map_pow, hi]`.

Use `choose f hf using key`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩` and prove the remaining obligations. Conclude with `Units.ext (hinj (by simp [hf]))`. Introduce `a b`. Conclude with `Units.ext (hinj (by simp [hf]))`.
-/
theorem exists_char_descent {L K G : Type} [Field L] [Field K] [Group G] (e : L →+* K) {n : ℕ} (hn : 0 < n) {z : L}
    (hz : IsPrimitiveRoot z n) (χ : G →* Kˣ) (hχ : ∀ g, χ g ^ n = 1) :
    ∃ ψ : G →* Lˣ, ∀ g, e (ψ g : L) = (χ g : K) := by
  have hinj : Function.Injective e := e.injective
  have : NeZero n := ⟨hn.ne'⟩
  have hez : IsPrimitiveRoot (e z) n := hz.map_of_injective hinj
  have key : ∀ g, ∃ u : Lˣ, e (u : L) = (χ g : K) := by
    intro g
    have h1 : (χ g : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hχ g, Units.val_one]
    obtain ⟨i, -, hi⟩ := hez.eq_pow_of_pow_eq_one h1
    refine ⟨Units.mk0 (z ^ i) (pow_ne_zero _ (hz.ne_zero hn.ne')), ?_⟩
    rw [Units.val_mk0, map_pow, hi]
  choose f hf using key
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · exact Units.ext (hinj (by simp [hf]))
  · intro a b
    exact Units.ext (hinj (by simp [hf]))

end GlobalTheory.TwistChoice

end
