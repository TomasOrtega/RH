import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativesInBlowupCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

/- English proof (translation)
Use `Finset.induction_on u ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `b t hb ih`. Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb, ← ih]`. Simplify using the standard rewrite rules.
-/
private theorem finset_sum_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {μ : Type*} (u : Finset μ) (D : μ → Derivation R A A) (x : A) :
    (∑ j ∈ u, D j) x = ∑ j ∈ u, (D j) x := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem smul_derivation_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (a : A) (D : Derivation R A A) (x : A) : (a • D) x = a * D x := by
  simp

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

/- English proof (translation)
Establish `hmapspan : Ideal.span (⇑φ '' (J : Set S)) = Ideal.map φ J`. Rewrite using `[← Ideal.map_span, Ideal.span_eq]`. Establish `hgen : ∀ x ∈ (⇑φ '' (J : Set S)), partialDeriv k ι S₁ i x ∈ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L')`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `h1 : partialDeriv k ι S₁ i (φ f) = coord k ι S₁ s * φ (partialDeriv k ι S i f)` using `partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f`.

Establish `h2 : φ (partialDeriv k ι S i f) ∈ Ideal.map φ (derivIdeal k J)` using `Ideal.mem_map_of_mem φ (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (SetLike.mem_coe.mp hf))`. Take `⟨z, hz, hzeq⟩` from `Ideal.mem_span_singleton_mul.mp (hD h2)`. Rewrite using `[h1, ← hzeq]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨z, Submodule.mem_sup_right hz, by ring⟩`. Establish `hGT : Ideal.span (⇑φ '' (J : Set S)) ≤ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L')`.

Rewrite using `[hmapspan, ← hJ]`. Conclude with `Ideal.mul_mono_right le_sup_left`. Establish `hmem : coord k ι S₁ s ^ (c + 1) * g ∈ Ideal.span (⇑φ '' (J : Set S))`. Rewrite using `[hmapspan, ← hJ]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩`.

Establish `key` using `derivation_apply_mem_of_mem_span (partialDeriv k ι S₁ i) hGT hgen hmem`. Establish `hDy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0` using `partialDeriv_coord_of_ne k ι S₁ i s his`. Establish `hDypow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1)) = 0`. Rewrite using `[Derivation.leibniz_pow, hDy, smul_zero, smul_zero]`. Establish `hexp : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1) * g) = coord k ι S₁ s ^ (c + 1) * partialDeriv k ι S₁ i g`.

Rewrite using `[Derivation.leibniz, hDypow, smul_zero, add_zero, smul_eq_mul]`. Rewrite `key` using `[hexp]`. Take `⟨w, hw, hweq⟩` from `Ideal.mem_span_singleton_mul.mp key`. Establish `hnz : coord k ι S₁ s ^ (c + 1) ∈ nonZeroDivisors S₁` using `pow_mem hnzd (c + 1)`. Establish `h0 : (partialDeriv k ι S₁ i g - w) * coord k ι S₁ s ^ (c + 1) = 0`.

Take the linear combination `-hweq`. Establish `h1 : partialDeriv k ι S₁ i g - w = 0` using `(mem_nonZeroDivisors_iff.mp hnz).2 _ h0`. Establish `h2 : partialDeriv k ι S₁ i g = w` using `sub_eq_zero.mp h1`. Rewrite using `[h2]`. Conclude with `hw`.
-/
theorem partialDeriv_mem_sup_of_span_pow_mul_eq_map
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (L L' : Ideal S₁) (c : ℕ)
    (hJ : Ideal.span {coord k ι S₁ s ^ (c + 1)} * L = Ideal.map φ J)
    (hD : Ideal.map φ (derivIdeal k J) ≤ Ideal.span {coord k ι S₁ s ^ c} * L')
    (g : S₁) (hg : g ∈ L) :
    partialDeriv k ι S₁ i g ∈ L ⊔ L' := by
  have hmapspan : Ideal.span (⇑φ '' (J : Set S)) = Ideal.map φ J := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hgen : ∀ x ∈ (⇑φ '' (J : Set S)),
      partialDeriv k ι S₁ i x ∈ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 : partialDeriv k ι S₁ i (φ f)
        = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
      partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
    have h2 : φ (partialDeriv k ι S i f) ∈ Ideal.map φ (derivIdeal k J) :=
      Ideal.mem_map_of_mem φ
        (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (SetLike.mem_coe.mp hf))
    obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp (hD h2)
    rw [h1, ← hzeq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, Submodule.mem_sup_right hz, by ring⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S))
      ≤ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rw [hmapspan, ← hJ]
    exact Ideal.mul_mono_right le_sup_left
  have hmem : coord k ι S₁ s ^ (c + 1) * g ∈ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [hmapspan, ← hJ]
    exact Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩
  have key := derivation_apply_mem_of_mem_span (partialDeriv k ι S₁ i) hGT hgen hmem
  have hDy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hDypow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hDy, smul_zero, smul_zero]
  have hexp : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1) * g)
      = coord k ι S₁ s ^ (c + 1) * partialDeriv k ι S₁ i g := by
    rw [Derivation.leibniz, hDypow, smul_zero, add_zero, smul_eq_mul]
  rw [hexp] at key
  obtain ⟨w, hw, hweq⟩ := Ideal.mem_span_singleton_mul.mp key
  have hnz : coord k ι S₁ s ^ (c + 1) ∈ nonZeroDivisors S₁ := pow_mem hnzd (c + 1)
  have h0 : (partialDeriv k ι S₁ i g - w) * coord k ι S₁ s ^ (c + 1) = 0 := by
    linear_combination -hweq
  have h1 : partialDeriv k ι S₁ i g - w = 0 :=
    (mem_nonZeroDivisors_iff.mp hnz).2 _ h0
  have h2 : partialDeriv k ι S₁ i g = w := sub_eq_zero.mp h1
  rw [h2]
  exact hw

/- English proof (translation)
Take `⟨e, rfl⟩ : ∃ e, m = e + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `hJmem : ∀ f ∈ J, ∃ f₁ ∈ J₁, φ f = coord k ι S₁ s ^ (e + 1) * f₁`. Introduce `f hf`. Take `⟨f₁, hf₁, hfe⟩` from `Ideal.mem_span_singleton_mul.mp (hJ (Ideal.mem_map_of_mem φ hf))`.

Conclude with `⟨f₁, hf₁, hfe.symm⟩`. Establish `htan : ∀ j : ι, j ≠ i → partialDeriv k ι S₁ j ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i})`. Introduce `j hj`. Rewrite using `[mem_tangentDerivations_span_singleton]`. Rewrite using `[partialDeriv_coord_of_ne k ι S₁ j i hj]`.

Conclude with `Submodule.zero_mem _`. Establish `htanmul : (coord k ι S₁ i) • partialDeriv k ι S₁ i ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i})` using `smul_mem_tangentDerivations k (Ideal.span {coord k ι S₁ i}) (Ideal.subset_span (Set.mem_singleton _)) (partialDeriv k ι S₁ i)`. Rewrite using `[Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap]`. Take `⟨f₁, hf₁, hfe⟩` from `hJmem f hf`. Use `Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * f₁, ?_, ?_⟩` and prove the remaining obligations. Conclude with `le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (J₁.mul_mem_left _ hf₁)`. Rewrite using `[hfe]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `D hD f hf`. Rewrite using `[Ideal.mem_comap]`. Take `⟨f₁, hf₁, hfe⟩` from `hJmem f hf`. Establish `hpd : ∀ j : ι, j ≠ i → partialDeriv k ι S₁ j f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁`.

Introduce `j hj`. Conclude with `derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (partialDeriv k ι S₁ j) (htan j hj) hf₁`. Establish `hpdi : coord k ι S₁ i * partialDeriv k ι S₁ i f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁`. Establish `h` using `derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ ((coord k ι S₁ i) • partialDeriv k ι S₁ i) htanmul hf₁`. Rewrite `h` using `[smul_derivation_apply]`. Then use the resulting hypothesis.

Establish `hDi : D (coord k ι S i) ∈ Ideal.span {coord k ι S i}` using `(mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hDi`. Establish `hDf : φ (D f) = ∑ j : ι, φ (D (coord k ι S j)) * φ (partialDeriv k ι S j f)`. Establish `h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f` using `by conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]`. Rewrite using `[finset_sum_derivation_apply]`.

Conclude with `Finset.sum_congr rfl (fun j _ => smul_derivation_apply _ _ _)`. Rewrite using `[h0, map_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => map_mul φ _ _)`. Rewrite using `[hDf]`. Use `Ideal.sum_mem _ ?_` and prove the remaining obligations.

Introduce `j _`. Distinguish the cases in `hji : j = i`. Rewrite using `[hji]`. Establish `h1 : φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i f₁` using `map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f f₁ e hfe`. Establish `h2 : φ (D (coord k ι S i)) = φ a * (coord k ι S₁ i * coord k ι S₁ s)`.

Rewrite using `[← ha, map_mul, hin i hiT his]`. Rewrite using `[h1, h2]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨φ a * coord k ι S₁ s * (coord k ι S₁ i * partialDeriv k ι S₁ i f₁), Ideal.mul_mem_left _ _ hpdi, by ring⟩`. Establish `hkey : φ (partialDeriv k ι S j f) ∈ Ideal.span {coord k ι S₁ s ^ e} * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁`. Distinguish the cases in `hjT : j ∈ T`.

Distinguish the cases in `hjs : j = s`. Rewrite using `[hjs]`. Establish `h1` using `map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd f f₁ e hfe`. Establish `hbr : coord k ι S₁ s * partialDeriv k ι S₁ s f₁ + ((e + 1 : ℕ) : S₁) * f₁ - ∑ l ∈ T.erase s, coord k ι S₁ l * partialDeriv k ι S₁ l f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁`. Use `Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_` and prove the remaining obligations.

Conclude with `Ideal.mul_mem_left _ _ (hpd s his.symm)`. Conclude with `Ideal.mul_mem_left _ _ (le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ hf₁)`. Use `Ideal.sum_mem _ ?_` and prove the remaining obligations. Introduce `l _`. Distinguish the cases in `hli : l = i`.

Rewrite using `[hli]`. Conclude with `hpdi`. Conclude with `Ideal.mul_mem_left _ _ (hpd l hli)`. Rewrite using `[h1]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨_, hbr, rfl⟩`.

Establish `h1` using `map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd j hjT hjs f f₁ e hfe`. Rewrite using `[h1]`. Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨_, hpd j hji, rfl⟩`. Establish `h1` using `map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT j hjT f f₁ e hfe`. Rewrite using `[h1]`.

Conclude with `Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * partialDeriv k ι S₁ j f₁, Ideal.mul_mem_left _ _ (hpd j hji), by ring⟩`. Conclude with `Ideal.mul_mem_left _ _ hkey`.
-/
theorem map_logDerivIdeal_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ) (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (logDerivIdeal k (Ideal.span {coord k ι S i}) J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)}
          * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hJmem : ∀ f ∈ J, ∃ f₁ ∈ J₁, φ f = coord k ι S₁ s ^ (e + 1) * f₁ := by
    intro f hf
    obtain ⟨f₁, hf₁, hfe⟩ := Ideal.mem_span_singleton_mul.mp (hJ (Ideal.mem_map_of_mem φ hf))
    exact ⟨f₁, hf₁, hfe.symm⟩
  have htan : ∀ j : ι, j ≠ i →
      partialDeriv k ι S₁ j ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) := by
    intro j hj
    rw [mem_tangentDerivations_span_singleton]
    rw [partialDeriv_coord_of_ne k ι S₁ j i hj]
    exact Submodule.zero_mem _
  have htanmul : (coord k ι S₁ i) • partialDeriv k ι S₁ i
      ∈ tangentDerivations k (Ideal.span {coord k ι S₁ i}) :=
    smul_mem_tangentDerivations k (Ideal.span {coord k ι S₁ i})
      (Ideal.subset_span (Set.mem_singleton _)) (partialDeriv k ι S₁ i)
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    refine Ideal.mem_span_singleton_mul.mpr ⟨coord k ι S₁ s * f₁, ?_, ?_⟩
    · exact le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ (J₁.mul_mem_left _ hf₁)
    · rw [hfe]; ring
  · intro D hD f hf
    rw [Ideal.mem_comap]
    obtain ⟨f₁, hf₁, hfe⟩ := hJmem f hf
    have hpd : ∀ j : ι, j ≠ i →
        partialDeriv k ι S₁ j f₁ ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      intro j hj
      exact derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        (partialDeriv k ι S₁ j) (htan j hj) hf₁
    have hpdi : coord k ι S₁ i * partialDeriv k ι S₁ i f₁
        ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
      have h := derivation_apply_mem_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁
        ((coord k ι S₁ i) • partialDeriv k ι S₁ i) htanmul hf₁
      rwa [smul_derivation_apply] at h
    have hDi : D (coord k ι S i) ∈ Ideal.span {coord k ι S i} :=
      (mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hDi
    have hDf : φ (D f) = ∑ j : ι, φ (D (coord k ι S j)) * φ (partialDeriv k ι S j f) := by
      have h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f := by
        conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]
        rw [finset_sum_derivation_apply]
        exact Finset.sum_congr rfl (fun j _ => smul_derivation_apply _ _ _)
      rw [h0, map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_mul φ _ _)
    rw [hDf]
    refine Ideal.sum_mem _ ?_
    intro j _
    by_cases hji : j = i
    · rw [hji]
      have h1 : φ (partialDeriv k ι S i f)
          = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i f₁ :=
        map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f f₁ e hfe
      have h2 : φ (D (coord k ι S i)) = φ a * (coord k ι S₁ i * coord k ι S₁ s) := by
        rw [← ha, map_mul, hin i hiT his]
      rw [h1, h2]
      exact Ideal.mem_span_singleton_mul.mpr
        ⟨φ a * coord k ι S₁ s * (coord k ι S₁ i * partialDeriv k ι S₁ i f₁),
          Ideal.mul_mem_left _ _ hpdi, by ring⟩
    · have hkey : φ (partialDeriv k ι S j f)
          ∈ Ideal.span {coord k ι S₁ s ^ e}
              * logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
        by_cases hjT : j ∈ T
        · by_cases hjs : j = s
          · rw [hjs]
            have h1 := map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd f f₁ e hfe
            have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s f₁ + ((e + 1 : ℕ) : S₁) * f₁
                - ∑ l ∈ T.erase s, coord k ι S₁ l * partialDeriv k ι S₁ l f₁
                ∈ logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ := by
              refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
              · exact Ideal.mul_mem_left _ _ (hpd s his.symm)
              · exact Ideal.mul_mem_left _ _
                  (le_logDerivIdeal k (Ideal.span {coord k ι S₁ i}) J₁ hf₁)
              · refine Ideal.sum_mem _ ?_
                intro l _
                by_cases hli : l = i
                · rw [hli]; exact hpdi
                · exact Ideal.mul_mem_left _ _ (hpd l hli)
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hbr, rfl⟩
          · have h1 :=
              map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd j hjT hjs f f₁ e hfe
            rw [h1]
            exact Ideal.mem_span_singleton_mul.mpr ⟨_, hpd j hji, rfl⟩
        · have h1 :=
            map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT j hjT f f₁ e hfe
          rw [h1]
          exact Ideal.mem_span_singleton_mul.mpr
            ⟨coord k ι S₁ s * partialDeriv k ι S₁ j f₁,
              Ideal.mul_mem_left _ _ (hpd j hji), by ring⟩
      exact Ideal.mul_mem_left _ _ hkey

/- English proof (translation)
Use `revert hj`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`. Rewrite using `[logDerivIdealIterate_zero, logDerivIdealIterate_zero, Nat.sub_zero]`.

Conclude with `hJ`. Consider the case `succ j ih`. Introduce `hj`. Establish `h1` using `ih (Nat.le_of_succ_le hj)`. Establish `h2` using `map_logDerivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd i hiT his (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J) (logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁) (m - j) (by omega) h1`.

Rewrite using `[logDerivIdealIterate_succ, logDerivIdealIterate_succ]`. Establish `hsub : m - j - 1 = m - (j + 1)` using `by omega`. Rewrite `h2` using `[hsub]`. Then use the resulting hypothesis.
-/
theorem map_logDerivIdealIterate_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)}
          * logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁ := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero, Nat.sub_zero]
      exact hJ
  | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have h2 := map_logDerivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd i hiT his
        (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
        (logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁) (m - j) (by omega) h1
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      have hsub : m - j - 1 = m - (j + 1) := by omega
      rwa [hsub] at h2

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
