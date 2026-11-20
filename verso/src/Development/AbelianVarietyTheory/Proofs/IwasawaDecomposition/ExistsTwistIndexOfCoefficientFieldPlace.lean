import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.FormsStep.CoverPl

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

def vRing (v : AddValuation K (WithTop ℤ)) : ValuationSubring K where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := by
    show 0 ≤ v 1
    rw [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by
    show 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    show 0 ≤ v (-a)
    rw [v.map_neg]
    exact ha
  mem_or_inv_mem' x := by
    by_cases hx : 0 ≤ v x
    · exact Or.inl hx
    · right
      show 0 ≤ v x⁻¹
      by_contra hy
      push_neg at hx hy
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [v.map_zero] at hx
        exact absurd hx (not_lt.mpr le_top)
      have h1 : v x + v x⁻¹ = 0 := by
        rw [← v.map_mul, mul_inv_cancel₀ hx0, v.map_one]
      have h2 : v x + v x⁻¹ ≤ v x + 0 := add_le_add le_rfl hy.le
      rw [add_zero, h1] at h2
      exact absurd hx (not_lt.mpr h2)

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (a : K)` using `NumberField.RingOfIntegers.isIntegral_coe a`. Establish `h2 : IsIntegral (vRing v) (a : K)` using `h1.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h2`. Establish `h3 : algebraMap (vRing v) K y ∈ vRing v` using `y.2`. Rewrite `h3` using `[hy]`.

Conclude with `h3`.
-/
theorem v_nonneg_int [NumberField K] (v : AddValuation K (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (a : K) := by
  have h1 : IsIntegral ℤ (a : K) := NumberField.RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral (vRing v) (a : K) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : algebraMap (vRing v) K y ∈ vRing v := y.2
  rw [hy] at h3
  exact h3

/- English proof (translation)
Take `⟨p, hp, hev⟩` from `NumberField.RingOfIntegers.isIntegral_coe a`. Establish `h1 : IsIntegral O (e (a : K))`. Use `⟨p.map (algebraMap ℤ O), hp.map _, ?_⟩` and prove the remaining obligations. Establish `hc : (algebraMap O (FractionRing O)).comp (algebraMap ℤ O) = e.comp (algebraMap ℤ K)` using `RingHom.ext_int _ _`. Rewrite using `[Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hev, map_zero]`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.mp h1`.
-/
theorem emb_int_mem [NumberField K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (a : 𝓞 K) : ∃ y : O, algebraMap O (FractionRing O) y = e a := by
  obtain ⟨p, hp, hev⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  have h1 : IsIntegral O (e (a : K)) := by
    refine ⟨p.map (algebraMap ℤ O), hp.map _, ?_⟩
    have hc : (algebraMap O (FractionRing O)).comp (algebraMap ℤ O) = e.comp (algebraMap ℤ K) := RingHom.ext_int _ _
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hev, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.mp h1

/- English proof (translation)
Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective A z`. Use `haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)`. Establish `hinj : Function.Injective (algebraMap A (Localization.AtPrime q))` using `IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors`. Establish `hy0 : algebraMap A K y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Take `⟨c, hc⟩` from `ValuationRing.cond (algebraMap A (Localization.AtPrime q) x) (algebraMap A (Localization.AtPrime q) y)`.

Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective q.primeCompl c`. Establish `hs` using `IsLocalization.mk'_spec (Localization.AtPrime q) a s`. Break down `hc with hc | hc` into its components or cases. Establish `h : x * a = y * s` using `hinj (by`. Rewrite using `[map_mul, map_mul, ← hs, ← hc]`.

Use the proof step `ring)`. Use `⟨a, s, s.2, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, h, mul_comm]`. Establish `h : y * a = x * s` using `hinj (by`. Rewrite using `[map_mul, map_mul, ← hs, ← hc]`.

Use the proof step `ring)`. Use `⟨a, s, s.2, Or.inl ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, ← h, mul_comm]`.
-/
theorem exists_frac_compl {A : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) (z : K) :
    ∃ a s : A, s ∉ q ∧ (z * algebraMap A K s = algebraMap A K a ∨ z * algebraMap A K a = algebraMap A K s) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hy0 : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) x)
    (algebraMap A (Localization.AtPrime q) y)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl c
  have hs := IsLocalization.mk'_spec (Localization.AtPrime q) a s
  rcases hc with hc | hc
  · have h : x * a = y * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inr ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, h, mul_comm]
  · have h : y * a = x * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inl ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, ← h, mul_comm]

end SlopeTestRemainingChoices

section Cen

variable {K : Type} [Field K] [NumberField K]

def cen (v : AddValuation K (WithTop ℤ)) : Ideal (𝓞 K) where
  carrier := {a | 0 < v (a : K)}
  add_mem' {a b} ha hb := by
    show 0 < v ((a : K) + (b : K))
    exact lt_of_lt_of_le (lt_min ha hb) (v.map_add _ _)
  zero_mem' := by
    show 0 < v (0 : K)
    rw [v.map_zero]
    exact WithTop.coe_lt_top 0
  smul_mem' c a ha := by
    show 0 < v ((c : K) * (a : K))
    rw [v.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (v_nonneg_int v c))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_cen {v : AddValuation K (WithTop ℤ)} {a : 𝓞 K} : a ∈ cen v ↔ 0 < v (a : K) := Iff.rfl

/- English proof (translation)
Establish `h1 : (1 : 𝓞 K) ∈ cen v` using `h ▸ Submodule.mem_top`. Express the relevant statement in the definitionally equal form `0 < v (1 : K) at h1`. Rewrite `h1` using `[v.map_one]`. Conclude with `lt_irrefl _ h1`. Use the proof step `mem_or_mem' {a b} hab := by`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `ha : v (a : K) = 0` using `le_antisymm (not_lt.mp (fun h => hn.1 h)) (v_nonneg_int v a)`. Establish `hb : v (b : K) = 0` using `le_antisymm (not_lt.mp (fun h => hn.2 h)) (v_nonneg_int v b)`. Establish `h` using `(mem_cen (v := v)).mp hab`.

Express the relevant statement in the definitionally equal form `0 < v ((a : K) * (b : K)) at h`. Rewrite `h` using `[v.map_mul, ha, hb, add_zero]`. Conclude with `lt_irrefl _ h`.
-/
theorem cen_isPrime (v : AddValuation K (WithTop ℤ)) : (cen v).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 K) ∈ cen v := h ▸ Submodule.mem_top
    change 0 < v (1 : K) at h1
    rw [v.map_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' {a b} hab := by
    by_contra hn
    push_neg at hn
    have ha : v (a : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.1 h)) (v_nonneg_int v a)
    have hb : v (b : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.2 h)) (v_nonneg_int v b)
    have h := (mem_cen (v := v)).mp hab
    change 0 < v ((a : K) * (b : K)) at h
    rw [v.map_mul, ha, hb, add_zero] at h
    exact lt_irrefl _ h

/- English proof (translation)
Establish `hφ : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O (FractionRing O)`. Establish `hout : ∀ a : 𝓞 K, a ∉ q → v (a : K) = 0 ∧ ∃ u : O, IsUnit u ∧ algebraMap O (FractionRing O) u = e (a : K)`. Introduce `a ha`. Use `⟨le_antisymm (not_lt.mp (fun h => ha ((hq a).mpr h))) (v_nonneg_int v a), ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `emb_int_mem e a`.

Conclude with `⟨u, IsLocalRing.notMem_maximalIdeal.mp (fun hm => ha ((he a).mpr ⟨u, hm, hu⟩)), hu⟩`. Take `⟨a, s, hs, h⟩` from `exists_frac_compl q hq0 x`. Take `⟨hvs, us, hus, hes⟩` from `hout s hs`. Break down `h with h | h` into its components or cases. Take `⟨ua, hua⟩` from `emb_int_mem e a`.

Establish `h1 : 0 ≤ v x`. Establish `h'` using `congrArg v h`. Rewrite `h'` using `[v.map_mul]`. Express the relevant statement in the definitionally equal form `v x + v (s : K) = v (a : K) at h'`. Rewrite `h'` using `[hvs, add_zero]`.

Rewrite using `[h']`. Conclude with `v_nonneg_int v a`. Establish `h2 : e x ∈ (algebraMap O (FractionRing O)).range`. Use `⟨ua * ↑hus.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg e h`.

Rewrite `h'` using `[map_mul]`. Express the relevant statement in the definitionally equal form `e x * e (s : K) = e (a : K) at h'`. Rewrite `h'` using `[← hes, ← hua]`. Rewrite using `[map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]`. Conclude with `⟨fun _ => h2, fun _ => h1⟩`.

Distinguish the cases in `ha : a ∈ q`. Establish `hva` using `(hq a).mp ha`. Take `⟨ua, hum, hua⟩` from `(he a).mp ha`. Establish `h1 : ¬ 0 ≤ v x`. Introduce `hx`.

Establish `h'` using `congrArg v h`. Rewrite `h'` using `[v.map_mul]`. Express the relevant statement in the definitionally equal form `v x + v (a : K) = v (s : K) at h'`. Rewrite `h'` using `[hvs]`. Establish `h3 : 0 < v x + v (a : K)` using `lt_of_lt_of_le hva (le_add_of_nonneg_left hx)`.

Rewrite `h3` using `[h']`. Conclude with `lt_irrefl _ h3`. Establish `h2 : e x ∉ (algebraMap O (FractionRing O)).range`. Introduce and unpack `⟨y, hy⟩`. Establish `h'` using `congrArg e h`.

Rewrite `h'` using `[map_mul]`. Express the relevant statement in the definitionally equal form `e x * e (a : K) = e (s : K) at h'`. Rewrite `h'` using `[← hy, ← hua, ← hes, ← map_mul]`. Establish `h4` using `hφ h'`. Apply `IsLocalRing.notMem_maximalIdeal.mpr hus` to reduce the goal to its premises.

Rewrite using `[← h4]`. Conclude with `Ideal.mul_mem_left _ y hum`. Conclude with `⟨fun hx => absurd hx h1, fun hx => absurd hx h2⟩`. Take `⟨hva, ua, hua', hua⟩` from `hout a ha`. Establish `h1 : 0 ≤ v x`.

Establish `h'` using `congrArg v h`. Rewrite `h'` using `[v.map_mul]`. Express the relevant statement in the definitionally equal form `v x + v (a : K) = v (s : K) at h'`. Rewrite `h'` using `[hvs, hva, add_zero]`. Rewrite using `[h']`.

Establish `h2 : e x ∈ (algebraMap O (FractionRing O)).range`. Use `⟨us * ↑hua'.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg e h`. Rewrite `h'` using `[map_mul]`. Express the relevant statement in the definitionally equal form `e x * e (a : K) = e (s : K) at h'`.

Rewrite `h'` using `[← hes, ← hua]`. Rewrite using `[map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]`. Conclude with `⟨fun _ => h2, fun _ => h1⟩`.
-/
theorem v_nonneg_iff (v : AddValuation K (WithTop ℤ)) (q : Ideal (𝓞 K)) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hq : ∀ a : 𝓞 K, a ∈ q ↔ 0 < v (a : K)) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O)
    (he : ∀ a : 𝓞 K, a ∈ q ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (a : K)) (x : K) :
    0 ≤ v x ↔ e x ∈ (algebraMap O (FractionRing O)).range := by
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hout : ∀ a : 𝓞 K, a ∉ q → v (a : K) = 0 ∧ ∃ u : O, IsUnit u ∧ algebraMap O (FractionRing O) u = e (a : K) := by
    intro a ha
    refine ⟨le_antisymm (not_lt.mp (fun h => ha ((hq a).mpr h))) (v_nonneg_int v a), ?_⟩
    obtain ⟨u, hu⟩ := emb_int_mem e a
    exact ⟨u, IsLocalRing.notMem_maximalIdeal.mp (fun hm => ha ((he a).mpr ⟨u, hm, hu⟩)), hu⟩
  obtain ⟨a, s, hs, h⟩ := exists_frac_compl q hq0 x
  obtain ⟨hvs, us, hus, hes⟩ := hout s hs
  rcases h with h | h
  · obtain ⟨ua, hua⟩ := emb_int_mem e a
    have h1 : 0 ≤ v x := by
      have h' := congrArg v h
      rw [v.map_mul] at h'
      change v x + v (s : K) = v (a : K) at h'
      rw [hvs, add_zero] at h'
      rw [h']
      exact v_nonneg_int v a
    have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
      refine ⟨ua * ↑hus.unit⁻¹, ?_⟩
      have h' := congrArg e h
      rw [map_mul] at h'
      change e x * e (s : K) = e (a : K) at h'
      rw [← hes, ← hua] at h'
      rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
    exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases ha : a ∈ q
    · have hva := (hq a).mp ha
      obtain ⟨ua, hum, hua⟩ := (he a).mp ha
      have h1 : ¬ 0 ≤ v x := by
        intro hx
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs] at h'
        have h3 : 0 < v x + v (a : K) := lt_of_lt_of_le hva (le_add_of_nonneg_left hx)
        rw [h'] at h3
        exact lt_irrefl _ h3
      have h2 : e x ∉ (algebraMap O (FractionRing O)).range := by
        rintro ⟨y, hy⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hy, ← hua, ← hes, ← map_mul] at h'
        have h4 := hφ h'
        apply IsLocalRing.notMem_maximalIdeal.mpr hus
        rw [← h4]
        exact Ideal.mul_mem_left _ y hum
      exact ⟨fun hx => absurd hx h1, fun hx => absurd hx h2⟩
    · obtain ⟨hva, ua, hua', hua⟩ := hout a ha
      have h1 : 0 ≤ v x := by
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs, hva, add_zero] at h'
        rw [h']
      have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
        refine ⟨us * ↑hua'.unit⁻¹, ?_⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hes, ← hua] at h'
        rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
      exact ⟨fun _ => h2, fun _ => h1⟩

end Cen

section Main

/- English proof (translation)
Introduce `D cf b0 b1 Sx T Sp w`. Set `v : AddValuation D.LL0 (WithTop ℤ)` to `(D.what₂.places.val w).comap (algebraMap D.LL0 D.what₂.LL)`. Establish `hv : ∀ x : D.LL0, v x = D.what₂.places.val w (x : D.what₂.LL)` using `fun x => rfl`. Use `haveI := cen_isPrime v`. Establish `hp` using `D.what₂.places.resChar_prime w`.

Establish `hpc : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) ∈ cen v`. Rewrite using `[mem_cen, hv]`. Establish `h1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) : D.LL0) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)` using `by simp`. Rewrite using `[h1, D.what₂.places.val_resChar w]`. Conclude with `D.what₂.places.ramIdx_pos w` after adjusting the coercions.

Establish `hne : cen v ≠ ⊥`. Introduce `h`. Rewrite `hpc` using `[h, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hpc)`. Set `q : HeightOneSpectrum (𝓞 D.LL0)` to `⟨cen v, cen_isPrime v, hne⟩`.

Use `⟨Sp.eTw.symm q, ?_, ?_⟩` and prove the remaining obligations. Take `⟨hl, -⟩` from `Sp.pl_emb (Sp.eTw.symm q)`. Rewrite `hl` using `[Equiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `_ ∈ cen v at hl`. Assume the negation of the conclusion as `hne'`.

Establish `hcop : Nat.Coprime (T.l (Sp.eTw.symm q)) (D.what₂.places.resChar w)` using `(Nat.coprime_primes Fact.out hp).mpr hne'`. Take `⟨u, u', huv⟩` from `Nat.isCoprime_iff_coprime.mpr hcop`. Establish `h1 : (1 : 𝓞 D.LL0) ∈ cen v`. Establish `h2` using `congrArg (Int.cast : ℤ → 𝓞 D.LL0) huv`. Move the coercions through the operations in `at h2`.

Rewrite using `[← h2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hpc)`. Conclude with `(cen_isPrime v).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Introduce `x`. Take `⟨-, hq⟩` from `Sp.pl_emb (Sp.eTw.symm q)`.

Rewrite `hq` using `[Equiv.apply_symm_apply]`. Conclude with `v_nonneg_iff v (cen v) hne (fun a => mem_cen) (T.emb0 (Sp.eTw.symm q)) hq x`.
-/
theorem exists_setting_of_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host))
    (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  intro D cf b0 b1 Sx T Sp w
  let v : AddValuation D.LL0 (WithTop ℤ) := (D.what₂.places.val w).comap (algebraMap D.LL0 D.what₂.LL)
  have hv : ∀ x : D.LL0, v x = D.what₂.places.val w (x : D.what₂.LL) := fun x => rfl
  haveI := cen_isPrime v
  have hp := D.what₂.places.resChar_prime w
  have hpc : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) ∈ cen v := by
    rw [mem_cen, hv]
    have h1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) : D.LL0) : D.what₂.LL) =
        ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by simp
    rw [h1, D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hne : cen v ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpc
    exact hp.ne_zero (by exact_mod_cast hpc)
  let q : HeightOneSpectrum (𝓞 D.LL0) := ⟨cen v, cen_isPrime v, hne⟩
  refine ⟨Sp.eTw.symm q, ?_, ?_⟩
  · obtain ⟨hl, -⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hl
    change _ ∈ cen v at hl
    by_contra hne'
    have hcop : Nat.Coprime (T.l (Sp.eTw.symm q)) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes Fact.out hp).mpr hne'
    obtain ⟨u, u', huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : 𝓞 D.LL0) ∈ cen v := by
      have h2 := congrArg (Int.cast : ℤ → 𝓞 D.LL0) huv
      push_cast at h2
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hpc)
    exact (cen_isPrime v).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro x
    obtain ⟨-, hq⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hq
    exact v_nonneg_iff v (cen v) hne (fun a => mem_cen) (T.emb0 (Sp.eTw.symm q)) hq x

end Main

end GlobalTheory.HeightCounting.FormsStep.CoverPl
