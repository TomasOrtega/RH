import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DualLemmaOfWachHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

/- English proof (translation)
Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := R) (M := M)`. Use `⟨fun g hg => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ k, g (k + 1) - g k ∈ I ^ k • Submodule.span R (Set.range s)`. Introduce `k`. Rewrite using `[hs]`.

Establish `h` using `SModEq.sub_mem.1 (hg (Nat.le_succ k))`. Establish `h2` using `neg_mem h`. Rewrite `h2` using `[neg_sub]`. Then use the resulting hypothesis. Use `choose A hA hAs using fun k => (Submodule.mem_ideal_smul_span_iff_exists_sum (I ^ k) s (g (k + 1) - g k)).1 (hd k)`. Establish `hc : ∀ i : Fin n, ∀ {a b : ℕ}, a ≤ b → (∑ k ∈ Finset.range a, A k i) ≡ (∑ k ∈ Finset.range b, A k i) [SMOD (I ^ a • ⊤ : Submodule R R)]`.

Introduce `i a b hab`. Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Finset.sum_range_add_sum_Ico _ hab, sub_add_cancel_left]`. Use `neg_mem (sum_mem fun k hk => ?_)` and prove the remaining obligations. Conclude with `Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (hA k i)`. Use `choose C hC using fun i : Fin n => hR.prec' _ (hc i)`.

Use `⟨g 0 + ∑ i, C i • s i, fun K => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem]`. Establish `hgK : g K = g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i`. Establish `h1 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) = g K - g 0` using `Finset.sum_range_sub g K`. Establish `h2 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) = ∑ i, (∑ k ∈ Finset.range K, A k i) • s i`.

Simplify using `only [← hAs, Finsupp.sum_fintype, zero_smul, implies_true, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Rewrite using `[← h2, h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[hgK]`.

Establish `hsplit : g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i - (g 0 + ∑ i, C i • s i) = ∑ i, ((∑ k ∈ Finset.range K, A k i) - C i) • s i`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[hsplit]`. Use `sum_mem fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations.

Establish `h` using `SModEq.sub_mem.1 (hC i K)`. Rewrite `h` using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis.
-/
private theorem isPrecomplete_of_module_finite {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [hR : IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨fun g hg => ?_⟩
  have hd : ∀ k, g (k + 1) - g k ∈ I ^ k • Submodule.span R (Set.range s) := by
    intro k
    rw [hs]
    have h := SModEq.sub_mem.1 (hg (Nat.le_succ k))
    have h2 := neg_mem h
    rwa [neg_sub] at h2
  choose A hA hAs using fun k =>
    (Submodule.mem_ideal_smul_span_iff_exists_sum (I ^ k) s (g (k + 1) - g k)).1 (hd k)
  have hc : ∀ i : Fin n, ∀ {a b : ℕ}, a ≤ b →
      (∑ k ∈ Finset.range a, A k i) ≡ (∑ k ∈ Finset.range b, A k i) [SMOD (I ^ a • ⊤ : Submodule R R)] := by
    intro i a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Finset.sum_range_add_sum_Ico _ hab,
      sub_add_cancel_left]
    refine neg_mem (sum_mem fun k hk => ?_)
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (hA k i)
  choose C hC using fun i : Fin n => hR.prec' _ (hc i)
  refine ⟨g 0 + ∑ i, C i • s i, fun K => ?_⟩
  rw [SModEq.sub_mem]
  have hgK : g K = g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
    have h1 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) = g K - g 0 := Finset.sum_range_sub g K
    have h2 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) =
        ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
      simp only [← hAs, Finsupp.sum_fintype, zero_smul, implies_true, Finset.sum_smul]
      exact Finset.sum_comm
    rw [← h2, h1]
    abel
  rw [hgK]
  have hsplit : g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i - (g 0 + ∑ i, C i • s i) =
      ∑ i, ((∑ k ∈ Finset.range K, A k i) - C i) • s i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  refine sum_mem fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h := SModEq.sub_mem.1 (hC i K)
  rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `haveI hmax : (IsLocalRing.maximalIdeal ↥(OL LL)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _`. Establish `hcomap : (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) = IsLocalRing.maximalIdeal ℤ_[l]` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)`. Establish `hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l]` using `by first`. Consider the case `(rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)`. Consider the case `exact (IsLocalRing.mem_maximalIdeal _).2 (PadicInt.mem_nonunits.2 PadicInt.norm_p_lt_one)`.

Establish `hl0 : algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l]) ≠ 0`. Rewrite using `[map_natCast]`. Introduce `h`. Establish `h2` using `congrArg (fun x : ↥(OL LL) => ((x : ↥LL.1) : Om l)) h`. Simplify using `at h2`.

Conclude with `(Fact.out : l.Prime).ne_zero h2`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ}` using `by first`. Consider the case `exact hϖ.maximalIdeal_eq`.

Consider the case `exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `key1 : ∀ (k : ℕ) (x : ↥(OL LL)), x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ ((e + 1) * k) → x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL))`. Introduce `k x hx`. Establish `hle : e * k ≤ (e + 1) * k` using `by rw [add_mul, one_mul]; exact Nat.le_add_right _ _`. Establish `hx' : x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ (e * k)` using `Ideal.pow_le_pow_right hle hx`.

Rewrite `hx'` using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `hx'`. Establish `hϖe : ϖ ^ e = ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) * algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l])`. Rewrite using `[hu, ← mul_assoc, Units.inv_mul, one_mul]`. Establish `hb : b * ϖ ^ (e * k) = ((l : ℤ_[l]) ^ k) • (b * ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) ^ k)`.

Rewrite using `[Algebra.smul_def, map_pow, pow_mul, hϖe, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow hl k) Submodule.mem_top`. Establish `key2 : ∀ (k : ℕ) (x : ↥(OL LL)), x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) → x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k`.

Introduce `k x hx`. Establish `hmap : (IsLocalRing.maximalIdeal ℤ_[l] ^ k).map (algebraMap ℤ_[l] ↥(OL LL)) ≤ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hcomap.ge) k`. Establish `hsub : ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) ≤ ((IsLocalRing.maximalIdeal ↥(OL LL)) ^ k).restrictScalars ℤ_[l]`.

Rewrite using `[Submodule.smul_le]`. Introduce `r hr y _`. Rewrite using `[Submodule.restrictScalars_mem, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (hmap (Ideal.mem_map_of_mem _ hr))`. Conclude with `hsub hx`.

Use `haveI hH : IsHausdorff (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hI` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal ↥(OL LL)) (IsLocalRing.maximalIdeal.isMaximal _).ne_top`. Establish `hx' : x ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal ↥(OL LL)) ^ i`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `i`. Establish `h` using `SModEq.sub_mem.1 (hx i)`. Rewrite `h` using `[sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis. Rewrite `hx'` using `[hI]`. Conclude with `(Submodule.mem_bot _).1 hx'`.

Use `haveI hP : IsPrecomplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hcau : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ a`. Introduce `a b hab`. Establish `h` using `SModEq.sub_mem.1 (hf hab)`.

Rewrite `h` using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis. Establish `hSp : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL)` using `isPrecomplete_of_module_finite _`. Take `⟨L, hL⟩` from `hSp.prec' (fun k => f ((e + 1) * k)) (fun {a b} hab => by`. Rewrite using `[SModEq.sub_mem]`. Conclude with `key1 a _ (hcau (Nat.mul_le_mul (le_refl _) hab)))`.

Use `⟨L, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]`. Establish `hk : k ≤ (e + 1) * k` using `by rw [add_mul, one_mul]; exact Nat.le_add_left k (e * k)`. Establish `h1` using `hcau hk`. Establish `h2 : f ((e + 1) * k) - L ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k` using `key2 k _ (SModEq.sub_mem.1 (hL k))`.

Establish `h3` using `Ideal.add_mem _ h1 h2`. Rewrite `h3` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Conclude with `IsAdicComplete.mk`.
-/
theorem complete_max {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  classical
  haveI hmax : (IsLocalRing.maximalIdeal ↥(OL LL)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have hcomap : (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) =
      IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
    by
    first
      | (rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
      | exact (IsLocalRing.mem_maximalIdeal _).2 (PadicInt.mem_nonunits.2 PadicInt.norm_p_lt_one)
  have hl0 : algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l]) ≠ 0 := by
    rw [map_natCast]
    intro h
    have h2 := congrArg (fun x : ↥(OL LL) => ((x : ↥LL.1) : Om l)) h
    simp at h2
    exact (Fact.out : l.Prime).ne_zero h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key1 : ∀ (k : ℕ) (x : ↥(OL LL)), x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ ((e + 1) * k) →
      x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) := by
    intro k x hx
    have hle : e * k ≤ (e + 1) * k := by rw [add_mul, one_mul]; exact Nat.le_add_right _ _
    have hx' : x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ (e * k) := Ideal.pow_le_pow_right hle hx
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
    obtain ⟨b, rfl⟩ := hx'
    have hϖe : ϖ ^ e = ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) * algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l]) := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    have hb : b * ϖ ^ (e * k) =
        ((l : ℤ_[l]) ^ k) • (b * ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) ^ k) := by
      rw [Algebra.smul_def, map_pow, pow_mul, hϖe, mul_pow]
      ring
    rw [hb]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl k) Submodule.mem_top
  have key2 : ∀ (k : ℕ) (x : ↥(OL LL)),
      x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) →
      x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k := by
    intro k x hx
    have hmap : (IsLocalRing.maximalIdeal ℤ_[l] ^ k).map (algebraMap ℤ_[l] ↥(OL LL)) ≤
        (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hcomap.ge) k
    have hsub : ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) ≤
        ((IsLocalRing.maximalIdeal ↥(OL LL)) ^ k).restrictScalars ℤ_[l] := by
      rw [Submodule.smul_le]
      intro r hr y _
      rw [Submodule.restrictScalars_mem, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hmap (Ideal.mem_map_of_mem _ hr))
    exact hsub hx
  haveI hH : IsHausdorff (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
    refine ⟨fun x hx => ?_⟩
    have hI := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal ↥(OL LL))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hx' : x ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal ↥(OL LL)) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      have h := SModEq.sub_mem.1 (hx i)
      rwa [sub_zero, Ideal.smul_eq_mul, Ideal.mul_top] at h
    rw [hI] at hx'
    exact (Submodule.mem_bot _).1 hx'
  haveI hP : IsPrecomplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
    refine ⟨fun f hf => ?_⟩
    have hcau : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ a := by
      intro a b hab
      have h := SModEq.sub_mem.1 (hf hab)
      rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h
    have hSp : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL) := isPrecomplete_of_module_finite _
    obtain ⟨L, hL⟩ := hSp.prec' (fun k => f ((e + 1) * k)) (fun {a b} hab => by
      rw [SModEq.sub_mem]
      exact key1 a _ (hcau (Nat.mul_le_mul (le_refl _) hab)))
    refine ⟨L, fun k => ?_⟩
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    have hk : k ≤ (e + 1) * k := by rw [add_mul, one_mul]; exact Nat.le_add_left k (e * k)
    have h1 := hcau hk
    have h2 : f ((e + 1) * k) - L ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k :=
      key2 k _ (SModEq.sub_mem.1 (hL k))
    have h3 := Ideal.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at h3
  exact IsAdicComplete.mk

/- English proof (translation)
Introduce `l _ K LL hg _`. Establish `hT` using `h1 l K 1 LL hg`. Take `⟨hE, hC, hQ⟩` from `h11 l K LL`. Use `complete_max LL` as an intermediate fact. Establish `h9D : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F` using `fun l' _ K' s' LL' h' => (h1 l' K' s' LL' h').2.2.2.2.2.2.2.2.1`.

Establish `hpt` using `Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9D`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Use `Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lemmaDN0_of_admits _ hE hC hQ (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg) hT.2.2.2.1 hT.2.2.2.2.1 hT.2.2.2.2.2.2.2.2.1 ?_ ?_` and prove the remaining obligations. Introduce `hA hl11 c ζ hζ`. Establish `hK : K.1 ≤ MaximalUnramifiedExtension l`.

Introduce `x hx`. Take `⟨y, hy⟩` from `hA.1.2 ⟨x, hx⟩`. Establish `hyx : ((y : ↥(K0 K)) : Om l) = x` using `congrArg (fun z : ↥K.1 => (z : Om l)) hy`. Rewrite using `[← hyx]`. Conclude with `y.2.2`.

Establish `hAD : CaseA K LL` using `⟨hK, by rw [← hp]; exact hA.2.2, hg⟩`. Establish `h5l : 5 ≤ l` using `by rw [← hp]; omega`. Take `⟨τ, hτ⟩` from `hpt l K LL hAD h5l c ζ (by rwa [hp] at hζ)`. Use `⟨τ, ?_, hτ⟩` and prove the remaining obligations. Take `⟨τs, ⟨hemb, -⟩, hres⟩` from `hτ`.

Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `x`. Establish `hy : (x : Om l) ∈ Ks K 1` using `(le_sup_left : K0 K ≤ Ks K 1) x.2`. Use `show τ (algebraMap ↥(K0 K) ↥K.1 x) = _`. Rewrite using `[hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]`.

Conclude with `hemb x ⟨x, hy⟩ rfl`. Rewrite using `[hp]`. Conclude with `Formalism.BasicNotions.Examples₂.LB.l_mem_max LL`.
-/
theorem lemmaDN0_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hT := h1 l K 1 LL hg
  obtain ⟨hE, hC, hQ⟩ := h11 l K LL
  have := complete_max LL
  have h9D : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l' _ K' s' LL' h' => (h1 l' K' s' LL' h').2.2.2.2.2.2.2.2.1
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9D
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lemmaDN0_of_admits _ hE hC hQ (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg) hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.2.2.2.1 ?_ ?_
  · intro hA hl11 c ζ hζ
    have hK : K.1 ≤ MaximalUnramifiedExtension l := by
      intro x hx
      obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
      have hyx : ((y : ↥(K0 K)) : Om l) = x := congrArg (fun z : ↥K.1 => (z : Om l)) hy
      rw [← hyx]
      exact y.2.2
    have hAD : CaseA K LL := ⟨hK, by rw [← hp]; exact hA.2.2, hg⟩
    have h5l : 5 ≤ l := by rw [← hp]; omega
    obtain ⟨τ, hτ⟩ := hpt l K LL hAD h5l c ζ (by rwa [hp] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  · rw [hp]
    exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev
