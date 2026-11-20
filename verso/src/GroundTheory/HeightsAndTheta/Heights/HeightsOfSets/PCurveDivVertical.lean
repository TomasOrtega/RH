import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveDivVertical

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def wt (T : Finset K) : (Σ k, ι k) → ℕ := fun p ↦ if p.1 ∈ T then 1 else 0

def proj (T : Finset K) : MRing ι →+* MRing ι :=
  GradedRing.projZeroRingHom (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T))

/- English proof (translation)
Rewrite using `[proj, GradedRing.projZeroRingHom_apply]`. Conclude with `weightedDecomposition.decompose'_apply ℤ (wt T) f 0`.
-/
theorem proj_apply (T : Finset K) (f : MRing ι) :
    proj T f = weightedHomogeneousComponent (wt T) 0 f := by
  rw [proj, GradedRing.projZeroRingHom_apply]
  exact weightedDecomposition.decompose'_apply ℤ (wt T) f 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h p hp`. Conclude with `(mul_eq_zero.mp (h p (Finsupp.mem_support_iff.mpr hp))).resolve_left hp`. Introduce `h p hp`.

Rewrite using `[smul_eq_mul, h p (Finsupp.mem_support_iff.mp hp), mul_zero]`.
-/
theorem weight_eq_zero_iff {σ : Type*} (w : σ → ℕ) (d : σ →₀ ℕ) :
    Finsupp.weight w d = 0 ↔ ∀ p, d p ≠ 0 → w p = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h p hp
    exact (mul_eq_zero.mp (h p (Finsupp.mem_support_iff.mpr hp))).resolve_left hp
  · intro h p hp
    rw [smul_eq_mul, h p (Finsupp.mem_support_iff.mp hp), mul_zero]

/- English proof (translation)
Rewrite using `[proj_apply, coeff_weightedHomogeneousComponent]`. Establish `: Finsupp.weight (wt T) d = 0 ↔ ∀ p, d p ≠ 0 → p.1 ∉ T`. Rewrite using `[weight_eq_zero_iff]`. Use `forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_` and prove the remaining obligations. Unfold `wt`.

Apply the tactic sequence `split_ifs with h <;> simp [h]`. Distinguish the cases in `h : ∀ p, d p ≠ 0 → p.1 ∉ T`. Rewrite using `[if_pos (this.mpr h), if_pos h]`. Rewrite using `[if_neg (mt this.mp h), if_neg h]`.
-/
theorem coeff_proj (T : Finset K) (f : MRing ι) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (proj T f) = if ∀ p, d p ≠ 0 → p.1 ∉ T then coeff d f else 0 := by
  classical
  rw [proj_apply, coeff_weightedHomogeneousComponent]
  have : Finsupp.weight (wt T) d = 0 ↔ ∀ p, d p ≠ 0 → p.1 ∉ T := by
    rw [weight_eq_zero_iff]
    refine forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_
    unfold wt
    split_ifs with h <;> simp [h]
  by_cases h : ∀ p, d p ≠ 0 → p.1 ∉ T
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (mt this.mp h), if_neg h]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_proj, if_pos (fun _ _ ↦ Finset.notMem_empty _)]`.
-/
theorem proj_empty (f : MRing ι) : proj ∅ f = f := by
  ext d
  rw [coeff_proj, if_pos (fun _ _ ↦ Finset.notMem_empty _)]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_proj, coeff_proj, coeff_proj]`. Distinguish the cases in `h : ∀ p, d p ≠ 0 → p.1 ∉ T`. Rewrite using `[if_pos h, if_pos h, if_pos fun p hp hS ↦ h p hp (hST hS)]`. Rewrite using `[if_neg h, if_neg h]`.
-/
theorem proj_proj {S T : Finset K} (hST : S ⊆ T) (f : MRing ι) : proj T (proj S f) = proj T f := by
  ext d
  rw [coeff_proj, coeff_proj, coeff_proj]
  by_cases h : ∀ p, d p ≠ 0 → p.1 ∉ T
  · rw [if_pos h, if_pos h, if_pos fun p hp hS ↦ h p hp (hST hS)]
  · rw [if_neg h, if_neg h]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_proj, coeff_C, constantCoeff_eq]`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (Ne.symm hd), if_neg]`. Introduce `h`. Apply `hd` to reduce the goal to its premises. Use extensionality with `p`. Assume the negation of the conclusion as `hp`.

Conclude with `h p hp (Finset.mem_univ _)`.
-/
theorem proj_univ (f : MRing ι) : proj Finset.univ f = C (constantCoeff f) := by
  ext d
  rw [coeff_proj, coeff_C, constantCoeff_eq]
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg (Ne.symm hd), if_neg]
    intro h
    apply hd
    ext p
    by_contra hp
    exact h p hp (Finset.mem_univ _)

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_proj, coeff_zero, coeff_X]`. Use `split_ifs with h1 h2`. Substitute `h2` using the available equality. Conclude with `absurd hk (h1 ⟨k, i⟩ (by simp))`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem proj_X_of_mem {T : Finset K} {k : K} (hk : k ∈ T) (i : ι k) :
    proj T (X ⟨k, i⟩ : MRing ι) = 0 := by
  ext d
  rw [coeff_proj, coeff_zero, coeff_X]
  split_ifs with h1 h2
  · subst h2
    exact absurd hk (h1 ⟨k, i⟩ (by simp))
  · rfl
  · rfl

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_proj, coeff_X]`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Substitute `h2` using the available equality. Conclude with `absurd (fun p hp ↦ by`. Rewrite `hp` using `[Finsupp.single_apply]`. Use `split_ifs at hp with hq`. Substitute `hq` using the available equality.

Conclude with `hk`. Conclude with `absurd rfl hp) h1`. Both sides reduce to the same expression.
-/
theorem proj_X_of_notMem {T : Finset K} {k : K} (hk : k ∉ T) (i : ι k) :
    proj T (X ⟨k, i⟩ : MRing ι) = X ⟨k, i⟩ := by
  ext d
  rw [coeff_proj, coeff_X]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · subst h2
    exact absurd (fun p hp ↦ by
      rw [Finsupp.single_apply] at hp
      split_ifs at hp with hq
      · subst hq; exact hk
      · exact absurd rfl hp) h1
  · rfl

/- English proof (translation)
Introduce `d hd`. Establish `hmon` using `hf d (mem_support_iff.mpr hd)`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp), Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Unfold `wt`.

Distinguish the cases in `hk : k ∈ T`. Simplify using `only [hk, if_true, smul_eq_mul, mul_one]`. Conclude with `hmon k`. Simplify using `[hk]`.
-/
theorem isWeightedHomogeneous_of_isMultiHomog (T : Finset K) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (wt T) f (∑ k, if k ∈ T then a k else 0) := by
  classical
  intro d hd
  have hmon := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold wt
  by_cases hk : k ∈ T
  · simp only [hk, if_true, smul_eq_mul, mul_one]
    exact hmon k
  · simp [hk]

/- English proof (translation)
Take `⟨G, hG, rfl⟩` from `hW`. Rewrite using `[← Ideal.span_union]`. Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce and unpack `x (hx | hx)`. Take `⟨b, hb⟩` from `hG x hx`.

Conclude with `⟨_, isWeightedHomogeneous_of_isMultiHomog T hb⟩`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `⟨_, isWeightedHomogeneous_of_isMultiHomog T hs⟩`.
-/
theorem isHomogeneous_sup (T : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    (W ⊔ Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)) := by
  obtain ⟨G, hG, rfl⟩ := hW
  rw [← Ideal.span_union]
  apply Ideal.homogeneous_span
  rintro x (hx | hx)
  · obtain ⟨b, hb⟩ := hG x hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hb⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hs⟩

/- English proof (translation)
Use `set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)`. Use `replace hV : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ J ≤ q) V := hV`. Establish `hcore : (V.homogeneousCore 𝒜).toIdeal.IsPrime` using `hV.prop.1.homogeneousCore`. Establish `hJc : J ≤ (V.homogeneousCore 𝒜).toIdeal` using `hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hV.prop.2)`. Establish `heq` using `hV.eq_of_le ⟨hcore, hJc⟩ (Ideal.toIdeal_homogeneousCore_le 𝒜 V)`.

Rewrite using `[← heq]`. Conclude with `(V.homogeneousCore 𝒜).isHomogeneous`.
-/
theorem isHomogeneous_of_mem_minimalPrimes (T : Finset K) {J V : Ideal (MRing ι)}
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)))
    (hV : V ∈ J.minimalPrimes) :
    V.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)) := by
  set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)
  replace hV : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ J ≤ q) V := hV
  have hcore : (V.homogeneousCore 𝒜).toIdeal.IsPrime := hV.prop.1.homogeneousCore
  have hJc : J ≤ (V.homogeneousCore 𝒜).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hV.prop.2)
  have heq := hV.eq_of_le ⟨hcore, hJc⟩ (Ideal.toIdeal_homogeneousCore_le 𝒜 V)
  rw [← heq]
  exact (V.homogeneousCore 𝒜).isHomogeneous

end CurveDivVertical

open CurveDivVertical in

/- English proof (translation)
Introduce `K _ ι _ W s a hW hs hsW V hV hhor`. Take `⟨_, ⟨hWp, hWh, -⟩, -, hdim⟩` from `hW`. Take `⟨hVmin', hVrel⟩` from `hV`. Establish `hVmin : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ W ⊔ Ideal.span {s} ≤ q) V` using `hVmin'`. Establish `hVp : V.IsPrime` using `hVmin.prop.1`.

Establish `hWV : W ≤ V` using `le_trans le_sup_left hVmin.prop.2`. Establish `hsV : s ∈ V` using `hVmin.prop.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Establish `hproj : ∀ (T : Finset K) f, f ∈ V → proj T f ∈ V`. Introduce `T f hf`. Rewrite using `[proj_apply]`.

Conclude with `weightedHomogeneousComponent_mem_of_mem ℤ (wt T) (isHomogeneous_of_mem_minimalPrimes T (isHomogeneous_sup T hWh hs) hVmin') hf 0`. Set `Z` to `PrimeSpectrum.zeroLocus (R := MRing ι) (W : Set (MRing ι))`. Set `pt : (I : Ideal (MRing ι)) → I.IsPrime → W ≤ I → Z` to `fun I hI hWI ↦ ⟨⟨I, hI⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hWI⟩`. Establish `pt_lt : ∀ (I J : Ideal (MRing ι)) hI hJ hWI hWJ, I < J → pt I hI hWI < pt J hJ hWJ` using `fun _ _ _ _ _ _ h ↦ h`. Establish `hPp : ∀ T : Finset K, (V.comap (proj T)).IsPrime` using `fun T ↦ hVp.comap _`.

Establish `hVP : ∀ T : Finset K, V ≤ V.comap (proj T)` using `fun T f hf ↦ hproj T f hf`. Set `P : Finset K → Z` to `fun T ↦ pt _ (hPp T) (hWV.trans (hVP T))`. Establish `hstep : ∀ (T : Finset K) (k : K), k ∉ T → P T < P (insert k T)`. Introduce `T k hk`. It suffices to establish `key : V.comap (proj T) < V.comap (proj (insert k T)) from pt_lt _ _ (hPp T) (hPp _) (hWV.trans (hVP T)) (hWV.trans (hVP _)) key`.

Use `lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `proj _ f ∈ V`. Rewrite using `[← proj_proj (Finset.subset_insert k T)]`. Conclude with `hproj _ _ hf`. Take `⟨i, hi⟩` from `hVrel k`.

Establish `h1 : (X ⟨k, i⟩ : MRing ι) ∈ V.comap (proj (insert k T))`. Express the relevant statement in the definitionally equal form `proj _ _ ∈ V`. Rewrite using `[proj_X_of_mem (Finset.mem_insert_self k T)]`. Conclude with `V.zero_mem`. Rewrite `h1` using `[← h]`.

Express the relevant statement in the definitionally equal form `proj _ _ ∈ V at h1`. Rewrite `h1` using `[proj_X_of_notMem hk]`. Conclude with `hi h1`. Establish `hbot : pt W hWp le_rfl < P ∅`. It suffices to establish `key : W < V.comap (proj ∅) from pt_lt _ _ hWp (hPp ∅) le_rfl (hWV.trans (hVP ∅)) key`.

Use `lt_of_le_of_ne (hWV.trans (hVP ∅)) fun h ↦ hsW ?_` and prove the remaining obligations. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `proj ∅ s ∈ V`. Rewrite using `[proj_empty]`. Conclude with `hsV`.

Establish `hchain : ∀ T : Finset K, ∃ l : LTSeries Z, l.last = P T ∧ l.length = T.card + 1`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨(RelSeries.singleton _ (pt W hWp le_rfl)).snoc (P ∅) hbot, RelSeries.last_snoc _ _ _, rfl⟩`. Consider the case `insert k T hk ih`.

Take `⟨l, hl, hlen⟩` from `ih`. Use `⟨l.snoc (P (insert k T)) (hl ▸ hstep T k hk), RelSeries.last_snoc _ _ _, ?_⟩` and prove the remaining obligations. Use `show l.length + 1 = _`. Rewrite using `[hlen, Finset.card_insert_of_notMem hk]`. Establish `hQp : (Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)})).IsPrime` using `((Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two).comap _`.

Establish `hPQ : V.comap (proj Finset.univ) < Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)})`. Establish `hc : ∀ c : ℤ, C c ∈ V → c = 0` using `fun c hc ↦ by`. Establish `: c ∈ V.comap (C : ℤ →+* MRing ι)` using `hc`. Rewrite `this` using `[hhor]`. Conclude with `this`.

Use `lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `proj _ f ∈ V at hf`. Rewrite `hf` using `[proj_univ]`. Rewrite using `[Ideal.mem_comap, hc _ hf]`. Conclude with `Ideal.zero_mem _`.

Establish `h2 : (C 2 : MRing ι) ∈ Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)})`. Rewrite using `[Ideal.mem_comap, constantCoeff_C]`. Conclude with `Ideal.mem_span_singleton_self 2`. Rewrite `h2` using `[← h]`. Express the relevant statement in the definitionally equal form `proj _ _ ∈ V at h2`.

Rewrite `h2` using `[proj_univ, constantCoeff_C]`. Conclude with `two_ne_zero (hc 2 h2)`. Set `Q : Z` to `pt _ hQp ((hWV.trans (hVP Finset.univ)).trans hPQ.le)`. Take `⟨l, hl, hlen⟩` from `hchain Finset.univ`. Establish `hlen'` using `Order.LTSeries.length_le_krullDim (l.snoc Q (by`.

Rewrite using `[hl]`. Conclude with `pt_lt _ _ (hPp _) hQp (hWV.trans (hVP _)) ((hWV.trans (hVP Finset.univ)).trans hPQ.le) hPQ))`. Express the relevant statement in the definitionally equal form `((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ _ at hlen'`. Rewrite `hlen'` using `[hlen, Finset.card_univ, ← ringKrullDim_quotient, hdim]`. Establish `: Fintype.card K + 1 + 1 ≤ 1 + Fintype.card K` using `by exact_mod_cast hlen'`.

Use linear arithmetic over natural numbers and integers.
-/
theorem CurveDivVertical.full : CurveDivVertical.Statement := by
  classical
  intro K _ ι _ W s a hW hs hsW V hV hhor
  obtain ⟨_, ⟨hWp, hWh, -⟩, -, hdim⟩ := hW
  obtain ⟨hVmin', hVrel⟩ := hV
  have hVmin : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ W ⊔ Ideal.span {s} ≤ q) V := hVmin'
  have hVp : V.IsPrime := hVmin.prop.1
  have hWV : W ≤ V := le_trans le_sup_left hVmin.prop.2
  have hsV : s ∈ V := hVmin.prop.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))

  have hproj : ∀ (T : Finset K) f, f ∈ V → proj T f ∈ V := by
    intro T f hf
    rw [proj_apply]
    exact weightedHomogeneousComponent_mem_of_mem ℤ (wt T)
      (isHomogeneous_of_mem_minimalPrimes T (isHomogeneous_sup T hWh hs) hVmin') hf 0

  let Z := PrimeSpectrum.zeroLocus (R := MRing ι) (W : Set (MRing ι))
  let pt : (I : Ideal (MRing ι)) → I.IsPrime → W ≤ I → Z := fun I hI hWI ↦
    ⟨⟨I, hI⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hWI⟩
  have pt_lt : ∀ (I J : Ideal (MRing ι)) hI hJ hWI hWJ, I < J → pt I hI hWI < pt J hJ hWJ :=
    fun _ _ _ _ _ _ h ↦ h
  have hPp : ∀ T : Finset K, (V.comap (proj T)).IsPrime := fun T ↦ hVp.comap _
  have hVP : ∀ T : Finset K, V ≤ V.comap (proj T) := fun T f hf ↦ hproj T f hf
  let P : Finset K → Z := fun T ↦ pt _ (hPp T) (hWV.trans (hVP T))

  have hstep : ∀ (T : Finset K) (k : K), k ∉ T → P T < P (insert k T) := by
    intro T k hk
    suffices key : V.comap (proj T) < V.comap (proj (insert k T)) from
      pt_lt _ _ (hPp T) (hPp _) (hWV.trans (hVP T)) (hWV.trans (hVP _)) key
    refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
    · change proj _ f ∈ V
      rw [← proj_proj (Finset.subset_insert k T)]
      exact hproj _ _ hf
    · obtain ⟨i, hi⟩ := hVrel k
      have h1 : (X ⟨k, i⟩ : MRing ι) ∈ V.comap (proj (insert k T)) := by
        change proj _ _ ∈ V
        rw [proj_X_of_mem (Finset.mem_insert_self k T)]
        exact V.zero_mem
      rw [← h] at h1
      change proj _ _ ∈ V at h1
      rw [proj_X_of_notMem hk] at h1
      exact hi h1
  have hbot : pt W hWp le_rfl < P ∅ := by
    suffices key : W < V.comap (proj ∅) from
      pt_lt _ _ hWp (hPp ∅) le_rfl (hWV.trans (hVP ∅)) key
    refine lt_of_le_of_ne (hWV.trans (hVP ∅)) fun h ↦ hsW ?_
    rw [h]
    change proj ∅ s ∈ V
    rw [proj_empty]
    exact hsV
  have hchain : ∀ T : Finset K, ∃ l : LTSeries Z, l.last = P T ∧ l.length = T.card + 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨(RelSeries.singleton _ (pt W hWp le_rfl)).snoc (P ∅) hbot, RelSeries.last_snoc _ _ _, rfl⟩
    | insert k T hk ih =>
      obtain ⟨l, hl, hlen⟩ := ih
      refine ⟨l.snoc (P (insert k T)) (hl ▸ hstep T k hk), RelSeries.last_snoc _ _ _, ?_⟩
      show l.length + 1 = _
      rw [hlen, Finset.card_insert_of_notMem hk]

  have hQp : (Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)})).IsPrime :=
    ((Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two).comap _
  have hPQ : V.comap (proj Finset.univ) <
      Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)}) := by
    have hc : ∀ c : ℤ, C c ∈ V → c = 0 := fun c hc ↦ by
      have : c ∈ V.comap (C : ℤ →+* MRing ι) := hc
      rw [hhor] at this
      exact this
    refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
    · change proj _ f ∈ V at hf
      rw [proj_univ] at hf
      rw [Ideal.mem_comap, hc _ hf]
      exact Ideal.zero_mem _
    · have h2 : (C 2 : MRing ι) ∈ Ideal.comap (constantCoeff : MRing ι →+* ℤ)
          (Ideal.span {(2 : ℤ)}) := by
        rw [Ideal.mem_comap, constantCoeff_C]
        exact Ideal.mem_span_singleton_self 2
      rw [← h] at h2
      change proj _ _ ∈ V at h2
      rw [proj_univ, constantCoeff_C] at h2
      exact two_ne_zero (hc 2 h2)
  let Q : Z := pt _ hQp ((hWV.trans (hVP Finset.univ)).trans hPQ.le)
  obtain ⟨l, hl, hlen⟩ := hchain Finset.univ
  have hlen' := Order.LTSeries.length_le_krullDim (l.snoc Q (by
    rw [hl]
    exact pt_lt _ _ (hPp _) hQp (hWV.trans (hVP _)) ((hWV.trans (hVP Finset.univ)).trans hPQ.le) hPQ))
  change ((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ _ at hlen'
  rw [hlen, Finset.card_univ, ← ringKrullDim_quotient, hdim] at hlen'
  have : Fintype.card K + 1 + 1 ≤ 1 + Fintype.card K := by exact_mod_cast hlen'
  omega

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
