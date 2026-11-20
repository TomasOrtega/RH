import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  midDeg midVar joinCoord_midVar)

namespace FlagPairJoinRight

section Charts

variable {Ω : Type*} [Field Ω] {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂]
  {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def midChart (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => s (.inl k)
  | .inr k => s (.inr (.inr k))

def wChart (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) : ∀ k, ι₂ k :=
  fun k => s (.inr (.inl k))

def extChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k
  | .inl k => t (.inl k)
  | .inr (.inl k) => u k
  | .inr (.inr k) => t (.inr k)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply the tactic sequence `rcases k with k | k <;> rfl`.
-/
theorem midChart_extChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    midChart (extChart t u) = t := by
  funext k
  rcases k with k | k <;> rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wChart_extChart (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    wChart (extChart (ι₂ := ι₂) t u) = u :=
  rfl

/- English proof (translation)
Simplify using `only [mseg, Fintype.prod_sum_type]`. Simplify using `only [joinCoord, midChart, wChart]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mseg_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    mseg (joinCoord x (joinCoord w z)) s = mseg (joinCoord x z) (midChart s) * mseg w (wChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp only [joinCoord, midChart, wChart]
  ring

/- English proof (translation)
Simplify using `only [chartMon, Fintype.prod_sum_type]`. Simplify using `[joinCoord, midChart, midDeg]`.
-/
theorem chartMon_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) (a : K ⊕ K' → ℤ) :
    chartMon (joinCoord x (joinCoord w z)) s (midDeg (K₂ := K₂) a) =
      chartMon (joinCoord x z) (midChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, midChart, midDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

/- English proof (translation)
Establish `hw : mseg w (wChart s) ≠ 0`. Rewrite `hs` using `[mseg_mid]`. Conclude with `right_ne_zero_of_mul hs`. Unfold `chartRing`. Apply `Algebra.adjoin_le` to reduce the goal to its premises.

Introduce and unpack `_ ⟨t', rfl⟩`. Establish `h : mseg (joinCoord x z) t' / mseg (joinCoord x z) (midChart s) = mseg (joinCoord x (joinCoord w z)) (extChart t' (wChart s)) / mseg (joinCoord x (joinCoord w z)) s`. Rewrite using `[mseg_mid x z w (extChart t' (wChart s)), mseg_mid x z w s, midChart_extChart, wChart_extChart, mul_div_mul_right _ _ hw]`. Simplify using `only`. Rewrite using `[h]`.

Conclude with `div_mem_chartRing (o := O) _ _ _`.
-/
theorem chartRing_le_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    chartRing O (mseg (joinCoord x z)) (midChart s) ≤ chartRing O (mseg (joinCoord x (joinCoord w z))) s := by
  have hw : mseg w (wChart s) ≠ 0 := by
    rw [mseg_mid] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg (joinCoord x z) t' / mseg (joinCoord x z) (midChart s) =
      mseg (joinCoord x (joinCoord w z)) (extChart t' (wChart s)) /
        mseg (joinCoord x (joinCoord w z)) s := by
    rw [mseg_mid x z w (extChart t' (wChart s)), mseg_mid x z w s, midChart_extChart, wChart_extChart,
      mul_div_mul_right _ _ hw]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

end Charts

section Forms

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

/- English proof (translation)
Rewrite using `[aeval_rename]`. Conclude with `congrArg (fun y => aeval y p) (funext (joinCoord_midVar x z w))`.
-/
theorem aeval_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (p : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) :
    aeval (joinCoord x (joinCoord w z)) (rename (midVar ι₂) p) = aeval (joinCoord x z) p := by
  rw [aeval_rename]
  exact congrArg (fun y => aeval y p) (funext (joinCoord_midVar x z w))

/- English proof (translation)
Use function extensionality and compare the values at `k`. Apply the tactic sequence `rcases k with k | k | k <;> simp [midDeg]`.
-/
theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end Forms

section Frames

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂] {ι : K → Type} {ι' : K' → Type}
  {ι₂ : K₂ → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] [∀ k, Fintype (ι₂ k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

/- English proof (translation)
Establish `hsF : mseg (joinCoord x z) (midChart s) ≠ 0`. Rewrite `hs` using `[mseg_mid]`. Conclude with `left_ne_zero_of_mul hs`. Rewrite using `[hF _ hsF, hB s hs]`. Apply `AddSubgroup.closure_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Conclude with `⟨a, chartRing_le_mid O x z w s hs ha, e, he, rfl⟩`.
-/
theorem lat_le_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V} (hF : IsPull O x z E EF)
    (hB : IsPull O x (joinCoord w z) E EB) (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    EF.lat (midChart s) ≤ EB.lat s := by
  have hsF : mseg (joinCoord x z) (midChart s) ≠ 0 := by
    rw [mseg_mid] at hs
    exact left_ne_zero_of_mul hs
  rw [hF _ hsF, hB s hs]
  apply AddSubgroup.closure_mono
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, chartRing_le_mid O x z w s hs ha, e, he, rfl⟩

/- English proof (translation)
Introduce `s hs`. Establish `hsF : mseg (joinCoord x z) (midChart s) ≠ 0`. Rewrite `hs` using `[mseg_mid]`. Conclude with `left_ne_zero_of_mul hs`. Establish `hle` using `chartRing_le_mid O x z w s hs`.

Establish `hlat` using `lat_le_mid O x z w hF hB s hs`. Take `⟨k, f, c, hf, hc, hsum, hl⟩` from `h _ hsF`. Use `⟨k, f, c, fun l => hle (hf l), fun l => hle (hc l), hsum, fun l => ?_⟩` and prove the remaining obligations. Take `⟨b, hli, hspan, hiff, hw⟩` from `hl l`. Establish `hfR : f l ∈ chartRing O (mseg (joinCoord x (joinCoord w z))) s` using `hle (hf l)`.

Use `⟨b, hli, hspan, fun e => ⟨?_, ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨n, hn⟩`. Distinguish the cases in `h0 : f l = 0`. Take `⟨a, ha, he⟩` from `(hiff e).mp ⟨1, by rw [h0, pow_one, zero_smul]; exact zero_mem _⟩`. Conclude with `⟨a, fun q => (ha q).imp fun _ hk => hle hk, he⟩`.

Establish `key : ∀ v ∈ EB.lat s, ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O (mseg (joinCoord x (joinCoord w z))) s) ∧ v = ∑ q, a q • b q`. Introduce `v hv`. Rewrite `hv` using `[hB s hs]`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem v hv`.

Take `⟨c', hc', e', he', rfl⟩` from `hv`. Establish `he'F : e' ∈ EF.lat (midChart s)`. Rewrite using `[hF _ hsF]`. Conclude with `AddSubgroup.subset_closure ⟨1, one_mem _, e', he', (one_smul _ _).symm⟩`. Take `⟨a, ha, rfl⟩` from `(hiff e').mp ⟨0, by rwa [pow_zero, one_smul]⟩`.

Use `⟨fun q => c' * a q, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem hc' (hle hn)`.

Rewrite using `[Finset.smul_sum]`. Simplify using `only [smul_smul]`. Consider the case `zero => exact ⟨0, fun _ => ⟨0, by simp⟩, by simp⟩`. Consider the case `add v v' _ _ hv hv'`. Take `⟨a, ha, rfl⟩` from `hv`.

Take `⟨a', ha', rfl⟩` from `hv'`. Use `⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩` and prove the remaining obligations. Take `⟨n₁, h₁⟩` from `ha q`. Take `⟨n₂, h₂⟩` from `ha' q`. Use `⟨n₁ + n₂, ?_⟩` and prove the remaining obligations.

Establish `h12 : f l ^ (n₁ + n₂) * (a + a') q = f l ^ n₂ * (f l ^ n₁ * a q) + f l ^ n₁ * (f l ^ n₂ * a' q)`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h12]`. Conclude with `add_mem (mul_mem (pow_mem hfR _) h₁) (mul_mem (pow_mem hfR _) h₂)`.

Consider the case `neg v _ hv`. Take `⟨a, ha, rfl⟩` from `hv`. Use `⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`. Conclude with `⟨n, by simpa [mul_neg] using neg_mem hn⟩`.

Take `⟨a, ha, he⟩` from `key _ hn`. Establish `hfn : f l ^ n ≠ 0` using `pow_ne_zero _ h0`. Use `⟨fun q => (f l ^ n)⁻¹ * a q, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k', hk'⟩` from `ha q`. Use `⟨k' + n, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_add, mul_assoc, ← mul_assoc (f l ^ n), mul_inv_cancel₀ hfn, one_mul]`. Conclude with `hk'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[he, Finset.smul_sum]`. Simplify using `only [smul_smul]`.

Introduce and unpack `⟨a, ha, rfl⟩`. Establish `hb : ∀ q, ∃ n : ℕ, f l ^ n • b q ∈ EB.lat s`. Introduce `q`. Establish `h1 : ∀ q', ∃ n : ℕ, f l ^ n * (Pi.single q (1 : Ω) : Fin N → Ω) q' ∈ chartRing O (mseg (joinCoord x z)) (midChart s)`. Introduce `q'`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : q' = q`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hq]`.

Establish `h2 : b q = ∑ q', (Pi.single q (1 : Ω) : Fin N → Ω) q' • b q'`. Simplify using `[Pi.single_apply]`. Take `⟨n, hn⟩` from `(hiff (b q)).mpr ⟨Pi.single q 1, h1, h2⟩`. Conclude with `⟨n, hlat hn⟩`. Use `choose nb hnb using hb`.

Use `choose na hna using ha`. Use `⟨∑ q, (na q + nb q), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Establish `hq : na q + nb q ≤ ∑ q, (na q + nb q)` using `Finset.single_le_sum (f := fun q => na q + nb q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)`.

Establish `hpow : f l ^ (∑ q, (na q + nb q)) = f l ^ (∑ q, (na q + nb q) - (na q + nb q)) * f l ^ na q * f l ^ nb q`. Rewrite using `[mul_assoc, ← pow_add, ← pow_add, Nat.sub_add_cancel hq]`. Establish `heq : f l ^ (∑ q, (na q + nb q)) • (a q • b q) = (f l ^ (∑ q, (na q + nb q) - (na q + nb q)) * (f l ^ na q * a q)) • (f l ^ nb q • b q)`. Rewrite using `[smul_smul, smul_smul, hpow]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `EB.stable s _ (mul_mem (pow_mem hfR _) (hna q)) _ (hnb q)`. Take `⟨u, ⟨hu0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩` from `hw i`. Use `⟨u, ⟨hu0, ⟨n₁, hle hn₁⟩, ⟨n₂, hle hn₂⟩⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[chartMon_mid]`. Conclude with `hmem`.
-/
theorem isGradedFrame_mid (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V} (hF : IsPull O x z E EF)
    (hB : IsPull O x (joinCoord w z) E EB) {Vs : Fin (N + 1) → Submodule Ω V} {m : Fin N → K ⊕ K' → ℤ}
    {gen : Fin N → V} (h : IsGradedFrame O (joinCoord x z) EF Vs m gen) :
    IsGradedFrame O (joinCoord x (joinCoord w z)) EB Vs (fun i => midDeg (K₂ := K₂) (m i)) gen := by
  intro s hs
  have hsF : mseg (joinCoord x z) (midChart s) ≠ 0 := by
    rw [mseg_mid] at hs
    exact left_ne_zero_of_mul hs
  have hle := chartRing_le_mid O x z w s hs
  have hlat := lat_le_mid O x z w hF hB s hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ hsF
  refine ⟨k, f, c, fun l => hle (hf l), fun l => hle (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hw⟩ := hl l
  have hfR : f l ∈ chartRing O (mseg (joinCoord x (joinCoord w z))) s := hle (hf l)
  refine ⟨b, hli, hspan, fun e => ⟨?_, ?_⟩, fun i => ?_⟩
  · rintro ⟨n, hn⟩
    by_cases h0 : f l = 0
    · obtain ⟨a, ha, he⟩ := (hiff e).mp ⟨1, by rw [h0, pow_one, zero_smul]; exact zero_mem _⟩
      exact ⟨a, fun q => (ha q).imp fun _ hk => hle hk, he⟩
    have key : ∀ v ∈ EB.lat s, ∃ a : Fin N → Ω,
        (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O (mseg (joinCoord x (joinCoord w z))) s) ∧
          v = ∑ q, a q • b q := by
      intro v hv
      rw [hB s hs] at hv
      induction hv using AddSubgroup.closure_induction with
      | mem v hv =>
        obtain ⟨c', hc', e', he', rfl⟩ := hv
        have he'F : e' ∈ EF.lat (midChart s) := by
          rw [hF _ hsF]
          exact AddSubgroup.subset_closure ⟨1, one_mem _, e', he', (one_smul _ _).symm⟩
        obtain ⟨a, ha, rfl⟩ := (hiff e').mp ⟨0, by rwa [pow_zero, one_smul]⟩
        refine ⟨fun q => c' * a q, fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := ha q
          refine ⟨n, ?_⟩
          rw [mul_left_comm]
          exact mul_mem hc' (hle hn)
        · rw [Finset.smul_sum]
          simp only [smul_smul]
      | zero => exact ⟨0, fun _ => ⟨0, by simp⟩, by simp⟩
      | add v v' _ _ hv hv' =>
        obtain ⟨a, ha, rfl⟩ := hv
        obtain ⟨a', ha', rfl⟩ := hv'
        refine ⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
        obtain ⟨n₁, h₁⟩ := ha q
        obtain ⟨n₂, h₂⟩ := ha' q
        refine ⟨n₁ + n₂, ?_⟩
        have h12 : f l ^ (n₁ + n₂) * (a + a') q =
            f l ^ n₂ * (f l ^ n₁ * a q) + f l ^ n₁ * (f l ^ n₂ * a' q) := by
          simp only [Pi.add_apply]
          ring
        rw [h12]
        exact add_mem (mul_mem (pow_mem hfR _) h₁) (mul_mem (pow_mem hfR _) h₂)
      | neg v _ hv =>
        obtain ⟨a, ha, rfl⟩ := hv
        refine ⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by simpa [mul_neg] using neg_mem hn⟩
    obtain ⟨a, ha, he⟩ := key _ hn
    have hfn : f l ^ n ≠ 0 := pow_ne_zero _ h0
    refine ⟨fun q => (f l ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨k', hk'⟩ := ha q
      refine ⟨k' + n, ?_⟩
      rw [pow_add, mul_assoc, ← mul_assoc (f l ^ n), mul_inv_cancel₀ hfn, one_mul]
      exact hk'
    · calc e = (f l ^ n)⁻¹ • (f l ^ n • e) := by rw [smul_smul, inv_mul_cancel₀ hfn, one_smul]
        _ = _ := by
          rw [he, Finset.smul_sum]
          simp only [smul_smul]
  · rintro ⟨a, ha, rfl⟩
    have hb : ∀ q, ∃ n : ℕ, f l ^ n • b q ∈ EB.lat s := by
      intro q
      have h1 : ∀ q', ∃ n : ℕ, f l ^ n * (Pi.single q (1 : Ω) : Fin N → Ω) q' ∈
          chartRing O (mseg (joinCoord x z)) (midChart s) := by
        intro q'
        refine ⟨0, ?_⟩
        by_cases hq : q' = q
        · subst hq
          simp
        · simp [hq]
      have h2 : b q = ∑ q', (Pi.single q (1 : Ω) : Fin N → Ω) q' • b q' := by
        simp [Pi.single_apply]
      obtain ⟨n, hn⟩ := (hiff (b q)).mpr ⟨Pi.single q 1, h1, h2⟩
      exact ⟨n, hlat hn⟩
    choose nb hnb using hb
    choose na hna using ha
    refine ⟨∑ q, (na q + nb q), ?_⟩
    rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun q _ => ?_
    have hq : na q + nb q ≤ ∑ q, (na q + nb q) :=
      Finset.single_le_sum (f := fun q => na q + nb q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have hpow : f l ^ (∑ q, (na q + nb q)) =
        f l ^ (∑ q, (na q + nb q) - (na q + nb q)) * f l ^ na q * f l ^ nb q := by
      rw [mul_assoc, ← pow_add, ← pow_add, Nat.sub_add_cancel hq]
    have heq : f l ^ (∑ q, (na q + nb q)) • (a q • b q) =
        (f l ^ (∑ q, (na q + nb q) - (na q + nb q)) * (f l ^ na q * a q)) • (f l ^ nb q • b q) := by
      rw [smul_smul, smul_smul, hpow]
      congr 1
      ring
    rw [heq]
    exact EB.stable s _ (mul_mem (pow_mem hfR _) (hna q)) _ (hnb q)
  · obtain ⟨u, ⟨hu0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hw i
    refine ⟨u, ⟨hu0, ⟨n₁, hle hn₁⟩, ⟨n₂, hle hn₂⟩⟩, ?_⟩
    dsimp only
    rw [chartMon_mid]
    exact hmem

end Frames

end FlagPairJoinRight

open FlagPairJoinRight in

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w N V _ _ E E' EF E'F hp hp' φ EB E'B hB hB'`. Use `⟨{ Vs := φ.Vs mono := φ.mono dim := φ.dim top := φ.top deg := fun i => midDeg (K₂ := K₂) (φ.deg i) gen := φ.gen gen_mem := φ.gen_mem frame := isGradedFrame_mid O x z w hp hB φ.frame deg' := fun i => midDeg (K₂ := K₂) (φ.deg' i) gen' := φ.gen' gen'_mem := φ.gen'_mem frame' := isGr …` and prove the remaining obligations. Simplify using `only [aeval_mid]`. Conclude with `φ.rel i`. Use `vert := fun i => by`.

Simplify using `only [midDeg_sub]`. Conclude with `hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (φ.vert i) }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩`.
-/
theorem FlagPairJoinRight.proof (hVert : JoinVerticalDivisorRight.Statement) :
    FlagPairJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w N V _ _ E E' EF E'F hp hp' φ EB E'B hB hB'
  refine ⟨{
    Vs := φ.Vs
    mono := φ.mono
    dim := φ.dim
    top := φ.top
    deg := fun i => midDeg (K₂ := K₂) (φ.deg i)
    gen := φ.gen
    gen_mem := φ.gen_mem
    frame := isGradedFrame_mid O x z w hp hB φ.frame
    deg' := fun i => midDeg (K₂ := K₂) (φ.deg' i)
    gen' := φ.gen'
    gen'_mem := φ.gen'_mem
    frame' := isGradedFrame_mid O x z w hp' hB' φ.frame'
    f := fun i => rename (midVar ι₂) (φ.f i)
    g := fun i => rename (midVar ι₂) (φ.g i)
    rel := fun i => by
      simp only [aeval_mid]
      exact φ.rel i
    vert := fun i => by
      simp only [midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (φ.vert i) }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
