import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumberFieldPrimeZetaSumAddLogIsBigO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNorm
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
open Filter Topology Asymptotics
open scoped Pointwise

namespace GlobalTheory.Bauer

/- English proof (translation)
Establish `: Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Conclude with `Nat.one_le_iff_ne_zero.mpr this` after adjusting the coercions.
-/
theorem one_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

/- English proof (translation)
Introduce `h`. Use `choose P P' hne hP hP' hN hN' using h`. Establish `huniq : ∀ (Q : HeightOneSpectrum (𝓞 M)) (v w : HeightOneSpectrum (𝓞 K)), Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w`. Introduce `Q v w hv hw`. Conclude with `HeightOneSpectrum.ext (hv.over.trans hw.over.symm)`.

Set `i : (Sᶜ : Set _) ⊕ (Sᶜ : Set _) → HeightOneSpectrum (𝓞 M)` to `Sum.elim (fun v => P v.1 v.2) (fun v => P' v.1 v.2)`. Establish `hi : Function.Injective i`. Introduce and unpack `(⟨v, hv⟩ | ⟨v, hv⟩) (⟨w, hw⟩ | ⟨w, hw⟩) e`. Establish `e' : P v hv = P w hw` using `e`. Use `huniq _ v w (hP v hv) (e' ▸ hP w hw)` as an intermediate fact.

Substitute `this` using the available equality. Both sides reduce to the same expression. Establish `e' : P v hv = P' w hw` using `e`. Use `huniq _ v w (hP v hv) (e' ▸ hP' w hw)` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `absurd e' (hne v hv)`. Establish `e' : P' v hv = P w hw` using `e`. Use `huniq _ v w (hP' v hv) (e' ▸ hP w hw)` as an intermediate fact. Substitute `this` using the available equality. Conclude with `absurd e'.symm (hne v hv)`.

Establish `e' : P' v hv = P' w hw` using `e`. Use `huniq _ v w (hP' v hv) (e' ▸ hP' w hw)` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression. Use `set c : ℝ := ∑' v : S, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ)⁻¹ with hc`.

Establish `key : ∀ s : ℝ, 1 < s → 2 * ((∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) - c) ≤ ∑' Q : HeightOneSpectrum (𝓞 M), ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ) ^ (-s)`. Introduce `s hs`. Establish `hf` using `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2`. Establish `hg` using `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow M).2 s hs).2`. Establish `h0` using `hf.tsum_subtype_add_tsum_subtype_compl S`.

Establish `h1 : ∑' v : S, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s) ≤ c`. Use `(hf.subtype S).tsum_le_tsum (fun v => ?_) hS` and prove the remaining obligations. Rewrite using `[← Real.rpow_neg_one]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (one_le_absNorm _) (by linarith)`. Establish `hT` using `(hf.subtype (Sᶜ : Set _)).hasSum`.

Establish `hsum : HasSum ((fun Q : HeightOneSpectrum (𝓞 M) => ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ) ^ (-s)) ∘ i) ((∑' v : (Sᶜ : Set _), ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s)) + ∑' v : (Sᶜ : Set _), ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s))`. Apply `HasSum.sum` to reduce the goal to its premises. Use `hT.congr_fun ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Use `show ((Ideal.absNorm (P v hv).asIdeal : ℕ) : ℝ) ^ (-s) = _`.

Rewrite using `[hN v hv]`. Both sides reduce to the same expression. Use `hT.congr_fun ?_` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Use `show ((Ideal.absNorm (P' v hv).asIdeal : ℕ) : ℝ) ^ (-s) = _`.

Rewrite using `[hN' v hv]`. Both sides reduce to the same expression. Establish `hle` using `tsum_comp_le_tsum_of_inj hg (fun _ => by positivity) hi`. Rewrite `hle` using `[hsum.tsum_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨C, hC⟩` from `(GlobalTheory.ChebCyc.primeSum_add_log_isBigO K).bound`. Take `⟨D, hD⟩` from `(GlobalTheory.ChebCyc.primeSum_add_log_isBigO M).bound`. Establish `hlog : Tendsto (fun s : ℝ => Real.log (s - 1)) (𝓝[>] 1) atBot`. Use `Real.tendsto_log_nhdsGT_zero.comp ?_` and prove the remaining obligations. Apply `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` to reduce the goal to its premises.

Establish `: Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1))` using `(continuous_id.sub continuous_const).tendsto 1`. Rewrite `this` using `[sub_self]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Simplify using `using hs`.

Establish `hev` using `hlog.eventually_lt_atBot (-(2 * C + D + 2 * c))`. Establish `: ∀ᶠ s : ℝ in 𝓝[>] 1, False` using `by filter_upwards [hC, hD, hev, self_mem_nhdsWithin] with s h1 h2 h3 hs`. Establish `h4` using `key s hs`. Rewrite `h1`, `h2` using `[norm_one, mul_one, Real.norm_eq_abs, abs_le]`. Combine the linear relations using `[h1.1, h2.2]`.

Conclude with `this.exists.elim fun _ h => h`.
-/
theorem not_forall_two_liesOver (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : Summable fun v : S => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ)⁻¹) :
    ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧
      P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro h
  choose P P' hne hP hP' hN hN' using h
  have huniq : ∀ (Q : HeightOneSpectrum (𝓞 M)) (v w : HeightOneSpectrum (𝓞 K)),
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w := by
    intro Q v w hv hw
    exact HeightOneSpectrum.ext (hv.over.trans hw.over.symm)
  let i : (Sᶜ : Set _) ⊕ (Sᶜ : Set _) → HeightOneSpectrum (𝓞 M) :=
    Sum.elim (fun v => P v.1 v.2) (fun v => P' v.1 v.2)
  have hi : Function.Injective i := by
    rintro (⟨v, hv⟩ | ⟨v, hv⟩) (⟨w, hw⟩ | ⟨w, hw⟩) e
    · have e' : P v hv = P w hw := e
      have := huniq _ v w (hP v hv) (e' ▸ hP w hw)
      subst this; rfl
    · have e' : P v hv = P' w hw := e
      have := huniq _ v w (hP v hv) (e' ▸ hP' w hw)
      subst this; exact absurd e' (hne v hv)
    · have e' : P' v hv = P w hw := e
      have := huniq _ v w (hP' v hv) (e' ▸ hP w hw)
      subst this; exact absurd e'.symm (hne v hv)
    · have e' : P' v hv = P' w hw := e
      have := huniq _ v w (hP' v hv) (e' ▸ hP' w hw)
      subst this; rfl
  set c : ℝ := ∑' v : S, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ)⁻¹ with hc
  have key : ∀ s : ℝ, 1 < s →
      2 * ((∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) - c) ≤
        ∑' Q : HeightOneSpectrum (𝓞 M), ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ) ^ (-s) := by
    intro s hs
    have hf := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2
    have hg := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow M).2 s hs).2
    have h0 := hf.tsum_subtype_add_tsum_subtype_compl S
    have h1 : ∑' v : S, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s) ≤ c := by
      refine (hf.subtype S).tsum_le_tsum (fun v => ?_) hS
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_absNorm _) (by linarith)
    have hT := (hf.subtype (Sᶜ : Set _)).hasSum
    have hsum : HasSum ((fun Q : HeightOneSpectrum (𝓞 M) =>
        ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ) ^ (-s)) ∘ i)
        ((∑' v : (Sᶜ : Set _), ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s)) +
          ∑' v : (Sᶜ : Set _), ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s)) := by
      apply HasSum.sum
      · refine hT.congr_fun ?_
        rintro ⟨v, hv⟩
        show ((Ideal.absNorm (P v hv).asIdeal : ℕ) : ℝ) ^ (-s) = _
        rw [hN v hv]; rfl
      · refine hT.congr_fun ?_
        rintro ⟨v, hv⟩
        show ((Ideal.absNorm (P' v hv).asIdeal : ℕ) : ℝ) ^ (-s) = _
        rw [hN' v hv]; rfl
    have hle := tsum_comp_le_tsum_of_inj hg (fun _ => by positivity) hi
    rw [hsum.tsum_eq] at hle
    linarith
  obtain ⟨C, hC⟩ := (GlobalTheory.ChebCyc.primeSum_add_log_isBigO K).bound
  obtain ⟨D, hD⟩ := (GlobalTheory.ChebCyc.primeSum_add_log_isBigO M).bound
  have hlog : Tendsto (fun s : ℝ => Real.log (s - 1)) (𝓝[>] 1) atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hev := hlog.eventually_lt_atBot (-(2 * C + D + 2 * c))
  have : ∀ᶠ s : ℝ in 𝓝[>] 1, False := by
    filter_upwards [hC, hD, hev, self_mem_nhdsWithin] with s h1 h2 h3 hs
    have h4 := key s hs
    rw [norm_one, mul_one, Real.norm_eq_abs, abs_le] at h1 h2
    linarith [h1.1, h2.2]
  exact this.exists.elim fun _ h => h

/- English proof (translation)
Use `set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹`. Establish `f0 : ∀ v, 0 ≤ f v` using `fun v => by positivity`. Establish `h1 : Summable (S.indicator f)` using `summable_subtype_iff_indicator.1 (hS.summable f)`. Establish `h2 : Summable (Set.indicator {v | ¬ (Ideal.absNorm v.asIdeal).Prime} f)` using `summable_subtype_iff_indicator.1 (GlobalTheory.summable_inv_absNorm_of_not_prime K)`. Use `(summable_subtype_iff_indicator (f := f)).2 ?_` and prove the remaining obligations.

Use `Summable.of_nonneg_of_le (fun v => Set.indicator_nonneg (fun v _ => f0 v) v) (fun v => ?_) (h1.add h2)` and prove the remaining obligations. Use `f0 v` as an intermediate fact. Apply the tactic sequence `by_cases a : v ∈ S <;> by_cases b : (Ideal.absNorm v.asIdeal).Prime <;>`. Simplify using `[Set.indicator, a, b, this]`.
-/
theorem summable_finite_union_not_prime (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Summable fun v : (S ∪ {v | ¬ (Ideal.absNorm v.asIdeal).Prime} : Set _) =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹
  have f0 : ∀ v, 0 ≤ f v := fun v => by positivity
  have h1 : Summable (S.indicator f) := summable_subtype_iff_indicator.1 (hS.summable f)
  have h2 : Summable (Set.indicator {v | ¬ (Ideal.absNorm v.asIdeal).Prime} f) :=
    summable_subtype_iff_indicator.1 (GlobalTheory.summable_inv_absNorm_of_not_prime K)
  refine (summable_subtype_iff_indicator (f := f)).2 ?_
  refine Summable.of_nonneg_of_le (fun v => Set.indicator_nonneg (fun v _ => f0 v) v)
    (fun v => ?_) (h1.add h2)
  have := f0 v
  by_cases a : v ∈ S <;> by_cases b : (Ideal.absNorm v.asIdeal).Prime <;>
    simp [Set.indicator, a, b, this]

/- English proof (translation)
Use `haveI : IsGalois M N := IsGalois.tower_top_of_isGalois K M N`. Use `haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP`. Establish `h1` using `Ideal.card_stabilizer_eq (G := N ≃ₐ[K] N) (P.under (𝓞 K)) P`. Establish `h2` using `Ideal.card_stabilizer_eq (G := N ≃ₐ[M] N) (P.under (𝓞 M)) P`. Rewrite `h1` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[K] N), Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[K] N), Ideal.ramificationIdx_tower (P.under (𝓞 M)) P, Ideal.inertiaDeg_tower (P.under (𝓞 M)) P]`.

Rewrite `h2` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[M] N), Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[M] N)]`. Establish `h3 : Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P) = ((P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K)) * Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P)`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Set `j : MulAction.stabilizer (N ≃ₐ[M] N) P → MulAction.stabilizer (N ≃ₐ[K] N) P` to `fun σ => ⟨σ.1.restrictScalars K, σ.2⟩`.

Establish `hj : Function.Injective j`. Introduce `a b e`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `AlgEquiv.restrictScalars_injective K (congrArg Subtype.val e)`. Establish `hpos : 0 < Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P)` using `Nat.card_pos`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hs : Function.Surjective j`. Introduce and unpack `⟨σ, hσ⟩`. Conclude with `⟨⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (h σ hσ), hσ⟩, rfl⟩`.

Use `Nat.card_eq_of_bijective j ⟨hj, hs⟩` as an intermediate fact. Rewrite `this` using `[h3]`. Conclude with `(Nat.eq_of_mul_eq_mul_right hpos (by rw [← this, one_mul])).symm`. Introduce `h σ hσ x`. Rewrite `h3` using `[h, one_mul]`.

Establish `hb` using `(Nat.bijective_iff_injective_and_card j).2 ⟨hj, h3.symm⟩`. Take `⟨τ, hτ⟩` from `hb.2 ⟨σ, hσ⟩`. Establish `: σ = τ.1.restrictScalars K` using `(congrArg Subtype.val hτ).symm`. Rewrite using `[this]`. Conclude with `τ.1.commutes x`.
-/
theorem stabilizer_fixes_iff (K M N : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Field N] [NumberField N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]
    [IsGalois K N] (P : Ideal (𝓞 N)) [P.IsPrime] (hP : P ≠ ⊥) :
    (∀ σ : N ≃ₐ[K] N, σ • P = P → ∀ x : M, σ (algebraMap M N x) = algebraMap M N x) ↔
      (P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K) = 1 := by
  haveI : IsGalois M N := IsGalois.tower_top_of_isGalois K M N
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  have h1 := Ideal.card_stabilizer_eq (G := N ≃ₐ[K] N) (P.under (𝓞 K)) P
  have h2 := Ideal.card_stabilizer_eq (G := N ≃ₐ[M] N) (P.under (𝓞 M)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[K] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[K] N),
    Ideal.ramificationIdx_tower (P.under (𝓞 M)) P, Ideal.inertiaDeg_tower (P.under (𝓞 M)) P] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[M] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[M] N)] at h2
  have h3 : Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P) =
      ((P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K)) *
        Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := by
    rw [h1, h2]; ring
  let j : MulAction.stabilizer (N ≃ₐ[M] N) P → MulAction.stabilizer (N ≃ₐ[K] N) P :=
    fun σ => ⟨σ.1.restrictScalars K, σ.2⟩
  have hj : Function.Injective j := by
    intro a b e
    apply Subtype.ext
    exact AlgEquiv.restrictScalars_injective K (congrArg Subtype.val e)
  have hpos : 0 < Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := Nat.card_pos
  constructor
  · intro h
    have hs : Function.Surjective j := by
      rintro ⟨σ, hσ⟩
      exact ⟨⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (h σ hσ), hσ⟩, rfl⟩
    have := Nat.card_eq_of_bijective j ⟨hj, hs⟩
    rw [h3] at this
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← this, one_mul])).symm
  · intro h σ hσ x
    rw [h, one_mul] at h3
    have hb := (Nat.bijective_iff_injective_and_card j).2 ⟨hj, h3.symm⟩
    obtain ⟨τ, hτ⟩ := hb.2 ⟨σ, hσ⟩
    have : σ = τ.1.restrictScalars K := (congrArg Subtype.val hτ).symm
    rw [this]
    exact τ.1.commutes x

/- English proof (translation)
Rewrite using `[← Set.ncard_image_of_injective _ (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]`. Use `congr 1`. Use extensionality with `Q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, rfl⟩`.

Conclude with `⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, h2.over.symm, rfl⟩`.
-/
theorem ncard_eq_ncard_primesOver (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (v : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = v.asIdeal}.ncard =
      (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Set.ncard_image_of_injective _ (f := HeightOneSpectrum.asIdeal)
    (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, h2.over.symm, rfl⟩

/- English proof (translation)
Use `haveI := v.isPrime`. Use `haveI := v.isMaximal`. Use `haveI : Fintype (v.asIdeal.primesOver (𝓞 M)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).fintype`. Establish `h` using `Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 M)`. Establish `h' : Module.finrank (𝓞 K) (𝓞 M) = Module.finrank K M` using `(Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 M) M).symm`.

Establish `h1 : (v.asIdeal.primesOver (𝓞 M)).ncard = ∑ _q : v.asIdeal.primesOver (𝓞 M), 1`. Rewrite using `[Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]`. Rewrite using `[← h', ← h, h1, Finset.sum_eq_sum_iff_of_le]`. Simplify using `only [Finset.mem_univ, forall_true_left, Subtype.forall]`. Conclude with `forall₂_congr fun _ _ => eq_comm`.

Introduce and unpack `⟨Q, hQ, _⟩ -`. Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos Q _) (Ideal.inertiaDeg_pos Q _)`.
-/
theorem ncard_eq_finrank_iff (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ↔
      ∀ Q ∈ v.asIdeal.primesOver (𝓞 M), Q.ramificationIdx (𝓞 K) * Q.inertiaDeg (𝓞 K) = 1 := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Fintype (v.asIdeal.primesOver (𝓞 M)) :=
    (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).fintype
  have h := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 M)
  have h' : Module.finrank (𝓞 K) (𝓞 M) = Module.finrank K M :=
    (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 M) M).symm
  have h1 : (v.asIdeal.primesOver (𝓞 M)).ncard = ∑ _q : v.asIdeal.primesOver (𝓞 M), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  rw [← h', ← h, h1, Finset.sum_eq_sum_iff_of_le]
  · simp only [Finset.mem_univ, forall_true_left, Subtype.forall]
    exact forall₂_congr fun _ _ => eq_comm
  · rintro ⟨Q, hQ, _⟩ -
    exact Nat.mul_pos (Ideal.ramificationIdx_pos Q _) (Ideal.inertiaDeg_pos Q _)

/- English proof (translation)
Set `N` to `IntermediateField.normalClosure K T (AlgebraicClosure T)`. Use `haveI : NumberField N := NumberField.of_module_finite K N`. Use `haveI : IsGalois K N := IsGalois.normalClosure K T (AlgebraicClosure T)`. Use `letI : Algebra R N := ((algebraMap T N).comp (algebraMap R T)).toAlgebra`. Use `letI : Algebra M N := ((algebraMap T N).comp (algebraMap M T)).toAlgebra`.

Use `haveI : IsScalarTower R T N := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower M T N := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower K R N := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply R T N, ← IsScalarTower.algebraMap_apply K R T, ← IsScalarTower.algebraMap_apply K T N]`. Use `haveI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply M T N, ← IsScalarTower.algebraMap_apply K M T, ← IsScalarTower.algebraMap_apply K T N]`. Take `⟨⟨P, hP, hPQ⟩⟩` from `Q.nonempty_primesOver (S := 𝓞 N)`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot hQ P`. Establish `hQP : Q = P.under (𝓞 T)` using `hPQ.over`. Rewrite `hR`, `hM` using `[hQP, Ideal.under_under]`.

Rewrite using `[hQP, ← stabilizer_fixes_iff K T N P hP0]`. Rewrite `hR` using `[← stabilizer_fixes_iff K R N P hP0]`. Rewrite `hM` using `[← stabilizer_fixes_iff K M N P hP0]`. Introduce `σ hσ x`. Use `hgen N ((σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K T N)) (IsScalarTower.toAlgHom K T N) (hR σ hσ) (hM σ hσ)` as an intermediate fact.

Conclude with `DFunLike.congr_fun this x`.
-/
theorem ef_eq_one_of_generate (K R M T : Type) [Field K] [NumberField K] [Field R] [NumberField R]
    [Field M] [NumberField M] [Field T] [NumberField T] [Algebra K R] [Algebra K M] [Algebra K T]
    [Algebra R T] [Algebra M T] [IsScalarTower K R T] [IsScalarTower K M T]
    (hgen : ∀ (N : Type) [Field N] [Algebra K N] (φ ψ : T →ₐ[K] N),
      (∀ x : R, φ (algebraMap R T x) = ψ (algebraMap R T x)) →
      (∀ x : M, φ (algebraMap M T x) = ψ (algebraMap M T x)) → φ = ψ)
    (Q : Ideal (𝓞 T)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hR : (Q.under (𝓞 R)).ramificationIdx (𝓞 K) * (Q.under (𝓞 R)).inertiaDeg (𝓞 K) = 1)
    (hM : (Q.under (𝓞 M)).ramificationIdx (𝓞 K) * (Q.under (𝓞 M)).inertiaDeg (𝓞 K) = 1) :
    Q.ramificationIdx (𝓞 K) * Q.inertiaDeg (𝓞 K) = 1 := by
  let N := IntermediateField.normalClosure K T (AlgebraicClosure T)
  haveI : NumberField N := NumberField.of_module_finite K N
  haveI : IsGalois K N := IsGalois.normalClosure K T (AlgebraicClosure T)
  letI : Algebra R N := ((algebraMap T N).comp (algebraMap R T)).toAlgebra
  letI : Algebra M N := ((algebraMap T N).comp (algebraMap M T)).toAlgebra
  haveI : IsScalarTower R T N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower M T N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K R N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R T N, ← IsScalarTower.algebraMap_apply K R T,
      ← IsScalarTower.algebraMap_apply K T N]
  haveI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply M T N, ← IsScalarTower.algebraMap_apply K M T,
      ← IsScalarTower.algebraMap_apply K T N]
  obtain ⟨⟨P, hP, hPQ⟩⟩ := Q.nonempty_primesOver (S := 𝓞 N)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ P
  have hQP : Q = P.under (𝓞 T) := hPQ.over
  rw [hQP, Ideal.under_under] at hR hM
  rw [hQP, ← stabilizer_fixes_iff K T N P hP0]
  rw [← stabilizer_fixes_iff K R N P hP0] at hR
  rw [← stabilizer_fixes_iff K M N P hP0] at hM
  intro σ hσ x
  have := hgen N ((σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K T N))
    (IsScalarTower.toAlgHom K T N) (hR σ hσ) (hM σ hσ)
  exact DFunLike.congr_fun this x

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hS1 : ((fun v : HeightOneSpectrum (𝓞 R) => v.under (𝓞 K)) ⁻¹' F).Finite`. Use `hF.preimage' fun p _ => ?_` and prove the remaining obligations. Use `haveI := p.isMaximal`.

Use `Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 R)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)` and prove the remaining obligations. Introduce and unpack `_ ⟨Q, rfl, rfl⟩`. Conclude with `⟨Q.isPrime, ⟨rfl⟩⟩`. Establish `hS2 : {v : HeightOneSpectrum (𝓞 R) | v.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 R)}.Finite` using `Ideal.finite_factors differentIdeal_ne_bot`. Use `not_forall_two_liesOver R T _ (summable_finite_union_not_prime R _ (hS1.union hS2)) ?_` and prove the remaining obligations.

Introduce `v hv`. Simplify using `only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_not] at hv`. Take `⟨⟨hvF, hvd⟩, hvp⟩` from `hv`. Use `haveI := v.isPrime`. Use `set p : HeightOneSpectrum (𝓞 K) := v.under (𝓞 K) with hp`.

Use `haveI := p.isPrime`. Use `haveI : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩`. Use `haveI : Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal := not_dvd_differentIdeal_iff.1 hvd`. Establish `he : v.asIdeal.ramificationIdx (𝓞 K) = 1` using `Ideal.ramificationIdx_eq_one _ _`. Establish `hn` using `Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal`.

Establish `hf : v.asIdeal.inertiaDeg (𝓞 K) = 1` using `(hn ▸ hvp).eq_one_of_pow`. Rewrite `hn` using `[hf, pow_one]`. Establish `hR : (p.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank K R`. Use `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p.asIdeal (𝓞 R) (R ≃ₐ[K] R)` as an intermediate fact. Rewrite `this` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (R ≃ₐ[K] R), Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (R ≃ₐ[K] R), he, hf, mul_one, mul_one, IsGalois.card_aut_eq_finrank]`. Then use the resulting hypothesis.

Establish `hM` using `(ncard_eq_finrank_iff K M p).1 (h p hvF (hn ▸ hvp) hR)`. Establish `hT : ∀ Q ∈ v.asIdeal.primesOver (𝓞 T), Q.ramificationIdx (𝓞 R) * Q.inertiaDeg (𝓞 R) = 1`. Introduce and unpack `Q ⟨hQ, hQv⟩`. Use `haveI : Q.LiesOver p.asIdeal := Ideal.LiesOver.trans Q v.asIdeal p.asIdeal`. Establish `h1` using `ef_eq_one_of_generate K R M T hgen Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q) (by rw [← hQv.over, he, hf]) (hM _ ⟨inferInstance, inferInstance⟩)`.

Rewrite `h1` using `[Ideal.ramificationIdx_tower v.asIdeal Q, Ideal.inertiaDeg_tower v.asIdeal Q, he, hf, one_mul, one_mul]`. Then use the resulting hypothesis. Establish `hN : ∀ Q ∈ v.asIdeal.primesOver (𝓞 T), Ideal.absNorm Q = Ideal.absNorm v.asIdeal`. Introduce and unpack `Q hQ`. Establish `h1` using `Nat.eq_one_of_mul_eq_one_left (hT Q hQ)`. Take `⟨_, _⟩` from `hQ`.

Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v.asIdeal Q, h1, pow_one]`. Rewrite `hlt` using `[← (ncard_eq_finrank_iff R T v).2 hT, Set.one_lt_ncard_iff_nontrivial_and_finite]`. Take `⟨⟨Q, hQ, Q', hQ', hne⟩, -⟩` from `hlt`. Use `haveI := hQ.2`. Use `haveI := hQ'.2`.

Conclude with `⟨⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ⟨Q', hQ'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q'⟩, fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hQ.2, hQ'.2, hN Q hQ, hN Q' hQ'⟩`.
-/
theorem finrank_le_one_of_generate (K R M T : Type) [Field K] [NumberField K] [Field R]
    [NumberField R] [Field M] [NumberField M] [Field T] [NumberField T] [Algebra K R] [Algebra K M]
    [Algebra K T] [Algebra R T] [Algebra M T] [IsScalarTower K R T] [IsScalarTower K M T]
    [IsGalois K R]
    (hgen : ∀ (N : Type) [Field N] [Algebra K N] (φ ψ : T →ₐ[K] N),
      (∀ x : R, φ (algebraMap R T x) = ψ (algebraMap R T x)) →
      (∀ x : M, φ (algebraMap M T x) = ψ (algebraMap M T x)) → φ = ψ)
    (F : Set (HeightOneSpectrum (𝓞 K))) (hF : F.Finite)
    (h : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ F → (Ideal.absNorm p.asIdeal).Prime →
      (p.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank K R →
      (p.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M) :
    Module.finrank R T ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hS1 : ((fun v : HeightOneSpectrum (𝓞 R) => v.under (𝓞 K)) ⁻¹' F).Finite := by
    refine hF.preimage' fun p _ => ?_
    haveI := p.isMaximal
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 R)).subset ?_)
      (fun _ _ _ _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨Q, rfl, rfl⟩
    exact ⟨Q.isPrime, ⟨rfl⟩⟩
  have hS2 : {v : HeightOneSpectrum (𝓞 R) | v.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 R)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine not_forall_two_liesOver R T _ (summable_finite_union_not_prime R _ (hS1.union hS2)) ?_
  intro v hv
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨hvF, hvd⟩, hvp⟩ := hv
  haveI := v.isPrime
  set p : HeightOneSpectrum (𝓞 K) := v.under (𝓞 K) with hp
  haveI := p.isPrime
  haveI : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal := not_dvd_differentIdeal_iff.1 hvd
  have he : v.asIdeal.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one _ _
  have hn := Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal
  have hf : v.asIdeal.inertiaDeg (𝓞 K) = 1 := (hn ▸ hvp).eq_one_of_pow
  rw [hf, pow_one] at hn
  have hR : (p.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank K R := by
    have := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p.asIdeal (𝓞 R)
      (R ≃ₐ[K] R)
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (R ≃ₐ[K] R),
      Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (R ≃ₐ[K] R), he, hf, mul_one, mul_one,
      IsGalois.card_aut_eq_finrank] at this
  have hM := (ncard_eq_finrank_iff K M p).1 (h p hvF (hn ▸ hvp) hR)
  have hT : ∀ Q ∈ v.asIdeal.primesOver (𝓞 T),
      Q.ramificationIdx (𝓞 R) * Q.inertiaDeg (𝓞 R) = 1 := by
    rintro Q ⟨hQ, hQv⟩
    haveI : Q.LiesOver p.asIdeal := Ideal.LiesOver.trans Q v.asIdeal p.asIdeal
    have h1 := ef_eq_one_of_generate K R M T hgen Q
      (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q) (by rw [← hQv.over, he, hf])
      (hM _ ⟨inferInstance, inferInstance⟩)
    rwa [Ideal.ramificationIdx_tower v.asIdeal Q, Ideal.inertiaDeg_tower v.asIdeal Q, he, hf,
      one_mul, one_mul] at h1
  have hN : ∀ Q ∈ v.asIdeal.primesOver (𝓞 T), Ideal.absNorm Q = Ideal.absNorm v.asIdeal := by
    rintro Q hQ
    have h1 := Nat.eq_one_of_mul_eq_one_left (hT Q hQ)
    obtain ⟨_, _⟩ := hQ
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal Q, h1, pow_one]
  rw [← (ncard_eq_finrank_iff R T v).2 hT, Set.one_lt_ncard_iff_nontrivial_and_finite] at hlt
  obtain ⟨⟨Q, hQ, Q', hQ', hne⟩, -⟩ := hlt
  haveI := hQ.2
  haveI := hQ'.2
  exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    ⟨Q', hQ'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hQ.2, hQ'.2, hN Q hQ, hN Q' hQ'⟩

/- English proof (translation)
Introduce `K Ω _ _ _ _ R M _ _ _ hfin`. Set `T : IntermediateField K Ω` to `R ⊔ M`. Use `haveI : NumberField T := NumberField.of_module_finite K T`. Use `letI : Algebra R T := (IntermediateField.inclusion (le_sup_left : R ≤ T)).toRingHom.toAlgebra`. Use `letI : Algebra M T := (IntermediateField.inclusion (le_sup_right : M ≤ T)).toRingHom.toAlgebra`.

Use `haveI : IsScalarTower K R T := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower K M T := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `h1 : Module.finrank R T ≤ 1`. Use `finrank_le_one_of_generate K R M T ?_ _ hfin ?_` and prove the remaining obligations. Introduce `N _ _ φ ψ hR hM`.

Use `IntermediateField.algHom_ext_of_eq_adjoin K (IntermediateField.sup_def R M) ?_` and prove the remaining obligations. Introduce and unpack `x (hx | hx)`. Conclude with `hR ⟨x, hx⟩`. Conclude with `hM ⟨x, hx⟩`. Introduce `p hp hpp hR`.

Rewrite `hR`, the goal using `[← ncard_eq_ncard_primesOver]`. Assume the negation of the conclusion as `hM`. Conclude with `hp ⟨hpp, hR, hM⟩`. Establish `h2 : Module.finrank K T ≤ Module.finrank K R` using `by haveI : Module.Free R T := Module.Free.of_divisionRing R T`. Rewrite using `[← Module.finrank_mul_finrank K R T]`.

Conclude with `mul_le_of_le_one_right' h1`. Establish `h3 : R = T` using `IntermediateField.eq_of_le_of_finrank_le le_sup_left h2`. Conclude with `h3 ▸ (le_sup_right : M ≤ T)`.
-/
theorem le_of_finite_split_not_split :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (R M : IntermediateField K Ω) [NumberField R] [NumberField M] [IsGalois K R], {𝔭 : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm 𝔭.asIdeal).Prime ∧ {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = 𝔭.asIdeal}.ncard = Module.finrank K R ∧ ¬ {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M}.Finite → M ≤ R := by
  intro K Ω _ _ _ _ R M _ _ _ hfin
  let T : IntermediateField K Ω := R ⊔ M
  haveI : NumberField T := NumberField.of_module_finite K T
  letI : Algebra R T := (IntermediateField.inclusion (le_sup_left : R ≤ T)).toRingHom.toAlgebra
  letI : Algebra M T := (IntermediateField.inclusion (le_sup_right : M ≤ T)).toRingHom.toAlgebra
  haveI : IsScalarTower K R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K M T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank R T ≤ 1 := by
    refine finrank_le_one_of_generate K R M T ?_ _ hfin ?_
    · intro N _ _ φ ψ hR hM
      refine IntermediateField.algHom_ext_of_eq_adjoin K (IntermediateField.sup_def R M) ?_
      rintro x (hx | hx)
      · exact hR ⟨x, hx⟩
      · exact hM ⟨x, hx⟩
    · intro p hp hpp hR
      rw [← ncard_eq_ncard_primesOver] at hR ⊢
      by_contra hM
      exact hp ⟨hpp, hR, hM⟩
  have h2 : Module.finrank K T ≤ Module.finrank K R := by
    haveI : Module.Free R T := Module.Free.of_divisionRing R T
    rw [← Module.finrank_mul_finrank K R T]
    exact mul_le_of_le_one_right' h1
  have h3 : R = T := IntermediateField.eq_of_le_of_finrank_le le_sup_left h2
  exact h3 ▸ (le_sup_right : M ≤ T)

end GlobalTheory.Bauer
