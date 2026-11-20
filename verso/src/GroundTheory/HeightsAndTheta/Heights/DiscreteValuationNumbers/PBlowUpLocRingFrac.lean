import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel`. Use `hP.multiProj.isPrime` as an intermediate fact. Introduce `W' hW' hW'rel hW'W`. Establish `hW'p : W'.IsPrime` using `hW'.1.1`. Establish `hbl : blowUpOf P u ≤ W'` using `le_trans le_sup_left hW'.1.2`.

Establish `hmh : IsMultiHomogIdeal W'` using `MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W' (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c) (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'`. Take `⟨e, L, hL, he, hLQ⟩` from `havoid O (Option K) (extIdx ι J) _ (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)`. Establish `hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧ W'.comap (liftForm (ι` using `ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩`. Establish `: (blowUpOf P u).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨φ, hφ⟩` from `hiso O K ι J P u W' hbl`.

Establish `hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0`. Introduce `d H hH hHW h0`. Establish `h1` using `hφ d H H hH hH hHW`. Rewrite `h1` using `[h0, div_zero]`. Establish `h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ : homLocRing (blowUpOf P u) W') = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))`. Apply `div_self` to reduce the goal to its premises. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `fun h => hHW (hbl h)`.

Rewrite `h1` using `[h2, map_one]`. Conclude with `one_ne_zero h1`. Establish `hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b → G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u, (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / …`. Introduce `b F G hF hG hGW`. Use `set k := ∑ o, b o with hk`.

Take `⟨M, hM, hMW⟩` from `homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)`. Establish `hdeg : b + (fun o => k * e o - b o) = k • e`. Use function extensionality and compare the values at `o`. Establish `: b o ≤ k * e o` using `le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Use linear arithmetic over natural numbers and integers. Establish `hFM : IsMultiHomog (F * M) (k • e)` using `hdeg ▸ hF.mul hM`. Establish `hGM : IsMultiHomog (G * M) (k • e)` using `hdeg ▸ hG.mul hM`. Establish `hLk : IsMultiHomog (L ^ k) (k • e)` using `hL.pow k`. Establish `hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧ blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι` using `ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q := fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)`.

Establish `hmemB : ∀ H, IsMultiHomog H (k • e) → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈ blowUpOverLoc P W u` using `fun H hH => Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ => Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩`. Establish `hGMW : G * M ∉ W'` using `fun h => (hW'p.mem_or_mem h).elim hGW hMW`. Establish `hLkW : L ^ k ∉ W'` using `hLkQ W' hW'fam`. Establish `hG0` using `hne _ _ hG hGW`. Establish `hGM0` using `hne _ _ hGM hGMW`.

Establish `hLk0` using `hne _ _ hLk hLkW`. Use `⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_, Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, mul_comm]`. Conclude with `div_self (mul_ne_zero hLk0 hGM0)`. Rewrite `hGM0`, the goal using `[map_mul, map_mul]`.

Rewrite using `[map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `z hz`. Proceed by induction on `hz using Subring.closure_induction with`. Consider the case `mem z hz`.

Take `⟨b, F, G, hF, hG, hGW, rfl⟩` from `hz`. Conclude with `hgen b F G hF hG hGW`. Consider the case `zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩`. Consider the case `one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩`. Consider the case `add x y _ _ h₁ h₂`.

Take `⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩` from `h₁`. Take `⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩` from `h₂`. Use `⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂, ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx₁, ← hx₂]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `neg x _ h`. Take `⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩` from `h`. Conclude with `⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩`. Consider the case `mul x y _ _ h₁ h₂`. Take `⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩` from `h₁`.

Take `⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩` from `h₂`. Use `⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂, ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx₁, ← hx₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BlowUpLocRingFrac.proof (hiso : BlowUpLocRingIso.Statement.{u})
    (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) (havoid : MultiHomogPrimeAvoid.Statement.{u}) :
    BlowUpLocRingFrac.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  obtain ⟨e, L, hL, he, hLQ⟩ := havoid O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl

  have hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' →
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0 := by
    intro d H hH hHW h0
    have h1 := hφ d H H hH hH hHW
    rw [h0, div_zero] at h1
    have h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ :
        homLocRing (blowUpOf P u) W') = 1 := by
      apply Subtype.ext
      show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
      apply div_self
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hHW (hbl h)
    rw [h2, map_one] at h1
    exact one_ne_zero h1

  have hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b →
      G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
        (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * s = bb := by
    intro b F G hF hG hGW
    set k := ∑ o, b o with hk
    obtain ⟨M, hM, hMW⟩ := homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)
    have hdeg : b + (fun o => k * e o - b o) = k • e := by
      funext o
      have : b o ≤ k * e o := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hFM : IsMultiHomog (F * M) (k • e) := hdeg ▸ hF.mul hM
    have hGM : IsMultiHomog (G * M) (k • e) := hdeg ▸ hG.mul hM
    have hLk : IsMultiHomog (L ^ k) (k • e) := hL.pow k
    have hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q :=
      fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)
    have hmemB : ∀ H, IsMultiHomog H (k • e) →
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈
          blowUpOverLoc P W u := fun H hH =>
      Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ =>
        Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩
    have hGMW : G * M ∉ W' := fun h => (hW'p.mem_or_mem h).elim hGW hMW
    have hLkW : L ^ k ∉ W' := hLkQ W' hW'fam
    have hG0 := hne _ _ hG hGW
    have hGM0 := hne _ _ hGM hGMW
    have hLk0 := hne _ _ hLk hLkW
    refine ⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_,
      Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩
    · rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero hLk0 hGM0)
    · rw [map_mul, map_mul] at hGM0 ⊢
      rw [map_mul, map_mul]
      field_simp
  intro z hz
  induction hz using Subring.closure_induction with
  | mem z hz =>
    obtain ⟨b, F, G, hF, hG, hGW, rfl⟩ := hz
    exact hgen b F G hF hG hGW
  | zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩
  | add x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring
  | neg x _ h =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩ := h
    exact ⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩
  | mul x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
