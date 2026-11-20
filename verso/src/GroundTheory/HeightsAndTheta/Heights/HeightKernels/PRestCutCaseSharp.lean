import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun i _ => by simpa [RestTerms.yRoot] using ((isHomogeneous_C_mul_X (R := ℚ) _ (RestTerms.yIndex f r a cs τ i)).pow n)`.
-/
theorem KRest.smallPowerSum_isHomogeneous (f r a : ℕ) (cs : RestTerms.SmallBlock) (n : ℕ) (τ : Fin f) :
    (RestTerms.smallPowerSum f r a cs n τ).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa [RestTerms.yRoot] using ((isHomogeneous_C_mul_X (R := ℚ) _ (RestTerms.yIndex f r a cs τ i)).pow n)

/- English proof (translation)
Introduce `f j k r a cs e hf hj hk hr ha hN hra hF hJ hlie I hI vol hvol P hP B₀ hB φ`. Establish `hB' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀` using `by rw [hN]; exact hB`. Take `⟨hex0, hall0⟩` from `h₁ f r a cs B₀ hf hr ha hB'`. Take `⟨c, hcomp, hdeg⟩` from `h₂ f j k r a cs e hf hr ha hN hJ I hI`. Take `⟨⟨Q₀, hQ₀, hQ₀h⟩, hexQ⟩` from `h₃ f j k r a cs e hf hN (by omega) hF hex0`.

Use `⟨hexQ, fun Q hQ => ?_⟩` and prove the remaining obligations. Establish `hQ' : IsPowerSumDecomposition f j k (restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs)) Q`. Rewrite using `[hF]`. Conclude with `hQ`. Establish `hterm : ∀ m : ℕ, 2 ≤ m → m ≤ r + a → ∀ τ τ' : Fin f, I (restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs (m - 1) τ') * Q τ m) = c * RestTerms.flagIntegral f (r + a) (RestTerms.smallPowerSum f r a cs (m - 1) τ' * Q₀ m τ)` using `fun m hm2 hmN τ τ' => h₄ f j k (r + a) e I c hcomp _ Q₀ hQ₀ hQ₀h Q hQ' m (by omega) hmN τ _ (KRest.smallPowerSum_isHomogeneous f r a cs (m - 1) τ')`.

Take `⟨s, ε, hε, heq⟩` from `h₅ f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ`. Take `⟨hsum, hbound⟩` from `hall0 Q₀ hQ₀ s ε hε P`. Establish `hfun : (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) = fun p : primesAbove P B₀ => (vol * c) * RestTerms.restPrimeModel f r a cs Q₀ s ε p.1`. Use function extensionality and compare the values at `fun p => heq vol p.1`. Rewrite using `[hfun]`.

Use `⟨(hsum.of_abs).mul_left _, ?_⟩` and prove the remaining obligations. Rewrite using `[tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hdeg, abs_mul]`. Establish `hn : (((f * (r * a) + 1 : ℕ)) : ℝ) = ((f * j * k : ℕ) : ℝ) + 1`. Rewrite using `[hra]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hbound` using `[hn]`. Establish `hc : 0 ≤ vol * |c|` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RestCutCaseSharp.proof (h₁ : RestTerms.RestBound.Statement) (h₂ : RestCutCaseCompare.Statement)
    (h₃ : RestCutCaseDecomp.Statement) (h₄ : RestCutTermEq.Statement)
    (h₅ : RestCutPrimeEq.Statement) : RestCutCaseSharp.Statement := by
  intro f j k r a cs e hf hj hk hr ha hN hra hF hJ hlie I hI vol hvol P hP B₀ hB φ
  have hB' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ := by rw [hN]; exact hB
  obtain ⟨hex0, hall0⟩ := h₁ f r a cs B₀ hf hr ha hB'
  obtain ⟨c, hcomp, hdeg⟩ := h₂ f j k r a cs e hf hr ha hN hJ I hI
  obtain ⟨⟨Q₀, hQ₀, hQ₀h⟩, hexQ⟩ := h₃ f j k r a cs e hf hN (by omega) hF hex0
  refine ⟨hexQ, fun Q hQ => ?_⟩
  have hQ' : IsPowerSumDecomposition f j k
      (restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs)) Q := by
    rw [hF]; exact hQ
  have hterm : ∀ m : ℕ, 2 ≤ m → m ≤ r + a → ∀ τ τ' : Fin f,
      I (restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs (m - 1) τ') * Q τ m) =
        c * RestTerms.flagIntegral f (r + a)
          (RestTerms.smallPowerSum f r a cs (m - 1) τ' * Q₀ m τ) := fun m hm2 hmN τ τ' =>
    h₄ f j k (r + a) e I c hcomp _ Q₀ hQ₀ hQ₀h Q hQ' m (by omega) hmN τ _
      (KRest.smallPowerSum_isHomogeneous f r a cs (m - 1) τ')
  obtain ⟨s, ε, hε, heq⟩ := h₅ f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ
  obtain ⟨hsum, hbound⟩ := hall0 Q₀ hQ₀ s ε hε P
  have hfun : (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) =
      fun p : primesAbove P B₀ => (vol * c) * RestTerms.restPrimeModel f r a cs Q₀ s ε p.1 :=
    funext fun p => heq vol p.1
  rw [hfun]
  refine ⟨(hsum.of_abs).mul_left _, ?_⟩
  rw [tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hdeg, abs_mul]
  have hn : (((f * (r * a) + 1 : ℕ)) : ℝ) = ((f * j * k : ℕ) : ℝ) + 1 := by
    rw [hra]; push_cast; ring
  rw [hn] at hbound
  have hc : 0 ≤ vol * |c| := by positivity
  calc vol * |c| * |∑' p : primesAbove P B₀, RestTerms.restPrimeModel f r a cs Q₀ s ε p.1|
      ≤ vol * |c| * (1.6 * (((f * j * k : ℕ) : ℝ) + 1) * |(RestTerms.fibreDegree f r a cs : ℝ)|) :=
        mul_le_mul_of_nonneg_left hbound hc
    _ = 1.6 * (((f * j * k : ℕ) : ℝ) + 1) * vol * (|c| * |(RestTerms.fibreDegree f r a cs : ℝ)|) := by
        ring

end GroundTheory.Heights₂.Heights
