import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BalancedPairs

set_option autoImplicit false

namespace GlobalTheory.BalancedTwist

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem pairing_eq {S : Type} [CommRing S] {d : ℕ} (M : Fin d → Fin d → S) (v w : Fin d → S) :
    ∑ i, ∑ j, M i j * v i * w j = v ⬝ᵥ (Matrix.of M *ᵥ w) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `eL : ∀ a ℓ ℓ', u ℓ ⬝ᵥ (((A a)ᵀ * Matrix.of M) *ᵥ u ℓ') = algebraMap c.F S (embK c ℓ.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ'))`. Introduce `a ℓ ℓ'`. Rewrite using `[← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, heig, smul_dotProduct, smul_eq_mul]`. Establish `eR : ∀ a ℓ ℓ', u ℓ ⬝ᵥ ((Matrix.of M * A a) *ᵥ u ℓ') = algebraMap c.F S (embK c ℓ'.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ'))`. Introduce `a ℓ ℓ'`.

Rewrite using `[← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ` using `fun τ => by`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate]`. Prove the components needed by the constructor for the conclusion.

Introduce `h ℓ ℓ' hne`. Assume the negation of the conclusion as `hc`. Apply `hne` to reduce the goal to its premises. Rewrite using `[pairing_eq]`. Use `GlobalTheory.ChartJoints.balanced_pairs H c ℓ.1 ℓ'.1 _ (fun a => ?_) (fun h' => hc ?_)` and prove the remaining obligations.

Rewrite using `[← eL, ← eR, h]`. Rewrite using `[h', cc]`. Introduce `h a set N := (A a)ᵀ * Matrix.of M - Matrix.of M * A (H.bar a) with hN`. Establish `h0 : ∀ ℓ ℓ', u ℓ ⬝ᵥ (N *ᵥ u ℓ') = 0`. Introduce `ℓ ℓ'`.

Rewrite using `[hN, sub_mulVec, dotProduct_sub, eL, eR]`. Distinguish the cases in `hz : ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j = 0`. Rewrite using `[← pairing_eq, hz]`. Simplify using the standard rewrite rules. Establish `hb : embK c ℓ'.1 (H.bar a) = embK c ℓ.1 a`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[embK_coe, embK_coe, GlobalTheory.ChartJoints.emb_bar, h ℓ ℓ' hz, cc]`. Rewrite using `[hb, sub_self]`. Establish `hv : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, v = ∑ ℓ, a ℓ • u ℓ`. Introduce `v`.

Take `⟨a, ha⟩` from `hsp v`. Conclude with `⟨a, funext fun j => by simp [← ha j, Finset.sum_apply]⟩`. Establish `h1 : ∀ v w : Fin d → S, v ⬝ᵥ (N *ᵥ w) = 0`. Introduce `v w`. Take `⟨a, rfl⟩` from `hv v`.

Take `⟨b, rfl⟩` from `hv w`. Simplify using `[sum_dotProduct, mulVec_sum, dotProduct_sum, mulVec_smul, h0]`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Use `h1 (Pi.single i 1) (Pi.single j 1)` as an intermediate fact.

Establish `h2 : N i j = 0` using `by simpa using this`. Conclude with `h2`.
-/
theorem balanced_iff (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ}
    (A : 𝓞 E → Matrix (Fin d) (Fin d) S) (u : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), A a *ᵥ u ℓ = algebraMap c.F S (embK c ℓ.1 a) • u ℓ)
    (hsp : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j)
    (M : Fin d → Fin d → S) :
    (∀ a, (A a)ᵀ * Matrix.of M = Matrix.of M * A (H.bar a)) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  have eL : ∀ a ℓ ℓ', u ℓ ⬝ᵥ (((A a)ᵀ * Matrix.of M) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, heig, smul_dotProduct, smul_eq_mul]
  have eR : ∀ a ℓ ℓ', u ℓ ⬝ᵥ ((Matrix.of M * A a) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ'.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext x; simp [ComplexEmbedding.conjugate]
  constructor
  · intro h ℓ ℓ' hne
    by_contra hc
    apply hne
    rw [pairing_eq]
    refine GlobalTheory.ChartJoints.balanced_pairs H c ℓ.1 ℓ'.1 _ (fun a => ?_) (fun h' => hc ?_)
    · rw [← eL, ← eR, h]
    · rw [h', cc]
  · intro h a
    set N := (A a)ᵀ * Matrix.of M - Matrix.of M * A (H.bar a) with hN
    have h0 : ∀ ℓ ℓ', u ℓ ⬝ᵥ (N *ᵥ u ℓ') = 0 := by
      intro ℓ ℓ'
      rw [hN, sub_mulVec, dotProduct_sub, eL, eR]
      by_cases hz : ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j = 0
      · rw [← pairing_eq, hz]; simp
      · have hb : embK c ℓ'.1 (H.bar a) = embK c ℓ.1 a := by
          apply Subtype.ext
          rw [embK_coe, embK_coe, GlobalTheory.ChartJoints.emb_bar, h ℓ ℓ' hz, cc]
        rw [hb, sub_self]
    have hv : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, v = ∑ ℓ, a ℓ • u ℓ := by
      intro v
      obtain ⟨a, ha⟩ := hsp v
      exact ⟨a, funext fun j => by simp [← ha j, Finset.sum_apply]⟩
    have h1 : ∀ v w : Fin d → S, v ⬝ᵥ (N *ᵥ w) = 0 := by
      intro v w
      obtain ⟨a, rfl⟩ := hv v
      obtain ⟨b, rfl⟩ := hv w
      simp [sum_dotProduct, mulVec_sum, dotProduct_sum, mulVec_smul, h0]
    rw [← sub_eq_zero]
    ext i j
    have := h1 (Pi.single i 1) (Pi.single j 1)
    have h2 : N i j = 0 := by simpa using this
    exact h2

/- English proof (translation)
Establish `key : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (M : Fin C.d → Fin C.d → S), (∀ a, ( …`. Introduce `E _ _ _ H Dw l Xo c _ S _ _ _ y C M`. Use `balanced_iff c (fun a => TB.dLin (C.B.A.act a)) C.uvec (fun a ℓ => ?_) (fun v => (C.chart.basis v).exists) M` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i`.

Prove the components needed by the constructor for the conclusion. Introduce `h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C`. Take `⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩` from `h E H Dw l Xo c hs S y C`. Conclude with `⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).1 (h4 m), h5⟩`. Introduce `h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C`.

Take `⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩` from `h E H Dw l Xo c hs S y C`. Conclude with `⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).2 (h4 m), h5⟩`.
-/
theorem frTruncFix_iff : FrTruncFixSt ↔ FrTruncFixBSt := by
  have key : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
      (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (M : Fin C.d → Fin C.d → S),
      (∀ a, (TB.dLin (C.B.A.act a))ᵀ * Matrix.of M = Matrix.of M * TB.dLin (C.B.A.act (H.bar a))) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C M
    refine balanced_iff c (fun a => TB.dLin (C.B.A.act a)) C.uvec (fun a ℓ => ?_)
      (fun v => (C.chart.basis v).exists) M
    funext i
    exact GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  constructor
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).1 (h4 m), h5⟩
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).2 (h4 m), h5⟩

end GlobalTheory.BalancedTwist
