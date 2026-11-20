import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨a, b, c, d⟩` from `hδ`. Establish `e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N)` using `fun x => ZMod.cast_intCast h x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, a]`.

Simplify using `[ZMod.cast_one h]`. Rewrite using `[← e, b]`. Simplify using the standard rewrite rules. Rewrite using `[← e, c]`. Simplify using the standard rewrite rules.

Rewrite using `[← e, d]`. Simplify using `[ZMod.cast_one h]`.
-/
theorem relTriv_gamma_of_dvd {N M : ℕ} (h : N ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

/- English proof (translation)
Rewrite `hδ` using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨a, b, c, d⟩` from `hδ`. Simplify using `only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]`. Rewrite using `[MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n))` using `fun x => map_intCast _ x`. Apply the tactic sequence `fin_cases i <;>`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]`.
-/
theorem toZModPow_eval_mulVec {l : ℕ} [Fact l.Prime] (n : ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) (q : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval
      (((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℤ_[l]) *ᵥ u) q) =
      PadicInt.toZModPow n (MvPolynomial.eval u q) := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  obtain ⟨a, b, c, d⟩ := hδ
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  have e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n)) := fun x => map_intCast _ x
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]

/- English proof (translation)
Introduce `Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF`. Take `⟨ψ, p, hψ, hFψ⟩` from `hF`. Use function extensionality and compare the values at `u`. Apply `AdicCompletion.ext` to reduce the goal to its premises. Introduce `n`.

Take `⟨χ, hK, M₁, hM₁, hχ⟩` from `hR u n`. Express the relevant statement in the definitionally equal form `AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)`. Rewrite using `[Pi.zero_apply, map_zero]`. Use `GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `: 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`.

Check the signs of the components of the expression. Establish `h1 : δ ∈ CongruenceSubgroup.Gamma M₁` using `relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ`. Establish `h0 : δ ∈ Γ` using `hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)`. Establish `hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n)` using `relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ`. Establish `hI : Complex.I ∈ Hs` using `by simp [Hs]`.

Establish `hδI : mob (ofSL δ) Complex.I ∈ Hs` using `(GlobalTheory.T.glTwoPosRatMobius_basic_laws).1 _ _ hI`. Establish `key` using `hχ δ h1 Complex.I hI`. Use `beta_reduce at key`. Rewrite using `[← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]`. Simplify using `only [map_add, GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub, toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]`.
-/
theorem rel_triv_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ →
      ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  intro Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF
  obtain ⟨ψ, p, hψ, hFψ⟩ := hF
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, hK, M₁, hM₁, hχ⟩ := hR u n
  change AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)
  rw [Pi.zero_apply, map_zero]
  refine GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩
  · have : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    positivity
  have h1 : δ ∈ CongruenceSubgroup.Gamma M₁ := relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ
  have h0 : δ ∈ Γ := hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)
  have hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hδI : mob (ofSL δ) Complex.I ∈ Hs := (GlobalTheory.T.glTwoPosRatMobius_basic_laws).1 _ _ hI
  have key := hχ δ h1 Complex.I hI
  beta_reduce at key
  rw [← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]
  simp only [map_add, GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub,
    toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]

end GlobalTheory.KZ.H3
