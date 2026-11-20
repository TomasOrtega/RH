import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStepNilExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfIsStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorizationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

/- English proof (translation)
The claim follows from `fun l hl hs ↦ h l hl (e.trans hs)`.
-/
theorem NilExp.mono {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {N M : ℕ} (h : NilExp κ N)
    (e : N ≤ M) : NilExp κ M :=
  fun l hl hs ↦ h l hl (e.trans hs)

/- English proof (translation)
Establish `h1` using `h [(1, a)] (by simpa using ha) (by simp)`. Simplify `h1` using `[κ.dpow_one ha]`.
-/
theorem NilExp.eq_zero {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) {a : R}
    (ha : a ∈ I) : a = 0 := by

  have h1 := h [(1, a)] (by simpa using ha) (by simp)
  simpa [κ.dpow_one ha] using h1

/- English proof (translation)
Establish `hbot : I = ⊥` using `eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)`. Establish `hI : I ^ 2 = 0`. Rewrite using `[hbot, pow_two, Ideal.mul_bot]`. Both sides reduce to the same expression. Use `⟨hI, ?_⟩` and prove the remaining obligations.

Use extensionality with `n x hx`. Take `rfl` from `h.eq_zero hx`. Break down `n with _ | _ | n` into its components or cases. Rewrite using `[κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]`. Rewrite using `[κ.dpow_one hx, (divided₂ hI).dpow_one hx]`.

Rewrite using `[squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]`.
-/
theorem NilExp.eq_sqDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) :
    ∃ hI : I ^ 2 = 0, κ = divided₂ hI := by
  have hbot : I = ⊥ := eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)
  have hI : I ^ 2 = 0 := by
    rw [hbot, pow_two, Ideal.mul_bot]
    rfl
  refine ⟨hI, ?_⟩

  ext n x hx
  obtain rfl := h.eq_zero hx
  rcases n with _ | _ | n
  · rw [κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]
  · rw [κ.dpow_one hx, (divided₂ hI).dpow_one hx]
  · rw [squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) → LiftObj κ π ∧ LiftHom κ π`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ I κ R₀ _ π hπ hker h`.

Take `⟨hI, rfl⟩` from `NilExp.eq_sqDP h`. Conclude with `hS R I hI R₀ π hπ hker`. Consider the case `succ n ih`. Introduce `R _ I κ R₀ _ π hπ hker h`. Take `⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩` from `exists_isStep_nilExp R R₀ I κ π hπ hker n h`.

Establish `hsq` using `hS R J hJ R₁ ρ st.surj st.kerJ`. Establish `hih` using `ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁`. Conclude with `⟨GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1, liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩`. Introduce `R _ I κ hκ R₀ _ π hπ hker`. Take `⟨N, hN⟩` from `(isPDNilpotent_iff κ).1 hκ`.

Conclude with `key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))`.
-/
theorem abelianLifting_of_sqLifting (hD : AbelianDeRham) (hU : AbelianUnobstructed) (hS : SqLifting) :
    AbelianLifting := by

  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) →
        LiftObj κ π ∧ LiftHom κ π := by
    intro n
    induction n with
    | zero =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨hI, rfl⟩ := NilExp.eq_sqDP h
      exact hS R I hI R₀ π hπ hker
    | succ n ih =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩ := exists_isStep_nilExp R R₀ I κ π hπ hker n h
      have hsq := hS R J hJ R₁ ρ st.surj st.kerJ
      have hih := ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁
      exact ⟨GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1,
        liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩
  intro R _ I κ hκ R₀ _ π hπ hker
  obtain ⟨N, hN⟩ := (isPDNilpotent_iff κ).1 hκ
  exact key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))

/- English proof (translation)
Introduce `hD hL hU`. Use `abelianLifting_of_sqLifting hD hU (GlobalTheory.T.squareZeroLifting_of_noetherian_case hD ?_)` and prove the remaining obligations. Introduce `R _ _ I hI R₀ _ π hπ hk`. Conclude with `⟨GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk), GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩`.
-/
theorem abelianLifting_of_schemeLifts :
    AbelianDeRham → AbelianSchemeLifts → AbelianUnobstructed → AbelianLifting := by
  intro hD hL hU
  refine abelianLifting_of_sqLifting hD hU (GlobalTheory.T.squareZeroLifting_of_noetherian_case hD ?_)
  intro R _ _ I hI R₀ _ π hπ hk
  exact ⟨GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk),
    GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩

end GlobalTheory.SqLift
