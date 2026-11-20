import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg

open Finset
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

/- English proof (translation)
Introduce `a b c d _ _` and use `hE a b c d`.
-/
lemma kRel_of_glRel {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) : CompanionTheory.D.DSIC.KRel ε E :=
  fun a b c d _ _ => hE a b c d

/- English proof (translation)
Introduce `a b he x y`. Rewrite using `[hU a b x y]`. Simplify using `[Formalism.REAL.sgn, he]`.
-/
lemma kUnit_of_isUnitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) : CompanionTheory.D.DSIC.KUnit ε E := by
  intro a b he x y
  rw [hU a b x y]
  simp [Formalism.REAL.sgn, he]

/- English proof (translation)
Establish `h` using `GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1`. Rewrite `h` using `[hh.2 a b hab he, norm_zero]`. Establish `hp : 0 < ‖u‖ ^ 2` using `by have := norm_pos_iff.2 hu; positivity`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Establish `: 0 < (μ b - μ a) * ‖u‖ ^ 2` using `mul_pos (by linarith) hp`. Use `sq_nonneg ‖E b a u‖` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma dominant_of_kHighest {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hF : CompanionTheory.D.DSIC.KRel ε E) (hU : CompanionTheory.D.DSIC.KUnit ε E)
    {μ : Fin n → ℝ} {u : V} (hu : u ≠ 0) (hh : KHighest ε E μ u) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    μ b ≤ μ a := by
  have h := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1
  rw [hh.2 a b hab he, norm_zero] at h
  have hp : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  by_contra hc
  push Not at hc
  have : 0 < (μ b - μ a) * ‖u‖ ^ 2 := mul_pos (by linarith) hp
  have := sq_nonneg ‖E b a u‖
  nlinarith

/- English proof (translation)
Use `⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, rhoC, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, ((2 : ℝ) • rhoC ε) a = m := by
  refine ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  simp only [Pi.smul_apply, rhoC, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Use `choose m hm using hμ`. Use `choose r hr using two_rhoC_int ε`. Use `⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩` and prove the remaining obligations. Establish `h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2`. Introduce `a`.

Establish `h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2` using `Int.toNat_of_nonneg (sq_nonneg _)`. Establish `h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ)` using `by exact_mod_cast h0`. Rewrite using `[h1, hm a, hr a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Nat.cast_sum]`. Simplify using `only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [h a, sq]`.
-/
lemma vNormSq_nat (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : ∀ a, ∃ m : ℤ, μ a = m) :
    ∃ k : ℕ, vNormSq ε μ = k := by
  choose m hm using hμ
  choose r hr using two_rhoC_int ε
  refine ⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩
  have h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2 := by
    intro a
    have h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    have h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1, hm a, hr a]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [h a, sq]

/- English proof (translation)
Introduce `n ε V _ _ E hE hV hU hfin hint`. Establish `hF : CompanionTheory.D.DSIC.KRel ε E` using `kRel_of_glRel hE`. Establish `hK : CompanionTheory.D.DSIC.KUnit ε E` using `kUnit_of_isUnitary hU`. Establish `hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m` using `fun μ x hx hh => hint μ x hx hh.1`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`.

Take `⟨S, hfd, hS, hxS⟩` from `hfin x`. Take `⟨y, -, hy0, ν, hy⟩` from `Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS (fun h => hx (by simpa [h] using hxS))`. Establish `hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k`. Take `⟨k, hk⟩` from `vNormSq_nat ε (hintK ν y hy0 hy)`. Conclude with `⟨k, ν, y, hy0, hy, hk⟩`.

Take `⟨γ, u, hu, hγ, hk⟩` from `Nat.find_spec hex`. Use `⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩` and prove the remaining obligations. Introduce `μ w hw hμ`. Take `⟨k, hk'⟩` from `vNormSq_nat ε (hintK μ w hw hμ)`. Rewrite using `[hk, hk']`.

Conclude with `Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩` after adjusting the coercions.
-/
theorem lktExists : LKTExists := by
  classical
  intro n ε V _ _ E hE hV hU hfin hint
  have hF : CompanionTheory.D.DSIC.KRel ε E := kRel_of_glRel hE
  have hK : CompanionTheory.D.DSIC.KUnit ε E := kUnit_of_isUnitary hU
  have hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m :=
    fun μ x hx hh => hint μ x hx hh.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨S, hfd, hS, hxS⟩ := hfin x
  obtain ⟨y, -, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS
    (fun h => hx (by simpa [h] using hxS))
  have hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k := by
    obtain ⟨k, hk⟩ := vNormSq_nat ε (hintK ν y hy0 hy)
    exact ⟨k, ν, y, hy0, hy, hk⟩
  obtain ⟨γ, u, hu, hγ, hk⟩ := Nat.find_spec hex
  refine ⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩
  intro μ w hw hμ
  obtain ⟨k, hk'⟩ := vNormSq_nat ε (hintK μ w hw hμ)
  rw [hk, hk']
  exact_mod_cast Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩

end GlobalTheory.CompanionTheory.RgExhFarReg
