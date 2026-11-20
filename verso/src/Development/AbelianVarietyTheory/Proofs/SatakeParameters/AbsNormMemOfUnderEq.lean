import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.DenseUsable

/- English proof (translation)
Set `F : Polynomial ℤ` to `Polynomial.X ^ 2 + Polynomial.C (d : ℤ)`. Establish `hF : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 + d` using `by intro z; simp [F]`. Establish `hF' : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z`. Introduce `z`. Simplify using `[F]`.

Use `left`. Conclude with `map_ofNat _ 2`. Establish `hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[q])‖ < 1` using `(PadicInt.norm_int_lt_one_iff_dvd _).2 h1`. Establish `hn : ‖((2 * a : ℤ) : ℤ_[q])‖ = 1` using `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))`. Take `⟨z, hz, -⟩` from `hensels_lemma (F := F) (a := (a : ℤ_[q])) (by`.

Rewrite using `[hF, hF']`. Move the coercions through the operations in `at hn hlt`. Rewrite using `[hn]`. Simplify using `using hlt)`. Rewrite `hz` using `[hF]`.

Use `⟨(z : ℚ_[q]), ?_⟩` and prove the remaining obligations. Establish `: ((z ^ 2 + d : ℤ_[q]) : ℚ_[q]) = 0` using `by rw [hz]; simp`. Move the coercions through the operations in `at this`. Take the linear combination `-this`.
-/
theorem isSquare_neg_padic (q : ℕ) [hq : Fact q.Prime] (d : ℕ) (a : ℤ)
    (h1 : (q : ℤ) ∣ a ^ 2 + d) (h2 : ¬ (q : ℤ) ∣ 2 * a) : IsSquare (-(d : ℚ_[q])) := by
  let F : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (d : ℤ)
  have hF : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 + d := by intro z; simp [F]
  have hF' : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z := by
    intro z; simp [F]; left; exact map_ofNat _ 2
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 h1
  have hn : ‖((2 * a : ℤ) : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[q])) (by
    rw [hF, hF']; push_cast at hn hlt; rw [hn]; simpa using hlt)
  rw [hF] at hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + d : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz]; simp
  push_cast at this
  linear_combination -this

/- English proof (translation)
Use `set p := Ideal.absNorm w.asIdeal`. Use `letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _`. Establish `hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p`. Rewrite using `[← Nat.card_eq_fintype_card]`. Use `show _ = Ideal.absNorm w.asIdeal`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Set `e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal)` to `ZMod.ringEquivOfPrime _ hp hc`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd, map_intCast, ← map_intCast e, map_eq_zero_iff _ e.injective]`.
-/
theorem intCast_mem_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (n : ℤ) :
    ((n : 𝓞 E) ∈ w.asIdeal ↔ ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∣ n) := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd, map_intCast, ← map_intCast e,
    map_eq_zero_iff _ e.injective]

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

/- English proof (translation)
Use `set p := Ideal.absNorm w.asIdeal`. Use `letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _`. Establish `hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p`. Rewrite using `[← Nat.card_eq_fintype_card]`. Use `show _ = Ideal.absNorm w.asIdeal`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Set `e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal)` to `ZMod.ringEquivOfPrime _ hp hc`. Take `⟨c, hc'⟩` from `e.surjective (Ideal.Quotient.mk w.asIdeal y)`. Take `⟨a, rfl⟩` from `ZMod.intCast_surjective c`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc', map_intCast, map_intCast, sub_self]`.
-/
theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (y : 𝓞 E) : ∃ a : ℤ, y - (a : 𝓞 E) ∈ w.asIdeal := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  obtain ⟨c, hc'⟩ := e.surjective (Ideal.Quotient.mk w.asIdeal y)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc', map_intCast, map_intCast, sub_self]

/- English proof (translation)
Establish `hf` using `((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp`. Use `⟨GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w hf he, fun q hq hqw => ?_⟩` and prove the remaining obligations. Establish `hqw' : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal` using `by rwa [Int.cast_natCast]`. Establish `hpq : Ideal.absNorm w.asIdeal = q`. Use `(intCast_mem_iff w hp q).1 hqw'` as an intermediate fact.

Conclude with `(Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 this)`. Take `⟨-, x, hx⟩` from `hd`. Establish `hi : IsIntegral ℤ x`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hx]`.

Establish `: -(d : E) = algebraMap ℤ E (-(d : ℤ))` using `by simp`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Set `y : 𝓞 E` to `⟨x, hi⟩`. Establish `hy : y ^ 2 = -(d : 𝓞 E)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hx`. Take `⟨a, ha⟩` from `exists_int_sub_mem w hp y`. Establish `h1 : ((q : ℤ) : ℤ) ∣ a ^ 2 + d`.

Rewrite using `[← hpq]`. Use `(intCast_mem_iff w hp _).1 ?_` and prove the remaining obligations. Establish `: (((a ^ 2 + d : ℤ)) : 𝓞 E) = (y - a) * (-(y + a)) + (y ^ 2 + d)` using `by push_cast; ring`. Rewrite using `[this, hy, neg_add_cancel, add_zero]`. Conclude with `w.asIdeal.mul_mem_right _ ha`.

Establish `hnd : ¬ (q : ℤ) ∣ 2 * d`. Introduce `h`. Apply `h2d` to reduce the goal to its premises. Use `(intCast_mem_iff w hp (2 * d)).2 (by rw [hpq]; exact h)` as an intermediate fact. Simplify using `using this`.

Establish `hqz : Prime (q : ℤ)` using `Nat.prime_iff_prime_int.1 hq`. Use `haveI : Fact q.Prime := ⟨hq⟩`. Use `isSquare_neg_padic q d a h1 fun h => ?_` and prove the remaining obligations. Break down `hqz.dvd_or_dvd h with h' | h'` into its components or cases. Conclude with `hnd (dvd_mul_of_dvd_left h' _)`.

Apply `hnd` to reduce the goal to its premises. Use `dvd_mul_of_dvd_right ?_ _` and prove the remaining obligations. Establish `h3 : (q : ℤ) ∣ a ^ 2` using `dvd_pow h' two_ne_zero`. Use `(Int.dvd_add_right h3).1 h1` as an intermediate fact. Conclude with `this`.
-/
theorem usPl_of_absNorm_prime {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : ImQ E d)
    (w : HeightOneSpectrum (𝓞 E)) (hp : (Ideal.absNorm w.asIdeal).Prime)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (h2d : ((2 * d : ℕ) : 𝓞 E) ∉ w.asIdeal) : UsPl d w := by
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  refine ⟨GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w hf he, fun q hq hqw => ?_⟩
  have hqw' : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal := by rwa [Int.cast_natCast]
  have hpq : Ideal.absNorm w.asIdeal = q := by
    have := (intCast_mem_iff w hp q).1 hqw'
    exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 this)
  obtain ⟨-, x, hx⟩ := hd
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hx]
    have : -(d : E) = algebraMap ℤ E (-(d : ℤ)) := by simp
    rw [this]; exact isIntegral_algebraMap
  let y : 𝓞 E := ⟨x, hi⟩
  have hy : y ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  obtain ⟨a, ha⟩ := exists_int_sub_mem w hp y
  have h1 : ((q : ℤ) : ℤ) ∣ a ^ 2 + d := by
    rw [← hpq]
    refine (intCast_mem_iff w hp _).1 ?_
    have : (((a ^ 2 + d : ℤ)) : 𝓞 E) = (y - a) * (-(y + a)) + (y ^ 2 + d) := by push_cast; ring
    rw [this, hy, neg_add_cancel, add_zero]
    exact w.asIdeal.mul_mem_right _ ha
  have hnd : ¬ (q : ℤ) ∣ 2 * d := by
    intro h
    apply h2d
    have := (intCast_mem_iff w hp (2 * d)).2 (by rw [hpq]; exact h)
    simpa using this
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  haveI : Fact q.Prime := ⟨hq⟩
  refine isSquare_neg_padic q d a h1 fun h => ?_
  rcases hqz.dvd_or_dvd h with h' | h'
  · exact hnd (dvd_mul_of_dvd_left h' _)
  · apply hnd
    refine dvd_mul_of_dvd_right ?_ _
    have h3 : (q : ℤ) ∣ a ^ 2 := dvd_pow h' two_ne_zero
    have := (Int.dvd_add_right h3).1 h1
    exact this

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Use `push_cast`. Conclude with `w.asIdeal.mul_mem_right _ hn`.
-/
theorem natCast_mem_of_dvd {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n M : ℕ}
    (h : n ∣ M) (hn : (n : 𝓞 E) ∈ w.asIdeal) : (M : 𝓞 E) ∈ w.asIdeal := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact w.asIdeal.mul_mem_right _ hn

/- English proof (translation)
Establish `hu : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal` using `Ideal.absNorm_mem u.asIdeal`. Establish `h'` using `congrArg HeightOneSpectrum.asIdeal h`. Simplify using `only [HeightOneSpectrum.under_asIdeal] at h'`. Establish `hm : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal.under (𝓞 (maximalRealSubfield E))`. Rewrite using `[Ideal.under, Ideal.mem_comap, map_natCast]`.

Conclude with `hu`. Rewrite `hm` using `[← h', Ideal.under, Ideal.mem_comap, map_natCast]`. Conclude with `hm`.
-/
theorem absNorm_mem_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w u : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hu : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem u.asIdeal
  have h' := congrArg HeightOneSpectrum.asIdeal h
  simp only [HeightOneSpectrum.under_asIdeal] at h'
  have hm : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hu
  rw [← h', Ideal.under, Ideal.mem_comap, map_natCast] at hm
  exact hm

end GlobalTheory.DenseUsable
