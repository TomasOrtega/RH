import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormNatEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CompleteDvrToComplex

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ`. Rewrite `ha` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n` from `Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)`. Establish `h : ‖g a‖ ^ n < 1`.

Rewrite using `[← norm_pow, ← map_pow, hc, map_mul, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)`. Conclude with `lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)`.
-/
theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ IsLocalRing.maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

/- English proof (translation)
Establish `hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖`. Rewrite using `[PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]`. Rewrite using `[← hv]`. Establish `: Valued.v (x : ℂ_[p]) ≤ 1` using `x.2`. Conclude with `this` after adjusting the coercions.
-/
theorem norm_le_one_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' p (p : ℚ_[p])`. Establish `hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p])` using `by push_cast; rfl`. Rewrite `h` using `[hc]`. Rewrite using `[h]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; rfl
  rw [hc] at h
  rw [h]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Introduce `V _ _ _ _ hc hf`. Set `T : Formalism.L2.Pj.CDVR` to `{ V := V }`. Take `⟨p, hp, k, kO, hk⟩` from `GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf`. Use `letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra`. Take `⟨eC⟩` from `GlobalTheory.MomOne.Inh.nonempty_iso p`.

Use `⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩` and prove the remaining obligations. Establish `hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1` using `fun r => by`. Rewrite using `[← hk r]`. Conclude with `norm_le_one_padicComplexInt p (kO r)`. Conclude with `hle`.

Establish `hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1` using `fun r => by`. Rewrite using `[RingHom.comp_apply, ← hk r]`. Conclude with `norm_le_one_padicComplexInt p (kO r)`. Establish `hp0 : (p : V) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`. Establish `hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1`.

Rewrite using `[map_natCast]`. Conclude with `norm_natCast_prime_lt_one p`. Introduce `r hr`. Conclude with `norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr`.
-/
theorem exists_complete_closed_field :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hc hf
  let T : Formalism.L2.Pj.CDVR := { V := V }
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf
  letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra
  obtain ⟨eC⟩ := GlobalTheory.MomOne.Inh.nonempty_iso p
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩
  · have hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1 := fun r => by
      rw [← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    exact hle
  · have hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1 := fun r => by
      rw [RingHom.comp_apply, ← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1 := by
      rw [map_natCast]; exact norm_natCast_prime_lt_one p
    intro r hr
    exact norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr

end GlobalTheory.CompleteDvrToComplex
