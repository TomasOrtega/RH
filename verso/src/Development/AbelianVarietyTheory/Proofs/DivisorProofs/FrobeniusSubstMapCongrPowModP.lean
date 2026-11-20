import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FrobCong

/- English proof (translation)
Establish `hp : p ≠ 0` using `hpf.out.ne_zero`. Use `set I : Ideal B := Ideal.span {(p : B)} with hI`. Use `set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ`. Establish `hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) = expand p hp (map σB g)`. Rewrite using `[expand, substAlgHom_apply]`.

Rewrite using `[hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ, ← coeff_map, map_sub, map_pow, map_expand, map_map]`. Break down `subsingleton_or_nontrivial (B ⧸ I) with hs | hs` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `hp0 : ((p : ℕ) : B ⧸ I) = 0`. Establish `h1 : π (p : B) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`.

Rewrite `h1` using `[map_natCast]`. Then use the resulting hypothesis. Use `haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0`. Use `haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out`. Establish `hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π`. Use extensionality with `b`.

Simplify using `only [RingHom.comp_apply, frobenius_def]`. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton.2 (hσ b)`. Rewrite using `[hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]`.
-/
theorem frobenius_congr (p : ℕ) [hpf : Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B)
    (hσ : ∀ b, (p : B) ∣ σB b - b ^ p) (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ) :
    (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  have hp : p ≠ 0 := hpf.out.ne_zero
  set I : Ideal B := Ideal.span {(p : B)} with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g)
      = expand p hp (map σB g) := by
    rw [expand, substAlgHom_apply]
  rw [hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ,
    ← coeff_map, map_sub, map_pow, map_expand, map_map]
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hs
  · exact Subsingleton.elim _ _
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    have h1 : π (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rwa [map_natCast] at h1
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out
  have hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCong
