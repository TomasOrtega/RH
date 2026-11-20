import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt.Res

open GlobalTheory.CMVal.PicFin

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mk_eq_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) (z a : intR E) :
    Ideal.Quotient.mk (Ideal.span {(N : intR E)}) z = Ideal.Quotient.mk _ a ↔
      ∀ w, Valued.v (z.1 w - a.1 w) ≤ radN E N w := by
  have hn0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨β, hβ⟩ w
    have h3 : z.1 - a.1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : z.1 w - a.1 w = algebraMap E (w.adicCompletion E) (N : E) * β.1 w := congrArg (fun y : Af E => y w) h3
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  · intro hz
    refine ⟨⟨algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1), fun P => ?_⟩, Subtype.ext ?_⟩
    · have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hN
      show Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹ * (z.1 P - a.1 P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
    · show z.1 - a.1 = (N : Af E) * (algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1))
      rw [← map_natCast (algebraMap E (Af E)), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_residues : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E),
    (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) →
      ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  classical
  intro E _ _ N hN
  haveI := finite_quot (E := E) hN.ne'
  haveI := Fintype.ofFinite (intR E ⧸ Ideal.span {(N : intR E)})
  choose s hs using Ideal.Quotient.mk_surjective (I := Ideal.span {(N : intR E)})
  refine ⟨Finset.univ.image fun q => (s q).1, fun a ha w => ?_, fun z hz => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((s q).2 w)
  · let z' : intR E := ⟨z, fun w => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz w)⟩
    refine ⟨(s (Ideal.Quotient.mk _ z')).1, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (mk_eq_iff hN z' _).1 (hs _).symm⟩, ?_⟩
    rintro a ⟨ha, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    rw [(mk_eq_iff hN z' (s q)).2 h, hs]

end GlobalTheory.CMVal.LatEnt.Res
