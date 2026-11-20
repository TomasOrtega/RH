import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartAPf

variable {B : Type} [CommRing B]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem one_mem_S (I : Ideal B) {e : B ⧸ I} {u : B} (hu : Ideal.Quotient.mk I u = e) (he : IsIdempotentElem e) :
    u ∈ S I e := ⟨1, by rw [hu, mul_one, he.eq]⟩

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_map_of_comp (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P)
    (hz : ∀ e : P.1, z e ∈ I.map (algebraMap B (Localization (S I e.1)))) : z ∈ I.map (βP I P) := by
  classical
  choose a ha using fun e : P.1 =>
    (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 (hz e)
  have key : z = ∑ e : P.1, βP I P ((a e).1 : B) *
      Pi.single e (IsLocalization.mk' (Localization (S I e.1)) (1 : B) (a e).2) := by
    funext e'
    rw [Finset.sum_apply, Finset.sum_eq_single e']
    · simp only [Pi.mul_apply, Pi.single_eq_same, βP, RingHom.pi_apply]
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
      exact ha e'
    · intro e _ hne
      simp [Pi.single_eq_of_ne' hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a e).1.2)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem comp_mem (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P) (hz : z ∈ I.map (βP I P)) (e : P.1) :
    z e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h := Ideal.mem_map_of_mem (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) hz
  rw [Ideal.map_map] at h
  exact h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem sum_mul_single (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (c : P.1 → B ⧸ I) (e' : P.1) :
    (∑ e : P.1, c e * e.1) * e'.1 = c e' * e'.1 := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single e']
  · rw [mul_assoc, (P.idem e'.1 e'.2).1.eq]
  · intro e _ hne
    rw [mul_assoc, P.orth e.1 e.2 e'.1 e'.2 (fun h => hne (Subtype.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem PartA_of : PartA := by
  intro B _ I P
  classical
  constructor
  · apply Ideal.quotientMap_injective'
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcomp : ∀ e : P.1, Ideal.Quotient.mk I x * e.1 = 0 := by
      intro e
      have h := comp_mem I P _ hx e
      obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 h
      simp only [βP, RingHom.pi_apply] at hs
      rw [← map_mul] at hs
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (S I e.1) (Localization (S I e.1))).1 hs
      have hq := congrArg (Ideal.Quotient.mk I) hc
      rw [map_mul, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 i.2, mul_zero] at hq
      obtain ⟨t, ht⟩ := c.2
      obtain ⟨t', ht'⟩ := s.2
      calc Ideal.Quotient.mk I x * e.1
          = Ideal.Quotient.mk I x * ((Ideal.Quotient.mk I c * t * e.1) * (Ideal.Quotient.mk I s * t' * e.1)) := by
            rw [ht, ht', (P.idem e.1 e.2).1.eq]
        _ = (Ideal.Quotient.mk I c * (Ideal.Quotient.mk I x * Ideal.Quotient.mk I s)) * (t * t' * e.1 * e.1) := by ring
        _ = 0 := by rw [hq, zero_mul]
    calc Ideal.Quotient.mk I x = Ideal.Quotient.mk I x * ∑ e ∈ P.1, e := by rw [P.sum_eq, mul_one]
      _ = ∑ e : P.1, Ideal.Quotient.mk I x * e.1 := by
          rw [Finset.mul_sum, ← Finset.sum_coe_sort P.1]
      _ = 0 := Finset.sum_eq_zero fun e _ => hcomp e
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hB : ∀ e : P.1, ∃ (b : B) (s : S I e.1), IsLocalization.mk' (Localization (S I e.1)) b s = y e :=
      fun e => by
        obtain ⟨⟨b, s⟩, h⟩ := IsLocalization.mk'_surjective (S I e.1) (y e)
        exact ⟨b, s, h⟩
    choose b s hbs using hB
    have hS : ∀ e : P.1, ∃ t, Ideal.Quotient.mk I (s e : B) * t * e.1 = e.1 := fun e => (s e).2
    choose t ht using hS
    choose τ hτ using fun e : P.1 => Ideal.Quotient.mk_surjective (t e)
    choose ε hε using fun e : P.1 => Ideal.Quotient.mk_surjective e.1
    refine ⟨Ideal.Quotient.mk _ (∑ e : P.1, b e * τ e * ε e), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    apply mem_map_of_comp
    intro e'
    set x := ∑ e : P.1, b e * τ e * ε e
    have hεS : ε e' ∈ S I e'.1 := one_mem_S I (hε e') (P.idem e'.1 e'.2).1
    rw [IsLocalization.mem_map_algebraMap_iff (S I e'.1) (Localization (S I e'.1))]
    refine ⟨⟨⟨(x * s e' - b e') * ε e', ?_⟩, s e' * ⟨ε e', hεS⟩⟩, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_mul, hε]
      have hx : Ideal.Quotient.mk I x = ∑ e : P.1, (Ideal.Quotient.mk I (b e) * t e) * e.1 := by
        simp only [x, map_sum, map_mul, hτ, hε]
      rw [sub_mul, mul_right_comm, hx, sum_mul_single]
      calc Ideal.Quotient.mk I (b e') * t e' * e'.1 * Ideal.Quotient.mk I (s e') - Ideal.Quotient.mk I (b e') * e'.1
          = Ideal.Quotient.mk I (b e') * (Ideal.Quotient.mk I (s e') * t e' * e'.1) - Ideal.Quotient.mk I (b e') * e'.1 := by ring
        _ = 0 := by rw [ht e', sub_self]
    · simp only [Pi.sub_apply, βP, RingHom.pi_apply, Submonoid.coe_mul, map_mul, map_sub, ← hbs e']
      rw [sub_mul, sub_mul, ← mul_assoc (IsLocalization.mk' _ _ _), IsLocalization.mk'_spec]
      ring

end LateralTheory.E.PartAPf
