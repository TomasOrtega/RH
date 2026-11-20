import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem eq_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.HF.Formalism.HC.HostAx.isRt_eq_one_of_sub_mem :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.muW → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P →
      ∀ ξ ξ' : 𝓞 H.E, H.IsRt (ξ : H.E) → H.IsRt (ξ' : H.E) → ξ - ξ' ∈ P → ξ = ξ' := by
  intro φ H p hp hpw P hP hpP ξ ξ' hξ hξ' hsub
  have key : ∀ x : 𝓞 H.E, H.IsRt (x : H.E) → x ^ H.muW = 1 := by
    intro x hx
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact (H.isRt_iff _).1 hx
  have hw : ((H.muW : ℕ) : 𝓞 H.E) ∉ P := by
    intro h
    have hc : IsCoprime ((p : ℕ) : 𝓞 H.E) ((H.muW : ℕ) : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hpw)
    obtain ⟨a, b, hab⟩ := hc
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.add_mem (P.mul_mem_left a hpP) (P.mul_mem_left b h)
  exact eq_of_pow_eq_one_of_sub_mem P hw (key ξ hξ) (key ξ' hξ') hsub
