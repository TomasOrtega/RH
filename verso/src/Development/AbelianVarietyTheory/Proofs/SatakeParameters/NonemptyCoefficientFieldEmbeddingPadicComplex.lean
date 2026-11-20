import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ G hV`. Set `v : Fin G.P.nV` to `⟨0, hV⟩`. Establish `S` using `G.P.setting v`. Use `haveI := S.frac_alt`. Use `haveI := S.frac_O`.

Use `haveI : IsAdicComplete (maximalIdeal G.O) G.O := S.complete_O`. Use `haveI hW0 : CharZero (G.P.W v) := by`. Take `⟨l, hl⟩` from `CharP.exists (G.P.W v)`. Break down `CharP.char_is_prime_or_zero (G.P.W v) l with hlp | hl0` into its components or cases. It suffices to derive a contradiction.

Distinguish the cases in `hlpe : l = p`. Substitute `hlpe` using the available equality. Conclude with `S.p_unif.ne_zero (CharP.cast_eq_zero _ l)`. Establish `hcop : Nat.Coprime p l` using `(Nat.coprime_primes (Fact.out) hlp).2 (Ne.symm hlpe)`. Establish `h` using `Nat.gcd_eq_gcd_ab p l`.

Rewrite `h` using `[hcop]`. Establish `h'` using `congrArg (fun z : ℤ => (z : G.P.W v)) h`. Simplify using `only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul, add_zero] at h'`. Conclude with `S.p_unif.not_isUnit (IsUnit.of_mul_eq_one _ h'.symm)`. Substitute `hl0` using the available equality.

Conclude with `CharP.charP_to_charZero _`. Use `haveI : CharZero (G.P.Qq v) := (RingHom.charZero_iff (IsFractionRing.injective (G.P.W v) (G.P.Qq v))).1 hW0`. Use `haveI : CharZero G.Kf := (RingHom.charZero_iff (G.P.ι v).injective).1 inferInstance`. Use `letI : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra`. Use `haveI : Module.Finite (G.P.W v) G.O := S.finite`.

Establish `hcomap : (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) = Ideal.span {(p : G.P.W v)}`. Establish `hmax : ((maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _`. Rewrite using `[IsLocalRing.eq_maximalIdeal hmax, S.p_unif.maximalIdeal_eq]`. Establish `hpO : (p : G.O) ∈ maximalIdeal G.O`. Establish `: (p : G.P.W v) ∈ (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)` using `hcomap ▸ Ideal.subset_span rfl`.

Simplify using `using this`. Use `haveI : Finite (ResidueField (G.P.W v)) := by`. Establish `h` using `S.res_card`. Rewrite `h` using `[← S.p_unif.maximalIdeal_eq]`. Conclude with `Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)`.

Use `haveI : Finite (ResidueField G.O) := by haveI : Module.Finite (G.P.W v) (ResidueField G.O) := inferInstance haveI : Algebra.IsIntegral (G.P.W v) (ResidueField G.O) := inferInstance`. Conclude with `Module.finite_of_finite (ResidueField (G.P.W v))`. Take `⟨p', hp', K₀, e, e₀, hfd, he⟩` from `exists_ringEquiv_integralClosure_padicInt G.O G.Kf`. Establish `hpp : p' = p`. Establish `h1 : e₀ (p : G.O) ∈ maximalIdeal (integralClosure ℤ_[p'] K₀)`.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `(mem_maximalIdeal _).1 hpO (by simpa using hu.map e₀.symm)`. Rewrite `h1` using `[mem_maximalIdeal_integralClosure_iff, map_natCast]`. Establish `h2 : (((p : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') = algebraMap ℚ_[p'] (PadicAlgCl p') p` using `by simp`.

Rewrite `h1` using `[h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff]`. Conclude with `(Nat.prime_dvd_prime_iff_eq hp'.out Fact.out).1 h1`. Substitute `hpp` using the available equality. Use `⟨⟨(algebraMap (PadicAlgCl p') ℂ_[p']).comp (K₀.val.toRingHom.comp e.toRingHom), fun x => ?_⟩⟩` and prove the remaining obligations. Establish `hx : ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p') = (((e₀ x : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p')`.

Rewrite using `[he x]`. Simplify using `only [RingHom.comp_apply]`. Use `show ‖algebraMap (PadicAlgCl p') ℂ_[p'] ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p')‖ ≤ 1`. Rewrite using `[hx, ← PadicComplex.coe_eq, PadicComplex.norm_extends]`. Conclude with `(mem_integralClosure_padicInt_iff K₀ _).1 (e₀ x).2`.
-/
theorem nonempty_cEmb_of_pos_nV : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV →
    Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  intro p _ G hV
  let v : Fin G.P.nV := ⟨0, hV⟩
  have S := G.P.setting v
  haveI := S.frac_alt
  haveI := S.frac_O
  haveI : IsAdicComplete (maximalIdeal G.O) G.O := S.complete_O

  haveI hW0 : CharZero (G.P.W v) := by
    obtain ⟨l, hl⟩ := CharP.exists (G.P.W v)
    rcases CharP.char_is_prime_or_zero (G.P.W v) l with hlp | hl0
    · exfalso
      by_cases hlpe : l = p
      · subst hlpe
        exact S.p_unif.ne_zero (CharP.cast_eq_zero _ l)
      · have hcop : Nat.Coprime p l := (Nat.coprime_primes (Fact.out) hlp).2 (Ne.symm hlpe)
        have h := Nat.gcd_eq_gcd_ab p l
        rw [hcop] at h
        have h' := congrArg (fun z : ℤ => (z : G.P.W v)) h
        simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h'
        exact S.p_unif.not_isUnit (IsUnit.of_mul_eq_one _ h'.symm)
    · subst hl0
      exact CharP.charP_to_charZero _
  haveI : CharZero (G.P.Qq v) :=
    (RingHom.charZero_iff (IsFractionRing.injective (G.P.W v) (G.P.Qq v))).1 hW0
  haveI : CharZero G.Kf := (RingHom.charZero_iff (G.P.ι v).injective).1 inferInstance

  letI : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra
  haveI : Module.Finite (G.P.W v) G.O := S.finite
  have hcomap : (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) = Ideal.span {(p : G.P.W v)} := by
    have hmax : ((maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    rw [IsLocalRing.eq_maximalIdeal hmax, S.p_unif.maximalIdeal_eq]
  have hpO : (p : G.O) ∈ maximalIdeal G.O := by
    have : (p : G.P.W v) ∈ (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) :=
      hcomap ▸ Ideal.subset_span rfl
    simpa using this

  haveI : Finite (ResidueField (G.P.W v)) := by
    have h := S.res_card
    rw [← S.p_unif.maximalIdeal_eq] at h
    exact Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Finite (ResidueField G.O) := by
    haveI : Module.Finite (G.P.W v) (ResidueField G.O) := inferInstance
    haveI : Algebra.IsIntegral (G.P.W v) (ResidueField G.O) := inferInstance
    exact Module.finite_of_finite (ResidueField (G.P.W v))

  obtain ⟨p', hp', K₀, e, e₀, hfd, he⟩ := exists_ringEquiv_integralClosure_padicInt G.O G.Kf
  have hpp : p' = p := by
    have h1 : e₀ (p : G.O) ∈ maximalIdeal (integralClosure ℤ_[p'] K₀) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hpO (by simpa using hu.map e₀.symm)
    rw [mem_maximalIdeal_integralClosure_iff, map_natCast] at h1
    have h2 : (((p : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') =
        algebraMap ℚ_[p'] (PadicAlgCl p') p := by simp
    rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp'.out Fact.out).1 h1
  subst hpp

  refine ⟨⟨(algebraMap (PadicAlgCl p') ℂ_[p']).comp (K₀.val.toRingHom.comp e.toRingHom), fun x => ?_⟩⟩
  have hx : ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p') = (((e₀ x : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') := by
    rw [he x]
  simp only [RingHom.comp_apply]
  show ‖algebraMap (PadicAlgCl p') ℂ_[p'] ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p')‖ ≤ 1
  rw [hx, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  exact (mem_integralClosure_padicInt_iff K₀ _).1 (e₀ x).2
end GlobalTheory
