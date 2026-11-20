import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfCore

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO.EighthRoots

section Quartic

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (σ : E ≃ₐ[ℚ] E)

@[reducible] def quarticFields : Fields where
  F := maximalRealSubfield E
  E := E
  K := E
  starE := IsCMField.starRing E
  starK := IsCMField.starRing E
  Tau := Bool
  emb := fun b => if b then (σ : E →+* E) else RingHom.id E

def conj : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E x`.
-/
theorem conj_conj (x : E) : conj E (conj E x) = x := IsCMField.complexConj_apply_apply E x

/- English proof (translation)
Introduce `h` and use `IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)`.
-/
theorem conj_ne_one : conj E ≠ 1 := fun h =>
  IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h true false`. Introduce `h a b`. Apply the tactic sequence `cases a <;> cases b`.

Both sides reduce to the same expression. Conclude with `h.symm`. Conclude with `h`. Both sides reduce to the same expression.
-/
theorem mem_Kq (x : E) : x ∈ (quarticFields E σ).Kq ↔ σ x = x := by
  constructor
  · intro h
    exact h true false
  · intro h a b
    cases a <;> cases b
    · rfl
    · exact h.symm
    · exact h
    · rfl

/- English proof (translation)
Establish `hr : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hcc : conj E * conj E = 1` using `AlgEquiv.ext (conj_conj E)`. Establish `hσc1 : σ * conj E ≠ 1` using `fun h => hc (by rw [← mul_one σ, ← hcc, ← mul_assoc, h, one_mul])`. Establish `hσc2 : σ * conj E ≠ σ` using `fun h => conj_ne_one E (by simpa using h)`. Establish `hσc3 : σ * conj E ≠ conj E` using `fun h => h1 (by simpa using h)`.

Use `{ realF := inferInstanceAs (IsTotallyReal (maximalRealSubfield E)) rankE := hr star_F := fun x => IsCMField.complexConj_apply_eq_self E x conjE := fun φ x => IsCMField.complexEmbedding_complexConj E φ x cplxE := inferInstanceAs (IsTotallyComplex E) emb_star := fun b x => ?_ card_ …` and prove the remaining obligations. Consider the cases of `b`. Both sides reduce to the same expression. Conclude with `AlgEquiv.congr_fun (hab σ (conj E)) x`. Use `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E` as an intermediate fact.

Rewrite `this` using `[hr, h4]`. Express the relevant statement in the definitionally equal form `Fintype.card Bool = Module.finrank ℚ (maximalRealSubfield E)`. Rewrite using `[Fintype.card_bool]`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `cases a <;> cases b`.

Both sides reduce to the same expression. Conclude with `absurd (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm) h1`. Conclude with `absurd (AlgEquiv.ext fun x => RingHom.congr_fun h x) h1`. Both sides reduce to the same expression. Apply the tactic sequence `cases a <;> cases b`.

Conclude with `conj_ne_one E (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)`. Conclude with `hσc1 (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)`. Conclude with `hc (AlgEquiv.ext fun x => RingHom.congr_fun h x)`. Conclude with `hσc2 (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)`. Set `g : E ≃ₐ[ℚ] E` to `AlgEquiv.ofBijective φ.toRatAlgHom (Algebra.IsAlgebraic.algHom_bijective _)`.

Establish `hcard : Fintype.card (E ≃ₐ[ℚ] E) = 4`. Rewrite using `[← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h4]`. Establish `hu : ({1, σ, conj E, σ * conj E} : Finset (E ≃ₐ[ℚ] E)) = Finset.univ`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[hcard, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hσc3.symm]`.

Simplify using `[hc, hσc2.symm]`. Simplify using `[h1.symm, (conj_ne_one E).symm, hσc1.symm]`. Establish `hg : g ∈ ({1, σ, conj E, σ * conj E} : Finset (E ≃ₐ[ℚ] E))` using `hu ▸ Finset.mem_univ g`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hg`. Break down `hg with h | h | h | h` into its components or cases.

Conclude with `⟨false, Or.inl (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩`. Conclude with `⟨true, Or.inl (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩`. Conclude with `⟨false, Or.inr (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩`. Conclude with `⟨true, Or.inr (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩`. Establish `ho : orderOf σ = 2` using `orderOf_eq_prime (by rw [pow_two, h2]) h1`.

Establish `hM` using `IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)`. Rewrite `hM` using `[Nat.card_zpowers, ho]`. Establish `ht` using `Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)) E`. Rewrite `ht` using `[hM, h4]`. Establish `he : (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield = (quarticFields E σ).Kq`.

Use extensionality with `x`. Rewrite using `[mem_Kq, IntermediateField.mem_toSubfield, IntermediateField.mem_fixedField_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h σ (Subgroup.mem_zpowers σ)`. Introduce `h f hf`.

Conclude with `(Subgroup.zpowers_le (H := MulAction.stabilizer (E ≃ₐ[ℚ] E) x)).2 h hf`. Establish `h3 : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield = 2`. Express the relevant statement in the definitionally equal form `Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)) = 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← he]`.

Conclude with `h3`.
-/
theorem quarticFields_ok [IsGalois ℚ E] (hab : ∀ s t : E ≃ₐ[ℚ] E, s * t = t * s) (h4 : Module.finrank ℚ E = 4)
    (h1 : σ ≠ 1) (h2 : σ * σ = 1) (hc : σ ≠ conj E) : (quarticFields E σ).Ok := by
  classical
  have hr : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hcc : conj E * conj E = 1 := AlgEquiv.ext (conj_conj E)
  have hσc1 : σ * conj E ≠ 1 := fun h => hc (by rw [← mul_one σ, ← hcc, ← mul_assoc, h, one_mul])
  have hσc2 : σ * conj E ≠ σ := fun h => conj_ne_one E (by simpa using h)
  have hσc3 : σ * conj E ≠ conj E := fun h => h1 (by simpa using h)
  refine
    { realF := inferInstanceAs (IsTotallyReal (maximalRealSubfield E))
      rankE := hr
      star_F := fun x => IsCMField.complexConj_apply_eq_self E x
      conjE := fun φ x => IsCMField.complexEmbedding_complexConj E φ x
      cplxE := inferInstanceAs (IsTotallyComplex E)
      emb_star := fun b x => ?_
      card_Tau := ?_
      emb_inj := fun a b h => ?_
      emb_ne := fun a b h => ?_
      emb_all := fun φ => ?_
      cplxK := inferInstanceAs (IsTotallyComplex E)
      normalK := inferInstanceAs (Normal ℚ E)
      conjK := ⟨Classical.arbitrary (E →+* ℂ), fun x => IsCMField.complexEmbedding_complexConj E _ x⟩
      quad := ?_ }
  · cases b
    · rfl
    · exact AlgEquiv.congr_fun (hab σ (conj E)) x
  · have := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [hr, h4] at this
    change Fintype.card Bool = Module.finrank ℚ (maximalRealSubfield E)
    rw [Fintype.card_bool]
    omega
  · cases a <;> cases b
    · rfl
    · exact absurd (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm) h1
    · exact absurd (AlgEquiv.ext fun x => RingHom.congr_fun h x) h1
    · rfl
  · cases a <;> cases b
    · exact conj_ne_one E (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)
    · exact hσc1 (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)
    · exact hc (AlgEquiv.ext fun x => RingHom.congr_fun h x)
    · exact hσc2 (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)
  · let g : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective φ.toRatAlgHom (Algebra.IsAlgebraic.algHom_bijective _)
    have hcard : Fintype.card (E ≃ₐ[ℚ] E) = 4 := by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h4]
    have hu : ({1, σ, conj E, σ * conj E} : Finset (E ≃ₐ[ℚ] E)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hσc3.symm]
      · simp [hc, hσc2.symm]
      · simp [h1.symm, (conj_ne_one E).symm, hσc1.symm]
    have hg : g ∈ ({1, σ, conj E, σ * conj E} : Finset (E ≃ₐ[ℚ] E)) := hu ▸ Finset.mem_univ g
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with h | h | h | h
    · exact ⟨false, Or.inl (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩
    · exact ⟨true, Or.inl (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩
    · exact ⟨false, Or.inr (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩
    · exact ⟨true, Or.inr (RingHom.ext fun x => AlgEquiv.congr_fun h x)⟩
  · have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two, h2]) h1
    have hM := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers, ho] at hM
    have ht := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)) E
    rw [hM, h4] at ht
    have he : (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield = (quarticFields E σ).Kq := by
      ext x
      rw [mem_Kq, IntermediateField.mem_toSubfield, IntermediateField.mem_fixedField_iff]
      constructor
      · exact fun h => h σ (Subgroup.mem_zpowers σ)
      · intro h f hf
        exact (Subgroup.zpowers_le (H := MulAction.stabilizer (E ≃ₐ[ℚ] E) x)).2 h hf
    have h3 : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield = 2 := by
      change Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers σ)) = 2
      omega
    rw [← he]
    exact h3

end Quartic

/- English proof (translation)
Establish `hp : Nat.Prime 11` using `by norm_num`. Establish `hn : Ideal.absNorm (Ideal.span {((11 : ℕ) : 𝓞 M)}) = 11 ^ 2`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, hM]`. Establish `hne : Ideal.span {((11 : ℕ) : 𝓞 M)} ≠ ⊤` using `fun h => by`. Rewrite `hn` using `[h, Ideal.absNorm_top]`.

Evaluate the numerical expressions using `at hn`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hmul : 11 ^ 2 = Ideal.absNorm P * Ideal.absNorm J` using `by rw [← hn, hJ, map_mul]`. Take `⟨k, hk, hPk⟩` from `(Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩`.

Use `interval_cases k`. Conclude with `absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hPk)) hP.ne_top`. It suffices to derive a contradiction. Establish `hint : IsIntegral ℤ i` using `IsIntegral.of_pow (n := 2) (by norm_num) (hi ▸ isIntegral_one.neg)`. Set `j : 𝓞 M` to `⟨i, hint⟩`.

Establish `hj : j ^ 2 = -1` using `RingOfIntegers.ext hi`. Establish `hc : Nat.card (𝓞 M ⧸ P) = 11`. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk, pow_one]`. Use `haveI : Finite (𝓞 M ⧸ P) := Nat.finite_of_card_ne_zero (by omega)`. Use `letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _`.

Use `letI : Field (𝓞 M ⧸ P) := Ideal.Quotient.field P`. Establish `hs : IsSquare (-1 : 𝓞 M ⧸ P)` using `⟨Ideal.Quotient.mk P j, by rw [← map_mul, ← pow_two, hj, map_neg, map_one]⟩`. Rewrite `hs` using `[FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hc]`. Conclude with `hs rfl`. Rewrite `hmul` using `[hPk]`.

Establish `: J = ⊤` using `Ideal.absNorm_eq_one_iff.1 (by omega)`. Rewrite using `[hJ, this, Ideal.mul_top]`. Conclude with `hP.isPrime`.
-/
theorem isPrime_eleven (M : Type) [Field M] [NumberField M] (hM : Module.finrank ℚ M = 2) (i : M) (hi : i ^ 2 = -1) :
    (Ideal.span {((11 : ℕ) : 𝓞 M)}).IsPrime := by
  have hp : Nat.Prime 11 := by norm_num
  have hn : Ideal.absNorm (Ideal.span {((11 : ℕ) : 𝓞 M)}) = 11 ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hM]
  have hne : Ideal.span {((11 : ℕ) : 𝓞 M)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    norm_num at hn
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmul : 11 ^ 2 = Ideal.absNorm P * Ideal.absNorm J := by rw [← hn, hJ, map_mul]
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩
  interval_cases k
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hPk)) hP.ne_top
  · exfalso
    have hint : IsIntegral ℤ i := IsIntegral.of_pow (n := 2) (by norm_num) (hi ▸ isIntegral_one.neg)
    let j : 𝓞 M := ⟨i, hint⟩
    have hj : j ^ 2 = -1 := RingOfIntegers.ext hi
    have hc : Nat.card (𝓞 M ⧸ P) = 11 := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk, pow_one]
    haveI : Finite (𝓞 M ⧸ P) := Nat.finite_of_card_ne_zero (by omega)
    letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
    letI : Field (𝓞 M ⧸ P) := Ideal.Quotient.field P
    have hs : IsSquare (-1 : 𝓞 M ⧸ P) :=
      ⟨Ideal.Quotient.mk P j, by rw [← map_mul, ← pow_two, hj, map_neg, map_one]⟩
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hc] at hs
    exact hs rfl
  · rw [hPk] at hmul
    have : J = ⊤ := Ideal.absNorm_eq_one_iff.1 (by omega)
    rw [hJ, this, Ideal.mul_top]
    exact hP.isPrime

/- English proof (translation)
Introduce `h`. Establish `hint : IsIntegral ℤ s` using `IsIntegral.of_pow (n := 2) (by norm_num) (by`. Rewrite using `[hs]`. Conclude with `isIntegral_algebraMap (R := ℤ) (A := E) (x := -2))` after adjusting the coercions. Set `t : 𝓞 E` to `⟨s, hint⟩`.

Establish `ht : t ^ 2 = -2` using `RingOfIntegers.ext hs`. Establish `hct : cO E t = -t` using `RingOfIntegers.ext hc`. Establish `h3 : cO E 3 = 3` using `map_ofNat _ 3`. Establish `hiff : 3 + t ∈ Q.asIdeal ↔ 3 - t ∈ Q.asIdeal` using `by conv_lhs => rw [h, mem_conjP, map_add, h3, hct, ← sub_eq_add_neg]`. Establish `hprod : (3 + t) * (3 - t) ∈ Q.asIdeal`.

Establish `: (3 + t) * (3 - t) = ((11 : ℕ) : 𝓞 E)` using `by push_cast; linear_combination -ht`. Rewrite using `[this]` and apply the resulting hypothesis. Establish `hboth : 3 + t ∈ Q.asIdeal ∧ 3 - t ∈ Q.asIdeal` using `(Q.isPrime.mem_or_mem hprod).elim (fun a => ⟨a, hiff.1 a⟩) fun a => ⟨hiff.2 a, a⟩`. Use `Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)` and prove the remaining obligations. Establish `: (1 : 𝓞 E) = 2 * ((3 + t) + (3 - t)) - ((11 : ℕ) : 𝓞 E)` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ (add_mem hboth.1 hboth.2)) hQ`.
-/
theorem ne_conjP_eleven (E : Type) [Field E] [NumberField E] [StarRing E] (s : E) (hs : s ^ 2 = -2) (hc : star s = -s)
    (Q : HeightOneSpectrum (𝓞 E)) (hQ : ((11 : ℕ) : 𝓞 E) ∈ Q.asIdeal) : Q ≠ conjPrime₂ Q := by
  intro h
  have hint : IsIntegral ℤ s := IsIntegral.of_pow (n := 2) (by norm_num) (by
    rw [hs]
    exact_mod_cast isIntegral_algebraMap (R := ℤ) (A := E) (x := -2))
  let t : 𝓞 E := ⟨s, hint⟩
  have ht : t ^ 2 = -2 := RingOfIntegers.ext hs
  have hct : cO E t = -t := RingOfIntegers.ext hc
  have h3 : cO E 3 = 3 := map_ofNat _ 3
  have hiff : 3 + t ∈ Q.asIdeal ↔ 3 - t ∈ Q.asIdeal := by
    conv_lhs => rw [h, mem_conjP, map_add, h3, hct, ← sub_eq_add_neg]
  have hprod : (3 + t) * (3 - t) ∈ Q.asIdeal := by
    have : (3 + t) * (3 - t) = ((11 : ℕ) : 𝓞 E) := by push_cast; linear_combination -ht
    rwa [this]
  have hboth : 3 + t ∈ Q.asIdeal ∧ 3 - t ∈ Q.asIdeal :=
    (Q.isPrime.mem_or_mem hprod).elim (fun a => ⟨a, hiff.1 a⟩) fun a => ⟨hiff.2 a, a⟩
  refine Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have : (1 : 𝓞 E) = 2 * ((3 + t) + (3 - t)) - ((11 : ℕ) : 𝓞 E) := by push_cast; ring
  rw [this]
  exact sub_mem (Ideal.mul_mem_left _ _ (add_mem hboth.1 hboth.2)) hQ

/- English proof (translation)
Set `E` to `CyclotomicField 8 ℚ`. Use `haveI hE : IsCyclotomicExtension {8} ℚ E := CyclotomicField.isCyclotomicExtension 8 ℚ`. Use `haveI : IsCMField E := IsCyclotomicExtension.Rat.isCMField E (S := {8}) ⟨8, rfl, by norm_num⟩`. Use `haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {8} ℚ E`. Establish `hab : ∀ s t : E ≃ₐ[ℚ] E, s * t = t * s` using `(IsCyclotomicExtension.isMulCommutative {8} ℚ E).is_comm.comm`.

Establish `hirr` using `Polynomial.cyclotomic.irreducible_rat (n := 8) (by norm_num)`. Establish `h4 : Module.finrank ℚ E = 4`. Rewrite using `[IsCyclotomicExtension.finrank (n := 8) E hirr]`. Evaluate the decidable proposition. Use `set ζ := IsCyclotomicExtension.zeta 8 ℚ E with hζdef`.

Establish `hζ : IsPrimitiveRoot ζ 8` using `IsCyclotomicExtension.zeta_spec 8 ℚ E`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (by norm_num)`. Establish `hz4 : ζ ^ 4 = -1` using `(hζ.pow (by norm_num) (show 8 = 4 * 2 by norm_num)).eq_neg_one_of_two_right`. Set `σ : E ≃ₐ[ℚ] E` to `IsCyclotomicExtension.fromZetaAut (hζ.pow_of_coprime 5 (by norm_num)) hirr`. Establish `hσ : σ ζ = -ζ`.

Rewrite using `[IsCyclotomicExtension.fromZetaAut_spec]`. Take the linear combination `ζ * hz4`. Establish `hcζ : conj E ζ = -ζ ^ 3`. Set `φ : E →+* ℂ` to `Classical.arbitrary _`. Establish `hn : ‖φ ζ‖ = 1` using `(hζ.map_of_injective φ.injective).norm'_eq_one (by norm_num)`.

Establish `h1 : conj E ζ = ζ⁻¹` using `φ.injective (by`. Rewrite using `[map_inv₀, Complex.inv_eq_conj hn]`. Conclude with `IsCMField.complexEmbedding_complexConj E φ ζ)`. Rewrite using `[h1]`. Conclude with `inv_eq_of_mul_eq_one_right (by linear_combination -hz4)`.

Establish `h1 : σ ≠ 1` using `fun h => hζ0 (by`. Rewrite `hσ` using `[h, AlgEquiv.one_apply]`. Take the linear combination `hσ / 2)`. Establish `h2 : σ * σ = 1` using `IsCyclotomicExtension.algEquiv_eq_of_apply_eq {8} ℚ E fun n hn _ => by`. Take `rfl : n = 8` from `hn`.

Conclude with `⟨ζ, hζ, by rw [AlgEquiv.mul_apply, hσ, map_neg, hσ, neg_neg, AlgEquiv.one_apply]⟩`. Establish `hc : σ ≠ conj E` using `fun h => by`. Rewrite `hσ` using `[h, hcζ]`. Establish `h5 : ζ ^ 2 = 1` using `mul_left_cancel₀ hζ0 (by linear_combination -hσ)`. Establish `: (2 : E) = 0` using `by linear_combination hz4 - (ζ ^ 2 + 1) * h5`.

Conclude with `two_ne_zero this`. Establish `hok` using `quarticFields_ok E σ hab h4 h1 h2 hc`. Use `⟨quarticFields E σ, hok, rfl, inferInstanceAs (IsGalois ℚ E), hab, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← NumberField.not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.1 (by norm_num)), Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr 8 E]`. Establish `h6 : Nat.primeFactors 8 = {2}` using `Nat.primeFactors_prime_pow (k := 3) (by norm_num) Nat.prime_two`.

Establish `h7 : Nat.totient 8 = 4` using `by decide`. Rewrite using `[h6, h7]`. Evaluate the numerical expressions. Use `haveI : FiniteDimensional ℚ (quarticFields E σ).Kq := Module.finite_of_finrank_pos (by rw [hok.quad]; norm_num) haveI : NumberField (quarticFields E σ).Kq := {}`. Use `isPrime_eleven _ hok.quad ⟨ζ ^ 2, (mem_Kq E σ _).2 (by rw [map_pow, hσ, neg_sq])⟩ (Subtype.ext ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(ζ ^ 2) ^ 2 = -1`. Take the linear combination `hz4`. Use `@ne_conjP_eleven E _ _ (IsCMField.starRing E) (ζ + ζ ^ 3) (by linear_combination (ζ ^ 2 + 2) * hz4) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `conj E (ζ + ζ ^ 3) = -(ζ + ζ ^ 3)`. Rewrite using `[map_add, map_pow, hcζ]`.

Take the linear combination `(-ζ ^ 5 + ζ) * hz4`.
-/
theorem exists_fields_ok_eleven :
    ∃ X : Fields, X.Ok ∧ X.f = 2 ∧ IsGalois ℚ X.E ∧ (∀ s t : X.E ≃ₐ[ℚ] X.E, s * t = t * s) ∧
      Algebra.IsUnramifiedIn (𝓞 X.E) (Ideal.span {((11 : ℕ) : ℤ)}) ∧ (Ideal.span {((11 : ℕ) : 𝓞 X.Kq)}).IsPrime ∧
      ∀ Q : HeightOneSpectrum (𝓞 X.E), ((11 : ℕ) : 𝓞 X.E) ∈ Q.asIdeal → Q ≠ conjPrime₂ Q := by
  let E := CyclotomicField 8 ℚ
  haveI hE : IsCyclotomicExtension {8} ℚ E := CyclotomicField.isCyclotomicExtension 8 ℚ
  haveI : IsCMField E := IsCyclotomicExtension.Rat.isCMField E (S := {8}) ⟨8, rfl, by norm_num⟩
  haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {8} ℚ E
  have hab : ∀ s t : E ≃ₐ[ℚ] E, s * t = t * s := (IsCyclotomicExtension.isMulCommutative {8} ℚ E).is_comm.comm
  have hirr := Polynomial.cyclotomic.irreducible_rat (n := 8) (by norm_num)
  have h4 : Module.finrank ℚ E = 4 := by
    rw [IsCyclotomicExtension.finrank (n := 8) E hirr]
    decide
  set ζ := IsCyclotomicExtension.zeta 8 ℚ E with hζdef
  have hζ : IsPrimitiveRoot ζ 8 := IsCyclotomicExtension.zeta_spec 8 ℚ E
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hz4 : ζ ^ 4 = -1 := (hζ.pow (by norm_num) (show 8 = 4 * 2 by norm_num)).eq_neg_one_of_two_right
  let σ : E ≃ₐ[ℚ] E := IsCyclotomicExtension.fromZetaAut (hζ.pow_of_coprime 5 (by norm_num)) hirr
  have hσ : σ ζ = -ζ := by
    rw [IsCyclotomicExtension.fromZetaAut_spec]
    linear_combination ζ * hz4
  have hcζ : conj E ζ = -ζ ^ 3 := by
    let φ : E →+* ℂ := Classical.arbitrary _
    have hn : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (by norm_num)
    have h1 : conj E ζ = ζ⁻¹ := φ.injective (by
      rw [map_inv₀, Complex.inv_eq_conj hn]
      exact IsCMField.complexEmbedding_complexConj E φ ζ)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hz4)
  have h1 : σ ≠ 1 := fun h => hζ0 (by
    rw [h, AlgEquiv.one_apply] at hσ
    linear_combination hσ / 2)
  have h2 : σ * σ = 1 := IsCyclotomicExtension.algEquiv_eq_of_apply_eq {8} ℚ E fun n hn _ => by
    obtain rfl : n = 8 := hn
    exact ⟨ζ, hζ, by rw [AlgEquiv.mul_apply, hσ, map_neg, hσ, neg_neg, AlgEquiv.one_apply]⟩
  have hc : σ ≠ conj E := fun h => by
    rw [h, hcζ] at hσ
    have h5 : ζ ^ 2 = 1 := mul_left_cancel₀ hζ0 (by linear_combination -hσ)
    have : (2 : E) = 0 := by linear_combination hz4 - (ζ ^ 2 + 1) * h5
    exact two_ne_zero this
  have hok := quarticFields_ok E σ hab h4 h1 h2 hc
  refine ⟨quarticFields E σ, hok, rfl, inferInstanceAs (IsGalois ℚ E), hab, ?_, ?_, ?_⟩
  · rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.1 (by norm_num)),
      Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr 8 E]
    have h6 : Nat.primeFactors 8 = {2} := Nat.primeFactors_prime_pow (k := 3) (by norm_num) Nat.prime_two
    have h7 : Nat.totient 8 = 4 := by decide
    rw [h6, h7]
    norm_num
  · haveI : FiniteDimensional ℚ (quarticFields E σ).Kq := Module.finite_of_finrank_pos (by rw [hok.quad]; norm_num)
    haveI : NumberField (quarticFields E σ).Kq := {}
    refine isPrime_eleven _ hok.quad ⟨ζ ^ 2, (mem_Kq E σ _).2 (by rw [map_pow, hσ, neg_sq])⟩ (Subtype.ext ?_)
    change (ζ ^ 2) ^ 2 = -1
    linear_combination hz4
  · refine @ne_conjP_eleven E _ _ (IsCMField.starRing E) (ζ + ζ ^ 3) (by linear_combination (ζ ^ 2 + 2) * hz4) ?_
    change conj E (ζ + ζ ^ 3) = -(ζ + ζ ^ 3)
    rw [map_add, map_pow, hcζ]
    linear_combination (-ζ ^ 5 + ζ) * hz4

/- English proof (translation)
Take `⟨X, hX, -, hG, hab, hur, hin, hsp⟩` from `exists_fields_ok_eleven`. Conclude with `⟨X, 11, hX.core, hG, hab, by norm_num, by norm_num, hur, hin, hsp⟩`.
-/
theorem exists_fields_prime :
    ∃ (X : Fields) (p : ℕ), X.Core ∧ IsGalois ℚ X.E ∧ (∀ s t : X.E ≃ₐ[ℚ] X.E, s * t = t * s) ∧ p.Prime ∧ 5 ≤ p ∧
      Algebra.IsUnramifiedIn (𝓞 X.E) (Ideal.span {(p : ℤ)}) ∧ (Ideal.span {((p : ℕ) : 𝓞 X.Kq)}).IsPrime ∧
      ∀ Q : HeightOneSpectrum (𝓞 X.E), ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal → Q ≠ conjPrime₂ Q := by
  obtain ⟨X, hX, -, hG, hab, hur, hin, hsp⟩ := exists_fields_ok_eleven
  exact ⟨X, 11, hX.core, hG, hab, by norm_num, by norm_num, hur, hin, hsp⟩

/- English proof (translation)
Take `⟨X, hX, -, hG, hab, hur, hin, hsp⟩` from `exists_fields_ok_eleven`. Conclude with `⟨X, 11, hX, hG, hab, by norm_num, by norm_num, hur, hin, hsp⟩`.
-/
theorem exists_fields_ok_prime :
    ∃ (X : Fields) (p : ℕ), X.Ok ∧ IsGalois ℚ X.E ∧ (∀ s t : X.E ≃ₐ[ℚ] X.E, s * t = t * s) ∧ p.Prime ∧ 5 ≤ p ∧
      Algebra.IsUnramifiedIn (𝓞 X.E) (Ideal.span {(p : ℤ)}) ∧ (Ideal.span {((p : ℕ) : 𝓞 X.Kq)}).IsPrime ∧
      ∀ Q : HeightOneSpectrum (𝓞 X.E), ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal → Q ≠ conjPrime₂ Q := by
  obtain ⟨X, hX, -, hG, hab, hur, hin, hsp⟩ := exists_fields_ok_eleven
  exact ⟨X, 11, hX, hG, hab, by norm_num, by norm_num, hur, hin, hsp⟩

/- English proof (translation)
Take `⟨X, hX, hf, hG, hab, hur, hin, hsp⟩` from `exists_fields_ok_eleven`. Conclude with `⟨X, 11, hX, hf, exists_plTie_of_core X hX.core hG hab 11 (by norm_num) (by norm_num) hur hin hsp⟩`.
-/
theorem exists_plTie_model :
    ∃ (X : Fields) (p : ℕ), X.Ok ∧ X.f = 2 ∧ ∀ (m r : ℕ) (lam : X.Tau → DomWeight (m + 1)) (c : ℤ),
      ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf)
        (P : Places p O Kf) (hm : P.m = m), P.r = r ∧ 0 < P.nV ∧
          ∃ T : PlTie X P, T.WtEq (congrArg (· + 1) hm.symm) lam c := by
  obtain ⟨X, hX, hf, hG, hab, hur, hin, hsp⟩ := exists_fields_ok_eleven
  exact ⟨X, 11, hX, hf, exists_plTie_of_core X hX.core hG hab 11 (by norm_num) (by norm_num) hur hin hsp⟩

end GlobalTheory.GO.EighthRoots
