import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])` using `(lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem az_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Cardinal in
/- English proof (translation)
Establish `h1 : #ℚ_[l] ≤ #(CauSeq ℚ (padicNorm l))` using `mk_le_of_surjective (f := (Quotient.mk'' : CauSeq ℚ (padicNorm l) → ℚ_[l])) Quotient.mk''_surjective`. Establish `h2 : #(CauSeq ℚ (padicNorm l)) ≤ #(ℕ → ℚ)` using `mk_subtype_le _`. Establish `h3 : #(ℕ → ℚ) = 𝔠` using `by simp`. Apply `le_antisymm` to reduce the goal to its premises. Use `(Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans ?_` and prove the remaining obligations.

Conclude with `max_le (h1.trans (h2.trans h3.le)) aleph0_le_continuum`. Establish `h : 𝔠 ≤ #ℚ_[l]` using `continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]`. Conclude with `h.trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)`.
-/
private theorem az_card (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  have h1 : #ℚ_[l] ≤ #(CauSeq ℚ (padicNorm l)) :=
    mk_le_of_surjective (f := (Quotient.mk'' : CauSeq ℚ (padicNorm l) → ℚ_[l])) Quotient.mk''_surjective
  have h2 : #(CauSeq ℚ (padicNorm l)) ≤ #(ℕ → ℚ) := mk_subtype_le _
  have h3 : #(ℕ → ℚ) = 𝔠 := by simp
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans ?_
    exact max_le (h1.trans (h2.trans h3.le)) aleph0_le_continuum
  · have h : 𝔠 ≤ #ℚ_[l] := continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]
    exact h.trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)

private noncomputable def azV (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (NormedField.valuation : Valuation (PadicAlgCl l) NNReal).valuationSubring

/- English proof (translation)
Use `show ‖x‖₊ ≤ 1 ↔ _`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
private theorem mem_azV {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : x ∈ azV l ↔ ‖x‖ ≤ 1 := by
  show ‖x‖₊ ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

private noncomputable def azA {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O →+* azV l :=
  (c.O.val : c.O →+* PadicAlgCl l).codRestrict (azV l) fun x =>
    (mem_azV _).2 ((az_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val))

/- English proof (translation)
Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx.exists_left_inv`. Establish `hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1` using `congrArg Subtype.val hy`. Establish `h0 : (x : PadicAlgCl l) ≠ 0` using `right_ne_zero_of_mul_eq_one hy'`. Establish `hm : (y : PadicAlgCl l) ∈ c.O` using `(coefSup l).2.2.2 c y ((az_intIff _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩`.

Conclude with `IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')`.
-/
private theorem azA_loc {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalHom (azA c) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  have hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1 := congrArg Subtype.val hy
  have h0 : (x : PadicAlgCl l) ≠ 0 := right_ne_zero_of_mul_eq_one hy'
  have hm : (y : PadicAlgCl l) ∈ c.O :=
    (coefSup l).2.2.2 c y ((az_intIff _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩
  exact IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')

/- English proof (translation)
Introduce `l hl`. Use `⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ }, RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩` and prove the remaining obligations. Take `⟨c, -⟩` from `(coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)`. Take `⟨c', -, hx⟩` from `(coefSup l).2.2.1 c x ((az_intIff _).2 ((mem_azV _).1 x.2))`. Use `⟨c', ⟨x, hx⟩, ?_⟩` and prove the remaining obligations.

Establish `: azA c' ⟨x, hx⟩ = x` using `rfl`. Rewrite using `[this, sub_self]`. Conclude with `Ideal.zero_mem _`. Apply `IsAlgClosed.ringEquiv_of_equiv_of_charZero` to reduce the goal to its premises. Rewrite using `[az_card]`.

Conclude with `Cardinal.aleph0_lt_continuum`. Conclude with `Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])`.
-/
theorem UpperTheory.V.Ws.ambZero :
    ∀ (l : ℕ) [Fact l.Prime], (∃ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e) ∧ Nonempty (PadicAlgCl l ≃+* ℂ) := by
  intro l hl
  refine ⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ },
    RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩
  · obtain ⟨c, -⟩ := (coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)
    obtain ⟨c', -, hx⟩ := (coefSup l).2.2.1 c x ((az_intIff _).2 ((mem_azV _).1 x.2))
    refine ⟨c', ⟨x, hx⟩, ?_⟩
    have : azA c' ⟨x, hx⟩ = x := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [az_card]; exact Cardinal.aleph0_lt_continuum
    · exact Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])
