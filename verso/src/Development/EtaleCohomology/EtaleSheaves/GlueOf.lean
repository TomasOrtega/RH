import Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.Gluing₂

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩`. Consider the case `succ n ih`. Introduce `ε hε`.

Take `⟨ε₀, ho, hd, hs⟩` from `ih (fun j => ε j.succ) (fun j => hε j.succ)`. Establish `ha : IsIdempotentElem (ε 0)` using `hε 0`. Establish `ha' : IsIdempotentElem (1 - ε 0)` using `ha.one_sub`. Use `⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using ha`. Simplify using `only [Fin.cons_succ]`. Conclude with `ha'.mul (ho.idem j)`. Introduce `i k hik`.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `k using Fin.cases with`. Consider the case `zero => exact absurd rfl hik`. Consider the case `succ k`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]`. Consider the case `succ i`. Proceed by induction on `k using Fin.cases with`. Consider the case `zero`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]`. Consider the case `succ k`. Simplify using `only [Fin.cons_succ]`. Establish `hik' : i ≠ k` using `fun h => hik (by rw [h])`.

Combine the equalities or inequalities in the displayed calculation. Introduce `i`. Use `Fin.cases ⟨1, by simp⟩ (fun j => ?_) i` and prove the remaining obligations. Take `⟨c, hc⟩` from `hd j`. Conclude with `⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩`.

Rewrite using `[Fin.sum_univ_succ, Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← Finset.mul_sum, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem orth {S : Type} [CommRing S] : ∀ (n : ℕ) (ε : Fin n → S), (∀ j, IsIdempotentElem (ε j)) →
    ∃ ε' : Fin n → S, OrthogonalIdempotents ε' ∧ (∀ j, ∃ c, ε' j = ε j * c) ∧
      ∑ j, ε' j = 1 - ∏ j, (1 - ε j) := by
  intro n
  induction n with
  | zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨ε₀, ho, hd, hs⟩ := ih (fun j => ε j.succ) (fun j => hε j.succ)
    have ha : IsIdempotentElem (ε 0) := hε 0
    have ha' : IsIdempotentElem (1 - ε 0) := ha.one_sub
    refine ⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simp only [Fin.cons_succ]
        exact ha'.mul (ho.idem j)
    · intro i k hik
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact absurd rfl hik
        | succ k =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
      | succ i =>
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
        | succ k =>
          simp only [Fin.cons_succ]
          have hik' : i ≠ k := fun h => hik (by rw [h])
          calc (1 - ε 0) * ε₀ i * ((1 - ε 0) * ε₀ k) = ((1 - ε 0) * (1 - ε 0)) * (ε₀ i * ε₀ k) := by ring
            _ = 0 := by rw [ho.ortho hik', mul_zero]
    · intro i
      refine Fin.cases ⟨1, by simp⟩ (fun j => ?_) i
      obtain ⟨c, hc⟩ := hd j
      exact ⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hs]
      ring

/- English proof (translation)
Introduce `S C _ _ _ n e he hsurj ε hε hr hh`. Take `⟨ε', ho, hd, hs⟩` from `orth n ε hε`. Establish `hf0 : ∏ j, (1 - ε j) = 0`. Establish `hidem : IsIdempotentElem (∏ j, (1 - ε j))`. Use `ho.isIdempotentElem_sum (s := Finset.univ).one_sub` as an intermediate fact.

Rewrite `this` using `[hs, sub_sub_cancel]`. Then use the resulting hypothesis. Use `hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)` and prove the remaining obligations. Take `⟨q, hq⟩` from `hsurj ⟨J, hJ⟩`. Establish `: ∃ j, e j ∉ q.asIdeal`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))`. Take `⟨j, hj⟩` from `this`. Establish `hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j))))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]`.

Conclude with `hj`. Take `⟨q', rfl⟩` from `hq'`. Establish `hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))`. Rewrite using `[← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩`. Establish `hεj : ε j ∉ J` using `hmem`.

Establish `h1 : 1 - ε j ∈ J`. Establish `: ε j * (1 - ε j) ∈ J` using `by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem`. Conclude with `(hJ.mem_or_mem this).resolve_left hεj`. Conclude with `J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1`. Establish `hco : CompleteOrthogonalIdempotents ε'` using `⟨ho, by rw [hs, hf0, sub_zero]⟩`.

Use `choose h hh using hh`. Use `choose c hc using hd`. Establish `hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j))`. Introduce `j`. Use `isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩` and prove the remaining obligations.

Rewrite using `[← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]`. Establish `hm` using `(Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))`. Rewrite `hm` using `[neg_sub]`. Then use the resulting hypothesis. Set `L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j}` to `fun j => IsLocalization.Away.lift (ε j) (hunit j)`. Set `Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j})` to `RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))`.

Set `E` to `RingEquiv.ofBijective _ hco.bijective_pi`. Establish `hΦ : ∀ s : S, Φ (algebraMap S C s) = E s`. Introduce `s`. Use function extensionality and compare the values at `j`. Use `congrArg (fun g => L j (g s)) (hh j)` as an intermediate fact.

Simplify using `only [RingHom.comp_apply] at this`. Use `show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s`. Rewrite using `[this]`. Conclude with `IsLocalization.Away.lift_eq (ε j) (hunit j) s`. Use `⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩` and prove the remaining obligations.

Simplify using `only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]`. Simplify using the standard rewrite rules.
-/
theorem glue : LateralTheory.E.FinEtSectionPf.Glue := by
  intro S C _ _ _ n e he hsurj ε hε hr hh
  obtain ⟨ε', ho, hd, hs⟩ := orth n ε hε

  have hf0 : ∏ j, (1 - ε j) = 0 := by
    have hidem : IsIdempotentElem (∏ j, (1 - ε j)) := by
      have := ho.isIdempotentElem_sum (s := Finset.univ).one_sub
      rwa [hs, sub_sub_cancel] at this
    refine hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)
    obtain ⟨q, hq⟩ := hsurj ⟨J, hJ⟩
    have : ∃ j, e j ∉ q.asIdeal := by
      by_contra hall
      push_neg at hall
      exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))
    obtain ⟨j, hj⟩ := this
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]; exact hj
    obtain ⟨q', rfl⟩ := hq'
    have hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S)) := by
      rw [← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩
    have hεj : ε j ∉ J := hmem
    have h1 : 1 - ε j ∈ J := by
      have : ε j * (1 - ε j) ∈ J := by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem
      exact (hJ.mem_or_mem this).resolve_left hεj
    exact J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1
  have hco : CompleteOrthogonalIdempotents ε' := ⟨ho, by rw [hs, hf0, sub_zero]⟩
  choose h hh using hh
  choose c hc using hd
  have hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j)) := by
    intro j
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩
    rw [← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]
    have hm := (Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))
    rwa [neg_sub] at hm
  let L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j} :=
    fun j => IsLocalization.Away.lift (ε j) (hunit j)
  let Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j}) :=
    RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))
  let E := RingEquiv.ofBijective _ hco.bijective_pi
  have hΦ : ∀ s : S, Φ (algebraMap S C s) = E s := by
    intro s
    funext j
    have := congrArg (fun g => L j (g s)) (hh j)
    simp only [RingHom.comp_apply] at this
    show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s
    rw [this]
    exact IsLocalization.Away.lift_eq (ε j) (hunit j) s
  refine ⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]
  simp

/- English proof (translation)
The claim follows from `glue`.
-/
theorem Glue_of (_hL : LateralTheory.E.t_E1Cut.EtLift) (_hA : LateralTheory.E.t_E1Cut.EtAIC) : LateralTheory.E.FinEtSectionPf.Glue := glue

end LateralTheory.E.Gluing₂
