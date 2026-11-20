import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteQuotientComap

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.InertParity.LengthSign

/- English proof (translation)
Introduce `hd`. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `: Finite (B ⧸ A.addSubgroupOf B)` using `Nat.finite_of_card_ne_zero h0`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) q hd`. Establish `: s • x = 0`.

Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H y`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Conclude with `h y y.2`. Establish `h1` using `addOrderOf_dvd_of_nsmul_eq_zero this`.

Rewrite `h1` using `[hx]`. Conclude with `hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hs.symm h1)`.
-/
theorem not_dvd_relIndex {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (h0 : A.relIndex B ≠ 0) {q s : ℕ}
    (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ B, s • x ∈ A) : ¬ q ∣ A.relIndex B := by
  intro hd
  have : Fact q.Prime := ⟨hq⟩
  have : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) q hd
  have : s • x = 0 := by
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact h y y.2
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero this
  rw [hx] at h1
  exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hs.symm h1)

/- English proof (translation)
Establish `hX : (A ⊓ A').relIndex B ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero h0 h0'`. Establish `e1` using `AddSubgroup.relIndex_inf_mul_relIndex A A' B`. Establish `e2` using `AddSubgroup.relIndex_inf_mul_relIndex A' A B`. Rewrite `e2` using `[inf_comm A' A]`. Establish `n1 : A.relIndex (A' ⊓ B) ≠ 0` using `left_ne_zero_of_mul (e1 ▸ hX)`.

Establish `n2 : A'.relIndex (A ⊓ B) ≠ 0` using `left_ne_zero_of_mul (e2 ▸ hX)`. Establish `d1` using `not_dvd_relIndex A (A' ⊓ B) n1 hq hs fun x hx => h' x hx.1`. Establish `d2` using `not_dvd_relIndex A' (A ⊓ B) n2 hq hs fun x hx => h x hx.1`. Establish `e` using `congrArg (fun m : ℕ => m.factorization q) (e1.trans e2.symm)`. Simplify using `only [Nat.factorization_mul n1 h0', Nat.factorization_mul n2 h0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd d1, Nat.factorization_eq_zero_of_not_dvd d2, zero_add] at e`.

Conclude with `e.symm`.
-/
theorem factorization_relIndex_eq {G : Type} [AddCommGroup G] (A A' B : AddSubgroup G) (h0 : A.relIndex B ≠ 0)
    (h0' : A'.relIndex B ≠ 0) {q s : ℕ} (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ A, s • x ∈ A')
    (h' : ∀ x ∈ A', s • x ∈ A) : (A.relIndex B).factorization q = (A'.relIndex B).factorization q := by
  have hX : (A ⊓ A').relIndex B ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h0 h0'
  have e1 := AddSubgroup.relIndex_inf_mul_relIndex A A' B
  have e2 := AddSubgroup.relIndex_inf_mul_relIndex A' A B
  rw [inf_comm A' A] at e2
  have n1 : A.relIndex (A' ⊓ B) ≠ 0 := left_ne_zero_of_mul (e1 ▸ hX)
  have n2 : A'.relIndex (A ⊓ B) ≠ 0 := left_ne_zero_of_mul (e2 ▸ hX)
  have d1 := not_dvd_relIndex A (A' ⊓ B) n1 hq hs fun x hx => h' x hx.1
  have d2 := not_dvd_relIndex A' (A ⊓ B) n2 hq hs fun x hx => h x hx.1
  have e := congrArg (fun m : ℕ => m.factorization q) (e1.trans e2.symm)
  simp only [Nat.factorization_mul n1 h0', Nat.factorization_mul n2 h0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd d1, Nat.factorization_eq_zero_of_not_dvd d2, zero_add] at e
  exact e.symm

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap`. Consider the case `exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap`. Consider the case `(apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap ..)`.
-/
theorem finite_quot {E : Type} [Field E] [NumberField E] {n : ℕ} (L₀ L : Submodule (𝓞 E) (Fin n → E))
    (h₀ : L₀.FG) (h : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by
  first
  | exact @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | (apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap ..)

/- English proof (translation)
Use extensionality with `x`. Conclude with `(h x).trans (AdLattice.mem_lat g x).symm`.
-/
theorem eq_lat {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : L = AdLattice.lat g := by
  ext x
  exact (h x).trans (AdLattice.mem_lat g x).symm

/- English proof (translation)
The claim follows from `finite_quot _ _ (AdLattice.lat_one_eq D n ▸ (AdLattice.lat_isLattice _).fg) (AdLattice.lat_isLattice g).span_eq_top`.
-/
theorem finite_lat (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) :
    Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype (AdLattice.lat g)) :=
  finite_quot _ _ (AdLattice.lat_one_eq D n ▸ (AdLattice.lat_isLattice _).fg) (AdLattice.lat_isLattice g).span_eq_top

/- English proof (translation)
Use `finite_lat D g` as an intermediate fact. Conclude with `Nat.card_pos.ne'`.
-/
theorem idx_lat_ne_zero (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) : idx D (AdLattice.lat g) ≠ 0 := by
  have := finite_lat D g
  exact Nat.card_pos.ne'

/- English proof (translation)
Establish `h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) * (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D`. Introduce `i j`. Take `⟨m, -, hm, s, hs, he⟩` from `h i j 0`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite `he` using `[pow_zero, one_mul]`.

Rewrite using `[he]`. Conclude with `hs`. Use `choose m hm hmS using h0`. Use `set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs`. Establish `hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D`.

Introduce `i j`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `: (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) * (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j`. Rewrite using `[hs, hc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)`. Use `⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]`.

Use `Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

/- English proof (translation)
Take `⟨s, hs, h1, h2⟩` from `exists_int_mul D q k h`. Use `⟨s, hs, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.E]`. Use `AdLattice.smul_mem_lat s ?_ hx` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]`.

Conclude with `h2`. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.E]`. Use `AdLattice.smul_mem_lat s ?_ hx` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, inv_mul_cancel_left]`. Conclude with `h1`.
-/
theorem agree (D : D7) {n : ℕ} (q : ℕ) (g k : GA D n) (h : TrivAt D q (k : GL (Fin n) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ x ∈ AdLattice.lat (g : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D))) ∧
      ∀ x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat (g : GL (Fin n) (AE D)) := by
  obtain ⟨s, hs, h1, h2⟩ := exists_int_mul D q k h
  refine ⟨s, hs, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]
    exact h2
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, inv_mul_cancel_left]
    exact h1

/- English proof (translation)
Rewrite using `[eq_lat h]`. Conclude with `finite_lat D g`.
-/
theorem finite_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype L) := by
  rw [eq_lat h]
  exact finite_lat D g

/- English proof (translation)
Rewrite using `[← idx_eq_relIndex, eq_lat h]`. Conclude with `idx_lat_ne_zero D g`.
-/
theorem relIndex_ne_zero_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Moves D g L) :
    L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup ≠ 0 := by
  rw [← idx_eq_relIndex, eq_lat h]
  exact idx_lat_ne_zero D g

/- English proof (translation)
Rewrite using `[eq_lat hL, eq_lat hL']`. Conclude with `agree D q g k h`.
-/
theorem agree_of_moves {D : D7} {n : ℕ} {q : ℕ} {g k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (g : GL (Fin n) (AE D)) L)
    (hL' : Moves D ((g * k : GA D n) : GL (Fin n) (AE D)) L') :
    ∃ s : ℕ, Nat.Coprime s q ∧ (∀ x ∈ L.toAddSubgroup, s • x ∈ L'.toAddSubgroup) ∧
      ∀ x ∈ L'.toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  rw [eq_lat hL, eq_lat hL']
  exact agree D q g k h

/- English proof (translation)
Take `⟨s, hsq, h, -⟩` from `agree D q 1 k h`. Rewrite `h` using `[one_mul, OneMemClass.coe_one, AdLattice.lat_one_eq, ← eq_lat hL]`. Conclude with `⟨s, hsq, h⟩`.
-/
theorem agree_std {D : D7} {n : ℕ} {q : ℕ} {k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (k : GL (Fin n) (AE D)) L) :
    ∃ s : ℕ, Nat.Coprime s q ∧ ∀ x ∈ (stdL D n).toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  obtain ⟨s, hsq, h, -⟩ := agree D q 1 k h
  rw [one_mul, OneMemClass.coe_one, AdLattice.lat_one_eq, ← eq_lat hL] at h
  exact ⟨s, hsq, h⟩

/- English proof (translation)
Introduce `D n gs gi Li L hs hi hLi hL`. Use `finite_of_moves hLi` as an intermediate fact. Establish `h1 : sgn D (idx D Li) = (-1 : ℂ) ^ lenQ D (stdL D n) Li`. Use `(GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length D (stdL D n ⧸ Submodule.comap (stdL D n).subtype Li)).2 fun q hq hd => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Take `⟨s, hsq, h⟩` from `agree_std (hi q hq hn) hLi`. Conclude with `not_dvd_relIndex _ _ (relIndex_ne_zero_of_moves hLi) hq hsq h ((idx_eq_relIndex Li) ▸ hd)`. Rewrite using `[← h1]`. Use `sgn_congr fun q hq hiq => ?_` and prove the remaining obligations. Take `⟨s, hsq, h, h'⟩` from `agree_of_moves (hs q hq hiq) hLi hL`.

Rewrite using `[idx_eq_relIndex, idx_eq_relIndex]`. Conclude with `factorization_relIndex_eq _ _ _ (relIndex_ne_zero_of_moves hLi) (relIndex_ne_zero_of_moves hL) hq hsq h h'`.
-/
theorem neg_one_pow_lenQ : ∀ (D : D7) (n : ℕ) (gs gi : GA D n) (Li L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), SuppSplit D (gs : GL (Fin n) (AE D)) → SuppInert D (gi : GL (Fin n) (AE D)) → Moves D (gi : GL (Fin n) (AE D)) Li → Moves D ((gi * gs : GA D n) : GL (Fin n) (AE D)) L → (-1 : ℂ) ^ lenQ D (stdL D n) Li = sgn D (idx D L) := by
  intro D n gs gi Li L hs hi hLi hL
  have := finite_of_moves hLi
  have h1 : sgn D (idx D Li) = (-1 : ℂ) ^ lenQ D (stdL D n) Li := by
    refine (GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length D (stdL D n ⧸ Submodule.comap (stdL D n).subtype Li)).2 fun q hq hd => ?_
    by_contra hn
    obtain ⟨s, hsq, h⟩ := agree_std (hi q hq hn) hLi
    exact not_dvd_relIndex _ _ (relIndex_ne_zero_of_moves hLi) hq hsq h ((idx_eq_relIndex Li) ▸ hd)
  rw [← h1]
  refine sgn_congr fun q hq hiq => ?_
  obtain ⟨s, hsq, h, h'⟩ := agree_of_moves (hs q hq hiq) hLi hL
  rw [idx_eq_relIndex, idx_eq_relIndex]
  exact factorization_relIndex_eq _ _ _ (relIndex_ne_zero_of_moves hLi) (relIndex_ne_zero_of_moves hL) hq hsq h h'

end GlobalTheory.InertParity.LengthSign
