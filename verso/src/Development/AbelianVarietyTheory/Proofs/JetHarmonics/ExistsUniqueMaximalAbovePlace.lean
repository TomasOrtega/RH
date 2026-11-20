import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.OnePrime

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

/- English proof (translation)
Apply `Ideal.Quotient.nontrivial_iff.mpr` to reduce the goal to its premises. Introduce `h`. Rewrite `h` using `[Ideal.span_singleton_eq_top]`. Establish `h1 : (1 - w.e) * (1 - w.e) = (1 - w.e) * 1`. Rewrite using `[mul_one]`.

Conclude with `w.idem.one_sub`. Conclude with `w.ne_zero (sub_eq_self.mp (h.mul_left_cancel h1))`.
-/
theorem nontrivial_Ow (w : Place p R) : Nontrivial w.Ow := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have h1 : (1 - w.e) * (1 - w.e) = (1 - w.e) * 1 := by
    rw [mul_one]; exact w.idem.one_sub
  exact w.ne_zero (sub_eq_self.mp (h.mul_left_cancel h1))

/- English proof (translation)
Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective d`. Establish `hx : x * x - x ∈ Ideal.span {1 - w.e}` using `Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hx`. Establish `hee : w.e * w.e = w.e` using `w.idem`. Establish `he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1`.

Rewrite using `[← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩`. Establish `hf : IsIdempotentElem (w.e * x)` using `by show w.e * x * (w.e * x) = w.e * x`. Take the linear combination `(x * x - c) * hee - w.e * hc`. Establish `hfe : w.e * x * w.e = w.e * x` using `by linear_combination x * hee`.

Establish `hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) = Ideal.Quotient.mk (Ideal.span {1 - w.e}) x`. Rewrite using `[map_mul, he1, one_mul]`. Break down `w.primitive _ hf hfe with h0 | h1` into its components or cases. Use `left`. Rewrite using `[← hmk, h0, map_zero]`.

Use `right`. Rewrite using `[← hmk, h1, he1]`.
-/
theorem idem_Ow (w : Place p R) {d : w.Ow} (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hx : x * x - x ∈ Ideal.span {1 - w.e} :=
    Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  have hee : w.e * w.e = w.e := w.idem
  have he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  have hf : IsIdempotentElem (w.e * x) := by
    show w.e * x * (w.e * x) = w.e * x
    linear_combination (x * x - c) * hee - w.e * hc
  have hfe : w.e * x * w.e = w.e * x := by linear_combination x * hee
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) x := by
    rw [map_mul, he1, one_mul]
  rcases w.primitive _ hf hfe with h0 | h1
  · left
    rw [← hmk, h0, map_zero]
  · right
    rw [← hmk, h1, he1]

/- English proof (translation)
Establish `: HenselianLocalRing ℤ_[p]` using `GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]`. Use `hM` as an intermediate fact. Take `⟨d, hd, hmem⟩` from `GlobalTheory.exists_idempotent_notMem_iff_of_henselian ℤ_[p] (S := w.Ow) M`. Break down `idem_Ow w hd with rfl | rfl` into its components or cases. Conclude with `absurd M.zero_mem ((hmem M hM).mpr rfl)`.

Conclude with `(hmem N hN).mp (fun h => hN.ne_top ((Ideal.eq_top_iff_one _).mpr h))`.
-/
theorem maximal_unique [Module.Finite ℤ R] (w : Place p R) (M N : Ideal w.Ow) (hM : M.IsMaximal)
    (hN : N.IsMaximal) : N = M := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have := hM
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian ℤ_[p] (S := w.Ow) M
  rcases idem_Ow w hd with rfl | rfl
  · exact absurd M.zero_mem ((hmem M hM).mpr rfl)
  · exact (hmem N hN).mp (fun h => hN.ne_top ((Ideal.eq_top_iff_one _).mpr h))

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul z r`. Take `⟨n, -, hn⟩` from `PadicInt.exists_mem_range (x := z)`. Rewrite `hn` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`.

Take `⟨t, ht⟩` from `hn`. Use `⟨(n : R) * r, t ⊗ₜ r, ?_⟩` and prove the remaining obligations. Establish `hz : z = (n : ℤ_[p]) + t * p` using `by rw [ht]; ring`. Establish `h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Use `_ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]`. Use `_ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by`. Rewrite using `[Algebra.TensorProduct.natCast_def']`. Use `_ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.

Establish `h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r)`. Rewrite using `[Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]`. Rewrite using `[hz, TensorProduct.add_tmul, h1, h2]`. Consider the case `add x y hx hy`. Take `⟨r₁, t₁, h₁⟩` from `hx`.

Take `⟨r₂, t₂, h₂⟩` from `hy`. Conclude with `⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩`.
-/
private theorem exists_eq_one_tmul_add_mul (x : Op p R) :
    ∃ (r : R) (t : Op p R), x = (1 : ℤ_[p]) ⊗ₜ r + (p : Op p R) * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z r =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨(n : R) * r, t ⊗ₜ r, ?_⟩
    have hz : z = (n : ℤ_[p]) + t * p := by rw [ht]; ring
    have h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by
      calc (n : ℤ_[p]) ⊗ₜ[ℤ] r = ((n : ℤ_[p]) ⊗ₜ[ℤ] (1 : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]
        _ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.natCast_def']
        _ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r) := by
      rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    rw [hz, TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨r₁, t₁, h₁⟩ := hx
    obtain ⟨r₂, t₂, h₂⟩ := hy
    exact ⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩

/- English proof (translation)
Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Take `⟨r, t, h⟩` from `exists_eq_one_tmul_add_mul x`. Use `⟨r, Ideal.Quotient.mk _ t, ?_⟩` and prove the remaining obligations. Rewrite using `[h, map_add, map_mul, map_natCast]`. Both sides reduce to the same expression.
-/
theorem exists_eq_add (w : Place p R) (s : w.Ow) :
    ∃ (r : R) (t : w.Ow), s = w.toOw r + (p : w.Ow) * t := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, t, h⟩ := exists_eq_one_tmul_add_mul x
  refine ⟨r, Ideal.Quotient.mk _ t, ?_⟩
  rw [h, map_add, map_mul, map_natCast]
  rfl

/- English proof (translation)
Establish `: HenselianLocalRing ℤ_[p]` using `GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]`. Establish `: Nontrivial w.Ow` using `nontrivial_Ow w`. Establish `: IsLocalRing w.Ow`. Take `⟨M, hM⟩` from `Ideal.exists_maximal w.Ow`. Conclude with `IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => maximal_unique w M N hM hN⟩`.

Use `set m := IsLocalRing.maximalIdeal w.Ow with hm`. Use `set P := m.comap w.toOw with hP`. Establish `hpm : (p : w.Ow) ∈ m`. Establish `hc` using `GlobalTheory.comap_eq_maximalIdeal_of_finite (R := ℤ_[p]) (S := w.Ow) m`. Establish `h0 : (p : ℤ_[p]) ∈ m.comap (algebraMap ℤ_[p] w.Ow)`.

Rewrite using `[hc, PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h0` using `[Ideal.mem_comap, map_natCast]`. Conclude with `h0`. Establish `hpP : (p : R) ∈ P`.

Rewrite using `[hP, Ideal.mem_comap, map_natCast]`. Conclude with `hpm`. Establish `hPne : P ≠ ⊥`. Introduce `h`. Rewrite `hpP` using `[h, Ideal.mem_bot]`.

Conclude with `(Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpP`. Establish `: P.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hPmax : P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hPne`. Establish `hmap : P.map w.toOw = m`. Use `le_antisymm Ideal.map_comap_le fun s hs => ?_` and prove the remaining obligations.

Take `⟨r, t, rfl⟩` from `exists_eq_add w s`. Establish `hpt : (p : w.Ow) * t ∈ P.map w.toOw`. Rewrite using `[← map_natCast w.toOw p]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hpP)`. Establish `hr : w.toOw r ∈ m`.

Establish `h1` using `m.sub_mem hs (m.mul_mem_right t hpm)`. Rewrite `h1` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `Ideal.add_mem _ (Ideal.mem_map_of_mem _ (show r ∈ P from hr)) hpt`. Use `⟨P, hPmax, hpP, by rw [hmap]; infer_instance, fun Q hQ hQP => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hle : Q.map w.toOw ≤ m` using `IsLocalRing.le_maximalIdeal hne`. Conclude with `hQP (hQ.eq_of_le hPmax.ne_top fun q hq => hle (Ideal.mem_map_of_mem _ hq))`.
-/
theorem exists_prime_under (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R]
    [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
      ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤ := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have : Nontrivial w.Ow := nontrivial_Ow w
  have : IsLocalRing w.Ow := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal w.Ow
    exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => maximal_unique w M N hM hN⟩
  set m := IsLocalRing.maximalIdeal w.Ow with hm
  set P := m.comap w.toOw with hP
  have hpm : (p : w.Ow) ∈ m := by
    have hc := GlobalTheory.comap_eq_maximalIdeal_of_finite (R := ℤ_[p]) (S := w.Ow) m
    have h0 : (p : ℤ_[p]) ∈ m.comap (algebraMap ℤ_[p] w.Ow) := by
      rw [hc, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hpP : (p : R) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hpm
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  have hmap : P.map w.toOw = m := by
    refine le_antisymm Ideal.map_comap_le fun s hs => ?_
    obtain ⟨r, t, rfl⟩ := exists_eq_add w s
    have hpt : (p : w.Ow) * t ∈ P.map w.toOw := by
      rw [← map_natCast w.toOw p]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hpP)
    have hr : w.toOw r ∈ m := by
      have h1 := m.sub_mem hs (m.mul_mem_right t hpm)
      rwa [add_sub_cancel_right] at h1
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ (show r ∈ P from hr)) hpt
  refine ⟨P, hPmax, hpP, by rw [hmap]; infer_instance, fun Q hQ hQP => ?_⟩
  by_contra hne
  have hle : Q.map w.toOw ≤ m := IsLocalRing.le_maximalIdeal hne
  exact hQP (hQ.eq_of_le hPmax.ne_top fun q hq => hle (Ideal.mem_map_of_mem _ hq))

end GlobalTheory.OnePrime
