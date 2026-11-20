import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem C_dvd_of_forall_dvd_coeff (a : O) (w : PowerSeries O) (h : ∀ n, a ∣ coeff n w) :
    C a ∣ w := by
  choose q hq using h
  refine ⟨PowerSeries.mk q, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hq n

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem C_dvd_of_C_dvd_mul (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (f w : PowerSeries O)
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f ≠ 0)
    (h : C ϖ ∣ f * w) : C ϖ ∣ w := by
  obtain ⟨q, hq⟩ := h
  have hk : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have h0 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f * w) = 0 := by
    rw [hq, map_mul, PowerSeries.map_C, hk, map_zero, zero_mul]
  rw [map_mul] at h0
  have hw : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w = 0 :=
    (mul_eq_zero.mp h0).resolve_left hf
  apply C_dvd_of_forall_dvd_coeff
  intro n
  have hn := congrArg (PowerSeries.coeff n) hw
  rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hn
  exact hn

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem map_ne_zero_of_unitDist (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (d : ℕ)
    (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p ≠ 0 := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  subst hdeg
  rw [map_mul]
  refine mul_ne_zero (hu.map _).ne_zero ?_
  intro h0
  have hc := congrArg (PowerSeries.coeff E.natDegree) h0
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, hE.monic.coeff_natDegree, map_one, map_zero] at hc
  exact one_ne_zero hc

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem constantCoeff_mem_of_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p)
    (hd : 1 ≤ d) : coeff 0 p ∈ Ideal.span {ϖ} := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  exact hE.mem (by omega)

end Helpers

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the hypotheses and the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
private theorem mem_span_of_C_pow_mul_mem_span {O : Type} [CommRing O] [IsDomain O] (ϖ : O)
    [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0) (q : PowerSeries O)
    (hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q ≠ 0) :
    ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {q} → z ∈ Ideal.span {q} := by
  have hC : (C ϖ : PowerSeries O) ≠ 0 := fun h =>
    hϖ0 (by simpa using congrArg PowerSeries.constantCoeff h)
  intro N
  induction N with
  | zero =>
    intro z hz
    simpa using hz
  | succ N ih =>
    intro z hz
    apply ih
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨y, hy⟩ := hz
    have hdiv : C ϖ ∣ q * y := ⟨C (ϖ ^ N) * z, by rw [← hy, pow_succ, map_mul]; ring⟩
    obtain ⟨y', rfl⟩ := C_dvd_of_C_dvd_mul ϖ q y hq hdiv
    refine ⟨y', ?_⟩
    apply mul_left_cancel₀ hC
    rw [pow_succ, map_mul] at hy
    linear_combination hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_span_pow_of_uniformizer_mul : SatDist := by
  intro O _ _ _ ϖ hϖ d p hp k N z hz
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero k (map_ne_zero_of_unitDist ϖ d p hp)
  exact mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero (p ^ k) hq N z hz

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem pow_dvd_of_const_mem_span : ConstDist := by
  intro O _ _ _ ϖ hϖ d p hp hd c y N a h
  have key : ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {p} → z ∈ Ideal.span {p} :=
    fun N z hz => by simpa using mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp 1 N z (by simpa using hz)
  have hp0 := constantCoeff_mem_of_unitDist ϖ d p hp hd
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Ideal.mem_span_singleton] at hp0
  have h1 := key N _ h
  clear h
  induction y generalizing c a with
  | zero => simp
  | succ y ih =>
    have e2 : C (ϖ ^ y) * (C ϖ * a) = C (ϖ ^ (y + 1)) * a := by
      rw [← mul_assoc, ← map_mul, pow_succ]
    have h2 : C c - C (ϖ ^ y) * (C ϖ * a) ∈ Ideal.span {p} := by
      rw [e2]
      exact h1
    obtain ⟨c', rfl⟩ := ih c (C ϖ * a) h2
    have e3 : C (ϖ ^ y) * (C c' - C ϖ * a) = C (ϖ ^ y * c') - C (ϖ ^ (y + 1)) * a := by
      rw [mul_sub, ← map_mul, ← mul_assoc, ← map_mul, ← pow_succ]
    have h3 : C c' - C ϖ * a ∈ Ideal.span {p} := by
      apply key y
      rw [e3]
      exact h1
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h3
    have h4 := congrArg PowerSeries.constantCoeff hg
    simp only [map_mul, map_sub, PowerSeries.constantCoeff_C] at h4
    have hc' : ϖ ∣ c' := by
      have e : c' = PowerSeries.constantCoeff g * PowerSeries.constantCoeff p +
          ϖ * PowerSeries.constantCoeff a := by
        linear_combination (-1 : O) * h4
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hp0 _) (dvd_mul_right _ _)
    obtain ⟨c'', rfl⟩ := hc'
    exact ⟨c'', by ring⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem coprimeRat_symm' {O : Type} [CommRing O] {ϖ : O} {x y : PowerSeries O}
    (h : CoprimeRat ϖ x y) : CoprimeRat ϖ y x := by
  unfold CoprimeRat at h ⊢
  obtain ⟨N, A, A', hA⟩ := h
  exact ⟨N, A', A, by rw [← hA]; ring⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem coprimeRat_mul_left' {O : Type} [CommRing O] {ϖ : O} {x x' y : PowerSeries O}
    (h1 : CoprimeRat ϖ x y) (h2 : CoprimeRat ϖ x' y) : CoprimeRat ϖ (x * x') y := by
  unfold CoprimeRat at h1 h2 ⊢
  obtain ⟨N, A, A', hA⟩ := h1
  obtain ⟨M, B, B', hB⟩ := h2
  refine ⟨N + M, A * B, A * x * B' + A' * (B * x' + B' * y), ?_⟩
  rw [pow_add, map_mul, ← hA, ← hB]
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Replace the relevant objects with their definitions. Supply the required witnesses or components. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem coprimeRat_pow_left' {O : Type} [CommRing O] {ϖ : O} {x y : PowerSeries O}
    (h : CoprimeRat ϖ x y) (a : ℕ) : CoprimeRat ϖ (x ^ a) y := by
  induction a with
  | zero =>
    unfold CoprimeRat
    exact ⟨0, 1, 0, by simp⟩
  | succ a ih =>
    rw [pow_succ]
    exact coprimeRat_mul_left' ih h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem coprimeProd_statement : CoprimeProd := by
  intro O _ _ _ ϖ hϖ d d' p p' hp hp' hcop a b z hza hzb
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hc : CoprimeRat ϖ (p ^ a) (p' ^ b) :=
    coprimeRat_symm' (coprimeRat_pow_left' (coprimeRat_symm' (coprimeRat_pow_left' hcop a)) b)
  unfold CoprimeRat at hc
  obtain ⟨M, B, B', hB⟩ := hc
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hza
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hzb
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ a * p' ^ b) ≠ 0 := by
    rw [map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero a (map_ne_zero_of_unitDist ϖ d p hp))
      (pow_ne_zero b (map_ne_zero_of_unitDist ϖ d' p' hp'))
  refine mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero _ hq M z
    (Ideal.mem_span_singleton'.mpr ⟨B * t + B' * s, ?_⟩)
  rw [← hB]
  linear_combination (B * p ^ a) * ht + (B' * p' ^ b) * hs

end Formalism.ExponentWindows
