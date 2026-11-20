import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.IntegralUnitCongrCoprimeIntMod
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.FiniteFreeOfBoundedDenominatorsLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDenominatorOfLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.LatticeSaturatedAtPAndPrimeToP
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDivOfREqSmulCompletedLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsIntBilinFormOfScaledForm
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormCongrModNOfUnitCongr
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPrimeToPMultipleInRangeOfBilinForm
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsLatticeLiftCongrModCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul

noncomputable section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Wit.Sys

variable {p : ℕ} [Fact p.Prime] {D : Datum p} (X : Sys D)

/- English proof (translation)
The claim follows from `map_nsmul X.r n w`.
-/
theorem r_nsmul (n : ℕ) (w : VQ D) : X.r (n • w) = n • X.r w := map_nsmul X.r n w

/- English proof (translation)
Establish `hw : (u : VQ D) - v ∈ X.lat` using `sub_mem u.2 v.2`. Establish `hr : X.r ((u : VQ D) - v) = n • e` using `by rw [map_sub, h]; abel`. Take `⟨y, hy, ey⟩` from `UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X _ n e hw hn hnp he hr`. Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (u : VQ D) = v + n • y`.

Rewrite using `[← ey]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_add {n : ℕ} (hn : 0 < n) (hnp : n.Coprime p) (u v : X.lat) {e : AfP p ⊗[ℚ] VQ D} (he : e ∈ LaHat D)
    (h : X.r (u : VQ D) = X.r (v : VQ D) + n • e) : ∃ e' : X.lat, u = v + n • e' := by
  have hw : (u : VQ D) - v ∈ X.lat := sub_mem u.2 v.2
  have hr : X.r ((u : VQ D) - v) = n • e := by rw [map_sub, h]; abel
  obtain ⟨y, hy, ey⟩ := UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X _ n e hw hn hnp he hr
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  show (u : VQ D) = v + n • y
  rw [← ey]; abel

def plat (hfin : Module.Finite ℤ X.lat) (hfree : Module.Free ℤ X.lat) (E : LinearMap.BilinForm ℤ X.lat)
    (hE : ∀ u w : X.lat, ((E u w : ℤ) : ℚ) = X.s * X.B (u : VQ D) (w : VQ D)) : PLat D.O D.inv where
  La := X.lat
  fin := hfin
  free := hfree
  EF := (2 : ℤ) • E
  alt x := by
    have h : ((E x x : ℤ) : ℚ) = 0 := by rw [hE, X.alt, mul_zero]
    have h' : E x x = 0 := by exact_mod_cast h
    simp [h']
  nondeg x h := by
    have hs : X.s ≠ 0 := X.s_pos.ne'
    have hB : ∀ w, X.B (x : VQ D) w = 0 := by
      intro w
      obtain ⟨m, hm, hw⟩ := (UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X).2.2 w
      have h1 := h ⟨m • w, hw⟩
      have h2 : E x ⟨m • w, hw⟩ = 0 := by
        simpa using h1
      have h3 := hE x ⟨m • w, hw⟩
      rw [h2, map_nsmul] at h3
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
      simp only [Int.cast_zero, nsmul_eq_mul] at h3
      have := mul_eq_zero.1 h3.symm
      rcases this with h4 | h4
      · exact absurd h4 hs
      · exact (mul_eq_zero.1 h4).resolve_left hm'
    exact Subtype.ext (X.nondeg _ hB)
  adj a x y := by
    have h : ((E (a • x) y : ℤ) : ℚ) = ((E x (D.inv a • y) : ℤ) : ℚ) := by
      rw [hE, hE, coe_smul, coe_smul, X.adj]
    have h' : E (a • x) y = E x (D.inv a • y) := by exact_mod_cast h
    simp [h']

/- English proof (translation)
Take `⟨hfin, hfree⟩` from `UpperTheory.finite_free_of_bounded_denominators_lattice p D X (UpperTheory.exists_denominator_of_lattice p D X)`. Take `⟨E, hE⟩` from `UpperTheory.exists_int_bilinForm_of_scaled_form p D X`. Take `⟨f, hf⟩` from `UpperTheory.exists_lattice_lift_congr_mod_coprime p D X`. Establish `hν` using `UpperTheory.integral_unit_congr_coprime_int_mod p X.ε X.ε_int X.ε_inv`. Use `choose! ν b hν using hν`.

Take `⟨hp1, hp2, hp3⟩` from `UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X`. Establish `hEint : ∀ (n : ℕ), 0 < n → n.Coprime p → ∀ a a', ∃ z : ℤ, E (f n a) (f n a') = ν n * D.EF a a' + n * z`. Introduce `n hn hnp a a'`. Take `⟨e, he, re⟩` from `hf n hn hnp a`. Take `⟨e', he', re'⟩` from `hf n hn hnp a'`.

Take `⟨hb, hεb, -⟩` from `hν n hn hnp`. Take `⟨z, hz⟩` from `UpperTheory.scaled_form_congr_mod_n_of_unit_congr p D X n (ν n) (b n) _ _ a a' e e' hn hnp hb hεb (f n a).2 (f n a').2 he he' re re'`. Use `⟨z, ?_⟩` and prove the remaining obligations. Use `(hE (f n a) (f n a')).trans hz` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `c1 : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧ ∀ a : D.La, ∃ e : X.lat, f (n * m) a = f n a + n • e`. Introduce `n m hn hm hnm`. Establish `hnp : n.Coprime p` using `Nat.Coprime.coprime_mul_right hnm`. Establish `hnmp : 0 < n * m` using `Nat.mul_pos hn hm`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations.

Take `⟨hb, hεb, -⟩` from `hν n hn hnp`. Take `⟨hb', hεb', -⟩` from `hν (n * m) hnmp hnm`. Use `GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ (b n - m * b (n * m)) ?_ ?_` and prove the remaining obligations. Introduce `v`. Rewrite using `[map_sub, map_mul, map_natCast]`.

Conclude with `sub_mem (hb v) (mul_mem (natCast_mem _ m) (hb' v))`. Establish `e1` using `hεb.symm.trans hεb'`. Move the coercions through the operations in `at e1 ⊢`. Simplify using `only [map_sub, map_intCast]`. Take the linear combination `-e1`.

Take `⟨e₁, he₁, r₁⟩` from `hf (n * m) hnmp hnm a`. Take `⟨e₂, he₂, r₂⟩` from `hf n hn hnp a`. Use `eq_add X hn hnp _ _ (e := m • e₁ - e₂) (sub_mem (nsmul_mem he₁ m) he₂) ?_` and prove the remaining obligations. Rewrite using `[r₁, r₂, smul_sub, smul_smul]`. Normalize the expressions using the abelian group laws.

Establish `c2 : ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧ (∀ (c : D.O) (a : D.La), ∃ e : X.lat, f n (c • a) = c • f n a + n • e) ∧ (∀ a : D.La, (∃ e : X.lat, f n a = n • e) ↔ ∃ e : D.La, a = n • e) ∧ (∀ a' : X.lat, ∃ (a : D.La) (e : X.lat), a' = f n a + n • e) ∧ ∀ a a' : D.La …`. Introduce `n hn hnp`. Take `⟨hb, hεb, hcop⟩` from `hν n hn hnp`. Use `⟨hcop, fun c a => ?_, fun a => ⟨?_, ?_⟩, fun a' => ?_, fun a a' => ?_⟩` and prove the remaining obligations. Take `⟨e₁, he₁, r₁⟩` from `hf n hn hnp (c • a)`.

Take `⟨e₂, he₂, r₂⟩` from `hf n hn hnp a`. Use `eq_add X hn hnp (f n (c • a)) (c • f n a) (e := e₁ - (actQ D c).baseChange (AfP p) e₂) (sub_mem he₁ (GlobalTheory.AdelicSim.bc_mem D c he₂)) ?_` and prove the remaining obligations. Rewrite using `[r₁, coe_smul, r_act, r₂, map_add, map_nsmul, GlobalTheory.AdelicSim.bc_inAf, smul_sub]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨e, he⟩`.

Take `⟨e₁, he₁, r₁⟩` from `hf n hn hnp a`. Establish `h1 : X.r (f n a : VQ D) = n • X.r (e : VQ D)`. Rewrite using `[he, AddSubgroup.coe_nsmul, r_nsmul]`. Use `GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf p D n hn hnp (GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp) a ⟨X.r (e : VQ D) - e₁, sub_mem e.2.2 he₁, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← h1, r₁]`.

Normalize the expressions using the abelian group laws. Introduce and unpack `⟨e, rfl⟩`. Take `⟨e₁, he₁, r₁⟩` from `hf n hn hnp (n • e)`. Establish `h2 : inAf D (n • e) = n • inAf D e` using `GlobalTheory.AdelicSim.inAf_nsmul D n e`. Take `⟨y, hy, ey⟩` from `UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X (f n (n • e) : VQ D) n (inAf D e + e₁) (f n (n • e)).2 hn hnp (add_mem (GlobalTheory.AdelicSim.inAf_mem D e) he₁) (by rw [r₁, h2, smul_add])`.

Conclude with `⟨⟨y, hy⟩, Subtype.ext ey⟩`. Take `⟨a, w, hw, ew⟩` from `exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ a'.2.2`. Take `⟨e₁, he₁, r₁⟩` from `hf n hn hnp a`. Take `⟨e', he'⟩` from `eq_add X hn hnp a' (f n a) (e := w - e₁) (sub_mem hw he₁) (by`. Rewrite using `[ew, r₁, smul_sub]`.

Use the proof step `abel)`. Conclude with `⟨a, e', he'⟩`. Take `⟨z, hz⟩` from `hEint n hn hnp a a'`. Use `⟨2 * z, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, hz, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Set `D'` to `X.plat hfin hfree E hE`. Establish `hG : Genus p N D.plat D' (fun a => f N a)` using `⟨f, ν, rfl, c1, c2⟩`. Establish `hH : HalfPerf p D'`. Take `⟨e, he, h⟩` from `UpperTheory.exists_prime_to_p_multiple_in_range_of_bilinForm p D X E hE`.

Conclude with `⟨E, rfl, e, he, h⟩`. Use `⟨D', fun a => f N a, X.lat.subtype, ⟨hG, hH⟩, Subtype.val_injective, fun c u => rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Take `⟨m, hm, hw⟩` from `hp3 w`. Conclude with `⟨m, ⟨m • w, hw⟩, hm, rfl⟩`.

Establish `h : ∀ u u' : X.lat, ((((2 : ℤ) • E) u u' : ℤ) : ℚ) = (2 * X.s) * X.B (u : VQ D) (u' : VQ D)`. Introduce `u u'`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, hE]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h`. Introduce `w`. Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨r, u, hu⟩`. Establish `h1 : p ^ r • X.r w ∈ LaHat D`.

Rewrite using `[← r_nsmul, hu]`. Conclude with `Subtype.property (p := (· ∈ X.lat)) u |>.2`. Establish `hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ r))` using `fun v => by`. Rewrite using `[map_pow, map_pow]`. Conclude with `pow_mem (DenEnd.isIntAf_inv v) r`.

Establish `hm` using `DenEnd.smul_mem D hint h1`. Establish `hp : (p : ℚ) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Use `hm using 1` and compare the differences between its conclusion and the goal. Rewrite using `[algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]`. Use `push_cast`.

Rewrite using `[← mul_pow, inv_mul_cancel₀ hp, one_pow, one_smul]`. Take `⟨k, hk⟩` from `hp1 w h`. Conclude with `⟨k, ⟨p ^ k • w, hk⟩, rfl⟩`. Introduce `a`. Take `⟨e, he, re⟩` from `hf N hN hNp a`.

Conclude with `⟨e, he, re⟩`. Introduce `w`. Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨m, u, hm, hu⟩`. Conclude with `(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 m w hm (by rw [hu]; exact (Subtype.property (p := (· ∈ X.lat)) u).1)`.

Take `⟨m, -, hm, hw⟩` from `hp2 w h`. Conclude with `⟨m, ⟨m • w, hw⟩, hm, rfl⟩`.
-/
theorem main (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (j : D'.La →+ VQ D), D.Cls N D' t ∧ Function.Injective j ∧
      (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) ∧ (∀ w, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u) ∧
      (∀ u u', (D'.EF u u' : ℚ) = (2 * X.s) * X.B (j u) (j u')) ∧
      (∀ w, (∃ (r : ℕ) (u : D'.La), p ^ r • w = j u) ↔ X.r w ∈ LaHat D) ∧
      (∀ a, ∃ w ∈ LaHat D, X.r (j (t a)) = inAf D a + N • w) ∧
      (∀ w, (∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u) ↔ w ∈ X.M) := by
  obtain ⟨hfin, hfree⟩ := UpperTheory.finite_free_of_bounded_denominators_lattice p D X (UpperTheory.exists_denominator_of_lattice p D X)
  obtain ⟨E, hE⟩ := UpperTheory.exists_int_bilinForm_of_scaled_form p D X
  obtain ⟨f, hf⟩ := UpperTheory.exists_lattice_lift_congr_mod_coprime p D X
  have hν := UpperTheory.integral_unit_congr_coprime_int_mod p X.ε X.ε_int X.ε_inv
  choose! ν b hν using hν
  obtain ⟨hp1, hp2, hp3⟩ := UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X
  have hEint : ∀ (n : ℕ), 0 < n → n.Coprime p → ∀ a a', ∃ z : ℤ,
      E (f n a) (f n a') = ν n * D.EF a a' + n * z := by
    intro n hn hnp a a'
    obtain ⟨e, he, re⟩ := hf n hn hnp a
    obtain ⟨e', he', re'⟩ := hf n hn hnp a'
    obtain ⟨hb, hεb, -⟩ := hν n hn hnp
    obtain ⟨z, hz⟩ := UpperTheory.scaled_form_congr_mod_n_of_unit_congr p D X n (ν n) (b n) _ _ a a' e e' hn hnp hb hεb (f n a).2 (f n a').2 he he' re re'
    refine ⟨z, ?_⟩
    have := (hE (f n a) (f n a')).trans hz
    exact_mod_cast this
  have c1 : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧
      ∀ a : D.La, ∃ e : X.lat, f (n * m) a = f n a + n • e := by
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnm
    have hnmp : 0 < n * m := Nat.mul_pos hn hm
    refine ⟨?_, fun a => ?_⟩
    · obtain ⟨hb, hεb, -⟩ := hν n hn hnp
      obtain ⟨hb', hεb', -⟩ := hν (n * m) hnmp hnm
      refine GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ (b n - m * b (n * m)) ?_ ?_
      · intro v
        rw [map_sub, map_mul, map_natCast]
        exact sub_mem (hb v) (mul_mem (natCast_mem _ m) (hb' v))
      · have e1 := hεb.symm.trans hεb'
        push_cast at e1 ⊢
        simp only [map_sub, map_intCast]
        linear_combination -e1
    · obtain ⟨e₁, he₁, r₁⟩ := hf (n * m) hnmp hnm a
      obtain ⟨e₂, he₂, r₂⟩ := hf n hn hnp a
      refine eq_add X hn hnp _ _ (e := m • e₁ - e₂) (sub_mem (nsmul_mem he₁ m) he₂) ?_
      rw [r₁, r₂, smul_sub, smul_smul]
      abel
  have c2 : ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧
      (∀ (c : D.O) (a : D.La), ∃ e : X.lat, f n (c • a) = c • f n a + n • e) ∧
      (∀ a : D.La, (∃ e : X.lat, f n a = n • e) ↔ ∃ e : D.La, a = n • e) ∧
      (∀ a' : X.lat, ∃ (a : D.La) (e : X.lat), a' = f n a + n • e) ∧
      ∀ a a' : D.La, (n : ℤ) ∣ ((2 : ℤ) • E) (f n a) (f n a') - ν n * ((2 : ℤ) • D.EF) a a' := by
    intro n hn hnp
    obtain ⟨hb, hεb, hcop⟩ := hν n hn hnp
    refine ⟨hcop, fun c a => ?_, fun a => ⟨?_, ?_⟩, fun a' => ?_, fun a a' => ?_⟩
    · obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp (c • a)
      obtain ⟨e₂, he₂, r₂⟩ := hf n hn hnp a
      refine eq_add X hn hnp (f n (c • a)) (c • f n a)
        (e := e₁ - (actQ D c).baseChange (AfP p) e₂) (sub_mem he₁ (GlobalTheory.AdelicSim.bc_mem D c he₂)) ?_
      rw [r₁, coe_smul, r_act, r₂, map_add, map_nsmul, GlobalTheory.AdelicSim.bc_inAf, smul_sub]
      abel
    · rintro ⟨e, he⟩
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp a
      have h1 : X.r (f n a : VQ D) = n • X.r (e : VQ D) := by
        rw [he, AddSubgroup.coe_nsmul, r_nsmul]
      refine GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf p D n hn hnp
        (GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp) a
        ⟨X.r (e : VQ D) - e₁, sub_mem e.2.2 he₁, ?_⟩
      rw [smul_sub, ← h1, r₁]; abel
    · rintro ⟨e, rfl⟩
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp (n • e)
      have h2 : inAf D (n • e) = n • inAf D e := GlobalTheory.AdelicSim.inAf_nsmul D n e
      obtain ⟨y, hy, ey⟩ := UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X (f n (n • e) : VQ D) n (inAf D e + e₁) (f n (n • e)).2 hn hnp
        (add_mem (GlobalTheory.AdelicSim.inAf_mem D e) he₁) (by rw [r₁, h2, smul_add])
      exact ⟨⟨y, hy⟩, Subtype.ext ey⟩
    · obtain ⟨a, w, hw, ew⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ a'.2.2
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp a
      obtain ⟨e', he'⟩ := eq_add X hn hnp a' (f n a) (e := w - e₁) (sub_mem hw he₁) (by
        rw [ew, r₁, smul_sub]; abel)
      exact ⟨a, e', he'⟩
    · obtain ⟨z, hz⟩ := hEint n hn hnp a a'
      refine ⟨2 * z, ?_⟩
      simp only [LinearMap.smul_apply, hz, smul_eq_mul]
      ring
  let D' := X.plat hfin hfree E hE
  have hG : Genus p N D.plat D' (fun a => f N a) := ⟨f, ν, rfl, c1, c2⟩
  have hH : HalfPerf p D' := by
    obtain ⟨e, he, h⟩ := UpperTheory.exists_prime_to_p_multiple_in_range_of_bilinForm p D X E hE
    exact ⟨E, rfl, e, he, h⟩
  refine ⟨D', fun a => f N a, X.lat.subtype, ⟨hG, hH⟩, Subtype.val_injective, fun c u => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨m, hm, hw⟩ := hp3 w
    exact ⟨m, ⟨m • w, hw⟩, hm, rfl⟩
  · have h : ∀ u u' : X.lat, ((((2 : ℤ) • E) u u' : ℤ) : ℚ) = (2 * X.s) * X.B (u : VQ D) (u' : VQ D) := by
      intro u u'
      simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, hE]
      push_cast; ring
    exact h
  · intro w
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨r, u, hu⟩
      have h1 : p ^ r • X.r w ∈ LaHat D := by
        rw [← r_nsmul, hu]; exact Subtype.property (p := (· ∈ X.lat)) u |>.2
      have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ r)) := fun v => by
        rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv v) r
      have hm := DenEnd.smul_mem D hint h1
      have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      convert hm using 1
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [← mul_pow, inv_mul_cancel₀ hp, one_pow, one_smul]
    · obtain ⟨k, hk⟩ := hp1 w h
      exact ⟨k, ⟨p ^ k • w, hk⟩, rfl⟩
  · intro a
    obtain ⟨e, he, re⟩ := hf N hN hNp a
    exact ⟨e, he, re⟩
  · intro w
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨m, u, hm, hu⟩
      exact (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 m w hm (by rw [hu]; exact (Subtype.property (p := (· ∈ X.lat)) u).1)
    · obtain ⟨m, -, hm, hw⟩ := hp2 w h
      exact ⟨m, ⟨m • w, hw⟩, hm, rfl⟩

end UpperTheory.Gal.W2.Wit.Sys
