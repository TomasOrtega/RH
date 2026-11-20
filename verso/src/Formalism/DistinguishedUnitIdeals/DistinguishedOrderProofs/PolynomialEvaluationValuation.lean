import Mathlib
import Formalism.DistinguishedUnitIdeals.PhiFreeOfBasis
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEPrim
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Descent
import Formalism.WindowSums.PowerSeriesRelationList

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PolynomialValuationLemmas

/- English proof (translation)
Establish `key : ∀ r : ℕ, 1 ≤ r → ∃ ε : Oˣ, (u : O) ^ r - 1 = (ε : O) * (ℓ : O) ^ (1 + padicValNat ℓ r)`. Introduce `r hr`. Rewrite using `[hu]`. Conclude with `GoodPlacesAlt.one_add_pow_sub_one_valuation hp h3 hl x.isUnit r hr`. Introduce `m hm`.

Take `⟨r, rfl | rfl⟩` from `m.eq_nat_or_neg`. Establish `hr : 1 ≤ r`. Break down `Nat.eq_zero_or_pos r with rfl | h` into its components or cases. Conclude with `absurd rfl hm`. Conclude with `h`.

Take `⟨ε, hε⟩` from `key r hr`. Use `⟨-ε, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, padicValInt.of_nat, Units.val_neg]`. Take the linear combination `-hε`. Establish `hr : 1 ≤ r`.

Break down `Nat.eq_zero_or_pos r with rfl | h` into its components or cases. Conclude with `absurd (by simp) hm`. Conclude with `h`. Take `⟨ε, hε⟩` from `key r hr`. Use `⟨(u ^ r)⁻¹ * ε, ?_⟩` and prove the remaining obligations.

Establish `hv : padicValInt ℓ (-(r : ℤ)) = padicValNat ℓ r` using `by simp [padicValInt]`. Establish `hinv : (((u ^ r)⁻¹ : Oˣ) : O) * (u : O) ^ r = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, Units.inv_mul]`. Rewrite using `[zpow_neg, zpow_natCast, hv, Units.val_mul]`. Take the linear combination `(((u ^ r)⁻¹ : Oˣ) : O) * hε - hinv`.
-/
theorem factV {O : Type} [CommRing O] [IsLocalRing O] {ℓ : ℕ} {u x : Oˣ} (hp : ℓ.Prime)
    (h3 : 3 ≤ ℓ) (hl : ¬ IsUnit (ℓ : O)) (hu : (u : O) = 1 + (ℓ : O) * (x : O)) :
    FactVval u ℓ := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∃ ε : Oˣ, (u : O) ^ r - 1 = (ε : O) * (ℓ : O) ^ (1 + padicValNat ℓ r) := by
    intro r hr
    rw [hu]
    exact GoodPlacesAlt.one_add_pow_sub_one_valuation hp h3 hl x.isUnit r hr
  intro m hm
  obtain ⟨r, rfl | rfl⟩ := m.eq_nat_or_neg
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd rfl hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨-ε, ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, padicValInt.of_nat, Units.val_neg]
    linear_combination -hε
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd (by simp) hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨(u ^ r)⁻¹ * ε, ?_⟩
    have hv : padicValInt ℓ (-(r : ℤ)) = padicValNat ℓ r := by simp [padicValInt]
    have hinv : (((u ^ r)⁻¹ : Oˣ) : O) * (u : O) ^ r = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    rw [zpow_neg, zpow_natCast, hv, Units.val_mul]
    linear_combination (((u ^ r)⁻¹ : Oˣ) : O) * hε - hinv

/- English proof (translation)
Establish `h2 : ((ℓ ^ E : ℕ) : ℤ) ≠ 0` using `by exact_mod_cast pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero`. Rewrite using `[padicValInt.mul hi h2, padicValInt.of_nat, padicValNat.prime_pow, add_comm]`.
-/
theorem val_mul_pow (ℓ E : ℕ) [Fact ℓ.Prime] {i : ℤ} (hi : i ≠ 0) :
    padicValInt ℓ (i * ((ℓ ^ E : ℕ) : ℤ)) = E + padicValInt ℓ i := by
  have h2 : ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  rw [padicValInt.mul hi h2, padicValInt.of_nat, padicValNat.prime_pow, add_comm]

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hf : ∀ i ∈ JS.erase 0, ∃ ε : Oˣ, (1 : O) - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Oˣ) : O) = (ε : O) * (ℓ : O) ^ (1 + E + padicValInt ℓ i)`. Introduce `i hi`. Establish `hi0 : i ≠ 0` using `Finset.ne_of_mem_erase hi`. Establish `hm : i * ((ℓ ^ E : ℕ) : ℤ) ≠ 0` using `mul_ne_zero hi0 (by exact_mod_cast pow_ne_zero _ hp.ne_zero)`.

Take `⟨ε, hε⟩` from `hV _ hm`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Rewrite using `[hε, val_mul_pow ℓ E hi0, add_assoc]`. Use `choose! ε hε using hf`. Use `⟨∏ i ∈ JS.erase 0, ε i, ?_⟩` and prove the remaining obligations.

Unfold `kapExp`. Rewrite using `[G.PPoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finset_sum]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Rewrite using `[Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.coe_prod]`. Use `push_cast`.

Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ppevalVal {O : Type} [CommRing O] (u : Oˣ) (ℓ E : ℕ) (JS : Finset ℤ) (hp : ℓ.Prime)
    (hV : FactVval u ℓ) :
    ∃ ε : Oˣ, (G.PPoly u ℓ E JS).eval 1 = (ε : O) * (ℓ : O) ^ kapExp ℓ E JS := by
  haveI := Fact.mk hp
  have hf : ∀ i ∈ JS.erase 0, ∃ ε : Oˣ, (1 : O) - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Oˣ) : O) =
      (ε : O) * (ℓ : O) ^ (1 + E + padicValInt ℓ i) := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hm : i * ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := mul_ne_zero hi0 (by exact_mod_cast pow_ne_zero _ hp.ne_zero)
    obtain ⟨ε, hε⟩ := hV _ hm
    refine ⟨ε, ?_⟩
    rw [hε, val_mul_pow ℓ E hi0, add_assoc]
  choose! ε hε using hf
  refine ⟨∏ i ∈ JS.erase 0, ε i, ?_⟩
  unfold kapExp
  rw [G.PPoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.coe_prod]
  push_cast
  rw [pow_add]
  ring

/- English proof (translation)
Take `⟨ε, h1⟩` from `ppevalVal u ℓ E JS hp hV`. Take `⟨ε', h2⟩` from `ppevalVal u ℓ E JS' hp hV`. Conclude with `⟨kapExp ℓ E JS + kapExp ℓ E JS', ε * ε', hk, by rw [h1, h2, Units.val_mul, pow_add]; ring⟩`.
-/
theorem ppval_of_le {O : Type} [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ)
    (hp : ℓ.Prime) (hV : FactVval u ℓ) (hk : kapExp ℓ E JS + kapExp ℓ E JS' ≤ 2 * kap) :
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS') := by
  obtain ⟨ε, h1⟩ := ppevalVal u ℓ E JS hp hV
  obtain ⟨ε', h2⟩ := ppevalVal u ℓ E JS' hp hV
  exact ⟨kapExp ℓ E JS + kapExp ℓ E JS', ε * ε', hk, by rw [h1, h2, Units.val_mul, pow_add]; ring⟩

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hS i hi`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ∑ k, ∑ i ∈ S, if i ∈ W k then g i else 0 := Finset.sum_comm`.

Use `_ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by`. Simplify using `only [Finset.sum_filter]`.
-/
theorem sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (if i ∈ W k then g i else 0) := by rw [if_pos hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S, if i ∈ W k then g i else 0 := Finset.sum_comm
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        simp only [Finset.sum_filter]

/- English proof (translation)
Introduce `i hi`. Establish `h1` using `h.1 (Finset.mem_of_mem_erase hi)`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨k, -, hk⟩` from `h1`. Conclude with `⟨k, hk⟩`.
-/
theorem cover {JS : Finset ℤ} {K : ℕ} {a : Fin K → ℤ} {y : Fin K → ℕ} {R : ℕ}
    (h : InWindows JS K a y R) :
    ∀ i ∈ JS.erase 0, ∃ k, i ∈ Finset.Ico (a k) (a k + (y k : ℤ)) := by
  intro i hi
  have h1 := h.1 (Finset.mem_of_mem_erase hi)
  rw [Finset.mem_biUnion] at h1
  obtain ⟨k, -, hk⟩ := h1
  exact ⟨k, hk⟩

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hp⟩`. Use `set S := JS.erase 0 with hSdef`. Use `set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (y k : ℤ)) with hWdef`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sum_le_sum_cover W S (cover h) (fun i => padicValInt ℓ i)` after adjusting the coercions.

Use `_ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by push_cast; rfl`. Use `_ ≤ ∑ k, ((y k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ R) := by`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Use `Formalism.WindowSums.arc_WindowSum ℓ (a k) (y k) R _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`.

Conclude with `(Finset.mem_filter.mp hi).2`. Introduce `h0`. Use `(Finset.mem_filter.mp h0).1` as an intermediate fact. Simplify using `[hSdef] at this`. Introduce `i hi`.

Conclude with `h.2 i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)`. Use `_ = (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) + (K : ℝ) * Real.logb ℓ R := by`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.
-/
theorem winSum (ℓ : ℕ) (JS : Finset ℤ) (K : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (R : ℕ)
    (hp : ℓ.Prime) (h : InWindows JS K a y R) :
    ((∑ i ∈ JS.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) + (K : ℝ) * Real.logb ℓ R := by
  have : Fact ℓ.Prime := ⟨hp⟩
  set S := JS.erase 0 with hSdef
  set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (y k : ℤ)) with hWdef
  calc ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ)
      ≤ ((∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
        exact_mod_cast sum_le_sum_cover W S (cover h) (fun i => padicValInt ℓ i)
    _ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ k, ((y k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ R) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine Formalism.WindowSums.arc_WindowSum ℓ (a k) (y k) R _ ?_ ?_ ?_
        · intro i hi
          exact (Finset.mem_filter.mp hi).2
        · intro h0
          have := (Finset.mem_filter.mp h0).1
          simp [hSdef] at this
        · intro i hi
          exact h.2 i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)
    _ = (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) + (K : ℝ) * Real.logb ℓ R := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.card_eq_sum_ones]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le {JS : Finset ℤ} {K : ℕ} {a : Fin K → ℤ} {y : Fin K → ℕ} {R : ℕ}
    (h : InWindows JS K a y R) : (JS.erase 0).card ≤ ∑ k, y k := by
  calc (JS.erase 0).card = ∑ i ∈ JS.erase 0, 1 := by simp
    _ ≤ ∑ k, ∑ i ∈ (JS.erase 0).filter (fun i => i ∈ Finset.Ico (a k) (a k + (y k : ℤ))), 1 :=
        sum_le_sum_cover (fun k => Finset.Ico (a k) (a k + (y k : ℤ))) _ (cover h) (fun _ => 1)
    _ ≤ ∑ k, y k := Finset.sum_le_sum fun k _ => by
        rw [← Finset.card_eq_sum_ones]
        calc _ ≤ (Finset.Ico (a k) (a k + (y k : ℤ))).card :=
              Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = y k := by simp

/- English proof (translation)
Establish `hw` using `winSum ℓ JS K a y R hp h`. Establish `hc` using `card_le h`. Establish `hsplit : (∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i) : ℕ) = (JS.erase 0).card * (1 + E) + ∑ i ∈ JS.erase 0, padicValInt ℓ i`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]`. Unfold `kapExp kapWin`.

Rewrite using `[hsplit]`. Move the coercions through the operations in `at hw ⊢`. Establish `hc' : ((JS.erase 0).card : ℝ) ≤ ∑ m, (y m : ℝ)` using `by exact_mod_cast hc`. Establish `hpos : (0 : ℝ) ≤ 1 + (E : ℝ)` using `by positivity`. Establish `hm` using `mul_le_mul_of_nonneg_right hc' hpos`.

Establish `hl : (0 : ℝ) < (ℓ : ℝ) - 1`. Establish `: (2 : ℝ) ≤ ℓ` using `by exact_mod_cast hp.two_le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) = 1 / ((ℓ : ℝ) - 1) * ∑ m, (y m : ℝ)` using `by ring`. Rewrite `hw` using `[he]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem kapExpWin (ℓ E : ℕ) (JS : Finset ℤ) (K : ℕ) (a : Fin K → ℤ) (y : Fin K → ℕ) (R : ℕ)
    (hp : ℓ.Prime) (h : InWindows JS K a y R) : (kapExp ℓ E JS : ℝ) ≤ kapWin ℓ E K y R := by
  have hw := winSum ℓ JS K a y R hp h
  have hc := card_le h
  have hsplit : (∑ i ∈ JS.erase 0, (1 + E + padicValInt ℓ i) : ℕ) =
      (JS.erase 0).card * (1 + E) + ∑ i ∈ JS.erase 0, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  unfold kapExp kapWin
  rw [hsplit]
  push_cast at hw ⊢
  have hc' : ((JS.erase 0).card : ℝ) ≤ ∑ m, (y m : ℝ) := by exact_mod_cast hc
  have hpos : (0 : ℝ) ≤ 1 + (E : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hc' hpos
  have hl : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hp.two_le
    linarith
  have he : (∑ m, (y m : ℝ)) / ((ℓ : ℝ) - 1) = 1 / ((ℓ : ℝ) - 1) * ∑ m, (y m : ℝ) := by ring
  rw [he] at hw
  nlinarith

section free
variable {O : Type} [CommRing O]

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Take `⟨v, a, hv, hx⟩` from `hx`. Conclude with `⟨v, C c * a, hv, by rw [hx, map_mul, mul_assoc]⟩`.
-/
theorem QQ_of_dvd {l l' : O} (h : l' ∣ l) {x : PowerSeries O} {d : ℕ} (hx : Prim.QQ l x d) :
    Prim.QQ l' x d := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨v, a, hv, hx⟩ := hx
  exact ⟨v, C c * a, hv, by rw [hx, map_mul, mul_assoc]⟩

/- English proof (translation)
Take `⟨E, u, hm, hdeg, hc, hu, hPe⟩` from `Prim.prep hl hQ`. Establish `hI : Ideal.span {l} ≠ ⊤` using `Ideal.span_singleton_ne_top hl`. Establish `hE : E.IsDistinguishedAt (Ideal.span {l})` using `⟨⟨fun {i} hi => Ideal.mem_span_singleton.2 (hc i (hdeg ▸ hi))⟩, hm⟩`. Establish `hPnu : ¬ IsUnit (φ X)`. Introduce `hunit`.

Establish `h1` using `isUnit_constantCoeff _ hunit`. Establish `hmem0 : constantCoeff (φ X) ∈ Ideal.span {l}`. Rewrite using `[hPe, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O), Polynomial.coeff_coe]`. Conclude with `Ideal.mul_mem_left _ _ (hE.mem (by omega))`. Conclude with `hI (Ideal.eq_top_of_isUnit_mem _ hmem0 h1)`.

Establish `hP0 : φ X ≠ 0`. Introduce `h0`. Rewrite `h0` using `[hPe]`. Establish `hE0 : (E : PowerSeries O) = 0` using `(hu.mul_right_eq_zero).mp h0`. Rewrite `hE0` using `[Polynomial.coe_eq_zero_iff]`.

Conclude with `hE.monic.ne_zero hE0`. Establish `hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < d ∧ F = φ X * q + r`. Introduce `F`. Take `⟨q, r, hr, hF⟩` from `exists_div_of_isDistinguishedAt hI hE F`. Use `⟨↑hu.unit⁻¹ * q, r, by rwa [hdeg] at hr, ?_⟩` and prove the remaining obligations.

Establish `hinv : u * ↑hu.unit⁻¹ = 1` using `hu.mul_val_inv`. Rewrite using `[hPe]`. Take the linear combination `hF - ((E : PowerSeries O) * q) * hinv`. Establish `huniq : ∀ (a : Fin d → O) (q : PowerSeries O), ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0`. Introduce `a q hq j`.

Establish `hr : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).degree < E.natDegree` using `by rw [hdeg]; exact Polynomial.degree_sum_fin_lt a`. Establish `h0` using `eq_zero_of_isDistinguishedAt_mul hI hE (q := u * q) hr (by`. Rewrite using `[coe_sum_fin, hq, hPe]`. Use the proof step `ring)`. Use `coeff_sum_fin a j` as an intermediate fact.

Rewrite `this` using `[h0, Polynomial.coeff_zero]`. Conclude with `this.symm`. Establish `hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0` using `fun x hx => eq_zero_of_forall_pow_dvd hPnu hx`. Prove the components needed by the constructor for the conclusion. Introduce `a`.

Take `⟨α, hα⟩` from `exists_sum_algHom_mul_X_pow φ d hdiv hkrull a`. Conclude with `⟨α, hα.trans (Finset.sum_congr rfl fun t _ => mul_comm _ _)⟩`. Introduce `a' h t`. Establish `h' : ∑ i, φ (a' i) * X ^ (i : ℕ) = 0`. Rewrite using `[← h]`.

Conclude with `Finset.sum_congr rfl fun t _ => mul_comm _ _`. Use extensionality with `m`. Rewrite using `[map_zero]`. Conclude with `eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0 m a' h' t`.
-/
theorem basis_of_QQ [IsDomain O] [IsDiscreteValuationRing O] {l : O} (hl : ¬ IsUnit l)
    [IsAdicComplete (Ideal.span {l}) O] (φ : PowerSeries O →ₐ[O] PowerSeries O) {d : ℕ}
    (hd1 : 1 ≤ d) (hQ : Prim.QQ l (φ X) d) :
    (∀ a : PowerSeries O, ∃ a' : Fin d → PowerSeries O,
      a = ∑ t : Fin d, X ^ (t : ℕ) * φ (a' t)) ∧
    ∀ a' : Fin d → PowerSeries O, ∑ t : Fin d, X ^ (t : ℕ) * φ (a' t) = 0 → ∀ t, a' t = 0 := by
  obtain ⟨E, u, hm, hdeg, hc, hu, hPe⟩ := Prim.prep hl hQ
  have hI : Ideal.span {l} ≠ ⊤ := Ideal.span_singleton_ne_top hl
  have hE : E.IsDistinguishedAt (Ideal.span {l}) :=
    ⟨⟨fun {i} hi => Ideal.mem_span_singleton.2 (hc i (hdeg ▸ hi))⟩, hm⟩
  have hPnu : ¬ IsUnit (φ X) := by
    intro hunit
    have h1 := isUnit_constantCoeff _ hunit
    have hmem0 : constantCoeff (φ X) ∈ Ideal.span {l} := by
      rw [hPe, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O),
        Polynomial.coeff_coe]
      exact Ideal.mul_mem_left _ _ (hE.mem (by omega))
    exact hI (Ideal.eq_top_of_isUnit_mem _ hmem0 h1)
  have hP0 : φ X ≠ 0 := by
    intro h0
    rw [hPe] at h0
    have hE0 : (E : PowerSeries O) = 0 := (hu.mul_right_eq_zero).mp h0
    rw [Polynomial.coe_eq_zero_iff] at hE0
    exact hE.monic.ne_zero hE0
  have hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r := by
    intro F
    obtain ⟨q, r, hr, hF⟩ := exists_div_of_isDistinguishedAt hI hE F
    refine ⟨↑hu.unit⁻¹ * q, r, by rwa [hdeg] at hr, ?_⟩
    have hinv : u * ↑hu.unit⁻¹ = 1 := hu.mul_val_inv
    rw [hPe]
    linear_combination hF - ((E : PowerSeries O) * q) * hinv
  have huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0 := by
    intro a q hq j
    have hr : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).degree
        < E.natDegree := by rw [hdeg]; exact Polynomial.degree_sum_fin_lt a
    have h0 := eq_zero_of_isDistinguishedAt_mul hI hE (q := u * q) hr (by
      rw [coe_sum_fin, hq, hPe]
      ring)
    have := coeff_sum_fin a j
    rw [h0, Polynomial.coeff_zero] at this
    exact this.symm
  have hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0 :=
    fun x hx => eq_zero_of_forall_pow_dvd hPnu hx
  constructor
  · intro a
    obtain ⟨α, hα⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull a
    exact ⟨α, hα.trans (Finset.sum_congr rfl fun t _ => mul_comm _ _)⟩
  · intro a' h t
    have h' : ∑ i, φ (a' i) * X ^ (i : ℕ) = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    ext m
    rw [map_zero]
    exact eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0 m a' h' t

/- English proof (translation)
Establish `hQ : Prim.QQ l (Prim.itAlg B.φ k X) (B.ℓ ^ k)`. Rewrite using `[Prim.itAlg_apply]`. Conclude with `QQ_of_dvd hd (Prim.QQ_it h3 h1 k)`. Establish `h` using `basis_of_QQ hl (Prim.itAlg B.φ k) (Nat.one_le_pow _ _ h1) hQ`. Simplify using `only [Prim.itAlg_apply] at h`.

Conclude with `h`.
-/
theorem phiBasis [IsDomain O] [IsDiscreteValuationRing O] {l : O} (hl : ¬ IsUnit l)
    [IsAdicComplete (Ideal.span {l}) O] (B : Base O) (hd : l ∣ (B.ℓ : O)) (h1 : 1 ≤ B.ℓ)
    (h3 : B.E3) (k : ℕ) : B.PhiBasis k := by
  have hQ : Prim.QQ l (Prim.itAlg B.φ k X) (B.ℓ ^ k) := by
    rw [Prim.itAlg_apply]
    exact QQ_of_dvd hd (Prim.QQ_it h3 h1 k)
  have h := basis_of_QQ hl (Prim.itAlg B.φ k) (Nat.one_le_pow _ _ h1) hQ
  simp only [Prim.itAlg_apply] at h
  exact h

variable {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Simplify using `only [Lat.phiIt]`. Rewrite using `[ih, L₀.φ_semi, h, Function.iterate_succ_apply']`.
-/
theorem phiIt_smul (L₀ : Lat B n V₀) (e₀ : V₀) (h : ∀ i, L₀.φ i e₀ = e₀) (i : ZMod n) (k : ℕ)
    (a : PowerSeries O) : L₀.phiIt i k (a • e₀) = (⇑B.φ)^[k] a • e₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Lat.phiIt]
    rw [ih, L₀.φ_semi, h, Function.iterate_succ_apply']

/- English proof (translation)
Take `⟨r, b, h1, h2⟩` from `hB`. Use `⟨r, b, h1, fun m hm hsum t => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ t, ∃ c : PowerSeries O, m t = c • e₀`. Introduce `t`. Establish `h3` using `hm t`.

Rewrite `h3` using `[hU.1 i, Submodule.mem_span_singleton]`. Take `⟨c, hc⟩` from `h3`. Conclude with `⟨c, hc.symm⟩`. Use `choose c hc using hc`. Simplify using `only [hc, phiIt_smul L₀ e₀ hU.2.1, smul_smul, ← Finset.sum_smul] at hsum`.

Establish `hz` using `h2 c (hU.2.2 _ hsum)`. Rewrite using `[hc t, hz t, zero_smul]`.
-/
theorem phiFree_of (L₀ : Lat B n V₀) (e₀ : V₀) (hU : IsUnitObj L₀ e₀) (i : ZMod n) (k : ℕ)
    (hB : B.PhiFree k) : L₀.PhiFree i k := by
  obtain ⟨r, b, h1, h2⟩ := hB
  refine ⟨r, b, h1, fun m hm hsum t => ?_⟩
  have hc : ∀ t, ∃ c : PowerSeries O, m t = c • e₀ := by
    intro t
    have h3 := hm t
    rw [hU.1 i, Submodule.mem_span_singleton] at h3
    obtain ⟨c, hc⟩ := h3
    exact ⟨c, hc.symm⟩
  choose c hc using hc
  simp only [hc, phiIt_smul L₀ e₀ hU.2.1, smul_smul, ← Finset.sum_smul] at hsum
  have hz := h2 c (hU.2.2 _ hsum)
  rw [hc t, hz t, zero_smul]

/- English proof (translation)
Introduce `i v hv hX`. Rewrite `hv` using `[hU.1 i, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hv`. Rewrite `hX` using `[smul_smul]`. Establish `ha : X * a = 0` using `hU.2.2 _ hX`.

Establish `ha0 : a = 0`. Use extensionality with `n`. Establish `h1` using `congrArg (PowerSeries.coeff (n + 1)) ha`. Rewrite `h1` using `[PowerSeries.coeff_succ_X_mul, map_zero]`. Then use the resulting hypothesis. Rewrite using `[ha0, zero_smul]`.
-/
theorem xreg_of (L₀ : Lat B n V₀) (e₀ : V₀) (hU : IsUnitObj L₀ e₀) : L₀.XReg := by
  intro i v hv hX
  rw [hU.1 i, Submodule.mem_span_singleton] at hv
  obtain ⟨a, rfl⟩ := hv
  rw [smul_smul] at hX
  have ha : X * a = 0 := hU.2.2 _ hX
  have ha0 : a = 0 := by
    ext n
    have h1 := congrArg (PowerSeries.coeff (n + 1)) ha
    rwa [PowerSeries.coeff_succ_X_mul, map_zero] at h1
  rw [ha0, zero_smul]

end free

end PolynomialValuationLemmas

open PolynomialValuationLemmas

/- English proof (translation)
Introduce `O _ _ ℓ u x hp h3 hl hu`. Conclude with `factV hp h3 hl hu`.
-/
theorem factorial_valuation_holds : FactVvalOf := by
  intro O _ _ ℓ u x hp h3 hl hu
  exact factV hp h3 hl hu

/- English proof (translation)
Introduce `O LL Ks Δ _ _ _ _ _ Lev u ℓ hu hl hV m hm h1`. Take `⟨ε, hε⟩` from `hV m hm`. Establish `hU : Lev.u = Units.map (algebraMap O LL : O →* LL) u` using `Units.ext hu`. Establish `h2 : algebraMap O LL ((u ^ m : Oˣ) : O) = 1`. Establish `: ((Lev.u ^ m : LLˣ) : LL) = algebraMap O LL ((u ^ m : Oˣ) : O)`.

Rewrite using `[hU, ← map_zpow]`. Both sides reduce to the same expression. Rewrite using `[← this, h1, Units.val_one]`. Establish `h3` using `congrArg (algebraMap O LL) hε`. Rewrite `h3` using `[map_sub, map_one, h2, sub_self, map_mul, map_pow, map_natCast]`.

Conclude with `mul_ne_zero ((ε.isUnit.map (algebraMap O LL)).ne_zero) (pow_ne_zero _ hl) h3.symm`.
-/
theorem factorial_bound_holds : FactVOf := by
  intro O LL Ks Δ _ _ _ _ _ Lev u ℓ hu hl hV m hm h1
  obtain ⟨ε, hε⟩ := hV m hm
  have hU : Lev.u = Units.map (algebraMap O LL : O →* LL) u := Units.ext hu
  have h2 : algebraMap O LL ((u ^ m : Oˣ) : O) = 1 := by
    have : ((Lev.u ^ m : LLˣ) : LL) = algebraMap O LL ((u ^ m : Oˣ) : O) := by
      rw [hU, ← map_zpow]
      rfl
    rw [← this, h1, Units.val_one]
  have h3 := congrArg (algebraMap O LL) hε
  rw [map_sub, map_one, h2, sub_self, map_mul, map_pow, map_natCast] at h3
  exact mul_ne_zero ((ε.isUnit.map (algebraMap O LL)).ne_zero) (pow_ne_zero _ hl) h3.symm

/- English proof (translation)
Introduce `O _ u ℓ E JS hp hV`. Conclude with `ppevalVal u ℓ E JS hp hV`.
-/
theorem polynomial_evaluation_valuation : PPevalVal := by
  intro O _ u ℓ E JS hp hV
  exact ppevalVal u ℓ E JS hp hV

/- English proof (translation)
Introduce `O _ u ℓ E kap JS JS' hp hV h`. Conclude with `ppval_of_le u ℓ E kap JS JS' hp hV (by unfold kapExp; omega)`.
-/
theorem polynomial_valuation_holds : PPvalOf := by
  intro O _ u ℓ E kap JS JS' hp hV h
  exact ppval_of_le u ℓ E kap JS JS' hp hV (by unfold kapExp; omega)

/- English proof (translation)
Introduce `ℓ JS K a y R hp h`. Conclude with `winSum ℓ JS K a y R hp h`.
-/
theorem window_sum_bound : WinSum := by
  intro ℓ JS K a y R hp h
  exact winSum ℓ JS K a y R hp h

/- English proof (translation)
Introduce `ℓ E JS K a y R hp h`. Conclude with `kapExpWin ℓ E JS K a y R hp h`.
-/
theorem kappa_exponent_in_window : KapExpWin := by
  intro ℓ E JS K a y R hp h
  exact kapExpWin ℓ E JS K a y R hp h

/- English proof (translation)
Introduce `O _ u ℓ E kap JS JS' hp hV K K' a y a' y' R R' hW hW' hk hk'`. Establish `h1 : (kapExp ℓ E JS : ℝ) ≤ kap` using `(kapExpWin ℓ E JS K a y R hp hW).trans hk`. Establish `h2 : (kapExp ℓ E JS' : ℝ) ≤ kap` using `(kapExpWin ℓ E JS' K' a' y' R' hp hW').trans hk'`. Establish `h1' : kapExp ℓ E JS ≤ kap` using `by exact_mod_cast h1`. Establish `h2' : kapExp ℓ E JS' ≤ kap` using `by exact_mod_cast h2`.

Conclude with `ppval_of_le u ℓ E kap JS JS' hp hV (by omega)`.
-/
theorem polynomial_valuation_window : PPvalWin := by
  intro O _ u ℓ E kap JS JS' hp hV K K' a y a' y' R R' hW hW' hk hk'
  have h1 : (kapExp ℓ E JS : ℝ) ≤ kap := (kapExpWin ℓ E JS K a y R hp hW).trans hk
  have h2 : (kapExp ℓ E JS' : ℝ) ≤ kap := (kapExpWin ℓ E JS' K' a' y' R' hp hW').trans hk'
  have h1' : kapExp ℓ E JS ≤ kap := by exact_mod_cast h1
  have h2' : kapExp ℓ E JS' ≤ kap := by exact_mod_cast h2
  exact ppval_of_le u ℓ E kap JS JS' hp hV (by omega)

/- English proof (translation)
Introduce `O _ u ℓ E kap g h JS JS' hp hV a y a' y' hW hW' hy hy' hk`. Establish `hl2 : (0 : ℝ) < (ℓ : ℝ) - 1`. Establish `: (2 : ℝ) ≤ ℓ` using `by exact_mod_cast hp.two_le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl : (0 : ℝ) ≤ (E : ℝ) + 1 + 1 / ((ℓ : ℝ) - 1)` using `add_nonneg (by positivity) (one_div_nonneg.mpr hl2.le)`.

Establish `bound : ∀ yy : Fin 3 → ℕ, ∑ m, yy m ≤ 7 * g → kapWin ℓ E 3 yy (2 * h) ≤ kap`. Introduce `yy hyy`. Establish `hs : (∑ m, (yy m : ℝ)) ≤ 7 * (g : ℝ)` using `by exact_mod_cast hyy`. Establish `hm` using `mul_le_mul_of_nonneg_left hs hl`. Unfold `kapWin`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `polynomial_valuation_window O u ℓ E kap JS JS' hp hV 3 3 a y a' y' (2 * h) (2 * h) hW hW' (bound y hy) (bound y' hy')`.
-/
theorem polynomial_valuation_kappa : PPvalKap := by
  intro O _ u ℓ E kap g h JS JS' hp hV a y a' y' hW hW' hy hy' hk
  have hl2 : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hp.two_le
    linarith
  have hl : (0 : ℝ) ≤ (E : ℝ) + 1 + 1 / ((ℓ : ℝ) - 1) :=
    add_nonneg (by positivity) (one_div_nonneg.mpr hl2.le)
  have bound : ∀ yy : Fin 3 → ℕ, ∑ m, yy m ≤ 7 * g → kapWin ℓ E 3 yy (2 * h) ≤ kap := by
    intro yy hyy
    have hs : (∑ m, (yy m : ℝ)) ≤ 7 * (g : ℝ) := by exact_mod_cast hyy
    have hm := mul_le_mul_of_nonneg_left hs hl
    unfold kapWin
    push_cast
    nlinarith
  exact polynomial_valuation_window O u ℓ E kap JS JS' hp hV 3 3 a y a' y' (2 * h) (2 * h) hW hW' (bound y hy) (bound y' hy')

/- English proof (translation)
Introduce `O _ B k h`. Conclude with `⟨B.ℓ ^ k, fun t => X ^ (t : ℕ), h.1, h.2⟩`.
-/
theorem phi_free_of_basis : PhiFreeOfBasis := by
  intro O _ B k h
  exact ⟨B.ℓ ^ k, fun t => X ^ (t : ℕ), h.1, h.2⟩

/- English proof (translation)
Introduce `O _ B n V₀ _ _ L₀ e₀ i k hB hU`. Conclude with `phiFree_of L₀ e₀ hU i k hB`.
-/
theorem phi_free_holds : PhiFreeOf := by
  intro O _ B n V₀ _ _ L₀ e₀ i k hB hU
  exact phiFree_of L₀ e₀ hU i k hB

/- English proof (translation)
Introduce `O _ B n V₀ _ _ L₀ e₀ hU`. Conclude with `xreg_of L₀ e₀ hU`.
-/
theorem X_regular_of_unit : XRegUnitOf := by
  intro O _ B n V₀ _ _ L₀ e₀ hU
  exact xreg_of L₀ e₀ hU

/- English proof (translation)
Introduce `O _ _ B h1 hl hc h3 k`. Use `hc` as an intermediate fact. Conclude with `Prim.prep hl (Prim.QQ_it h3 h1 k)`.
-/
theorem phi_X_shape_holds : PhiXShapeOf := by
  intro O _ _ B h1 hl hc h3 k
  have := hc
  exact Prim.prep hl (Prim.QQ_it h3 h1 k)

/- English proof (translation)
Introduce `O _ _ _ B h1 hl hc h3 k`. Use `haveI := hc`. Conclude with `phiBasis hl B (dvd_refl _) h1 h3 k`.
-/
theorem phi_basis_holds : PhiBasisOf := by
  intro O _ _ _ B h1 hl hc h3 k
  haveI := hc
  exact phiBasis hl B (dvd_refl _) h1 h3 k

/- English proof (translation)
Introduce `O _ _ _ hc B h1 hl h3 k`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hspan : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O` using `hϖ.maximalIdeal_eq.symm`. Use `haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [hspan]; exact hc`. Establish `hd : ϖ ∣ (B.ℓ : O)`.

Establish `hm : (B.ℓ : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr hl`. Rewrite `hm` using `[← hspan, Ideal.mem_span_singleton]`. Conclude with `hm`. Conclude with `phiBasis hϖ.not_isUnit B hd h1 h3 k`.
-/
theorem phi_basis_of_maximal : PhiBasisOfMax := by
  intro O _ _ _ hc B h1 hl h3 k
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hspan : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O := hϖ.maximalIdeal_eq.symm
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [hspan]; exact hc
  have hd : ϖ ∣ (B.ℓ : O) := by
    have hm : (B.ℓ : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hl
    rw [← hspan, Ideal.mem_span_singleton] at hm
    exact hm
  exact phiBasis hϖ.not_isUnit B hd h1 h3 k

/- English proof (translation)
Conclude with `⟨factorial_valuation_holds, factorial_bound_holds, polynomial_evaluation_valuation, polynomial_valuation_holds, window_sum_bound, kappa_exponent_in_window, polynomial_valuation_window, polynomial_valuation_kappa, phi_free_of_basis, phi_free_holds, X_regular_of_unit, phi_X_shape_h …`.
-/
theorem small_lemmas_all_hold : SmallAll := by
  exact ⟨factorial_valuation_holds, factorial_bound_holds, polynomial_evaluation_valuation, polynomial_valuation_holds, window_sum_bound, kappa_exponent_in_window,
    polynomial_valuation_window, polynomial_valuation_kappa, phi_free_of_basis, phi_free_holds, X_regular_of_unit, phi_X_shape_holds,
    phi_basis_holds, phi_basis_of_maximal⟩

end Formalism.ExponentWindows.E
