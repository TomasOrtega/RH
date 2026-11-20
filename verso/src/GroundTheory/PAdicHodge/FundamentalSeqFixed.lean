import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqSurj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p

section Residue

/- English proof (translation)
Establish `hmon : (X ^ p - X : (ZMod p)[X]).Monic` using `(monic_X_pow p).sub_of_left (by rw [degree_X, degree_X_pow]; exact_mod_cast hp.out.one_lt)`. Establish `hr : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val`. Simplify `FiniteField.roots_X_pow_card_sub_X (ZMod p)` using `[ZMod.card]`. Establish `hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p` using `FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt`. Establish `h` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by`.

Rewrite using `[hr, hdeg, Finset.card_val, Finset.card_univ, ZMod.card])`. Rewrite `h` using `[hr, ← Finset.prod_eq_multiset_prod]`. Rewrite using `[← h]`. Use `Finset.prod_nbij' (fun a => (a : ZMod p)) (fun a => a.val) (fun a _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun a ha => ?_) (fun a _ => ZMod.natCast_zmod_val a) (fun a _ => rfl)` and prove the remaining obligations. Conclude with `ZMod.val_cast_of_lt (Finset.mem_range.1 ha)`.
-/
theorem prod_range_X_sub_C_zmod :
    ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ZMod p)) = X ^ p - X := by
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic :=
    (monic_X_pow p).sub_of_left (by rw [degree_X, degree_X_pow]; exact_mod_cast hp.out.one_lt)
  have hr : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hr, hdeg, Finset.card_val, Finset.card_univ, ZMod.card])
  rw [hr, ← Finset.prod_eq_multiset_prod] at h
  rw [← h]
  refine Finset.prod_nbij' (fun a => (a : ZMod p)) (fun a => a.val) (fun a _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun a ha => ?_) (fun a _ => ZMod.natCast_zmod_val a)
    (fun a _ => rfl)
  exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)

/- English proof (translation)
Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `i`. Establish `h1 : (F.coeff i : ZMod p) = 0`. Use `congrArg (fun f => Polynomial.coeff f i) h` as an intermediate fact. Simplify `this` using `only [coeff_map, eq_intCast, coeff_zero]`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1`.
-/
theorem C_dvd_of_map_eq_zero {F : ℤ[X]} (h : F.map (Int.castRingHom (ZMod p)) = 0) :
    C (p : ℤ) ∣ F := by
  rw [C_dvd_iff_dvd_coeff]
  intro i
  have h1 : (F.coeff i : ZMod p) = 0 := by
    have := congrArg (fun f => Polynomial.coeff f i) h
    simpa only [coeff_map, eq_intCast, coeff_zero] using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1

/- English proof (translation)
Establish `hmap : (∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) - (X ^ p - X)).map (Int.castRingHom (ZMod p)) = 0`. Rewrite using `[Polynomial.map_sub, Polynomial.map_prod, sub_eq_zero]`. Establish `e1 : Polynomial.map (Int.castRingHom (ZMod p)) (X ^ p - X) = X ^ p - X` using `by simp`. Rewrite using `[e1, ← prod_range_X_sub_C_zmod]`. Conclude with `Finset.prod_congr rfl fun i _ => by simp`.

Take `⟨G, hG⟩` from `C_dvd_of_map_eq_zero hmap`. Conclude with `⟨G, by rw [← hG]; ring⟩`.
-/
theorem exists_prod_range_X_sub_C_eq :
    ∃ G : ℤ[X], ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) = X ^ p - X + C (p : ℤ) * G := by
  have hmap : (∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) - (X ^ p - X)).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_prod, sub_eq_zero]
    have e1 : Polynomial.map (Int.castRingHom (ZMod p)) (X ^ p - X) = X ^ p - X := by simp
    rw [e1, ← prod_range_X_sub_C_zmod]
    exact Finset.prod_congr rfl fun i _ => by simp
  obtain ⟨G, hG⟩ := C_dvd_of_map_eq_zero hmap
  exact ⟨G, by rw [← hG]; ring⟩

/- English proof (translation)
Take `⟨G, hG⟩` from `exists_prod_range_X_sub_C_eq (p := p)`. Use `⟨aeval v G, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (aeval v) hG`. Simplify `h` using `[map_prod]`.
-/
theorem exists_prod_range_sub_eq (v : 𝒪) :
    ∃ g : 𝒪, ∏ a ∈ Finset.range p, (v - (a : 𝒪)) = v ^ p - v + (p : 𝒪) * g := by
  obtain ⟨G, hG⟩ := exists_prod_range_X_sub_C_eq (p := p)
  refine ⟨aeval v G, ?_⟩
  have h := congrArg (aeval v) hG
  simpa [map_prod] using h

/- English proof (translation)
Establish `h1 : ‖(n : ℚ_[p])‖ = 1`. Use `le_antisymm (Padic.norm_int_le_one n) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `hd` using `Padic.norm_intCast_lt_one_iff.1 hlt`. Use `Int.natAbs_dvd_natAbs.2 hd` as an intermediate fact. Simplify using `only [Int.natAbs_natCast] at this`.

Conclude with `absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) this) (by omega)`. Establish `h2` using `PadicComplex.norm_extends' (p := p) (n : ℚ_[p])`. Rewrite `h2` using `[h1, PadicComplex.coe_eq, map_intCast, map_intCast]`. Conclude with `h2`.
-/
theorem norm_intCast_eq_one {n : ℤ} (hn0 : n ≠ 0) (hn : n.natAbs < p) : ‖(n : ℂ_[p])‖ = 1 := by
  have h1 : ‖(n : ℚ_[p])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one n) (not_lt.1 fun hlt => ?_)
    have hd := Padic.norm_intCast_lt_one_iff.1 hlt
    have := Int.natAbs_dvd_natAbs.2 hd
    simp only [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) this) (by omega)
  have h2 := PadicComplex.norm_extends' (p := p) (n : ℚ_[p])
  rw [h1, PadicComplex.coe_eq, map_intCast, map_intCast] at h2
  exact h2

/- English proof (translation)
Establish `hb' : (b : ℂ_[p]) ≠ 0` using `fun h => hb (Subtype.ext h)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[MulMemClass.coe_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (mem_normInteger.1 c.2)`.

Introduce `h`. Use `⟨⟨(a : ℂ_[p]) / b, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _)`. Rewrite using `[MulMemClass.coe_mul]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dvd_iff_norm_le {a b : 𝒪} (hb : b ≠ 0) : b ∣ a ↔ ‖(a : ℂ_[p])‖ ≤ ‖(b : ℂ_[p])‖ := by
  have hb' : (b : ℂ_[p]) ≠ 0 := fun h => hb (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    rw [MulMemClass.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_normInteger.1 c.2)
  · intro h
    refine ⟨⟨(a : ℂ_[p]) / b, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    · rw [MulMemClass.coe_mul]
      field_simp

/- English proof (translation)
Introduce `h` and use `by have := congrArg (fun x : 𝒪 => (x : ℂ_[p])) h simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this exact hp.out.ne_zero this`.
-/
theorem natCast_p_ne_zero' : (p : 𝒪) ≠ 0 := fun h => by
  have := congrArg (fun x : 𝒪 => (x : ℂ_[p])) h
  simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
  exact hp.out.ne_zero this

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_prod_range_sub_eq v`. Establish `hprod : (p : 𝒪) ∣ ∏ a ∈ Finset.range p, (v - (a : 𝒪))`. Rewrite using `[hg]`. Conclude with `dvd_add hv (dvd_mul_right _ _)`. Rewrite `hprod` using `[dvd_iff_norm_le natCast_p_ne_zero']`.

Establish `hnp : ‖((p : 𝒪) : ℂ_[p])‖ < 1`. Simplify using `using norm_natCast_p_lt_one (p := p)`. Simplify using `only [SubmonoidClass.coe_finsetProd, norm_prod] at hprod`. Establish `hle : ∀ a : ℕ, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ ≤ 1` using `fun a => mem_normInteger.1 (v - a).2`. Distinguish the cases in `hex : ∃ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ < 1`.

Take `⟨a, ha, hlt⟩` from `hex`. Use `⟨a, Finset.mem_range.1 ha, ?_⟩` and prove the remaining obligations. Rewrite using `[dvd_iff_norm_le natCast_p_ne_zero']`. Rewrite `hprod` using `[Finset.prod_eq_single_of_mem a ha]`. Conclude with `hprod`.

Introduce `b hb hba`. Establish `hab : ‖(((a : ℤ) - b : ℤ) : ℂ_[p])‖ = 1` using `norm_intCast_eq_one (by omega) (by have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega)`. Establish `e : ((v - (b : 𝒪) : 𝒪) : ℂ_[p]) = ((v - (a : 𝒪) : 𝒪) : ℂ_[p]) + (((a : ℤ) - b : ℤ) : ℂ_[p])` using `by push_cast; ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hab]; exact hlt.ne), hab, max_eq_right hlt.le]`. Use `push Not at hex`.

Establish `h1 : ∏ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ = 1` using `Finset.prod_eq_one fun a ha => le_antisymm (hle a) (hex a ha)`. Rewrite `hprod` using `[h1]`. Conclude with `absurd hprod (not_le.2 hnp)`.
-/
theorem exists_natCast_dvd_sub_of_dvd_pow_sub {v : 𝒪} (hv : (p : 𝒪) ∣ v ^ p - v) :
    ∃ a : ℕ, a < p ∧ (p : 𝒪) ∣ v - a := by
  obtain ⟨g, hg⟩ := exists_prod_range_sub_eq v
  have hprod : (p : 𝒪) ∣ ∏ a ∈ Finset.range p, (v - (a : 𝒪)) := by
    rw [hg]
    exact dvd_add hv (dvd_mul_right _ _)
  rw [dvd_iff_norm_le natCast_p_ne_zero'] at hprod
  have hnp : ‖((p : 𝒪) : ℂ_[p])‖ < 1 := by
    simpa using norm_natCast_p_lt_one (p := p)
  simp only [SubmonoidClass.coe_finsetProd, norm_prod] at hprod
  have hle : ∀ a : ℕ, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ ≤ 1 := fun a => mem_normInteger.1 (v - a).2
  by_cases hex : ∃ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ < 1
  · obtain ⟨a, ha, hlt⟩ := hex
    refine ⟨a, Finset.mem_range.1 ha, ?_⟩
    rw [dvd_iff_norm_le natCast_p_ne_zero']
    rw [Finset.prod_eq_single_of_mem a ha] at hprod
    · exact hprod
    · intro b hb hba
      have hab : ‖(((a : ℤ) - b : ℤ) : ℂ_[p])‖ = 1 := norm_intCast_eq_one (by omega)
        (by have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega)
      have e : ((v - (b : 𝒪) : 𝒪) : ℂ_[p]) = ((v - (a : 𝒪) : 𝒪) : ℂ_[p]) +
          (((a : ℤ) - b : ℤ) : ℂ_[p]) := by push_cast; ring
      rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hab]; exact hlt.ne),
        hab, max_eq_right hlt.le]
  · push Not at hex
    have h1 : ∏ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ = 1 :=
      Finset.prod_eq_one fun a ha => le_antisymm (hle a) (hex a ha)
    rw [h1] at hprod
    exact absurd hprod (not_le.2 hnp)

end Residue

section Approx

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro v _; exact ⟨0, by simp⟩`. Consider the case `succ m ih`. Introduce and unpack `v ⟨c, hc⟩`. Establish `h0 : ∀ k, (p : 𝒪) ∣ v - c 0 ^ p ^ k` using `fun k => by`.

Establish `h` using `(dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hc k)`. Rewrite `h` using `[Finset.sum_range_succ', pow_zero, one_mul]`. Establish `hs : (p : 𝒪) ∣ ∑ i ∈ Finset.range m, (p : 𝒪) ^ (i + 1) * c (i + 1) ^ p ^ k` using `Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (dvd_pow_self _ i.succ_ne_zero) _`. Use `dvd_add h hs using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hv1 : (p : 𝒪) ∣ v ^ p - v`. Establish `e1 : (p : 𝒪) ∣ v ^ p - c 0 ^ p`. Establish `h` using `dvd_sub_pow_of_dvd_sub (by simpa using h0 0) 1`. Rewrite `h` using `[pow_one]`. Conclude with `(dvd_pow_self (p : 𝒪) two_ne_zero).trans h`.

Establish `e2` using `h0 1`. Rewrite `e2` using `[pow_one]`. Use `dvd_sub e1 e2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, hap, ha⟩` from `exists_natCast_dvd_sub_of_dvd_pow_sub hv1`.

Establish `hca : (p : 𝒪) ∣ c 0 - a`. Establish `h` using `h0 0`. Rewrite `h` using `[pow_zero, pow_one]`. Use `dvd_sub ha h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hfa : (p : 𝒪) ∣ (a : 𝒪) ^ p - a`. Establish `hz : (p : ℤ) ∣ (a : ℤ) ^ p - a`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card, sub_self]`.

Use `map_dvd (Int.castRingHom 𝒪) hz` as an intermediate fact. Simplify using `using this`. Establish `hak : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (a : 𝒪) ^ p ^ (m + j) - (a : 𝒪) ^ p ^ m`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ihj`. Establish `h1` using `dvd_sub_pow_of_dvd_sub hfa (m + j)`. Establish `e : ((a : 𝒪) ^ p) ^ p ^ (m + j) = (a : 𝒪) ^ p ^ (m + (j + 1))`. Rewrite using `[← pow_mul, ← pow_succ']`.

Both sides reduce to the same expression. Rewrite `h1` using `[e]`. Establish `h2` using `(pow_dvd_pow (p : 𝒪) (by omega : m + 1 ≤ m + j + 1)).trans h1`. Use `dvd_add h2 ihj using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hk : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (v - (a : 𝒪) ^ p ^ m) - (p : 𝒪) * ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + j)`. Introduce `j`. Establish `h1` using `hc (m + j)`. Rewrite `h1` using `[Finset.sum_range_succ', pow_zero, one_mul]`. Establish `h2 : (p : 𝒪) ^ (m + 1) ∣ c 0 ^ p ^ (m + j) - (a : 𝒪) ^ p ^ (m + j)` using `(pow_dvd_pow _ (by omega)).trans (dvd_sub_pow_of_dvd_sub hca (m + j))`.

Use `dvd_add (dvd_add h1 h2) (hak j) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← pow_succ']`. Expand and normalize the polynomial expressions, which then agree. Establish `hpz : (p : 𝒪) ∣ v - (a : 𝒪) ^ p ^ m`. Establish `h` using `dvd_add ((dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hk 0)) (dvd_mul_right (p : 𝒪) (∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + 0)))`.

Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨v', hv'⟩` from `hpz`. Establish `hv'c : ∀ k, (p : 𝒪) ^ m ∣ v' - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * (c (i + 1) ^ p ^ m) ^ p ^ k`. Introduce `k`. Establish `h` using `hk k`.

Rewrite `h` using `[hv', ← mul_sub, pow_succ']`. Establish `h'` using `(mul_dvd_mul_iff_left natCast_p_ne_zero').1 h`. Establish `e : ∀ i, c (i + 1) ^ p ^ (m + k) = (c (i + 1) ^ p ^ m) ^ p ^ k` using `fun i => by`. Rewrite using `[pow_add, pow_mul]`. Simplify using `only [e] at h'`.

Conclude with `h'`. Take `⟨z', hz'⟩` from `ih v' ⟨fun i => c (i + 1) ^ p ^ m, hv'c⟩`. Use `⟨(a : ℤ) ^ p ^ m + p * z', ?_⟩` and prove the remaining obligations. Establish `e : v - (((a : ℤ) ^ p ^ m + p * z' : ℤ) : 𝒪) = (p : 𝒪) * (v' - z')`. Use `push_cast`.

Take the linear combination `hv'`. Rewrite using `[e, pow_succ']`. Conclude with `mul_dvd_mul_left _ hz'`.
-/
theorem exists_int_dvd_sub (m : ℕ) : ∀ v : 𝒪, (∃ c : ℕ → 𝒪, ∀ k : ℕ,
    (p : 𝒪) ^ m ∣ v - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c i ^ p ^ k) →
    ∃ z : ℤ, (p : 𝒪) ^ m ∣ v - z := by
  induction m with
  | zero => intro v _; exact ⟨0, by simp⟩
  | succ m ih =>
    rintro v ⟨c, hc⟩
    have h0 : ∀ k, (p : 𝒪) ∣ v - c 0 ^ p ^ k := fun k => by
      have h := (dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hc k)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h
      have hs : (p : 𝒪) ∣ ∑ i ∈ Finset.range m, (p : 𝒪) ^ (i + 1) * c (i + 1) ^ p ^ k :=
        Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (dvd_pow_self _ i.succ_ne_zero) _
      convert dvd_add h hs using 1
      ring
    have hv1 : (p : 𝒪) ∣ v ^ p - v := by
      have e1 : (p : 𝒪) ∣ v ^ p - c 0 ^ p := by
        have h := dvd_sub_pow_of_dvd_sub (by simpa using h0 0) 1
        rw [pow_one] at h
        exact (dvd_pow_self (p : 𝒪) two_ne_zero).trans h
      have e2 := h0 1
      rw [pow_one] at e2
      convert dvd_sub e1 e2 using 1
      ring
    obtain ⟨a, hap, ha⟩ := exists_natCast_dvd_sub_of_dvd_pow_sub hv1
    have hca : (p : 𝒪) ∣ c 0 - a := by
      have h := h0 0
      rw [pow_zero, pow_one] at h
      convert dvd_sub ha h using 1
      ring
    have hfa : (p : 𝒪) ∣ (a : 𝒪) ^ p - a := by
      have hz : (p : ℤ) ∣ (a : ℤ) ^ p - a := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.pow_card, sub_self]
      have := map_dvd (Int.castRingHom 𝒪) hz
      simpa using this
    have hak : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (a : 𝒪) ^ p ^ (m + j) - (a : 𝒪) ^ p ^ m := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have h1 := dvd_sub_pow_of_dvd_sub hfa (m + j)
        have e : ((a : 𝒪) ^ p) ^ p ^ (m + j) = (a : 𝒪) ^ p ^ (m + (j + 1)) := by
          rw [← pow_mul, ← pow_succ']
          rfl
        rw [e] at h1
        have h2 := (pow_dvd_pow (p : 𝒪) (by omega : m + 1 ≤ m + j + 1)).trans h1
        convert dvd_add h2 ihj using 1
        ring
    have hk : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (v - (a : 𝒪) ^ p ^ m) -
        (p : 𝒪) * ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + j) := by
      intro j
      have h1 := hc (m + j)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h1
      have h2 : (p : 𝒪) ^ (m + 1) ∣ c 0 ^ p ^ (m + j) - (a : 𝒪) ^ p ^ (m + j) :=
        (pow_dvd_pow _ (by omega)).trans (dvd_sub_pow_of_dvd_sub hca (m + j))
      convert dvd_add (dvd_add h1 h2) (hak j) using 1
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_succ']
      ring
    have hpz : (p : 𝒪) ∣ v - (a : 𝒪) ^ p ^ m := by
      have h := dvd_add ((dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hk 0))
        (dvd_mul_right (p : 𝒪) (∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + 0)))
      rwa [sub_add_cancel] at h
    obtain ⟨v', hv'⟩ := hpz
    have hv'c : ∀ k, (p : 𝒪) ^ m ∣
        v' - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * (c (i + 1) ^ p ^ m) ^ p ^ k := by
      intro k
      have h := hk k
      rw [hv', ← mul_sub, pow_succ'] at h
      have h' := (mul_dvd_mul_iff_left natCast_p_ne_zero').1 h
      have e : ∀ i, c (i + 1) ^ p ^ (m + k) = (c (i + 1) ^ p ^ m) ^ p ^ k := fun i => by
        rw [pow_add, pow_mul]
      simp only [e] at h'
      exact h'
    obtain ⟨z', hz'⟩ := ih v' ⟨fun i => c (i + 1) ^ p ^ m, hv'c⟩
    refine ⟨(a : ℤ) ^ p ^ m + p * z', ?_⟩
    have e : v - (((a : ℤ) ^ p ^ m + p * z' : ℤ) : 𝒪) = (p : 𝒪) * (v' - z') := by
      push_cast
      linear_combination hv'
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hz'

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]`. Conclude with `PadicComplex.norm_extends' p q`.
-/
theorem norm_algebraMap_padic (q : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] q‖ = ‖q‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  exact PadicComplex.norm_extends' p q

/- English proof (translation)
The claim follows from `(AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_padic).isUniformInducing.isComplete_range.isClosed`.
-/
theorem isClosed_range_algebraMap_padic : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_padic).isUniformInducing.isComplete_range.isClosed

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `happrox : ∀ m : ℕ, ∃ z : ℤ, ‖((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) - (z : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m`. Introduce `m`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `⟨0, by simpa using mem_normInteger.1 (theta ℂ_[p] p y).2⟩`. Take `⟨c, hc⟩` from `exists_theta_eq_sum_of_phi_iterate (N := 1) le_rfl (by rw [Function.iterate_one]; exact hy) hm`.

Take `⟨z, hz⟩` from `exists_int_dvd_sub m (theta ℂ_[p] p y) ⟨c, fun k => by`. Take `⟨e, he⟩` from `hc k`. Use `⟨e, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [one_mul] at he`. Use `push_cast`.

Rewrite using `[he]`. Use the proof step `ring⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h` using `(dvd_iff_norm_le (pow_ne_zero m natCast_p_ne_zero')).1 hz`. Simplify using `using h`.

Establish `hmem : ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p]))`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `δ hδ`. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one hδ (norm_natCast_p_lt_one (p := p))`. Take `⟨z, hz⟩` from `happrox m`.

Use `⟨algebraMap ℚ_[p] ℂ_[p] z, ⟨z, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, map_intCast]`. Conclude with `hz.trans_lt hm`. Rewrite `hmem` using `[isClosed_range_algebraMap_padic.closure_eq]`. Take `⟨q, hq⟩` from `hmem`.

Conclude with `⟨q, hq.symm⟩`.
-/
theorem theta_mem_range_of_phi_eq {y : ACris ℂ_[p] p} (hy : phi ℂ_[p] p y = y) :
    ∃ q : ℚ_[p], ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q := by
  have happrox : ∀ m : ℕ, ∃ z : ℤ,
      ‖((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) - (z : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simpa using mem_normInteger.1 (theta ℂ_[p] p y).2⟩
    obtain ⟨c, hc⟩ := exists_theta_eq_sum_of_phi_iterate (N := 1) le_rfl
      (by rw [Function.iterate_one]; exact hy) hm
    obtain ⟨z, hz⟩ := exists_int_dvd_sub m (theta ℂ_[p] p y) ⟨c, fun k => by
      obtain ⟨e, he⟩ := hc k
      refine ⟨e, Subtype.ext ?_⟩
      simp only [one_mul] at he
      push_cast
      rw [he]
      ring⟩
    refine ⟨z, ?_⟩
    have h := (dvd_iff_norm_le (pow_ne_zero m natCast_p_ne_zero')).1 hz
    simpa using h
  have hmem : ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p])) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_natCast_p_lt_one (p := p))
    obtain ⟨z, hz⟩ := happrox m
    refine ⟨algebraMap ℚ_[p] ℂ_[p] z, ⟨z, rfl⟩, ?_⟩
    rw [dist_eq_norm, map_intCast]
    exact hz.trans_lt hm
  rw [isClosed_range_algebraMap_padic.closure_eq] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

end Approx

section Plus

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite `ih`, the goal using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `ih`.

Use `⟨(p : ACris ℂ_[p] p) ^ (m - 1) * phi ℂ_[p] p b, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← ha, ← hb]`. Rewrite using `[map_mul, map_pow, map_natCast]`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_pow_of_p_pow_mul_phi_eq {a : ACris ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a) (j : ℕ) : a ∈ 𝔭 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ih ⊢
    obtain ⟨b, hb⟩ := ih
    refine ⟨(p : ACris ℂ_[p] p) ^ (m - 1) * phi ℂ_[p] p b, ?_⟩
    conv_rhs => rw [← ha, ← hb]
    rw [map_mul, map_pow, map_natCast]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y`. Take `⟨k, hk⟩` from `s.2`. Simplify using `only at hs`. Rewrite `hs` using `[← hk, map_pow, map_natCast]`. Establish `h1` using `congrArg (phiPlus ℂ_[p] p) hs`.

Rewrite `h1` using `[map_mul, map_pow, map_natCast, phiPlus_algebraMap]`. Establish `ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a`. Apply `algebraMap_aCris_injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, map_natCast, ← h1, ← hs]`. Use `conv_rhs => rw [← hy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `ha0 : a = 0` using `IsHausdorff.haus' (I := 𝔭) a fun j => by`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `mem_pow_of_p_pow_mul_phi_eq hm ha j`. Rewrite `hs` using `[ha0, map_zero]`.

Conclude with `(isUnit_p_bCrisPlus.pow k).mul_left_eq_zero.1 hs`.
-/
theorem eq_zero_of_p_pow_mul_phiPlus_eq {y : BCrisPlus ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (hy : (p : BCrisPlus ℂ_[p] p) ^ m * phiPlus ℂ_[p] p y = y) : y = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk, map_pow, map_natCast] at hs
  have h1 := congrArg (phiPlus ℂ_[p] p) hs
  rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap] at h1
  have ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a := by
    apply algebraMap_aCris_injective
    rw [map_mul, map_pow, map_natCast, ← h1, ← hs]
    conv_rhs => rw [← hy]
    ring
  have ha0 : a = 0 := IsHausdorff.haus' (I := 𝔭) a fun j => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact mem_pow_of_p_pow_mul_phi_eq hm ha j
  rw [ha0, map_zero] at hs
  exact (isUnit_p_bCrisPlus.pow k).mul_left_eq_zero.1 hs

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in
/- English proof (translation)
Rewrite using `[iotaPlus_periodTPlus]`. Conclude with `fontaineT_ne_zero hε hζ`.
-/
theorem iotaPlus_periodTPlus_ne_zero : iotaPlus ℂ_[p] p (periodTPlus hε) ≠ 0 := by
  rw [iotaPlus_periodTPlus]
  exact fontaineT_ne_zero hε hζ

include hζ in

/- English proof (translation)
The claim follows from `iotaPlus_injective (K := ℂ_[p]) (p := p) (mul_left_cancel₀ (iotaPlus_periodTPlus_ne_zero hε hζ) (by rw [← map_mul, ← map_mul, h]))`.
-/
theorem periodTPlus_mul_left_cancel {a b : BCrisPlus ℂ_[p] p}
    (h : periodTPlus hε * a = periodTPlus hε * b) : a = b :=
  iotaPlus_injective (K := ℂ_[p]) (p := p) (mul_left_cancel₀ (iotaPlus_periodTPlus_ne_zero hε hζ)
    (by rw [← map_mul, ← map_mul, h]))

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', ih, map_mul, map_pow, map_pow, map_natCast, hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_phiPlus_eq_pow_mul {y : BCrisPlus ℂ_[p] p} {n : ℕ}
    (hy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y) (k : ℕ) :
    (phiPlus ℂ_[p] p)^[k] y = ((p : BCrisPlus ℂ_[p] p) ^ n) ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_pow, map_natCast, hy]
    ring

include hε hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y`. Take `⟨k, hk⟩` from `s.2`. Simplify using `only at hs`. Rewrite `hs` using `[← hk, map_pow, map_natCast]`. Establish `hφa : phi ℂ_[p] p a = a`.

Apply `algebraMap_aCris_injective` to reduce the goal to its premises. Establish `h1` using `congrArg (phiPlus ℂ_[p] p) hs`. Rewrite `h1` using `[map_mul, map_pow, map_natCast, phiPlus_algebraMap, hy, hs]`. Conclude with `h1.symm`. Take `⟨q0, hq0⟩` from `theta_mem_range_of_phi_eq hφa`.

Use `⟨q0 / (p : ℚ_[p]) ^ k, ?_⟩` and prove the remaining obligations. Use `set y' := y - algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (q0 / (p : ℚ_[p]) ^ k) with hy'_def`. Establish `hy' : phiPlus ℂ_[p] p y' = y'` using `by rw [hy'_def, map_sub, hy, phiPlus_algebraMap_padic]`. Establish `hθ : θdR (iotaPlus ℂ_[p] p y') = 0`. Establish `h1` using `congrArg (fun z => θdR (iotaPlus ℂ_[p] p z)) hs`.

Simplify using `only [map_mul, map_pow, map_natCast, thetaField_iotaPlus_algebraMap, hq0] at h1`. Rewrite using `[hy'_def, map_sub, map_sub, iotaPlus_algebraMap_padic, thetaBDeRhamPlusField_algebraMap, sub_eq_zero]`. Establish `hp0 : (p : ℂ_[p]) ^ k ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)`. Apply `mul_right_cancel₀ hp0` to reduce the goal to its premises. Rewrite using `[h1, map_div₀, map_pow, map_natCast, div_mul_cancel₀ _ hp0]`.

Establish `hall : ∀ n, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] y')) = 0` using `fun n => by`. Rewrite using `[Function.iterate_fixed hy' n, hθ]`. Establish `hmem` using `phiPlus_mem_span_periodT hε hζ hall`. Rewrite `hmem` using `[hy']`. Take `⟨y'', hy''⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Establish `h2 : (p : BCrisPlus ℂ_[p] p) ^ 1 * phiPlus ℂ_[p] p y'' = y''`. Apply `periodTPlus_mul_left_cancel hε hζ` to reduce the goal to its premises. Establish `h3` using `congrArg (phiPlus ℂ_[p] p) hy''`. Rewrite `h3` using `[map_mul, phiPlus_periodTPlus, hy', ← hy'']`. Rewrite using `[pow_one]`.

Take the linear combination `h3`. Establish `h4` using `eq_zero_of_p_pow_mul_phiPlus_eq le_rfl h2`. Rewrite `hy''` using `[h4, zero_mul]`. Rewrite using `[← sub_eq_zero, ← hy'_def, ← hy'']`.
-/
theorem exists_eq_algebraMap_of_phiPlus_eq {y : BCrisPlus ℂ_[p] p}
    (hy : phiPlus ℂ_[p] p y = y) : ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk, map_pow, map_natCast] at hs
  have hφa : phi ℂ_[p] p a = a := by
    apply algebraMap_aCris_injective
    have h1 := congrArg (phiPlus ℂ_[p] p) hs
    rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap, hy, hs] at h1
    exact h1.symm
  obtain ⟨q0, hq0⟩ := theta_mem_range_of_phi_eq hφa
  refine ⟨q0 / (p : ℚ_[p]) ^ k, ?_⟩
  set y' := y - algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (q0 / (p : ℚ_[p]) ^ k) with hy'_def
  have hy' : phiPlus ℂ_[p] p y' = y' := by rw [hy'_def, map_sub, hy, phiPlus_algebraMap_padic]
  have hθ : θdR (iotaPlus ℂ_[p] p y') = 0 := by
    have h1 := congrArg (fun z => θdR (iotaPlus ℂ_[p] p z)) hs
    simp only [map_mul, map_pow, map_natCast, thetaField_iotaPlus_algebraMap, hq0] at h1
    rw [hy'_def, map_sub, map_sub, iotaPlus_algebraMap_padic, thetaBDeRhamPlusField_algebraMap,
      sub_eq_zero]
    have hp0 : (p : ℂ_[p]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    apply mul_right_cancel₀ hp0
    rw [h1, map_div₀, map_pow, map_natCast, div_mul_cancel₀ _ hp0]
  have hall : ∀ n, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] y')) = 0 := fun n => by
    rw [Function.iterate_fixed hy' n, hθ]
  have hmem := phiPlus_mem_span_periodT hε hζ hall
  rw [hy'] at hmem
  obtain ⟨y'', hy''⟩ := Ideal.mem_span_singleton'.1 hmem
  have h2 : (p : BCrisPlus ℂ_[p] p) ^ 1 * phiPlus ℂ_[p] p y'' = y'' := by
    apply periodTPlus_mul_left_cancel hε hζ
    have h3 := congrArg (phiPlus ℂ_[p] p) hy''
    rw [map_mul, phiPlus_periodTPlus, hy', ← hy''] at h3
    rw [pow_one]
    linear_combination h3
  have h4 := eq_zero_of_p_pow_mul_phiPlus_eq le_rfl h2
  rw [h4, zero_mul] at hy''
  rw [← sub_eq_zero, ← hy'_def, ← hy'']

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `y hy _`. Take `⟨q, hq⟩` from `exists_eq_algebraMap_of_phiPlus_eq hε hζ (by rw [hy, pow_zero, one_mul])`. Conclude with `⟨q, by rw [hq, pow_zero, mul_one]⟩`.

Consider the case `succ n ih`. Introduce `y hy hι`. Establish `hθ0 : θdR (iotaPlus ℂ_[p] p y) = 0`. Establish `hT : fontaineT ε hε ^ (n + 1) ∈ RingHom.ker θdR`. Rewrite using `[← IsPerfectoidField.maximalIdeal_bDeRhamPlus, maximalIdeal_eq_span_fontaineT hε hζ]`.

Conclude with `Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ n.succ_pos`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hι`. Rewrite using `[← hd, map_mul, RingHom.mem_ker.1 hT, mul_zero]`. Establish `hall : ∀ k, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[k] y)) = 0` using `fun k => by`. Rewrite using `[iterate_phiPlus_eq_pow_mul hy k, map_mul, map_mul, hθ0, mul_zero]`.

Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hall)`. Use `set y1 := Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * w with hy1_def`. Establish `hinv : Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (p : BCrisPlus ℂ_[p] p) ^ (n + 1) = 1`. Rewrite using `[← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow]`. Establish `hyt : y = periodTPlus hε * y1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, hinv, one_mul]`. Use `_ = Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (w * periodTPlus hε) := by rw [← hy, hw]`. Use `_ = periodTPlus hε * y1 := by rw [hy1_def]; ring`. Establish `hy1 : phiPlus ℂ_[p] p y1 = (p : BCrisPlus ℂ_[p] p) ^ n * y1`.

Apply `isUnit_p_bCrisPlus.mul_left_cancel` to reduce the goal to its premises. Apply `periodTPlus_mul_left_cancel hε hζ` to reduce the goal to its premises. Establish `h3` using `congrArg (phiPlus ℂ_[p] p) hyt`. Rewrite `h3` using `[map_mul, phiPlus_periodTPlus, hy]`. Rewrite `h3` using `[hyt]`.

Take the linear combination `-h3`. Establish `hι1 : iotaPlus ℂ_[p] p y1 ∈ Ideal.span {fontaineT ε hε ^ n}`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hι`. Rewrite `hd` using `[hyt, map_mul, iotaPlus_periodTPlus]`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨d, mul_left_cancel₀ (fontaineT_ne_zero hε hζ) ?_⟩` and prove the remaining obligations. Rewrite using `[← hd]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨q, hq⟩` from `ih hy1 hι1`. Conclude with `⟨q, by rw [hyt, hq]; ring⟩`.
-/
theorem exists_eq_algebraMap_mul_pow_of_phiPlus_eq (n : ℕ) : ∀ {y : BCrisPlus ℂ_[p] p},
    phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y →
    iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT ε hε ^ n} →
    ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * periodTPlus hε ^ n := by
  induction n with
  | zero =>
    intro y hy _
    obtain ⟨q, hq⟩ := exists_eq_algebraMap_of_phiPlus_eq hε hζ (by rw [hy, pow_zero, one_mul])
    exact ⟨q, by rw [hq, pow_zero, mul_one]⟩
  | succ n ih =>
    intro y hy hι
    have hθ0 : θdR (iotaPlus ℂ_[p] p y) = 0 := by
      have hT : fontaineT ε hε ^ (n + 1) ∈ RingHom.ker θdR := by
        rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus, maximalIdeal_eq_span_fontaineT hε hζ]
        exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ n.succ_pos
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hι
      rw [← hd, map_mul, RingHom.mem_ker.1 hT, mul_zero]
    have hall : ∀ k, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[k] y)) = 0 := fun k => by
      rw [iterate_phiPlus_eq_pow_mul hy k, map_mul, map_mul, hθ0, mul_zero]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hall)
    set y1 := Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * w with hy1_def
    have hinv : Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (p : BCrisPlus ℂ_[p] p) ^ (n + 1) =
        1 := by
      rw [← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow]
    have hyt : y = periodTPlus hε * y1 := by
      calc y = Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * ((p : BCrisPlus ℂ_[p] p) ^ (n + 1) * y) := by
            rw [← mul_assoc, hinv, one_mul]
        _ = Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (w * periodTPlus hε) := by rw [← hy, hw]
        _ = periodTPlus hε * y1 := by rw [hy1_def]; ring
    have hy1 : phiPlus ℂ_[p] p y1 = (p : BCrisPlus ℂ_[p] p) ^ n * y1 := by
      apply isUnit_p_bCrisPlus.mul_left_cancel
      apply periodTPlus_mul_left_cancel hε hζ
      have h3 := congrArg (phiPlus ℂ_[p] p) hyt
      rw [map_mul, phiPlus_periodTPlus, hy] at h3
      rw [hyt] at h3
      linear_combination -h3
    have hι1 : iotaPlus ℂ_[p] p y1 ∈ Ideal.span {fontaineT ε hε ^ n} := by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hι
      rw [hyt, map_mul, iotaPlus_periodTPlus] at hd
      rw [Ideal.mem_span_singleton']
      refine ⟨d, mul_left_cancel₀ (fontaineT_ne_zero hε hζ) ?_⟩
      rw [← hd]
      ring
    obtain ⟨q, hq⟩ := ih hy1 hι1
    exact ⟨q, by rw [hyt, hq]; ring⟩

end Plus

end ACris

end GroundTheory.PAdicHodge
