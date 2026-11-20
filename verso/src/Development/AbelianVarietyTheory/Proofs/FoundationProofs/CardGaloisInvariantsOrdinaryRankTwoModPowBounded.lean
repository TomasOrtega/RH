import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce and unpack `⟨u, hu⟩`. Establish `h2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1` using `CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2`. Establish `h3 : (((u : c.Oˣ) : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1`. Rewrite using `[← Subalgebra.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Establish `hu' : (((u : c.Oˣ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l)` using `by rw [hu]; simp`. Rewrite `h3` using `[hu']`. Establish `hl : ‖((l : ℕ) : Qbar l)‖ < 1`. Establish `e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l])` using `by simp`. Rewrite using `[e, norm_algebraMap']`.

Conclude with `Padic.norm_p_lt_one`. Use `congrArg norm h3` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_one]`. Establish `: ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem natCast_not_isUnit (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : (((u : c.Oˣ) : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have hu' : (((u : c.Oˣ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  rw [hu'] at h3
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have := congrArg norm h3
  rw [norm_mul, norm_one] at this
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hl
  linarith

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hd hϖ`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h`.

Establish `h'` using `congrArg (fun x : c.O => (x : Qbar l)) h`. Simplify using `only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'`. Conclude with `(Fact.out : l.Prime).ne_zero h'`. Establish `hl : ϖ ∣ ((l : ℕ) : c.O)`. Take `⟨m, hm⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ`.

Break down `m with _ | m` into its components or cases. Conclude with `absurd (hm.isUnit_iff.2 (by simp)) (natCast_not_isUnit c)`. Conclude with `(dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd`. Conclude with `hk.dvd.trans (pow_dvd_pow_of_dvd hl k)`.
-/
theorem exists_dvd_pow (c : Coef l) {d : c.O} (hd : d ≠ 0) : ∃ k : ℕ, d ∣ ((l : ℕ) : c.O) ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : Qbar l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hl : ϖ ∣ ((l : ℕ) : c.O) := by
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) (natCast_not_isUnit c)
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  exact hk.dvd.trans (pow_dvd_pow_of_dvd hl k)

end GlobalTheory.Ord2.GwCard

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `set f := AddMonoidHom.mulLeft x`. Establish `h1` using `AddSubgroup.card_mul_index f.ker`. Establish `h2` using `AddSubgroup.card_mul_index f.range`. Establish `h3 : f.ker.index = Nat.card f.range`. Rewrite using `[AddSubgroup.index]`.

Conclude with `Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv`. Rewrite `h1` using `[h3]`. Establish `hpos : 0 < Nat.card f.range` using `Nat.card_pos`. Use `h1.trans h2.symm` as an intermediate fact. Rewrite `this` using `[mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hpos this`.
-/
theorem card_ker_eq_index {R : Type} [Ring R] [Finite R] (x : R) :
    Nat.card (AddMonoidHom.mulLeft x).ker = (AddMonoidHom.mulLeft x).range.index := by
  set f := AddMonoidHom.mulLeft x
  have h1 := AddSubgroup.card_mul_index f.ker
  have h2 := AddSubgroup.card_mul_index f.range
  have h3 : f.ker.index = Nat.card f.range := by
    rw [AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rw [h3] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have := h1.trans h2.symm
  rw [mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

/- English proof (translation)
Take `⟨g, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)`. Use `⟨Nat.card (Fin g → ZMod (l ^ k)), fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[card_ker_eq_index, AddSubgroup.index]`. Use `set H := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).range`. Use `Nat.card_le_card_of_surjective (fun z : Fin g → ZMod (l ^ k) => (QuotientAddGroup.mk (∑ i, (z i).val • red c n (s i)) : Qn c n ⧸ H)) ?_` and prove the remaining obligations.

Introduce `q`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨x, rfl⟩` from `red_surjective c n y`. Establish `hx : x ∈ Submodule.span ℤ_[l] (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx`.

Use `⟨fun i => PadicInt.toZModPow k (a i), ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[QuotientAddGroup.eq, ← ha, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : ℤ_[l], a i - (PadicInt.toZModPow k (a i)).val = (l : ℤ_[l]) ^ k * w := by`.

Establish `hm : a i - ((PadicInt.toZModPow k (a i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k}`. Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 hm`. Conclude with `⟨w, by rw [← hw, mul_comm]⟩`. Use `⟨red c n (w • s i), ?_⟩` and prove the remaining obligations.

Establish `e1 : (PadicInt.toZModPow k (a i)).val • red c n (s i) = red c n ((((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ_[l]) • s i)`. Rewrite using `[Nat.cast_smul_eq_nsmul, map_nsmul]`. Rewrite using `[e1, ← map_neg, ← map_add, ← neg_smul, ← add_smul, neg_add_eq_sub, hw, mul_smul]`. Simplify using `only [AddMonoidHom.coe_mulLeft]`. Rewrite using `[← map_natCast (red c n), ← map_pow, ← map_mul]`.

Use `congr 1`. Rewrite using `[← Nat.cast_pow (α := ℤ_[l]), Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]`.
-/
theorem exists_card_ker_pow_le (c : Coef l) (k : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, Nat.card (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker ≤ B := by
  obtain ⟨g, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine ⟨Nat.card (Fin g → ZMod (l ^ k)), fun n => ?_⟩
  rw [card_ker_eq_index, AddSubgroup.index]
  set H := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).range
  refine Nat.card_le_card_of_surjective
    (fun z : Fin g → ZMod (l ^ k) => (QuotientAddGroup.mk (∑ i, (z i).val • red c n (s i)) : Qn c n ⧸ H)) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow k (a i), ?_⟩
  simp only
  rw [QuotientAddGroup.eq, ← ha, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[l], a i - (PadicInt.toZModPow k (a i)).val = (l : ℤ_[l]) ^ k * w := by
    have hm : a i - ((PadicInt.toZModPow k (a i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨w, by rw [← hw, mul_comm]⟩
  refine ⟨red c n (w • s i), ?_⟩
  have e1 : (PadicInt.toZModPow k (a i)).val • red c n (s i) = red c n ((((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ_[l]) • s i) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [e1, ← map_neg, ← map_add, ← neg_smul, ← add_smul, neg_add_eq_sub, hw, mul_smul]
  simp only [AddMonoidHom.coe_mulLeft]
  rw [← map_natCast (red c n), ← map_pow, ← map_mul]
  congr 1
  rw [← Nat.cast_pow (α := ℤ_[l]), Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.Ord2.GwCard

namespace GlobalTheory.Ord2.GwCard

/- English proof (translation)
Introduce `l _ Ω _ _ _ e S A W hW c hint hN`. Take `⟨φ, -, hφ⟩` from `GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one (l := l) (Ω := Ω) (e := e) (S := S) (A := A) (W := W) hW`. Set `M : Matrix (Fin 2) (Fin 2) c.O` to `Matrix.of fun i j => ⟨mat W φ i j, hint φ i j⟩`. Establish `hM : (c.O.val : c.O →+* Qbar l).mapMatrix (M - 1) = mat W φ - 1`. Rewrite using `[map_sub, map_one]`.

Use `congr 1`. Establish `hd : (M - 1).det ≠ 0`. Introduce `h`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[← hM, ← RingHom.map_det, h, map_zero]`.

Take `⟨k, y, hy⟩` from `exists_dvd_pow c hd`. Take `⟨B, hB⟩` from `exists_card_ker_pow_le c k`. Use `⟨B ^ 2, fun n _ => ?_⟩` and prove the remaining obligations. Use `set K := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker`. Establish `hred : (red c n).mapMatrix (M - 1) = matQ c n W hint φ - 1`.

Rewrite using `[map_sub, map_one]`. Use `congr 1`. Establish `hmem : ∀ m ∈ H0 (rhoS c n W hint S hN), ∀ i, m i ∈ K`. Introduce `m hm i`. Establish `h1 : matQ c n W hint φ *ᵥ m = m` using `(mem_riemannRochSpace_iff_regularAt_everywhere _ m).1 hm (toGS Ω (S : Set Pl) φ)`.

Establish `h2 : (matQ c n W hint φ - 1) *ᵥ m = 0`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]`. Establish `h3 : (matQ c n W hint φ - 1).det • m = 0`. Rewrite using `[← Matrix.one_mulVec m, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]`. Establish `h4 : red c n (M - 1).det * m i = 0`.

Rewrite using `[RingHom.map_det, hred]`. Use `congrFun h3 i` as an intermediate fact. Simplify using `using this`. Use `show ((l : ℕ) : Qn c n) ^ k * m i = 0`. Rewrite using `[← map_natCast (red c n), ← map_pow, hy, map_mul, mul_comm (red c n _), mul_assoc, h4, mul_zero]`.

Set `F : H0 (rhoS c n W hint S hN) → (Fin 2 → K)` to `fun m i => ⟨m.1 i, hmem m.1 m.2 i⟩`. Establish `hF : Function.Injective F`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Conclude with `congrArg Subtype.val (congrFun hab i)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_card_H0_rhoS_le : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  intro l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨φ, -, hφ⟩ := GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one (l := l) (Ω := Ω) (e := e) (S := S) (A := A) (W := W) hW
  let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W φ i j, hint φ i j⟩
  have hM : (c.O.val : c.O →+* Qbar l).mapMatrix (M - 1) = mat W φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hd : (M - 1).det ≠ 0 := by
    intro h
    apply hφ
    rw [← hM, ← RingHom.map_det, h, map_zero]
  obtain ⟨k, y, hy⟩ := exists_dvd_pow c hd
  obtain ⟨B, hB⟩ := exists_card_ker_pow_le c k
  refine ⟨B ^ 2, fun n _ => ?_⟩
  set K := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker
  have hred : (red c n).mapMatrix (M - 1) = matQ c n W hint φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hmem : ∀ m ∈ H0 (rhoS c n W hint S hN), ∀ i, m i ∈ K := by
    intro m hm i
    have h1 : matQ c n W hint φ *ᵥ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).1 hm (toGS Ω (S : Set Pl) φ)
    have h2 : (matQ c n W hint φ - 1) *ᵥ m = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    have h3 : (matQ c n W hint φ - 1).det • m = 0 := by
      rw [← Matrix.one_mulVec m, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h2,
        Matrix.mulVec_zero]
    have h4 : red c n (M - 1).det * m i = 0 := by
      rw [RingHom.map_det, hred]
      have := congrFun h3 i
      simpa using this
    show ((l : ℕ) : Qn c n) ^ k * m i = 0
    rw [← map_natCast (red c n), ← map_pow, hy, map_mul, mul_comm (red c n _), mul_assoc, h4, mul_zero]
  let F : H0 (rhoS c n W hint S hN) → (Fin 2 → K) := fun m i => ⟨m.1 i, hmem m.1 m.2 i⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc Nat.card (H0 (rhoS c n W hint S hN)) ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective F hF
    _ = Nat.card K ^ 2 := by simp [Nat.card_fun]
    _ ≤ B ^ 2 := Nat.pow_le_pow_left (hB n) 2

end GlobalTheory.Ord2.GwCard
