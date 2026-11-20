import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitApprox

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_tmul (a : AF D.host.F) (x : D.host.E) : cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [cA_tmul, cA_tmul, star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [cA_tmul, cA_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, zero_mem _, 0, zero_mem _, by simp, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨d, a, ha, a', ha', h, h'⟩` from `hx`. Take `⟨e, b, hb, b', hb', g, g'⟩` from `hy`.

Use `⟨d + e, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, ← h, ← g, ← map_add, TensorProduct.tmul_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_add, ← h', ← g', ← map_add fp, TensorProduct.tmul_add, map_add c, map_add c]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a x`. Take `⟨m, hm, hx⟩` from `hE x`. Establish `hm' : (m : F) ≠ 0` using `Int.cast_ne_zero.2 hm`.

Take `⟨f, β, hβ, hy⟩` from `hB ((m : F)⁻¹ • φ a)`. Establish `key : ∀ x : E, fp (a ⊗ₜ[F] x - 1 ⊗ₜ[F] (f • (m • x))) = N * (β ⊗ₜ[F] (m • x))`. Introduce `x`. Establish `e2 : φ a ⊗ₜ[F] x = ((m : F)⁻¹ • φ a) ⊗ₜ[F] (m • x)`. Rewrite using `[TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hm', one_smul]`.

Rewrite using `[map_sub, hfp, hfp, h1, e2, hy, TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul f, add_sub_cancel_left, ← TensorProduct.smul_tmul', nsmul_eq_mul]`. Establish `hx' : IsIntegral ℤ (m • σ x)`. Rewrite using `[← map_zsmul]`. Conclude with `hx.map σ.toIntAlgHom`. Use `⟨f • (m • x), _, hI _ hβ _ hx, _, hI _ hβ _ hx', key x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc, ← TensorProduct.smul_tmul, hc, TensorProduct.smul_tmul, map_zsmul]`. Conclude with `key _`.
-/
theorem approx_gen {F A B E : Type} [Field F] [CharZero F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (φ : A → B) (σ : E →+* E) (fp : A ⊗[F] E →+* B ⊗[F] E) (c : A ⊗[F] E →+* A ⊗[F] E)
    (hfp : ∀ a x, fp (a ⊗ₜ[F] x) = φ a ⊗ₜ[F] x) (h1 : φ 1 = 1) (hc : ∀ a x, c (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x)
    (O : Set B) (I : AddSubgroup (B ⊗[F] E)) (hI : ∀ b ∈ O, ∀ x : E, IsIntegral ℤ x → b ⊗ₜ[F] x ∈ I)
    (hE : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x)) (N : ℕ)
    (hB : ∀ y : B, ∃ (f : F) (β : B), β ∈ O ∧ y = algebraMap F B f + N • β) (z : A ⊗[F] E) :
    ∃ x : E, ∃ a ∈ I, ∃ a' ∈ I, fp (z - 1 ⊗ₜ[F] x) = N * a ∧ fp (c z - c (1 ⊗ₜ[F] x)) = N * a' := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, 0, zero_mem _, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, a, ha, a', ha', h, h'⟩ := hx
    obtain ⟨e, b, hb, b', hb', g, g'⟩ := hy
    refine ⟨d + e, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_⟩
    · rw [mul_add, ← h, ← g, ← map_add, TensorProduct.tmul_add]; congr 1; ring
    · rw [mul_add, ← h', ← g', ← map_add fp, TensorProduct.tmul_add, map_add c, map_add c]; congr 1; ring
  | tmul a x =>
    obtain ⟨m, hm, hx⟩ := hE x
    have hm' : (m : F) ≠ 0 := Int.cast_ne_zero.2 hm
    obtain ⟨f, β, hβ, hy⟩ := hB ((m : F)⁻¹ • φ a)
    have key : ∀ x : E, fp (a ⊗ₜ[F] x - 1 ⊗ₜ[F] (f • (m • x))) = N * (β ⊗ₜ[F] (m • x)) := by
      intro x
      have e2 : φ a ⊗ₜ[F] x = ((m : F)⁻¹ • φ a) ⊗ₜ[F] (m • x) := by
        rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [map_sub, hfp, hfp, h1, e2, hy, TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul f, add_sub_cancel_left, ← TensorProduct.smul_tmul', nsmul_eq_mul]
    have hx' : IsIntegral ℤ (m • σ x) := by
      rw [← map_zsmul]
      exact hx.map σ.toIntAlgHom
    refine ⟨f • (m • x), _, hI _ hβ _ hx, _, hI _ hβ _ hx', key x, ?_⟩
    rw [hc, ← TensorProduct.smul_tmul, hc, TensorProduct.smul_tmul, map_zsmul]
    exact key _

/- English proof (translation)
Establish `: IsUnit (N : R)`. Use `(IsUnit.mk0 (N : F) (Nat.cast_ne_zero.2 hN.ne')).map (algebraMap F R)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Conclude with `this.mul_left_cancel h`.
-/
theorem cancel_gen {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {N : ℕ} (hN : 0 < N) {a b : R}
    (h : (N : R) * a = N * b) : a = b := by
  have : IsUnit (N : R) := by
    have := (IsUnit.mk0 (N : F) (Nat.cast_ne_zero.2 hN.ne')).map (algebraMap F R)
    rwa [map_natCast] at this
  exact this.mul_left_cancel h

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, ⟨x, hx⟩, rfl⟩`.
-/
theorem tmul_mem {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    a ⊗ₜ[D.host.F] x ∈ intAE D :=
  AddSubgroup.subset_closure ⟨a, ha, ⟨x, hx⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [neg_mul]`. Conclude with `neg_mem hx`. Consider the case `mem x hx`. Proceed by induction on `hb using AddSubgroup.closure_induction with`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`.

Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hx`. Take `⟨b, hb, y, rfl⟩` from `hy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Use `tmul_mem (fun v => ?_) (x.2.mul y.2)` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_mem (ha v) (hb v)`.
-/
theorem mul_mem_intAE {a b : Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) (hb : b ∈ intAE D) :
    a * b ∈ intAE D := by
  induction ha using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hx
      obtain ⟨b, hb, y, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      refine tmul_mem (fun v => ?_) (x.2.mul y.2)
      rw [map_mul]; exact mul_mem (ha v) (hb v)

/- English proof (translation)
The claim follows from `approx_gen (F := D.host.F) (sndA D.host.F) (starRingEnd D.host.E) (finPart D) (cA D) finPart_tmul (map_one _) cA_tmul (intAf D.host.F) (intAE D) (fun _ hb _ hx => tmul_mem hb hx) (fun x => ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) …`.
-/
theorem approx (N : ℕ) (hN : 0 < N) (z : AE D) : ∃ c : D.host.E, ∃ A ∈ intAE D, ∃ A' ∈ intAE D,
    finPart D (z - incA D c) = N * A ∧ finPart D (cA D z - incA D (star c)) = N * A' :=
  approx_gen (F := D.host.F) (sndA D.host.F) (starRingEnd D.host.E) (finPart D) (cA D) finPart_tmul (map_one _) cA_tmul
    (intAf D.host.F) (intAE D) (fun _ hb _ hx => tmul_mem hb hx)
    (fun x => ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple) N
    (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N hN).1 z

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hNE : (N : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hNk : (N : k) ≠ 0`. Use `(map_ne_zero (p.pr.comp (incA D))).2 hNE` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `he : finPart D p.e ∈ intAE D`.

Use `(p.int_iff 1).1 (one_mem _)` as an intermediate fact. Rewrite `this` using `[← map_one p.pr, p.sec_pr, mul_one]`. Then use the resulting hypothesis. Establish `h0 : (N : AE D) * p.sec (p.pr z / N) = p.e * z`. Rewrite using `[← p.sec_pr, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hNk]`. Establish `h1` using `congrArg (finPart D) h0`.

Rewrite `h1` using `[RingHom.map_mul, RingHom.map_mul, h, mul_left_comm]`. Establish `h1' : finPart D (N : AE D) = N` using `map_natCast (finPart D) N`. Rewrite `h1` using `[h1']`. Establish `h2` using `cancel_gen (F := D.host.F) hN h1`. Establish `h3 : p.pr z / N ∈ 𝒪[k]` using `(p.int_iff _).2 (by rw [h2]; exact mul_mem_intAE he hA)`.

Establish `h4 : valuation k (p.pr z / N) ≤ 1` using `h3`. Establish `h5 : p.pr z = N * (p.pr z / N)` using `(mul_div_cancel₀ _ hNk).symm`. Rewrite using `[h5, map_mul]`. Conclude with `mul_le_of_le_one_right' h4`.
-/
theorem val_le (p : SplitPt D k) (N : ℕ) (hN : 0 < N) (z : AE D) (A : Af D.host.F ⊗[D.host.F] D.host.E)
    (hA : A ∈ intAE D) (h : finPart D z = N * A) : valuation k (p.pr z) ≤ valuation k (N : k) := by
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNk : (N : k) ≠ 0 := by
    have := (map_ne_zero (p.pr.comp (incA D))).2 hNE
    rwa [map_natCast] at this
  have he : finPart D p.e ∈ intAE D := by
    have := (p.int_iff 1).1 (one_mem _)
    rwa [← map_one p.pr, p.sec_pr, mul_one] at this
  have h0 : (N : AE D) * p.sec (p.pr z / N) = p.e * z := by
    rw [← p.sec_pr, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hNk]
  have h1 := congrArg (finPart D) h0
  rw [RingHom.map_mul, RingHom.map_mul, h, mul_left_comm] at h1
  have h1' : finPart D (N : AE D) = N := map_natCast (finPart D) N
  rw [h1'] at h1
  have h2 := cancel_gen (F := D.host.F) hN h1
  have h3 : p.pr z / N ∈ 𝒪[k] := (p.int_iff _).2 (by rw [h2]; exact mul_mem_intAE he hA)
  have h4 : valuation k (p.pr z / N) ≤ 1 := h3
  have h5 : p.pr z = N * (p.pr z / N) := (mul_div_cancel₀ _ hNk).symm
  rw [h5, map_mul]
  exact mul_le_of_le_one_right' h4

/- English proof (translation)
Establish `hlt : ∀ x : 𝒪[k], ¬ IsUnit x → valuation k (x : k) < 1` using `fun x hx => Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx`. Establish `hq` using `hlt _ q.2.not_isUnit`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])`. Use `set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])`.

Establish `hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `FiniteField.cast_card_eq_zero _`. Rewrite `hQ` using `[q.2.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨r, hr⟩` from `hQ`.

Establish `hr' : (Q : k) = (q.1 : k) * r` using `by exact_mod_cast congrArg (fun x : 𝒪[k] => (x : k)) hr`. Establish `hle : valuation k (Q : k) ≤ valuation k ((q.1 : 𝒪[k]) : k)`. Rewrite using `[hr', map_mul]`. Conclude with `mul_le_of_le_one_right' r.2`. Establish `hq0 : 0 < valuation k ((q.1 : 𝒪[k]) : k)`.

Rewrite using `[Valuation.pos_iff]`. Conclude with `fun h => q.2.ne_zero (Subtype.ext h)`. Use `⟨Q * Q, Nat.mul_pos Fintype.card_pos Fintype.card_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, map_mul]`. Conclude with `(mul_le_mul' hle hle).trans_lt (mul_lt_of_lt_one_right hq0 hq)`.
-/
theorem exists_nat (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 ∧
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) < valuation k ((q.1 : 𝒪[k]) : k) := by
  have hlt : ∀ x : 𝒪[k], ¬ IsUnit x → valuation k (x : k) < 1 := fun x hx =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have hq := hlt _ q.2.not_isUnit
  refine ⟨hq, ?_⟩
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨r, hr⟩ := hQ
  have hr' : (Q : k) = (q.1 : k) * r := by exact_mod_cast congrArg (fun x : 𝒪[k] => (x : k)) hr
  have hle : valuation k (Q : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  have hq0 : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [Valuation.pos_iff]
    exact fun h => q.2.ne_zero (Subtype.ext h)
  refine ⟨Q * Q, Nat.mul_pos Fintype.card_pos Fintype.card_pos, ?_⟩
  rw [Nat.cast_mul, map_mul]
  exact (mul_le_mul' hle hle).trans_lt (mul_lt_of_lt_one_right hq0 hq)

/- English proof (translation)
Introduce `D k _ _ _ _ p q`. Take `⟨hq, N, hN, hNq⟩` from `exists_nat q`. Establish `hs : p.sec 1 = p.e` using `by rw [← map_one p.pr, p.sec_pr, mul_one]`. Establish `he : p.pr p.e = 1` using `by rw [← hs, p.pr_sec]`. Establish `hce : p.pr (cA D p.e) = 0`.

Establish `h : p.e * cA D p.e = 0` using `p.split.2.1`. Use `congrArg p.pr h` as an intermediate fact. Rewrite `this` using `[map_mul, he, one_mul, map_zero]`. Then use the resulting hypothesis. Establish `hcq : ∀ a, p.pr (cA D (p.sec a)) = 0` using `fun a => by`. Establish `h : p.sec a = p.e * p.sec a` using `by rw [← p.sec_pr, p.pr_sec]`.

Rewrite using `[h, map_mul, map_mul, hce, zero_mul]`. Take `⟨c, A, hA, A', hA', h, h'⟩` from `approx N hN (p.sec (q.1 : k) + cA D p.e)`. Establish `v1` using `val_le p N hN _ A hA h`. Establish `v2` using `val_le p N hN _ A' hA' h'`. Rewrite `v1` using `[map_sub, map_add, p.pr_sec, hce, add_zero]`.

Rewrite `v2` using `[map_sub, map_add, map_add, hcq, cA_cA, he, zero_add]`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap]; exact v1.trans_lt hNq)`. Rewrite using `[← map_one (valuation k)]`. Conclude with `Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, map_one]; exact v2.trans_lt (hNq.trans hq))`.
-/
theorem exists_unif_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k), ∃ c : D.host.E, valuation k (p.pr (incA D c)) = valuation k ((q.1 : 𝒪[k]) : k) ∧ valuation k (p.pr (incA D (star c))) = 1 := by
  intro D k _ _ _ _ p q
  obtain ⟨hq, N, hN, hNq⟩ := exists_nat q
  have hs : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have he : p.pr p.e = 1 := by rw [← hs, p.pr_sec]
  have hce : p.pr (cA D p.e) = 0 := by
    have h : p.e * cA D p.e = 0 := p.split.2.1
    have := congrArg p.pr h
    rwa [map_mul, he, one_mul, map_zero] at this
  have hcq : ∀ a, p.pr (cA D (p.sec a)) = 0 := fun a => by
    have h : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
    rw [h, map_mul, map_mul, hce, zero_mul]
  obtain ⟨c, A, hA, A', hA', h, h'⟩ := approx N hN (p.sec (q.1 : k) + cA D p.e)
  have v1 := val_le p N hN _ A hA h
  have v2 := val_le p N hN _ A' hA' h'
  rw [map_sub, map_add, p.pr_sec, hce, add_zero] at v1
  rw [map_sub, map_add, map_add, hcq, cA_cA, he, zero_add] at v2
  refine ⟨c, ?_, ?_⟩
  · exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap]; exact v1.trans_lt hNq)
  · rw [← map_one (valuation k)]
    exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, map_one]; exact v2.trans_lt (hNq.trans hq))

end GlobalTheory.FinPl.SplitApprox
