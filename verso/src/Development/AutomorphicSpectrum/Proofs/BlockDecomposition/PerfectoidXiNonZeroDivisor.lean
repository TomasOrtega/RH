import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.UntiltRegular

variable {W R : Type*} [CommRing W] [CommRing R]

/- English proof (translation)
Rewrite `h`, the goal using `[hmem]`. Rewrite `h` using `[map_mul]`. Conclude with `(mul_left_mem_nonZeroDivisors_eq_zero_iff hxi).mp h`.
-/
theorem mem_span_of_mul_mem_of_hom {l xi : W} (φ : W →+* R)
    (hmem : ∀ y, y ∈ Ideal.span {l} ↔ φ y = 0) (hxi : φ xi ∈ nonZeroDivisors R) (y : W)
    (h : xi * y ∈ Ideal.span {l}) : y ∈ Ideal.span {l} := by
  rw [hmem] at h ⊢
  rw [map_mul] at h
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hxi).mp h

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro t ht`. Simplify using `using ht`. Consider the case `succ m ihm`. Introduce `t ht`.

Rewrite `ht` using `[pow_succ, mul_assoc]`. Conclude with `hl t (ihm _ ht)`.
-/
private theorem eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' {l : W} (hl : ∀ x, l * x = 0 → x = 0) (m : ℕ) :
    ∀ t : W, l ^ m * t = 0 → t = 0 := by
  induction m with
  | zero => intro t ht; simpa using ht
  | succ m ihm =>
    intro t ht
    rw [pow_succ, mul_assoc] at ht
    exact hl t (ihm _ ht)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x hx`.

Establish `hx' : xi * x ∈ Ideal.span {l ^ n}`. Rewrite `hx`, the goal using `[Ideal.mem_span_singleton]`. Conclude with `(pow_dvd_pow l (Nat.le_succ n)).trans hx`. Establish `h1` using `ih x hx'`. Rewrite `h1`, `hx`, the goal using `[Ideal.mem_span_singleton]`.

Take `⟨c, rfl⟩` from `h1`. Take `⟨d, hd⟩` from `hx`. Establish `h2 : xi * c = l * d`. Establish `h0 : l ^ n * (xi * c - l * d) = 0` using `by linear_combination hd`. Conclude with `sub_eq_zero.mp (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' hl n _ h0)`.

Take `⟨e, rfl⟩` from `Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨d, h2⟩))`. Conclude with `⟨e, by ring⟩`.
-/
theorem mem_span_pow_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (n : ℕ) :
    ∀ x, xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hx' : xi * x ∈ Ideal.span {l ^ n} := by
      rw [Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow l (Nat.le_succ n)).trans hx
    have h1 := ih x hx'
    rw [Ideal.mem_span_singleton] at h1 hx ⊢
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, hd⟩ := hx
    have h2 : xi * c = l * d := by
      have h0 : l ^ n * (xi * c - l * d) = 0 := by linear_combination hd
      exact sub_eq_zero.mp (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' hl n _ h0)
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨d, h2⟩))
    exact ⟨e, by ring⟩

/- English proof (translation)
Establish `hall : ∀ n, y ∈ Ideal.span {l ^ n}` using `fun n => mem_span_pow_of_mul_mem hl key n y (by rw [h]; exact zero_mem _)`. Apply `hH.haus y` to reduce the goal to its premises. Introduce `n`. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Conclude with `hall n`.
-/
theorem eq_zero_of_mul_eq_zero {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W) (h : xi * y = 0) :
    y = 0 := by
  have hall : ∀ n, y ∈ Ideal.span {l ^ n} :=
    fun n => mem_span_pow_of_mul_mem hl key n y (by rw [h]; exact zero_mem _)
  apply hH.haus y
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hall n

/- English proof (translation)
Rewrite `h`, the goal using `[Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h`. Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨y, hc.symm⟩))`. Use `⟨d, sub_eq_zero.mp (hl _ ?_)⟩` and prove the remaining obligations. Take the linear combination `hc`.
-/
theorem mem_span_xi_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W)
    (h : l * y ∈ Ideal.span {xi}) : y ∈ Ideal.span {xi} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨y, hc.symm⟩))
  refine ⟨d, sub_eq_zero.mp (hl _ ?_)⟩
  linear_combination hc

/- English proof (translation)
Use `⟨?_, ?_, mem_span_pow_of_mul_mem hl key⟩` and prove the remaining obligations. Rewrite using `[mem_nonZeroDivisors_iff]`. Establish `hq : ∀ x : W ⧸ Ideal.span {xi}, x * Ideal.Quotient.mk (Ideal.span {xi}) l = 0 → x = 0`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Rewrite `hx` using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `mem_span_xi_of_mul_mem hl key x (by rw [mul_comm]; exact hx)`. Conclude with `⟨fun x hx => hq x (by rw [mul_comm]; exact hx), hq⟩`. Rewrite using `[mem_nonZeroDivisors_iff]`.

Establish `hw : ∀ x : W, xi * x = 0 → x = 0` using `fun x hx => eq_zero_of_mul_eq_zero hl hH key x hx`. Conclude with `⟨hw, fun x hx => hw x (by rw [mul_comm]; exact hx)⟩`.
-/
theorem regular_of_key {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) :
    Ideal.Quotient.mk (Ideal.span {xi}) l ∈ nonZeroDivisors (W ⧸ Ideal.span {xi}) ∧
      xi ∈ nonZeroDivisors W ∧
      ∀ (n : ℕ) (x : W), xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  refine ⟨?_, ?_, mem_span_pow_of_mul_mem hl key⟩
  · rw [mem_nonZeroDivisors_iff]
    have hq : ∀ x : W ⧸ Ideal.span {xi}, x * Ideal.Quotient.mk (Ideal.span {xi}) l = 0 → x = 0 := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_xi_of_mul_mem hl key x (by rw [mul_comm]; exact hx)
    exact ⟨fun x hx => hq x (by rw [mul_comm]; exact hx), hq⟩
  · rw [mem_nonZeroDivisors_iff]
    have hw : ∀ x : W, xi * x = 0 → x = 0 := fun x hx => eq_zero_of_mul_eq_zero hl hH key x hx
    exact ⟨hw, fun x hx => hw x (by rw [mul_comm]; exact hx)⟩

/- English proof (translation)
Use `mem_span_of_mul_mem_of_hom (WittVector.constantCoeff : A.W →+* A.A) (fun x => ?_) ?_ y h` and prove the remaining obligations. Rewrite using `[A.mem_span_l_iff x]`. Conclude with `Iff.rfl`. Establish `hc : (WittVector.constantCoeff : A.W →+* A.A) A.xi = -A.pi` using `A.xi_coeff_zero`. Establish `hpi : A.pi ∈ nonZeroDivisors A.A` using `A.tf`.

Rewrite using `[hc, ← neg_one_mul]`. Conclude with `mul_mem isUnit_one.neg.mem_nonZeroDivisors hpi`.
-/
theorem key {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : A.W)
    (h : A.xi * y ∈ Ideal.span {(l : A.W)}) : y ∈ Ideal.span {(l : A.W)} := by
  refine mem_span_of_mul_mem_of_hom (WittVector.constantCoeff : A.W →+* A.A) (fun x => ?_) ?_ y h
  · rw [A.mem_span_l_iff x]
    exact Iff.rfl
  · have hc : (WittVector.constantCoeff : A.W →+* A.A) A.xi = -A.pi := A.xi_coeff_zero
    have hpi : A.pi ∈ nonZeroDivisors A.A := A.tf
    rw [hc, ← neg_one_mul]
    exact mul_mem isUnit_one.neg.mem_nonZeroDivisors hpi

/- English proof (translation)
Introduce `l _ A`. Establish `hreg` using `regular_of_key (W := A.W) (l := (l : A.W)) (xi := A.xi) (fun x hx => A.l_mul_eq_zero hx) inferInstance (fun y hy => key A y hy)`. Use `⟨?_, hreg.2.1, hreg.2.2⟩` and prove the remaining obligations. Establish `h1` using `hreg.1`. Rewrite `h1` using `[map_natCast]`.

Conclude with `h1`.
-/
theorem untilt_regular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧
      ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} →
        x ∈ Ideal.span {(l : A.W) ^ n} := by
  intro l _ A
  have hreg := regular_of_key (W := A.W) (l := (l : A.W)) (xi := A.xi)
    (fun x hx => A.l_mul_eq_zero hx) inferInstance (fun y hy => key A y hy)
  refine ⟨?_, hreg.2.1, hreg.2.2⟩
  have h1 := hreg.1
  rw [map_natCast] at h1
  exact h1

end GlobalTheory.CompanionTheory.UntiltRegular
