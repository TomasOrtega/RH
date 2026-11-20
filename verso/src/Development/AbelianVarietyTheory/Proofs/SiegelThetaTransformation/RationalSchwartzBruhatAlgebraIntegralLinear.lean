import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarAlg

variable {K : Type} [Field K] {κ ι : Type}

/- English proof (translation)
Introduce `k i` and use `(hx k i).add (hy k i)`.
-/
theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

/- English proof (translation)
Introduce `k i`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]`. Conclude with `(hx k i).nsmul n`.
-/
theorem intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `intM_natCast_smul S (h.1 x hx)`. Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `h.2 x _ (intM_natCast_smul S hy)`.
-/
theorem hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (intM_natCast_smul S hy)

/- English proof (translation)
Take `⟨R, hR, h1⟩` from `hφ`. Take `⟨S, hS, h2⟩` from `hψ`. Conclude with `⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩`.
-/
theorem exists_common_level {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `a : φ x = 0`. Distinguish the cases in `b : ψ x = 0`. Conclude with `(hx (by simp only [a, b, hf])).elim`. Conclude with `h2.1 x b`.

Conclude with `h1.1 x a`. Simplify using `only [h1.2 x y hy, h2.2 x y hy]`.
-/
theorem hasLevel_map₂ {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]

/- English proof (translation)
Proceed by induction on `hp using AddSubgroup.closure_induction with`. Consider the case `mem p hp`. Take `⟨y, hy, rfl⟩` from `hp`. Conclude with `fun x => h.2 x y hy`. Consider the case `zero => simp`.

Consider the case `add p q _ _ hp hq => intro x`. Rewrite using `[← add_assoc, hq, hp]`. Consider the case `neg p _ hp => intro x`. Rewrite using `[← hp (x + -p)]`. Simplify using the standard rewrite rules.
-/
theorem apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp

/- English proof (translation)
Take `⟨p, hp⟩` from `QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x`. Rewrite using `[hp]`. Conclude with `apply_add_of_mem_perSub h p.2 x`.
-/
theorem apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by
  obtain ⟨p, hp⟩ := QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x
  rw [hp]
  exact apply_add_of_mem_perSub h p.2 x

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : κ × ι => b p.1 p.2)`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩` and prove the remaining obligations. Establish `h` using `hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite `h` using `[zsmul_eq_mul]`.

Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite `h` using `[e, Int.cast_natCast]`. Conclude with `h`. Rewrite `h` using `[e, Int.cast_neg, Int.cast_natCast, neg_mul]`. Simplify using `using h.neg`.
-/
theorem exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b)`. Rewrite using `[Nat.cast_mul]`. Use `module`. Rewrite using `[e]`.

Conclude with `intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)`. Use `show φ _ = φ _`. Rewrite using `[add_sub_right_comm]`. Conclude with `(hasLevel_mul h N).2 _ y hy`.
-/
theorem hasLevel_translate {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy

/- English proof (translation)
Rewrite using `[← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b : Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']`. Both sides reduce to the same expression.
-/
theorem finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl

end GlobalTheory.SW.HaarAlg

open GlobalTheory.SW.HaarAlg in

/- English proof (translation)
Introduce `K κ ι _ _ _ _ φ ψ hφ hψ`. Take `⟨R, hR, h1, h2⟩` from `exists_common_level hφ hψ`. Establish `hadd : HasLevel R (φ + ψ)` using `hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)`. Establish `hsmul : ∀ c : ℂ, HasLevel R (c • φ)` using `fun c => hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)`. Establish `hmul : HasLevel R (φ * ψ)` using `hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)`.

Establish `hconj : HasLevel R (fun x => conj (φ x))` using `hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)`. Take `⟨e1, f1⟩` from `GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1`. Take `⟨e2, f2⟩` from `GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2`. Use `⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_, fun c => ?_, ?_, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]`.

Unfold `haarAt`. Rewrite using `[← mul_add, ← finsum_add_distrib f1 f2]`. Both sides reduce to the same expression. Rewrite using `[(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]`. Unfold `haarAt`.

Rewrite using `[mul_left_comm c]`. Use `congr 1`. Conclude with `((AddMonoidHom.mulLeft c).map_finsum f1).symm`. Rewrite using `[(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]`. Unfold `haarAt`.

Rewrite using `[map_mul, map_inv₀, map_pow, map_natCast]`. Use `congr 1`. Conclude with `((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm`. Take `⟨N, hN, hb⟩` from `exists_natCast_smul_intM b`. Establish `hRN` using `Nat.mul_pos hR hN`.

Establish `ht` using `hasLevel_translate h1 hb`. Use `⟨⟨_, hRN, ht⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]`. Unfold `haarAt`. Rewrite using `[finsum_translate (hasLevel_mul h1 N) b]`.
-/
theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
