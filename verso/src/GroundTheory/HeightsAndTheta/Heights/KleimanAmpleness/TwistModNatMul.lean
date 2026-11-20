import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Charts

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Rewrite using `[Submodule.mul_eq_span_mul_set]`. Use `show Submodule.span _ _ = _`. Use `congr 1`. Use extensionality with `z`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, g, hg, rfl⟩`. Conclude with `⟨q, hq, g, hg, rfl⟩`. Introduce and unpack `⟨q, hq, g, hg, rfl⟩`. Conclude with `⟨q, hq, g, hg, rfl⟩`.
-/
theorem PowRealises.twist_sub (G Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    (G.twist Q).sub I = Q.sub I * G.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem PowRealises.twistSys_sub (c : ℤ) (I : Kleiman.Chart x) :
    (Kleiman.twistSys F x c).sub I = Kleiman.twistMod F x c I := rfl

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).mp (I.2.2 hi)`. Rewrite using `[Kleiman.twistMod_eq_span a I hi, Kleiman.twistMod_eq_span b I hi, Kleiman.twistMod_eq_span (a + b) I hi, Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]`.
-/
theorem PowRealises.twistMod_mul (a b : ℤ) (I : Kleiman.Chart x) :
    Kleiman.twistMod F x a I * Kleiman.twistMod F x b I = Kleiman.twistMod F x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
  rw [Kleiman.twistMod_eq_span a I hi, Kleiman.twistMod_eq_span b I hi, Kleiman.twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Rewrite using `[Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]`.
-/
theorem PowRealises.twistMod_zero (I : Kleiman.Chart x) : Kleiman.twistMod F x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

/- English proof (translation)
The claim follows from `| 0 => by rw [Nat.cast_zero, zero_mul, pow_zero]; exact PowRealises.twistMod_zero I | p + 1 => by rw [pow_succ', ← PowRealises.twistMod_nat_mul c I p, PowRealises.twistMod_mul] congr 1 push_cast ring`.
-/
theorem PowRealises.twistMod_nat_mul (c : ℤ) (I : Kleiman.Chart x) :
    ∀ p : ℕ, Kleiman.twistMod F x ((p : ℤ) * c) I = Kleiman.twistMod F x c I ^ p
  | 0 => by rw [Nat.cast_zero, zero_mul, pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    rw [pow_succ', ← PowRealises.twistMod_nat_mul c I p, PowRealises.twistMod_mul]
    congr 1
    push_cast
    ring

/- English proof (translation)
The claim follows from `| 0 => by rw [pow_zero]; exact PowRealises.twistMod_zero I | p + 1 => by show ((Q.pow p).twist Q).sub I = _ rw [PowRealises.twist_sub, PowRealises.pow_sub Q I p, pow_succ']`.
-/
theorem PowRealises.pow_sub (Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    ∀ p : ℕ, (Q.pow p).sub I = Q.sub I ^ p
  | 0 => by rw [pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    show ((Q.pow p).twist Q).sub I = _
    rw [PowRealises.twist_sub, PowRealises.pow_sub Q I p, pow_succ']

end Charts

section Model

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

/- English proof (translation)
Rewrite using `[Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]`. Conclude with `a.2`.

Introduce `h`. Use `⟨⟨z * u, h⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul]`. Conclude with `mul_inv_cancel_right₀ hu z`.
-/
theorem PowRealises.mem_span_inv_iff (A : Subalgebra F Ω) {u z : Ω} (hu : u ≠ 0) :
    z ∈ Submodule.span A {u⁻¹} ↔ z * u ∈ A := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨z * u, h⟩, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact mul_inv_cancel_right₀ hu z

variable {K : Type} [Fintype K] {ι : K → Type}

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`.
-/
theorem PowRealises.mem_secOver (y : (Σ k, ι k) → Ω) (n : K → ℤ) (s : Ω) :
    s ∈ secOver F y n ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

/- English proof (translation)
Establish `hu : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `t ht`. Conclude with `(PowRealises.mem_span_inv_iff _ hu).mpr ((PowRealises.mem_secOver y n t).mp ht c hc)`.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]`. Take `⟨m, s, hs, hgen⟩` from `hg`. Take `⟨u, hu', hsum⟩` from `hgen c hc`. Establish `key : (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ = ∑ j, (⟨u j, hu' j⟩ : chartRingOver F y c) • s j`. Rewrite using `[← one_mul (_⁻¹), ← hsum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_assoc, mul_inv_cancel_right₀ hu]`. Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))`.
-/
theorem PowRealises.span_secOver_eq (y : (Σ k, ι k) → Ω) (n : K → ℤ) (hg : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Submodule.span (chartRingOver F y c) (secOver F y n : Set Ω) =
      Submodule.span (chartRingOver F y c) {(∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹} := by
  have hu : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro t ht
    exact (PowRealises.mem_span_inv_iff _ hu).mpr ((PowRealises.mem_secOver y n t).mp ht c hc)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hgen⟩ := hg
    obtain ⟨u, hu', hsum⟩ := hgen c hc
    have key : (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ =
        ∑ j, (⟨u j, hu' j⟩ : chartRingOver F y c) • s j := by
      rw [← one_mul (_⁻¹), ← hsum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, mul_inv_cancel_right₀ hu]
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))

/- English proof (translation)
Establish `h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)`. Rewrite using `[Finset.prod_eq_single k₀]`. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.baseDeg]`. Introduce `k _ hk`. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h0, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hc k)]`.

Use `congr 1`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PowRealises.prod_exp [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (β : K → ℤ) (p : ℕ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ^ p =
      ∏ k, y ⟨k, cc k⟩ ^ (-(p • β + ((p : ℤ) * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

end Model

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod Q β hQ p ct`. Take `⟨c₀, hc₀⟩` from `Kleiman.Generated.full F Ω N x Q`. Take `⟨c₁, hc₁⟩` from `hG F K ι Ω y k₀ hmod β`. Take `⟨c, hc0, hc1⟩ : ∃ c, c₀ ≤ c ∧ c₁ ≤ c` from `⟨max c₀ c₁, le_max_left _ _, le_max_right _ _⟩`. Establish `hgenQ` using `hc₀ c hc0`.

Establish `hgenY` using `hc₁ c hc1`. Take `⟨d, rfl⟩ : ∃ d, ct = (p : ℤ) * c + d` from `⟨ct - (p : ℤ) * c, by ring⟩`. Establish `hchart : ∀ I : Kleiman.Chart x, (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).sub I = Submodule.span (Kleiman.chartRing F x I) ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I`. Introduce `I`. Establish `h1 : (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)`.

Rewrite using `[← hgenQ I, hQ c]`. Rewrite `h1` using `[PowRealises.twist_sub, PowRealises.twistSys_sub]`. Use `show ((Q.toSubSystem.pow p).twist (Kleiman.twistSys F x ((p : ℤ) * c + d))).sub I = _`. Rewrite using `[PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.pow_sub, ← PowRealises.twistMod_mul, PowRealises.twistMod_nat_mul, ← Submodule.span_pow, ← h1, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsecs : (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).secs = ⨅ I : Kleiman.Chart x, (Submodule.span (Kleiman.chartRing F x I) ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I).restrictScalars F`. Simplify using `only [Kleiman.SubSystem.secs, hchart]`. Use extensionality with `s`. Rewrite using `[hsecs, hS F K ι Ω y k₀ N e x hx hmod _ d s, PowRealises.mem_secOver]`. Use `forall_congr' fun cc => forall_congr' fun hc => ?_` and prove the remaining obligations.

Establish `hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Rewrite using `[← Submodule.span_pow, PowRealises.span_secOver_eq y _ hgenY cc hc, Submodule.span_pow, Set.singleton_pow, inv_pow, PowRealises.mem_span_inv_iff _ (pow_ne_zero _ hu), mul_assoc, PowRealises.prod_exp y k₀ β p c d cc hc]`.
-/
theorem PowRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) : PowRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod Q β hQ p ct
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full F Ω N x Q
  obtain ⟨c₁, hc₁⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨c, hc0, hc1⟩ : ∃ c, c₀ ≤ c ∧ c₁ ≤ c := ⟨max c₀ c₁, le_max_left _ _, le_max_right _ _⟩
  have hgenQ := hc₀ c hc0
  have hgenY := hc₁ c hc1
  obtain ⟨d, rfl⟩ : ∃ d, ct = (p : ℤ) * c + d := ⟨ct - (p : ℤ) * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart x, (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).sub I =
      Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I := by
    intro I
    have h1 : (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I =
        Submodule.span (Kleiman.chartRing F x I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgenQ I, hQ c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at h1
    show ((Q.toSubSystem.pow p).twist (Kleiman.twistSys F x ((p : ℤ) * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.pow_sub, ← PowRealises.twistMod_mul,
      PowRealises.twistMod_nat_mul, ← Submodule.span_pow, ← h1, mul_pow]
    ring
  have hsecs : (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).secs = ⨅ I : Kleiman.Chart x,
      (Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) *
        Kleiman.twistMod F x d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e x hx hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_pow, PowRealises.span_secOver_eq y _ hgenY cc hc, Submodule.span_pow, Set.singleton_pow,
    inv_pow, PowRealises.mem_span_inv_iff _ (pow_ne_zero _ hu), mul_assoc, PowRealises.prod_exp y k₀ β p c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
