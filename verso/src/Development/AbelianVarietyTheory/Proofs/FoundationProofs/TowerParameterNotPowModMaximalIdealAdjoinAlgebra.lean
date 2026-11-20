import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicIntStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizerStatement

open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.NotPow

/- English proof (translation)
Introduce `p _ O Ω _ _ _ hmax v hv T hT π hπ hπ0 hvπ hpπ f hf hstep`. Establish `hint : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x ≤ 1` using `fun x hx => (hv x).2 (Algebra.adjoin_le (S := integralClosure O Ω) (fun t ht => hT t ht) hx)`. Establish `hunit : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x = 1 → ∃ w ∈ Algebra.adjoin O (T : Set Ω), x * w = 1`. Introduce `x hx hx1`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hx1` using `[map_zero]`. Conclude with `zero_ne_one hx1`. Take `⟨P, hPm, hP⟩` from `(hv x⁻¹).1 (by rw [map_inv₀, hx1, inv_one])`. Use `letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)`.

Establish `h1` using `Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) x⁻¹ P`. Rewrite `h1` using `[hP, invOf_eq_inv, inv_inv]`. Establish `h2 : Polynomial.eval₂ (algebraMap O Ω) x P.reverse = 0` using `(mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hx0))`. Establish `h3` using `Polynomial.divX_mul_X_add P.reverse`. Rewrite `h3` using `[Polynomial.coeff_zero_reverse, hPm.leadingCoeff, Polynomial.C_1]`.

Rewrite `h2` using `[← h3, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_one]`. Use `⟨-Polynomial.eval₂ (algebraMap O Ω) x (Polynomial.divX P.reverse), neg_mem ?_, ?_⟩` and prove the remaining obligations. Establish `hm` using `(Polynomial.aeval (⟨x, hx⟩ : Algebra.adjoin O (T : Set Ω)) (Polynomial.divX P.reverse)).2`. Rewrite `hm` using `[Polynomial.aeval_subalgebra_coe, Polynomial.aeval_def]`. Then use the resulting hypothesis. Take the linear combination `-h2`.

Set `I : Ideal (Algebra.adjoin O (T : Set Ω))` to `Ideal.span {⟨π, hπ⟩}`. Establish `memI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I ↔ (z : Ω) / π ∈ Algebra.adjoin O (T : Set Ω)`. Introduce `z`. Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, rfl⟩ show ((w : Ω) * π) / π ∈ _`. Rewrite using `[mul_div_cancel_right₀ _ hπ0]`. Conclude with `w.2`. Introduce `h`. Conclude with `⟨⟨(z : Ω) / π, h⟩, Subtype.ext (div_mul_cancel₀ _ hπ0)⟩`.

Establish `hvI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I → v z < 1`. Introduce `z hz`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Use `show v ((w : Ω) * π) < 1`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpI : (p : Algebra.adjoin O (T : Set Ω)) ∈ I`. Rewrite using `[memI]`. Simplify using `using hpπ`. Use `haveI hmaxI := hmax`.

Use `letI hk : Field (O ⧸ Ideal.span {(p : O)}) := Ideal.Quotient.field _`. Use `haveI : CharP (O ⧸ Ideal.span {(p : O)}) p := CharP.quotient O p (fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.2 hu))`. Set `φ : (O ⧸ Ideal.span {(p : O)}) →+* Algebra.adjoin O (T : Set Ω) ⧸ I` to `Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (algebraMap O _)) (by`. Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`.

Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]`. Conclude with `I.mul_mem_left _ hpI)`. Use `letI : Algebra (O ⧸ Ideal.span {(p : O)}) (Algebra.adjoin O (T : Set Ω) ⧸ I) := φ.toAlgebra`. Use `haveI hnt : Nontrivial (Algebra.adjoin O (T : Set Ω) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by`. Introduce `h`.

Establish `h1 : (1 : Algebra.adjoin O (T : Set Ω)) ∈ I` using `by rw [h]; exact Submodule.mem_top`. Use `hvI 1 h1` as an intermediate fact. Simplify using `at this)`. Use `haveI : IsLocalRing (Algebra.adjoin O (T : Set Ω) ⧸ I) := by`. Use `{ toNontrivial := hnt, isUnit_or_isUnit_of_add_one := ?_ }` and prove the remaining obligations.

Introduce `a b hab`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `hxy : x + y - 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hab, map_one, sub_self]`.

Establish `hv1` using `hvI _ hxy`. Establish `key : v x = 1 ∨ v y = 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hx' : v x < 1` using `lt_of_le_of_ne (hint _ x.2) hcon.1`.

Establish `hy' : v y < 1` using `lt_of_le_of_ne (hint _ y.2) hcon.2`. Establish `e1 : (1 : Ω) = ((x : Ω) + y) - ((x + y - 1 : Algebra.adjoin O (T : Set Ω)) : Ω)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: v (1 : Ω) < 1`.

Rewrite using `[e1]`. Conclude with `lt_of_le_of_lt (v.map_sub _ _) (max_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt hx' hy')) hv1)`. Simplify using `at this`. Break down `key with h | h` into its components or cases. Take `⟨w, hw, hxw⟩` from `hunit _ x.2 h left`.

Establish `e : x * ⟨w, hw⟩ = 1` using `Subtype.ext hxw`. Use `IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, e, map_one]`. Take `⟨w, hw, hyw⟩` from `hunit _ y.2 h right`. Establish `e : y * ⟨w, hw⟩ = 1` using `Subtype.ext hyw`.

Use `IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, e, map_one]`. Set `T' : Finset (Algebra.adjoin O (T : Set Ω) ⧸ I)` to `T.attach.image (fun t => Ideal.Quotient.mk I ⟨t.1, Algebra.subset_adjoin (Finset.mem_coe.2 t.2)⟩)`. Establish `hgen0 : ∀ x (hx : x ∈ Algebra.adjoin O (T : Set Ω)), Ideal.Quotient.mk I ⟨x, hx⟩ ∈ Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I))`. Introduce `x hx`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Apply `Algebra.subset_adjoin` to reduce the goal to its premises. Rewrite using `[Finset.mem_coe, Finset.mem_image]`. Conclude with `⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩`.

Consider the case `algebraMap r`. Use `Subalgebra.algebraMap_mem (Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I))) (Ideal.Quotient.mk (Ideal.span {(p : O)}) r) using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Consider the case `add x y hx hy ihx ihy`. Establish `e : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`.

Rewrite using `[e, map_add]`. Conclude with `add_mem ihx ihy`. Consider the case `mul x y hx hy ihx ihy`. Establish `e : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ * ⟨y, hy⟩` using `rfl`. Rewrite using `[e, map_mul]`.

Conclude with `mul_mem ihx ihy`. Establish `hgen : Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `a -`. Take `⟨⟨x, hx⟩, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Conclude with `hgen0 x hx`. Establish `hfrob : ∀ t ∈ T', t ^ p ^ f = t`. Introduce `t ht`. Rewrite `ht` using `[Finset.mem_image]`. Take `⟨⟨t0, ht0⟩, -, rfl⟩` from `ht`.

Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]`. Simplify using `using hstep t0 ht0`. Take `⟨hfield, hroot⟩` from `GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed p (O ⧸ Ideal.span {(p : O)}) (Algebra.adjoin O (T : Set Ω) ⧸ I) T' f hf hgen hfrob`. Establish `hzero : ∀ z : Algebra.adjoin O (T : Set Ω), v z < 1 → z ∈ I`. Introduce `z hz`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Assume the negation of the conclusion as `hne`. Take `⟨b, hb⟩` from `hfield.mul_inv_cancel hne`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `h1 : z * w - 1 ∈ I`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]`. Establish `h2` using `hvI _ h1`. Establish `h3 : v ((z : Ω) * w) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e1 : (1 : Ω) = (z : Ω) * w - ((z * w - 1 : Algebra.adjoin O (T : Set Ω)) : Ω)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: v (1 : Ω) < 1`. Rewrite using `[e1]`.

Conclude with `lt_of_le_of_lt (v.map_sub _ _) (max_lt h3 h2)`. Simplify using `at this`. Use `⟨fun x hx hvx => (memI ⟨x, hx⟩).1 (hzero _ hvx), ?_⟩` and prove the remaining obligations. Introduce `y hy a hva`. Establish `hI : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) ^ p - algebraMap O _ a ∈ I` using `hzero _ (by simpa using hva)`.

Establish `heq : (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p = algebraMap (O ⧸ Ideal.span {(p : O)}) _ (Ideal.Quotient.mk _ a)`. Establish `h0` using `(Ideal.Quotient.eq_zero_iff_mem).2 hI`. Rewrite `h0` using `[map_sub, map_pow]`. Conclude with `sub_eq_zero.1 h0`. Take `⟨b', hb'⟩` from `hroot _ _ heq`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b'`. Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `h5 : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) - algebraMap O _ b ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb', sub_eq_zero]`. Both sides reduce to the same expression.

Simplify using `using hvI _ h5`.
-/
theorem residue_core : ∀ (p : ℕ) [Fact p.Prime] (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω], (Ideal.span {(p : O)}).IsMaximal →
  ∀ (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (T : Finset Ω), (∀ t ∈ T, IsIntegral O t) → ∀ π ∈ Algebra.adjoin O (T : Set Ω), π ≠ 0 → v π < 1 →
  (p : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) →
  ∀ f : ℕ, 0 < f → (∀ t ∈ T, (t ^ p ^ f - t) / π ∈ Algebra.adjoin O (T : Set Ω)) →
  (∀ x ∈ Algebra.adjoin O (T : Set Ω), v x < 1 → x / π ∈ Algebra.adjoin O (T : Set Ω)) ∧
  ∀ y ∈ Algebra.adjoin O (T : Set Ω), ∀ a : O, v (y ^ p - algebraMap O Ω a) < 1 → ∃ b : O, v (y - algebraMap O Ω b) < 1 := by
  intro p _ O Ω _ _ _ hmax v hv T hT π hπ hπ0 hvπ hpπ f hf hstep
  classical
  have hint : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure O Ω) (fun t ht => hT t ht) hx)
  have hunit : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x = 1 →
      ∃ w ∈ Algebra.adjoin O (T : Set Ω), x * w = 1 := by
    intro x hx hx1
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx1
      exact zero_ne_one hx1
    obtain ⟨P, hPm, hP⟩ := (hv x⁻¹).1 (by rw [map_inv₀, hx1, inv_one])
    letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
    have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) x⁻¹ P
    rw [hP, invOf_eq_inv, inv_inv] at h1
    have h2 : Polynomial.eval₂ (algebraMap O Ω) x P.reverse = 0 :=
      (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hx0))
    have h3 := Polynomial.divX_mul_X_add P.reverse
    rw [Polynomial.coeff_zero_reverse, hPm.leadingCoeff, Polynomial.C_1] at h3
    rw [← h3, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_one] at h2
    refine ⟨-Polynomial.eval₂ (algebraMap O Ω) x (Polynomial.divX P.reverse), neg_mem ?_, ?_⟩
    · have hm := (Polynomial.aeval (⟨x, hx⟩ : Algebra.adjoin O (T : Set Ω))
        (Polynomial.divX P.reverse)).2
      rwa [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_def] at hm
    · linear_combination -h2
  let I : Ideal (Algebra.adjoin O (T : Set Ω)) := Ideal.span {⟨π, hπ⟩}
  have memI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I ↔
      (z : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) := by
    intro z
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩
      show ((w : Ω) * π) / π ∈ _
      rw [mul_div_cancel_right₀ _ hπ0]
      exact w.2
    · intro h
      exact ⟨⟨(z : Ω) / π, h⟩, Subtype.ext (div_mul_cancel₀ _ hπ0)⟩
  have hvI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I → v z < 1 := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    show v ((w : Ω) * π) < 1
    rw [map_mul]
    calc v w * v π ≤ 1 * v π := mul_le_mul_of_nonneg_right (hint _ w.2) zero_le
      _ < 1 := by rw [one_mul]; exact hvπ
  have hpI : (p : Algebra.adjoin O (T : Set Ω)) ∈ I := by
    rw [memI]
    simpa using hpπ
  haveI hmaxI := hmax
  letI hk : Field (O ⧸ Ideal.span {(p : O)}) := Ideal.Quotient.field _
  haveI : CharP (O ⧸ Ideal.span {(p : O)}) p :=
    CharP.quotient O p (fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.2 hu))
  let φ : (O ⧸ Ideal.span {(p : O)}) →+* Algebra.adjoin O (T : Set Ω) ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (algebraMap O _)) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
      exact I.mul_mem_left _ hpI)
  letI : Algebra (O ⧸ Ideal.span {(p : O)}) (Algebra.adjoin O (T : Set Ω) ⧸ I) := φ.toAlgebra
  haveI hnt : Nontrivial (Algebra.adjoin O (T : Set Ω) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro h
    have h1 : (1 : Algebra.adjoin O (T : Set Ω)) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hvI 1 h1
    simp at this)
  haveI : IsLocalRing (Algebra.adjoin O (T : Set Ω) ⧸ I) := by
    refine { toNontrivial := hnt, isUnit_or_isUnit_of_add_one := ?_ }
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hxy : x + y - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hab, map_one, sub_self]
    have hv1 := hvI _ hxy
    have key : v x = 1 ∨ v y = 1 := by
      by_contra hcon
      push_neg at hcon
      have hx' : v x < 1 := lt_of_le_of_ne (hint _ x.2) hcon.1
      have hy' : v y < 1 := lt_of_le_of_ne (hint _ y.2) hcon.2
      have e1 : (1 : Ω) = ((x : Ω) + y) - ((x + y - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
        push_cast
        ring
      have : v (1 : Ω) < 1 := by
        rw [e1]
        exact lt_of_le_of_lt (v.map_sub _ _)
          (max_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt hx' hy')) hv1)
      simp at this
    rcases key with h | h
    · obtain ⟨w, hw, hxw⟩ := hunit _ x.2 h
      left
      have e : x * ⟨w, hw⟩ = 1 := Subtype.ext hxw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
    · obtain ⟨w, hw, hyw⟩ := hunit _ y.2 h
      right
      have e : y * ⟨w, hw⟩ = 1 := Subtype.ext hyw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
  let T' : Finset (Algebra.adjoin O (T : Set Ω) ⧸ I) :=
    T.attach.image (fun t => Ideal.Quotient.mk I ⟨t.1, Algebra.subset_adjoin (Finset.mem_coe.2 t.2)⟩)
  have hgen0 : ∀ x (hx : x ∈ Algebra.adjoin O (T : Set Ω)),
      Ideal.Quotient.mk I ⟨x, hx⟩ ∈ Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
        (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem t ht =>
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
    | algebraMap r =>
      convert Subalgebra.algebraMap_mem
        (Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)))
        (Ideal.Quotient.mk (Ideal.span {(p : O)}) r) using 1
      rfl
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul]
      exact mul_mem ihx ihy
  have hgen : Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
      (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hgen0 x hx
  have hfrob : ∀ t ∈ T', t ^ p ^ f = t := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨⟨t0, ht0⟩, -, rfl⟩ := ht
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]
    simpa using hstep t0 ht0
  obtain ⟨hfield, hroot⟩ := GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed p (O ⧸ Ideal.span {(p : O)})
    (Algebra.adjoin O (T : Set Ω) ⧸ I) T' f hf hgen hfrob
  have hzero : ∀ z : Algebra.adjoin O (T : Set Ω), v z < 1 → z ∈ I := by
    intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : z * w - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h2 := hvI _ h1
    have h3 : v ((z : Ω) * w) < 1 := by
      rw [map_mul]
      calc v z * v w ≤ v z * 1 := mul_le_mul_of_nonneg_left (hint _ w.2) zero_le
        _ < 1 := by rw [mul_one]; exact hz
    have e1 : (1 : Ω) = (z : Ω) * w - ((z * w - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
      push_cast
      ring
    have : v (1 : Ω) < 1 := by
      rw [e1]
      exact lt_of_le_of_lt (v.map_sub _ _) (max_lt h3 h2)
    simp at this
  refine ⟨fun x hx hvx => (memI ⟨x, hx⟩).1 (hzero _ hvx), ?_⟩
  intro y hy a hva
  have hI : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) ^ p - algebraMap O _ a ∈ I :=
    hzero _ (by simpa using hva)
  have heq : (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p =
      algebraMap (O ⧸ Ideal.span {(p : O)}) _ (Ideal.Quotient.mk _ a) := by
    have h0 := (Ideal.Quotient.eq_zero_iff_mem).2 hI
    rw [map_sub, map_pow] at h0
    exact sub_eq_zero.1 h0
  obtain ⟨b', hb'⟩ := hroot _ _ heq
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_⟩
  have h5 : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) - algebraMap O _ b ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb', sub_eq_zero]
    rfl
  simpa using hvI _ h5

/- English proof (translation)
Introduce `h`. Take `⟨e, he⟩` from `exists_completedLaurent_quot_prime_equiv_laurentFp p`. Establish `h1` using `(Ideal.Quotient.eq_zero_iff_dvd _ _).mpr h`. Rewrite `h1` using `[map_sub, map_pow, sub_eq_zero]`. Establish `h2` using `congrArg e h1`.

Rewrite `h2` using `[map_pow, he]`. Establish `h3` using `congrArg HahnSeries.order h2`. Rewrite `h3` using `[HahnSeries.order_pow, HahnSeries.order_single one_ne_zero, nsmul_eq_mul]`. Establish `h4 : (p : ℤ) ∣ 1` using `Dvd.intro _ h3`. Conclude with `hp.out.not_dvd_one (by exact_mod_cast h4)`.
-/
theorem q_not_pow_mod (p : ℕ) [hp : Fact p.Prime] (a : O0 p) : ¬ (p : O0 p) ∣ a ^ p - qO p := by
  intro h
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have h1 := (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr h
  rw [map_sub, map_pow, sub_eq_zero] at h1
  have h2 := congrArg e h1
  rw [map_pow, he] at h2
  have h3 := congrArg HahnSeries.order h2
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero, nsmul_eq_mul] at h3
  have h4 : (p : ℤ) ∣ 1 := Dvd.intro _ h3
  exact hp.out.not_dvd_one (by exact_mod_cast h4)

/- English proof (translation)
Introduce `p _ Ω _ _ hclo S hS y hy hyint`. Introduce and unpack `⟨m, hm, hmint⟩`. Take `⟨v, hv, -, hvp0, hvp1⟩` from `exists_valuation_isInt p Ω hclo`. Use `haveI := Basic.charZero_of_isClo hclo`. Take `⟨hdom, hdvr, hirr⟩` from `completed_laurent_isDVR p`.

Establish `huni` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr`. Establish `hmax : (Ideal.span {(p : O0 p)}).IsMaximal`. Rewrite using `[← huni]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal _`. Use `letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra`.

Use `haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hinj : Function.Injective (algebraMap ℤ_[p] Ω)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`.

Establish `e` using `PadicInt.unitCoeff_spec hx0`. Rewrite `hx` using `[e, map_mul, map_pow, map_natCast]`. Break down `mul_eq_zero.1 hx with h | h` into its components or cases. Conclude with `((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h`.

Establish `hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1` using `fun x hx => (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)`. Establish `hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s`. Introduce `s hs`. Take `⟨P, hP0, hP⟩` from `hS s hs`. Conclude with `⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩`.

Take `⟨R, hRfin, hRpid, hRS⟩` from `GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg`. Take `⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩` from `GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid`. Establish `hfg : (Subalgebra.toSubmodule R).FG` using `Module.Finite.iff_fg.1 hRfin`. Take `⟨T, hT⟩` from `Subalgebra.fg_of_fg_toSubmodule hfg`. Establish `hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω)`.

Introduce `x hx`. Establish `hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤ (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p]` using `Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))`. Rewrite `hle` using `[hT]`. Conclude with `(Subalgebra.mem_restrictScalars _).1 (hle hx)`. Establish `hTR : ∀ t ∈ T, t ∈ R` using `fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)`.

Establish `hTint : ∀ t ∈ T, IsIntegral (O0 p) t` using `fun t ht => (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top`. Take `⟨hdiv, hres⟩` from `residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))`. Establish `hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1` using `fun x hx => (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)`. Establish `hclosed` using `GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv`. Establish `hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤ Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω)`.

Rewrite using `[Subfield.closure_le]`. Introduce and unpack `x (⟨c, rfl⟩ | hx)`. Conclude with `Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)`. Take `⟨a, ha, b, hb, rfl⟩` from `hRS x hx`. Conclude with `div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))`.

Take `⟨a, ha, b, hb, hab⟩` from `Subfield.mem_closure_iff.1 (hsub hy)`. Establish `hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω), z ∈ Algebra.adjoin (O0 p) (T : Set Ω)` using `fun z hz => (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz`. Establish `hyv : v y ≤ 1` using `(hv y).2 hyint`. Establish `hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω)`. Rewrite using `[← hab]`.

Conclude with `hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)`. Establish `hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1`. Establish `h1` using `(hv _).2 hmint`. Rewrite `h1` using `[map_div₀, map_pow]`. Establish `h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1` using `lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `absurd h2 (not_lt.2 (one_le_pow₀ hc))`. Take `⟨b, hb⟩` from `hres y hyB (qO p) hvq`. Establish `hbv : v (algebraMap (O0 p) Ω b) ≤ 1` using `(hv _).2 isIntegral_algebraMap`.

Establish `hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1`. Establish `e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) - (y ^ p - (algebraMap (O0 p) Ω b) ^ p)`. Rewrite using `[map_sub, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1`.

Rewrite using `[← geom_sum₂_mul, map_mul]`. Establish `hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1`. Apply `v.map_sum_le` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul, map_pow, map_pow]`.

Conclude with `mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)`. Apply `q_not_pow_mod p b` to reduce the goal to its premises.

Assume the negation of the conclusion as `hnd`. Establish `hu : IsUnit (b ^ p - qO p)`. Assume the negation of the conclusion as `hnu`. Apply `hnd` to reduce the goal to its premises. Establish `hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p)` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`.

Rewrite `hmem` using `[huni]`. Conclude with `Ideal.mem_span_singleton.1 hmem`. Take `⟨u, hu⟩` from `hu`. Establish `h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`.

Establish `h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1` using `(hv _).2 isIntegral_algebraMap`. Rewrite `hvb` using `[← hu]`. Establish `h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h4` using `[h1]`.

Conclude with `lt_irrefl _ h4`.
-/
theorem not_pow_mod_max : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  intro p _ Ω _ _ hclo S hS y hy hyint
  rintro ⟨m, hm, hmint⟩
  classical
  obtain ⟨v, hv, -, hvp0, hvp1⟩ := exists_valuation_isInt p Ω hclo
  haveI := Basic.charZero_of_isClo hclo
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have huni := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
    rw [← huni]
    exact IsLocalRing.maximalIdeal.isMaximal _
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have e := PadicInt.unitCoeff_spec hx0
    rw [e, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
  have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
    (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s := by
    intro s hs
    obtain ⟨P, hP0, hP⟩ := hS s hs
    exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
  obtain ⟨R, hRfin, hRpid, hRS⟩ := GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg
  obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
    GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
  have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
  obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
  have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    intro x hx
    have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
        (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
      Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
    rw [hT] at hle
    exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
  have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
    (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
  obtain ⟨hdiv, hres⟩ := residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
    (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
  have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
  have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
  have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤
      Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
      exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
  have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
      z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
    (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
  have hyv : v y ≤ 1 := (hv y).2 hyint
  have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    rw [← hab]
    exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
  have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
    have h1 := (hv _).2 hmint
    rw [map_div₀, map_pow] at h1
    have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
      lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
  have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
  have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
    have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
        (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
      rw [map_sub, map_pow]
      ring
    have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
        apply v.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
      calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
        _ < 1 := by rw [one_mul]; exact hb
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
  apply q_not_pow_mod p b
  by_contra hnd
  have hu : IsUnit (b ^ p - qO p) := by
    by_contra hnu
    apply hnd
    have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [huni] at hmem
    exact Ideal.mem_span_singleton.1 hmem
  obtain ⟨u, hu⟩ := hu
  have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
  rw [← hu] at hvb
  have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
    calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
      _ < 1 := by rw [mul_one]; exact hvb
  rw [h1] at h4
  exact lt_irrefl _ h4

end GlobalTheory.K5.NotPow
