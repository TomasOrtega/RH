import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel

namespace GlobalTheory.NormBall

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Simplify using `only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, zero_pow two_ne_zero, zero_add]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]`. Conclude with `ht.ne`.
-/
private lemma eval_zero_quadratic_mem_maximalIdeal (t : F) (ht : valuation F t < 1) (htmem : t ∈ 𝒪[F]) :
    Polynomial.eval 0 (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    zero_pow two_ne_zero, zero_add]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact ht.ne

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace F`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := F)`. Establish `hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F])` using `IsAdicComplete.henselianRing _ _`. Establish `htmem : t ∈ 𝒪[F]` using `(Valuation.mem_integer_iff _ _).2 ht.le`. Establish `hf : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F]).Monic` using `by monicity!`.

Establish `h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F])) (Polynomial.eval 0 (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F]))))`. Simplify using `[Polynomial.derivative_X_pow]`. Take `⟨w, hw, -⟩` from `hH.is_henselian _ hf 0 (eval_zero_quadratic_mem_maximalIdeal t ht htmem) h1`. Use `⟨(w : F), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun x : 𝒪[F] => (x : F)) hw.eq_zero`.

Simplify using `at h`. Take the linear combination `4 * h`.
-/
private lemma exists_sq_eq_one_sub_four_mul {t : F} (ht : valuation F t < 1) :
    ∃ w : F, (1 + 2 * w) ^ 2 = 1 - 4 * t := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) :=
    IsAdicComplete.henselianRing _ _
  have htmem : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hf : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]).Monic := by
    monicity!
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F]))
      (Polynomial.eval 0 (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F])))) := by
    simp [Polynomial.derivative_X_pow]
  obtain ⟨w, hw, -⟩ := hH.is_henselian _ hf 0 (eval_zero_quadratic_mem_maximalIdeal t ht htmem) h1
  refine ⟨(w : F), ?_⟩
  have h := congrArg (fun x : 𝒪[F] => (x : F)) hw.eq_zero
  simp at h
  linear_combination 4 * h

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Rewrite using `[← one_add_one_eq_two]`. Conclude with `(valuation F).map_add_le (by simp) (by simp)`.
-/
private lemma valuation_two_le_one : valuation F (2 : F) ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact (valuation F).map_add_le (by simp) (by simp)

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
Break down `eq_or_ne (2 * a) 0 with h2a | h2a` into its components or cases. Simplify using `[h2a]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `set e := a ^ 2 - d * b ^ 2 with he`.

Establish `ha : a ≠ 0` using `right_ne_zero_of_mul h2a`. Establish `h2 : (2 : F) ≠ 0` using `left_ne_zero_of_mul h2a`. Establish `het : e = e / (2 * a) ^ 2 * (2 * a) ^ 2` using `by field_simp`. Establish `ht : valuation F (e / (2 * a) ^ 2) < 1`. Assume the negation of the conclusion as `hge`.

Use `push_neg at hge`. Establish `hv : valuation F e = valuation F (e / (2 * a) ^ 2) * valuation F (2 * a) ^ 2`. Rewrite using `[← map_pow, ← map_mul, ← het]`. Establish `: valuation F (2 * a) ^ 2 ≤ valuation F e`. Rewrite using `[hv]`.

Conclude with `le_mul_of_one_le_left' hge`. Conclude with `(not_le.2 hlt) this`. Take `⟨w, hw⟩` from `exists_sq_eq_one_sub_four_mul ht`. Break down `eq_or_ne b 0 with hb | hb` into its components or cases. Establish `hea : e = a ^ 2` using `by simp [he, hb]`.

Establish `: valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2)`. Rewrite using `[map_mul, map_pow, mul_pow]`. Conclude with `mul_le_of_le_one_left' (pow_le_one₀ zero_le valuation_two_le_one)`. Rewrite `hlt` using `[hea]`. Conclude with `(not_le.2 hlt) this`.

Apply `hd (a / b * (1 + 2 * w))` to reduce the goal to its premises. Rewrite using `[mul_pow, hw]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.NormBall.val_trace_sq_le {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (a b : F) :
    valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2 - d * b ^ 2) := by
  rcases eq_or_ne (2 * a) 0 with h2a | h2a
  · simp [h2a]
  by_contra hlt
  push_neg at hlt
  set e := a ^ 2 - d * b ^ 2 with he
  have ha : a ≠ 0 := right_ne_zero_of_mul h2a
  have h2 : (2 : F) ≠ 0 := left_ne_zero_of_mul h2a
  have het : e = e / (2 * a) ^ 2 * (2 * a) ^ 2 := by field_simp
  have ht : valuation F (e / (2 * a) ^ 2) < 1 := by
    by_contra hge
    push_neg at hge
    have hv : valuation F e = valuation F (e / (2 * a) ^ 2) * valuation F (2 * a) ^ 2 := by
      rw [← map_pow, ← map_mul, ← het]
    have : valuation F (2 * a) ^ 2 ≤ valuation F e := by
      rw [hv]
      exact le_mul_of_one_le_left' hge
    exact (not_le.2 hlt) this
  obtain ⟨w, hw⟩ := exists_sq_eq_one_sub_four_mul ht
  rcases eq_or_ne b 0 with hb | hb
  · have hea : e = a ^ 2 := by simp [he, hb]
    have : valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2) := by
      rw [map_mul, map_pow, mul_pow]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le valuation_two_le_one)
    rw [hea] at hlt
    exact (not_le.2 hlt) this
  apply hd (a / b * (1 + 2 * w))
  rw [mul_pow, hw]
  field_simp
  rw [he]
  ring

def ballSub {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (s : Fˣ) : AddSubgroup (F × F) where
  carrier := {p | p.1 ^ 2 - d * p.2 ^ 2 ∈ GlobalTheory.SplitWeil.cball s}
  zero_mem' := by simp [GlobalTheory.SplitWeil.cball]
  neg_mem' := by
    intro p hp
    simpa using hp
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h h'
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at h h' ⊢
    have e : (a + a') ^ 2 - d * (b + b') ^ 2 =
        (a ^ 2 - d * b ^ 2) + (a' ^ 2 - d * b' ^ 2) + 2 * (a * a' - d * b * b') := by ring
    have k := val_trace_sq_le hd (a * a' - d * b * b') (a * b' - b * a')
    have e2 : (a * a' - d * b * b') ^ 2 - d * (a * b' - b * a') ^ 2 =
        (a ^ 2 - d * b ^ 2) * (a' ^ 2 - d * b' ^ 2) := by ring
    rw [e2, map_mul (valuation F) (a ^ 2 - d * b ^ 2)] at k
    have k2 : valuation F (2 * (a * a' - d * b * b')) ≤ valuation F (s : F) := by
      refine le_of_pow_le_pow_left₀ two_ne_zero zero_le (k.trans ?_)
      rw [sq (valuation F (s : F))]
      exact mul_le_mul' h h'
    rw [e]
    exact (valuation F).map_add_le ((valuation F).map_add_le h h') k2

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.SplitWeil.cball, Set.mem_union, Set.mem_setOf_eq, Units.val_one, map_one]`. Distinguish the cases in `hy : valuation F y ≤ 1`. Conclude with `Or.inl hy`. Use `right push_neg at hy`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma mem_union_of_valuation_sq_le (u : Fˣ) {y : F} (h : valuation F y ^ 2 ≤ valuation F (u : F)) :
    y ∈ _root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball u := by
  simp only [_root_.GlobalTheory.SplitWeil.cball, Set.mem_union, Set.mem_setOf_eq, Units.val_one, map_one]
  by_cases hy : valuation F y ≤ 1
  · exact Or.inl hy
  · right
    push_neg at hy
    calc valuation F y = valuation F y * 1 := (mul_one _).symm
      _ ≤ valuation F y * valuation F y := by gcongr
      _ = valuation F y ^ 2 := (sq _).symm
      _ ≤ _ := h

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Use `haveI := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := F)).2`. Establish `hq : Continuous fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2` using `by fun_prop`. Establish `hset : ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) = (fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2) ⁻¹' _root_.GlobalTheory.SplitWeil.cball s` using `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `set D : Fˣ := Units.mk0 d hd0 set K₁ := (fun y : F => (2 : F)⁻¹ * y) '' (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball s) set K₂ := (fun y : F => (2 * d)⁻¹ * y) '' (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.c …`.

Establish `hK₁ : IsCompact K₁` using `((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image (continuous_const.mul continuous_id)`. Establish `hK₂ : IsCompact K₂` using `((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image (continuous_const.mul continuous_id)`. Establish `hclosed : IsClosed ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F))`. Rewrite using `[hset]`. Conclude with `(_root_.GlobalTheory.SplitWeil.isCompact_cball s).isClosed.preimage hq`.

Use `(hK₁.prod hK₂).of_isClosed_subset hclosed ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ hp`. Establish `hp' : valuation F (a ^ 2 - d * b ^ 2) ≤ valuation F (s : F)` using `hp`. Use `⟨⟨2 * a, mem_union_of_valuation_sq_le s ?_, by field_simp⟩, ⟨2 * (d * b), mem_union_of_valuation_sq_le (D * s) ?_, by field_simp⟩⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`.

Conclude with `(by simpa [map_pow] using _root_.GlobalTheory.NormBall.val_trace_sq_le hd a b : valuation F ((2 * a) ^ 2) ≤ _).trans hp'`. Establish `k` using `_root_.GlobalTheory.NormBall.val_trace_sq_le hd (d * b) a`. Establish `e : (d * b) ^ 2 - d * a ^ 2 = -d * (a ^ 2 - d * b ^ 2)` using `by ring`. Rewrite `k` using `[e, map_mul (valuation F) (-d), Valuation.map_neg]`. Use `k.trans ?_` and prove the remaining obligations.

Simplify using `only [D, Units.val_mul, Units.val_mk0, map_mul]`. Use `gcongr`. Rewrite using `[hset]`. Conclude with `(_root_.GlobalTheory.SplitWeil.isOpen_cball s).preimage hq`.
-/
private lemma isCompact_isOpen_normFormBall {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (hd0 : d ≠ 0)
    (h2 : (2 : F) ≠ 0) (s : Fˣ) :
    IsCompact ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) ∧
      IsOpen ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
  haveI := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := F)).2
  have hq : Continuous fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2 := by fun_prop
  have hset : ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) =
      (fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2) ⁻¹' _root_.GlobalTheory.SplitWeil.cball s := rfl
  refine ⟨?_, ?_⟩
  · set D : Fˣ := Units.mk0 d hd0
    set K₁ := (fun y : F => (2 : F)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball s)
    set K₂ := (fun y : F => (2 * d)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball (D * s))
    have hK₁ : IsCompact K₁ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hK₂ : IsCompact K₂ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hclosed : IsClosed ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      rw [hset]
      exact (_root_.GlobalTheory.SplitWeil.isCompact_cball s).isClosed.preimage hq
    refine (hK₁.prod hK₂).of_isClosed_subset hclosed ?_
    rintro ⟨a, b⟩ hp
    have hp' : valuation F (a ^ 2 - d * b ^ 2) ≤ valuation F (s : F) := hp
    refine ⟨⟨2 * a, mem_union_of_valuation_sq_le s ?_, by field_simp⟩,
      ⟨2 * (d * b), mem_union_of_valuation_sq_le (D * s) ?_, by field_simp⟩⟩
    · rw [← map_pow]
      exact (by simpa [map_pow] using _root_.GlobalTheory.NormBall.val_trace_sq_le hd a b : valuation F ((2 * a) ^ 2) ≤ _).trans hp'
    · have k := _root_.GlobalTheory.NormBall.val_trace_sq_le hd (d * b) a
      have e : (d * b) ^ 2 - d * a ^ 2 = -d * (a ^ 2 - d * b ^ 2) := by ring
      rw [e, map_mul (valuation F) (-d), Valuation.map_neg] at k
      refine k.trans ?_
      simp only [D, Units.val_mul, Units.val_mk0, map_mul]
      gcongr
  · rw [hset]
    exact (_root_.GlobalTheory.SplitWeil.isOpen_cball s).preimage hq

open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ _ c δ hE s`. Use `haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero`. Establish `hneg : c δ = -δ` using `hE.anti`. Establish `hfix : c (δ ^ 2) = δ ^ 2` using `by rw [map_pow, hneg, neg_sq]`. Take `⟨d, hdδ⟩` from `hE.exists_of_fixed hfix`.

Establish `hinj` using `hE.algebraMap_injective`. Establish `h2E : (2 : E) ≠ 0`. Introduce `h`. Apply `two_ne_zero (α := F)` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_ofNat, map_zero]`. Conclude with `h`. Establish `hd : ∀ r : F, r ^ 2 ≠ d`. Introduce `r hr`. Establish `hc : c (algebraMap F E r) = algebraMap F E r` using `c.commutes r`.

Establish `hsq : (δ - algebraMap F E r) * (δ + algebraMap F E r) = 0`. Rewrite `hdδ` using `[← hr, map_pow]`. Take the linear combination `hdδ`. Establish `hδ0 : δ = 0`. Break down `mul_eq_zero.1 hsq with h | h` into its components or cases.

Establish `h' : δ = algebraMap F E r` using `sub_eq_zero.1 h`. Establish `hr'` using `hneg`. Rewrite `hr'` using `[h', hc]`. Establish `: (2 : E) * algebraMap F E r = 0` using `by linear_combination hr'`. Rewrite using `[h']`.

Conclude with `(mul_eq_zero.1 this).resolve_left h2E`. Establish `h' : δ = -algebraMap F E r` using `eq_neg_of_add_eq_zero_left h`. Establish `hr'` using `hneg`. Rewrite `hr'` using `[h', map_neg, hc]`. Establish `: (2 : E) * algebraMap F E r = 0` using `by linear_combination -hr'`.

Rewrite using `[h', (mul_eq_zero.1 this).resolve_left h2E, neg_zero]`. Conclude with `hE.unit.ne_zero hδ0`. Establish `hd0 : d ≠ 0` using `fun h => hd 0 (by simp [h])`. Establish `hnorm : ∀ a b : F, Algebra.norm F (a • (1 : E) + b • δ) = a ^ 2 - d * b ^ 2`. Introduce `a b`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hE.algebraMap_norm]`. Simplify using `only [Algebra.smul_def, mul_one, map_add, map_mul, AlgHom.commutes, hneg, map_sub, map_pow]`. Take the linear combination `(-(algebraMap F E b) ^ 2) * hdδ`. Take `⟨bs, hb0, hb1⟩` from `hE.basis`.

Set `ψ : E →ₗ[F] F × F` to `(LinearMap.proj 0 ∘ₗ bs.equivFun.toLinearMap).prod (LinearMap.proj 1 ∘ₗ bs.equivFun.toLinearMap)`. Establish `hψ : Continuous ψ` using `IsModuleTopology.continuous_of_linearMap ψ`. Establish `hφψ : ∀ z : E, (ψ z).1 • (1 : E) + (ψ z).2 • δ = z`. Introduce `z`. Establish `h` using `bs.sum_equivFun z`.

Rewrite `h` using `[Fin.sum_univ_two, hb0, hb1]`. Conclude with `h`. Use `haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E`. Use `haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E`. Establish `hφ : Continuous fun p : F × F => p.1 • (1 : E) + p.2 • δ` using `(continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)`.

Take `⟨hK, hU⟩` from `isCompact_isOpen_normFormBall hd hd0 two_ne_zero s`. Use `⟨(_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Express the relevant statement in the definitionally equal form `(ψ z).1 ^ 2 - d * (ψ z).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s ↔ _`. Rewrite using `[← hnorm, hφψ]`.

Both sides reduce to the same expression. Establish `himg : (((_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ : AddSubgroup E) : Set E) = (fun p : F × F => p.1 • (1 : E) + p.2 • δ) '' ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Conclude with `⟨ψ z, hz, hφψ z⟩`. Introduce and unpack `⟨p, hp, rfl⟩`. Express the relevant statement in the definitionally equal form `(ψ _).1 ^ 2 - d * (ψ _).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s`. Rewrite using `[← hnorm, hφψ, hnorm]`. Conclude with `hp`.

Rewrite using `[himg]`. Conclude with `hK.image hφ`. Conclude with `hU.preimage hψ`.
-/
theorem _root_.GlobalTheory.NormBall.exists_normBall : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ _root_.GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hneg : c δ = -δ := hE.anti
  have hfix : c (δ ^ 2) = δ ^ 2 := by rw [map_pow, hneg, neg_sq]
  obtain ⟨d, hdδ⟩ := hE.exists_of_fixed hfix
  have hinj := hE.algebraMap_injective
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply two_ne_zero (α := F)
    apply hinj
    rw [map_ofNat, map_zero]
    exact h
  have hd : ∀ r : F, r ^ 2 ≠ d := by
    intro r hr
    have hc : c (algebraMap F E r) = algebraMap F E r := c.commutes r
    have hsq : (δ - algebraMap F E r) * (δ + algebraMap F E r) = 0 := by
      rw [← hr, map_pow] at hdδ
      linear_combination hdδ
    have hδ0 : δ = 0 := by
      rcases mul_eq_zero.1 hsq with h | h
      · have h' : δ = algebraMap F E r := sub_eq_zero.1 h
        have hr' := hneg
        rw [h', hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination hr'
        rw [h']
        exact (mul_eq_zero.1 this).resolve_left h2E
      · have h' : δ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h
        have hr' := hneg
        rw [h', map_neg, hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination -hr'
        rw [h', (mul_eq_zero.1 this).resolve_left h2E, neg_zero]
    exact hE.unit.ne_zero hδ0
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  have hnorm : ∀ a b : F, Algebra.norm F (a • (1 : E) + b • δ) = a ^ 2 - d * b ^ 2 := by
    intro a b
    apply hinj
    rw [hE.algebraMap_norm]
    simp only [Algebra.smul_def, mul_one, map_add, map_mul, AlgHom.commutes, hneg, map_sub,
      map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hdδ
  obtain ⟨bs, hb0, hb1⟩ := hE.basis
  let ψ : E →ₗ[F] F × F :=
    (LinearMap.proj 0 ∘ₗ bs.equivFun.toLinearMap).prod (LinearMap.proj 1 ∘ₗ bs.equivFun.toLinearMap)
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have hφψ : ∀ z : E, (ψ z).1 • (1 : E) + (ψ z).2 • δ = z := by
    intro z
    have h := bs.sum_equivFun z
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have hφ : Continuous fun p : F × F => p.1 • (1 : E) + p.2 • δ :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  obtain ⟨hK, hU⟩ := isCompact_isOpen_normFormBall hd hd0 two_ne_zero s
  refine ⟨(_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ, ?_, ?_, ?_⟩
  · ext z
    change (ψ z).1 ^ 2 - d * (ψ z).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s ↔ _
    rw [← hnorm, hφψ]
    rfl
  · have himg : (((_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ : AddSubgroup E) : Set E) =
        (fun p : F × F => p.1 • (1 : E) + p.2 • δ) ''
          ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      ext z
      constructor
      · intro hz
        exact ⟨ψ z, hz, hφψ z⟩
      · rintro ⟨p, hp, rfl⟩
        change (ψ _).1 ^ 2 - d * (ψ _).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s
        rw [← hnorm, hφψ, hnorm]
        exact hp
    rw [himg]
    exact hK.image hφ
  · exact hU.preimage hψ

end GlobalTheory.NormBall
