import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace CutRegular

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

omit [DecidableEq K] in

/- English proof (translation)
Unfold `mixedDiff`. Rewrite using `[List.ofFn_succ', List.concat_eq_append, List.foldr_concat]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`.
-/
theorem mixedDiff_snoc {n : ℕ} (bs : Fin n → K → ℤ) (c : K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc (α := fun _ => K → ℤ) bs c) h = mixedDiff bs (diffStep c h) := by
  unfold mixedDiff
  rw [List.ofFn_succ', List.concat_eq_append, List.foldr_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

omit [DecidableEq K] in

/- English proof (translation)
The claim follows from `| [] => hh | b :: l => by have ih := foldr_diffStep_eventually_zero hh l filter_upwards [ih, (tendsto_sub_const_atTop b).eventually ih] with m h1 h2 simp only [List.foldr_cons, diffStep, h1, h2, sub_self]`.
-/
theorem foldr_diffStep_eventually_zero {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) :
    ∀ l : List (K → ℤ), ∀ᶠ m in Filter.atTop, l.foldr diffStep h m = 0
  | [] => hh
  | b :: l => by
    have ih := foldr_diffStep_eventually_zero hh l
    filter_upwards [ih, (tendsto_sub_const_atTop b).eventually ih] with m h1 h2
    simp only [List.foldr_cons, diffStep, h1, h2, sub_self]

omit [DecidableEq K] in

/- English proof (translation)
Unfold `eventualValue`. Use `split_ifs with h`. Take `⟨m, h1, h2⟩` from `(h.choose_spec.and hf).exists`. Rewrite using `[← h1, h2]`. Both sides reduce to the same expression.
-/
theorem eventualValue_eq_zero {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in Filter.atTop, f m = 0) :
    eventualValue f = 0 := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, h1, h2⟩ := (h.choose_spec.and hf).exists
    rw [← h1, h2]
  · rfl

/- English proof (translation)
The claim follows from `eventualValue_eq_zero (foldr_diffStep_eventually_zero hI (List.ofFn bs))`.
-/
theorem intNum_eq_zero_of_eventually {I : Ideal (MRing ι F)}
    (hI : ∀ᶠ m in Filter.atTop, hilbFn I m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F I bs = 0 :=
  eventualValue_eq_zero (foldr_diffStep_eventually_zero hI (List.ofFn bs))

/- English proof (translation)
Unfold `hilbFn`. Use `split_ifs`. Establish `: gradedPiece (⊤ : Ideal (MRing ι F)) (fun k => (m k).toNat) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x _`.

Rewrite using `[Submodule.mem_bot]`. Establish `: Subsingleton (MRing ι F ⧸ (⊤ : Ideal (MRing ι F)))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Conclude with `Subsingleton.elim _ _`. Rewrite using `[this, finrank_bot, Nat.cast_zero]`. Both sides reduce to the same expression.
-/
theorem hilbFn_top (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by
  unfold hilbFn
  split_ifs
  · have : gradedPiece (⊤ : Ideal (MRing ι F)) (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [Submodule.mem_bot]
      have : Subsingleton (MRing ι F ⧸ (⊤ : Ideal (MRing ι F))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Subsingleton.elim _ _
    rw [this, finrank_bot, Nat.cast_zero]
  · rfl

/- English proof (translation)
Establish `hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ I`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨⟨k', i⟩, hv, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at hv`. Substitute `hv` using the available equality.

Conclude with `hk i`. Apply `hspan` to reduce the goal to its premises. Rewrite using `[mem_ideal_span_X_image]`. Introduce `d hd`. Assume the negation of the conclusion as `hno`.

Use `push Not at hno`. Establish `hw : Finsupp.weight (blockWeight ι) d = m` using `hf (mem_support_iff.mp hd)`. Establish `h0 : Finsupp.weight (blockWeight ι) d k = 0`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun v _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v.1 = k`. Simplify using `[hno v hv]`. Simplify using `[blockWeight, Pi.single_apply, Ne.symm hv]`. Rewrite `h0` using `[hw]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_of_block_le {I : Ideal (MRing ι F)} {k : K}
    (hk : ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I) {m : K → ℕ} (hm : 1 ≤ m k)
    {f : MRing ι F} (hf : IsMultiHomog f m) : f ∈ I := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hk i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  by_contra hno
  push Not at hno
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (mem_support_iff.mp hd)
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 = k
    · simp [hno v hv]
    · simp [blockWeight, Pi.single_apply, Ne.symm hv]
  rw [hw] at h0
  omega

/- English proof (translation)
Unfold `IsRelevant at hI`. Use `push Not at hI`. Take `⟨k, hk⟩` from `hI`. Use `filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm`. Unfold `hilbFn`.

Use `split_ifs with h0`. Establish `: gradedPiece I (fun k => (m k).toNat) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Rewrite using `[Submodule.mem_bot]`.

Establish `hmk : (1 : ℤ) ≤ m k` using `hm k`. Establish `hfk : 1 ≤ (m k).toNat` using `by omega`. Establish `hfI` using `mem_of_block_le hk hfk ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)`. Simplify `hfI` using `[Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[this, finrank_bot, Nat.cast_zero]`.

Both sides reduce to the same expression.
-/
theorem hilbFn_eventually_zero_of_not_relevant {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I) :
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0 := by
  unfold IsRelevant at hI
  push Not at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
  unfold hilbFn
  split_ifs with h0
  · have : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot]
      have hmk : (1 : ℤ) ≤ m k := hm k
      have hfk : 1 ≤ (m k).toNat := by omega
      have hfI := mem_of_block_le hk hfk ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hfI
    rw [this, finrank_bot, Nat.cast_zero]
  · rfl

/- English proof (translation)
Introduce `f hf b`. Take `⟨a, ha, t', ht', rfl⟩` from `Submodule.mem_sup.mp hf`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp ht'`. Rewrite using `[map_add, HilbExactDivide.component_mul_form hs]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left (hP a ha b)) ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s))`. Conclude with `Ideal.zero_mem _`.
-/
theorem isMultiHomogIdeal_sup_span {P : Ideal (MRing ι F)} (hP : IsMultiHomogIdeal P)
    {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := by
  classical
  intro f hf b
  obtain ⟨a, ha, t', ht', rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ht'
  rw [map_add, HilbExactDivide.component_mul_form hs]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hP a ha b)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s))
  · exact Ideal.zero_mem _

omit [DecidableEq K] in

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[HilbExactDivide.mem_colon_span_iff]`. Conclude with `⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩`.
-/
theorem colon_eq_of_not_mem {P : Ideal (MRing ι F)} [hP : P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext g
  rw [HilbExactDivide.mem_colon_span_iff]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩

omit [DecidableEq K] in

/- English proof (translation)
Unfold `relDim`. Consider the cases of `hd : ringKrullDim (MRing ι F ⧸ I) using WithBot.recBotCoe with`. Consider the case `bot`. Rewrite using `[WithBot.map_bot]`. Conclude with `iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)`.

Consider the case `coe y`. Rewrite using `[WithBot.map_coe]`. Consider the cases of `y using ENat.recTopCoe with`. Consider the case `top`. Use `iff_of_false (fun h => ?_) (fun h => ?_)` and prove the remaining obligations.

Conclude with `WithTop.top_ne_coe (WithBot.coe_inj.mp h)`. Conclude with `ENat.top_ne_natCast _ (WithBot.coe_inj.mp h)`. Consider the case `coe e`. Establish `key : WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) = (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)` using `rfl`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ((e : ℤ) - Fintype.card K : ℤ) = d` using `WithTop.coe_inj.mp (WithBot.coe_inj.mp h)`. Establish `h2 : e = d + Fintype.card K` using `by omega`. Rewrite using `[h2]`.

Both sides reduce to the same expression. Introduce `h`. Establish `h1 : (e : ℕ∞) = ((d + Fintype.card K : ℕ) : ℕ∞)` using `WithBot.coe_inj.mp h`. Establish `h2 : e = d + Fintype.card K` using `by exact_mod_cast h1`. Substitute `h2` using the available equality.

Rewrite using `[show (((d + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = (d : ℤ) by push_cast; ring]`. Both sides reduce to the same expression.
-/
theorem relDim_eq_natCast_iff [Fintype K] (I : Ideal (MRing ι F)) (d : ℕ) :
    relDim I = ((d : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MRing ι F ⧸ I) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold relDim
  cases hd : ringKrullDim (MRing ι F ⧸ I) using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.map_bot]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe y =>
    rw [WithBot.map_coe]
    cases y using ENat.recTopCoe with
    | top =>
      refine iff_of_false (fun h => ?_) (fun h => ?_)
      · exact WithTop.top_ne_coe (WithBot.coe_inj.mp h)
      · exact ENat.top_ne_natCast _ (WithBot.coe_inj.mp h)
    | coe e =>
      have key : WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) =
          (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := rfl
      rw [key]
      constructor
      · intro h
        have h1 : ((e : ℤ) - Fintype.card K : ℤ) = d := WithTop.coe_inj.mp (WithBot.coe_inj.mp h)
        have h2 : e = d + Fintype.card K := by omega
        rw [h2]
        rfl
      · intro h
        have h1 : (e : ℕ∞) = ((d + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_inj.mp h
        have h2 : e = d + Fintype.card K := by exact_mod_cast h1
        subst h2
        rw [show (((d + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = (d : ℤ) by push_cast; ring]
        rfl

/- English proof (translation)
Consider the cases of `x using WithBot.recBotCoe with`. Consider the case `bot => simp at h2`. Consider the case `coe y`. Consider the cases of `y using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `h1`. Establish `h2'` using `WithBot.coe_le_coe.mp h1'`. Rewrite `h2'` using `[top_add, top_le_iff]`. Conclude with `ENat.natCast_ne_top _ h2'`.

Consider the case `coe y`. Establish `a1 : y + 1 ≤ e + 1` using `by exact_mod_cast h1`. Establish `a2 : e ≤ y` using `by exact_mod_cast h2`. Establish `: y = e` using `by omega`. Substitute `this` using the available equality.

Both sides reduce to the same expression.
-/
theorem eq_of_add_one_le_of_le {x : WithBot ℕ∞} {e : ℕ}
    (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) (h2 : ((e : ℕ) : WithBot ℕ∞) ≤ x) :
    x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => simp at h2
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      have h2' := WithBot.coe_le_coe.mp h1'
      rw [top_add, top_le_iff] at h2'
      exact ENat.natCast_ne_top _ h2'
    | coe y =>
      have a1 : y + 1 ≤ e + 1 := by exact_mod_cast h1
      have a2 : e ≤ y := by exact_mod_cast h2
      have : y = e := by omega
      subst this
      rfl

/- English proof (translation)
Consider the cases of `x using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Rewrite `hsum` using `[WithBot.add_bot]`. Conclude with `WithBot.bot_ne_natCast _ hsum`.

Consider the case `coe y`. Consider the cases of `y using ENat.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe y`. Consider the cases of `h using ENat.recTopCoe with`.

Consider the case `top => simp at hh`. Consider the case `coe h`. Establish `a1 : h + y = e + 1` using `by exact_mod_cast hsum`. Establish `a2 : h ≤ 1` using `by exact_mod_cast hh`. Establish `: e ≤ y` using `by omega`.

Conclude with `this` after adjusting the coercions.
-/
theorem le_of_height_add {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (hh : h ≤ 1)
    (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : ((e : ℕ) : WithBot ℕ∞) ≤ x := by
  cases x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hsum
    exact WithBot.bot_ne_natCast _ hsum
  | coe y =>
    cases y using ENat.recTopCoe with
    | top => simp
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have : e ≤ y := by omega
        exact_mod_cast this

omit [DecidableEq K] in

/- English proof (translation)
Establish `hne : (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P) ≠ ⊥`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk P s ∈ (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P)` using `Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`.

Rewrite `this` using `[h, Ideal.mem_bot]`. Then use the resulting hypothesis. Use `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne` as an intermediate fact. Rewrite `this` using `[ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE le_sup_left)]`. Then use the resulting hypothesis.
-/
theorem ringKrullDim_sup_span_add_one_le {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  have hne : (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    apply hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P s ∈ (P ⊔ Ideal.span {s}).map (Ideal.Quotient.mk P) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    rwa [h, Ideal.mem_bot] at this
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE le_sup_left)] at this

/- English proof (translation)
Establish `hWprime : W.IsPrime` using `hW.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hsW : s ∈ W` using `(le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)`. Establish `_ : Algebra.FiniteType F (MRing ι F ⧸ P)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)`. Use `set W' : Ideal (MRing ι F ⧸ P) := W.map (Ideal.Quotient.mk P)`.

Establish `_ : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `: Ideal.Quotient.mk P s ∈ W'` using `Ideal.mem_map_of_mem _ hsW`. Rewrite `this` using `[h, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hht : W'.height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `hquot : ringKrullDim ((MRing ι F ⧸ P) ⧸ W') = ringKrullDim (MRing ι F ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)`. Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'`.

Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`. Rewrite `hform`, `hdrop` using `[hquot, hdim]`. Conclude with `eq_of_add_one_le_of_le hdrop (le_of_height_add hht hform)`.
-/
theorem ringKrullDim_minimalPrime [Fintype K] [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι F)}
    [P.IsPrime] {s : MRing ι F} (hs : s ∉ P) (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes)
    {e : ℕ} (hdim : ringKrullDim (MRing ι F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType F (MRing ι F ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)
  set W' : Ideal (MRing ι F ⧸ P) := W.map (Ideal.Quotient.mk P)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim ((MRing ι F ⧸ P) ⧸ W') = ringKrullDim (MRing ι F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact eq_of_add_one_le_of_le hdrop (le_of_height_add hht hform)

end CutRegular

open CutRegular in

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP n hdim c s hs hsP bs`. Use `haveI := hP.isPrime`. Use `set I := P ⊔ Ideal.span {s} with hIdef`. Establish `hdiff : diffStep (fun k => (c k : ℤ)) (hilbFn P) = hilbFn I`. Use function extensionality and compare the values at `m`.

Use `h1 F K ι P hP.multiHomog c s hs m` as an intermediate fact. Rewrite `this` using `[colon_eq_of_not_mem hsP]`. Conclude with `this`. Establish `hLHS : intNum F P (Fin.snoc (α` using `fun _ => K → ℤ) bs (fun k => (c k : ℤ))) = intNum F I bs := by`. Unfold `intNum`.

Rewrite using `[mixedDiff_snoc, hdiff]`. Rewrite using `[hLHS]`. Establish `hP' : ringKrullDim (MRing ι F ⧸ P) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞)`. Rewrite using `[(relDim_eq_natCast_iff P (n + 1)).mp hdim, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega]`. Establish `hmin : ∀ W ∈ I.minimalPrimes, ringKrullDim (MRing ι F ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)` using `fun W hW => ringKrullDim_minimalPrime hsP hW hP'`.

Distinguish the cases in `hgood : IsRelevant I ∧ I ≠ ⊤`. Take `⟨hrel, hne⟩` from `hgood`. Establish `hIdim : relDim I = ((n : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[relDim_eq_natCast_iff]`. Take `⟨⟨W, hW⟩⟩` from `Ideal.nonempty_minimalPrimes hne`.

Establish `_ : W.IsPrime` using `hW.1.1`. Establish `hle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ I)` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.2) (Ideal.Quotient.factor_surjective hW.1.2)`. Rewrite `hle` using `[hmin W hW]`. Establish `hup` using `ringKrullDim_sup_span_add_one_le hsP`. Rewrite `hup` using `[hP']`.

Conclude with `eq_of_add_one_le_of_le hup hle`. Rewrite using `[h2 F K ι I (isMultiHomogIdeal_sup_span hP.multiHomog hs) hrel n hIdim bs]`. Use `congr 1`. Use function extensionality and compare the values at `W`. Unfold `topCycle divCycle`.

Distinguish the cases in `hW : W ∈ I.minimalPrimes ∧ IsRelevant W`. Establish `hWd : relDim W = ((n : ℕ) : WithBot (WithTop ℤ))` using `(relDim_eq_natCast_iff W n).mpr (hmin W hW.1)`. Rewrite using `[dif_pos ⟨hW.1, hW.2, hWd⟩, dif_pos hW]`. Rewrite using `[dif_neg (fun h => hW ⟨h.1, h.2.1⟩), dif_neg hW]`. Establish `hzero : ∀ᶠ m in Filter.atTop, hilbFn I m = 0`.

Distinguish the cases in `htop : I = ⊤`. Rewrite using `[htop]`. Conclude with `Filter.Eventually.of_forall hilbFn_top`. Conclude with `hilbFn_eventually_zero_of_not_relevant (fun h => hgood ⟨h, htop⟩)`. Rewrite using `[intNum_eq_zero_of_eventually hzero]`.

Establish `hdiv : divCycle P s = 0`. Use function extensionality and compare the values at `W`. Simplify using `only [Pi.zero_apply]`. Unfold `divCycle`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨hWm, hWr⟩`. Establish `hIW : I ≤ W` using `hWm.1.2`. Distinguish the cases in `htop : I = ⊤`. Conclude with `hWm.1.1.ne_top (top_le_iff.mp (htop ▸ hIW))`. Use `hgood ⟨fun k => ?_, htop⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hWr k`. Conclude with `⟨i, fun h => hi (hIW h)⟩`. Rewrite using `[hdiv]`. Simplify using `[cycEval]`.
-/
theorem CutRegular.proof (h1 : HilbExactDivide.Statement.{u}) (h2 : MultEqualsCoeff.Statement.{u})
    (_h3 : IntNumSymm.Statement.{u}) : CutRegular.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hdim c s hs hsP bs
  haveI := hP.isPrime
  set I := P ⊔ Ideal.span {s} with hIdef
  have hdiff : diffStep (fun k => (c k : ℤ)) (hilbFn P) = hilbFn I := by
    funext m
    have := h1 F K ι P hP.multiHomog c s hs m
    rw [colon_eq_of_not_mem hsP] at this
    exact this
  have hLHS : intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (c k : ℤ))) =
      intNum F I bs := by
    unfold intNum
    rw [mixedDiff_snoc, hdiff]
  rw [hLHS]
  have hP' : ringKrullDim (MRing ι F ⧸ P) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    rw [(relDim_eq_natCast_iff P (n + 1)).mp hdim, show n + 1 + Fintype.card K =
      n + Fintype.card K + 1 by omega]
  have hmin : ∀ W ∈ I.minimalPrimes,
      ringKrullDim (MRing ι F ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    fun W hW => ringKrullDim_minimalPrime hsP hW hP'
  by_cases hgood : IsRelevant I ∧ I ≠ ⊤
  · obtain ⟨hrel, hne⟩ := hgood
    have hIdim : relDim I = ((n : ℕ) : WithBot (WithTop ℤ)) := by
      rw [relDim_eq_natCast_iff]
      obtain ⟨⟨W, hW⟩⟩ := Ideal.nonempty_minimalPrimes hne
      have _ : W.IsPrime := hW.1.1
      have hle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.2)
          (Ideal.Quotient.factor_surjective hW.1.2)
      rw [hmin W hW] at hle
      have hup := ringKrullDim_sup_span_add_one_le hsP
      rw [hP'] at hup
      exact eq_of_add_one_le_of_le hup hle
    rw [h2 F K ι I (isMultiHomogIdeal_sup_span hP.multiHomog hs) hrel n hIdim bs]
    congr 1
    funext W
    unfold topCycle divCycle
    by_cases hW : W ∈ I.minimalPrimes ∧ IsRelevant W
    · have hWd : relDim W = ((n : ℕ) : WithBot (WithTop ℤ)) :=
        (relDim_eq_natCast_iff W n).mpr (hmin W hW.1)
      rw [dif_pos ⟨hW.1, hW.2, hWd⟩, dif_pos hW]
    · rw [dif_neg (fun h => hW ⟨h.1, h.2.1⟩), dif_neg hW]
  · have hzero : ∀ᶠ m in Filter.atTop, hilbFn I m = 0 := by
      by_cases htop : I = ⊤
      · rw [htop]
        exact Filter.Eventually.of_forall hilbFn_top
      · exact hilbFn_eventually_zero_of_not_relevant (fun h => hgood ⟨h, htop⟩)
    rw [intNum_eq_zero_of_eventually hzero]
    have hdiv : divCycle P s = 0 := by
      funext W
      simp only [Pi.zero_apply]
      unfold divCycle
      rw [dif_neg]
      rintro ⟨hWm, hWr⟩
      have hIW : I ≤ W := hWm.1.2
      by_cases htop : I = ⊤
      · exact hWm.1.1.ne_top (top_le_iff.mp (htop ▸ hIW))
      · refine hgood ⟨fun k => ?_, htop⟩
        obtain ⟨i, hi⟩ := hWr k
        exact ⟨i, fun h => hi (hIW h)⟩
    rw [hdiv]
    simp [cycEval]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
