import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DegreePositive

variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]

/- English proof (translation)
Establish `hWprime : W.IsPrime` using `hmin.1.1`. Establish `hIW : q ≤ W` using `le_sup_left.trans hmin.1.2`. Establish `hxW : x ∈ W` using `(le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)`. Use `set B := MRing (fun _ : Unit => ι₀) F ⧸ q`. Establish `_ : Algebra.FiniteType F B` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)`.

Use `set W' : Ideal B := W.map (Ideal.Quotient.mk q)`. Establish `hW'prime : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk q x ∈ W'` using `Ideal.mem_map_of_mem _ hxW`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `this`. Establish `hht : W'.height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hmin`.

Establish `hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)`. Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'`. Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`. Rewrite `hform`, `hdrop` using `[hquot]`. Express the relevant statement in the definitionally equal form `ringKrullDim B = _ at hdim`.

Rewrite `hform`, `hdrop` using `[hdim]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by`. Consider the cases of `h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with`. Consider the case `bot`. Use `ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `absurd this (by simp)`. Consider the case `coe y => exact ⟨y, rfl⟩`. Rewrite `hform`, `hdrop`, the goal using `[hy]`. Establish `h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hdrop`.

Establish `h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hform`. Establish `hyle : y ≤ e`. Establish `: y + 1 ≤ (e : ℕ∞) + 1` using `by exact_mod_cast h1`. Conclude with `(ENat.add_le_add_iff_right ENat.one_ne_top).mp this`. Take `⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y` from `ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top e) hyle)`.

Establish `h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m` using `by rw [← h2]; gcongr`. Establish `h4 : e + 1 ≤ 1 + m` using `by exact_mod_cast h3`. Establish `h5 : m ≤ e` using `by exact_mod_cast hyle`. Establish `: m = e` using `by omega`. Substitute `this` using the available equality.

Both sides reduce to the same expression.
-/
theorem ringKrullDim_of_mem_minimalPrimes (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl

omit [Fintype ι₀] in

/- English proof (translation)
Introduce `k`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Establish `hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W`. Introduce and unpack `⟨⟨⟩, i⟩`.

Consider the cases of `k`. Conclude with `h i`. Establish `hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W))`. Introduce `z`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Conclude with `⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩`. Consider the case `add p r hp hr`. Take `⟨a, ha⟩` from `hp`.

Take `⟨b, hb⟩` from `hr`. Conclude with `⟨a + b, by rw [map_add, ha, hb, map_add]⟩`. Consider the case `mul_X p v _`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]`.

Establish `hle` using `ringKrullDim_le_of_surjective _ hsurj`. Rewrite `hle` using `[hW, ringKrullDim_eq_zero_of_field]`. Establish `: e + 1 ≤ 0` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem isRelevant_of_ringKrullDim (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by
  intro k
  by_contra h
  simp only [not_exists, not_not] at h
  have hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W := by
    rintro ⟨⟨⟩, i⟩
    cases k
    exact h i
  have hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩
    | add p r hp hr =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hr
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p v _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [hW, ringKrullDim_eq_zero_of_field] at hle
  have : e + 1 ≤ 0 := by exact_mod_cast hle
  omega

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨i, hi⟩` from `hq.relevant ()`. Establish `hqp` using `hq.isPrime`. Take `⟨hfin, heq⟩` from `GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)`. Establish `heq' : hilbFn q (fun _ => (n : ℤ)) = (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ)` using `heq`. Rewrite using `[heq']`.

Establish `hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈ gradedPiece q (fun _ : Unit => n)`. Use `⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)`. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `hp` using `(isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n`.

Use `hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Consider the cases of `k`. Simplify using `[blockWeight]`. Establish `hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `fun h => hi (hqp.mem_of_pow_mem n h)`. Use `hfin` as an intermediate fact. Establish `: Nontrivial (gradedPiece q (fun _ : Unit => n))` using `⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩`. Establish `hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n))` using `Module.finrank_pos`.

Conclude with `hpos` after adjusting the coercions.
-/
theorem hilbFn_pos (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by
  obtain ⟨i, hi⟩ := hq.relevant ()
  have hqp := hq.isPrime
  obtain ⟨hfin, heq⟩ :=
    GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)
  have heq' : hilbFn q (fun _ => (n : ℤ)) =
      (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ) := heq
  rw [heq']
  have hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈
      gradedPiece q (fun _ : Unit => n) := by
    refine ⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩
    change _ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)
    rw [mem_weightedHomogeneousSubmodule]
    have hp := (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n
    convert hp using 1
    funext k
    cases k
    simp [blockWeight]
  have hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hi (hqp.mem_of_pow_mem n h)
  have := hfin
  have : Nontrivial (gradedPiece q (fun _ : Unit => n)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n)) := Module.finrank_pos
  exact_mod_cast hpos

omit [Fintype ι₀] in

/- English proof (translation)
Introduce `p hp`. Rewrite using `[RingHom.mem_ker]`. Assume the negation of the conclusion as `h`. Establish `h0` using `hq.multiHomog p hp 0`. Rewrite using `[weightedHomogeneousComponent_zero p (fun v => by`.

Take `⟨⟨⟩, _⟩` from `v`. Introduce `h'`. Use `congrFun h' ()` as an intermediate fact. Simplify using `[blockWeight] at this)] at h0`. Establish `hu : IsUnit (C (coeff 0 p) : MRing (fun _ : Unit => ι₀) F)` using `(isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C`.

Conclude with `hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)`.
-/
theorem le_ker_constantCoeff (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (coeff 0 p) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)

/- English proof (translation)
Proceed by induction on `D with`. Consider the case `zero`. Introduce `q hq hd`. Take `⟨a₀, ha⟩` from `HilbertDimZero.proof F Unit (fun _ => ι₀) q hq (by rw [Fintype.card_unit]; exact hd)`. Establish `h` using `ha (fun _ => a₀) (fun _ => le_rfl)`.

Establish `e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ)`. Use function extensionality and compare the values at `fun j => j.elim0`. Rewrite using `[e, ← h]`. Conclude with `hilbFn_pos q hq a₀`. Consider the case `succ D ih`.

Introduce `q hq hd`. Establish `hqp : q.IsPrime` using `hq.isPrime`. Take `⟨i, hX⟩` from `hq.relevant ()`. Use `set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef`. Establish `hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩)` using `isWeightedHomogeneous_X F _ _`.

Establish `hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) < ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞)`. Rewrite using `[hd, Fintype.card_unit]`. Conclude with `(by omega : D + 1 + 1 < D + 2 + 1)` after adjusting the coercions. Establish `hcut` using `CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX (fun _ : Fin D => fun _ : Unit => (1 : ℤ))`. Establish `e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ)) (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ)`.

Use function extensionality and compare the values at `j k`. Consider the cases of `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]`. Rewrite `hcut` using `[e1]`. Rewrite using `[hcut, cycEval]`.

Use `set J := q ⊔ Ideal.span {x} with hJdef`. Establish `hJh : IsMultiHomogIdeal J` using `isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx`. Establish `hterm : ∀ W, divCycle q x W ≠ 0 → 0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ))`. Introduce `W hW`. Unfold `divCycle at hW ⊢`.

Distinguish the cases in `hc : W ∈ J.minimalPrimes ∧ IsRelevant W`. Rewrite `hW`, the goal using `[dif_pos hc]`. Establish `hWp : W.IsPrime` using `hc.1.1.1`. Establish `hWd` using `ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1`. Establish `hWq : IsMultiProjPrime W` using `⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩`.

Conclude with `⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩`. Rewrite `hW` using `[dif_neg hc]`. Conclude with `absurd rfl hW`. Establish `hfin` using `DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x`. Rewrite using `[finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]`.

Use `Finset.sum_pos' (fun W _ => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hW : divCycle q x W = 0`. Rewrite using `[hW, zero_mul]`. Conclude with `(mul_pos (hterm W hW).1 (hterm W hW).2).le`. Establish `hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)`.

Use `sup_le (le_ker_constantCoeff q hq) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Express the relevant statement in the definitionally equal form `constantCoeff x = 0`. Rewrite using `[hxdef, constantCoeff_X]`. Establish `hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime` using `(RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime`.

Take `⟨W, hmin, -⟩` from `Ideal.exists_minimalPrimes_le hJm`. Establish `hWp : W.IsPrime` using `hmin.1.1`. Establish `hWd` using `ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin`. Establish `hrel` using `isRelevant_of_ringKrullDim W D hWd`. Establish `hne : divCycle q x W ≠ 0`.

Unfold `divCycle`. Rewrite using `[dif_pos ⟨hmin, hrel⟩]`. Establish `htop` using `length_localizedQuot_ne_top J W hmin`. Establish `hzero : multAt J W ≠ 0`. Unfold `multAt`.

Rewrite using `[Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]`. Introduce `hs`. Take `⟨r, hr, hr1⟩` from `hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)`. Rewrite `hr1` using `[Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hr (hmin.1.2 hr1)`.

Establish `: (multAt J W).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero]`. Conclude with `not_or.mpr ⟨hzero, htop⟩`. Conclude with `this` after adjusting the coercions. Use `⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩` and prove the remaining obligations.
-/
theorem pos (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨a₀, ha⟩ := HilbertDimZero.proof F Unit (fun _ => ι₀) q hq
      (by rw [Fintype.card_unit]; exact hd)
    have h := ha (fun _ => a₀) (fun _ => le_rfl)
    have e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ) :=
      funext fun j => j.elim0
    rw [e, ← h]
    exact hilbFn_pos q hq a₀
  | succ D ih =>
    intro q hq hd
    have hqp : q.IsPrime := hq.isPrime
    obtain ⟨i, hX⟩ := hq.relevant ()
    set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef
    have hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩) :=
      isWeightedHomogeneous_X F _ _
    have hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) <
        ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
      rw [hd, Fintype.card_unit]
      exact_mod_cast (by omega : D + 1 + 1 < D + 2 + 1)
    have hcut := CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ))
    have e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ))
        (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ) := by
      funext j k
      cases k
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]
    rw [e1] at hcut
    rw [hcut, cycEval]
    set J := q ⊔ Ideal.span {x} with hJdef
    have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

    have hterm : ∀ W, divCycle q x W ≠ 0 →
        0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
      intro W hW
      unfold divCycle at hW ⊢
      by_cases hc : W ∈ J.minimalPrimes ∧ IsRelevant W
      · rw [dif_pos hc] at hW ⊢
        have hWp : W.IsPrime := hc.1.1.1
        have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1
        have hWq : IsMultiProjPrime W :=
          ⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩
        exact ⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩
      · rw [dif_neg hc] at hW
        exact absurd rfl hW
    have hfin := DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x
    rw [finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]
    refine Finset.sum_pos' (fun W _ => ?_) ?_
    · by_cases hW : divCycle q x W = 0
      · rw [hW, zero_mul]
      · exact (mul_pos (hterm W hW).1 (hterm W hW).2).le

    have hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
      refine sup_le (le_ker_constantCoeff q hq) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change constantCoeff x = 0
      rw [hxdef, constantCoeff_X]
    have hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime
    obtain ⟨W, hmin, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have hWp : W.IsPrime := hmin.1.1
    have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin
    have hrel := isRelevant_of_ringKrullDim W D hWd
    have hne : divCycle q x W ≠ 0 := by
      unfold divCycle
      rw [dif_pos ⟨hmin, hrel⟩]
      have htop := length_localizedQuot_ne_top J W hmin
      have hzero : multAt J W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr1⟩ := hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr1
        exact hr (hmin.1.2 hr1)
      have : (multAt J W).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]
        exact not_or.mpr ⟨hzero, htop⟩
      exact_mod_cast this
    refine ⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩

end DegreePositive

/- English proof (translation)
Introduce `F _ ι₀ _ q D hq hd`. Conclude with `DegreePositive.pos D q hq hd`.
-/
theorem DegreePositive.proof : DegreePositive.Statement := by
  intro F _ ι₀ _ q D hq hd
  exact DegreePositive.pos D q hq hd

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
