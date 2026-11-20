import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpenPoly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

/- English proof (translation)
Establish `h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)` using `ringKrullDim_nonneg_of_nontrivial`. Establish `h1` using `ringKrullDim_quotient_le J`. Rewrite `h1` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢`. Proceed by induction on `x using WithBot.recBotCoe with`.

Consider the case `bot => simp at h0`. Consider the case `coe k`. Proceed by induction on `k using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Establish `h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞)` using `h1`. Conclude with `absurd (WithBot.coe_le_coe.1 h2) (by simp)`. Consider the case `coe k => exact ⟨k, rfl⟩`.
-/
theorem IsolatedPointsCountPrime.exists_dim_eq {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_quotient_le J
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k => exact ⟨k, rfl⟩

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]`. Consider the case `mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]`.
-/
theorem IsolatedPointsCountPrime.eval_aeval {n m : ℕ} (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin m) ℂ) (x : Fin n → ℂ) :
    eval x (aeval Q f) = eval (fun i => eval x (Q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

/- English proof (translation)
Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hS`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_and, not_not] at h`. Apply `hΔ` to reduce the goal to its premises. Use `funext_set (fun i => Metric.ball (w i) ε) (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)` and prove the remaining obligations.

Rewrite using `[map_zero]`. Use `h y (hball ?_)` and prove the remaining obligations. Rewrite using `[ball_pi w hε]`. Conclude with `hy`.
-/
theorem IsolatedPointsCountPrime.exists_eval_ne_zero {d : ℕ} {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0)
    {w : Fin d → ℂ} {S : Set (Fin d → ℂ)} (hS : S ∈ 𝓝 w) : ∃ w' ∈ S, eval w' Δ ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hΔ
  refine funext_set (fun i => Metric.ball (w i) ε)
    (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hball ?_)
  rw [ball_pi w hε]
  exact hy

/- English proof (translation)
Introduce `n m P hP Q`. Establish `hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime` using `RingHom.ker_isPrime _`. Use `set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK`. Take `⟨d, hd⟩` from `IsolatedPointsCountPrime.exists_dim_eq P`. Take `⟨r, hr⟩` from `IsolatedPointsCountPrime.exists_dim_eq K`.

Establish `hrd : r ≤ d`. Establish `h` using `hDim n m P Q hP`. Rewrite `h` using `[← hK, hr, hd]`. Conclude with `h` after adjusting the coercions. Take `⟨B, hB⟩` from `(GenericProjectionFinite.full m r K hKp hr).2.1`.

Establish `hfib` using `FibreBound.full m r K B hKp hr hB`. Use `set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm`. Establish `hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K`. Introduce `x hx f hf`. Establish `hf' : aeval Q f ∈ P`.

Rewrite `hf` using `[hK, RingHom.mem_ker]`. Simplify `hf` using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← IsolatedPointsCountPrime.eval_aeval]`. Conclude with `hx _ hf'`. Establish `hQc : Continuous Qm` using `continuous_pi fun i => MvPolynomial.continuous_eval _`.

Use `set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq`. Establish `hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x)`. Introduce `x`. Use function extensionality and compare the values at `i`. Simplify using `only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X, Matrix.mulVec, dotProduct, hQm]`.

Establish `step1 : ∀ z x, x ∈ isolatedFibrePts P Q z → ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x`. Introduce and unpack `z x ⟨hxP, hxQ, V, hV, hiso⟩`. Establish `hQx : Qm x = z` using `funext hxQ`. Establish `hfin : (fibre K B (B.mulVec z) \ {z}).Finite` using `(hfib (B.mulVec z)).2.1.subset Set.sdiff_subset`. Establish `hO : (fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x)`.

Rewrite using `[hQx]`. Conclude with `hfin.isClosed.compl_mem_nhds fun h => h.2 rfl`. Use `⟨V ∩ Qm ⁻¹' (fibre K B (B.mulVec z) \ {z})ᶜ, Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩` and prove the remaining obligations. Introduce and unpack `x' ⟨hx'P, hx'V, hx'O⟩ hx'q`. Use `hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i` and prove the remaining obligations.

Establish `h1 : B.mulVec (Qm x') = B.mulVec z`. Rewrite using `[← hqe, ← hQx, ← hqe]`. Use function extensionality and compare the values at `i`. Conclude with `hx'q i`. Assume the negation of the conclusion as `hne`.

Conclude with `hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩`. Break down `lt_or_eq_of_le hrd with hlt | rfl` into its components or cases. Use `⟨0, fun z => ?_⟩` and prove the remaining obligations. It suffices to establish `isolatedFibrePts P Q z = ∅ by simp [this]`. Use `Set.eq_empty_of_forall_notMem fun x hx => ?_` and prove the remaining obligations.

Take `⟨W, hW, hiso⟩` from `step1 z x hx`. Use `set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp`. Establish `hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x` using `⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by`. Simplify `h ⟨i, i.isLt.trans hlt⟩⟩` using `[hp, i.isLt]`. Establish `himg` using `hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem`.

Use `set px : Fin d → ℂ := fun i => eval x (p i) with hpx`. Use `set j : Fin d := ⟨r, hlt⟩`. Establish `hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆ {w | w j = 0}`. Introduce and unpack `_ ⟨y, -, rfl⟩`. Simplify using `[hp, j]`.

Establish `hc : Continuous fun t : ℂ => Function.update px j t` using `continuous_const.update j continuous_id`. Establish `h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j)`. Use `hc.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[Function.update_eq_self]`. Conclude with `Filter.mem_of_superset himg hsub`.

Establish `h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0}`. Introduce `t ht`. Simplify using `using ht`. Conclude with `(infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)`. Establish `hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q))`.

Establish `hcomp : aeval q = (aeval Q).comp (pullback B)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[hq, pullback]`. Introduce `a b hab`.

Apply `hB.injective` to reduce the goal to its premises. Simplify using `only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢`. Rewrite `hab` using `[hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]`. Rewrite using `[hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hab`.

Take `⟨e, Δ, hΔ, hbound⟩` from `hDom n r P q hP hd hinj`. Use `⟨e, fun z => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Take `⟨t, hts, htc⟩` from `Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)`.

Establish `htc' : t.encard = ((e + 1 : ℕ) : ℕ∞)` using `by rw [htc]; push_cast; rfl`. Establish `htf : t.Finite` using `Set.finite_of_encard_eq_coe htc'`. Take `⟨U, hUo, hUd⟩` from `htf.t2_separation`. Establish `hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈ 𝓝 (B.mulVec z)`. Introduce `x hx`.

Establish `hx'` using `hts hx`. Take `⟨W, hW, hiso⟩` from `step1 z x hx'`. Establish `h` using `hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)`. Establish `e1 : (fun i => eval x (q i)) = B.mulVec z`. Rewrite using `[hqe]`.

Use `congr 1`. Conclude with `funext hx'.2.1`. Rewrite `h` using `[e1]`. Then use the resulting hypothesis. Establish `hI` using `(Filter.biInter_mem htf).2 hw`. Take `⟨w', hw'I, hΔw'⟩` from `IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI`.

Establish `hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w'` using `fun x hx => Set.mem_iInter₂.1 hw'I x hx`. Use `choose! g hg1 hg2 using hpick`. Establish `hinjg : Set.InjOn g t`. Introduce `x hx y hy hxy`. Assume the negation of the conclusion as `hne`.

Use `Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_` and prove the remaining obligations. Rewrite using `[hxy]`. Conclude with `(hg1 y hy).2`. Establish `himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i}`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩`. Establish `hle` using `(Set.encard_le_encard himg).trans (hbound w' hΔw')`. Rewrite `hle` using `[hinjg.encard_image, htc']`. Establish `hle' : e + 1 ≤ e` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsolatedPointsCountPrime.proof (hOpen : IsolatedFibreOpenPoly.Statement)
    (hDom : DominantFibreBound.Statement) (hDim : ImageDimLe.Statement) :
    IsolatedPointsCountPrime.Statement := by
  classical
  intro n m P hP Q

  have hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime := RingHom.ker_isPrime _
  set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK
  obtain ⟨d, hd⟩ := IsolatedPointsCountPrime.exists_dim_eq P
  obtain ⟨r, hr⟩ := IsolatedPointsCountPrime.exists_dim_eq K
  have hrd : r ≤ d := by
    have h := hDim n m P Q hP
    rw [← hK, hr, hd] at h
    exact_mod_cast h
  obtain ⟨B, hB⟩ := (GenericProjectionFinite.full m r K hKp hr).2.1
  have hfib := FibreBound.full m r K B hKp hr hB

  set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm
  have hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K := by
    intro x hx f hf
    have hf' : aeval Q f ∈ P := by
      rw [hK, RingHom.mem_ker] at hf
      simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hf
    rw [← IsolatedPointsCountPrime.eval_aeval]
    exact hx _ hf'
  have hQc : Continuous Qm := continuous_pi fun i => MvPolynomial.continuous_eval _

  set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq
  have hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x) := by
    intro x
    funext i
    simp only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X,
      Matrix.mulVec, dotProduct, hQm]

  have step1 : ∀ z x, x ∈ isolatedFibrePts P Q z →
      ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x := by
    rintro z x ⟨hxP, hxQ, V, hV, hiso⟩
    have hQx : Qm x = z := funext hxQ
    have hfin : (fibre K B (B.mulVec z) \ {z}).Finite := (hfib (B.mulVec z)).2.1.subset Set.sdiff_subset
    have hO : (fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x) := by
      rw [hQx]
      exact hfin.isClosed.compl_mem_nhds fun h => h.2 rfl
    refine ⟨V ∩ Qm ⁻¹' (fibre K B (B.mulVec z) \ {z})ᶜ,
      Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩
    rintro x' ⟨hx'P, hx'V, hx'O⟩ hx'q
    refine hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i
    have h1 : B.mulVec (Qm x') = B.mulVec z := by
      rw [← hqe, ← hQx, ← hqe]
      funext i
      exact hx'q i
    by_contra hne
    exact hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩
  rcases lt_or_eq_of_le hrd with hlt | rfl
  ·
    refine ⟨0, fun z => ?_⟩
    suffices isolatedFibrePts P Q z = ∅ by simp [this]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨W, hW, hiso⟩ := step1 z x hx
    set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp
    have hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x :=
      ⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by
        simpa [hp, i.isLt] using h ⟨i, i.isLt.trans hlt⟩⟩
    have himg := hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem
    set px : Fin d → ℂ := fun i => eval x (p i) with hpx
    set j : Fin d := ⟨r, hlt⟩
    have hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆
        {w | w j = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp [hp, j]
    have hc : Continuous fun t : ℂ => Function.update px j t := continuous_const.update j continuous_id
    have h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [Function.update_eq_self]
      exact Filter.mem_of_superset himg hsub
    have h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0} := by
      intro t ht
      simpa using ht
    exact (infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)
  ·
    have hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q)) := by
      have hcomp : aeval q = (aeval Q).comp (pullback B) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [hq, pullback]
      intro a b hab
      apply hB.injective
      simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢
      rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub] at hab
      rw [hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hab
    obtain ⟨e, Δ, hΔ, hbound⟩ := hDom n r P q hP hd hinj
    refine ⟨e, fun z => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have htc' : t.encard = ((e + 1 : ℕ) : ℕ∞) := by rw [htc]; push_cast; rfl
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc'
    obtain ⟨U, hUo, hUd⟩ := htf.t2_separation
    have hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈
        𝓝 (B.mulVec z) := by
      intro x hx
      have hx' := hts hx
      obtain ⟨W, hW, hiso⟩ := step1 z x hx'
      have h := hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)
      have e1 : (fun i => eval x (q i)) = B.mulVec z := by
        rw [hqe]
        congr 1
        exact funext hx'.2.1
      rwa [e1] at h
    have hI := (Filter.biInter_mem htf).2 hw
    obtain ⟨w', hw'I, hΔw'⟩ := IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI
    have hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w' :=
      fun x hx => Set.mem_iInter₂.1 hw'I x hx
    choose! g hg1 hg2 using hpick
    have hinjg : Set.InjOn g t := by
      intro x hx y hy hxy
      by_contra hne
      refine Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_
      rw [hxy]
      exact (hg1 y hy).2
    have himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩
    have hle := (Set.encard_le_encard himg).trans (hbound w' hΔw')
    rw [hinjg.encard_image, htc'] at hle
    have hle' : e + 1 ≤ e := by exact_mod_cast hle
    omega

end

end GroundTheory.Heights₂.Heights
