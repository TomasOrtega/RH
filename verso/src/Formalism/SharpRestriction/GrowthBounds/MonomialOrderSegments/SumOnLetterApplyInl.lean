import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DdivOnLetterMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

/- English proof (translation)
Introduce `β`. Rewrite using `[coeff_ddiv]`. Establish `h1 : vge v 0 ((β + M).prod fun x k => (k.choose (M x) : K))`. Unfold `Finsupp.prod`. Rewrite using `[← Nat.cast_prod]`.

Conclude with `vge_natCast v _`. Use `vge_mul v (hF (β + M)) h1` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.
-/
theorem cge_ddiv (v : AddValuation K (WithTop ℚ)) {σ : Type} (M : σ →₀ ℕ) {a : ℝ}
    {F : MvPolynomial σ K} (hF : cge v a F) : cge v a (ddiv M F) := by
  intro β
  rw [coeff_ddiv]
  have h1 : vge v 0 ((β + M).prod fun x k => (k.choose (M x) : K)) := by
    unfold Finsupp.prod
    rw [← Nat.cast_prod]
    exact vge_natCast v _
  have := vge_mul v (hF (β + M)) h1
  rwa [add_zero] at this

namespace TwistData

variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)

def ChOK (θ : (j : Fin D.J) → Fin (D.nch j) → ℝ) (a : ℝ) (G : MvPolynomial (D.OL × Fin D.r) K) : Prop :=
  ∃ G0 E : MvPolynomial (D.OL × Fin D.r) K, G = G0 + E ∧ cge v a G0 ∧ cge v (a + D.c) E ∧
    ∀ (ρ : D.Tau → Fin D.r → ℕ) (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (θ j i) (D.digitPart p ρ G0)

variable {D v p}

/- English proof (translation)
Take `⟨G0, E, h1, h2, h3, h4⟩` from `h`. Conclude with `⟨G0, E, h1, h2, h3, fun ρ j i => vala_mono (hθ j i) (h4 ρ j i)⟩`.
-/
theorem ChOK.mono {θ θ' : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (hθ : ∀ j i, θ' j i ≤ θ j i) :
    D.ChOK v p θ' a G := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  exact ⟨G0, E, h1, h2, h3, fun ρ j i => vala_mono (hθ j i) (h4 ρ j i)⟩

variable (D p)

def CostA (n : ℕ) (f : D.EA → K) : Prop :=
  ∀ ρ : D.Tau → Fin D.r → ℕ, CostV D.msg Set.univ n (fun ζ => f (D.emb p ρ ζ))

/- English proof (translation)
The claim follows from `costV_ok D.msg Set.univ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)`.
-/
theorem costM_ok : CostOK (CostV (K := K) (r := D.r) D.msg Set.univ) :=
  costV_ok D.msg Set.univ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)

/- English proof (translation)
Introduce `_` and use `D.costM_ok.one mul := fun m n _ _ hf hg ρ => D.costM_ok.mul m n _ _ (hf ρ) (hg ρ) add := fun n _ _ hf hg ρ => D.costM_ok.add n _ _ (hf ρ) (hg ρ) smul := fun n a _ hf ρ => D.costM_ok.smul n a _ (hf ρ) mono := fun m n _ hmn hf ρ => D.costM_ok.mono m n _ hmn (hf ρ)`.
-/
theorem costA_ok : CostOK (D.CostA p) where
  one := fun _ => D.costM_ok.one
  mul := fun m n _ _ hf hg ρ => D.costM_ok.mul m n _ _ (hf ρ) (hg ρ)
  add := fun n _ _ hf hg ρ => D.costM_ok.add n _ _ (hf ρ) (hg ρ)
  smul := fun n a _ hf ρ => D.costM_ok.smul n a _ (hf ρ)
  mono := fun m n _ hmn hf ρ => D.costM_ok.mono m n _ hmn (hf ρ)

/- English proof (translation)
Introduce `_ _ _ _ h` and use `vala_dg_choose hV2 x k h`.
-/
theorem costM_choose [NeZero D.r] (hV2 : V2 K) (x : D.ML × Fin D.r) (k : ℕ) :
    CostV (K := K) D.msg Set.univ k (fun ζ => ((ζ x).choose k : K)) :=
  fun _ _ _ _ h => vala_dg_choose hV2 x k h

/- English proof (translation)
Introduce `ρ`. Take `⟨i, a⟩` from `x`. Break down `i with b | t` into its components or cases. Simplify using `only [emb_inl]`. Conclude with `D.costM_choose hV2 (D.mb b, a) k`.

Simplify using `only [emb_inr]`. Conclude with `cost_choose_affine D.costM_ok (fun ζ => ζ (D.mw t, a)) (fun k => D.costM_choose hV2 (D.mw t, a) k) (ρ t a) (D.P p t) k`.
-/
theorem costA_choose [NeZero D.r] (hV2 : V2 K) (x : D.OL × Fin D.r) (k : ℕ) :
    D.CostA p k (fun α => ((α x).choose k : K)) := by
  intro ρ
  obtain ⟨i, a⟩ := x
  rcases i with b | t
  · simp only [emb_inl]
    exact D.costM_choose hV2 (D.mb b, a) k
  · simp only [emb_inr]
    exact cost_choose_affine D.costM_ok (fun ζ => ζ (D.mw t, a))
      (fun k => D.costM_choose hV2 (D.mw t, a) k) (ρ t a) (D.P p t) k

variable {D p}

/- English proof (translation)
Take `⟨G0, E, h1, h2, h3, h4⟩` from `h`. Establish `hC` using `D.costA_ok (K := K) p`. Take `⟨g, hg0, hg1, hg2⟩` from `approx_of_trunc (v := v) hC (D.costA_choose p hV2) T lam hlam f hf`. Use `⟨Formalism.MainNotions.PlaneGram.dg g G0, Formalism.MainNotions.PlaneGram.dg (fun α => f α - g α) G0 + Formalism.MainNotions.PlaneGram.dg f E, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, map_add, dg_sub_fun]`.

Normalize the expressions using the abelian group laws. Use `cge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) h2` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Use `cge_add v ?_ ?_` and prove the remaining obligations. Use `cge_dg v (fun α => (vge_natCast_bound v D.c _).mpr (hg1 α)) h2` as an intermediate fact.

Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Use `cge_dg v (fun α => (vge_zero_iff v _).mpr (hf0 α)) h3` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Introduce `ρ j i`. Rewrite using `[digitPart_dg]`.

Use `hg2 ρ (D.chainSet j i) (Set.mem_univ _) (θ j i) _ (h4 ρ j i)` as an intermediate fact. Establish `e : θ j i - ((6 * D.c : ℕ) : ℝ) = θ j i - 6 * D.c` using `by push_cast; ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem ChOK.dg [NeZero D.r] (hV2 : V2 K) {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (f : D.EA → K)
    (hf0 : ∀ α, 0 ≤ v (f α)) (T : Finset (D.OL × Fin D.r → ℕ)) (lam : (D.OL × Fin D.r → ℕ) → K)
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c)
    (hf : ∀ α : D.EA, ((D.c : ℕ) : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    D.ChOK v p (fun j i => θ j i - 6 * D.c) a (Formalism.MainNotions.PlaneGram.dg f G) := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  have hC := D.costA_ok (K := K) p
  obtain ⟨g, hg0, hg1, hg2⟩ :=
    approx_of_trunc (v := v) hC (D.costA_choose p hV2) T lam hlam f hf
  refine ⟨Formalism.MainNotions.PlaneGram.dg g G0, Formalism.MainNotions.PlaneGram.dg (fun α => f α - g α) G0 + Formalism.MainNotions.PlaneGram.dg f E,
    ?_, ?_, ?_, ?_⟩
  · rw [h1, map_add, dg_sub_fun]; abel
  · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) h2
    rwa [zero_add] at this
  · refine cge_add v ?_ ?_
    · have := cge_dg v (fun α => (vge_natCast_bound v D.c _).mpr (hg1 α)) h2
      rwa [add_comm] at this
    · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hf0 α)) h3
      rwa [zero_add] at this
  · intro ρ j i
    rw [digitPart_dg]
    have := hg2 ρ (D.chainSet j i) (Set.mem_univ _) (θ j i) _ (h4 ρ j i)
    have e : θ j i - ((6 * D.c : ℕ) : ℝ) = θ j i - 6 * D.c := by push_cast; ring
    rwa [e] at this

/- English proof (translation)
Rewrite using `[opS_apply]`. Use `vala_smul c1 (vala_mul_left_nonneg ?_ (vala_ddiv_letter hV2 (D.mw t) κ1 hQ))` and prove the remaining obligations. Use `valS_nonneg_of_vec D.msg S _ fun α hα i a hne => ?_` and prove the remaining obligations. Use `support_monomial_subset hα` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`.

Rewrite `hne` using `[this, onLetter_apply]`. Distinguish the cases in `hi : i = D.mw t`. Rewrite using `[hi]`. Both sides reduce to the same expression. Rewrite `hne` using `[if_neg hi]`.

Conclude with `absurd rfl hne`.
-/
theorem vala_opS [NeZero D.r] (hV2 : V2 K) (t : D.Tau) (S : Finset D.ML) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S (θ - absE κ1) (D.opS t μ κ1 c1 Q) := by
  classical
  rw [opS_apply]
  refine vala_smul c1 (vala_mul_left_nonneg ?_ (vala_ddiv_letter hV2 (D.mw t) κ1 hQ))
  refine valS_nonneg_of_vec D.msg S _ fun α hα i a hne => ?_
  have := support_monomial_subset hα
  rw [Finset.mem_singleton] at this
  rw [this, onLetter_apply] at hne
  by_cases hi : i = D.mw t
  · rw [hi]; rfl
  · rw [if_neg hi] at hne; exact absurd rfl hne

/- English proof (translation)
Establish `hform : ∀ α : D.EM, D.opS t μ κ1 c1 (monomial α 1) = monomial (onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1)) (c1 * bin κ1 (letE α (D.mw t)))`. Introduce `α`. Rewrite using `[opS_apply, ddiv_monomial', monomial_mul, smul_monomial, bin_onLetter]`. Simplify using the standard rewrite rules. Use `vala_outside_linear (D.opS t μ κ1 c1) (fun i => i = D.mw t) (fun i hi h => hS (h ▸ hi)) ?_ ?_ hQ` and prove the remaining obligations.

Introduce `α`. Rewrite using `[hform, hform, monomial_mul, one_mul]`. Establish `e1 : onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1) = eIn (fun i => i = D.mw t) α + (onLetter (D.mw t) μ + (eOut (fun i => i = D.mw t) α - onLetter (D.mw t) κ1))`. Use extensionality with `⟨i, a⟩`. Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, onLetter_apply, eIn_apply, eOut_apply]`.

Distinguish the cases in `hi : i = D.mw t`. Simplify using `[hi]`. Simplify using `[hi]`. Establish `e2 : letE (eOut (fun i => i = D.mw t) α) (D.mw t) = letE α (D.mw t)`. Use extensionality with `a`.

Simplify using `[eOut_apply]`. Rewrite using `[e1, e2]`. Introduce `α`. Rewrite using `[hform]`. Use `valS_nonneg_of_vec D.msg S _ fun β hβ i a hne => ?_` and prove the remaining obligations.

Use `support_monomial_subset hβ` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Distinguish the cases in `hi : i = D.mw t`. Rewrite using `[hi]`. Both sides reduce to the same expression.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Rewrite using `[this]`. Simplify using `[onLetter_apply, eOut_apply, hi]`.
-/
theorem vala_opS_out (t : D.Tau) (S : Finset D.ML) (hS : D.mw t ∉ S) (μ κ1 : Fin D.r →₀ ℕ) (c1 : K)
    {θ : ℝ} {Q : MvPolynomial (D.ML × Fin D.r) K} (hQ : vala D.msg S θ Q) :
    vala D.msg S θ (D.opS t μ κ1 c1 Q) := by
  classical
  have hform : ∀ α : D.EM, D.opS t μ κ1 c1 (monomial α 1) =
      monomial (onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1))
        (c1 * bin κ1 (letE α (D.mw t))) := by
    intro α
    rw [opS_apply, ddiv_monomial', monomial_mul, smul_monomial, bin_onLetter]
    simp
  refine vala_outside_linear (D.opS t μ κ1 c1) (fun i => i = D.mw t)
    (fun i hi h => hS (h ▸ hi)) ?_ ?_ hQ
  · intro α
    rw [hform, hform, monomial_mul, one_mul]
    have e1 : onLetter (D.mw t) μ + (α - onLetter (D.mw t) κ1) =
        eIn (fun i => i = D.mw t) α + (onLetter (D.mw t) μ +
          (eOut (fun i => i = D.mw t) α - onLetter (D.mw t) κ1)) := by
      ext ⟨i, a⟩
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, onLetter_apply, eIn_apply, eOut_apply]
      by_cases hi : i = D.mw t
      · simp [hi]
      · simp [hi]
    have e2 : letE (eOut (fun i => i = D.mw t) α) (D.mw t) = letE α (D.mw t) := by
      ext a
      simp [eOut_apply]
    rw [e1, e2]
  · intro α
    rw [hform]
    refine valS_nonneg_of_vec D.msg S _ fun β hβ i a hne => ?_
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    by_cases hi : i = D.mw t
    · rw [hi]; rfl
    · exfalso
      apply hne
      rw [this]
      simp [onLetter_apply, eOut_apply, hi]

/- English proof (translation)
Introduce `hm`. Unfold `chainSet wSet at hm`. Break down `Finset.mem_union.mp hm with h1 | h1` into its components or cases. Take `⟨b, -, hb⟩` from `Finset.mem_image.mp h1`. Simplify using `[mb, mw] at hb`.

Take `⟨m, -, hm'⟩` from `Finset.mem_image.mp h1`. Apply `h` to reduce the goal to its premises. Establish `: (D.aux₃ j, m) = t` using `by simpa [mw] using hm'`. Rewrite using `[← this]`.
-/
theorem mw_not_mem_chainSet (D : TwistData K) (t : D.Tau) (j : Fin D.J) (i : Fin (D.nch j))
    (h : t.1 ≠ D.aux₃ j) : D.mw t ∉ D.chainSet j i := by
  classical
  intro hm
  unfold chainSet wSet at hm
  rcases Finset.mem_union.mp hm with h1 | h1
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h1
    simp [mb, mw] at hb
  · obtain ⟨m, -, hm'⟩ := Finset.mem_image.mp h1
    apply h
    have : (D.aux₃ j, m) = t := by simpa [mw] using hm'
    rw [← this]

/- English proof (translation)
Take `⟨G0, E, h1, h2, h3, h4⟩` from `h`. Take `⟨I, hI, cls, cf, ρ', δ, κ, hcf, hκ, hder⟩` from `der' v p hDER hD D.r (D.g t) M D.c hc`. Establish `hP : 0 < D.P p t` using `pow_pos hD.prime.pos _`. Use `⟨appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0, (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G0 - appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0) + Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) E, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, ddiv_add]`.

Normalize the expressions using the abelian group laws. Conclude with `cge_appL v _ _ cls cf ρ' δ κ hcf h2`. Conclude with `cge_add v (cge_ddiv_sub_appL v _ (D.P p t) M cls cf ρ' δ κ D.c hder h2) (cge_ddiv v _ h3)`. Introduce `ρ'' j i`. Rewrite using `[D.digitPart_appL p t hP]`.

Use `vala_sum _ _ fun s _ => ?_` and prove the remaining obligations. Use `show vala D.msg (D.chainSet j i) (θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) _`. Distinguish the cases in `hB : (fun a => ρ' s a % D.P p t) = ρ'' t`. Rewrite using `[if_pos hB]`. Distinguish the cases in `hj : t.1 = D.aux₃ j`.

Rewrite using `[if_pos hj]`. Use `vala_mono ?_ (vala_opS hV2 t _ _ (κ s) (cf s) (h4 (Function.update ρ'' t (cls s)) j i))` and prove the remaining obligations. Use `hκ s` as an intermediate fact. Establish `e : ((D.P p t : ℕ) : ℝ) = (p : ℝ) ^ D.g t` using `by unfold P; push_cast; rfl`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hj, sub_zero]`. Conclude with `vala_opS_out t _ (D.mw_not_mem_chainSet t j i hj) _ (κ s) (cf s) (h4 (Function.update ρ'' t (cls s)) j i)`. Rewrite using `[if_neg hB]`. Conclude with `vala_zero _`.
-/
theorem ChOK.ddiv [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (t : D.Tau) (M : Fin D.r →₀ ℕ) :
    D.ChOK v p (fun j i => θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G) := by
  classical
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  obtain ⟨I, hI, cls, cf, ρ', δ, κ, hcf, hκ, hder⟩ := der' v p hDER hD D.r (D.g t) M D.c hc
  have hP : 0 < D.P p t := pow_pos hD.prime.pos _
  refine ⟨appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0,
    (Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) G0 - appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G0) +
      Formalism.MainNotions.PlaneGram.ddiv (onLetter (Sum.inr t) M) E, ?_, ?_, ?_, ?_⟩
  · rw [h1, ddiv_add]; abel
  · exact cge_appL v _ _ cls cf ρ' δ κ hcf h2
  · exact cge_add v (cge_ddiv_sub_appL v _ (D.P p t) M cls cf ρ' δ κ D.c hder h2) (cge_ddiv v _ h3)
  · intro ρ'' j i
    rw [D.digitPart_appL p t hP]
    refine vala_sum _ _ fun s _ => ?_
    show vala D.msg (D.chainSet j i)
      (θ j i - (if t.1 = D.aux₃ j then (absE M : ℝ) / (D.P p t : ℝ) + D.c else 0)) _
    by_cases hB : (fun a => ρ' s a % D.P p t) = ρ'' t
    · rw [if_pos hB]
      by_cases hj : t.1 = D.aux₃ j
      · rw [if_pos hj]
        refine vala_mono ?_ (vala_opS hV2 t _ _ (κ s) (cf s) (h4 (Function.update ρ'' t (cls s)) j i))
        have := hκ s
        have e : ((D.P p t : ℕ) : ℝ) = (p : ℝ) ^ D.g t := by unfold P; push_cast; rfl
        rw [e]
        linarith
      · rw [if_neg hj, sub_zero]
        exact vala_opS_out t _ (D.mw_not_mem_chainSet t j i hj) _ (κ s) (cf s)
          (h4 (Function.update ρ'' t (cls s)) j i)
    · rw [if_neg hB]
      exact vala_zero _

/- English proof (translation)
Rewrite using `[Finsupp.finsetSum_apply]`. Simplify using `only [onLetter_apply, letE_apply, Sum.inr.injEq]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem sum_onLetter_apply_inr (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (t : D.Tau) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inr t, a) =
      if t ∈ s then M (Sum.inr t, a) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [onLetter_apply, letE_apply, Sum.inr.injEq]
  rw [Finset.sum_ite_eq]

/- English proof (translation)
Rewrite using `[Finsupp.finsetSum_apply]`. Use `Finset.sum_eq_zero fun t' _ => ?_` and prove the remaining obligations. Rewrite using `[onLetter_apply, if_neg (by simp)]`.
-/
theorem sum_onLetter_apply_inl (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (b : D.Lb) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inl b, a) = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun t' _ => ?_
  rw [onLetter_apply, if_neg (by simp)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty, sub_zero]`. Rewrite using `[ddiv_zero']`. Conclude with `h`.

Consider the case `insert t s ht ih`. Establish `h1` using `ih.ddiv hV2 hDER hD hc t (letE M (Sum.inr t))`. Rewrite `h1` using `[ddiv_ddiv_of_disjoint]`. Rewrite using `[Finset.sum_insert ht]`. Use `h1.mono fun j i => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_insert ht, absE_letE]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨i, a⟩`. Break down `i with b | t'` into its components or cases. Use `right`.

Conclude with `D.sum_onLetter_apply_inl M s b a`. Distinguish the cases in `htt : t' = t`. Use `right`. Rewrite using `[D.sum_onLetter_apply_inr M s t' a, if_neg (htt ▸ ht)]`. Use `left`.

Rewrite using `[onLetter_apply, if_neg (fun hh => htt (Sum.inr.inj hh))]`.
-/
theorem ChOK.ddiv_finset [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA) (s : Finset D.Tau) :
    D.ChOK v p (fun j i => θ j i - ∑ t ∈ s,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (∑ t ∈ s, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) G) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    rw [ddiv_zero']
    exact h
  | insert t s ht ih =>
    have h1 := ih.ddiv hV2 hDER hD hc t (letE M (Sum.inr t))
    rw [ddiv_ddiv_of_disjoint] at h1
    · rw [Finset.sum_insert ht]
      refine h1.mono fun j i => ?_
      rw [Finset.sum_insert ht, absE_letE]
      linarith
    · rintro ⟨i, a⟩
      rcases i with b | t'
      · right; exact D.sum_onLetter_apply_inl M s b a
      · by_cases htt : t' = t
        · right
          rw [D.sum_onLetter_apply_inr M s t' a, if_neg (htt ▸ ht)]
        · left
          rw [onLetter_apply, if_neg (fun hh => htt (Sum.inr.inj hh))]

/- English proof (translation)
Establish `h1` using `h.ddiv_finset hV2 hDER hD hc M Finset.univ`. Establish `e : (∑ t, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) = M`. Use extensionality with `⟨i, a⟩`. Break down `i with b | t` into its components or cases. Rewrite using `[D.sum_onLetter_apply_inl M _ b a, hM]`.

Rewrite using `[D.sum_onLetter_apply_inr M _ t a, if_pos (Finset.mem_univ _)]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem ChOK.ddiv_all [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA)
    (hM : ∀ b a, M (Sum.inl b, a) = 0) :
    D.ChOK v p (fun j i => θ j i - ∑ t,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv M G) := by
  have h1 := h.ddiv_finset hV2 hDER hD hc M Finset.univ
  have e : (∑ t, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) = M := by
    ext ⟨i, a⟩
    rcases i with b | t
    · rw [D.sum_onLetter_apply_inl M _ b a, hM]
    · rw [D.sum_onLetter_apply_inr M _ t a, if_pos (Finset.mem_univ _)]
  rwa [e] at h1

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `hJ : 0 < D.J` using `j.pos`. Establish `hj` using `j.isLt`. Simplify using `only [nxt, aux₃]`. Rewrite using `[Nat.mod_add_mod, show j.val + D.J - 1 + 1 = j.val + D.J by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]`.
-/
theorem nxt_prv (D : TwistData K) (j : Fin D.J) : D.nxt (D.aux₃ j) = j := by
  apply Fin.ext
  have hJ : 0 < D.J := j.pos
  have hj := j.isLt
  simp only [nxt, aux₃]
  rw [Nat.mod_add_mod, show j.val + D.J - 1 + 1 = j.val + D.J by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj]

/- English proof (translation)
Establish `h` using `hH (D.aux₃ j) m`. Rewrite `h` using `[D.nxt_prv j]`. Conclude with `h i`.
-/
theorem hypH' (D : TwistData K) (p : ℕ) (kH : ℝ) (hH : D.HypH p kH) (j : Fin D.J) (m : Fin D.r)
    (i : Fin (D.nch j)) :
    (D.r : ℝ) * D.dLL (D.aux₃ j) / (D.P p (D.aux₃ j, m) : ℝ) + kH * D.r * D.c ≤ D.sl j i := by
  have h := hH (D.aux₃ j) m
  rw [D.nxt_prv j] at h
  exact h i

/- English proof (translation)
Establish `hr' : (0 : ℝ) < D.r` using `by exact_mod_cast hr`. Establish `hr1 : (1 : ℝ) ≤ D.r` using `by exact_mod_cast hr`. Establish `hc0 : (0 : ℝ) ≤ D.c` using `Nat.cast_nonneg _`. Establish `e1 : (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) = ∑ m : Fin D.r, ((ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c)`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single (D.aux₃ j)]`.

Simplify using the standard rewrite rules. Introduce `j0 _ hj0`. Simplify using `[hj0]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[e1]`. Establish `e2 : ∀ m : Fin D.r, (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c ≤ (D.sl j i - 13 * D.r * D.c) / D.r + D.c`. Introduce `m`. Establish `hP : (0 : ℝ) < (D.P p (D.aux₃ j, m) : ℝ)`. Establish `: 0 < D.P p (D.aux₃ j, m)` using `pow_pos hp _`.

Conclude with `this` after adjusting the coercions. Establish `h1` using `D.hypH' p 13 hH j m i`. Establish `h2 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) ≤ D.dLL (D.aux₃ j)` using `by exact_mod_cast hMd (D.aux₃ j, m)`. Establish `h3 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤ (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ)` using `div_le_div_of_nonneg_right h2 hP.le`. Establish `h4 : (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤ (D.sl j i - 13 * D.r * D.c) / D.r`.

Rewrite using `[le_div_iff₀ hr']`. Rewrite `h1` using `[mul_div_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3` using `Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin D.r))) => e2 m)`.

Rewrite `e3` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hr'.ne']`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_ldeg_div_add_le_sl (D : TwistData K) (p : ℕ) (hp : 0 < p) (hr : 0 < D.r) (hH : D.HypH p 13) (M : D.EA)
    (hMd : ∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) (j : Fin D.J) (i : Fin (D.nch j)) :
    (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) +
      12 * D.c ≤ D.sl j i := by
  classical
  have hr' : (0 : ℝ) < D.r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
  have hc0 : (0 : ℝ) ≤ D.c := Nat.cast_nonneg _
  have e1 : (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) =
      ∑ m : Fin D.r, ((ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (D.aux₃ j)]
    · simp
    · intro j0 _ hj0
      simp [hj0]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  have e2 : ∀ m : Fin D.r, (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) + D.c ≤
      (D.sl j i - 13 * D.r * D.c) / D.r + D.c := by
    intro m
    have hP : (0 : ℝ) < (D.P p (D.aux₃ j, m) : ℝ) := by
      have : 0 < D.P p (D.aux₃ j, m) := pow_pos hp _
      exact_mod_cast this
    have h1 := D.hypH' p 13 hH j m i
    have h2 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) ≤ D.dLL (D.aux₃ j) := by exact_mod_cast hMd (D.aux₃ j, m)
    have h3 : (ldeg M (Sum.inr (D.aux₃ j, m)) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤
        (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) := div_le_div_of_nonneg_right h2 hP.le
    have h4 : (D.dLL (D.aux₃ j) : ℝ) / (D.P p (D.aux₃ j, m) : ℝ) ≤ (D.sl j i - 13 * D.r * D.c) / D.r := by
      rw [le_div_iff₀ hr']
      rw [mul_div_assoc] at h1
      linarith
    linarith
  have e3 := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin D.r))) => e2 m)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
    mul_div_cancel₀ _ hr'.ne'] at e3
  nlinarith

end TwistData

/- English proof (translation)
Introduce `hD D hValid hH F hF hb M hM0 hMd ρ`. Take `⟨hr, -, hc, -, -, -, hgu, hgs⟩` from `hValid`. Use `haveI : NeZero D.r := ⟨hr.ne'⟩`. Establish `h0 : D.ChOK v p D.th (-D.n0 v) F`. Use `⟨F, 0, by rw [add_zero], ?_, cge_zero v _, fun ρ j i => hF.2.1 ρ j i⟩` and prove the remaining obligations.

Use `cge_of_bge hD hF.1 hb` as an intermediate fact. Rewrite `this` using `[zero_sub]`. Conclude with `this`. Take `⟨T1, lam1, hl1, hf1⟩` from `hgs 1 (Or.inl rfl)`. Take `⟨T2, lam2, hl2, hf2⟩` from `hgs (-1) (Or.inr rfl)`.

Establish `h1` using `h0.dg hV2 D.ga (fun α => (hgu α).ge) T1 lam1 hl1 (fun α => by have := hf1 α; rwa [zpow_one] at this)`. Establish `h2` using `h1.ddiv_all hV2 hDER hD hc M hM0`. Establish `h3` using `h2.dg hV2 (fun α => (D.ga α)⁻¹) (fun α => (v_unit_inv v (hgu α)).ge) T2 lam2 hl2 (fun α => by have := hf2 α; rwa [zpow_neg_one] at this)`. Take `⟨G0, E, hG, -, hE, hval⟩` from `h3`. Use `⟨D.digitPart p ρ G0, D.digitPart p ρ E, ?_, fun j i => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[D.gaAct_eq, hG, D.digitPart_add]`. Use `vala_mono ?_ (hval ρ j i)` and prove the remaining obligations. Use `D.sum_ldeg_div_add_le_sl p hD.prime.pos hr hH M hMd j i` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `D.cge_digitPart p v ρ hE` as an intermediate fact.

Rewrite `this` using `[neg_add_eq_sub]`. Then use the resulting hypothesis.
-/
theorem stepE_of [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (hV2 : V2 K) (hDER : DER K v p) :
    StepE K v p := by
  intro hD D hValid hH F hF hb M hM0 hMd ρ
  obtain ⟨hr, -, hc, -, -, -, hgu, hgs⟩ := hValid
  haveI : NeZero D.r := ⟨hr.ne'⟩
  have h0 : D.ChOK v p D.th (-D.n0 v) F := by
    refine ⟨F, 0, by rw [add_zero], ?_, cge_zero v _, fun ρ j i => hF.2.1 ρ j i⟩
    have := cge_of_bge hD hF.1 hb
    rw [zero_sub] at this
    exact this
  obtain ⟨T1, lam1, hl1, hf1⟩ := hgs 1 (Or.inl rfl)
  obtain ⟨T2, lam2, hl2, hf2⟩ := hgs (-1) (Or.inr rfl)
  have h1 := h0.dg hV2 D.ga (fun α => (hgu α).ge) T1 lam1 hl1
    (fun α => by have := hf1 α; rwa [zpow_one] at this)
  have h2 := h1.ddiv_all hV2 hDER hD hc M hM0
  have h3 := h2.dg hV2 (fun α => (D.ga α)⁻¹) (fun α => (v_unit_inv v (hgu α)).ge) T2 lam2 hl2
    (fun α => by have := hf2 α; rwa [zpow_neg_one] at this)
  obtain ⟨G0, E, hG, -, hE, hval⟩ := h3
  refine ⟨D.digitPart p ρ G0, D.digitPart p ρ E, ?_, fun j i => ?_, ?_⟩
  · rw [D.gaAct_eq, hG, D.digitPart_add]
  · refine vala_mono ?_ (hval ρ j i)
    have := D.sum_ldeg_div_add_le_sl p hD.prime.pos hr hH M hMd j i
    linarith
  · have := D.cge_digitPart p v ρ hE
    rwa [neg_add_eq_sub] at this

end Formalism.MainNotions.PlaneGram
