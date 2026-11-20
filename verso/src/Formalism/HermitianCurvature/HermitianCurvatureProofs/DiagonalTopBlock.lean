import Formalism.HermitianCurvature.StatementTA

namespace Formalism.FourierDecayAlt.P.TA1

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

section general
variable {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def form (P : Finset α) (k : α → α → ℂ) (U V : α → H) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪U p, V p'⟫_ℂ

/- English proof (translation)
Set `S : Submodule ℂ H` to `Submodule.span ℂ (V '' (P : Set α))`. Establish `: FiniteDimensional ℂ S` using `FiniteDimensional.span_of_finite ℂ (P.finite_toSet.image V)`. Set `b` to `stdOrthonormalBasis ℂ S`. Establish `hmem : ∀ p ∈ P, V p ∈ S` using `fun p hp => Submodule.subset_span ⟨p, hp, rfl⟩`. Set `a : Fin (Module.finrank ℂ S) → α → ℂ` to `fun i p => ⟪((b i : S) : H), V p⟫_ℂ`.

Establish `hin : ∀ p ∈ P, ∀ p' ∈ P, ⟪V p, V p'⟫_ℂ = ∑ i, conj (a i p) * a i p'`. Introduce `p hp p' hp'`. Establish `h` using `b.sum_inner_mul_inner ⟨V p, hmem p hp⟩ ⟨V p', hmem p' hp'⟩`. Simplify using `only [Submodule.coe_inner] at h`. Rewrite using `[← h]`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [a, inner_conj_symm]`. Establish `e : form P k V V = ∑ i, ∑ p ∈ P, ∑ p' ∈ P, conj (a i p) * k p p' * a i p'`. Unfold `form`. Use `symm`.

Rewrite using `[Finset.sum_comm]`. Use `sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `sum_congr rfl fun p' hp' => ?_` and prove the remaining obligations. Rewrite using `[hin p hp p' hp', mul_sum]`.

Conclude with `sum_congr rfl fun i _ => by ring`. Rewrite using `[e, Complex.re_sum]`. Conclude with `sum_nonneg fun i _ => hk.2 (a i)`. Use the proof step `@[instance_reducible]`.
-/
lemma form_self_nonneg (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) (V : α → H) :
    0 ≤ (form P k V V).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set α))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (P.finite_toSet.image V)
  let b := stdOrthonormalBasis ℂ S
  have hmem : ∀ p ∈ P, V p ∈ S := fun p hp => Submodule.subset_span ⟨p, hp, rfl⟩
  let a : Fin (Module.finrank ℂ S) → α → ℂ := fun i p => ⟪((b i : S) : H), V p⟫_ℂ
  have hin : ∀ p ∈ P, ∀ p' ∈ P, ⟪V p, V p'⟫_ℂ = ∑ i, conj (a i p) * a i p' := by
    intro p hp p' hp'
    have h := b.sum_inner_mul_inner ⟨V p, hmem p hp⟩ ⟨V p', hmem p' hp'⟩
    simp only [Submodule.coe_inner] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    simp only [a, inner_conj_symm]
  have e : form P k V V = ∑ i, ∑ p ∈ P, ∑ p' ∈ P, conj (a i p) * k p p' * a i p' := by
    unfold form
    symm
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p' hp' => ?_
    rw [hin p hp p' hp', mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [e, Complex.re_sum]
  exact sum_nonneg fun i _ => hk.2 (a i)

@[instance_reducible]
noncomputable def core (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) :
    PreInnerProductSpace.Core ℂ (α → H) where
  inner U V := form P k U V
  conj_inner_symm U V := by
    unfold form
    simp only [map_sum, map_mul, inner_conj_symm]
    rw [sum_comm]
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hk.1 p' hp' p hp]
  re_inner_nonneg V := form_self_nonneg P k hk V
  add_left U V X := by
    simp only [form, Pi.add_apply, inner_add_left, mul_add, sum_add_distrib]
  smul_left U V r := by
    simp only [form, Pi.smul_apply, inner_smul_left, mul_sum]
    exact sum_congr rfl fun p _ => sum_congr rfl fun p' _ => by ring

/- English proof (translation)
Set `c : PreInnerProductSpace.Core ℂ (α → H)` to `core P k hk`. Set `_ : SeminormedAddCommGroup (α → H)` to `@InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (α → H) _ _ _ c`. Conclude with `norm_sum_le T U`.
-/
lemma sqrt_form_sum_le (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) {ι : Type} (T : Finset ι)
    (U : ι → α → H) :
    √(form P k (∑ s ∈ T, U s) (∑ s ∈ T, U s)).re ≤ ∑ s ∈ T, √(form P k (U s) (U s)).re := by
  let c : PreInnerProductSpace.Core ℂ (α → H) := core P k hk
  let _ : SeminormedAddCommGroup (α → H) :=
    @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (α → H) _ _ _ c
  exact norm_sum_le T U

end general

section points
variable {E : Type} [DecidableEq E]

def ls (p : Pt E) : ℕ := (p.getLast?.map Prod.fst).getD 0

omit [DecidableEq E] in
/- English proof (translation)
Simplify using `[ls, Formalism.FourierDecayAlt.TA.ext]`.
-/
lemma ls_ext (h : Pt E) (s : ℕ) (t : E) : ls (Formalism.FourierDecayAlt.TA.ext h s t) = s := by
  simp [ls, Formalism.FourierDecayAlt.TA.ext]

/- English proof (translation)
Rewrite using `[PT]`. Simplify using `only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, h, hh, t, ht, rfl⟩`. Conclude with `⟨m, hm, h, hh, t, ht, rfl⟩`.

Introduce and unpack `⟨m, hm, h, hh, t, ht, rfl⟩`. Conclude with `⟨m, hm, h, hh, t, ht, rfl⟩`.
-/
lemma mem_PT_succ (Sg : ℕ → ℕ → Finset E) (n : ℕ) (p : Pt E) :
    p ∈ PT Sg (n + 1) ↔ ∃ m, m < n + 1 ∧ ∃ h ∈ PT Sg m, ∃ t ∈ Sg (n + 1) (n + 1 - m),
      Formalism.FourierDecayAlt.TA.ext h (n + 1 - m) t = p := by
  rw [PT]
  simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]
  constructor
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, i = n + 1` from `⟨i - 1, by omega⟩`. Take `⟨m, hm, h, _, t, _, rfl⟩` from `(mem_PT_succ Sg n p).1 hp`. Rewrite using `[ls_ext, mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
lemma ls_mem_Icc (Sg : ℕ → ℕ → Finset E) (i : ℕ) (hi : 1 ≤ i) (p : Pt E) (hp : p ∈ PT Sg i) :
    ls p ∈ Icc 1 i := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, hm, h, _, t, _, rfl⟩ := (mem_PT_succ Sg n p).1 hp
  rw [ls_ext, mem_Icc]; omega

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, i = n + 1` from `⟨i - 1, by omega⟩`. Use extensionality with `p`. Simplify using `only [mem_filter, mem_PT_succ, mem_image, mem_product, Prod.exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨m, hm, h, hh, t, ht, rfl⟩, hls⟩`.

Rewrite `hls` using `[ls_ext]`. Substitute `hls` using the available equality. Establish `e : n + 1 - (n + 1 - m) = m` using `by omega`. Conclude with `⟨h, t, ⟨by rwa [e], ht⟩, rfl⟩`. Introduce and unpack `⟨h, t, ⟨hh, ht⟩, rfl⟩`.

Establish `e : n + 1 - (n + 1 - s) = s` using `by omega`. Conclude with `⟨⟨n + 1 - s, by omega, h, hh, t, by rwa [e], by rw [e]⟩, ls_ext _ _ _⟩`.
-/
lemma filter_PT (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    (PT Sg i).filter (fun p => ls p = s) =
      ((PT Sg (i - s)) ×ˢ (Sg i s)).image (fun x => Formalism.FourierDecayAlt.TA.ext x.1 s x.2) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  ext p
  simp only [mem_filter, mem_PT_succ, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨m, hm, h, hh, t, ht, rfl⟩, hls⟩
    rw [ls_ext] at hls
    subst hls
    have e : n + 1 - (n + 1 - m) = m := by omega
    exact ⟨h, t, ⟨by rwa [e], ht⟩, rfl⟩
  · rintro ⟨h, t, ⟨hh, ht⟩, rfl⟩
    have e : n + 1 - (n + 1 - s) = s := by omega
    exact ⟨⟨n + 1 - s, by omega, h, hh, t, by rwa [e], by rw [e]⟩, ls_ext _ _ _⟩

/- English proof (translation)
Rewrite using `[← sum_filter, filter_PT Sg i s hs hsi, sum_image, sum_product_right]`. Introduce and unpack `⟨h, t⟩ _ ⟨h', t'⟩ _ hxy`. Simplify using `only [Formalism.FourierDecayAlt.TA.ext] at hxy`. Use `List.append_inj' hxy rfl` as an intermediate fact. Simplify using `only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this`.

Conclude with `Prod.ext this.1 this.2`.
-/
lemma sum_PT_ls {M : Type} [AddCommMonoid M] (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s)
    (hsi : s ≤ i) (F : Pt E → M) :
    ∑ p ∈ PT Sg i, (if ls p = s then F p else 0) =
      ∑ t ∈ Sg i s, ∑ h ∈ PT Sg (i - s), F (Formalism.FourierDecayAlt.TA.ext h s t) := by
  rw [← sum_filter, filter_PT Sg i s hs hsi, sum_image, sum_product_right]
  rintro ⟨h, t⟩ _ ⟨h', t'⟩ _ hxy
  simp only [Formalism.FourierDecayAlt.TA.ext] at hxy
  have := List.append_inj' hxy rfl
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact Prod.ext this.1 this.2

end points

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `p hp`. Consider the cases of `n with`.

Consider the case `zero`. Simplify using `[PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩`. Consider the case `succ n`. Take `⟨m, hm, h, hh, t, ht, rfl⟩` from `(mem_PT_succ Sg n p).1 hp`. Establish `h0` using `ih m (by omega) h hh`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `h0.1` as an intermediate fact. Simplify using `only [lvl] at this`. Simplify using `[lvl, Formalism.FourierDecayAlt.TA.ext, this]`. Use linear arithmetic over natural numbers and integers.

Introduce `b hb`. Simplify using `only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb`. Break down `hb with hb | rfl` into its components or cases. Conclude with `h0.2 b hb`. Conclude with `⟨by simp; omega, hNZ _ _ t ht⟩`.
-/
theorem isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := (mem_PT_succ Sg n p).1 hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩

end Formalism.FourierDecayAlt.P.TA1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate

/- English proof (translation)
Introduce `E _ _ H _ _ W D Sg Φ w i _ hi hK`. Set `U : ℕ → Pt E → H` to `fun s p => if ls p = s then Φ w p else 0`. Establish `h1 : Slev D Sg Φ w i = (form (PT Sg i) (D.K i) (∑ s ∈ Icc 1 i, U s) (∑ s ∈ Icc 1 i, U s)).re`. Establish `hU : ∀ p ∈ PT Sg i, (∑ s ∈ Icc 1 i, U s) p = Φ w p`. Introduce `p hp`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [U]`. Rewrite using `[sum_ite_eq, if_pos (ls_mem_Icc Sg i hi p hp)]`. Unfold `Slev gram form`. Use `congr 1`.

Use `sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_` and prove the remaining obligations. Rewrite using `[hU p hp, hU p' hp']`. Establish `h2 : ∀ s ∈ Icc 1 i, Ssplit D Sg Φ w i s = (form (PT Sg i) (D.K i) (U s) (U s)).re`. Introduce `s hs`. Take `⟨hs1, hsi⟩` from `mem_Icc.1 hs`.

Establish `e : form (PT Sg i) (D.K i) (U s) (U s) = ∑ p ∈ PT Sg i, if ls p = s then (∑ p' ∈ PT Sg i, if ls p' = s then D.K i p p' * ⟪Φ w p, Φ w p'⟫_ℂ else 0) else 0`. Unfold `form`. Use `sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp : ls p = s`. Rewrite using `[if_pos hp]`.

Use `sum_congr rfl fun p' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp' : ls p' = s`. Simplify using `only [U, if_pos hp, if_pos hp']`. Simplify using `only [U, if_neg hp', inner_zero_right, mul_zero]`. Rewrite using `[if_neg hp]`.

Use `sum_eq_zero fun p' _ => ?_` and prove the remaining obligations. Simplify using `only [U, if_neg hp, inner_zero_left, mul_zero]`. Rewrite using `[e, sum_PT_ls Sg i s hs1 hsi]`. Unfold `Ssplit Nst offK`. Use `congr 1`.

Use `sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[sum_PT_ls Sg i s hs1 hsi]`. Rewrite using `[h1]`.

Use `(sqrt_form_sum_le (PT Sg i) (D.K i) hK (Icc 1 i) U).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `sum_congr rfl fun s hs => by rw [h2 s hs]`.
-/
theorem split_last_block : Formalism.FourierDecayAlt.TA.SplitLast := by
  intro E _ _ H _ _ W D Sg Φ w i _ hi hK
  let U : ℕ → Pt E → H := fun s p => if ls p = s then Φ w p else 0
  have h1 : Slev D Sg Φ w i =
      (form (PT Sg i) (D.K i) (∑ s ∈ Icc 1 i, U s) (∑ s ∈ Icc 1 i, U s)).re := by
    have hU : ∀ p ∈ PT Sg i, (∑ s ∈ Icc 1 i, U s) p = Φ w p := by
      intro p hp
      rw [Finset.sum_apply]
      simp only [U]
      rw [sum_ite_eq, if_pos (ls_mem_Icc Sg i hi p hp)]
    unfold Slev gram form
    congr 1
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hU p hp, hU p' hp']
  have h2 : ∀ s ∈ Icc 1 i, Ssplit D Sg Φ w i s = (form (PT Sg i) (D.K i) (U s) (U s)).re := by
    intro s hs
    obtain ⟨hs1, hsi⟩ := mem_Icc.1 hs
    have e : form (PT Sg i) (D.K i) (U s) (U s) =
        ∑ p ∈ PT Sg i, if ls p = s then
          (∑ p' ∈ PT Sg i, if ls p' = s then D.K i p p' * ⟪Φ w p, Φ w p'⟫_ℂ else 0) else 0 := by
      unfold form
      refine sum_congr rfl fun p _ => ?_
      by_cases hp : ls p = s
      · rw [if_pos hp]
        refine sum_congr rfl fun p' _ => ?_
        by_cases hp' : ls p' = s
        · simp only [U, if_pos hp, if_pos hp']
        · simp only [U, if_neg hp', inner_zero_right, mul_zero]
      · rw [if_neg hp]
        refine sum_eq_zero fun p' _ => ?_
        simp only [U, if_neg hp, inner_zero_left, mul_zero]
    rw [e, sum_PT_ls Sg i s hs1 hsi]
    unfold Ssplit Nst offK
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_PT_ls Sg i s hs1 hsi]
  rw [h1]
  refine (sqrt_form_sum_le (PT Sg i) (D.K i) hK (Icc 1 i) U).trans (le_of_eq ?_)
  exact sum_congr rfl fun s hs => by rw [h2 s hs]

/- English proof (translation)
Introduce `E _ _ H _ _ W D Sg Φ w hNZ hA2`. Unfold `Ssplit Diag`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single t]`.

Introduce `t' ht' hne`. Unfold `Nst`. Use `Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_` and prove the remaining obligations. Use `hA2 (D.r + 1) 1 le_rfl (by omega) le_rfl h h' t t' (isPt_PT Sg hNZ _ h hh) (isPt_PT Sg hNZ _ h' hh') (hNZ _ _ t ht) (hNZ _ _ t' ht') (Or.inr ⟨rfl, rfl, fun e => hne e.symm⟩)` as an intermediate fact. Simplify using `[offK, this]`.

Introduce `h`. Conclude with `absurd ht h`.
-/
theorem diagonal_top_block : Formalism.FourierDecayAlt.TA.DiagTop := by
  intro E _ _ H _ _ W D Sg Φ w hNZ hA2
  unfold Ssplit Diag
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_eq_single t]
  · intro t' ht' hne
    unfold Nst
    refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
    have := hA2 (D.r + 1) 1 le_rfl (by omega) le_rfl h h' t t' (isPt_PT Sg hNZ _ h hh)
      (isPt_PT Sg hNZ _ h' hh') (hNZ _ _ t ht) (hNZ _ _ t' ht')
      (Or.inr ⟨rfl, rfl, fun e => hne e.symm⟩)
    simp [offK, this]
  · intro h; exact absurd ht h

/- English proof (translation)
Introduce `E _ _ H _ _ W D Sg Φ w i s R hNZ hs hsi hi hA hcov huniq`. Take `⟨_, hper, hdom, _⟩` from `hA i s hs hsi hi`. Establish `hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h` using `isPt_PT Sg hNZ (i - s)`. Establish `key : ∀ t ∈ Sg i s, ∀ t0, t - t0 ∈ D.La i s → (Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re ≤ (Nst (Φ w) (PT Sg (i - s)) (D.Th i s t0) s t t).re`. Introduce `t ht t0 h0`.

Establish `e : D.Th i s t = D.Th i s t0`. Use `hper t0 (t - t0) h0` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `h` using `form_self_nonneg (PT Sg (i - s)) _ (hdom t (PT Sg (i - s)) (hNZ _ _ t ht) hHd) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t))`. Establish `e2 : form (PT Sg (i - s)) (fun h h' => D.Th i s t h h' - D.K i (Formalism.FourierDecayAlt.TA.ext h s t) (Formalism.FourierDecayAlt.TA.ext h' s t)) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) = Nst (Φ w) (PT Sg (i …`.

Simplify using `only [form, Nst, offK, sub_mul, sum_sub_distrib]`. Rewrite `h` using `[e2, e, Complex.sub_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Diag Cosets`. Use `le_trans ?_ (le_of_eq (sum_comm' (s := Sg i s) (t := fun t => R.filter (fun t0 => t - t0 ∈ D.La i s)) ?_))` and prove the remaining obligations.

Use `sum_le_sum fun t ht => ?_` and prove the remaining obligations. Take `⟨t0, ht0, h0⟩` from `hcov t ht`. Establish `hf : R.filter (fun x => t - x ∈ D.La i s) = {t0}`. Use extensionality with `x`. Simplify using `only [mem_filter, mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxl⟩`. Use `huniq x hx t0 ht0 ?_` and prove the remaining obligations. Use `(D.La i s).sub_mem h0 hxl` as an intermediate fact. Simplify using `using this`.

Introduce and unpack `rfl`. Conclude with `⟨ht0, h0⟩`. Rewrite using `[hf, sum_singleton]`. Conclude with `key t ht t0 h0`. Introduce `t t0`.

Simplify using `only [mem_filter]`. The claim follows by propositional logic.
-/
theorem diagonal_cosets : Formalism.FourierDecayAlt.TA.DiagCosets := by
  classical
  intro E _ _ H _ _ W D Sg Φ w i s R hNZ hs hsi hi hA hcov huniq
  obtain ⟨_, hper, hdom, _⟩ := hA i s hs hsi hi
  have hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_PT Sg hNZ (i - s)
  have key : ∀ t ∈ Sg i s, ∀ t0, t - t0 ∈ D.La i s →
      (Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re ≤
        (Nst (Φ w) (PT Sg (i - s)) (D.Th i s t0) s t t).re := by
    intro t ht t0 h0
    have e : D.Th i s t = D.Th i s t0 := by
      have := hper t0 (t - t0) h0
      rwa [add_sub_cancel] at this
    have h := form_self_nonneg (PT Sg (i - s)) _ (hdom t (PT Sg (i - s)) (hNZ _ _ t ht) hHd)
      (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t))
    have e2 : form (PT Sg (i - s))
        (fun h h' => D.Th i s t h h' - D.K i (Formalism.FourierDecayAlt.TA.ext h s t) (Formalism.FourierDecayAlt.TA.ext h' s t))
        (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) =
        Nst (Φ w) (PT Sg (i - s)) (D.Th i s t) s t t -
          Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t := by
      simp only [form, Nst, offK, sub_mul, sum_sub_distrib]
    rw [e2, e, Complex.sub_re] at h
    linarith
  unfold Diag Cosets
  refine le_trans ?_ (le_of_eq (sum_comm' (s := Sg i s)
    (t := fun t => R.filter (fun t0 => t - t0 ∈ D.La i s)) ?_))
  · refine sum_le_sum fun t ht => ?_
    obtain ⟨t0, ht0, h0⟩ := hcov t ht
    have hf : R.filter (fun x => t - x ∈ D.La i s) = {t0} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hx, hxl⟩
        refine huniq x hx t0 ht0 ?_
        have := (D.La i s).sub_mem h0 hxl
        simpa using this
      · rintro rfl; exact ⟨ht0, h0⟩
    rw [hf, sum_singleton]
    exact key t ht t0 h0
  · intro t t0
    simp only [mem_filter]
    tauto

/- English proof (translation)
Introduce `E H _ _ W _ len k P Φ V w0 B0 Bc jn hw0 hb hE hV`. Establish `h1 : ∀ᶠ eps in 𝓝[>] (0 : ℝ), (gram k V P).re ≤ Bc * wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)`. Establish `hall : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ p ∈ P, Φ eps w0 p = V p` using `(Filter.eventually_all_finset P).2 hV`. Use `filter_upwards [hall, self_mem_nhdsWithin] with eps h1 h2`. Establish `h3` using `hb eps h2`.

Establish `e : gram k (Φ eps w0) P = gram k V P`. Unfold `gram`. Use `Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_` and prove the remaining obligations. Rewrite using `[h1 p hp, h1 p' hp']`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.

Establish `h2 : Tendsto (fun eps => wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 jn)`. Use `tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `filter_upwards [(tendsto_order.1 (hE w0 hw0)).1 a ha] with eps h`. Conclude with `lt_of_lt_of_le h (le_ciSup (f := fun w : {w // len w ≤ B0} => ‖Φ eps w.1 []‖ ^ 2) (Set.finite_range _).bddAbove ⟨w0, hw0⟩)`. Establish `: ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ w : {w // len w ≤ B0}, ‖Φ eps w.1 []‖ ^ 2 < (a + jn) / 2` using `eventually_all.2 (fun w => (tendsto_order.1 (hE w.1 w.2)).2 _ (by linarith)) filter_upwards [this] with eps h`.

Establish `: Nonempty {w // len w ≤ B0}` using `⟨⟨w0, hw0⟩⟩`. Conclude with `lt_of_le_of_lt (ciSup_le fun w => (h w).le) (by linarith)`. Conclude with `ge_of_tendsto (h2.const_mul Bc) h1`.
-/
theorem epsilon_limit : Formalism.FourierDecayAlt.TA.EpsLimit := by
  intro E H _ _ W _ len k P Φ V w0 B0 Bc jn hw0 hb hE hV
  have h1 : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      (gram k V P).re ≤ Bc * wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2) := by
    have hall : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ p ∈ P, Φ eps w0 p = V p :=
      (Filter.eventually_all_finset P).2 hV
    filter_upwards [hall, self_mem_nhdsWithin] with eps h1 h2
    have h3 := hb eps h2
    have e : gram k (Φ eps w0) P = gram k V P := by
      unfold gram
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
      rw [h1 p hp, h1 p' hp']
    rwa [e] at h3
  have h2 : Tendsto (fun eps => wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 jn) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [(tendsto_order.1 (hE w0 hw0)).1 a ha] with eps h
      exact lt_of_lt_of_le h (le_ciSup (f := fun w : {w // len w ≤ B0} => ‖Φ eps w.1 []‖ ^ 2)
        (Set.finite_range _).bddAbove ⟨w0, hw0⟩)
    · have : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ w : {w // len w ≤ B0}, ‖Φ eps w.1 []‖ ^ 2 < (a + jn) / 2 :=
        eventually_all.2 (fun w => (tendsto_order.1 (hE w.1 w.2)).2 _ (by linarith))
      filter_upwards [this] with eps h
      have : Nonempty {w // len w ≤ B0} := ⟨⟨w0, hw0⟩⟩
      exact lt_of_le_of_lt (ciSup_le fun w => (h w).le) (by linarith)
  exact ge_of_tendsto (h2.const_mul Bc) h1

end Formalism.FourierDecayAlt.P
