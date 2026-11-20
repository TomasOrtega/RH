import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp ht`. Rewrite using `[a.as_sum, Finset.sum_mul, map_sum]`. Use `Ideal.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Establish `hd : IsWeightedHomogeneous (blockWeight ι) (monomial d (coeff d a) * s) (Finsupp.weight (blockWeight ι) d + c)` using `(isWeightedHomogeneous_monomial _ d _ rfl).mul hs`. Distinguish the cases in `hb : b = Finsupp.weight (blockWeight ι) d + c`.

Substitute `hb` using the available equality. Rewrite using `[hd.weightedHomogeneousComponent_same]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)`. Rewrite using `[hd.weightedHomogeneousComponent_ne b hb]`. Conclude with `Ideal.zero_mem _`.
-/
theorem weightedHomogeneousComponent_mem_span_of_isMultiHomog {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  rw [a.as_sum, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd : IsWeightedHomogeneous (blockWeight ι) (monomial d (coeff d a) * s)
      (Finsupp.weight (blockWeight ι) d + c) :=
    (isWeightedHomogeneous_monomial _ d _ rfl).mul hs
  by_cases hb : b = Finsupp.weight (blockWeight ι) d + c
  · subst hb
    rw [hd.weightedHomogeneousComponent_same]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [hd.weightedHomogeneousComponent_ne b hb]
    exact Ideal.zero_mem _

/- English proof (translation)
Introduce `f hf b`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hf`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b)) (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))`.
-/
theorem isMultiHomogIdeal_sup_span_of_form {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  intro f hf b
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b))
    (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))

/- English proof (translation)
Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe x`. Proceed by induction on `x using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `: ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞)` using `rfl`. Rewrite `h` using `[this]`. Conclude with `absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))`. Consider the case `coe k`.

Establish `h' : ((k + 1 : ℕ) : WithBot ℕ∞) < ((N + 1 : ℕ) : WithBot ℕ∞)`. Conclude with `h` after adjusting the coercions. Establish `h'' : k + 1 < N + 1` using `by exact_mod_cast h'`. Establish `: k < N` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem withBot_lt_of_add_one_lt {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h
      exact absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) < ((N + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h
      have h'' : k + 1 < N + 1 := by exact_mod_cast h'
      have : k < N := by omega
      exact_mod_cast this

/- English proof (translation)
Introduce `F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs`. Establish `: G.IsPrime` using `hGp`. Use `set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef`. Use `set c' : K → ℤ := fun k => (c k : ℤ) with hc'`. Establish `hnzd : ∀ y, s * y ∈ G → y ∈ G` using `fun y hy => (hGp.mem_or_mem hy).resolve_left hsG`.

Establish `hH : hilbFn J = diffStep c' (hilbFn G)`. Use function extensionality and compare the values at `m`. Conclude with `h2 F K ι G s c hG hs hnzd m`. Establish `hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs`. Take `⟨-, -, -, h4, h5⟩` from `h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'`.

Unfold `intNum`. Rewrite using `[h5, ← h4, hH]`. Establish `hJ : IsMultiHomogIdeal J` using `isMultiHomogIdeal_sup_span_of_form hG hs`. Establish `hle : G ≤ J` using `le_sup_left`. Establish `hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G)` using `mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)`.

Establish `hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G)` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle) hr (by`. Rewrite using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span rfl))`. Establish `hdimJ : ringKrullDim (MRing ι F ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Apply `withBot_lt_of_add_one_lt` to reduce the goal to its premises.

Establish `he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K` using `by omega`. Rewrite using `[he]`. Conclude with `lt_of_le_of_lt hsucc hdim`. Rewrite using `[hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]`.
-/
theorem CutByForm.proof (h1 : IntNumAssoc.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : MixedDiffLinear.Statement) : CutByForm.Statement.{u} := by
  intro F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs
  have : G.IsPrime := hGp
  set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef
  set c' : K → ℤ := fun k => (c k : ℤ) with hc'

  have hnzd : ∀ y, s * y ∈ G → y ∈ G := fun y hy => (hGp.mem_or_mem hy).resolve_left hsG
  have hH : hilbFn J = diffStep c' (hilbFn G) := by
    funext m
    exact h2 F K ι G s c hG hs hnzd m

  have hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs := by
    obtain ⟨-, -, -, h4, h5⟩ := h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'
    unfold intNum
    rw [h5, ← h4, hH]

  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hG hs

  have hle : G ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hdimJ : ringKrullDim (MRing ι F ⧸ J) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_lt_of_add_one_lt
    have he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K := by omega
    rw [he]
    exact lt_of_le_of_lt hsucc hdim

  rw [hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
