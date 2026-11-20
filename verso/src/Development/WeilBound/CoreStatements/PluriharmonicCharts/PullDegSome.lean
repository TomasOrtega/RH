import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def κ₁ (k₀ : K) (k : K) : Option K := if k = k₀ then none else some k

/- English proof (translation)
The claim follows from `if_pos rfl`.
-/
theorem κ₁_self (k₀ : K) : κ₁ k₀ k₀ = none := if_pos rfl

/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem κ₁_ne {k₀ k : K} (h : k ≠ k₀) : κ₁ k₀ k = some k := if_neg h

/- English proof (translation)
Introduce `a b h`. Unfold `κ₁ at h`. Apply the tactic sequence `split_ifs at h with ha hb hb <;> first`. Consider the case `exact ha.trans hb.symm`. Consider the case `(cases h; rfl)`.

Consider the case `cases h`. Consider the case `exact Option.some_injective _ h`.
-/
theorem κ₁_inj (k₀ : K) : Function.Injective (κ₁ k₀) := by
  intro a b h
  unfold κ₁ at h
  split_ifs at h with ha hb hb <;>
    first
    | exact ha.trans hb.symm
    | (cases h; rfl)
    | cases h
    | exact Option.some_injective _ h

/- English proof (translation)
Establish `h3 : ∀ p : (k : K) × ι k, (v₁ k₀ p).fst = κ₁ k₀ p.fst` using `fun p => by`. Unfold `v₁ κ₁`. Apply the tactic sequence `split_ifs <;> rfl`. Use `⟨κ₁_inj k₀, ?_, h3, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, x⟩ ⟨b, y⟩ h`.

Establish `hfst : κ₁ k₀ a = κ₁ k₀ b`. Establish `e` using `congrArg Sigma.fst h`. Rewrite `e` using `[h3, h3]`. Then use the resulting hypothesis. Establish `hab : a = b` using `κ₁_inj k₀ hfst`. Substitute `hab` using the available equality.

Unfold `v₁ at h`. Use `split_ifs at h with ha`. Establish `h2` using `(Sigma.mk.inj_iff.mp h).2`. Take `rfl` from `eq_of_heq ((cast_heq _ x).symm.trans (h2.trans (cast_heq _ y)))`. Both sides reduce to the same expression.

Establish `h2` using `(Sigma.mk.inj_iff.mp h).2`. Take `rfl` from `eq_of_heq h2`. Both sides reduce to the same expression. Introduce and unpack `⟨o, x⟩ ⟨j, hj⟩`. Consider the cases of `o with`.

Consider the case `none`. Use `⟨⟨k₀, x⟩, ?_⟩` and prove the remaining obligations. Unfold `v₁`. Rewrite using `[dif_pos rfl]`. Both sides reduce to the same expression.

Consider the case `some k`. Establish `hk : k ≠ k₀`. Introduce `hk`. Unfold `κ₁ at hj`. Apply the tactic sequence `split_ifs at hj with h1 <;> first`.

Consider the case `(cases hj; exact h1 hk)`. Consider the case `cases hj`. Consider the case `exact h1 ((Option.some_injective _ hj).trans hk)`. Use `⟨⟨k, x⟩, ?_⟩` and prove the remaining obligations. Unfold `v₁`.

Rewrite using `[dif_neg hk]`.
-/
theorem isBlockMap_v₁ (k₀ : K) :
    IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) (κ₁ k₀) (v₁ k₀) := by
  have h3 : ∀ p : (k : K) × ι k, (v₁ k₀ p).fst = κ₁ k₀ p.fst := fun p => by
    unfold v₁ κ₁
    split_ifs <;> rfl
  refine ⟨κ₁_inj k₀, ?_, h3, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hfst : κ₁ k₀ a = κ₁ k₀ b := by
      have e := congrArg Sigma.fst h
      rwa [h3, h3] at e
    have hab : a = b := κ₁_inj k₀ hfst
    subst hab
    unfold v₁ at h
    split_ifs at h with ha
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq ((cast_heq _ x).symm.trans (h2.trans (cast_heq _ y)))
      rfl
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq h2
      rfl
  · rintro ⟨o, x⟩ ⟨j, hj⟩
    cases o with
    | none =>
      refine ⟨⟨k₀, x⟩, ?_⟩
      unfold v₁
      rw [dif_pos rfl]
      rfl
    | some k =>
      have hk : k ≠ k₀ := by
        intro hk
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      refine ⟨⟨k, x⟩, ?_⟩
      unfold v₁
      rw [dif_neg hk]

/- English proof (translation)
Unfold `pullDeg`. Consider the cases of `o with`. Consider the case `none`. Establish `hn : ¬∃ a : K, some a = (none : Option K)`. Introduce and unpack `⟨a, ha⟩`.

Consider the cases of `ha`. Rewrite using `[Function.extend_apply' _ _ _ hn]`. Both sides reduce to the same expression. Consider the case `some k`. Conclude with `(Option.some_injective K).extend_apply xi 0 k`.
-/
theorem pullDeg_some (xi : K → ℤ) (o : Option K) : pullDeg (some : K → Option K) xi o = o.elim 0 xi := by
  unfold pullDeg
  cases o with
  | none =>
    have hn : ¬∃ a : K, some a = (none : Option K) := by
      rintro ⟨a, ha⟩
      cases ha
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  | some k =>
    exact (Option.some_injective K).extend_apply xi 0 k

/- English proof (translation)
Unfold `pullDeg`. Consider the cases of `o with`. Consider the case `none`. Establish `e` using `(κ₁_inj k₀).extend_apply xi 0 k₀`. Rewrite `e` using `[κ₁_self]`.

Conclude with `e`. Consider the case `some k`. Distinguish the cases in `hk : k = k₀`. Establish `hn : ¬∃ j : K, κ₁ k₀ j = some k`. Introduce and unpack `⟨j, hj⟩`.

Unfold `κ₁ at hj`. Apply the tactic sequence `split_ifs at hj with h1 <;> first`. Consider the case `(cases hj; exact h1 hk)`. Consider the case `cases hj`. Consider the case `exact h1 ((Option.some_injective _ hj).trans hk)`.

Rewrite using `[Function.extend_apply' _ _ _ hn]`. Simplify using `[hk]`. Establish `e` using `(κ₁_inj k₀).extend_apply xi 0 k`. Rewrite `e` using `[κ₁_ne hk]`. Rewrite using `[e]`.

Simplify using `[hk]`.
-/
theorem pullDeg_κ₁ (k₀ : K) (xi : K → ℤ) (o : Option K) :
    pullDeg (κ₁ k₀) xi o = o.elim (xi k₀) fun k => if k = k₀ then 0 else xi k := by
  unfold pullDeg
  cases o with
  | none =>
    have e := (κ₁_inj k₀).extend_apply xi 0 k₀
    rw [κ₁_self] at e
    exact e
  | some k =>
    by_cases hk : k = k₀
    · have hn : ¬∃ j : K, κ₁ k₀ j = some k := by
        rintro ⟨j, hj⟩
        unfold κ₁ at hj
        split_ifs at hj with h1 <;>
          first
          | (cases hj; exact h1 hk)
          | cases hj
          | exact h1 ((Option.some_injective _ hj).trans hk)
      rw [Function.extend_apply' _ _ _ hn]
      simp [hk]
    · have e := (κ₁_inj k₀).extend_apply xi 0 k
      rw [κ₁_ne hk] at e
      rw [e]
      simp [hk]

end PositivityTheory.Xgp.c_algsq
