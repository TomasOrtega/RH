import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FinConv

noncomputable section

open NumberField GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC

namespace GlobalTheory.CompanionTheory.FamClP

section Generic

variable {H : Type} [Group H]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_rStab' {u : H → ℂ} {r : H} : r ∈ rStab u ↔ ∀ x, u (x * r) = u x := Iff.rfl

/- English proof (translation)
Simplify using `[hint]`.
-/
theorem hint_zero (K : Subgroup H) : hint K (fun _ => (0 : ℂ)) = 0 := by
  simp [hint]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[mem_rStab', mem_rStab']`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Simplify `h (k⁻¹ * x)` using `[mul_assoc]`.

Introduce `h x`. Simplify `h (k * x)` using `[mul_assoc]`.
-/
theorem rStab_left (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext r
  rw [mem_rStab', mem_rStab']
  constructor
  · intro h x
    simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x
    simpa [mul_assoc] using h (k * x)

/- English proof (translation)
Unfold `hint`. Rewrite using `[rStab_left]`. Use `congr 1`. Use `Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)))` and prove the remaining obligations. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Establish `hq : (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)) q = ((k * q.out : H) : H ⧸ (rStab u ⊓ K))` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[hq]`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * q.out)`. Rewrite using `[hh]`.

Conclude with `(h.2.1 _).symm`.
-/
theorem hint_left (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  unfold hint
  rw [rStab_left]
  congr 1
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)))
  refine finsum_congr fun q => ?_
  have hq : (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)) q =
      ((k * q.out : H) : H ⧸ (rStab u ⊓ K)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * q.out)
  rw [hh]
  exact (h.2.1 _).symm

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[mem_rStab']`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hr`.

Use `h 1` as an intermediate fact. Simplify using `[Set.indicator, hr, one_mem] at this`. Introduce `hr x`. Distinguish the cases in `hx : x ∈ K`. Establish `hxr : x * r ∈ K` using `mul_mem hx hr`.

Simplify using `[Set.indicator, hx, hxr]`. Establish `hxr : x * r ∉ K` using `fun h => hx (by simpa using mul_mem h (inv_mem hr))`. Simplify using `[Set.indicator, hx, hxr]`.
-/
theorem rStab_ind (K : Subgroup H) : rStab ((K : Set H).indicator (1 : H → ℂ)) = K := by
  ext r
  rw [mem_rStab']
  constructor
  · intro h
    by_contra hr
    have := h 1
    simp [Set.indicator, hr, one_mem] at this
  · intro hr x
    by_cases hx : x ∈ K
    · have hxr : x * r ∈ K := mul_mem hx hr
      simp [Set.indicator, hx, hxr]
    · have hxr : x * r ∉ K := fun h => hx (by simpa using mul_mem h (inv_mem hr))
      simp [Set.indicator, hx, hxr]

/- English proof (translation)
Unfold `hint`. Rewrite using `[rStab_ind, inf_idem, Subgroup.relIndex_self]`. Rewrite using `[finsum_eq_single _ ((1 : H) : H ⧸ K)]`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul K (1 : H)`. Establish `hm : (((1 : H) : H ⧸ K)).out ∈ K`.

Rewrite using `[hh]`. Simplify using `using h.2`. Simplify using `[Set.indicator, hm]`. Introduce `q hq`. Establish `hn : q.out ∉ K`.

Introduce `hm`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `QuotientGroup.eq.2 (by simpa using inv_mem hm)`. Simplify using `[Set.indicator, hn]`.
-/
theorem hint_ind (K : Subgroup H) : hint K ((K : Set H).indicator (1 : H → ℂ)) = 1 := by
  unfold hint
  rw [rStab_ind, inf_idem, Subgroup.relIndex_self]
  rw [finsum_eq_single _ ((1 : H) : H ⧸ K)]
  · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (1 : H)
    have hm : (((1 : H) : H ⧸ K)).out ∈ K := by
      rw [hh]
      simpa using h.2
    simp [Set.indicator, hm]
  · intro q hq
    have hn : q.out ∉ K := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using inv_mem hm)
    simp [Set.indicator, hn]

variable [TopologicalSpace H]

variable [IsTopologicalGroup H]

end Generic

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

end Fam

end GlobalTheory.CompanionTheory.FamClP

end
