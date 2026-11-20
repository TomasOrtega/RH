import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePtRight

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]

end Ext

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Take `⟨gs, h0, hs, hl⟩` from `H`. Establish `key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro hn`.

Rewrite using `[pow_zero]`. Conclude with `h0.1`. Consider the case `succ n ih`. Introduce `hn`. Establish `e` using `(hs ⟨n, by omega⟩).1`.

Rewrite using `[pow_succ, ← ih (by omega)]`. Conclude with `e`. Rewrite using `[← hl]`. Conclude with `key k (Nat.lt_succ_self k)`.
-/
theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

/- English proof (translation)
Introduce `h` and use `by haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩ have h2 : (2 : FractionRing ℤ_[2]) ≠ 0 := two_ne_zero have e := (RelModel.fe_zeroUq_iff ℤ_[2] (IsLocalRing.maximalIdeal ℤ_[2]) (FractionRing ℤ_[2]) 1 (Units.mk0 2 h2)).1 (h ℤ_[2] (cdvr_padicInt 2) _ _ _ (RelModel.zeroUq ℤ_[2] _ (Un …`.
-/
theorem not_allPre_fe : ¬ AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => U.FE (FractionRing V) 2 := fun h => by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : FractionRing ℤ_[2]) ≠ 0 := two_ne_zero
  have e := (RelModel.fe_zeroUq_iff ℤ_[2] (IsLocalRing.maximalIdeal ℤ_[2]) (FractionRing ℤ_[2]) 1
    (Units.mk0 2 h2)).1 (h ℤ_[2] (cdvr_padicInt 2) _ _ _ (RelModel.zeroUq ℤ_[2] _ (Units.mk0 2 h2)))
  have e' : (2 : FractionRing ℤ_[2]) = 1 := by simpa using congrArg Units.val e
  norm_num at e'

end GlobalTheory.UU.RelTests
end
