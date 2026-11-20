import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Introduce `E _ _ _ r X hne`. Take `⟨y0, hy0⟩` from `hne`. Use `haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by`. Use `congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩` as an intermediate fact. Simplify using `at this⟩⟩`.

Use `haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨ha, hb⟩` from `hcon`. Take `⟨F, hF, hFa⟩` from `a.2`.

Take `⟨G, hG, hGb⟩` from `b.2`. Establish `ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `ha (Subtype.ext (funext h))`.

Take `⟨y, hy⟩` from `ha'`. Establish `hfg : ∀ w ∈ X.dom, F w * G w = 0`. Introduce `w hw`. Use `congrFun (congrArg Subtype.val hab) ⟨w, hw⟩` as an intermediate fact. Rewrite using `[← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]`.

Simplify using `using this`. Establish `hFy : F y.1 ≠ 0` using `by rw [← hFa y]; exact hy`. Establish `key` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy`. Apply `hb` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `z`. Rewrite using `[hGb z]`. Simplify using `using key z.1 z.2⟩`. Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
