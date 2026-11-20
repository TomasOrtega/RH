import Mathlib
import Formalism.PeriodIntegrals.RTTIndependence

namespace PI.QmLemDWork

/- English proof (translation)
Introduce `A _ _ DD h0 hstep A' hmul hfrac n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `D hD _`. Rewrite `hD` using `[h0]`.

Conclude with `hD`. Consider the case `succ n ih`. Introduce `D hD hkill`. Establish `hcomm : ∀ a ∈ A', ∀ b : A, D (a * b) = a * D b`. Introduce `a ha b`.

Take `⟨D', hD', hD'eq⟩` from `hstep n D hD a`. Establish `hz : D' = 0` using `ih D' hD' (fun x hx => by`. Rewrite using `[hD'eq, hkill _ (hmul a ha x hx), hkill x hx, mul_zero, sub_zero])`. Use `hD'eq b` as an intermediate fact. Rewrite `this` using `[hz, AddMonoidHom.zero_apply]`.

Conclude with `(sub_eq_zero.mp this.symm)`. Use extensionality with `b`. Take `⟨a₁, ha₁, a₂, ha₂, hne, hb⟩` from `hfrac b`. Establish `h1 : a₂ * D b = 0`. Rewrite using `[← hcomm a₂ ha₂ b, hb, hkill a₁ ha₁]`.

Rewrite using `[AddMonoidHom.zero_apply]`. Conclude with `(mul_eq_zero.mp h1).resolve_left hne`.
-/
theorem main : PI.LemmaD := by
  intro A _ _ DD h0 hstep A' hmul hfrac n
  induction n with
  | zero =>
    intro D hD _
    rw [h0] at hD
    exact hD
  | succ n ih =>
    intro D hD hkill
    have hcomm : ∀ a ∈ A', ∀ b : A, D (a * b) = a * D b := by
      intro a ha b
      obtain ⟨D', hD', hD'eq⟩ := hstep n D hD a
      have hz : D' = 0 := ih D' hD' (fun x hx => by
        rw [hD'eq, hkill _ (hmul a ha x hx), hkill x hx, mul_zero, sub_zero])
      have := hD'eq b
      rw [hz, AddMonoidHom.zero_apply] at this
      exact (sub_eq_zero.mp this.symm)
    ext b
    obtain ⟨a₁, ha₁, a₂, ha₂, hne, hb⟩ := hfrac b
    have h1 : a₂ * D b = 0 := by
      rw [← hcomm a₂ ha₂ b, hb, hkill a₁ ha₁]
    rw [AddMonoidHom.zero_apply]
    exact (mul_eq_zero.mp h1).resolve_left hne

end PI.QmLemDWork
