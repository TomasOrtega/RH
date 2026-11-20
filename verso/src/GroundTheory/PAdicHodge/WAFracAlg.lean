import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WAFrac

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem galois_mem_den {R : Type*} [CommRing R] [IsDomain R] (g : R →+* R) {a b β γ T : R}
    (hgb : g b ≠ 0) (hrel : g a * b - a * g b = T * g b * b) (h : β * a = γ * b) :
    g β * a = (g γ - T * g β) * b := by
  have hg := congrArg g h
  rw [map_mul, map_mul] at hg
  refine mul_right_cancel₀ hgb ?_
  linear_combination b * hg - g β * hrel

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem galois_sub_of_mul_eq {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (gR : R →+* R) (gS : S →+* S) (hfg : ∀ x, gS (f x) = f (gR x)) {a b T : R} {u : S}
    (hb : f b ≠ 0) (hgb : gS (f b) ≠ 0) (hrel : gR a * b - a * gR b = T * gR b * b) (hu : u * f b = f a) :
    gS u - u = f T := by
  have h1 : gS u * gS (f b) = f (gR a) := by rw [← map_mul, hu, hfg]
  have h2 := congrArg f hrel
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, ← hfg, ← hfg] at h2
  refine mul_right_cancel₀ hb (mul_right_cancel₀ hgb ?_)
  linear_combination f b * h1 - gS (f b) * hu + h2 - f b * hfg a

end WAFrac

end GroundTheory.PAdicHodge
