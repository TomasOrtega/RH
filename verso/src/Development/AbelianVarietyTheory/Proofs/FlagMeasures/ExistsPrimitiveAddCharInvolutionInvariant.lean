import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

/- English proof (translation)
Break down `subsingleton_or_nontrivial B with hB | hB` into its components or cases. Use `⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `(AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero`. Set `T : B →+ B` to `AddMonoidHom.id B + c.toAddMonoidHom`. Establish `hT : ∀ u, T u = u + c u` using `fun u => rfl`.

Use `⟨ψ.compAddMonoidHom T, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha h`. Establish `hex : ∃ u, a * u + c (a * u) ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `h1` using `hne 1`. Establish `h2` using `hne ω`. Rewrite `h1` using `[mul_one]`. Rewrite `h2` using `[map_mul]`. Establish `h3 : a * (ω - c ω) = 0` using `by linear_combination h2 - c ω * h1`.

Conclude with `ha ((hω.mul_left_eq_zero).1 h3)`. Take `⟨u, hu⟩` from `hex`. Establish `hs : c (a * u + c (a * u)) = a * u + c (a * u)`. Rewrite using `[map_add, hc, add_comm]`. Take `⟨s', hs'⟩` from `(hfix _ hs hu).exists_right_inv`.

Establish `hcs : c s' = s'`. Establish `h4` using `congrArg c hs'`. Rewrite `h4` using `[map_mul, hs, map_one]`. Take the linear combination `s' * h4 - c s' * hs'`. Establish `h5 : T (a * (u * s')) = 1`.

Rewrite using `[hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']`. Expand and normalize the polynomial expressions, which then agree. Establish `h6` using `DFunLike.congr_fun h (u * s')`. Rewrite `h6` using `[AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5]`. Conclude with `hψ (by simpa using h6)`.

Introduce `u`. Simplify using `only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]`.
-/
theorem exists_isPrimitive_invol_invariant {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (ω : B) (hω : IsUnit (ω - c ω))
    (hfix : ∀ t, c t = t → t ≠ 0 → IsUnit t) :
    ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero
  let T : B →+ B := AddMonoidHom.id B + c.toAddMonoidHom
  have hT : ∀ u, T u = u + c u := fun u => rfl
  refine ⟨ψ.compAddMonoidHom T, ?_, ?_⟩
  · intro a ha h
    have hex : ∃ u, a * u + c (a * u) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := hne 1
      have h2 := hne ω
      rw [mul_one] at h1
      rw [map_mul] at h2
      have h3 : a * (ω - c ω) = 0 := by linear_combination h2 - c ω * h1
      exact ha ((hω.mul_left_eq_zero).1 h3)
    obtain ⟨u, hu⟩ := hex
    have hs : c (a * u + c (a * u)) = a * u + c (a * u) := by
      rw [map_add, hc, add_comm]
    obtain ⟨s', hs'⟩ := (hfix _ hs hu).exists_right_inv
    have hcs : c s' = s' := by
      have h4 := congrArg c hs'
      rw [map_mul, hs, map_one] at h4
      linear_combination s' * h4 - c s' * hs'
    have h5 : T (a * (u * s')) = 1 := by
      rw [hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']
      ring
    have h6 := DFunLike.congr_fun h (u * s')
    rw [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5] at h6
    exact hψ (by simpa using h6)
  · intro u
    simp only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]

end GlobalTheory.GramCount
