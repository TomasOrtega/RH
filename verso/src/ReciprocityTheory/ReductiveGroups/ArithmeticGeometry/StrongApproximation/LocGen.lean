import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SUEqClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement

namespace ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Use `haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨h01, h02, h12⟩` from `hcon`. Establish `hS : ∀ I J : Ideal K, I < J → Module.finrank k (I.restrictScalars k) < Module.finrank k (J.restrictScalars k)`.

Introduce `I J hIJ`. Apply `Submodule.finrank_lt_finrank_of_lt` to reduce the goal to its premises. Use `lt_of_le_of_ne (fun x hx => hIJ.le hx) ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hIJ.ne (Submodule.restrictScalars_injective k K K h)`.

Establish `a1 : m₀ < ⊤` using `lt_top_iff_ne_top.mpr h₀.ne_top`. Establish `a2 : m₀ ⊓ m₁ < m₀`. Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `h`. Conclude with `h01 (h₀.eq_of_le h₁.ne_top (inf_eq_left.mp h))`.

Establish `a3 : m₀ ⊓ m₁ ⊓ m₂ < m₀ ⊓ m₁`. Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `h`. Break down `(h₂.isPrime.inf_le).mp (inf_eq_left.mp h) with h' | h'` into its components or cases. Conclude with `h02 (h₀.eq_of_le h₂.ne_top h')`.

Conclude with `h12 (h₁.eq_of_le h₂.ne_top h')`. Establish `b1` using `hS _ _ a1`. Establish `b2` using `hS _ _ a2`. Establish `b3` using `hS _ _ a3`. Establish `htop : Module.finrank k ((⊤ : Ideal K).restrictScalars k) = 2`.

Rewrite using `[Submodule.restrictScalars_top, finrank_top]`. Conclude with `hrank`. Use linear arithmetic over natural numbers and integers.
-/
theorem max_ideals_le_two {k K : Type*} [Field k] [CommRing K] [Algebra k K]
    (hrank : Module.finrank k K = 2) (m₀ m₁ m₂ : Ideal K) (h₀ : m₀.IsMaximal) (h₁ : m₁.IsMaximal)
    (h₂ : m₂.IsMaximal) : m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂ := by
  classical
  haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)
  by_contra hcon
  push_neg at hcon
  obtain ⟨h01, h02, h12⟩ := hcon
  have hS : ∀ I J : Ideal K, I < J →
      Module.finrank k (I.restrictScalars k) < Module.finrank k (J.restrictScalars k) := by
    intro I J hIJ
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (fun x hx => hIJ.le hx) ?_
    intro h
    exact hIJ.ne (Submodule.restrictScalars_injective k K K h)
  have a1 : m₀ < ⊤ := lt_top_iff_ne_top.mpr h₀.ne_top
  have a2 : m₀ ⊓ m₁ < m₀ := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact h01 (h₀.eq_of_le h₁.ne_top (inf_eq_left.mp h))
  have a3 : m₀ ⊓ m₁ ⊓ m₂ < m₀ ⊓ m₁ := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    rcases (h₂.isPrime.inf_le).mp (inf_eq_left.mp h) with h' | h'
    · exact h02 (h₀.eq_of_le h₂.ne_top h')
    · exact h12 (h₁.eq_of_le h₂.ne_top h')
  have b1 := hS _ _ a1
  have b2 := hS _ _ a2
  have b3 := hS _ _ a3
  have htop : Module.finrank k ((⊤ : Ideal K).restrictScalars k) = 2 := by
    rw [Submodule.restrictScalars_top, finrank_top]
    exact hrank
  omega

/- English proof (translation)
Introduce `k K _ _ _ σ hσσ hfix hrank hred h2 N J hJ hdet e f hee hff hef`. Use `haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (R := k) (by omega)`. Use `haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)`. Establish `hfixU : ∀ x : K, σ.toRingHom x = x → x ≠ 0 → IsUnit x`. Introduce `x hx hx0`.

Take `⟨c, rfl⟩` from `(hfix _).mp hx`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx0 (map_zero _)`. Conclude with `(isUnit_iff_ne_zero.mpr hc).map (algebraMap k K)`.

Establish `h2i : (2 : K) * algebraMap k K 2⁻¹ = 1`. Rewrite using `[(map_ofNat (algebraMap k K) 2).symm, ← map_mul, mul_inv_cancel₀ h2, map_one]`. Establish `hex : ∃ x : K, σ x ≠ x`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`.

Establish `hsurj : Function.Surjective (Algebra.linearMap k K)` using `fun x => (hfix x).mp (hno x)`. Establish `h1` using `LinearMap.finrank_range_le (Algebra.linearMap k K)`. Rewrite `h1` using `[LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `hex`.

Establish `hσδ : σ.toRingHom (x - σ x) = -(x - σ x)` using `by show σ (x - σ x) = _`. Rewrite using `[map_sub, hσσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hδ0 : x - σ x ≠ 0` using `fun h => hx (sub_eq_zero.mp h).symm`. Establish `hsq : (x - σ x) * (x - σ x) ≠ 0`.

Introduce `h`. Conclude with `hδ0 (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact h⟩)`. Establish `hsqfix : σ.toRingHom ((x - σ x) * (x - σ x)) = (x - σ x) * (x - σ x)`. Rewrite using `[map_mul, hσδ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hδ : IsUnit (x - σ x)` using `isUnit_of_mul_isUnit_left (hfixU _ hsqfix hsq)`. Conclude with `SU_eq_closure hσσ hJ hee hff hef hfixU h2i hδ hσδ hdet (fun m₀ m₁ m₂ h₀ h₁ h₂ => max_ideals_le_two hrank m₀ m₁ m₂ h₀ h₁ h₂)`.
-/
theorem locGen : LocGenStatement := by
  intro k K _ _ _ σ hσσ hfix hrank hred h2 N J hJ hdet e f hee hff hef
  haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)
  have hfixU : ∀ x : K, σ.toRingHom x = x → x ≠ 0 → IsUnit x := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (hfix _).mp hx
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero _)
    exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap k K)
  have h2i : (2 : K) * algebraMap k K 2⁻¹ = 1 := by
    rw [(map_ofNat (algebraMap k K) 2).symm, ← map_mul, mul_inv_cancel₀ h2, map_one]
  have hex : ∃ x : K, σ x ≠ x := by
    by_contra hno
    push_neg at hno
    have hsurj : Function.Surjective (Algebra.linearMap k K) := fun x => (hfix x).mp (hno x)
    have h1 := LinearMap.finrank_range_le (Algebra.linearMap k K)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
    omega
  obtain ⟨x, hx⟩ := hex
  have hσδ : σ.toRingHom (x - σ x) = -(x - σ x) := by
    show σ (x - σ x) = _
    rw [map_sub, hσσ]
    ring
  have hδ0 : x - σ x ≠ 0 := fun h => hx (sub_eq_zero.mp h).symm
  have hsq : (x - σ x) * (x - σ x) ≠ 0 := by
    intro h
    exact hδ0 (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact h⟩)
  have hsqfix : σ.toRingHom ((x - σ x) * (x - σ x)) = (x - σ x) * (x - σ x) := by
    rw [map_mul, hσδ]
    ring
  have hδ : IsUnit (x - σ x) := isUnit_of_mul_isUnit_left (hfixU _ hsqfix hsq)
  exact SU_eq_closure hσσ hJ hee hff hef hfixU h2i hδ hσδ hdet
    (fun m₀ m₁ m₂ h₀ h₁ h₂ => max_ideals_le_two hrank m₀ m₁ m₂ h₀ h₁ h₂)

end ReciprocityTheory.ChartRestriction.G.SA
