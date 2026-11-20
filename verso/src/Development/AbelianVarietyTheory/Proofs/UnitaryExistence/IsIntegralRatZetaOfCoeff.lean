import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: zeta 0 = 1` using `by simp [zeta]`. Rewrite using `[this]`. Conclude with `isIntegral_one`. Establish `h` using `Complex.isPrimitiveRoot_exp n hn.ne'`.

Conclude with `(h.isIntegral hn).tower_top`.
-/
theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

/- English proof (translation)
Introduce `E _ _ _ H l s hs`. Set `b` to `Module.finBasis ℚ E`. Set `S : Set ℂ` to `(s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪ {zeta l.M', H.rt0, zeta l.A}`. Establish `hfin : S.Finite` using `((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)`. Use `haveI : Finite S := hfin.to_subtype`.

Establish `hint : ∀ x ∈ S, IsIntegral ℚ x`. Introduce and unpack `x ((hx | ⟨p, rfl⟩) | hx)`. Conclude with `(hs x hx).isIntegral`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom`. Break down `hx with rfl | rfl | rfl` into its components or cases.

Conclude with `isIntegral_rat_zeta_of_coeff _`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[H.sqrt_neg_disc_sq]`. Conclude with `(isIntegral_natCast _).neg`. Conclude with `isIntegral_rat_zeta_of_coeff _`.

Establish `hsub : S ⊆ IntermediateField.adjoin ℚ S` using `IntermediateField.subset_adjoin _ _`. Use `⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `τ a`. Rewrite using `[← b.sum_repr a, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_rat_smul]`. Conclude with `IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))`. Conclude with `hsub (Or.inr (by simp))`. Use `IntermediateField.adjoin.mono _ _ _ ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `Or.inr (Or.inr hx)`. Introduce `z hz`. Conclude with `hsub (Or.inl (Or.inl hz))`.
-/
theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a
    rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

end GlobalTheory
