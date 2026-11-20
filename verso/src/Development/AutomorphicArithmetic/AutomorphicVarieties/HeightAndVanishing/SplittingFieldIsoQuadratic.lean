import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
/- English proof (translation)
Use `set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf`. Establish `hsK : (f.map (algebraMap ℚ K)).Splits`. Establish `hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ))`. Establish `hpK : (p : K) = -(δ ^ 2)` using `by rw [hδ]; ring`. Rewrite using `[hf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_natCast, hpK]`.

Simplify using `only [map_neg, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac]`. Conclude with `(Splits.X_add_C _).mul (Splits.X_add_C _)`. Set `φ` to `IsSplittingField.lift L f hsK`.

Establish `hinj : Function.Injective φ` using `φ.toRingHom.injective`. Establish `hLK : Module.finrank ℚ L ≤ 2` using `hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj`. Establish `hL1 : Module.finrank ℚ L ≠ 1`. Introduce `h1`. Establish `hbt` using `Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1`.

Establish `hsL` using `IsSplittingField.splits L f`. Establish `hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0`. Rewrite using `[Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]`. Evaluate the numerical expressions. Take `⟨r, hr⟩` from `hsL.exists_eval_eq_zero hdeg`.

Establish `hrm : r ∈ (⊥ : Subalgebra ℚ L)` using `hbt ▸ Algebra.mem_top`. Take `⟨q, rfl⟩` from `Algebra.mem_bot.mp hrm`. Establish `hq : algebraMap ℚ L (q ^ 2 + p) = 0`. Simplify `hr` using `[hf, Polynomial.eval_map]`. Establish `hq0 : q ^ 2 + (p : ℚ) = 0` using `(algebraMap ℚ L).injective (by rw [hq, map_zero])`.

Establish `hpq : (0 : ℚ) < q ^ 2 + p`. Establish `: (0 : ℚ) < p` using `by exact_mod_cast hp`. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : 0 < Module.finrank ℚ L` using `Module.finrank_pos`.

Establish `h2 : Module.finrank ℚ L = 2` using `by omega`. Establish `hsurj : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap) (h2.trans hK.symm)).1 hinj`. Conclude with `⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩`.
-/
private theorem splitting_field_iso_quadratic (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  classical
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hsK : (f.map (algebraMap ℚ K)).Splits := by
    have hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ)) := by
      have hpK : (p : K) = -(δ ^ 2) := by rw [hδ]; ring
      rw [hf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        map_natCast, hpK]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Splits.X_add_C _).mul (Splits.X_add_C _)
  let φ := IsSplittingField.lift L f hsK
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hLK : Module.finrank ℚ L ≤ 2 :=
    hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hL1 : Module.finrank ℚ L ≠ 1 := by
    intro h1
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1
    have hsL := IsSplittingField.splits L f
    have hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
      rw [Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]
      norm_num
    obtain ⟨r, hr⟩ := hsL.exists_eval_eq_zero hdeg
    have hrm : r ∈ (⊥ : Subalgebra ℚ L) := hbt ▸ Algebra.mem_top
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hrm
    have hq : algebraMap ℚ L (q ^ 2 + p) = 0 := by
      simpa [hf, Polynomial.eval_map] using hr
    have hq0 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ L).injective (by rw [hq, map_zero])
    have hpq : (0 : ℚ) < q ^ 2 + p := by
      have : (0 : ℚ) < p := by exact_mod_cast hp
      positivity
    linarith
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have h2 : Module.finrank ℚ L = 2 := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (h2.trans hK.symm)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/- English proof (translation)
Introduce `p hp h3`. Take `⟨K, _, _, hK2, hd⟩` from `KStar.Consta.exists_quadField hp h3`. Take `⟨⟨δ, hδ⟩, -⟩` from `KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd`. Use `haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by`. Establish `h` using `Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))`.

Establish `h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))`. Use `h` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`. Conclude with `h'`. Take `⟨e⟩` from `splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)`.

Establish `hfr : Module.finrank ℚ (Kstar p) = 2` using `e.toLinearEquiv.finrank_eq.trans hK2`. Establish `hdisc : discr (Kstar p) = -(p : ℤ)`. Rewrite using `[NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]`. Take `⟨hs, htc⟩` from `KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc`. Conclude with `⟨hdisc, htc, hfr, hs⟩`.
-/
theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
      exact Subsingleton.elim _ _
    exact h'
  obtain ⟨e⟩ := splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
