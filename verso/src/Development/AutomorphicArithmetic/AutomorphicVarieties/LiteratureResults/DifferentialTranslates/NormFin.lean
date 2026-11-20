import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open UpperTheory.V.Lit.Dr

/- English proof (translation)
Take `⟨m, hmU, hmax⟩` from `hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn`. Establish `hle : ∀ u ∈ U, φ u ≤ 1` using `fun u hu => by`. Establish `h : φ (u * m) ≤ φ m` using `hmax (U.mul_mem hu hmU)`. Rewrite `h` using `[hm]`. Use `hp m` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Introduce `u hu`. Establish `h1 : φ 1 = 1`. Establish `h` using `hm 1 1`. Rewrite `h` using `[mul_one]`.

Use `hp 1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `hm u u⁻¹`. Rewrite `h2` using `[mul_inv_cancel, h1]`. Establish `h3` using `hle u hu`.

Establish `h4` using `hle _ (U.inv_mem hu)`. Establish `h5` using `hp u`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G → ℝ) (hc : Continuous φ) (hp : ∀ g, 0 < φ g) (hm : ∀ g h, φ (g * h) = φ g * φ h) :
    ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [hm] at h
    have := hp m
    nlinarith
  intro u hu
  have h1 : φ 1 = 1 := by
    have h := hm 1 1
    rw [mul_one] at h
    have := hp 1
    nlinarith
  have h2 := hm u u⁻¹
  rw [mul_inv_cancel, h1] at h2
  have h3 := hle u hu
  have h4 := hle _ (U.inv_mem hu)
  have h5 := hp u
  nlinarith

open NumberField Matrix GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CuspRep in
/- English proof (translation)
Introduce `E _ _ a U hU`. Set `φ : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) → ℝ` to `fun g => finiteModule (ofFinite (K := E) (GeneralLinearGroup.det g))`. Establish `hc : Continuous φ` using `continuous_finiteModule.comp (continuous_ofFinite.comp GeneralLinearGroup.continuous_det)`. Establish `hp : ∀ g, 0 < φ g` using `fun g => finiteModule_pos _`. Establish `hm : ∀ g h, φ (g * h) = φ g * φ h` using `fun g h => by`.

Simplify using `only [φ, map_mul, finiteModule_mul]`. Establish `h1` using `one_of_compact U hU φ hc hp hm`. Establish `hγ : ∀ γ : GL (Fin a) E, φ (GeneralLinearGroup.map (algebraMap E _) γ) = |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)|⁻¹` using `fun γ => by`. Establish `e : φ (GeneralLinearGroup.map (algebraMap E _) γ) = finiteModule (IdeleGroup.diagonal E (GeneralLinearGroup.det γ))`. Establish `hd : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ)) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) = algebraMap E _ γ.val.det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `h2 : ((ofFinite (K` using `E) (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ))).val).2 = algebraMap E _ γ.val.det := (congrArg Units.val (toFinite_ofFinite _)).trans hd`. Simplify using `only [φ, finiteModule, h2]`. Both sides reduce to the same expression.

Rewrite using `[e, finiteModule_diagonal, FinitePlace.prod_eq_inv_abs_norm (GeneralLinearGroup.det γ).ne_zero]`. Simplify using the standard rewrite rules. Use `⟨Quotient.lift φ fun g h hgh => ?_, fun s => ?_, fun γ s => ?_⟩` and prove the remaining obligations. Establish `h2` using `h1 _ (QuotientGroup.leftRel_apply.1 hgh)`. Establish `h3` using `hm g (g⁻¹ * h)`.

Rewrite `h3` using `[mul_inv_cancel_left, h2, mul_one]`. Conclude with `h3.symm`. Proceed by induction on `s using QuotientGroup.induction_on with`. Consider the case `H g => exact hp g`. Proceed by induction on `s using QuotientGroup.induction_on with`.

Consider the case `H g => exact (hm _ g).trans (by rw [hγ]; rfl)`.
-/
theorem UpperTheory.V.Lit.Dr.normFin :
    NormFin := by
  intro E _ _ a U hU
  let φ : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) → ℝ :=
    fun g => finiteModule (ofFinite (K := E) (GeneralLinearGroup.det g))
  have hc : Continuous φ :=
    continuous_finiteModule.comp (continuous_ofFinite.comp GeneralLinearGroup.continuous_det)
  have hp : ∀ g, 0 < φ g := fun g => finiteModule_pos _
  have hm : ∀ g h, φ (g * h) = φ g * φ h := fun g h => by
    simp only [φ, map_mul, finiteModule_mul]
  have h1 := one_of_compact U hU φ hc hp hm
  have hγ : ∀ γ : GL (Fin a) E, φ (GeneralLinearGroup.map (algebraMap E _) γ) =
      |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)|⁻¹ := fun γ => by
    have e : φ (GeneralLinearGroup.map (algebraMap E _) γ) =
        finiteModule (IdeleGroup.diagonal E (GeneralLinearGroup.det γ)) := by
      have hd : ((GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ)) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) =
          algebraMap E _ γ.val.det := by
        rw [RingHom.map_det]; rfl
      have h2 : ((ofFinite (K := E) (GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ))).val).2 = algebraMap E _ γ.val.det :=
        (congrArg Units.val (toFinite_ofFinite _)).trans hd
      simp only [φ, finiteModule, h2]
      rfl
    rw [e, finiteModule_diagonal, FinitePlace.prod_eq_inv_abs_norm (GeneralLinearGroup.det γ).ne_zero]
    simp
  refine ⟨Quotient.lift φ fun g h hgh => ?_, fun s => ?_, fun γ s => ?_⟩
  · have h2 := h1 _ (QuotientGroup.leftRel_apply.1 hgh)
    have h3 := hm g (g⁻¹ * h)
    rw [mul_inv_cancel_left, h2, mul_one] at h3
    exact h3.symm
  · induction s using QuotientGroup.induction_on with
    | H g => exact hp g
  · induction s using QuotientGroup.induction_on with
    | H g => exact (hm _ g).trans (by rw [hγ]; rfl)
