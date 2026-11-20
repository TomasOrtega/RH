import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `A _ _ Lr cs g u₀`. Establish `hval` using `@valAt'_rules`. Establish `hholprod` using `@holFamily_lift hval`. Establish `hT` using `@cube_trivialisation_on_uniformising_space hval hholprod`. Establish `hdbl` using `@exists_doubling_solution_pi`.

Establish `hdblu` using `@eventually_eq_zero_of_isBigO_cube_of_doubling`. Establish `hlock` using `@LocalCube.exists_third_difference hdbl hdblu`. Establish `hface` using `@cube_section_faces_and_doubling`. Establish `hloc` using `@exists_localFrame_compatible_cube @hface hlock`. Establish `hglob` using `@CubeFrame.exists_global_frame`.

Establish `hfac` using `@automorphyFactor_exp_linear_of_cube`. Establish `hnf` using `@appellHumbert_normal_form_of_linear_exponent`. Take `⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩` from `hT A _ Lr.L g u₀ Lr.isLB cs.t cs.isGen _ _ rfl rfl`. Take `⟨fr, κ, hfr, hκ⟩` from `hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4)`. Take `⟨a, B, ha, hab, hfa⟩` from `hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4 fr κ hfr hκ`.

Take `⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩` from `hnf g u₀.Λ u₀.discrete u₀.full a B ha hab`. Take `⟨f1, f2, f3⟩` from `hfr`. Use `⟨{ ex := u₀.ex, ex_add := u₀.ex_add, ex_onto := u₀.ex_onto, Λ := u₀.Λ, ker := u₀.ker, discrete := u₀.discrete, full := u₀.full, hol := u₀.hol, fr := fun i z => fr i z * Complex.exp (Q z), fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ }, Hm, χ, …` and prove the remaining obligations. Use `f1 i` as an intermediate fact. Rewrite `this` using `[Set.inter_univ]`.

Conclude with `this.mul hQ.cexp.differentiableOn`. Conclude with `mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)`. Use `f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial` as an intermediate fact. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `l i z hz show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))`. Rewrite using `[← hQn l z, hfa l i z hz, Complex.exp_sub]`. Use `Complex.exp_ne_zero (Q (z + l))` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_appellHumbert_frame_of_cubical :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  intro A _ _ Lr cs g u₀
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hT := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hT A _ Lr.L g u₀ Lr.isLB cs.t cs.isGen _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u₀.Λ u₀.discrete u₀.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u₀.ex, ex_add := u₀.ex_add, ex_onto := u₀.ex_onto, Λ := u₀.Λ, ker := u₀.ker,
            discrete := u₀.discrete, full := u₀.full, hol := u₀.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory.CompanionTheory.Ar
