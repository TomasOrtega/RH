import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

/- English proof (translation)
Establish `hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)`. Establish `he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) = fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)`. Use function extensionality and compare the values at `g`. Simplify using `[chiU, map_inv]`. Rewrite using `[he]`.

Conclude with `(D.nd.chi_cont i 1).comp continuous_inv`. Use `show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g`. Conclude with `hχ.smul hρ`.
-/
theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

/- English proof (translation)
Unfold `Br.loc Br.locM Br.locO mapM`. Simplify using `only [MonoidHom.coe_comp]`. Use `Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)` and prove the remaining obligations. Use `first`. Consider the case `exact continuous_id.matrix_map continuous_subtype_val`.

Consider the case `exact continuous_id.matrix_map continuous_induced_dom`. Conclude with `continuous_id.matrix_map (D.nbr i w hw).eO_cont`. Conclude with `continuous_subtype_val`. Use `first`. Consider the case `exact (D.nbr i w hw).e_symm_cont`.

Consider the case `exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont`.
-/
theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
      | exact continuous_id.matrix_map continuous_induced_dom
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont
      | exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont

/- English proof (translation)
Introduce `v`. Establish `hL` using `loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)`. Establish `h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v` using `hL.matrix_mulVec continuous_const`. Use `h2.congr fun g => ?_` and prove the remaining obligations. Use `first`.

Consider the case `rfl`. Consider the case `simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]`.
-/
theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl
    | simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]

end Formalism.MainNotions.N.KOrb

end
