import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

/- English proof (translation)
Introduce `S H H' _ _ f hf N M hN hM hs hiso s`. Take `⟨U, hU, t, ht⟩` from `hs s`. Use `⟨U, hU, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `LBIso.symm hiso`. Establish `hw'` using `(isGen_iff w).1 hw`.

Take `⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme, n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left` from `⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left` using `congrArg (fun q => q.left) (GrpObj.inv_hom f)`.

Set `ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left)` to `![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]`. Take `⟨c₂, h₂⟩` from `gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by fin_cases k`. Use `show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left`. Rewrite using `[← Category.assoc n, hn, Category.assoc, Category.assoc, hi]`. Use `show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι`.

Rewrite using `[hn])) t ht`. Conclude with `exists_down hw' hN hM (φ' := ψ) c₂ h₂`.
-/
theorem sym_of_lbIso_pull_hom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f →
    ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  intro S H H' _ _ f hf N M hN hM hs hiso s
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, ?_⟩
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme,
      n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left :=
    ⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  have hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom f)
  let ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left) :=
    ![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by
    fin_cases k
    · show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left =
        n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc, hi]
    · show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι
      rw [hn])) t ht
  exact exists_down hw' hN hM (φ' := ψ) c₂ h₂

end GlobalTheory
