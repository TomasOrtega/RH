import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolFibreIsogAny
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlatStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `inferInstanceAs (IsMonHom (1 : A ⟶ A))`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))`.
-/
theorem qi_isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (1 : A ⟶ A))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

/- English proof (translation)
Introduce `C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB h₁ h₂ hp`. Establish `hm : IsMonHom l` using `hp.1`. Establish `fib` using `h1 C v R hv A B P l g hA hB hgA hgB h₁ h₂ hp`. Take `⟨hf, hs⟩` from `GlobalTheory.T.finite_of_finite_fibres R A B l hA hB hm fun Ω _ _ s => ⟨(fib Ω s).1, (fib Ω s).2.2⟩`. Use `hA.comm` as an intermediate fact.

Use `hA.smooth` as an intermediate fact. Use `hB.smooth` as an intermediate fact. Establish `hfl : Flat l.left` using `GlobalTheory.T.flat_of_fibres_finite R A B l inferInstance inferInstance inferInstance hf fun Ω _ _ s => (fib Ω s).2.1`. Take `⟨F, _, _, h, hsub, hker⟩` from `GlobalTheory.T.kernel_finite_flat R A B l hA hB hm hf hfl`. Take `⟨n, hn, hk⟩` from `h5 C v R hv A F h hsub`.

Take `⟨g, hg, e⟩` from `GlobalTheory.T.factor_through_finite_flat R A B A l (𝟙 A ^ n) hm (qi_isMonHom_id_pow A n) hfl hs inferInstance fun S _ _ z hz => by`. Take `⟨φ, rfl⟩` from `(hker S z).1 hz`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`. Conclude with `hk S φ`. Use `⟨n, g, hn, hg, e, GlobalTheory.T.epi_of_finite_flat R A B B l hfl hs inferInstance _ _ ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, e, MonObj.comp_pow, MonObj.pow_comp, Category.id_comp, Category.comp_id]`.
-/
theorem quasiInverseR_of (h1 : PolFibreIsogAny) (h5 : KilledAny) : QuasiInverseR := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB h₁ h₂ hp
  have hm : IsMonHom l := hp.1
  have fib := h1 C v R hv A B P l g hA hB hgA hgB h₁ h₂ hp
  obtain ⟨hf, hs⟩ := GlobalTheory.T.finite_of_finite_fibres R A B l hA hB hm fun Ω _ _ s => ⟨(fib Ω s).1, (fib Ω s).2.2⟩
  have := hA.comm
  have := hA.smooth
  have := hB.smooth
  have hfl : Flat l.left := GlobalTheory.T.flat_of_fibres_finite R A B l inferInstance inferInstance inferInstance hf
    fun Ω _ _ s => (fib Ω s).2.1
  obtain ⟨F, _, _, h, hsub, hker⟩ := GlobalTheory.T.kernel_finite_flat R A B l hA hB hm hf hfl
  obtain ⟨n, hn, hk⟩ := h5 C v R hv A F h hsub
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.factor_through_finite_flat R A B A l (𝟙 A ^ n) hm (qi_isMonHom_id_pow A n) hfl hs inferInstance
    fun S _ _ z hz => by
      obtain ⟨φ, rfl⟩ := (hker S z).1 hz
      rw [MonObj.comp_pow, Category.comp_id]
      exact hk S φ
  refine ⟨n, g, hn, hg, e, GlobalTheory.T.epi_of_finite_flat R A B B l hfl hs inferInstance _ _ ?_⟩
  rw [← Category.assoc, e, MonObj.comp_pow, MonObj.pow_comp, Category.id_comp, Category.comp_id]

/- English proof (translation)
The claim follows from `Z2.polFibreIsogAny`.
-/
theorem polFibreIsogAny : PolFibreIsogAny := Z2.polFibreIsogAny

/- English proof (translation)
The claim follows from `killedAny_of Qi.killedCore`.
-/
theorem killedAny : KilledAny := killedAny_of Qi.killedCore

/- English proof (translation)
The claim follows from `quasiInverseR_of polFibreIsogAny killedAny`.
-/
theorem quasiInverseR : QuasiInverseR := quasiInverseR_of polFibreIsogAny killedAny

end PositivityTheory.PrwZar
