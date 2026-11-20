import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BChartEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `R _ Z W _ π hπ D c`. Use `set φ := MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s with hφ`. Establish `hs : (fun k => φ (MvPolynomial.X k)) = c.s`. Use function extensionality and compare the values at `k`. Simplify using `[hφ]`.

Establish `hflat : φ.Flat`. Establish `he` using `dCoord R Z D c`. Use `algebraize [φ]`. Conclude with `Algebra.Smooth.flat _ _`. Use `haveI : QuasiCompact (Over.Hom.left (dg Z)) := by`.

Express the relevant statement in the definitionally equal form `QuasiCompact (pullback.diagonal (Over.hom Z))`. Use `infer_instance`. Establish `hI : (Scheme.Hom.ker (Over.Hom.left (dg Z))).ideal ⟨c.N, c.aff⟩ = Ideal.span (Set.range fun k => φ (MvPolynomial.X k))`. Rewrite using `[Scheme.Hom.ker_apply, hs, Scheme.Hom.app_eq_appLE]`. Conclude with `c.ker`.

Establish `key` using `bChartEx R π _ hπ ⟨c.N, c.aff⟩ D (Sec Z c.U) φ hflat hI`. Rewrite `key` using `[hs]`. Conclude with `key`.
-/
theorem blChart : BlowUpChart₂ := by
  intro R _ Z W _ π hπ D c
  set φ := MvPolynomial.eval₂Hom (secMap (p1 Z) c.h1).toRingHom c.s with hφ
  have hs : (fun k => φ (MvPolynomial.X k)) = c.s := by
    funext k
    simp [hφ]
  have hflat : φ.Flat := by
    have he := dCoord R Z D c
    algebraize [φ]
    exact Algebra.Smooth.flat _ _
  haveI : QuasiCompact (Over.Hom.left (dg Z)) := by
    change QuasiCompact (pullback.diagonal (Over.hom Z))
    infer_instance
  have hI : (Scheme.Hom.ker (Over.Hom.left (dg Z))).ideal ⟨c.N, c.aff⟩
      = Ideal.span (Set.range fun k => φ (MvPolynomial.X k)) := by
    rw [Scheme.Hom.ker_apply, hs, Scheme.Hom.app_eq_appLE]
    exact c.ker
  have key := bChartEx R π _ hπ ⟨c.N, c.aff⟩ D (Sec Z c.U) φ hflat hI
  rw [hs] at key
  exact key

end UpperTheory.Gal.KunnethLefschetz.G
