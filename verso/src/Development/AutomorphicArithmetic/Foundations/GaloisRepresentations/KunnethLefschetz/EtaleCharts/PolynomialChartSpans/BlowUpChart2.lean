import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BChartEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
