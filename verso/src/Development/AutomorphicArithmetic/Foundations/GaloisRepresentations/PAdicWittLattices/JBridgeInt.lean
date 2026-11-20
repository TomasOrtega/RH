import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

/- English proof (translation)
Introduce `hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x`. Take `⟨φ, hφ, -⟩` from `hInt E Ω l w A hA O Bw hB`. Establish `h1 : Bw.j (algebraMap E Ω x) = ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l)`. Rewrite using `[hφ x]`. Both sides reduce to the same expression.

Establish `h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1`. Rewrite using `[h1]`. Establish `hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1` using `(φ x).2`. Conclude with `hm` after adjusting the coercions. Establish `h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖` using `(GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _`.

Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem UpperTheory.Gal.G3.jBridgeInt :
    UpperTheory.Gal.Seam.IntMap → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BridgeInt := by
  intro hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x
  obtain ⟨φ, hφ, -⟩ := hInt E Ω l w A hA O Bw hB
  have h1 : Bw.j (algebraMap E Ω x) =
      ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l) := by
    rw [hφ x]
    rfl
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1 := by
    rw [h1]
    have hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1 := (φ x).2
    exact_mod_cast hm
  have h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖ :=
    (GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _
  rw [h3]
  exact h2
