import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hSF hFS hFF q _ i Z S p _ w hw A hζ a`. Take `⟨ζ⟩` from `hζ`. Use `haveI : IsFinite A.r := Sq.finite A`. Establish `hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ)` using `((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm`. Take `⟨φ, hφ, hv⟩` from `hSF q i A.V (ζ.map A.r.appTop.hom) a`.

Take `⟨ψ, hψ, hs⟩` from `hw A φ hφ`. Take `⟨b, hb⟩` from `hFS q i A.U ζ ψ hψ`. Use `⟨b, fun Ω _ _ x => ?_⟩` and prove the remaining obligations. Establish `hfin : (fib A.r x).Finite` using `hFF A.r Ω x`. Establish `hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ)`.

Introduce `z hz`. Establish `hz' : z ≫ A.r = x` using `hz`. Rewrite using `[hv Ω z, hgen, res_res, hz']`. Rewrite using `[hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun z hzm => ?_` and prove the remaining obligations.

Rewrite using `[hz z (hfin.mem_toFinset.mp hzm), mul_smul]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.sumExLoc_of :
    SecFun → FunSec → FibFin → SumExLoc := by
  intro hSF hFS hFF q _ i Z S p _ w hw A hζ a
  obtain ⟨ζ⟩ := hζ
  haveI : IsFinite A.r := Sq.finite A
  have hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ) :=
    ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm
  obtain ⟨φ, hφ, hv⟩ := hSF q i A.V (ζ.map A.r.appTop.hom) a
  obtain ⟨ψ, hψ, hs⟩ := hw A φ hφ
  obtain ⟨b, hb⟩ := hFS q i A.U ζ ψ hψ
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hfin : (fib A.r x).Finite := hFF A.r Ω x
  have hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ) := by
    intro z hz
    have hz' : z ≫ A.r = x := hz
    rw [hv Ω z, hgen, res_res, hz']
  rw [hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hzm => ?_
  rw [hz z (hfin.mem_toFinset.mp hzm), mul_smul]
