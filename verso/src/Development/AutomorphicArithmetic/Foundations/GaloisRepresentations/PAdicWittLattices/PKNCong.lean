import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `p _ D G L N _ _ u hu h`. Establish `h1 : L.CongOne N u` using `GlobalTheory.AdelicSim.congOne_of D (L.actG u) N h`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Take `⟨w₁, hw₁, e₁⟩` from `hu.2 v hv`.

Establish `hv' : L.actG u⁻¹ v ∈ LaHat D`. Rewrite using `[e₁]`. Conclude with `add_mem hv (nsmul_mem hw₁ _)`. Take `⟨w, hw, e⟩` from `h1 _ hv'`. Establish `e' : L.actG u (L.actG u⁻¹ v) = v`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Use `⟨-w, neg_mem hw, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[e']`. Rewrite using `[smul_neg]`. Conclude with `eq_add_neg_of_add_eq e.symm`.
-/
theorem UpperTheory.Gal.G3.pKNCong :
    KNCong := by
  intro p _ D G L N _ _ u hu h
  have h1 : L.CongOne N u := GlobalTheory.AdelicSim.congOne_of D (L.actG u) N h
  refine ⟨h1, ?_⟩
  intro v hv
  obtain ⟨w₁, hw₁, e₁⟩ := hu.2 v hv
  have hv' : L.actG u⁻¹ v ∈ LaHat D := by
    rw [e₁]
    exact add_mem hv (nsmul_mem hw₁ _)
  obtain ⟨w, hw, e⟩ := h1 _ hv'
  have e' : L.actG u (L.actG u⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨-w, neg_mem hw, ?_⟩
  rw [e'] at e
  rw [smul_neg]
  exact eq_add_neg_of_add_eq e.symm
