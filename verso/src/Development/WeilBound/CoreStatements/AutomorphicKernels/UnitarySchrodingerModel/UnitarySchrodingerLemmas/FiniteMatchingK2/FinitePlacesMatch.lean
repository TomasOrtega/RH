import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.FinMatchGen

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.KFinMatch

/- English proof (translation)
Use `show ((1 : Matrix (Fin n) (Fin n) (AE D)).map (cA D))ᵀ = 1`. Rewrite using `[Matrix.map_one (cA D) (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]`.
-/
theorem adj_one_k {D : D7} {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  show ((1 : Matrix (Fin n) (Fin n) (AE D)).map (cA D))ᵀ = 1
  rw [Matrix.map_one (cA D) (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D n M a d bs g gv hP lam L hlam hL hstd`. Establish `ha1 : a.1 * (a⁻¹).1 = 1` using `a.mul_inv`. Establish `ha2 : (a⁻¹).1 * a.1 = 1` using `a.inv_mul`. Establish `hadj1 : adj (D` using `D) a.1 * adj (D := D) (a⁻¹).1 = 1 := by rw [← adj_mul, ha2, adj_one_k]`. Establish `hadj2 : adj (D` using `D) (a⁻¹).1 * adj (D := D) a.1 = 1 := by rw [← adj_mul, ha1, adj_one_k]`.

Take `⟨L₁, L₂, Φf, Φv, h1, h2, h3, h4, h5⟩` from `GlobalTheory.CompanionTheory.SwFinM.finMatchGen (F := D.host.F) (E := D.host.E) (M := M) a.1 (a⁻¹).1 (adj (D := D) a.1) (adj (D := D) (a⁻¹).1) ha1 ha2 hadj1 hadj2 bs g gv hP lam L hlam hL hstd`. Conclude with `⟨L₁, L₂, Φf, Φv, h1, h2, h3, fun x => h4 x, fun v b => h5 v b.1⟩`.
-/
theorem finite_places_match : PositivityTheory.PfSWUS.SwMatch.FinMatch := by
  intro D n M a d bs g gv hP lam L hlam hL hstd
  have ha1 : a.1 * (a⁻¹).1 = 1 := a.mul_inv
  have ha2 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
  have hadj1 : adj (D := D) a.1 * adj (D := D) (a⁻¹).1 = 1 := by rw [← adj_mul, ha2, adj_one_k]
  have hadj2 : adj (D := D) (a⁻¹).1 * adj (D := D) a.1 = 1 := by rw [← adj_mul, ha1, adj_one_k]
  obtain ⟨L₁, L₂, Φf, Φv, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.SwFinM.finMatchGen (F := D.host.F) (E := D.host.E) (M := M)
    a.1 (a⁻¹).1 (adj (D := D) a.1) (adj (D := D) (a⁻¹).1) ha1 ha2 hadj1 hadj2 bs g gv hP lam L hlam hL hstd
  exact ⟨L₁, L₂, Φf, Φv, h1, h2, h3, fun x => h4 x, fun v b => h5 v b.1⟩

end PositivityTheory.PfSWUS.KFinMatch

end
