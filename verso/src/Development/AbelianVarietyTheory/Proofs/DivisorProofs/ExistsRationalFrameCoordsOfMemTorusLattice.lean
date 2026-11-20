import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨t, ht, A, hA, rfl⟩` from `hz`. Establish `hAint : GlobalTheory.InertSign.IntE D (A p q)`. Establish `h1 : (Pi.single q 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N`.

Use `GlobalTheory.ThetaLatImage.mem_stdL.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = q`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`. Establish `h2` using `GlobalTheory.ThetaLatImage.mem_homL.1 hA _ h1`. Rewrite `h2` using `[Matrix.mulVec_single_one]`. Conclude with `GlobalTheory.ThetaLatImage.mem_stdL.1 h2 p`.

Take `⟨o, ho⟩` from `hAint`. Establish `ht' : t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨c, hc, a, ha, rfl⟩` from `ht`.

Establish `hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)` using `FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)`. Conclude with `FractionalIdeal.mul_mem_mul hc' ha`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul o x _ hx => exact Submodule.smul_mem _ o hx`.

Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o ht'`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul o x _ hx => exact Submodule.smul_mem _ o hx`.
-/
theorem entry_mem_AA {N N' : ℕ} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
    (p : Fin N') (q : Fin N) : z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    have hAint : GlobalTheory.InertSign.IntE D (A p q) := by
      have h1 : (Pi.single q 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
        refine GlobalTheory.ThetaLatImage.mem_stdL.2 fun i => ?_
        by_cases h : i = q
        · subst h; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      have h2 := GlobalTheory.ThetaLatImage.mem_homL.1 hA _ h1
      rw [Matrix.mulVec_single_one] at h2
      exact GlobalTheory.ThetaLatImage.mem_stdL.1 h2 p
    obtain ⟨o, ho⟩ := hAint
    have ht' : t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨c, hc, a, ha, rfl⟩ := ht
        have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
          FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
        exact FractionalIdeal.mul_mem_mul hc' ha
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul o x _ hx => exact Submodule.smul_mem _ o hx
    rw [Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o ht'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ o hx

end GlobalTheory.ThetaLawLat

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

/- English proof (translation)
Introduce `v` and use `by rw [map_one]; exact one_mem _`.
-/
theorem one_mem_intAf' : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

/- English proof (translation)
Establish `h1 : (frS.1ᴴ * S.gram) * frS.1 = 1` using `hS`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_frame {S : HSp D} (frS : GL (Fin S.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1) :
    (frS⁻¹).1 = frS.1ᴴ * S.gram := by
  have h1 : (frS.1ᴴ * S.gram) * frS.1 = 1 := hS
  calc (frS⁻¹).1 = ((frS.1ᴴ * S.gram) * frS.1) * (frS⁻¹).1 := by rw [h1, Matrix.one_mul]
    _ = frS.1ᴴ * S.gram := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/- English proof (translation)
Establish `key : GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) = ∑ p, ∑ q, Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (z p q * (fun a => frT.1 a p) i * ∑ k, star ((fun a => frS.1 a q) k) * S.gram k j)`. Use extensionality with `i j`. Simplify using `only [Matrix.sum_apply, Matrix.of_apply]`. Simplify using `only [← TensorProduct.tmul_sum]`. Use `show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * z * (frS⁻¹).1) i j = _`.

Use `congr 1`. Rewrite using `[inv_frame frS hS]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring`.

Rewrite using `[key]`. Use `AddSubgroup.sum_mem _ fun p _ => AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Conclude with `⟨1, one_mem_intAf', fun v h => (h trivial).elim, z p q, hz p q, _, Submodule.subset_span ⟨q, rfl⟩, _, Submodule.subset_span ⟨p, rfl⟩, rfl⟩`.
-/
theorem finRat_frame_mem_latO {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : ∀ p q, z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) =
      ∑ p, ∑ q, Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F]
        (z p q * (fun a => frT.1 a p) i * ∑ k, star ((fun a => frS.1 a q) k) * S.gram k j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply]
    simp only [← TensorProduct.tmul_sum]
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * z * (frS⁻¹).1) i j = _
    congr 1
    rw [inv_frame frS hS]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [key]
  refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ?_
  exact ⟨1, one_mem_intAf', fun v h => (h trivial).elim, z p q, hz p q, _,
    Submodule.subset_span ⟨q, rfl⟩, _, Submodule.subset_span ⟨p, rfl⟩, rfl⟩

/- English proof (translation)
Introduce `D S T frS frT hS hT δ x hx`. Take `⟨z, hz, rfl⟩` from `GlobalTheory.ThetaLatImage.La_sub hx`. Use `⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO frS frT hS z (GlobalTheory.ThetaLawLat.entry_mem_AA hz), ?_⟩` and prove the remaining obligations. Establish `hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) = GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹`. Introduce `τ`.

Establish `hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ)`. Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[hi]`. Use `show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `τ a b`. Rewrite using `[GlobalTheory.ThetaLatImage.pt_apply]`. Use `show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) * GlobalTheory.FockPos.frAt frS τ) a b`.

Rewrite using `[hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]`. Both sides reduce to the same expression.
-/
theorem mem_La_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  intro D S T frS frT hS hT δ x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO frS frT hS z (GlobalTheory.ThetaLawLat.entry_mem_AA hz), ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

end GlobalTheory.ThetaLawLat
