import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem can_zero_mem_rad : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num → ∀ M : HermLB q, Can M 0 → cl M ∈ rad num := by
  intro hP k _ X _ q n ar num hn hS Q hQ
  haveI : IsLocallyNoetherian X := ar.isLocallyNoetherian
  obtain ⟨r, hr, hE, h1⟩ := hQ
  have hm (z : X) : (Q.div hr).mult z = 0 := by
    rw [hE]
    have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at this
    omega
  have hN (N : Fin (n + 1) → HermLB q) : num (Fin.cons (cl Q) fun j => cl (N j)) = 0 := by
    rw [GlobalTheory.VertMix.vertMix hP _ X q _ ar num hn Q r hr (fun σ y _ => (h1 σ y).2) N (fun _ => 2) (fun _ => 0)
      (fun z hz => absurd (hm z) hz)]
    simp [hm]
  have hg : num.curryLeft (cl Q) = 0 := by
    refine Module.Basis.ext_multilinear (fun _ => (Finsupp.basisSingleOne : Module.Basis (HermLB q) ℝ (Cl q))) fun N => ?_
    simpa [MultilinearMap.curryLeft_apply, Finsupp.coe_basisSingleOne, cl] using hN N
  have h0 (w : Fin (n + 1 + 1) → Cl q) : num (Function.update w 0 (cl Q)) = 0 := by
    have e : Function.update w 0 (cl Q) = Fin.cons (cl Q) (Fin.tail w) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp [Fin.tail, Function.update_of_ne (Fin.succ_ne_zero i)]
    rw [e, ← MultilinearMap.curryLeft_apply, hg]
    rfl
  intro v j
  rw [← hS _ (Equiv.swap 0 j), Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
  exact h0 _

end GlobalTheory.LatChain
