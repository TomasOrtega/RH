import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c : ℕ}

scoped instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩
scoped instance scMx (m n : ℕ) : SecondCountableTopology (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.1
scoped instance t2Mx (m n : ℕ) : T2Space (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.2.1

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_ci (w : InfinitePlace D.host.F) : Continuous (compInf D.host.F D.host.E w) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (evInf D.host.F w).toLinearMap (map_mul (evInf D.host.F w))
    ((continuous_apply w).comp continuous_fst)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_cv (v : Pl D) : Continuous (cv D v) := GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem box₁ {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (AE D)} (hK : IsCompact K) :
    ∃ K' : Set (AE D), IsCompact K' ∧
      ∀ x, (∀ v ∉ S, cv D v x ∈ intLoc D.host.F D.host.E v) → e * x ∈ K → x ∈ K' := by
  classical
  obtain ⟨K', hK', hmem⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box D.host.F D.host.E
    (fun w => compInf D.host.F D.host.E w '' K)
    (fun v => if v ∈ S then cv D v '' K else (intLoc D.host.F D.host.E v : Set _))
    (fun w => hK.image (continuous_ci w))
    (fun v => by
      split_ifs
      · exact hK.image (continuous_cv v)
      · exact (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1)
    (Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => Finset.mem_coe.2 (by
      by_contra h
      exact hv (by simp [h]))))
  refine ⟨K', hK', fun x hx hex => hmem x (fun w => ⟨e * x, hex, ?_⟩) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · by_cases hv : v ∈ S
    · simp only [if_pos hv]
      exact ⟨e * x, hex, by rw [map_mul, he.2 v, if_pos hv, one_mul]⟩
    · simp only [if_neg hv]
      exact hx v hv

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem boxM {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (Mx D a b)} (hK : IsCompact K) :
    ∃ K' : Set (Mx D a b), IsCompact K' ∧ ∀ x, IntOff S x → e • x ∈ K → x ∈ K' := by
  choose C hC hCm using fun i j => box₁ he (hK.image (continuous_id.matrix_elem i j))
  refine ⟨{x | ∀ i j, x i j ∈ C i j}, ?_, fun x hx hex i j => hCm i j (x i j) (fun v hv => hx v hv i j) ⟨e • x, hex, rfl⟩⟩
  exact isCompact_pi_infinite fun i => isCompact_pi_infinite fun j => hC i j

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem boxP {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (Mx D a b × Mx D a c)} (hK : IsCompact K) :
    ∃ K' : Set (Mx D a b × Mx D a c), IsCompact K' ∧
      ∀ z : Mx D a b × Mx D a c, IntOff S z.1 → IntOff S z.2 → (e • z.1, e • z.2) ∈ K → z ∈ K' := by
  obtain ⟨K1, h1, m1⟩ := boxM he (hK.image continuous_fst)
  obtain ⟨K2, h2, m2⟩ := boxM he (hK.image continuous_snd)
  exact ⟨K1 ×ˢ K2, h1.prod h2, fun z hz1 hz2 hz => ⟨m1 _ hz1 ⟨_, hz, rfl⟩, m2 _ hz2 ⟨_, hz, rfl⟩⟩⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cv_eq_zero {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {N : Mx D a b} (hN : e • N = N) {v : Pl D}
    (hv : v ∉ S) (i : Fin a) (j : Fin b) : cv D v (N i j) = 0 := by
  rw [← hN, Matrix.smul_apply, smul_eq_mul, map_mul, he.2 v, if_neg hv, zero_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intOff_iff {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {x x' : Mx D a b} (h : e • (x' - x) = x' - x) :
    IntOff S x' ↔ IntOff S x := by
  have key : ∀ v ∉ S, ∀ i j, cv D v (x' i j) = cv D v (x i j) := fun v hv i j => by
    have := cv_eq_zero he h hv i j
    rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  refine ⟨fun hx v hv i j => ?_, fun hx v hv i j => ?_⟩
  · rw [← key v hv i j]; exact hx v hv i j
  · rw [key v hv i j]; exact hx v hv i j

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isClosed_intOff (S : Finset (Pl D)) : IsClosed {x : Mx D a b | IntOff S x} := by
  have hc : ∀ v : Pl D, IsClosed (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := fun v => by
    have := AddSubgroup.isClosed_of_isOpen (intLoc D.host.F D.host.E v).toAddSubgroup (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
    exact this
  simp only [IntOff, Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => isClosed_iInter fun j =>
    (hc v).preimage ((continuous_cv v).comp (continuous_id.matrix_elem i j))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intOff_mul {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := fun v hv i j => by
  show cv D v ((x * y) i j) ∈ _
  rw [Matrix.mul_apply, map_sum]
  exact Subring.sum_mem _ fun k _ => by rw [map_mul]; exact Subring.mul_mem _ (hx v hv i k) (hy v hv k j)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := fun v hv i j => by
  show cv D v (cA D (x j i)) ∈ _
  rw [cv_cA]
  exact GlobalTheory.AdelicU.sigR_mem_intLoc _ (hx v hv j i)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem exists_intOff (M : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S M := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele (M i j)
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun S hS v hv i j => ?_⟩
  by_contra hn
  exact hv (hS ((Filter.eventually_cofinite.1 h).mem_toFinset.2 fun h' => hn (h' i j)))

end PositivityTheory.Rg.Rsw.L.LToS

end
