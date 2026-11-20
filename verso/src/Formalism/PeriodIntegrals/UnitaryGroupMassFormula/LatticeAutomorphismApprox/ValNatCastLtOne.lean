import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem val_natCast_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : (g : 𝓞 F) ∈ v.asIdeal) : Valued.v ((g : v.adicCompletion F)) < 1 := by
  have h1 : ((g : v.adicCompletion F)) = (((algebraMap (𝓞 F) F (g : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast (algebraMap (𝓞 F) F)]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
    | (rw [← map_natCast (algebraMap F (v.adicCompletion F)) g]; rfl)
  rw [h1]
  first
  | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hg
  | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hg
  | simpa [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] using hg

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem natCast_mem_max (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 := val_natCast_lt_one F v g hg
  have h2 : Valued.v ((w : v.adicCompletion F)) ≤ 1 := w.2
  have h3 : (g : v.adicCompletion F) * (w : v.adicCompletion F) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  have h5 : Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F)) < 1 :=
    calc Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F))
        ≤ Valued.v ((g : v.adicCompletion F)) * 1 := by gcongr
      _ = Valued.v ((g : v.adicCompletion F)) := mul_one _
      _ < 1 := h1
  exact (ne_of_lt h5) h4

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem vecV_smul' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E ⊗[I.F] Af I.F)
    (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (a • x) = PI.FinKW.psiV I v a • PI.FinKW.vecV I v x := by
  funext i
  simp only [PI.FinKW.vecV, Pi.smul_apply, smul_eq_mul, map_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem vecV_add' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by
  funext i
  simp only [PI.FinKW.vecV, Pi.add_apply, map_add]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiV_natCast (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    PI.FinKW.psiV I v (m : I.E ⊗[I.F] Af I.F) = (m : RV I v) := map_natCast _ m

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem vecV_mL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) (x : Fin I.n → I.E ⊗[I.F] Af I.F)
    (hx : x ∈ mL I m) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), PI.FinKW.vecV I v x = (m : RV I v) • w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', rfl⟩ := hy
    refine ⟨PI.FinKW.vecV I v x', PI.FinKW.LocTo.mem_local_lattice_iff I x' hx' v, ?_⟩
    rw [vecV_smul', psiV_natCast]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    funext i; simp [PI.FinKW.vecV]
  | add x y _ _ hx hy =>
    obtain ⟨w1, hw1, h1⟩ := hx
    obtain ⟨w2, hw2, h2⟩ := hy
    refine ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
    rw [vecV_add', h1, h2, smul_add]
  | smul c x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    refine ⟨PI.FinKW.psiV I v (c : I.E ⊗[I.F] Af I.F) • w,
      PI.FinKW.LocTo.intAf_le_mulSet I v c.2 w hw, ?_⟩
    show PI.FinKW.vecV I v ((c : I.E ⊗[I.F] Af I.F) • x) = _
    rw [vecV_smul', h, smul_comm]

end PI.UnitaryGroupMassFormula.ScXuExists
