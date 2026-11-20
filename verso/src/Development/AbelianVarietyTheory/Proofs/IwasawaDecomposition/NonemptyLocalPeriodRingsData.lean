import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfThetaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcrisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coreEx_alg_tower {l : ℕ} [Fact l.Prime] (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem coreEx_isUnit_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (h1 : e.untilt = 1) (h2 : e ≠ 1)
    (w : Per.Acris0 l)
    (hw : (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1)) :
    IsUnit (l : Per.Bcris l) := by
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hu : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
    exact GlobalTheory.CrisLoc.unit_of_root l e h1 h2
  have h3 := congrArg ((algebraMap (Per.Acris l) (Per.Bcris l)).comp
    (algebraMap (Per.Acris0 l) (Per.Acris l))) h0
  rw [map_mul, map_natCast, map_pow] at h3
  have h4 : (algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e)) := by
    rw [coreEx_alg_tower, RingHom.comp_apply]
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hu.pow (l - 1))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem nonempty_core : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  intro l _
  obtain ⟨ζ, ε, z0, zs, z1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_isBdRPlusSectionOfTheta l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l j hj
  have h1 : ε.untilt = 1 := by
    have h := hr 0
    rw [z0, map_one] at h
    exact Subtype.ext h
  have h2 : ε ≠ 1 := by
    intro h
    have h' := hr 1
    rw [h] at h'
    simp only [rootT, Function.iterate_one, map_one] at h'
    apply z1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h', map_one]
    rfl
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l ε h1
  have hA : ∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
    intro a
    have h := hι (algebraMap (Per.Ainf l) (Per.Acris l) a)
    have h' : j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
      rw [coreEx_alg_tower, hj.on0]; rfl
    rw [h'] at h
    rw [GlobalTheory.RingIface.aB_apply]
    exact h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris l o ι ho hinj hA (coreEx_isUnit_l ε h1 h2 w hw)
  obtain ⟨t, -, ht, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l ε h1
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  exact ⟨⟨ζ, z0, zs, z1, ε, hr, o, ho, j, hj, ι, hι, u, hu, t, ht, σ, hσ, χ, hχ⟩⟩

end

end GlobalTheory.MemLoc
