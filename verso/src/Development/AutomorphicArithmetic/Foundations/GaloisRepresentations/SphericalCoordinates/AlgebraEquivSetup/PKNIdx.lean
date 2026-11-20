import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem relIndex_ne_zero_of_isOpen {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem isOpen_map_conj {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K : Subgroup X} (hK : IsOpen (K : Set X)) (g : X) :
    IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  have e : ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) =
      (fun x => g⁻¹ * x * g) ⁻¹' (K : Set X) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  rw [e]
  exact hK.preimage (by fun_prop)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.Seed.pKNIdx :
    KNOpen → KNIdx := by
  intro hop E _ _ _ A n p _ S T N hN
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N hN
  have hKo : IsOpen (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.K.isOpen
  have hKc : IsCompact (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.compact
  refine ⟨fun g => relIndex_ne_zero_of_isOpen hKc (isOpen_map_conj hKo g), fun K hKc' _ h0 => ?_⟩
  have hO := relIndex_ne_zero_of_isOpen hKc' (hop E A n p S T N hN)
  have e : S.L.KN N = ((S.L.KN N).comap T.j).comap T.sec := by
    ext h
    simp [Subgroup.mem_comap, T.j_sec]
  rw [e, Tr.lv, Subgroup.relIndex_comap] at h0
  exact hO (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)
