import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K)` using `hO.preimage continuous_subtype_val`. Use `haveI := Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Nat.card_pos.ne'`.
-/
private theorem relIndex_ne_zero_of_isOpen {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

/- English proof (translation)
Establish `e : ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) = (fun x => g⁻¹ * x * g) ⁻¹' (K : Set X)`. Use extensionality with `x`. Simplify using `only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify `hy` using `[mul_assoc]`. Introduce `h`. Conclude with `⟨_, h, by simp [mul_assoc]⟩`. Rewrite using `[e]`. Conclude with `hK.preimage (by fun_prop)`.
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
Introduce `hop E _ _ _ A n p _ S T N hN`. Take `⟨Lv, hLv⟩` from `GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N hN`. Establish `hKo : IsOpen (S.L.KN N : Set S.G.GAf)` using `hLv ▸ Lv.K.isOpen`. Establish `hKc : IsCompact (S.L.KN N : Set S.G.GAf)` using `hLv ▸ Lv.compact`. Use `⟨fun g => relIndex_ne_zero_of_isOpen hKc (isOpen_map_conj hKo g), fun K hKc' _ h0 => ?_⟩` and prove the remaining obligations.

Establish `hO` using `relIndex_ne_zero_of_isOpen hKc' (hop E A n p S T N hN)`. Establish `e : S.L.KN N = ((S.L.KN N).comap T.j).comap T.sec`. Use extensionality with `h`. Simplify using `[Subgroup.mem_comap, T.j_sec]`. Rewrite `h0` using `[e, Tr.lv, Subgroup.relIndex_comap]`.

Conclude with `hO (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)`.
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
