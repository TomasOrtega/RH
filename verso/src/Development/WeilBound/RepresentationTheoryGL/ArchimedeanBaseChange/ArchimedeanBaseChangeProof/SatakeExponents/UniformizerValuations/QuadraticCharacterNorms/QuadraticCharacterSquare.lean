import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTriStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNormStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.CmQuadraticCharacterUnramified
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.ConsEta in
open PositivityTheory.Rg.BcB.F.Fok

namespace PositivityTheory.Rg.BcB.F.Fok.Mu2
open GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[infSign, MonoidHom.finset_prod_apply]`. Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Establish `: Units.map (GlobalTheory.IdeleNormChar.infEval w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E 1) w = 1`.

Rewrite using `[map_one]`. Both sides reduce to the same expression. Simplify using `only [MonoidHom.comp_apply, this, map_one]`.
-/
theorem infSign_ideleMap_finPartI (b : Neutral.B1.Ideles (maximalRealSubfield E)) :
    infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
  rw [infSign, MonoidHom.finset_prod_apply]
  refine Finset.prod_eq_one fun w _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval w)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
    refine Units.ext ?_
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E 1) w = 1
    rw [map_one]; rfl
  simp only [MonoidHom.comp_apply, this, map_one]

/- English proof (translation)
Use `set f := GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b`. Establish `h1 : ∀ v, ((b * f⁻¹ : Neutral.B1.Ideles _) : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1`. Introduce `v`. Establish `e : f⁻¹ = GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b⁻¹` using `(map_inv _ b).symm`. Rewrite using `[e]`.

Conclude with `congrArg (fun z : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) => z.2 v) b.mul_inv`. Establish `h2` using `GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial E _ h1`. Establish `h3` using `cm_quadratic_character_unramified E hU b hb`. Establish `e1 : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 (b * f⁻¹) * (GlobalTheory.GalOfCusp.quadChar E).1 f`. Rewrite using `[← map_mul, inv_mul_cancel_right]`.

Establish `e2 : infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) = infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (b * f⁻¹)) * infSign E (GlobalTheory.Indefin …`. Rewrite using `[← map_mul, ← map_mul, inv_mul_cancel_right]`. Rewrite using `[e1, e2, h2, h3, infSign_ideleMap_finPartI, mul_one]`.
-/
theorem eta_eq_infSign (hU : Unr E) (b : Neutral.B1.Ideles (maximalRealSubfield E))
    (hb : b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E)) :
    (GlobalTheory.GalOfCusp.quadChar E).1 b = infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  set f := GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b
  have h1 : ∀ v, ((b * f⁻¹ : Neutral.B1.Ideles _) : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1 := by
    intro v
    have e : f⁻¹ = GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b⁻¹ := (map_inv _ b).symm
    rw [e]
    exact congrArg (fun z : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) => z.2 v) b.mul_inv
  have h2 := GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial E _ h1
  have h3 := cm_quadratic_character_unramified E hU b hb
  have e1 : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 (b * f⁻¹) * (GlobalTheory.GalOfCusp.quadChar E).1 f := by
    rw [← map_mul, inv_mul_cancel_right]
  have e2 : infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (b * f⁻¹)) *
        infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E f) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [e1, e2, h2, h3, infSign_ideleMap_finPartI, mul_one]

/- English proof (translation)
Introduce `E _ _ _ hUnr`. Take `⟨w0, hw0⟩` from `GlobalTheory.T.exists_splitPlaceBelowCMField E`. Take `⟨V, hVo, hV⟩` from `GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity E w0`. Establish `hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E)` using `@GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra`. Use `⟨GlobalTheory.Mem.Chr.unitIdl E ⊓ (GlobalTheory.Mem.Chr.unitIdl E).comap (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) ⊓ V.comap (conjQuot E w0), infSign E, ?_, continuous_infSign, norm_infSign E, ?_⟩` and prove the remaining obligations.

Conclude with `(GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.preimage hC)).inter (hVo.preimage (continuous_conjQuot w0))`. Introduce `k b u hu hx`. Take `⟨⟨hx1, hx2⟩, hx3⟩` from `hx`. Establish `hu1` using `nsUnits_le_unitIdl hu`. Establish `hCu` using `GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles E u hu1`.

Use `set C := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E with hCdef`. Use `set I := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b with hI`. Use `set c : Eˣ →* Eˣ := Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toMonoidHom with hc`. Establish `hCx : C (Neutral.B1.diagUnits E k * I * u) = Neutral.B1.diagUnits E (c k) * I * C u`. Rewrite using `[map_mul, map_mul, hI, GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield]`.

Use `congr 2`. Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (maximalRealSubfield E) E k`. Use `set x := Neutral.B1.diagUnits E k * I * u with hxdef`. Use `set t : Eˣ := k / c k with ht`. Establish `hdt : Neutral.B1.diagUnits E t = (x / C x) * (u / C u)⁻¹`.

Rewrite using `[hCx, hxdef, ht, _root_.map_div]`. Conclude with `commGroup_div_eq_mul_div_mul_inv_div _ _ _ _ _`. Establish `htu : Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E`. Rewrite using `[hdt]`. Conclude with `mul_mem (div_mem hx1 hx2) (inv_mem (div_mem hu1 hCu))`.

Establish `hnorm : ∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1`. Introduce `φ`. Establish `h0 : φ (k : E) ≠ 0` using `by simp`. Establish `e : φ ((c k : Eˣ) : E) = starRingEnd ℂ (φ k)` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k`. Rewrite using `[ht, Units.val_div_eq_div_val, map_div₀, e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]`.

Establish `htor` using `GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one E t htu hnorm`. Establish `hcqu` using `GlobalTheory.T.conjQuot_eq_one_of_mem_nsUnits_of_isSplitAt E w0 hw0 u hu`. Establish `hmem : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t ∈ V`. Establish `e1 : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (Neutral.B1.diagUnits E t)` using `Units.ext rfl`. Establish `e2 : conjQuot E w0 x = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (x / C x)` using `rfl`.

Establish `e3 : conjQuot E w0 u = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (u / C u)` using `rfl`. Rewrite using `[e1, hdt, map_mul, map_inv, ← e2, ← e3, hcqu, inv_one, mul_one]`. Conclude with `hx3`. Establish `ht1` using `hV t htor hmem`. Establish `hck : c k = k` using `(div_eq_one.1 ht1).symm`.

Establish `hkF : (k : E) ∈ maximalRealSubfield E`. Use `(IsCMField.complexConj_eq_self_iff E _).1 ?_` and prove the remaining obligations. Conclude with `congrArg Units.val hck`. Use `set k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨(k : E), hkF⟩ (fun h => k.ne_zero (congrArg Subtype.val h)) with hk'`. Establish `hdk : Neutral.B1.diagUnits E k = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (Neutral.B1.diagUnits (maximalRealSubfield E) k')`.

Use `(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (maximalRealSubfield E) E k').trans ?_ |>.symm` and prove the remaining obligations. Conclude with `congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E) (Units.ext rfl)`. Use `set b' := Neutral.B1.diagUnits (maximalRealSubfield E) k' * b with hb'`. Establish `hxb : x = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' * u`. Rewrite using `[hxdef, hdk, hb', map_mul]`.

Establish `hηb : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 b'`. Rewrite using `[hb', map_mul, (GlobalTheory.GalOfCusp.quadChar E).2.2 k', one_mul]`. Establish `hb'E : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' ∈ GlobalTheory.Mem.Chr.unitIdl E`. Establish `: GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' = x * u⁻¹` using `by rw [hxb, mul_inv_cancel_right]`. Rewrite using `[this]`.

Conclude with `mul_mem hx1 (inv_mem hu1)`. Rewrite using `[hηb, eta_eq_infSign hUnr b' (GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield E b' hb'E), hxb, (infSign E).map_mul _ u, infSign_nsUnits hu, mul_one]`.
-/
theorem quadratic_character_square : type_of% GlobalTheory.T.exists_unitary_hecke_character_norm := by
  intro E _ _ _ hUnr
  obtain ⟨w0, hw0⟩ := GlobalTheory.T.exists_splitPlaceBelowCMField E
  obtain ⟨V, hVo, hV⟩ := GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity E w0
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine ⟨GlobalTheory.Mem.Chr.unitIdl E ⊓ (GlobalTheory.Mem.Chr.unitIdl E).comap (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) ⊓
    V.comap (conjQuot E w0), infSign E, ?_, continuous_infSign, norm_infSign E, ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.preimage hC)).inter
      (hVo.preimage (continuous_conjQuot w0))
  intro k b u hu hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hu1 := nsUnits_le_unitIdl hu
  have hCu := GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles E u hu1
  set C := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E with hCdef
  set I := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b with hI
  set c : Eˣ →* Eˣ := Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toMonoidHom with hc
  have hCx : C (Neutral.B1.diagUnits E k * I * u) = Neutral.B1.diagUnits E (c k) * I * C u := by
    rw [map_mul, map_mul, hI, GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield]
    congr 2
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (maximalRealSubfield E) E k
  set x := Neutral.B1.diagUnits E k * I * u with hxdef
  set t : Eˣ := k / c k with ht
  have hdt : Neutral.B1.diagUnits E t = (x / C x) * (u / C u)⁻¹ := by
    rw [hCx, hxdef, ht, _root_.map_div]
    exact commGroup_div_eq_mul_div_mul_inv_div _ _ _ _ _
  have htu : Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    rw [hdt]; exact mul_mem (div_mem hx1 hx2) (inv_mem (div_mem hu1 hCu))
  have hnorm : ∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1 := by
    intro φ
    have h0 : φ (k : E) ≠ 0 := by simp
    have e : φ ((c k : Eˣ) : E) = starRingEnd ℂ (φ k) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
    rw [ht, Units.val_div_eq_div_val, map_div₀, e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]
  have htor := GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one E t htu hnorm
  have hcqu := GlobalTheory.T.conjQuot_eq_one_of_mem_nsUnits_of_isSplitAt E w0 hw0 u hu
  have hmem : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t ∈ V := by
    have e1 : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t =
        Units.map (GlobalTheory.IdeleNormChar.finEval w0) (Neutral.B1.diagUnits E t) := Units.ext rfl
    have e2 : conjQuot E w0 x = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (x / C x) := rfl
    have e3 : conjQuot E w0 u = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (u / C u) := rfl
    rw [e1, hdt, map_mul, map_inv, ← e2, ← e3, hcqu, inv_one, mul_one]
    exact hx3
  have ht1 := hV t htor hmem
  have hck : c k = k := (div_eq_one.1 ht1).symm
  have hkF : (k : E) ∈ maximalRealSubfield E := by
    refine (IsCMField.complexConj_eq_self_iff E _).1 ?_
    exact congrArg Units.val hck
  set k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨(k : E), hkF⟩ (fun h => k.ne_zero (congrArg Subtype.val h)) with hk'
  have hdk : Neutral.B1.diagUnits E k =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (Neutral.B1.diagUnits (maximalRealSubfield E) k') := by
    refine (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (maximalRealSubfield E) E k').trans ?_ |>.symm
    exact congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E) (Units.ext rfl)
  set b' := Neutral.B1.diagUnits (maximalRealSubfield E) k' * b with hb'
  have hxb : x = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' * u := by
    rw [hxdef, hdk, hb', map_mul]
  have hηb : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 b' := by
    rw [hb', map_mul, (GlobalTheory.GalOfCusp.quadChar E).2.2 k', one_mul]
  have hb'E : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' = x * u⁻¹ := by rw [hxb, mul_inv_cancel_right]
    rw [this]; exact mul_mem hx1 (inv_mem hu1)
  rw [hηb, eta_eq_infSign hUnr b' (GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield E b' hb'E), hxb, (infSign E).map_mul _ u, infSign_nsUnits hu, mul_one]

end PositivityTheory.Rg.BcB.F.Fok.Mu2
