import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.NatCardTateOfIsCyclic
import GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic

def rationals : FiniteSubfield :=
  ⟨⊥, inferInstance⟩

/- English proof (translation)
The claim follows from `show (⊥ : IntermediateField ℚ ℚ̄) ≤ F.1 from bot_le`.
-/
theorem rationals_le (F : FiniteSubfield) : rationals ≤ F :=
  show (⊥ : IntermediateField ℚ ℚ̄) ≤ F.1 from bot_le

/- English proof (translation)
The claim follows from `IntermediateField.fixingSubgroup_bot`.
-/
theorem fixingSubgroup_rationals :
    rationals.1.fixingSubgroup = (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  IntermediateField.fixingSubgroup_bot

def baseEquiv :
    IdeleClassGroup rationals.1 ≃* fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  (fixedEquiv rationals).trans (MulEquiv.subgroupCongr (by rw [fixingSubgroup_rationals]))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_baseEquiv (c : IdeleClassGroup rationals.1) :
    (baseEquiv c : IdeleClassLimit) = of rationals c :=
  rfl

/- English proof (translation)
The claim follows from `ideleClassMap_injective (ideleClassMap_ideleClassMap (K := K) (L := K) (M := K) c)`.
-/
theorem ideleClassMap_self_eq (K : Type*) [Field K] [NumberField K] (c : IdeleClassGroup K) :
    ideleClassMap K K c = c :=
  ideleClassMap_injective (ideleClassMap_ideleClassMap (K := K) (L := K) (M := K) c)

def ratRingEquiv : ℚ ≃+* rationals.1 :=
  ((IntermediateField.botEquiv ℚ ℚ̄).symm : ℚ ≃ₐ[ℚ] (⊥ : IntermediateField ℚ ℚ̄)).toRingEquiv

/- English proof (translation)
Establish `h` using `ideleClassEquiv_ideleClassMap_of_comm (L := ℚ) (L' := ℚ) (M := ℚ) (M' := rationals.1) (RingEquiv.refl ℚ) ratRingEquiv (fun l ↦ by`. Rewrite using `[RingEquiv.refl_apply]`. Conclude with `(eq_ratCast (ratRingEquiv.toRingHom.comp (algebraMap ℚ ℚ)) l).trans (eq_ratCast (algebraMap ℚ rationals.1) l).symm) c`. Rewrite `h` using `[ideleClassMap_self_eq, ideleClassEquiv_refl]`. Then use the resulting hypothesis.
-/
theorem ideleClassEquiv_ratRingEquiv (c : IdeleClassGroup ℚ) :
    ideleClassEquiv ratRingEquiv c = ideleClassMap ℚ rationals.1 c := by
  have h := ideleClassEquiv_ideleClassMap_of_comm (L := ℚ) (L' := ℚ) (M := ℚ) (M' := rationals.1)
    (RingEquiv.refl ℚ) ratRingEquiv (fun l ↦ by
      rw [RingEquiv.refl_apply]
      exact (eq_ratCast (ratRingEquiv.toRingHom.comp (algebraMap ℚ ℚ)) l).trans
        (eq_ratCast (algebraMap ℚ rationals.1) l).symm) c
  rwa [ideleClassMap_self_eq, ideleClassEquiv_refl] at h

/- English proof (translation)
Rewrite using `[ideleClassEquiv_ratRingEquiv, ideleClassNorm_ideleClassMap, show Module.finrank ℚ rationals.1 = 1 from IntermediateField.finrank_bot, pow_one]`.
-/
theorem ideleClassNorm_ideleClassEquiv_ratRingEquiv (c : IdeleClassGroup ℚ) :
    ideleClassNorm ℚ rationals.1 (ideleClassEquiv ratRingEquiv c) = c := by
  rw [ideleClassEquiv_ratRingEquiv, ideleClassNorm_ideleClassMap,
    show Module.finrank ℚ rationals.1 = 1 from IntermediateField.finrank_bot, pow_one]

def ratEquiv :
    IdeleClassGroup ℚ ≃* fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  (ideleClassEquiv ratRingEquiv).toMulEquiv.trans baseEquiv

/- English proof (translation)
Rewrite using `[← ideleClassEquiv_ratRingEquiv]`. Both sides reduce to the same expression.
-/
theorem coe_ratEquiv (c : IdeleClassGroup ℚ) :
    (ratEquiv c : IdeleClassLimit) = of rationals (ideleClassMap ℚ rationals.1 c) := by
  rw [← ideleClassEquiv_ratRingEquiv]
  rfl

def val : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) →* Multiplicative ℤ̂ :=
  (cycDegree.comp (cycSymbol rationals)).comp baseEquiv.symm.toMonoidHom

/- English proof (translation)
Simplify using `[val]`.
-/
theorem val_baseEquiv (c : IdeleClassGroup rationals.1) :
    val (baseEquiv c) = cycDegree (cycSymbol rationals c) := by
  simp [val]

/- English proof (translation)
Establish `h : ratEquiv c = baseEquiv (ideleClassEquiv ratRingEquiv c)` using `MulEquiv.trans_apply _ _ c`. Rewrite using `[h, val_baseEquiv, cycSymbol, MonoidHom.comp_apply, ideleClassNorm_ideleClassEquiv_ratRingEquiv]`.
-/
theorem val_ratEquiv (c : IdeleClassGroup ℚ) :
    val (ratEquiv c) = cycDegree (reciprocityMap c) := by
  have h : ratEquiv c = baseEquiv (ideleClassEquiv ratRingEquiv c) := MulEquiv.trans_apply _ _ c
  rw [h, val_baseEquiv, cycSymbol, MonoidHom.comp_apply,
    ideleClassNorm_ideleClassEquiv_ratRingEquiv]

/- English proof (translation)
Set `` to `algebraOfLE h`. Establish `: IsScalarTower ℚ rationals.1 F.1` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Rewrite using `[cycSymbol, cycSymbol, MonoidHom.comp_apply, MonoidHom.comp_apply]`. Use `congr 1`. Conclude with `ideleClassNorm_ideleClassNorm (K := ℚ) (L := rationals.1) (M := F.1) c`.
-/
theorem cycSymbol_ideleClassNorm {F : FiniteSubfield} (h : rationals ≤ F)
    (c : IdeleClassGroup F.1) :
    cycSymbol rationals (FiniteSubfield.ideleClassNorm h c) = cycSymbol F c := by
  let := algebraOfLE h
  have : IsScalarTower ℚ rationals.1 F.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  rw [cycSymbol, cycSymbol, MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 1
  exact ideleClassNorm_ideleClassNorm (K := ℚ) (L := rationals.1) (M := F.1) c

/- English proof (translation)
Establish `h` using `coe_norm_of_eq (K := ⊤) (rationals_le F) fixingSubgroup_rationals.symm hU c hc`. Establish `he : norm IdeleClassLimit ⊤ U ⟨of F c, hc⟩ = baseEquiv (FiniteSubfield.ideleClassNorm (rationals_le F) c)` using `Subtype.ext h`. Rewrite using `[he, val_baseEquiv, cycSymbol_ideleClassNorm]`.
-/
theorem val_norm_of {U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} [(U.subgroupOf ⊤).FiniteIndex] {F : FiniteSubfield}
    (hU : U = F.1.fixingSubgroup) (c : IdeleClassGroup F.1)
    (hc : of F c ∈ fixedModule IdeleClassLimit U) :
    val (norm IdeleClassLimit ⊤ U ⟨of F c, hc⟩) = cycDegree (cycSymbol F c) := by
  have h := coe_norm_of_eq (K := ⊤) (rationals_le F) fixingSubgroup_rationals.symm hU c hc
  have he : norm IdeleClassLimit ⊤ U ⟨of F c, hc⟩ =
      baseEquiv (FiniteSubfield.ideleClassNorm (rationals_le F) c) :=
    Subtype.ext h
  rw [he, val_baseEquiv, cycSymbol_ideleClassNorm]

/- English proof (translation)
Rewrite using `[MonoidHom.range_comp, map_cycDegree_range_cycSymbol, fixingSubgroup_rationals, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]`. Conclude with `degree_surjective`.
-/
theorem range_cycDegree_comp_cycSymbol_rationals :
    (cycDegree.comp (cycSymbol rationals)).range = ⊤ := by
  rw [MonoidHom.range_comp, map_cycDegree_range_cycSymbol, fixingSubgroup_rationals,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact degree_surjective

/- English proof (translation)
Introduce `z`. Take `⟨c, hc⟩` from `MonoidHom.range_eq_top.1 range_cycDegree_comp_cycSymbol_rationals z`. Conclude with `⟨baseEquiv c, by rw [val_baseEquiv]; exact hc⟩`.
-/
theorem val_surjective : Function.Surjective val := by
  intro z
  obtain ⟨c, hc⟩ := MonoidHom.range_eq_top.1 range_cycDegree_comp_cycSymbol_rationals z
  exact ⟨baseEquiv c, by rw [val_baseEquiv]; exact hc⟩

/- English proof (translation)
The claim follows from `MonoidHom.range_eq_top.2 val_surjective`.
-/
theorem range_val : val.range = ⊤ :=
  MonoidHom.range_eq_top.2 val_surjective

/- English proof (translation)
The claim follows from `Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos (Subgroup.index_map_dvd _ degree_surjective) (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)))`.
-/
theorem inertiaDegree_ne_zero (F : FiniteSubfield) : inertiaDegree degree F.1.fixingSubgroup ≠ 0 :=
  Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos (Subgroup.index_map_dvd _ degree_surjective)
    (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)))

/- English proof (translation)
Rewrite using `[MonoidHom.range_comp, map_cycDegree_range_cycSymbol]`. Use extensionality with `x`. Rewrite using `[ProfiniteInteger.mem_of_index_ne_zero (inertiaDegree_ne_zero F)]`. Both sides reduce to the same expression.
-/
theorem range_cycDegree_comp_cycSymbol (F : FiniteSubfield) :
    (cycDegree.comp (cycSymbol F)).range =
      (powMonoidHom (inertiaDegree degree F.1.fixingSubgroup) :
        Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  rw [MonoidHom.range_comp, map_cycDegree_range_cycSymbol]
  ext x
  rw [ProfiniteInteger.mem_of_index_ne_zero (inertiaDegree_ne_zero F)]
  rfl

/- English proof (translation)
Use `set F := ofOpenSubgroup U`. Establish `hU : (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = F.1.fixingSubgroup` using `(fixingSubgroup_ofOpenSubgroup U).symm`. Establish `hR` using `range_cycDegree_comp_cycSymbol F`. Rewrite `hR` using `[← hU]`. Rewrite using `[range_val, ← MonoidHom.range_eq_map, ← hR]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (a : IdeleClassLimit) ∈ (of F).range := by`. Rewrite using `[← fixedModule_openSubgroup U]`.

Conclude with `a.2`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))`. Rewrite using `[hc]`. Conclude with `a.2`.

Establish `ha' : a = ⟨of F c, hc'⟩` using `Subtype.ext hc.symm`. Rewrite using `[ha']`. Conclude with `(val_norm_of hU c hc').symm`. Introduce and unpack `⟨c, rfl⟩`. Establish `hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))`.

Rewrite using `[fixedModule_openSubgroup]`. Conclude with `⟨c, rfl⟩`. Conclude with `⟨⟨of F c, hc'⟩, val_norm_of hU c hc'⟩`.
-/
theorem range_val_comp_norm (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (val.comp (norm IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)))).range =
      val.range.map (powMonoidHom (inertiaDegree degree (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)))) := by
  set F := ofOpenSubgroup U
  have hU : (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = F.1.fixingSubgroup := (fixingSubgroup_ofOpenSubgroup U).symm
  have hR := range_cycDegree_comp_cycSymbol F
  rw [← hU] at hR
  rw [range_val, ← MonoidHom.range_eq_map, ← hR]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, hc⟩ : (a : IdeleClassLimit) ∈ (of F).range := by
      rw [← fixedModule_openSubgroup U]
      exact a.2
    refine ⟨c, ?_⟩
    have hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [hc]; exact a.2
    have ha' : a = ⟨of F c, hc'⟩ := Subtype.ext hc.symm
    rw [ha']
    exact (val_norm_of hU c hc').symm
  · rintro ⟨c, rfl⟩
    have hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [fixedModule_openSubgroup]; exact ⟨c, rfl⟩
    exact ⟨⟨of F c, hc'⟩, val_norm_of hU c hc'⟩

/- English proof (translation)
Use `set N : ℕ+ := ⟨n, hn⟩`. Use `set x := Multiplicative.toAdd (val a)`. Use `set k : ℕ := (ProfiniteInteger.proj N x).val`. Establish `h0 : ProfiniteInteger.proj N (x - (k : ℤ̂)) = 0`. Rewrite using `[map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`.

Take `⟨y, hy⟩` from `ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero h0`. Take `⟨b, hb⟩` from `val_surjective (Multiplicative.ofAdd y)`. Use `⟨k, b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, toAdd_ofAdd, Int.cast_natCast]`. Express the relevant statement in the definitionally equal form `x = (k : ℤ̂) + (N : ℕ) • y`.

Rewrite using `[← hy]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_eq_intCast_add_nsmul (n : ℕ) (hn : 0 < n)
    (a : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) :
    ∃ (m : ℤ) (b : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b) := by
  set N : ℕ+ := ⟨n, hn⟩
  set x := Multiplicative.toAdd (val a)
  set k : ℕ := (ProfiniteInteger.proj N x).val
  have h0 : ProfiniteInteger.proj N (x - (k : ℤ̂)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨y, hy⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero h0
  obtain ⟨b, hb⟩ := val_surjective (Multiplicative.ofAdd y)
  refine ⟨k, b, ?_⟩
  rw [hb, toAdd_ofAdd, Int.cast_natCast]
  change x = (k : ℤ̂) + (N : ℕ) • y
  rw [← hy]
  abel

def classFieldTheory : ClassFieldTheory (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  deg := degree
  continuous_deg := continuous_degree
  surjective_deg := degree_surjective
  val := val
  intCast_mem_range_val _ := val_surjective _
  exists_eq_intCast_add_nsmul := exists_eq_intCast_add_nsmul
  range_val_comp_norm := range_val_comp_norm
  isDiscreteModule := inferInstance
  classFieldAxiom := classFieldAxiom

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem classFieldTheory_deg : classFieldTheory.deg = degree :=
  rfl

/- English proof (translation)
The claim follows from `val_ratEquiv c`.
-/
theorem classFieldTheory_val (c : IdeleClassGroup ℚ) :
    classFieldTheory.val (ratEquiv c) = cycDegree (reciprocityMap c) :=
  val_ratEquiv c

/- English proof (translation)
The claim follows from `val_surjective`.
-/
theorem classFieldTheory_val_surjective : Function.Surjective classFieldTheory.val :=
  val_surjective

end IdeleClassLimit

end

end GroundTheory.Global
