import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKGLIffVal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.UaF

open Formalism.UG GlobalTheory.DefU GlobalTheory.SplitPts

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
private theorem cLoc_eq (u : Plc L) (x : UA L n) :
    cLoc u x = GeneralLinearGroup.map (pLoc L u) (GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl

/- English proof (translation)
Use `Subtype.ext (ga_ext h1 (Units.ext (matAf_ext fun u => ?_)))` and prove the remaining obligations. Use `congrArg Units.val (h2 u)` as an intermediate fact. Conclude with `this`.
-/
private theorem ext_all {x y : UA L n} (h1 : cInf x = cInf y) (h2 : ∀ u, cLoc u x = cLoc u y) : x = y := by
  refine Subtype.ext (ga_ext h1 (Units.ext (matAf_ext fun u => ?_)))
  have := congrArg Units.val (h2 u)
  exact this

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => GlobalTheory.IsoPull.ext_coord fun τ => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin n) ℂ => g.val i j) (h τ)`.
-/
private theorem cInf_ext {x y : UA L n} (h : ∀ τ : L →+* ℂ, cEmb τ x = cEmb τ y) : cInf x = cInf y := by
  refine Units.ext (Matrix.ext fun i j => GlobalTheory.IsoPull.ext_coord fun τ => ?_)
  exact congrArg (fun g : GL (Fin n) ℂ => g.val i j) (h τ)

/- English proof (translation)
Establish `h : GeneralLinearGroup.map (pFin L) k.1 = 1` using `hk`. Rewrite using `[cLoc_eq, h, map_one]`.
-/
private theorem cLoc_of_inf {k : UA L n} (hk : k ∈ infU L n) (u : Plc L) : cLoc u k = 1 := by
  have h : GeneralLinearGroup.map (pFin L) k.1 = 1 := hk
  rw [cLoc_eq, h, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pFin L) k.1 = 1`. Use `Units.ext (matAf_ext fun u => ?_)` and prove the remaining obligations. Use `congrArg Units.val (h u)` as an intermediate fact. Rewrite `this`, the goal using `[Units.val_one]`. Rewrite using `[map_one]`.

Conclude with `this`.
-/
private theorem inf_of_cLoc {k : UA L n} (h : ∀ u : Plc L, cLoc u k = 1) : k ∈ infU L n := by
  change GeneralLinearGroup.map (pFin L) k.1 = 1
  refine Units.ext (matAf_ext fun u => ?_)
  have := congrArg Units.val (h u)
  rw [Units.val_one] at this ⊢
  rw [map_one]
  exact this

private noncomputable def fp (x : UA L n) : UA L n :=
  ⟨finGL L n (GeneralLinearGroup.map (pFin L) x.1), finGL_mem_UA _ fun u => comp_eq x u⟩

/- English proof (translation)
The claim follows from `pInf_finGL _`.
-/
private theorem fp_fin (x : UA L n) : fp x ∈ finU L n := pInf_finGL _

/- English proof (translation)
The claim follows from `(cLoc_finGL u _ _).trans (cLoc_eq u x).symm`.
-/
private theorem cLoc_fp (u : Plc L) (x : UA L n) : cLoc u (fp x) = cLoc u x :=
  (cLoc_finGL u _ _).trans (cLoc_eq u x).symm

/- English proof (translation)
Establish `key` using `GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w`. Establish `h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE L) w u → u = conjSrc (conjE L) w` using `fun u h => by`. Rewrite using `[eq_conjSrc h, conjSrc_conjSrc_cm]`. Use `⟨fun h => ((key u).1 h).imp_right (h2 u), ?_⟩` and prove the remaining obligations. Introduce and unpack `(rfl | rfl)`.

Both sides reduce to the same expression. Conclude with `(key _).2 (Or.inr (conjPl_self_conjSrc w))`.
-/
private theorem under_iff (w u : Plc L) : un u = un w ↔ u = w ∨ u = conjSrc (conjE L) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE L) w u → u = conjSrc (conjE L) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  refine ⟨fun h => ((key u).1 h).imp_right (h2 u), ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact (key _).2 (Or.inr (conjPl_self_conjSrc w))

/- English proof (translation)
Use `set T : Finset (Plc L) := {w, conjSrc (conjE L) w} with hT`. Establish `memT : ∀ u, u ∈ T ↔ un u = un w` using `fun u => by`. Rewrite using `[under_iff]`. Simplify using `[hT]`. Establish `memC : ∀ u, conjSrc (conjE L) u ∈ T ↔ u ∈ T` using `fun u => by`.

Simplify using `only [hT, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Use `right`. Rewrite using `[← h, conjSrc_conjSrc_cm]`.

Use `left`. Conclude with `conjSrc_injective _ h`. Introduce and unpack `(rfl | rfl)`. Use `right`. Both sides reduce to the same expression.

Use `left`. Conclude with `conjSrc_conjSrc_cm w`. Use `set g := GeneralLinearGroup.map (pFin L) x.1 with hg`. Establish `hU : finGL L n (GlobalTheory.EulerTw.prjG L n T g) ∈ UA L n`. Use `finGL_mem_UA _ fun u => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.EulerTwKU.pLoc_prjG, GlobalTheory.EulerTwKU.pLoc_prjG]`. Distinguish the cases in `hu : u ∈ T`. Rewrite using `[if_pos hu, if_pos ((memC u).2 hu)]`. Conclude with `comp_eq x u`. Rewrite using `[if_neg hu, if_neg (fun h => hu ((memC u).1 h))]`.

Simplify using the standard rewrite rules. Establish `hc : ∀ u, cLoc u (⟨_, hU⟩ : UA L n) = if u ∈ T then cLoc u x else 1` using `fun u => by`. Rewrite using `[cLoc_finGL, GlobalTheory.EulerTwKU.pLoc_prjG, cLoc_eq]`. Use `⟨⟨_, hU⟩, Subgroup.mem_inf.2 ⟨pInf_finGL _, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[hc, if_neg (fun h => hu ((memT u).1 h))]`.

Rewrite using `[hc, if_pos ((memT u).2 hu)]`.
-/
private theorem cut (w : Plc L) (x : UA L n) (hx : x ∈ finU L n) :
    ∃ a ∈ locU n w, ∀ u, un u = un w → cLoc u a = cLoc u x := by
  classical
  set T : Finset (Plc L) := {w, conjSrc (conjE L) w} with hT
  have memT : ∀ u, u ∈ T ↔ un u = un w := fun u => by
    rw [under_iff]; simp [hT]
  have memC : ∀ u, conjSrc (conjE L) u ∈ T ↔ u ∈ T := fun u => by
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · right; rw [← h, conjSrc_conjSrc_cm]
      · left; exact conjSrc_injective _ h
    · rintro (rfl | rfl)
      · right; rfl
      · left; exact conjSrc_conjSrc_cm w
  set g := GeneralLinearGroup.map (pFin L) x.1 with hg
  have hU : finGL L n (GlobalTheory.EulerTw.prjG L n T g) ∈ UA L n := by
    refine finGL_mem_UA _ fun u => ?_
    rw [GlobalTheory.EulerTwKU.pLoc_prjG, GlobalTheory.EulerTwKU.pLoc_prjG]
    by_cases hu : u ∈ T
    · rw [if_pos hu, if_pos ((memC u).2 hu)]
      exact comp_eq x u
    · rw [if_neg hu, if_neg (fun h => hu ((memC u).1 h))]
      simp
  have hc : ∀ u, cLoc u (⟨_, hU⟩ : UA L n) = if u ∈ T then cLoc u x else 1 := fun u => by
    rw [cLoc_finGL, GlobalTheory.EulerTwKU.pLoc_prjG, cLoc_eq]
  refine ⟨⟨_, hU⟩, Subgroup.mem_inf.2 ⟨pInf_finGL _, Subgroup.mem_iInf.2 fun u =>
    Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, fun u hu => ?_⟩
  · rw [hc, if_neg (fun h => hu ((memT u).1 h))]
  · rw [hc, if_pos ((memT u).2 hu)]

/- English proof (translation)
Establish `hv` using `(GlobalTheory.EulerTwKU.mem_KGL_iff_val _).1 h`. Use `set g := cLoc (conjSrc (conjE L) u) x with hg`. Use `set c := conjLoc (conjE L) u with hc`. Use `set g' := GeneralLinearGroup.map c g with hg'`. Establish `e1 : (g'.val)ᵀ * (cLoc u x).val = 1` using `comp_eq x u`.

Establish `e2 : (cLoc u x).val * (g'.val)ᵀ = 1` using `mul_eq_one_comm.1 e1`. Establish `e3 : ((cLoc u x)⁻¹).val = (g'.val)ᵀ` using `Units.inv_eq_of_mul_eq_one_right e2`. Establish `e4 : (cLoc u x).valᵀ * g'.val = 1`. Use `congrArg Matrix.transpose e1` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis.

Establish `e5 : (g'⁻¹).val = (cLoc u x).valᵀ` using `Units.inv_eq_of_mul_eq_one_left e4`. Establish `e6 : (g'⁻¹).val = (GeneralLinearGroup.map c g⁻¹).val` using `by rw [map_inv]`. Use `(GlobalTheory.EulerTwKU.mem_KGL_iff_val _).2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `: (cLoc u x).val i j = c ((g⁻¹).val j i)`. Use `congrFun (congrFun (e5.symm.trans e6) j) i` as an intermediate fact.

Conclude with `this`. Rewrite using `[this, (conjLoc_spec _ u).2.2]`. Conclude with `hv.2 j i`. Establish `: ((cLoc u x)⁻¹).val i j = c (g.val j i)` using `congrFun (congrFun e3 i) j`. Rewrite using `[this, (conjLoc_spec _ u).2.2]`.

Conclude with `hv.1 j i`.
-/
private theorem K_conj (x : UA L n) (u : Plc L) (h : cLoc (conjSrc (conjE L) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE L) u) n) :
    cLoc u x ∈ GlobalTheory.LFun.KGL u n := by
  have hv := (GlobalTheory.EulerTwKU.mem_KGL_iff_val _).1 h
  set g := cLoc (conjSrc (conjE L) u) x with hg
  set c := conjLoc (conjE L) u with hc
  set g' := GeneralLinearGroup.map c g with hg'
  have e1 : (g'.val)ᵀ * (cLoc u x).val = 1 := comp_eq x u
  have e2 : (cLoc u x).val * (g'.val)ᵀ = 1 := mul_eq_one_comm.1 e1
  have e3 : ((cLoc u x)⁻¹).val = (g'.val)ᵀ := Units.inv_eq_of_mul_eq_one_right e2
  have e4 : (cLoc u x).valᵀ * g'.val = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e5 : (g'⁻¹).val = (cLoc u x).valᵀ := Units.inv_eq_of_mul_eq_one_left e4
  have e6 : (g'⁻¹).val = (GeneralLinearGroup.map c g⁻¹).val := by rw [map_inv]
  refine (GlobalTheory.EulerTwKU.mem_KGL_iff_val _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (cLoc u x).val i j = c ((g⁻¹).val j i) := by
      have := congrFun (congrFun (e5.symm.trans e6) j) i
      exact this
    rw [this, (conjLoc_spec _ u).2.2]
    exact hv.2 j i
  · have : ((cLoc u x)⁻¹).val i j = c (g.val j i) := congrFun (congrFun e3 i) j
    rw [this, (conjLoc_spec _ u).2.2]
    exact hv.1 j i

end UpperTheory.V.Z.Sym.Dict.Br.UaF

open UpperTheory.V.Z.Sym.Dict.Br.UaF in
/- English proof (translation)
Introduce `L _ _ _ n`. Use `⟨fun w hw => ?_, fun w x hx y hy => ?_, fun x => ?_, fun f hf k hk => ?_, fun x y h1 h2 => ?_, fun x => ?_, fun w x hx => cut w x hx, fun w hw x hK u hu => ?_⟩` and prove the remaining obligations. Take `⟨a, b, c, d⟩` from `UpperTheory.V.Z.Sym.Al.secSpec L n w hw`. Conclude with `⟨a, b, d, fun x hx => (c x hx).symm⟩`. Establish `hi : cInf x = 1` using `MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1`.

Use `ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `h : un u = un w`. Rewrite using `[hy u h, one_mul, mul_one]`. Establish `: cLoc u x = 1` using `MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) h)`.

Rewrite using `[this, one_mul, mul_one]`. Use `⟨fp x, fp_fin x, (fp x)⁻¹ * x, inf_of_cLoc fun u => ?_, by group⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, cLoc_fp, inv_mul_cancel]`. Establish `hi : cInf f = 1` using `hf`. Use `ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, cLoc_of_inf hk, one_mul, mul_one]`. Conclude with `ext_all (cInf_ext h2) h1`. Use `⟨⟨fun hx τ => ?_, fun h => ?_⟩, ⟨fun hx w => cLoc_of_inf hx w, inf_of_cLoc⟩⟩` and prove the remaining obligations. Establish `hi : cInf x = 1` using `hx`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (coord τ) (cInf x) = 1`.

Rewrite using `[hi, map_one]`. Express the relevant statement in the definitionally equal form `cInf x = 1`. Rewrite using `[cInf_ext (y := 1) fun τ => by rw [h τ, map_one], map_one]`. Break down `(under_iff w u).1 hu with rfl | rfl` into its components or cases. Conclude with `hK`.

Use `K_conj x _ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitPts.conjSrc_conjSrc_cm]`. Conclude with `hK`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.uaFacts :
    UAFacts := by
  intro L _ _ _ n
  refine ⟨fun w hw => ?_, fun w x hx y hy => ?_, fun x => ?_, fun f hf k hk => ?_, fun x y h1 h2 => ?_, fun x => ?_,
    fun w x hx => cut w x hx, fun w hw x hK u hu => ?_⟩
  · obtain ⟨a, b, c, d⟩ := UpperTheory.V.Z.Sym.Al.secSpec L n w hw
    exact ⟨a, b, d, fun x hx => (c x hx).symm⟩
  · have hi : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h : un u = un w
    · rw [hy u h, one_mul, mul_one]
    · have : cLoc u x = 1 := MonoidHom.mem_ker.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) h)
      rw [this, one_mul, mul_one]
  · refine ⟨fp x, fp_fin x, (fp x)⁻¹ * x, inf_of_cLoc fun u => ?_, by group⟩
    rw [map_mul, map_inv, cLoc_fp, inv_mul_cancel]
  · have hi : cInf f = 1 := hf
    refine ext_all (by rw [map_mul, map_mul, hi, one_mul, mul_one]) fun u => ?_
    rw [map_mul, map_mul, cLoc_of_inf hk, one_mul, mul_one]
  · exact ext_all (cInf_ext h2) h1
  · refine ⟨⟨fun hx τ => ?_, fun h => ?_⟩, ⟨fun hx w => cLoc_of_inf hx w, inf_of_cLoc⟩⟩
    · have hi : cInf x = 1 := hx
      change GeneralLinearGroup.map (coord τ) (cInf x) = 1
      rw [hi, map_one]
    · change cInf x = 1
      rw [cInf_ext (y := 1) fun τ => by rw [h τ, map_one], map_one]
  · rcases (under_iff w u).1 hu with rfl | rfl
    · exact hK
    · refine K_conj x _ ?_
      rw [GlobalTheory.SplitPts.conjSrc_conjSrc_cm]
      exact hK
