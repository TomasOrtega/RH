import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.CofinalityAlt

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GLnLocal

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable abbrev fp (x : UA L n) : GL (Fin n) (Af L) :=
  Matrix.GeneralLinearGroup.map (pFin L) (x : GA L n)

/- English proof (translation)
The claim follows from `continuous_mapFin.comp continuous_subtype_val`.
-/
private theorem cont_fp : Continuous (fp : UA L n → GL (Fin n) (Af L)) :=
  continuous_mapFin.comp continuous_subtype_val

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Rewrite using `[finiteRestrictedEquiv_apply]`. Both sides reduce to the same expression.
-/
private theorem e_apply (w : Plc L) (x : UA L n) : finiteRestrictedEquiv L n (fp x) w = cLoc w x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [finiteRestrictedEquiv_apply]
  rfl

/- English proof (translation)
Establish `e : (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) = fun x => finiteRestrictedEquiv L n (fp x) w` using `funext fun x => (e_apply w x).symm`. Rewrite using `[e]`. Conclude with `(RestrictedProduct.continuous_eval w).comp ((finiteRestrictedEquiv L n).continuous.comp cont_fp)`.
-/
private theorem cont_cLoc (w : Plc L) : Continuous (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) := by
  have e : (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) =
      fun x => finiteRestrictedEquiv L n (fp x) w := funext fun x => (e_apply w x).symm
  rw [e]
  exact (RestrictedProduct.continuous_eval w).comp ((finiteRestrictedEquiv L n).continuous.comp cont_fp)

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun a b => by rw [prodEquiv_apply_snd]; rfl)`.
-/
private theorem snd_eq (x : UA L n) : (prodEquiv L n (x : GA L n)).2 = fp x :=
  Units.ext (Matrix.ext fun a b => by rw [prodEquiv_apply_snd]; rfl)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Rewrite using `[prodEquiv_apply_fst]`. Establish `key` using `congrArg (fun g : GL (Fin n) (Cinf L) => g.1 a b) (MonoidHom.mem_ker.1 x.2)`. Use `(infEq L).symm.injective (key.trans ?_)` and prove the remaining obligations. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.
-/
private theorem fst_eq (x : finU L n) : (prodEquiv L n ((x : UA L n) : GA L n)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [prodEquiv_apply_fst]
  have key := congrArg (fun g : GL (Fin n) (Cinf L) => g.1 a b) (MonoidHom.mem_ker.1 x.2)
  refine (infEq L).symm.injective (key.trans ?_)
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

/- English proof (translation)
Simplify using `[Kall, Subgroup.mem_inf, Subgroup.mem_iInf]`.
-/
private theorem mem_Kall {x : UA L n} :
    x ∈ Kall L n ↔ x ∈ finU L n ∧ ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w n := by
  simp [Kall, Subgroup.mem_inf, Subgroup.mem_iInf]

/- English proof (translation)
Take `⟨A, hA, eA⟩` from `isOpen_induced_iff.1 hU`. Take `⟨B, hB, rfl⟩` from `isOpen_induced_iff.1 hA`. Set `c : GL (Fin n) (Af L) → GA L n` to `fun k => (prodEquiv L n).symm (1, k)`. Establish `hc : Continuous c` using `(prodEquiv L n).symm.continuous.comp (continuous_const.prodMk continuous_id)`. Establish `hx : ∀ x : finU L n, c (fp x.1) = ((x : UA L n) : GA L n)` using `fun x => by`.

Express the relevant statement in the definitionally equal form `(prodEquiv L n).symm _ = _`. Rewrite using `[← fst_eq x, ← snd_eq]`. Conclude with `(prodEquiv L n).symm_apply_apply _`. Establish `hmem : ∀ x : finU L n, (x : UA L n) ∈ U ↔ ((x : UA L n) : GA L n) ∈ B` using `fun x => (Set.ext_iff.1 eA x).symm`. Use `⟨c ⁻¹' B, hB.preimage hc, ?_, fun x hx' => ?_⟩` and prove the remaining obligations.

Establish `h` using `hx 1`. Establish `h1 : fp ((1 : finU L n) : UA L n) = 1` using `map_one _`. Rewrite `h` using `[h1]`. Rewrite using `[Set.mem_preimage, h]`. Conclude with `(hmem 1).1 (one_mem U)`.

Rewrite `hx'` using `[Set.mem_preimage, hx]`. Conclude with `(hmem x).2 hx'`.
-/
private theorem exists_open {U : Subgroup (UA L n)} (hU : IsOpen {x : finU L n | (x : UA L n) ∈ U}) :
    ∃ O : Set (GL (Fin n) (Af L)), IsOpen O ∧ 1 ∈ O ∧ ∀ x : finU L n, fp x.1 ∈ O → (x : UA L n) ∈ U := by
  obtain ⟨A, hA, eA⟩ := isOpen_induced_iff.1 hU
  obtain ⟨B, hB, rfl⟩ := isOpen_induced_iff.1 hA
  let c : GL (Fin n) (Af L) → GA L n := fun k => (prodEquiv L n).symm (1, k)
  have hc : Continuous c := (prodEquiv L n).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : ∀ x : finU L n, c (fp x.1) = ((x : UA L n) : GA L n) := fun x => by
    change (prodEquiv L n).symm _ = _
    rw [← fst_eq x, ← snd_eq]
    exact (prodEquiv L n).symm_apply_apply _
  have hmem : ∀ x : finU L n, (x : UA L n) ∈ U ↔ ((x : UA L n) : GA L n) ∈ B := fun x =>
    (Set.ext_iff.1 eA x).symm
  refine ⟨c ⁻¹' B, hB.preimage hc, ?_, fun x hx' => ?_⟩
  · have h := hx 1
    have h1 : fp ((1 : finU L n) : UA L n) = 1 := map_one _
    rw [h1] at h
    rw [Set.mem_preimage, h]
    exact (hmem 1).1 (one_mem U)
  · rw [Set.mem_preimage, hx] at hx'
    exact (hmem x).2 hx'

/- English proof (translation)
Set `e` to `finiteRestrictedEquiv L n`. Set `s` to `RestrictedProduct.structureMap (fun v : Plc L => GL (Fin n) (v.adicCompletion L)) (fun v => (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) Filter.cofinite`. Establish `hs : Continuous fun a => e.symm (s a)` using `e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous`. Establish `hone : e.symm (s fun v => ⟨1, one_mem _⟩) = 1`. Establish `: s (fun v => ⟨1, one_mem _⟩) = 1` using `rfl`.

Rewrite using `[this, map_one]`. Take `⟨T, u, hu, hT⟩` from `isOpen_pi_iff.1 (hO.preimage hs) (fun v => ⟨1, one_mem _⟩) (by rw [Set.mem_preimage, hone]; exact h1)`. Use `⟨T, fun g hg hgT => ?_⟩` and prove the remaining obligations. Establish `hint` using `(mem_integralFiniteGL_iff_forall L n).1 hg`. Establish `hg' : e.symm (s fun v => ⟨e g v, hint v⟩) = g`.

Establish `: s (fun v => ⟨e g v, hint v⟩) = e g`. Use extensionality with `v`. Both sides reduce to the same expression. Rewrite using `[this, e.symm_apply_apply]`. Rewrite using `[← hg']`.

Use `hT fun v hv => ?_` and prove the remaining obligations. Establish `: (⟨e g v, hint v⟩ : (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) = ⟨1, one_mem _⟩` using `Subtype.ext (hgT v hv)`. Rewrite using `[this]`. Conclude with `(hu v hv).2`.
-/
private theorem nbhd {O : Set (GL (Fin n) (Af L))} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ T : Finset (Plc L), ∀ g : GL (Fin n) (Af L), g ∈ integralFiniteGL L n →
      (∀ v ∈ T, finiteRestrictedEquiv L n g v = 1) → g ∈ O := by
  let e := finiteRestrictedEquiv L n
  let s := RestrictedProduct.structureMap (fun v : Plc L => GL (Fin n) (v.adicCompletion L))
    (fun v => (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) Filter.cofinite
  have hs : Continuous fun a => e.symm (s a) :=
    e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hone : e.symm (s fun v => ⟨1, one_mem _⟩) = 1 := by
    have : s (fun v => ⟨1, one_mem _⟩) = 1 := rfl
    rw [this, map_one]
  obtain ⟨T, u, hu, hT⟩ := isOpen_pi_iff.1 (hO.preimage hs) (fun v => ⟨1, one_mem _⟩)
    (by rw [Set.mem_preimage, hone]; exact h1)
  refine ⟨T, fun g hg hgT => ?_⟩
  have hint := (mem_integralFiniteGL_iff_forall L n).1 hg
  have hg' : e.symm (s fun v => ⟨e g v, hint v⟩) = g := by
    have : s (fun v => ⟨e g v, hint v⟩) = e g := by
      ext v
      rfl
    rw [this, e.symm_apply_apply]
  rw [← hg']
  refine hT fun v hv => ?_
  have : (⟨e g v, hint v⟩ : (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) = ⟨1, one_mem _⟩ :=
    Subtype.ext (hgT v hv)
  rw [this]
  exact (hu v hv).2

/- English proof (translation)
The claim follows from `(mem_integralFiniteGL_iff_forall L n).2 fun v => by rw [e_apply] exact GlobalTheory.StabInt.mem_integralGL_of_mem_KGL (hx v)`.
-/
private theorem fp_mem {x : UA L n} (hx : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w n) :
    fp x ∈ integralFiniteGL L n :=
  (mem_integralFiniteGL_iff_forall L n).2 fun v => by
    rw [e_apply]
    exact GlobalTheory.StabInt.mem_integralGL_of_mem_KGL (hx v)

/- English proof (translation)
Take `⟨O, hO, h1, hOU⟩` from `exists_open hU`. Take `⟨T, hT⟩` from `nbhd hO h1`. Use `⟨T, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨hK, hA⟩` from `Subgroup.mem_inf.1 hx`. Take `⟨hf, hi⟩` from `mem_Kall.1 hK`.

Use `hOU ⟨x, hf⟩ (hT _ (fp_mem hi) fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[e_apply]`. Establish `h` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA v) hv`. Conclude with `MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h v) rfl)`.
-/
private theorem clause1 (U : Subgroup (UA L n)) (hU : IsOpen {x : finU L n | (x : UA L n) ∈ U}) :
    ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U := by
  obtain ⟨O, hO, h1, hOU⟩ := exists_open hU
  obtain ⟨T, hT⟩ := nbhd hO h1
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hf, hi⟩ := mem_Kall.1 hK
  refine hOU ⟨x, hf⟩ (hT _ (fp_mem hi) fun v hv => ?_)
  rw [e_apply]
  have h := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA v) hv
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h v) rfl)

/- English proof (translation)
Use `⟨le_rfl, ?_⟩` and prove the remaining obligations. Establish `e : {x : finU L n | (x : UA L n) ∈ Kall L n} = (fun x : finU L n => fp x.1) ⁻¹' (integralFiniteGL L n : Set (GL (Fin n) (Af L)))`. Use extensionality with `x`. Use `⟨fun h => fp_mem (mem_Kall.1 h).2, fun h => mem_Kall.2 ⟨x.2, fun w => ?_⟩⟩` and prove the remaining obligations. Establish `h'` using `(mem_integralFiniteGL_iff_forall L n).1 h w`.

Rewrite `h'` using `[e_apply]`. Conclude with `GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h'`. Rewrite using `[e]`. Conclude with `(isOpen_integralFiniteGL L n).preimage (cont_fp.comp continuous_subtype_val)`.
-/
private theorem clause2 : IsLevel (Kall L n) := by
  refine ⟨le_rfl, ?_⟩
  have e : {x : finU L n | (x : UA L n) ∈ Kall L n} =
      (fun x : finU L n => fp x.1) ⁻¹' (integralFiniteGL L n : Set (GL (Fin n) (Af L))) := by
    ext x
    refine ⟨fun h => fp_mem (mem_Kall.1 h).2, fun h => mem_Kall.2 ⟨x.2, fun w => ?_⟩⟩
    have h' := (mem_integralFiniteGL_iff_forall L n).1 h w
    rw [e_apply] at h'
    exact GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h'
  rw [e]
  exact (isOpen_integralFiniteGL L n).preimage (cont_fp.comp continuous_subtype_val)

/- English proof (translation)
Use `⟨inf_le_left.trans hU.1, ?_⟩` and prove the remaining obligations. Establish `e : {x : finU L n | (x : UA L n) ∈ lev U S V} = {x : finU L n | (x : UA L n) ∈ U} ∩ ⋂ w ∈ S, (fun x : finU L n => cLoc w (x : UA L n)) ⁻¹' ((V w).J n : Set (GL (Fin n) (Kw w)))`. Use extensionality with `x`. Simplify using `[lev, Subgroup.mem_inf, Subgroup.mem_iInf]`. Rewrite using `[e]`.

Conclude with `hU.2.inter (isOpen_biInter_finset fun w _ => ((Sig.finFacts _ (V w)).2.2.2.2.2 n).2.1.preimage ((cont_cLoc w).comp continuous_subtype_val))`.
-/
private theorem clause3 (U : Subgroup (UA L n)) (hU : IsLevel U) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) : IsLevel (lev U S V) := by
  refine ⟨inf_le_left.trans hU.1, ?_⟩
  have e : {x : finU L n | (x : UA L n) ∈ lev U S V} = {x : finU L n | (x : UA L n) ∈ U} ∩
      ⋂ w ∈ S, (fun x : finU L n => cLoc w (x : UA L n)) ⁻¹' ((V w).J n : Set (GL (Fin n) (Kw w))) := by
    ext x
    simp [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [e]
  exact hU.2.inter (isOpen_biInter_finset fun w _ =>
    ((Sig.finFacts _ (V w)).2.2.2.2.2 n).2.1.preimage ((cont_cLoc w).comp continuous_subtype_val))

/- English proof (translation)
Take `⟨T, hT⟩` from `clause1 U hU.2`. Establish `hfin : ∀ t : Plc L, {w : Plc L | w.under (𝓞 (Lp L)) = t.under (𝓞 (Lp L))}.Finite` using `fun t => ((IsDedekindDomain.primesOver_finite (t.under (𝓞 (Lp L))).asIdeal (𝓞 L)).preimage (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩`. Use `Filter.eventually_cofinite.2 ((T.finite_toSet.biUnion fun t _ => hfin t).subset fun w hw => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Use `hw fun x hx => hT ?_` and prove the remaining obligations.

Take `⟨hl, hK⟩` from `Subgroup.mem_inf.1 hx`. Use `Subgroup.mem_inf.2 ⟨hK, Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u) fun huw => hn ?_` and prove the remaining obligations. Conclude with `Set.mem_biUnion (Finset.mem_coe.2 ht) (huw.symm.trans hu)`.
-/
private theorem clause4 (U : Subgroup (UA L n)) (hU : IsLevel U) :
    ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  obtain ⟨T, hT⟩ := clause1 U hU.2
  have hfin : ∀ t : Plc L, {w : Plc L | w.under (𝓞 (Lp L)) = t.under (𝓞 (Lp L))}.Finite := fun t =>
    ((IsDedekindDomain.primesOver_finite (t.under (𝓞 (Lp L))).asIdeal (𝓞 L)).preimage
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet.biUnion fun t _ => hfin t).subset fun w hw => ?_)
  by_contra hn
  refine hw fun x hx => hT ?_
  obtain ⟨hl, hK⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hK, Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  refine Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u) fun huw => hn ?_
  exact Set.mem_biUnion (Finset.mem_coe.2 ht) (huw.symm.trans hu)

end UpperTheory.V.Z.Sym.Al.CofinalityAlt

open UpperTheory.V.Z.Sym.Al.CofinalityAlt in
/- English proof (translation)
Introduce `L _ _ _ n`. Conclude with `⟨clause1, clause2, clause3, clause4⟩`.
-/
theorem UpperTheory.V.Z.Sym.Al.cof :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ),
        (∀ U : Subgroup (UA L n), IsOpen {x : finU L n | (x : UA L n) ∈ U} → ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U) ∧
        IsLevel (Kall L n) ∧ (∀ U : Subgroup (UA L n), IsLevel U → ∀ S V, IsLevel (lev U S V)) ∧
        ∀ U : Subgroup (UA L n), IsLevel U → ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  intro L _ _ _ n
  exact ⟨clause1, clause2, clause3, clause4⟩
