import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerElliptic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CentLev

/- English proof (translation)
Take `⟨Ω, hΩ, hmem⟩` from `GlobalTheory.CentCpt.main E hU n w y hs`. Use `haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space`. Establish `hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a`. Introduce `a ha b hb`. Establish `ha' : a * y = y * a` using `ha`.

Establish `hb' : b * y = y * b` using `hb`. Establish `hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val`. Use `congrArg (fun z : UL n w => (z : GLw n w).val) ha'` as an intermediate fact. Simplify using `using this`. Establish `hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val`.

Use `congrArg (fun z : UL n w => (z : GLw n w).val) hb'` as an intermediate fact. Simplify using `using this`. Use `GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv` as an intermediate fact. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `using this`. Use `⟨Ω, hΩ, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨hzT, hzc⟩` from `GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz`. Conclude with `hmem z hzT hzc`.
-/
theorem loc_cpt_part {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : UL n w) (hs : y.1.val.charpoly.Separable) :
    ∃ C : Set (UL n w), IsCompact C ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ C := by
  obtain ⟨Ω, hΩ, hmem⟩ := GlobalTheory.CentCpt.main E hU n w y hs
  haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a * y = y * a := ha
    have hb' : b * y = y * b := hb
    have hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) ha'; simpa using this
    have hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) hb'; simpa using this
    have := GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv
    apply Subtype.ext; apply Units.ext; simpa using this
  refine ⟨Ω, hΩ, fun z hz => ?_⟩
  obtain ⟨hzT, hzc⟩ := GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz
  exact hmem z hzT hzc

/- English proof (translation)
Introduce `E _ _ _ hU n hn S hS K' hK' γ hγ x`. Use `set δ : finU E n := finPt γ with hδ`. Use `set T := twCent (MonoidHom.id (finU E n)) δ with hT`. Set `ρ : ∀ w : Pl E, finU E n →* UL n w` to `fun w => { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩ map_one' := Subtype.ext (by simp) map_mul' := fun a b => Subtype.ext (by simp) }`. Establish `hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n)` using `fun _ _ => rfl`.

Establish `hρc : ∀ w, Continuous (ρ w)` using `fun w => continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)`. Establish `hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1`. Introduce `w`. Rewrite using `[hρv, hδ, FinPtLoc.finPt_eq]`. Apply `Units.ext` to reduce the goal to its premises.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)`. Rewrite using `[FinPtLoc.snd_entry]`. Both sides reduce to the same expression. Establish `hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable`.

Introduce `w`. Rewrite using `[hδw]`. Establish `e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _)` using `rfl`. Rewrite using `[e, Matrix.charpoly_map]`. Conclude with `hγ.map`.

Establish `hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU E n)) = {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))}`. Introduce `K''`. Use extensionality with `z`. Simplify using `only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]`. Use `forall₂_congr fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, e⟩`. Establish `: a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩` using `Subtype.ext e`. Rewrite using `[← this]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `⟨_, h, rfl⟩`. Establish `hKc : IsCompact (globLev S (KL n) : Set (finU E n))`. Rewrite using `[hsetK]`. Conclude with `GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w))) (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)`.

Establish `hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU E n => x * g * x⁻¹`. Use extensionality with `g`. Simplify using the standard rewrite rules. Establish `hconj : ∀ H : Subgroup (finU E n), (H.map (MulAut.conj x).toMonoidHom : Set (finU E n)) = (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU E n))`. Introduce `H`.

Use extensionality with `g`. Rewrite using `[Subgroup.coe_map, hcf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify `hk` using `[mul_assoc]`.

Introduce `h`. Conclude with `⟨_, h, by group⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨htT, htK⟩`. Apply `Subgroup.subset_closure` to reduce the goal to its premises.

Use `⟨htT, ?_⟩` and prove the remaining obligations. Establish `hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU E n))`. Rewrite using `[Subgroup.coe_map, hcf]`. Conclude with `hKc.image (by fun_prop)`. Conclude with `hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs`.

Establish `hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU E n))`. Rewrite using `[hconj]`. Conclude with `(GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)`. Use `choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)`. Establish `hcof` using `GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ`.

Set `C : ∀ w : Pl E, Set (UL n w)` to `fun w => if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w`. Establish `hCc : ∀ w, IsCompact (C w)`. Introduce `w`. Distinguish the cases in `h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w`. Simplify using `only [C, if_pos h]`.

Conclude with `(GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2`. Simplify using `only [C, if_neg h]`. Conclude with `hC0c w`. Establish `hCK : ∀ᶠ w in cofinite, C w = KL n w` using `by filter_upwards [hcof] with w hw`. Establish `e : ρ w δ = locPt w γ`.

Rewrite using `[← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]`. Both sides reduce to the same expression. Establish `hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w` using `by rw [e]; exact hw`. Simplify using `only [C, if_pos hw']`. Establish `hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w`.

Introduce `w`. Distinguish the cases in `h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w`. Simplify using `only [C, if_pos h]`. Conclude with `h`. Simplify using `only [C, if_neg h]`.

Conclude with `hC0 w`. Establish `hD` using `GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK`. Establish `hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w)`. Rewrite using `[cptPart, Subgroup.closure_le]`. Introduce and unpack `t ⟨htT, htc⟩`.

Rewrite using `[SetLike.mem_coe, Subgroup.mem_iInf]`. Introduce `w`. Rewrite using `[Subgroup.mem_comap]`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `ht' : t * δ = δ * t` using `htT show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)`. Rewrite using `[MonoidHom.id_apply, ← map_mul, ht', map_mul]`. Establish `himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU E n)))` using `htc.image (hρc w)`. Use `himc.closure_of_subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩`. Establish `hTD : (cptPart T : Set (finU E n)) ⊆ {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w}`. Introduce `z hz w _`. Establish `hzw` using `Subgroup.mem_iInf.1 (hle hz) w`. Rewrite `hzw` using `[Subgroup.mem_comap]`.

Rewrite using `[FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]`. Conclude with `hsub w hzw`. Establish `hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) : Set (cptPart T))`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hUo.preimage continuous_subtype_val`.

Establish `hfi` using `GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'`. Establish `hTc : cptPart T ≤ T` using `(Subgroup.closure_le T).2 fun t ht => ht.1`. Establish `heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) = ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T)`. Use extensionality with `z`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`.

Conclude with `⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩`. Rewrite using `[Subgroup.relIndex, heq]`. Conclude with `hfi.index_ne_zero`.
-/
theorem stab_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU E n, twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ)) ∧ (twCent (MonoidHom.id (finU E n)) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU E n)) (finPt γ))) ≠ 0 := by
  intro E _ _ _ hU n hn S hS K' hK' γ hγ x
  set δ : finU E n := finPt γ with hδ
  set T := twCent (MonoidHom.id (finU E n)) δ with hT
  let ρ : ∀ w : Pl E, finU E n →* UL n w := fun w =>
    { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n) := fun _ _ => rfl
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)
  have hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
    intro w
    rw [hρv, hδ, FinPtLoc.finPt_eq]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
    rw [FinPtLoc.snd_entry]
    rfl
  have hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable := by
    intro w
    rw [hδw]
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _) := rfl
    rw [e, Matrix.charpoly_map]
    exact hγ.map
  have hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU E n)) =
      {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))} := by
    intro K''
    ext z
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine forall₂_congr fun w _ => ?_
    rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
    constructor
    · rintro ⟨a, ha, e⟩
      have : a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩ := Subtype.ext e
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hKc : IsCompact (globLev S (KL n) : Set (finU E n)) := by
    rw [hsetK]
    exact GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w)))
      (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)
  have hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU E n => x * g * x⁻¹ := by
    ext g; simp
  have hconj : ∀ H : Subgroup (finU E n), (H.map (MulAut.conj x).toMonoidHom : Set (finU E n)) =
      (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU E n)) := by
    intro H; ext g
    rw [Subgroup.coe_map, hcf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  refine ⟨?_, ?_⟩
  · rintro t ⟨htT, htK⟩
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU E n)) := by
      rw [Subgroup.coe_map, hcf]
      exact hKc.image (by fun_prop)
    exact hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs
  · have hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU E n)) := by
      rw [hconj]
      exact (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)
    choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)
    have hcof := GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ
    let C : ∀ w : Pl E, Set (UL n w) := fun w =>
      if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w
    have hCc : ∀ w, IsCompact (C w) := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
      · simp only [C, if_neg h]; exact hC0c w
    have hCK : ∀ᶠ w in cofinite, C w = KL n w := by
      filter_upwards [hcof] with w hw
      have e : ρ w δ = locPt w γ := by
        rw [← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
        rfl
      have hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w := by rw [e]; exact hw
      simp only [C, if_pos hw']
    have hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact h
      · simp only [C, if_neg h]; exact hC0 w
    have hD := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK
    have hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w) := by
      rw [cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      intro w
      rw [Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · have ht' : t * δ = δ * t := htT
        show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)
        rw [MonoidHom.id_apply, ← map_mul, ht', map_mul]
      · have himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU E n))) := htc.image (hρc w)
        refine himc.closure_of_subset ?_
        rintro _ ⟨k, rfl⟩
        exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have hTD : (cptPart T : Set (finU E n)) ⊆
        {z : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w} := by
      intro z hz w _
      have hzw := Subgroup.mem_iInf.1 (hle hz) w
      rw [Subgroup.mem_comap] at hzw
      rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
      exact hsub w hzw
    have hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) :
        Set (cptPart T)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hUo.preimage continuous_subtype_val
    have hfi := GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'
    have hTc : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
    have heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) =
        ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩
    rw [Subgroup.relIndex, heq]
    exact hfi.index_ne_zero

end GlobalTheory.BCT.CentLev
