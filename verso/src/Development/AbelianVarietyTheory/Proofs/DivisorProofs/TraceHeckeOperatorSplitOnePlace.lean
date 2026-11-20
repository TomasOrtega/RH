import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnOfNotFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.Peel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite`. Establish `h` using `(GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf`. Rewrite `h` using `[Filter.eventually_cofinite]`. Use `h.subset ?_` and prove the remaining obligations. Introduce and unpack `u hu ⟨h1, h2⟩`.

Apply `hu` to reduce the goal to its premises. Use `show f u _ = 1`. Rewrite using `[h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]`. Both sides reduce to the same expression. Unfold `globFn`.

Use `conv_lhs => rw [← Set.insert_diff_self_of_mem hw]`. Conclude with `finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)`.
-/
theorem globFn_eq (hU : Unr E) {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) {w : Pl E} (hw : w ∈ S) (x : finU E n) :
    globFn S f x = f w (toSub _ (cLoc w x.1)) * ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1)) := by
  have hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u hu ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  conv_lhs => rw [← Set.insert_diff_self_of_mem hw]
  exact finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)

/- English proof (translation)
Introduce `E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ`. Take `⟨e, he⟩` from `LocCompU.exists_equiv hU n w`. Set `ι : UL n w →* finU E n` to `(Subgroup.inclusion (inf_le_left : locU n w ≤ finU E n)).comp e.toMulEquiv.symm.toMonoidHom`. Set `r : finU E n →* UL n w` to `((cLoc w).comp (finU E n).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1`. Establish `hιw : ∀ h, cLoc w (ι h).1 = h.1` using `fun h => by`.

Express the relevant statement in the definitionally equal form `cLoc w ((e.symm h : locU n w) : UA E n) = _`. Rewrite using `[← he, e.apply_symm_apply]`. Establish `hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1` using `fun h u hu huw => by`. Take `⟨v, -, hv⟩` from `hS w`. Conclude with `GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)`.

Establish `hr : ∀ h, r (ι h) = h` using `fun h => Subtype.ext (hιw h)`. Establish `hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h)` using `fun x hx h => by`. Establish `h1 : cLoc w x.1 = 1` using `congrArg Subtype.val (MonoidHom.mem_ker.1 hx)`. Establish `h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_one]`. Use `Subtype.ext ((he _).trans ?_)` and prove the remaining obligations. Conclude with `(GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1`. Establish `h3` using `GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)`. Rewrite `h3` using `[h2, OneMemClass.coe_one, inv_one, one_mul]`.

Conclude with `Subtype.ext h3.eq`. Establish `hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K'` using `fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by`. Distinguish the cases in `huw : u = w`. Substitute `huw` using the available equality. Establish `: (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k` using `Subtype.ext (hιw k)`.

Rewrite using `[this]` and apply the resulting hypothesis. Establish `: (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1` using `Subtype.ext (hιu k u hu huw)`. Rewrite using `[this]`. Conclude with `one_mem _`. Establish `hK2 : ∀ k ∈ globLev S K', r k ∈ K' w` using `fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw`.

Take `⟨hind, h0, -⟩` from `GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ`. Use `set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'`. Establish `hf' : IsTest (KL n) K' (Function.update f w a')`. Use `⟨fun u => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `huw : u = w`.

Substitute `huw` using the available equality. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne huw]`. Conclude with `hf.1 u`. Use `filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2`.

Rewrite using `[Function.update_of_ne h2]` and apply the resulting hypothesis. Set `b : r.ker → ℂ` to `fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))`. Establish `hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) → ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x` using `fun g hg hgf h x => by`. Rewrite using `[globFn_eq hU hg.2 hw]`. Establish `h1 : cLoc w x.1.1 = 1` using `congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)`.

Use `congr 1`. Rewrite using `[Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dif_pos h.2]`. Use `finprod_mem_congr rfl fun u hu => ?_` and prove the remaining obligations. Rewrite using `[hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]`. Establish `hF` using `hsplit f hf fun _ _ => rfl`.

Establish `hF'` using `hsplit _ hf' fun u hu => Function.update_of_ne hu _ _`. Simplify using `only [Function.update_self] at hF'`. Establish `hH` using `GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf`. Establish `hH'` using `GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'`. Establish `hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x` using `fun x => by`.

Use `hF' 1 x` as an intermediate fact. Rewrite `this` using `[map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul]`. Conclude with `this.symm`. Establish `hopen` using `(GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1`. Establish `hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite`.

Use `Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU E n) : finU E n ⧸ globLev S K')) ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU E n)`. Express the relevant statement in the definitionally equal form `globFn S _ _ ≠ 0`. Rewrite using `[hk, (hH'.2 _ k.2 _).2, ← hb]`.

Conclude with `hq`. Establish `h' : ((((p.out : r.ker) : finU E n)) : finU E n ⧸ globLev S K') = ((q.out : r.ker) : finU E n)` using `h`. Rewrite using `[← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]`. Use `QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)` and prove the remaining obligations. Use `QuotientGroup.eq.1 h'` as an intermediate fact.

Simplify using `using this`. Use `haveI := σ.irred`. Establish `hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι)`. Take `⟨p, hp, -, φ, hφ0, hφm, hφ⟩` from `hσ`. Establish `hpe : ∀ g, p (e.symm g) = g` using `fun g => Subtype.ext ((hp _).trans (hιw g))`.

Set `π' : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`. Set `s : UL n w →* UA E n` to `(finU E n).subtype.comp ι`. Set `Φ : σ.ρ.IntertwiningMap (π'.rep.comp s)` to `⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by`. Use `hφ (e.symm g) v` as an intermediate fact. Rewrite `this` using `[hpe]`.

Conclude with `this)⟩`. Establish `hΦ0 : Φ ≠ 0` using `fun h => hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))`. Take `⟨h1, -⟩` from `GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by`. Establish `h3` using `GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)`. Establish `h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g`.

Express the relevant statement in the definitionally equal form `((e.symm (e _) : locU n w) : UA E n) = _`. Rewrite using `[e.symm_apply_apply]`. Rewrite using `[h4]`. Conclude with `h3⟩) Φ hΦ0`. Introduce `v hv`.

Establish `hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤ (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype`. Use `iSup_le fun ψ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y => congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ : σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩`. Rewrite `hle` using `[h1]`.

Conclude with `hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)`. Conclude with `trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _ (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2 (fun k hk x => by`. Rewrite using `[hb, hb, hb]`. Conclude with `hH'.2 _ hk _)`. Use the proof step `(GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin`.
-/
theorem trOn_hop_peel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  intro E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ
  obtain ⟨e, he⟩ := LocCompU.exists_equiv hU n w
  let ι : UL n w →* finU E n := (Subgroup.inclusion (inf_le_left : locU n w ≤ finU E n)).comp
    e.toMulEquiv.symm.toMonoidHom
  let r : finU E n →* UL n w := ((cLoc w).comp (finU E n).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1
  have hιw : ∀ h, cLoc w (ι h).1 = h.1 := fun h => by
    change cLoc w ((e.symm h : locU n w) : UA E n) = _
    rw [← he, e.apply_symm_apply]
  have hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1 := fun h u hu huw => by
    obtain ⟨v, -, hv⟩ := hS w
    exact GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)
  have hr : ∀ h, r (ι h) = h := fun h => Subtype.ext (hιw h)
  have hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h) := fun x hx h => by
    have h1 : cLoc w x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1 := by
      apply e.injective
      rw [map_one]
      refine Subtype.ext ((he _).trans ?_)
      exact (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1
    have h3 := GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)
    rw [h2, OneMemClass.coe_one, inv_one, one_mul] at h3
    exact Subtype.ext h3.eq
  have hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K' := fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by
    by_cases huw : u = w
    · subst huw
      have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k := Subtype.ext (hιw k)
      rwa [this]
    · have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1 := Subtype.ext (hιu k u hu huw)
      rw [this]
      exact one_mem _
  have hK2 : ∀ k ∈ globLev S K', r k ∈ K' w := fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw
  obtain ⟨hind, h0, -⟩ := GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ
  set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'
  have hf' : IsTest (KL n) K' (Function.update f w a') := by
    refine ⟨fun u => ?_, ?_⟩
    · by_cases huw : u = w
      · subst huw
        rwa [Function.update_self]
      · rw [Function.update_of_ne huw]
        exact hf.1 u
    · filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2
      rwa [Function.update_of_ne h2]
  let b : r.ker → ℂ := fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))
  have hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) →
      ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x := fun g hg hgf h x => by
    rw [globFn_eq hU hg.2 hw]
    have h1 : cLoc w x.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
    congr 1
    · rw [Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dif_pos h.2]
    · refine finprod_mem_congr rfl fun u hu => ?_
      rw [hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]
  have hF := hsplit f hf fun _ _ => rfl
  have hF' := hsplit _ hf' fun u hu => Function.update_of_ne hu _ _
  simp only [Function.update_self] at hF'
  have hH := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hH' := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'
  have hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x := fun x => by
    have := hF' 1 x
    rw [map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul] at this
    exact this.symm
  have hopen := (GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1
  have hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU E n) : finU E n ⧸ globLev S K'))
      ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU E n)
      change globFn S _ _ ≠ 0
      rw [hk, (hH'.2 _ k.2 _).2, ← hb]
      exact hq
    · have h' : ((((p.out : r.ker) : finU E n)) : finU E n ⧸ globLev S K') = ((q.out : r.ker) : finU E n) := h
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := QuotientGroup.eq.1 h'
      simpa using this
  haveI := σ.irred
  have hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι) := by
    obtain ⟨p, hp, -, φ, hφ0, hφm, hφ⟩ := hσ
    have hpe : ∀ g, p (e.symm g) = g := fun g => Subtype.ext ((hp _).trans (hιw g))
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let s : UL n w →* UA E n := (finU E n).subtype.comp ι
    let Φ : σ.ρ.IntertwiningMap (π'.rep.comp s) :=
      ⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by
        have := hφ (e.symm g) v
        rw [hpe] at this
        exact this)⟩
    have hΦ0 : Φ ≠ 0 := fun h =>
      hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨h1, -⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep
      σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by
        have h3 := GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)
        have h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g := by
          change ((e.symm (e _) : locU n w) : UA E n) = _
          rw [e.symm_apply_apply]
        rw [h4]
        exact h3⟩) Φ hΦ0
    intro v hv
    have hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤
        (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype := by
      refine iSup_le fun ψ => ?_
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y =>
        congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ :
          σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩
    rw [h1] at hle
    exact hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)
  exact trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _
    (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2
    (fun k hk x => by
      rw [hb, hb, hb]
      exact hH'.2 _ hk _)
    (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin

end GlobalTheory.BCT.Peel
