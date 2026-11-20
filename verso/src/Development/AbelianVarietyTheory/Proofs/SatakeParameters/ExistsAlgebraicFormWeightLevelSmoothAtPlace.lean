import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong

/- English proof (translation)
Distinguish the cases in `hsp : IsSplitAt w₀`. Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL E n w₀ hsp`. Use `⟨fun h => ((e.symm h : locU n w₀) : UA E n).1, continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩`. Rewrite using `[← he ⟨x, hx⟩]`.

Conclude with `e.symm_apply_apply _`. Simplify using `only [h1]`. Establish `hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀`. Assume the negation of the conclusion as `hne`. Conclude with `hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩`.

Establish `hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀`. Establish `h` using `GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀`. Express the relevant statement in the definitionally equal form `GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h`. Rewrite `h` using `[hc0]`. Then use the resulting hypothesis. Use `⟨fun h => finGL E n (locGL E n w₀ h), GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp, fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩` and prove the remaining obligations.
-/
theorem exists_continuous_inv_cLoc {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ ι : GL (Fin n) (w₀.adicCompletion E) → GA E n, Continuous ι ∧ ι 1 = 1 ∧
      ∀ x : UA E n, x ∈ locU n w₀ → ι (cLoc w₀ x) = x.1 := by
  by_cases hsp : IsSplitAt w₀
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w₀ hsp
    refine ⟨fun h => ((e.symm h : locU n w₀) : UA E n).1,
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩
    have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
      rw [← he ⟨x, hx⟩]
      exact e.symm_apply_apply _
    simp only [h1]
  · have hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀ := by
      by_contra hne
      exact hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩
    have hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀ := by
      have h := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀
      change GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h
      rwa [hc0] at h
    refine ⟨fun h => finGL E n (locGL E n w₀ h),
      GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp,
      fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩

/- English proof (translation)
Introduce `E _ _ _ n lam K U hK hU w₀`. Set `π : AutSub E n` to `⟨U, hU.aut⟩`. Use `set W := (AU.mk π).wt with hWdef`. Establish `hWat : ∀ τ, W.at τ = lam τ` using `fun τ => by`. Establish `h1 : (AU.mk π).HasWt τ (lam τ)` using `(AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)`.

Conclude with `hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)`. Set `M` to `π.finPart W`. Establish `hM0 : M ≠ ⊥` using `AutSub.finPart_wt_ne_bot E n π`. Establish `hV : π.V = Pairs.img (Pairs.jOf W M)` using `Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl`. Take `⟨φ, hφU, hφ0, hφK⟩` from `hU.fix`.

Use `haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1`. Set `b` to `Module.finBasis ℂ W.Sp`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by`. Rewrite using `[Pairs.range_total, ← hV]`. Conclude with `hφU`.

Set `Fx : Submodule ℂ (UA E n → ℂ)` to `{ carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ} add_mem' := fun {x y} hx hy k hk => by`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[map_add, hx k hk, hy k hk]`. Use the proof step `zero_mem' := fun k _ => map_zero _`. Use the proof step `smul_mem' := fun r ψ h k hk => by`.

Simplify using `only [Set.mem_setOf_eq] at h ⊢`. Rewrite using `[map_smul, h k hk] }`. Establish `hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx` using `fun x u hu k hk => by`. Express the relevant statement in the definitionally equal form `RU E n k (RU E n x.1 u) = RU E n x.1 u`. Rewrite using `[RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]`.

Establish `hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx` using `Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1) (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, c a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hφ0` to reduce the goal to its premises.

Rewrite using `[← hc, Pairs.total_apply]`. Simplify using `[h]`. Establish `hS : IsOpen {k : finU E n | algRep W k (c a).1 = (c a).1}` using `isSmooth_algRep W (c a).1`. Take `⟨ι, hι, hι1, hιx⟩` from `exists_continuous_inv_cLoc n w₀`. Establish `hS1 : {k : finU E n | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU E n)` using `hS.mem_nhds (by show algRep W 1 (c a).1 = (c a).1`.

Rewrite using `[map_one]`. Use the proof step `rfl)`. Rewrite `hS1` using `[nhds_subtype, Filter.mem_comap]`. Take `⟨T1, hT1, hT1S⟩` from `hS1`. Rewrite `hT1` using `[nhds_subtype, Filter.mem_comap]`.

Take `⟨T, hT, hTT1⟩` from `hT1`. Use `⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v, fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT), fun x hx hxN v g => ?_⟩` and prove the remaining obligations. Establish `hxfin : x ∈ finU E n` using `(Subgroup.mem_inf.1 hx).1`. Establish `h2 : x.1 ∈ T` using `hιx x hx ▸ hxN`. Establish `hk : (⟨x, hxfin⟩ : finU E n) ∈ {k : finU E n | algRep W k (c a).1 = (c a).1}` using `hT1S (hTT1 h2)`.

Conclude with `congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g`.
-/
theorem exists_algForm_ofType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU E n → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  intro E _ _ _ n lam K U hK hU w₀
  classical
  let π : AutSub E n := ⟨U, hU.aut⟩
  set W := (AU.mk π).wt with hWdef
  have hWat : ∀ τ, W.at τ = lam τ := fun τ => by
    have h1 : (AU.mk π).HasWt τ (lam τ) := (AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)
    exact hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)
  let M := π.finPart W
  have hM0 : M ≠ ⊥ := AutSub.finPart_wt_ne_bot E n π
  have hV : π.V = Pairs.img (Pairs.jOf W M) := Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1
  let b := Module.finBasis ℂ W.Sp
  obtain ⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by
    rw [Pairs.range_total, ← hV]
    exact hφU
  let Fx : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ}
      add_mem' := fun {x y} hx hy k hk => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, hx k hk, hy k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun r ψ h k hk => by
        simp only [Set.mem_setOf_eq] at h ⊢
        rw [map_smul, h k hk] }
  have hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx := fun x u hu k hk => by
    change RU E n k (RU E n x.1 u) = RU E n x.1 u
    rw [RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]
  have hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx := Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1)
    (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    rw [← hc, Pairs.total_apply]
    simp [h]
  have hS : IsOpen {k : finU E n | algRep W k (c a).1 = (c a).1} := isSmooth_algRep W (c a).1
  obtain ⟨ι, hι, hι1, hιx⟩ := exists_continuous_inv_cLoc n w₀
  have hS1 : {k : finU E n | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU E n) :=
    hS.mem_nhds (by
      show algRep W 1 (c a).1 = (c a).1
      rw [map_one]
      rfl)
  rw [nhds_subtype, Filter.mem_comap] at hS1
  obtain ⟨T1, hT1, hT1S⟩ := hS1
  rw [nhds_subtype, Filter.mem_comap] at hT1
  obtain ⟨T, hT, hTT1⟩ := hT1
  refine ⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v,
    fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT),
    fun x hx hxN v g => ?_⟩
  have hxfin : x ∈ finU E n := (Subgroup.mem_inf.1 hx).1
  have h2 : x.1 ∈ T := hιx x hx ▸ hxN
  have hk : (⟨x, hxfin⟩ : finU E n) ∈ {k : finU E n | algRep W k (c a).1 = (c a).1} := hT1S (hTT1 h2)
  exact congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g

end GlobalTheory.Cong

end
