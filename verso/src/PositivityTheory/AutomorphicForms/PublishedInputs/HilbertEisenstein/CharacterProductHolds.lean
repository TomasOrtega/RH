import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalCharacterUnits

open L4 GroundTheory.Automorphic.GodementSection

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pLoc_apply (w : HeightOneSpectrum (𝓞 F)) (x : Af F) : pLoc F w x = x w := rfl

/- English proof (translation)
Unfold `HChar.loc`. Rewrite using `[MonoidHom.comp_apply]`. Use `congr 3`.
-/
theorem loc_eq (ω : HChar F) (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    ((ω.loc v a : ℂˣ) : ℂ) = ((ω.1 (finiteEmbedding v a) : ℂˣ) : ℂ) := by
  unfold HChar.loc
  rw [MonoidHom.comp_apply]
  congr 3

/- English proof (translation)
Establish `h1 : Valued.v ((u : Af F) w) ≤ 1` using `h.1`. Establish `h2 : Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) ≤ 1` using `h.2`. Establish `h3 : Valued.v ((u : Af F) w) * Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) = 1`. Rewrite using `[← map_mul, units_mul_inv_apply, map_one]`. Assume the negation of the conclusion as `hne`.

Establish `hlt : Valued.v ((u : Af F) w) < 1` using `lt_of_le_of_ne h1 hne`. Establish `: Valued.v ((u : Af F) w) * Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) < 1` using `mul_lt_one_of_lt_of_le hlt h2`. Rewrite `this` using `[h3]`. Conclude with `lt_irrefl _ this`.
-/
theorem val_unit {u : (Af F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (h : IsIntegralUnitAt u w) :
    Valued.v ((u : Af F) w) = 1 := by
  have h1 : Valued.v ((u : Af F) w) ≤ 1 := h.1
  have h2 : Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) ≤ 1 := h.2
  have h3 : Valued.v ((u : Af F) w) * Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) = 1 := by
    rw [← map_mul, units_mul_inv_apply, map_one]
  by_contra hne
  have hlt : Valued.v ((u : Af F) w) < 1 := lt_of_le_of_ne h1 hne
  have : Valued.v ((u : Af F) w) * Valued.v (((u⁻¹ : (Af F)ˣ) : Af F) w) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h0` using `(H.cond w).1`. Rewrite `h0` using `[hc]`. Use `h0 (finUnitAt w b) (val_unit hb) ?_` and prove the remaining obligations. Establish `hx : ((finUnitAt w b : (w.adicCompletion F)ˣ) : w.adicCompletion F) - 1 ∈ w.adicCompletionIntegers F` using `sub_mem hb.1 (one_mem _)`. Rewrite `hx` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Simplify using `using hx`.
-/
theorem loc_unit_eq_one {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) {w : HeightOneSpectrum (𝓞 F)}
    (hc : c w = 0) {b : (Af F)ˣ} (hb : IsIntegralUnitAt b w) : ω.loc w (finUnitAt w b) = 1 := by
  have h0 := (H.cond w).1
  rw [hc] at h0
  refine h0 (finUnitAt w b) (val_unit hb) ?_
  have hx : ((finUnitAt w b : (w.adicCompletion F)ˣ) : w.adicCompletion F) - 1 ∈ w.adicCompletionIntegers F :=
    sub_mem hb.1 (one_mem _)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  simpa using hx

/- English proof (translation)
Use `set s : Af F := ∑ v ∈ S, finiteAdeleSingleAdd v (x v) with hs`. Establish `hsx : ∀ w, s w = if w ∈ S then x w else 0`. Introduce `w`. Establish `h1 : s w = ∑ v ∈ S, finiteAdeleSingleAdd v (x v) w` using `map_sum (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) w) _ _`. Rewrite using `[h1]`.

Use `split_ifs with hw`. Rewrite using `[Finset.sum_eq_single w]`. Conclude with `finiteAdeleSingleAdd_apply_self w (x w)`. Introduce `v _ hvw`. Conclude with `finiteAdeleSingleAdd_apply_of_ne (Ne.symm hvw) _`.

Introduce `h`. Conclude with `absurd hw h`. Use `Finset.sum_eq_zero fun v hv => finiteAdeleSingleAdd_apply_of_ne ?_ _` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hw hv`.

Establish `hrest : x - s ∈ finiteInvDifferent F`. Introduce `w`. Establish `h2 : (x - s) w = x w - s w` using `rfl`. Rewrite using `[h2, hsx]`. Use `split_ifs with hw`.

Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Rewrite using `[sub_zero]`. Conclude with `hx w hw`. Establish `hxs : x = s + (x - s)` using `by abel`.

Establish `hsum : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), finiteAdelicChar F (∑ v ∈ T, finiteAdeleSingleAdd v (x v)) = ∏ v ∈ T, finiteAdelicChar F (finiteAdeleSingleAdd v (x v))`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [AddChar.map_zero_eq_one]`. Consider the case `insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.

Use `conv_lhs => rw [hxs]`. Rewrite using `[AddChar.map_add_eq_mul, finiteAdelicChar_eq_one_of_mem hrest, mul_one, hs, hsum]`. Establish `h3 : ((∏ v ∈ S, finiteAdelicChar F (finiteAdeleSingleAdd v (x v)) : Circle) : ℂ) = ∏ v ∈ S, ((finiteAdelicChar F (finiteAdeleSingleAdd v (x v)) : Circle) : ℂ)` using `map_prod Circle.coeHom _ _`. Rewrite using `[h3]`. Both sides reduce to the same expression.
-/
theorem psi_split (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Af F)
    (hx : ∀ w ∉ S, x w ∈ localInvDifferent w) :
    ((finiteAdelicChar F x : Circle) : ℂ) = ∏ v ∈ S, ((localAdelicChar F v (x v) : Circle) : ℂ) := by
  classical
  set s : Af F := ∑ v ∈ S, finiteAdeleSingleAdd v (x v) with hs
  have hsx : ∀ w, s w = if w ∈ S then x w else 0 := by
    intro w
    have h1 : s w = ∑ v ∈ S, finiteAdeleSingleAdd v (x v) w :=
      map_sum (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) w) _ _
    rw [h1]
    split_ifs with hw
    · rw [Finset.sum_eq_single w]
      · exact finiteAdeleSingleAdd_apply_self w (x w)
      · intro v _ hvw
        exact finiteAdeleSingleAdd_apply_of_ne (Ne.symm hvw) _
      · intro h
        exact absurd hw h
    · refine Finset.sum_eq_zero fun v hv => finiteAdeleSingleAdd_apply_of_ne ?_ _
      rintro rfl
      exact hw hv
  have hrest : x - s ∈ finiteInvDifferent F := by
    intro w
    have h2 : (x - s) w = x w - s w := rfl
    rw [h2, hsx]
    split_ifs with hw
    · rw [sub_self]
      exact zero_mem _
    · rw [sub_zero]
      exact hx w hw
  have hxs : x = s + (x - s) := by abel
  have hsum : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), finiteAdelicChar F (∑ v ∈ T, finiteAdeleSingleAdd v (x v)) =
      ∏ v ∈ T, finiteAdelicChar F (finiteAdeleSingleAdd v (x v)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hxs]
  rw [AddChar.map_add_eq_mul, finiteAdelicChar_eq_one_of_mem hrest, mul_one, hs, hsum]
  have h3 : ((∏ v ∈ S, finiteAdelicChar F (finiteAdeleSingleAdd v (x v)) : Circle) : ℂ) =
      ∏ v ∈ S, ((finiteAdelicChar F (finiteAdeleSingleAdd v (x v)) : Circle) : ℂ) := map_prod Circle.coeHom _ _
  rw [h3]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_apply' (x y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (x * y) w = x w * y w := rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalCharacterUnits

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 LocalCharacterUnits GroundTheory.Automorphic.GodementSection

/- English proof (translation)
Introduce `F _ _ _ ω c H b S hS`. Establish `h1 : ωF ω b = ((hc ω H.fin).toIdele (ofFinite b) : ℂ)` using `(hc_toIdele ω H.fin _).symm`. Rewrite using `[h1, HeckeCharacter.toIdele_ofFinite_eq_finprod]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := S)]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[HeckeCharacter.localComponent_apply, hc_toIdele, loc_eq]`. Both sides reduce to the same expression. Introduce `v hv`. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises.

Establish `hvS' : v ∉ S` using `fun h => hvS (Finset.mem_coe.2 h)`. Use `show ((hc ω H.fin).localComponent v (finiteComponent v b) : ℂ) = 1`. Rewrite using `[HeckeCharacter.localComponent_apply, hc_toIdele, ← loc_eq]`. Use `loc_unit_eq_one H (hS v hvS').1 (hS v hvS').2` as an intermediate fact. Express the relevant statement in the definitionally equal form `((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ) = 1`.

Rewrite using `[this, Units.val_one]`.
-/
theorem character_product_holds : OmegaProd := by
  intro F _ _ _ ω c H b S hS
  classical
  have h1 : ωF ω b = ((hc ω H.fin).toIdele (ofFinite b) : ℂ) := (hc_toIdele ω H.fin _).symm
  rw [h1, HeckeCharacter.toIdele_ofFinite_eq_finprod]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [HeckeCharacter.localComponent_apply, hc_toIdele, loc_eq]
    rfl
  · intro v hv
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.2 h)
    show ((hc ω H.fin).localComponent v (finiteComponent v b) : ℂ) = 1
    rw [HeckeCharacter.localComponent_apply, hc_toIdele, ← loc_eq]
    have := loc_unit_eq_one H (hS v hvS').1 (hS v hvS').2
    change ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ) = 1
    rw [this, Units.val_one]

/- English proof (translation)
Introduce `F _ _ _ ω c H yf ξ S hS hloc`. Use `set Hs : Set (Af F)ˣ := {b | ∀ w ∉ S, finUnitAt w b ∈ intUnitsAt w} with hHs`. Use `set G : (Af F)ˣ → ℂ := Hs.indicator 1 with hGdef`. Establish `hHo : IsOpen Hs`. Rewrite using `[isOpen_iff_forall_mem_open]`.

Introduce `b hb`. Use `⟨(fun x => b⁻¹ * x) ⁻¹' (finiteIntegralUnits F : Set (Af F)ˣ), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx w hw`. Establish `hx'` using `(mem_finiteIntegralUnits_iff_forall_finUnitAt (b⁻¹ * x)).1 hx w`. Establish `h1 : finUnitAt w x = finUnitAt w b * finUnitAt w (b⁻¹ * x)`.

Rewrite using `[← map_mul, mul_inv_cancel_left]`. Rewrite using `[h1]`. Conclude with `mul_mem (hb w hw) hx'`. Conclude with `(isOpen_finiteIntegralUnits F).preimage (continuous_mul_left b⁻¹)`. Use `show b⁻¹ * b ∈ finiteIntegralUnits F`.

Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`. Establish `hGm : Measurable G` using `measurable_const.indicator hHo.measurableSet`. Establish `hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b'`. Introduce `b b' h`.

Establish `h1 : (b ∈ Hs) ↔ (b' ∈ Hs)`. Simplify using `only [hHs, Set.mem_setOf_eq]`. Conclude with `forall₂_congr fun w hw => by rw [h w hw]`. Simplify using `only [hGdef, Set.indicator_apply, h1, Pi.one_apply]`. Establish `hUG : (finUnitsAt S ⁻¹' intUnitsAtS S).indicator G = (finiteIntegralUnits F : Set (Af F)ˣ).indicator 1`.

Rewrite using `[hGdef, Set.indicator_indicator]`. Use `congr 1`. Use extensionality with `b`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, intUnitsAtS, Set.mem_pi, Set.mem_univ, true_implies, finUnitsAt_apply, hHs, Set.mem_setOf_eq, SetLike.mem_coe, mem_finiteIntegralUnits_iff_forall_finUnitAt]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩ w`. Distinguish the cases in `hw : w ∈ S`. Conclude with `h1 ⟨w, hw⟩`. Conclude with `h2 w hw`. Introduce `h`.

Conclude with `⟨fun v => h v.1, fun w _ => h w⟩`. Establish `hfin : finiteIdeleMeasure F (finiteIntegralUnits F : Set (Af F)ˣ) = 1` using `finiteIdeleMeasure_finiteIntegralUnits F`. Establish `hGi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator G) (finiteIdeleMeasure F)`. Rewrite using `[hUG, integrable_indicator_iff (isOpen_finiteIntegralUnits F).measurableSet]`. Conclude with `integrableOn_const (by rw [hfin]; exact ENNReal.one_ne_top)`.

Establish `hout : ∀ w ∉ S, ∀ b : (Af F)ˣ, (Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ)) ∧ Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F))) ≤ WithZero.exp ((c w : ℤ) + dd w)) ↔ finUnitAt w b ∈ intUnitsAt w`. Introduce `w hw b`. Take `⟨hc0, hd0, hyf, hξ⟩` from `hS w hw`. Establish `hy1` using `val_unit hyf`. Establish `hxi : ((xiF ξ : (Af F)ˣ) : Af F) = algebraMap F (Af F) (ξ : F)`.

Unfold `xiF`. Rewrite using `[Units.coe_map]`. Both sides reduce to the same expression. Establish `hξ1` using `val_unit hξ`. Rewrite `hξ1` using `[hxi]`.

Rewrite using `[finUnitAt_mem_intUnitsAt_iff, hc0, hd0]`. Simplify using `only [pLoc_apply, mul_apply', Valuation.map_mul, hy1, hξ1, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]`. Simplify using the standard rewrite rules. Establish `hpt : ∀ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ = (∏ v : S, locF ω c yf (ξ : F) v.1 (finUnitAt v.1 b)) * G b`. Introduce `b`.

Establish `hc1 : ∀ v : HeightOneSpectrum (𝓞 F), pLoc F v ((b : Af F) * (yf : Af F)) = ((finUnitAt v b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F)`. Introduce `v`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hc2 : ∀ v : HeightOneSpectrum (𝓞 F), pLoc F v (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F)) = (((finUnitAt v b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ξ : F)`.

Introduce `v`. Rewrite using `[map_mul, ← map_inv]`. Both sides reduce to the same expression. Distinguish the cases in `hb : b ∈ Hs`. Establish `hGb : G b = 1` using `by rw [hGdef, Set.indicator_of_mem hb, Pi.one_apply]`.

Rewrite using `[hGb, mul_one]`. Establish `hω : ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ)` using `character_product_holds F ω c H b S fun w hw => ⟨(hS w hw).1, hb w hw⟩`. Rewrite using `[hω, ← Finset.prod_coe_sort S, ← Finset.prod_inv_distrib]`. Simplify using `only [locF]`. Rewrite using `[Finset.prod_mul_distrib]`.

Use `congr 1`. Unfold `finK`. Use `split_ifs with hfk`. Rewrite using `[psi_split S _ fun w hw => mem_localInvDifferent_of_mem ?_]`. Rewrite using `[← Finset.prod_coe_sort S]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos ⟨by rw [← hc1]; exact hfk.1 v.1, by rw [← hc2]; exact hfk.2 v.1⟩]`. Use `congr 2`. Establish `hbw` using `hb w hw`. Establish `hξw` using `(hS w hw).2.2.2`.

Establish `hxi : ((xiF ξ : (Af F)ˣ) : Af F) = algebraMap F (Af F) (ξ : F)`. Unfold `xiF`. Rewrite using `[Units.coe_map]`. Both sides reduce to the same expression. Establish `h1 : (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F)) w = ((b⁻¹ : (Af F)ˣ) : Af F) w * ((xiF ξ : (Af F)ˣ) : Af F) w`.

Rewrite using `[hxi]`. Conclude with `mul_apply' _ _ w`. Rewrite using `[h1]`. Conclude with `mul_mem ((finUnitAt_mem_intUnitsAt_iff w b).1 hbw).2 hξw.1`. Establish `hex : ∃ v : S, ¬ (Valued.v (((finUnitAt v.1 b : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) * pLoc F v.1 (yf : Af F)) ≤ WithZero.exp (-(c v.1 : ℤ)) ∧ Valued.v ((((finUnitAt v.1 b)⁻¹ : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) * algebraMap F (v.1.adicCompletion F) (ξ : …`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hfk` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `w`.

Distinguish the cases in `hw : w ∈ S`. Rewrite using `[hc1]`. Conclude with `(hne ⟨w, hw⟩).1`. Conclude with `((hout w hw b).2 (hb w hw)).1`. Introduce `w`.

Distinguish the cases in `hw : w ∈ S`. Rewrite using `[hc2]`. Conclude with `(hne ⟨w, hw⟩).2`. Conclude with `((hout w hw b).2 (hb w hw)).2`. Take `⟨v, hv⟩` from `hex`.

Conclude with `(Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm`. Establish `hGb : G b = 0` using `by rw [hGdef, Set.indicator_of_notMem hb]`. Rewrite using `[hGb, mul_zero]`. Unfold `finK`. Rewrite using `[if_neg, zero_mul]`.

Introduce `hC`. Apply `hb` to reduce the goal to its premises. Introduce `w hw`. Conclude with `(hout w hw b).1 ⟨hC.1 w, hC.2 w⟩`. Take `⟨hi, he⟩` from `integral_finiteIdele_prod_local_mul S (fun v => locF ω c yf (ξ : F) v.1) (fun v => hloc v.1) hGm hG hGi`.

Use `⟨hi.congr (Filter.Eventually.of_forall fun b => (hpt b).symm), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt), he, hUG, integral_indicator (isOpen_finiteIntegralUnits F).measurableSet]`. Simplify using `only [Pi.one_apply]`. Rewrite using `[setIntegral_const, measureReal_def, hfin, ENNReal.toReal_one, one_smul, mul_one]`. Conclude with `Finset.prod_coe_sort S (fun v => ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F))`.
-/
theorem finite_split_holds : FinSplit := by
  intro F _ _ _ ω c H yf ξ S hS hloc
  classical
  set Hs : Set (Af F)ˣ := {b | ∀ w ∉ S, finUnitAt w b ∈ intUnitsAt w} with hHs
  set G : (Af F)ˣ → ℂ := Hs.indicator 1 with hGdef
  have hHo : IsOpen Hs := by
    rw [isOpen_iff_forall_mem_open]
    intro b hb
    refine ⟨(fun x => b⁻¹ * x) ⁻¹' (finiteIntegralUnits F : Set (Af F)ˣ), ?_, ?_, ?_⟩
    · intro x hx w hw
      have hx' := (mem_finiteIntegralUnits_iff_forall_finUnitAt (b⁻¹ * x)).1 hx w
      have h1 : finUnitAt w x = finUnitAt w b * finUnitAt w (b⁻¹ * x) := by
        rw [← map_mul, mul_inv_cancel_left]
      rw [h1]
      exact mul_mem (hb w hw) hx'
    · exact (isOpen_finiteIntegralUnits F).preimage (continuous_mul_left b⁻¹)
    · show b⁻¹ * b ∈ finiteIntegralUnits F
      rw [inv_mul_cancel]
      exact one_mem _
  have hGm : Measurable G := measurable_const.indicator hHo.measurableSet
  have hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b' := by
    intro b b' h
    have h1 : (b ∈ Hs) ↔ (b' ∈ Hs) := by
      simp only [hHs, Set.mem_setOf_eq]
      exact forall₂_congr fun w hw => by rw [h w hw]
    simp only [hGdef, Set.indicator_apply, h1, Pi.one_apply]
  have hUG : (finUnitsAt S ⁻¹' intUnitsAtS S).indicator G =
      (finiteIntegralUnits F : Set (Af F)ˣ).indicator 1 := by
    rw [hGdef, Set.indicator_indicator]
    congr 1
    ext b
    simp only [Set.mem_inter_iff, Set.mem_preimage, intUnitsAtS, Set.mem_pi, Set.mem_univ, true_implies,
      finUnitsAt_apply, hHs, Set.mem_setOf_eq, SetLike.mem_coe, mem_finiteIntegralUnits_iff_forall_finUnitAt]
    constructor
    · rintro ⟨h1, h2⟩ w
      by_cases hw : w ∈ S
      · exact h1 ⟨w, hw⟩
      · exact h2 w hw
    · intro h
      exact ⟨fun v => h v.1, fun w _ => h w⟩
  have hfin : finiteIdeleMeasure F (finiteIntegralUnits F : Set (Af F)ˣ) = 1 := finiteIdeleMeasure_finiteIntegralUnits F
  have hGi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator G) (finiteIdeleMeasure F) := by
    rw [hUG, integrable_indicator_iff (isOpen_finiteIntegralUnits F).measurableSet]
    exact integrableOn_const (by rw [hfin]; exact ENNReal.one_ne_top)

  have hout : ∀ w ∉ S, ∀ b : (Af F)ˣ,
      (Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F))) ≤
          WithZero.exp ((c w : ℤ) + dd w)) ↔ finUnitAt w b ∈ intUnitsAt w := by
    intro w hw b
    obtain ⟨hc0, hd0, hyf, hξ⟩ := hS w hw
    have hy1 := val_unit hyf
    have hxi : ((xiF ξ : (Af F)ˣ) : Af F) = algebraMap F (Af F) (ξ : F) := by
      unfold xiF
      rw [Units.coe_map]
      rfl
    have hξ1 := val_unit hξ
    rw [hxi] at hξ1
    rw [finUnitAt_mem_intUnitsAt_iff, hc0, hd0]
    simp only [pLoc_apply, mul_apply', Valuation.map_mul, hy1, hξ1, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
    simp
  have hpt : ∀ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ =
      (∏ v : S, locF ω c yf (ξ : F) v.1 (finUnitAt v.1 b)) * G b := by
    intro b
    have hc1 : ∀ v : HeightOneSpectrum (𝓞 F), pLoc F v ((b : Af F) * (yf : Af F)) =
        ((finUnitAt v b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F) := by
      intro v
      rw [map_mul]
      rfl
    have hc2 : ∀ v : HeightOneSpectrum (𝓞 F), pLoc F v (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F)) =
        (((finUnitAt v b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ξ : F) := by
      intro v
      rw [map_mul, ← map_inv]
      rfl
    by_cases hb : b ∈ Hs
    · have hGb : G b = 1 := by rw [hGdef, Set.indicator_of_mem hb, Pi.one_apply]
      rw [hGb, mul_one]
      have hω : ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ) :=
        character_product_holds F ω c H b S fun w hw => ⟨(hS w hw).1, hb w hw⟩
      rw [hω, ← Finset.prod_coe_sort S, ← Finset.prod_inv_distrib]
      simp only [locF]
      rw [Finset.prod_mul_distrib]
      congr 1
      unfold finK
      split_ifs with hfk
      · rw [psi_split S _ fun w hw => mem_localInvDifferent_of_mem ?_]
        · rw [← Finset.prod_coe_sort S]
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [if_pos ⟨by rw [← hc1]; exact hfk.1 v.1, by rw [← hc2]; exact hfk.2 v.1⟩]
          congr 2
        · have hbw := hb w hw
          have hξw := (hS w hw).2.2.2
          have hxi : ((xiF ξ : (Af F)ˣ) : Af F) = algebraMap F (Af F) (ξ : F) := by
            unfold xiF
            rw [Units.coe_map]
            rfl
          have h1 : (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) (ξ : F)) w =
              ((b⁻¹ : (Af F)ˣ) : Af F) w * ((xiF ξ : (Af F)ˣ) : Af F) w := by
            rw [hxi]
            exact mul_apply' _ _ w
          rw [h1]
          exact mul_mem ((finUnitAt_mem_intUnitsAt_iff w b).1 hbw).2 hξw.1
      · have hex : ∃ v : S, ¬ (Valued.v (((finUnitAt v.1 b : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) *
            pLoc F v.1 (yf : Af F)) ≤ WithZero.exp (-(c v.1 : ℤ)) ∧
            Valued.v ((((finUnitAt v.1 b)⁻¹ : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) *
              algebraMap F (v.1.adicCompletion F) (ξ : F)) ≤ WithZero.exp ((c v.1 : ℤ) + dd v.1)) := by
          by_contra hne
          push_neg at hne
          apply hfk
          constructor
          · intro w
            by_cases hw : w ∈ S
            · rw [hc1]
              exact (hne ⟨w, hw⟩).1
            · exact ((hout w hw b).2 (hb w hw)).1
          · intro w
            by_cases hw : w ∈ S
            · rw [hc2]
              exact (hne ⟨w, hw⟩).2
            · exact ((hout w hw b).2 (hb w hw)).2
        obtain ⟨v, hv⟩ := hex
        exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm
    · have hGb : G b = 0 := by rw [hGdef, Set.indicator_of_notMem hb]
      rw [hGb, mul_zero]
      unfold finK
      rw [if_neg, zero_mul]
      intro hC
      apply hb
      intro w hw
      exact (hout w hw b).1 ⟨hC.1 w, hC.2 w⟩
  obtain ⟨hi, he⟩ := integral_finiteIdele_prod_local_mul S (fun v => locF ω c yf (ξ : F) v.1) (fun v => hloc v.1)
    hGm hG hGi
  refine ⟨hi.congr (Filter.Eventually.of_forall fun b => (hpt b).symm), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), he, hUG,
    integral_indicator (isOpen_finiteIntegralUnits F).measurableSet]
  simp only [Pi.one_apply]
  rw [setIntegral_const, measureReal_def, hfin, ENNReal.toReal_one, one_smul, mul_one]
  exact Finset.prod_coe_sort S (fun v => ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
