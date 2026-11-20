import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealCountLeOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalIdealOfCountLeOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderExistsUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralIndicatorGeometricStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.UnrTate

open Formalism.L2.Host (aboveF finite_aboveF)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.T.local_ideal_count_le_order v 𝔞 x, GlobalTheory.T.mem_local_ideal_of_count_le_order v 𝔞 h𝔞 x⟩`.
-/
theorem memLocId_iff (v : Pl F) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) (x : (Fv F v ⊗[F] E)ˣ) :
    (x : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞 ↔ ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 ≤ ordAt v w x :=
  ⟨GlobalTheory.T.local_ideal_count_le_order v 𝔞 x, GlobalTheory.T.mem_local_ideal_of_count_le_order v 𝔞 h𝔞 x⟩

/- English proof (translation)
The claim follows from `GlobalTheory.T.absEv_eq_prod_norm_zpow v x`.
-/
theorem absEv_eq_prod (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ) :
    ((absEv F E v x : ℝ≥0) : ℝ) = ∏ w ∈ aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ (-ordAt v w x) :=
  GlobalTheory.T.absEv_eq_prod_norm_zpow v x

/- English proof (translation)
The claim follows from `GlobalTheory.T.local_order_exists_units v k`.
-/
theorem exists_ordAt (v : Pl F) (k : HeightOneSpectrum (𝓞 E) → ℤ) :
    ∃ x : (Fv F v ⊗[F] E)ˣ, ∀ w ∈ aboveF (L := E) F v, ordAt v w x = k w :=
  GlobalTheory.T.local_order_exists_units v k

/- English proof (translation)
The claim follows from `GlobalTheory.T.integral_indicator_geometric μ o ho hm h1 a ha0 ha c`.
-/
theorem integral_shells {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {ι : Type} [Fintype ι] (o : G →* Multiplicative (ι → ℤ)) (ho : Function.Surjective o)
    (hm : MeasurableSet {g : G | o g = 1}) (h1 : μ {g : G | o g = 1} = 1) (a : ι → ℂ) (ha0 : ∀ i, a i ≠ 0)
    (ha : ∀ i, ‖a i‖ < 1) (c : ι → ℤ) :
    ∫ g, Set.indicator {g : G | ∀ i, c i ≤ Multiplicative.toAdd (o g) i}
      (fun g => ∏ i, a i ^ Multiplicative.toAdd (o g) i) g ∂μ = ∏ i, a i ^ c i / (1 - a i) :=
  GlobalTheory.T.integral_indicator_geometric μ o ho hm h1 a ha0 ha c

/- English proof (translation)
Rewrite using `[GlobalTheory.LFun.ideleAt_eq_prod_locIdele, map_prod]`. Rewrite using `[show ((∏ w ∈ (finite_aboveF (L := E) F v).toFinset.attach, ν (locIdele F w.1 (Units.map (toCompl ((finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x)) : Circle) : ℂ) = ∏ w ∈ (finite_aboveF (L := E) F v).toFinset.attach, ((ν (locIdele F w.1 (Units.map (toCompl ((fini …`. Use `(Finset.prod_congr rfl fun w _ => ?_).trans (Finset.prod_attach (aboveF (L := E) F v) (fun w => ((val ν w : ℂˣ) : ℂ) ^ ordAt v w x))` and prove the remaining obligations. Establish `h : w.1.under (𝓞 F) = v` using `(finite_aboveF (L := E) F v).mem_toFinset.1 w.2`. Establish `hb : Valued.v ((Units.map (toCompl h).toMonoidHom x : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) = WithZero.exp (-ordAt v w.1 x)`.

Rewrite using `[← valAt_eq_exp, valAt_of_under h]`. Both sides reduce to the same expression. Establish `e` using `locChar_eq_val_zpow (hν w.1 h) hb`. Establish `e2` using `congrArg (fun z : ℂˣ => (z : ℂ)) e`. Simplify using `only [Units.val_zpow_eq_zpow_val] at e2`.

Conclude with `e2`.
-/
theorem nu_ideleAt (ν : Chr F E) (v : Pl F) (hν : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w)
    (x : (Fv F v ⊗[F] E)ˣ) :
    ((ν (ideleAt F E v x) : Circle) : ℂ) = ∏ w ∈ aboveF (L := E) F v, ((val ν w : ℂˣ) : ℂ) ^ ordAt v w x := by
  rw [GlobalTheory.LFun.ideleAt_eq_prod_locIdele, map_prod]
  rw [show ((∏ w ∈ (finite_aboveF (L := E) F v).toFinset.attach, ν (locIdele F w.1 (Units.map (toCompl ((finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x)) : Circle) : ℂ) = ∏ w ∈ (finite_aboveF (L := E) F v).toFinset.attach, ((ν (locIdele F w.1 (Units.map (toCompl ((finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x)) : Circle) : ℂ) from map_prod Circle.coeHom _ _]
  refine (Finset.prod_congr rfl fun w _ => ?_).trans
    (Finset.prod_attach (aboveF (L := E) F v) (fun w => ((val ν w : ℂˣ) : ℂ) ^ ordAt v w x))
  have h : w.1.under (𝓞 F) = v := (finite_aboveF (L := E) F v).mem_toFinset.1 w.2
  have hb : Valued.v ((Units.map (toCompl h).toMonoidHom x : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
      WithZero.exp (-ordAt v w.1 x) := by
    rw [← valAt_eq_exp, valAt_of_under h]
    rfl
  have e := locChar_eq_val_zpow (hν w.1 h) hb
  have e2 := congrArg (fun z : ℂˣ => (z : ℂ)) e
  simp only [Units.val_zpow_eq_zpow_val] at e2
  exact e2

omit [NumberField E] in
/- English proof (translation)
Establish `e : {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, z = a ⊗ₜ[F] (x : E)} = {y | ∃ c ∈ v.adicCompletionIntegers F, ∃ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E), y = c ⊗ₜ[F] x}`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, x, rfl⟩`. Conclude with `⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩`.

Introduce and unpack `⟨c, hc, x, hx, rfl⟩`. Take `⟨x', rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Conclude with `⟨c, hc, x', rfl⟩`. Express the relevant statement in the definitionally equal form `((AddSubgroup.closure _ : AddSubgroup (Fv F v ⊗[F] E)) : Set (Fv F v ⊗[F] E)) = _`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem intLoc_eq_locId_one (v : Pl F) :
    ((intLoc F E v : Subring (Fv F v ⊗[F] E)) : Set (Fv F v ⊗[F] E)) =
      (GlobalTheory.SnMass.locId v (1 : FractionalIdeal (𝓞 E)⁰ E) : Set (Fv F v ⊗[F] E)) := by
  have e : {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, z = a ⊗ₜ[F] (x : E)} =
      {y | ∃ c ∈ v.adicCompletionIntegers F, ∃ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E), y = c ⊗ₜ[F] x} := by
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩
    · rintro ⟨c, hc, x, hx, rfl⟩
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨c, hc, x', rfl⟩
  change ((AddSubgroup.closure _ : AddSubgroup (Fv F v ⊗[F] E)) : Set (Fv F v ⊗[F] E)) = _
  rw [e]
  rfl

/- English proof (translation)
Establish `h` using `memLocId_iff v (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0) x`. Simplify using `only [FractionalIdeal.count_one] at h`. Rewrite using `[← h, ← SetLike.mem_coe, intLoc_eq_locId_one]`. Both sides reduce to the same expression.
-/
theorem mem_intLoc_iff (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ) :
    (x : Fv F v ⊗[F] E) ∈ intLoc F E v ↔ ∀ w ∈ aboveF (L := E) F v, 0 ≤ ordAt v w x := by
  have h := memLocId_iff v (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0) x
  simp only [FractionalIdeal.count_one] at h
  rw [← h, ← SetLike.mem_coe, intLoc_eq_locId_one]
  rfl

/- English proof (translation)
Rewrite using `[mem_unitsAt]`. Establish `h1` using `mem_intLoc_iff v (unitFin F E v l)`. Establish `h2` using `mem_intLoc_iff v (unitFin F E v l)⁻¹`. Simplify using `only [ordAt_inv, Left.nonneg_neg_iff] at h2`. Express the relevant statement in the definitionally equal form `_ ∧ (unitFin F E v l : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((unitFin F E v l)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 ∈ intLoc F E v ↔ _`.

Rewrite using `[h1, h2]`. Conclude with `⟨fun h w hw => le_antisymm (h.2.2 w hw) (h.2.1 w hw), fun h => ⟨hl, fun w hw => (h w hw).ge, fun w hw => (h w hw).le⟩⟩`.
-/
theorem mem_unitsAt_iff (v : Pl F) {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v)) :
    l ∈ unitsAt E v ↔ ∀ w ∈ aboveF (L := E) F v, ordAt v w (unitFin F E v l) = 0 := by
  rw [mem_unitsAt]
  have h1 := mem_intLoc_iff v (unitFin F E v l)
  have h2 := mem_intLoc_iff v (unitFin F E v l)⁻¹
  simp only [ordAt_inv, Left.nonneg_neg_iff] at h2
  change _ ∧ (unitFin F E v l : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((unitFin F E v l)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 ∈ intLoc F E v ↔ _
  rw [h1, h2]
  exact ⟨fun h w hw => le_antisymm (h.2.2 w hw) (h.2.1 w hw), fun h => ⟨hl, fun w hw => (h w hw).ge, fun w hw => (h w hw).le⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ ν 𝔞 h𝔞 v hν s hs μ hμ`. Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evFin F v)`. Use `haveI := hμ.1`. Set `ι` to `{w // w ∈ aboveF (L := E) F v}`. Set `o : idelesAt E (evFin F v) →* Multiplicative (ι → ℤ)` to `(ordHom v).comp (idelesAtEquiv E v).toMonoidHom`.

Establish `ho : ∀ l (w : ι), Multiplicative.toAdd (o l) w = ordAt v w.1 (unitFin F E v l.1)` using `fun _ _ => rfl`. Set `N : HeightOneSpectrum (𝓞 E) → ℂ` to `fun w => (Ideal.absNorm w.asIdeal : ℂ)`. Establish `hN1 : ∀ w : HeightOneSpectrum (𝓞 E), 1 < (Ideal.absNorm w.asIdeal : ℝ)` using `fun w => by`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm w` after adjusting the coercions. Establish `hN0 : ∀ w, N w ≠ 0` using `fun w h => by`.

Use `hN1 w` as an intermediate fact. Establish `h' : (Ideal.absNorm w.asIdeal : ℂ) = 0` using `h`. Normalize the coercions in `at h'`. Rewrite `this` using `[h']`. Evaluate the numerical expressions using `at this`.

Set `a : ι → ℂ` to `fun w => (val ν w.1 : ℂ) * (N w.1 ^ s)⁻¹`. Set `c : ι → ℤ` to `fun w => FractionalIdeal.count E w.1 𝔞`. Establish `hf : ∀ l : idelesAt E (evFin F v), Set.indicator {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞} (fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s) l = Set.indicator {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i} (fun g => ∏ i, …`. Introduce `l`. Establish `hmem : (l ∈ {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}) ↔ l ∈ {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i}`.

Simplify using `only [Set.mem_setOf_eq, ho]`. Rewrite using `[memLocId_iff v h𝔞]`. Conclude with `⟨fun h i => h i.1 i.2, fun h w hw => h ⟨w, hw⟩⟩`. Distinguish the cases in `hl : l ∈ {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i}`. Rewrite using `[Set.indicator_of_mem hl, Set.indicator_of_mem (hmem.2 hl)]`.

Establish `e1 : ((ν l.1 : Circle) : ℂ) = ∏ w ∈ aboveF (L` using `E) F v, ((val ν w : ℂˣ) : ℂ) ^ ordAt v w (unitFin F E v l.1) := by`. Rewrite using `[← nu_ideleAt ν v hν, ideleAt_unitFin l.2]`. Establish `e2 : ((absE F E l.1 : ℝ) : ℂ) = ∏ w ∈ aboveF (L` using `E) F v, N w ^ (-ordAt v w (unitFin F E v l.1)) := by`. Rewrite using `[absE_of_mem l.2, absEv_eq_prod]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Rewrite using `[← Finset.prod_coe_sort (aboveF (L := E) F v)]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[ho, mul_zpow]`.

Use `congr 1`. Rewrite using `[inv_zpow', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Set.indicator_of_notMem hl, Set.indicator_of_notMem (fun h => hl (hmem.1 h))]`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hf)]`.

Establish `hker : {g : idelesAt E (evFin F v) | o g = 1} = {l | l.1 ∈ unitsAt E v}`. Use extensionality with `l`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[mem_unitsAt_iff v l.2, ← toAdd_eq_zero, funext_iff]`. Conclude with `⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩`.

Establish `hsurj : Function.Surjective o`. Introduce `k`. Take `⟨x, hx⟩` from `exists_ordAt v (fun w => if h : w ∈ aboveF (L := E) F v then Multiplicative.toAdd k ⟨w, h⟩ else 0)`. Use `⟨(idelesAtEquiv E v).symm x, ?_⟩` and prove the remaining obligations. Use `show ordHom v ((idelesAtEquiv E v) ((idelesAtEquiv E v).symm x)) = k`.

Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`. Rewrite using `[← ofAdd_toAdd k]`. Use `show Multiplicative.ofAdd (fun w : ι => ordAt v w.1 x) = _`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Rewrite using `[hx w.1 w.2, dif_pos w.2]`. Establish `hm : MeasurableSet {g : idelesAt E (evFin F v) | o g = 1}`. Rewrite using `[hker]`. Conclude with `(isCompact_isOpen_unitsAt v).2.measurableSet`. Establish `h1 : μ {g : idelesAt E (evFin F v) | o g = 1} = 1`.

Rewrite using `[hker]`. Conclude with `hμ.2`. Establish `hNs : ∀ w, 1 < ‖N w ^ s‖` using `fun w => by`. Rewrite using `[norm_pow]`. Establish `: ‖N w‖ = (Ideal.absNorm w.asIdeal : ℝ)` using `by show ‖((Ideal.absNorm w.asIdeal : ℕ) : ℂ)‖ = _`.

Rewrite using `[Complex.norm_natCast]`. Rewrite using `[this]`. Conclude with `one_lt_pow₀ (hN1 w) hs.ne'`. Establish `ha0 : ∀ i, a i ≠ 0` using `fun i => mul_ne_zero (val ν i.1).ne_zero (inv_ne_zero (pow_ne_zero _ (hN0 _)))`. Establish `ha : ∀ i, ‖a i‖ < 1` using `fun i => by show ‖(val ν i.1 : ℂ) * (N i.1 ^ s)⁻¹‖ < 1`.

Rewrite using `[norm_mul, norm_val, one_mul, norm_inv]`. Conclude with `inv_lt_one_of_one_lt₀ (hNs i.1)`. Rewrite using `[integral_shells μ o hsurj hm h1 a ha0 ha c]`. Unfold `unrFac Lv`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_coe_sort (aboveF (L := E) F v)]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.LFun.locL, charFam_of_unrAt (hν w.1 (GlobalTheory.LFun.mem_aboveF.1 w.2)), eulerFac_singleton]`. Establish `e1 : npow w.1 (-(s : ℂ)) = (N w.1 ^ s)⁻¹`. Unfold `npow`. Rewrite using `[Complex.cpow_neg, Complex.cpow_natCast]`.

Establish `e2 : npow w.1 (-((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ))) = ((N w.1 ^ s)⁻¹) ^ c w`. Unfold `npow`. Establish `: (-((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ))) = ((-((s : ℤ) * c w) : ℤ) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Complex.cpow_intCast, inv_zpow', ← zpow_natCast, ← zpow_mul, mul_neg]`. Rewrite using `[e1, e2, Units.val_zpow_eq_zpow_val, div_eq_mul_inv]`. Use `show ((val ν w.1 : ℂ) * (N w.1 ^ s)⁻¹) ^ c w * _ = _`. Rewrite using `[mul_zpow]`.
-/
theorem integral_locId_eq_unrFac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → ∀ v : Pl F, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w) →
    ∀ s : ℕ, 0 < s → ∀ μ : Measure (idelesAt E (evFin F v)), IsNormE E v μ →
      ∫ l : idelesAt E (evFin F v), Set.indicator {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
          (fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s) l ∂μ = unrFac ν 𝔞 (s : ℂ) v := by
  intro F E _ _ _ _ _ ν 𝔞 h𝔞 v hν s hs μ hμ
  classical
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  let ι := {w // w ∈ aboveF (L := E) F v}
  let o : idelesAt E (evFin F v) →* Multiplicative (ι → ℤ) := (ordHom v).comp (idelesAtEquiv E v).toMonoidHom
  have ho : ∀ l (w : ι), Multiplicative.toAdd (o l) w = ordAt v w.1 (unitFin F E v l.1) := fun _ _ => rfl
  let N : HeightOneSpectrum (𝓞 E) → ℂ := fun w => (Ideal.absNorm w.asIdeal : ℂ)
  have hN1 : ∀ w : HeightOneSpectrum (𝓞 E), 1 < (Ideal.absNorm w.asIdeal : ℝ) := fun w => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hN0 : ∀ w, N w ≠ 0 := fun w h => by
    have := hN1 w
    have h' : (Ideal.absNorm w.asIdeal : ℂ) = 0 := h
    norm_cast at h'
    rw [h'] at this
    norm_num at this
  let a : ι → ℂ := fun w => (val ν w.1 : ℂ) * (N w.1 ^ s)⁻¹
  let c : ι → ℤ := fun w => FractionalIdeal.count E w.1 𝔞

  have hf : ∀ l : idelesAt E (evFin F v),
      Set.indicator {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
          (fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s) l =
        Set.indicator {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i} (fun g => ∏ i, a i ^ Multiplicative.toAdd (o g) i) l := by
    intro l
    have hmem : (l ∈ {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}) ↔
        l ∈ {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i} := by
      simp only [Set.mem_setOf_eq, ho]
      rw [memLocId_iff v h𝔞]
      exact ⟨fun h i => h i.1 i.2, fun h w hw => h ⟨w, hw⟩⟩
    by_cases hl : l ∈ {g | ∀ i, c i ≤ Multiplicative.toAdd (o g) i}
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (hmem.2 hl)]
      have e1 : ((ν l.1 : Circle) : ℂ) = ∏ w ∈ aboveF (L := E) F v, ((val ν w : ℂˣ) : ℂ) ^ ordAt v w (unitFin F E v l.1) := by
        rw [← nu_ideleAt ν v hν, ideleAt_unitFin l.2]
      have e2 : ((absE F E l.1 : ℝ) : ℂ) = ∏ w ∈ aboveF (L := E) F v, N w ^ (-ordAt v w (unitFin F E v l.1)) := by
        rw [absE_of_mem l.2, absEv_eq_prod]
        push_cast
        rfl
      rw [e1, e2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      rw [← Finset.prod_coe_sort (aboveF (L := E) F v)]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [ho, mul_zpow]
      congr 1
      rw [inv_zpow', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      ring_nf
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (fun h => hl (hmem.1 h))]

  rw [integral_congr_ae (Filter.Eventually.of_forall hf)]
  have hker : {g : idelesAt E (evFin F v) | o g = 1} = {l | l.1 ∈ unitsAt E v} := by
    ext l
    simp only [Set.mem_setOf_eq]
    rw [mem_unitsAt_iff v l.2, ← toAdd_eq_zero, funext_iff]
    exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩
  have hsurj : Function.Surjective o := by
    intro k
    obtain ⟨x, hx⟩ := exists_ordAt v (fun w => if h : w ∈ aboveF (L := E) F v then Multiplicative.toAdd k ⟨w, h⟩ else 0)
    refine ⟨(idelesAtEquiv E v).symm x, ?_⟩
    show ordHom v ((idelesAtEquiv E v) ((idelesAtEquiv E v).symm x)) = k
    rw [ContinuousMulEquiv.apply_symm_apply]
    rw [← ofAdd_toAdd k]
    show Multiplicative.ofAdd (fun w : ι => ordAt v w.1 x) = _
    congr 1
    funext w
    rw [hx w.1 w.2, dif_pos w.2]
  have hm : MeasurableSet {g : idelesAt E (evFin F v) | o g = 1} := by
    rw [hker]
    exact (isCompact_isOpen_unitsAt v).2.measurableSet
  have h1 : μ {g : idelesAt E (evFin F v) | o g = 1} = 1 := by
    rw [hker]
    exact hμ.2
  have hNs : ∀ w, 1 < ‖N w ^ s‖ := fun w => by
    rw [norm_pow]
    have : ‖N w‖ = (Ideal.absNorm w.asIdeal : ℝ) := by
      show ‖((Ideal.absNorm w.asIdeal : ℕ) : ℂ)‖ = _
      rw [Complex.norm_natCast]
    rw [this]
    exact one_lt_pow₀ (hN1 w) hs.ne'
  have ha0 : ∀ i, a i ≠ 0 := fun i => mul_ne_zero (val ν i.1).ne_zero (inv_ne_zero (pow_ne_zero _ (hN0 _)))
  have ha : ∀ i, ‖a i‖ < 1 := fun i => by
    show ‖(val ν i.1 : ℂ) * (N i.1 ^ s)⁻¹‖ < 1
    rw [norm_mul, norm_val, one_mul, norm_inv]
    exact inv_lt_one_of_one_lt₀ (hNs i.1)
  rw [integral_shells μ o hsurj hm h1 a ha0 ha c]
  unfold unrFac Lv
  rw [← Finset.prod_mul_distrib, ← Finset.prod_coe_sort (aboveF (L := E) F v)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.LFun.locL, charFam_of_unrAt (hν w.1 (GlobalTheory.LFun.mem_aboveF.1 w.2)), eulerFac_singleton]
  have e1 : npow w.1 (-(s : ℂ)) = (N w.1 ^ s)⁻¹ := by
    unfold npow
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  have e2 : npow w.1 (-((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ))) = ((N w.1 ^ s)⁻¹) ^ c w := by
    unfold npow
    have : (-((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ))) = ((-((s : ℤ) * c w) : ℤ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.cpow_intCast, inv_zpow', ← zpow_natCast, ← zpow_mul, mul_neg]
  rw [e1, e2, Units.val_zpow_eq_zpow_val, div_eq_mul_inv]
  show ((val ν w.1 : ℂ) * (N w.1 ^ s)⁻¹) ^ c w * _ = _
  rw [mul_zpow]

end GlobalTheory.UnrTate

end
