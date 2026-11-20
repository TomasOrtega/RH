import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfGermEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

/- English proof (translation)
Establish `hf : (0 : ℝ) < D.factorial` using `by positivity`. Establish `h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1)` using `tendsto_natCast_div_add_atTop 1`. Establish `h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D)) atTop (nhds c)`. Use `(ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)` as an intermediate fact. Rewrite `this` using `[one_pow, mul_one, mul_div_cancel₀ _ hf.ne']`. Then use the resulting hypothesis.

Establish `h3` using `(ENNReal.tendsto_ofReal h2).limsup_eq`. Rewrite using `[CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]`. Use `limsup_le_limsup ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with m hm`. Establish `hm' : (m : ℝ) ≠ 0` using `by positivity`.

Establish `e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) = (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D`. Use `push_cast`. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]`.

Conclude with `ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _`.
-/
theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `e` using `cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0`. Simplify using `only [add_zero] at e`. Rewrite using `[zero_smul]`.

Conclude with `(left_eq_add.1 e).symm ▸ rfl`. Consider the case `succ k ih`. Establish `e` using `cls_common_add (common₀ X Z) (k • u) u`. Rewrite using `[succ_nsmul, succ_nsmul, ← ih]`. Conclude with `e`.
-/
theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

/- English proof (translation)
Introduce `y hy i hi`. Take `⟨t, ha, hb, hc⟩` from `((common₀ X Z).addChart h).cover y`. Rewrite using `[H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc, ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))`.
-/
theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

/- English proof (translation)
Establish `h : u + k • u = (k + 1) • u` using `by rw [succ_nsmul, add_comm]`. Set `C` to `(common₀ X Z).addChart h`. Set `φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u)` to `ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)`. Establish `hφ : Function.Injective φ`. Use `(ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)` and prove the remaining obligations.

Establish `e' : C.mul θ g = C.mul θ g'` using `congrArg Subtype.val e`. Assume the negation of the conclusion as `hne`. Use `GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_` and prove the remaining obligations. Rewrite using `[map_sub, e', sub_self]`. Establish `e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u)`.

Rewrite using `[CompHt.nsmul_wtOf, smul_zero]`. Rewrite using `[e]`. Establish `hr` using `LinearMap.rank_le_of_injective φ hφ`. Distinguish the cases in `hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)`. Rewrite `hr` using `[← Module.finrank_eq_rank]`.

Conclude with `(Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)`. Rewrite using `[Module.finrank_of_not_finite hfin]`. Conclude with `bot_le`.
-/
theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

/- English proof (translation)
Introduce `hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf`. Take `⟨f, hf⟩` from `hf`. Use `letI := algebraΓOfHom (str₀ X Z)`. Introduce `hnef`. Set `S : LinSys c.F` to `⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩`.

Establish `hS : S.IsVariety` using `⟨hV.1, hV.2.1, hV.2.2, hD⟩`. Use `haveI : IsIntegral (Y₀ X Z) := hS.isIntegral`. Establish `hp : IsProjOver (strHom c.F (Y₀ X Z))`. Rewrite using `[strHom_eq (f := str₀ X Z) fun _ => rfl]`. Conclude with `hV.2.1`.

Establish `hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw` using `ImageDegree.topologicalKrullDim_eq S hS`. Establish `ht` using `hN.2.2.tendsto hp hdim hnef`. Establish `h0` using `hN.2.2.topSelf_nonneg hp hdim hnef`. Set `θ` to `((hC u).1.equiv f).1`. Establish `hθ : θ ∈ vanBd X Z u` using `(hC u).1.space_le ((hC u).1.equiv f).2`.

Establish `hθ0 : θ ≠ 0` using `fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))`. Rewrite using `[CompHt.growthOn, dimFlag_eq]`. Use `ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_` and prove the remaining obligations. Rewrite using `[lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u)) (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]`. Conclude with `finrank_le_rank X Z U u m (hC _) hθ hθ0`.
-/
theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (Y₀ X Z)) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
