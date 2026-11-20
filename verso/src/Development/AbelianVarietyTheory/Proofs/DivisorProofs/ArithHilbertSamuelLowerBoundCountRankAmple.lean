import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdegStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.FLower

open MvPolynomial

abbrev Deg (D q : ℕ) : Type := {α : Fin (D + 1) →₀ ℕ // α.degree = q}

scoped instance (D q : ℕ) : Finite (Deg D q) :=
  Nat.finite_of_card_ne_zero <| by
    rw [(GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1]
    exact (Nat.choose_pos (Nat.le_add_left D q)).ne'

scoped instance (D q : ℕ) : Fintype (Deg D q) := Fintype.ofFinite _

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `(GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1`.
-/
theorem card_deg (D q : ℕ) : Fintype.card (Deg D q) = (q + D).choose D := by
  rw [← Nat.card_eq_fintype_card]; exact (GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1

def xm {K : Type} [CommRing K] {D : ℕ} (x : Fin (D + 1) → K) (α : Fin (D + 1) →₀ ℕ) : K := ∏ l, x l ^ α l

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq']`. Establish `hsub : T.support ⊆ Finset.univ.map (Function.Embedding.subtype fun α : Fin (D + 1) →₀ ℕ => α.degree = q)`. Introduce `d hd`. Establish `h` using `hT (mem_support_iff.1 hd)`. Use `Finset.mem_map.2 ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩` and prove the remaining obligations.

Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `h`. Rewrite using `[Finset.sum_subset hsub (fun d _ hd => by rw [notMem_support_iff.1 hd, map_zero, zero_mul]), Finset.sum_map]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, xm, algebraMap_int_eq, eq_intCast]`.

Both sides reduce to the same expression.
-/
theorem aeval_eq_sum {K : Type} [CommRing K] {D q : ℕ} (x : Fin (D + 1) → K) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous q) : aeval x T = ∑ α : Deg D q, coeff α.1 T • xm x α.1 := by
  rw [aeval_def, eval₂_eq']
  have hsub : T.support ⊆ Finset.univ.map (Function.Embedding.subtype fun α : Fin (D + 1) →₀ ℕ => α.degree = q) := by
    intro d hd
    have h := hT (mem_support_iff.1 hd)
    refine Finset.mem_map.2 ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩
    rw [Finsupp.degree_eq_weight_one]; exact h
  rw [Finset.sum_subset hsub (fun d _ hd => by rw [notMem_support_iff.1 hd, map_zero, zero_mul]), Finset.sum_map]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [zsmul_eq_mul, xm, algebraMap_int_eq, eq_intCast]
  rfl

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Substitute `ha hb` using the available equality. Conclude with `hf`.
-/
theorem H_congr (P : Pair p) {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {f : X.functionField} (hf : f ∈ P.H a b) :
    f ∈ P.H a' b' := by subst ha hb; exact hf

/- English proof (translation)
The claim follows from `mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`.
-/
theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Take `⟨h1, h2⟩` from `GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x 0) (hx 0) 0`. Simplify using `only [Finset.prod_empty, Finset.sum_empty, pow_zero, Nat.cast_zero, zero_mul] at h1 h2 ⊢`. Conclude with `⟨h1, fun σ y => h2 σ y⟩`.

Consider the case `insert l s hl ih`. Take `⟨h1, h2⟩` from `GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx l) (α l)`. Take `⟨h3, h4⟩` from `GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 ih.1`. Establish `ea : ((α l : ℕ) : ℤ) * e + (∑ l ∈ s, (α l : ℤ)) * e = (∑ l ∈ insert l s, (α l : ℤ)) * e`. Rewrite using `[Finset.sum_insert hl]`.

Expand and normalize the polynomial expressions, which then agree. Establish `eb : ((α l : ℕ) : ℤ) * 0 + 0 = 0` using `by ring`. Rewrite using `[Finset.prod_insert hl]`. Use `⟨H_congr P ea eb h3, fun σ y => ?_⟩` and prove the remaining obligations. Establish `h5` using `h4 σ y`.

Rewrite `h5` using `[eb, ea]`. Rewrite using `[Finset.prod_insert hl, h5, h2 σ y, ih.2 σ y]`.
-/
theorem prod_pow_mem (P : Pair p) (e : ℤ) {D : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (s : Finset (Fin (D + 1))) :
    (∏ l ∈ s, x l ^ α l) ∈ P.H ((∑ l ∈ s, (α l : ℤ)) * e) 0 ∧ ∀ σ y,
      P.nu ((∑ l ∈ s, (α l : ℤ)) * e) 0 σ y (∏ l ∈ s, x l ^ α l) = ∏ l ∈ s, P.nu e 0 σ y (x l) ^ α l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x 0) (hx 0) 0
    simp only [Finset.prod_empty, Finset.sum_empty, pow_zero, Nat.cast_zero, zero_mul] at h1 h2 ⊢
    exact ⟨h1, fun σ y => h2 σ y⟩
  | insert l s hl ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx l) (α l)
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 ih.1
    have ea : ((α l : ℕ) : ℤ) * e + (∑ l ∈ s, (α l : ℤ)) * e = (∑ l ∈ insert l s, (α l : ℤ)) * e := by
      rw [Finset.sum_insert hl]; ring
    have eb : ((α l : ℕ) : ℤ) * 0 + 0 = 0 := by ring
    rw [Finset.prod_insert hl]
    refine ⟨H_congr P ea eb h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [eb, ea] at h5
    rw [Finset.prod_insert hl, h5, h2 σ y, ih.2 σ y]

/- English proof (translation)
Establish `hq : (∑ l, (α l : ℤ)) * e = e * q`. Substitute `hα` using the available equality. Rewrite using `[mul_comm, Finsupp.degree_eq_sum]`. Use `push_cast`. Both sides reduce to the same expression.

Take `⟨h1, h2⟩` from `prod_pow_mem P e x hx α Finset.univ`. Conclude with `⟨H_congr P hq rfl h1, fun σ y => by rw [← hq, xm, h2]⟩`.
-/
theorem xm_mem (P : Pair p) (e : ℤ) {D q : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (hα : α.degree = q) :
    xm x α ∈ P.H (e * q) 0 ∧ ∀ σ y, P.nu (e * q) 0 σ y (xm x α) = ∏ l, P.nu e 0 σ y (x l) ^ α l := by
  have hq : (∑ l, (α l : ℤ)) * e = e * q := by
    subst hα; rw [mul_comm, Finsupp.degree_eq_sum]; push_cast; rfl
  obtain ⟨h1, h2⟩ := prod_pow_mem P e x hx α Finset.univ
  exact ⟨H_congr P hq rfl h1, fun σ y => by rw [← hq, xm, h2]⟩

/- English proof (translation)
Use `⟨AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hf j) _, fun σ y => ?_⟩` and prove the remaining obligations. Take `⟨ℓ, hℓ⟩` from `GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y`. Set `F : P.H a b` to `∑ j, n j • (⟨f j, hf j⟩ : P.H a b)`. Establish `hF : (F : X.functionField) = ∑ j, n j • f j` using `by simp [F]`. Rewrite using `[← hF, ← norm_val, ← hℓ, map_sum]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul, norm_mul, Complex.norm_intCast, hℓ, norm_val]`.
-/
theorem sum_zsmul (P : Pair p) (a b : ℤ) {J : Type} [Fintype J] (f : J → X.functionField) (hf : ∀ j, f j ∈ P.H a b)
    (n : J → ℤ) : (∑ j, n j • f j) ∈ P.H a b ∧ ∀ σ y,
      P.nu a b σ y (∑ j, n j • f j) ≤ ∑ j, |(n j : ℝ)| * P.nu a b σ y (f j) := by
  refine ⟨AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hf j) _, fun σ y => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y
  let F : P.H a b := ∑ j, n j • (⟨f j, hf j⟩ : P.H a b)
  have hF : (F : X.functionField) = ∑ j, n j • f j := by simp [F]
  rw [← hF, ← norm_val, ← hℓ, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, norm_mul, Complex.norm_intCast, hℓ, norm_val]

/- English proof (translation)
Introduce `k _ X _ p D hX P hA e x hx a b`. Use `haveI : CharZero X.functionField := (GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hX).1`. Take `⟨hx0, halg, hfin⟩` from `GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hx`. Use `set δ := Module.finrank (ratF x) X.functionField with hδ`. Take `⟨c, g, hg, hgi⟩ : ∃ (c : ℕ) (g : Fin δ → X.functionField), (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g` from `GlobalTheory.T.exists_functionField_basis_of_sections k X p D hX P hA e x hx a b`.

Establish `hbd : ∀ i, ∃ M : ℝ, ∀ σ y, P.nu (e * c + a) b σ y (g i) ≤ M` using `fun i => ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P _ b).2 (g i) (hg i)).2`. Use `choose M hM using hbd`. Use `set M' : ℝ := 1 + ∑ i, |M i| with hM'`. Establish `hM'0 : 0 ≤ M'` using `by positivity`. Establish `hgM : ∀ i σ y, P.nu (e * c + a) b σ y (g i) ≤ M'` using `fun i σ y => by`.

Use `Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg (M i)) (Finset.mem_univ i)` as an intermediate fact. Use `le_abs_self (M i)` as an intermediate fact. Use `hM i σ y` as an intermediate fact. Simplify using `only [hM'] at *`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨c, ((δ : ℝ) + 1) * M', by positivity, fun q => ?_⟩` and prove the remaining obligations. Set `w : Fin δ × Deg D q → X.functionField` to `fun ia => xm x ia.2.1 * g ia.1`. Establish `hidx : (e : ℤ) * q + (e * c + a) = e * ((q + c : ℕ) : ℤ) + a` using `by push_cast; ring`. Establish `hw : ∀ ia, w ia ∈ P.H (e * ((q + c : ℕ) : ℤ) + a) b ∧ ∀ σ y, P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) = (∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l) * P.nu (e * c + a) b σ y (g ia.1)`. Introduce `ia`.

Take `⟨h1, h2⟩` from `xm_mem P e x hx.mem ia.2.1 ia.2.2`. Take `⟨h3, h4⟩` from `GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 (hg ia.1)`. Establish `h0b : (0 : ℤ) + b = b` using `zero_add b`. Use `⟨H_congr P hidx h0b h3, fun σ y => ?_⟩` and prove the remaining obligations. Establish `h5` using `h4 σ y`.

Rewrite `h5` using `[hidx, h0b]`. Rewrite using `[h5, h2 σ y]`. Prove the components needed by the constructor for the conclusion. Establish `hcard : δ * (q + D).choose D = Nat.card (Fin δ × Deg D q)`. Rewrite using `[Nat.card_prod, Nat.card_eq_fintype_card (α := Deg D q), card_deg, Nat.card_eq_fintype_card, Fintype.card_fin]`.

Set `E : Fin (δ * (q + D).choose D) ≃ Fin δ × Deg D q` to `(finCongr hcard).trans (Finite.equivFin _).symm`. Use `⟨w ∘ E, fun i => (hw (E i)).1, (linearIndependent_equiv E).2 ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `n hn ia`. Set `T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ` to `fun i => ∑ α : Deg D q, monomial α.1 (n (i, α))`.

Establish `hT : ∀ i, (T i).IsHomogeneous q` using `fun i => IsHomogeneous.sum _ _ _ fun α _ => isHomogeneous_monomial _ α.2`. Establish `hTe : ∀ i, aeval x (T i) = ∑ α : Deg D q, n (i, α) • xm x α.1` using `fun i => by`. Simplify using `only [T, map_sum, aeval_monomial, Finsupp.prod_pow, algebraMap_int_eq, eq_intCast, zsmul_eq_mul, xm]`. Establish `h0` using `GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q T hT (by`. Rewrite using `[← hn, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hTe, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Simplify using `only [w, smul_mul_assoc])`. Establish `h1` using `congrArg (coeff ia.2.1) (congrFun h0 ia.1)`.

Simplify using `only [T, coeff_sum, coeff_monomial, Pi.zero_apply, coeff_zero] at h1`. Establish `h2 : ∀ α : Deg D q, (if (α : Fin (D + 1) →₀ ℕ) = ia.2.1 then n (ia.1, α) else 0) = if α = ia.2 then n (ia.1, α) else 0` using `fun α => by simp only [Subtype.coe_inj]`. Rewrite `h1` using `[Finset.sum_congr rfl fun α _ => h2 α]`. Simplify using `using h1`. Introduce `R hR hxl`.

Take `⟨hfinS, hcnt, -, -, -⟩` from `GlobalTheory.T.card_bounded_homogeneous_int_form_families D q δ R hR`. Set `Φ : (Fin δ → MvPolynomial (Fin (D + 1)) ℤ) → X.functionField` to `fun T => ∑ i, aeval x (T i) * g i`. Establish `hΦ : ∀ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous q) → Φ T = ∑ ia : Fin δ × Deg D q, coeff ia.2.1 (T ia.1) • w ia`. Introduce `T hT`. Simplify using `only [Φ, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_eq_sum x (T i) (hT i), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Simplify using `only [w, smul_mul_assoc]`. Establish `hinj : Set.InjOn Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}`.

Introduce `T hT T' hT' h`. Use `GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q (T - T') (fun i => (hT.1 i).sub (hT'.1 i)) (by` as an intermediate fact. Simplify using `only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`. Conclude with `sub_eq_zero.2 h)`. Conclude with `sub_eq_zero.1 this`.

Establish `hmaps : Set.MapsTo Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R} (P.Bl (e * (q + c : ℕ) + a) b (((δ : ℝ) + 1) * M' * (q + D).choose D * R))`. Introduce `T hT`. Rewrite `hT` using `[Set.mem_setOf_eq]`. Rewrite using `[hΦ T hT.1]`. Take `⟨h1, h2⟩` from `sum_zsmul P _ b w (fun ia => (hw ia).1) (fun ia => coeff ia.2.1 (T ia.1))`.

Use `⟨h1, fun σ y => (h2 σ y).trans ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ ia : Fin δ × Deg D q, |((coeff ia.2.1 (T ia.1) : ℤ) : ℝ)| * P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) ≤ R * M'`. Introduce `ia`. Rewrite using `[(hw ia).2 σ y]`. Establish `hp : ∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l ≤ 1` using `Finset.prod_le_one (fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _) (fun l _ => pow_le_one₀ (nu_nonneg _ _ _ _ _ _) (hxl l σ y))`.

Use `mul_le_mul (hT.2 _ _) ?_ (mul_nonneg (Finset.prod_nonneg fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _) (nu_nonneg _ _ _ _ _ _)) hR` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_le_sum fun ia _ => hterm ia).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_deg, nsmul_eq_mul, Nat.cast_mul]`. Establish `h0 : 0 ≤ ((q + D).choose D : ℝ) * R * M'` using `by positivity`.

Establish `key : ((δ : ℝ) + 1) * M' * ((q + D).choose D : ℝ) * R = (δ : ℝ) * ((q + D).choose D : ℝ) * (R * M') + ((q + D).choose D : ℝ) * R * M'` using `by ring`. Rewrite using `[key]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hcnt, hfinS.cast_ncard_eq, ← hinj.encard_image]`. Conclude with `Set.encard_le_encard hmaps.image_subset`.
-/
theorem count_rank_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (∃ v : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) → X.functionField, (∀ i, v i ∈ P.H (e * (q + c : ℕ) + a) b) ∧ LinearIndependent ℤ v) ∧ ∀ R : ℝ, 0 ≤ R → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (((2 * ⌊R⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + D).choose D) : ℕ) : ℕ∞) ≤ (P.Bl (e * (q + c : ℕ) + a) b (C * (q + D).choose D * R)).encard := by
  intro k _ X _ p D hX P hA e x hx a b
  haveI : CharZero X.functionField := (GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hX).1
  obtain ⟨hx0, halg, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hx
  set δ := Module.finrank (ratF x) X.functionField with hδ
  obtain ⟨c, g, hg, hgi⟩ : ∃ (c : ℕ) (g : Fin δ → X.functionField), (∀ i, g i ∈ P.H (e * c + a) b) ∧
      LinearIndependent (ratF x) g := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hX P hA e x hx a b
  have hbd : ∀ i, ∃ M : ℝ, ∀ σ y, P.nu (e * c + a) b σ y (g i) ≤ M := fun i =>
    ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P _ b).2 (g i) (hg i)).2
  choose M hM using hbd
  set M' : ℝ := 1 + ∑ i, |M i| with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have hgM : ∀ i σ y, P.nu (e * c + a) b σ y (g i) ≤ M' := fun i σ y => by
    have := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg (M i)) (Finset.mem_univ i)
    have := le_abs_self (M i)
    have := hM i σ y
    simp only [hM'] at *
    linarith
  refine ⟨c, ((δ : ℝ) + 1) * M', by positivity, fun q => ?_⟩
  let w : Fin δ × Deg D q → X.functionField := fun ia => xm x ia.2.1 * g ia.1
  have hidx : (e : ℤ) * q + (e * c + a) = e * ((q + c : ℕ) : ℤ) + a := by push_cast; ring
  have hw : ∀ ia, w ia ∈ P.H (e * ((q + c : ℕ) : ℤ) + a) b ∧ ∀ σ y,
      P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) =
        (∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l) * P.nu (e * c + a) b σ y (g ia.1) := by
    intro ia
    obtain ⟨h1, h2⟩ := xm_mem P e x hx.mem ia.2.1 ia.2.2
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 (hg ia.1)
    have h0b : (0 : ℤ) + b = b := zero_add b
    refine ⟨H_congr P hidx h0b h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [hidx, h0b] at h5
    rw [h5, h2 σ y]
  constructor
  · have hcard : δ * (q + D).choose D = Nat.card (Fin δ × Deg D q) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Deg D q), card_deg, Nat.card_eq_fintype_card, Fintype.card_fin]
    let E : Fin (δ * (q + D).choose D) ≃ Fin δ × Deg D q := (finCongr hcard).trans (Finite.equivFin _).symm
    refine ⟨w ∘ E, fun i => (hw (E i)).1, (linearIndependent_equiv E).2 ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro n hn ia
    let T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ := fun i => ∑ α : Deg D q, monomial α.1 (n (i, α))
    have hT : ∀ i, (T i).IsHomogeneous q := fun i =>
      IsHomogeneous.sum _ _ _ fun α _ => isHomogeneous_monomial _ α.2
    have hTe : ∀ i, aeval x (T i) = ∑ α : Deg D q, n (i, α) • xm x α.1 := fun i => by
      simp only [T, map_sum, aeval_monomial, Finsupp.prod_pow, algebraMap_int_eq, eq_intCast, zsmul_eq_mul, xm]
    have h0 := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q T hT (by
      rw [← hn, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc])
    have h1 := congrArg (coeff ia.2.1) (congrFun h0 ia.1)
    simp only [T, coeff_sum, coeff_monomial, Pi.zero_apply, coeff_zero] at h1
    have h2 : ∀ α : Deg D q, (if (α : Fin (D + 1) →₀ ℕ) = ia.2.1 then n (ia.1, α) else 0) =
        if α = ia.2 then n (ia.1, α) else 0 := fun α => by simp only [Subtype.coe_inj]
    rw [Finset.sum_congr rfl fun α _ => h2 α] at h1
    simpa using h1
  · intro R hR hxl
    obtain ⟨hfinS, hcnt, -, -, -⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D q δ R hR
    let Φ : (Fin δ → MvPolynomial (Fin (D + 1)) ℤ) → X.functionField := fun T => ∑ i, aeval x (T i) * g i
    have hΦ : ∀ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous q) →
        Φ T = ∑ ia : Fin δ × Deg D q, coeff ia.2.1 (T ia.1) • w ia := by
      intro T hT
      simp only [Φ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aeval_eq_sum x (T i) (hT i), Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc]
    have hinj : Set.InjOn Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R} := by
      intro T hT T' hT' h
      have := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q (T - T')
        (fun i => (hT.1 i).sub (hT'.1 i)) (by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          exact sub_eq_zero.2 h)
      exact sub_eq_zero.1 this
    have hmaps : Set.MapsTo Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}
        (P.Bl (e * (q + c : ℕ) + a) b (((δ : ℝ) + 1) * M' * (q + D).choose D * R)) := by
      intro T hT
      rw [Set.mem_setOf_eq] at hT
      rw [hΦ T hT.1]
      obtain ⟨h1, h2⟩ := sum_zsmul P _ b w (fun ia => (hw ia).1) (fun ia => coeff ia.2.1 (T ia.1))
      refine ⟨h1, fun σ y => (h2 σ y).trans ?_⟩
      have hterm : ∀ ia : Fin δ × Deg D q,
          |((coeff ia.2.1 (T ia.1) : ℤ) : ℝ)| * P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) ≤ R * M' := by
        intro ia
        rw [(hw ia).2 σ y]
        have hp : ∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l ≤ 1 :=
          Finset.prod_le_one (fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _)
            (fun l _ => pow_le_one₀ (nu_nonneg _ _ _ _ _ _) (hxl l σ y))
        refine mul_le_mul (hT.2 _ _) ?_
          (mul_nonneg (Finset.prod_nonneg fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _) (nu_nonneg _ _ _ _ _ _)) hR
        calc _ ≤ 1 * M' := mul_le_mul hp (hgM _ σ y) (nu_nonneg _ _ _ _ _ _) zero_le_one
          _ = M' := one_mul _
      refine (Finset.sum_le_sum fun ia _ => hterm ia).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_deg, nsmul_eq_mul,
        Nat.cast_mul]
      have h0 : 0 ≤ ((q + D).choose D : ℝ) * R * M' := by positivity
      have key : ((δ : ℝ) + 1) * M' * ((q + D).choose D : ℝ) * R =
          (δ : ℝ) * ((q + D).choose D : ℝ) * (R * M') + ((q + D).choose D : ℝ) * R * M' := by ring
      rw [key]
      linarith
    rw [← hcnt, hfinS.cast_ncard_eq, ← hinj.encard_image]
    exact Set.encard_le_encard hmaps.image_subset

end GlobalTheory.HSAmp.FLower
