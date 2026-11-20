import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationMixedTermOfPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

/- English proof (translation)
Establish `hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y` using `Subtype.ext (Category.comp_id _)`. Establish `hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p))`. Use `HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy) (fun z c c' hc hc' => ?_) fun σ c y _ => ?_` and prove the remaining obligations. Use `Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c') (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm` and prove the remaining obligations. Rewrite using `[Category.comp_id]`.

Conclude with `((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))`. Conclude with `hiso.symm`.
-/
theorem isometric_pull_id {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) :
    (L.pull (𝟙 X) (Category.id_comp p)).Isometric L := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  exact hiso.symm

/- English proof (translation)
The claim follows from `(topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq`.
-/
theorem hasDim_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) : HasDim (genericPoint X) (D + 1) :=
  (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq

/- English proof (translation)
Take `⟨Z, i, _, _, rfl⟩` from `exists_isClosedImmersion_genericPoint z`. Establish `hrange : Set.range i = closure {i (genericPoint Z)}`. Establish `h₁` using `(genericPoint_spec Z).image i.continuous`. Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]`. Conclude with `h₁.def.symm`.

Unfold `HasDim`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]`. Conclude with `PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz`.
-/
theorem hasDim_of_coheight_eq_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {z : X} (hz : Order.coheight z = 1) : HasDim z D := by
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  unfold HasDim
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  exact PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz

/- English proof (translation)
Simplify using `only [lin, zsmul_eq_mul, map_intCast]`.
-/
theorem lin_intCast {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun i => (n i : ℝ)) = ∑ i, n i • (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  simp only [lin, zsmul_eq_mul, map_intCast]

/- English proof (translation)
Introduce `hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr`. Use `⟨hAI k X p D hX M (comb L n) r hr, ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `hEx k X p (isAmb_of_isArithVar hX) (D + 1)`. Establish `hgen` using `hasDim_genericPoint hX`. Use `set F' : Option ι → HermLB p := fun o => o.elim M L with hF'`.

Set `F : (Fin (D + 1) → HermLB p) → ℝ` to `fun K => T (D + 1) K (genericPoint X)`. Take `⟨Φ₀, hΦ₀, -⟩` from `GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK) (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'`. Establish `hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) = Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1))`. Introduce `m`. Take `⟨g, hg, hg'⟩` from `GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT (comb F' m)`.

Establish `h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X))` using `⟨g, hg, hg' _ _ hgen⟩`. Establish `h₂` using `hΦ₀ (fun _ => m)`. Rewrite `h₂` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]`. Conclude with `h₂.symm`.

Establish `hpol` using `GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n`. Rewrite using `[hpol]`. Set `m₀ : Option ι → ℤ` to `fun o => o.elim 1 0`. Set `m₁ : Option ι → ℤ` to `fun o => o.elim 0 n`. Establish `hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none = ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ))`.

Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast, Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]`. Simplify using `only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X)`.

Rewrite using `[LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]`. Use `hT.iso _ _ _ _ le_rfl hgen fun a => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun a => ?_) a` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Use `HermLB.icls_eq_iff.1 ?_` and prove the remaining obligations.

Simplify using `[icls_comb, Fintype.sum_option, m₀, F']`. Simplify using `only [Fin.cons_succ]`. Use `HermLB.icls_eq_iff.1 ?_` and prove the remaining obligations. Simplify using `[icls_comb, Fintype.sum_option, m₁, F']`. Rewrite using `[hval]`.

Use `set N := comb L n`. Establish `hrec` using `hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N) (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr`. Establish `e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X` using `by simp`. Rewrite `hrec` using `[e₁]`. Rewrite using `[hrec, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]`.

Use `congrArg (· - _) (finsum_congr fun z => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : (M.div hr).mult z = 0`. Simplify using `[hz]`. Take `⟨g, hg, hg'⟩` from `GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT N`. Take `rfl : h = g` from `hh.unique hX hg`.

Establish `e₂ : (𝟙 X : X ⟶ X) z = z` using `by simp`. Rewrite using `[e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]`.
-/
theorem arMix_of_mixHt : ArchInteg →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) →
    GlobalTheory.Published.ArMix := by
  intro hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  refine ⟨hAI k X p D hX M (comb L n) r hr, ?_⟩
  obtain ⟨T, hT⟩ := hEx k X p (isAmb_of_isArithVar hX) (D + 1)
  have hgen := hasDim_genericPoint hX
  set F' : Option ι → HermLB p := fun o => o.elim M L with hF'
  let F : (Fin (D + 1) → HermLB p) → ℝ := fun K => T (D + 1) K (genericPoint X)
  obtain ⟨Φ₀, hΦ₀, -⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK)
    (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'

  have hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) =
      Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1)) := by
    intro m
    obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT (comb F' m)
    have h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X)) :=
      ⟨g, hg, hg' _ _ hgen⟩
    have h₂ := hΦ₀ (fun _ => m)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
    rw [HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]
    exact h₂.symm
  have hpol := GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n
  rw [hpol]

  let m₀ : Option ι → ℤ := fun o => o.elim 1 0
  let m₁ : Option ι → ℤ := fun o => o.elim 0 n
  have hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none =
      ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast,
      Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]
    ring
  have hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D *
      MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X) := by
    rw [LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]
    refine hT.iso _ _ _ _ le_rfl hgen fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₀, F']
    · simp only [Fin.cons_succ]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₁, F']
  rw [hval]

  set N := comb L n
  have hrec := hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N)
    (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr
  have e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X := by simp
  rw [e₁] at hrec
  rw [hrec, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT N
  obtain rfl : h = g := hh.unique hX hg
  have e₂ : (𝟙 X : X ⟶ X) z = z := by simp
  rw [e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]

end GlobalTheory.MixHt
