import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionZeroCase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqDetBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvTEqTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyDeriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralLabels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOfLabels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsumTrFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThJetOfNormalForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyInNf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.ArchProof

/- English proof (translation)
Establish `hi : Function.Injective fun χ : X => y + m • χ` using `fun a b h => by`. Establish `e : (m : ℤ) • a = (m : ℤ) • b` using `by simpa only [natCast_zsmul] using add_left_cancel h`. Conclude with `smul_right_injective X (by omega : (m : ℤ) ≠ 0) e`. Establish `hz : ∀ α ∉ Set.range fun χ : X => y + m • χ, A α = 0` using `fun α hα => h0 α fun χ e => hα ⟨χ, e.symm⟩`. Use `⟨(hi.summable_iff (f := fun α => ‖A α‖) fun α hα => by rw [hz α hα, norm_zero]).1 ?_, ?_⟩` and prove the remaining obligations.

Simplify `hB` using `only [Function.comp_def, h1]`. Rewrite using `[← hi.tsum_eq (f := A) fun α hα => by_contra fun h => hα (hz α h)]`. Simplify using `only [h1]`.
-/
theorem coset_series {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 1 ≤ m) (y : X) (A B : X → ℂ)
    (h1 : ∀ χ, A (y + m • χ) = B χ) (h0 : ∀ α, (∀ χ, α ≠ y + m • χ) → A α = 0) (hB : Summable fun χ => ‖B χ‖) :
    (Summable fun α => ‖A α‖) ∧ ∑' α, A α = ∑' χ, B χ := by
  have hi : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have e : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using add_left_cancel h
    exact smul_right_injective X (by omega : (m : ℤ) ≠ 0) e
  have hz : ∀ α ∉ Set.range fun χ : X => y + m • χ, A α = 0 := fun α hα => h0 α fun χ e => hα ⟨χ, e.symm⟩
  refine ⟨(hi.summable_iff (f := fun α => ‖A α‖) fun α hα => by rw [hz α hα, norm_zero]).1 ?_, ?_⟩
  · simpa only [Function.comp_def, h1] using hB
  · rw [← hi.tsum_eq (f := A) fun α hα => by_contra fun h => hα (hz α h)]
    simp only [h1]

/- English proof (translation)
Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `e : Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (Complex.log u / (2 * Real.pi * Complex.I))) = u`. Rewrite using `[mul_div_cancel₀ _ hne, Complex.exp_log hu]`. Use `⟨_, ?_, e⟩` and prove the remaining obligations. Rewrite `h` using `[← e, Complex.norm_exp, Real.exp_lt_exp]`.

Generalize the expression as in `Complex.log u / (2 * Real.pi * Complex.I) = w at h ⊢`. Establish `: ((2 * Real.pi * Complex.I : ℂ) * w).re = -(2 * Real.pi * w.im)` using `by simp`. Rewrite `h` using `[this]`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_log (T : ℝ) (u : ℂ) (hu : u ≠ 0) (h : ‖u‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) = u := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (Complex.log u / (2 * Real.pi * Complex.I))) = u := by
    rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]
  refine ⟨_, ?_, e⟩
  rw [← e, Complex.norm_exp, Real.exp_lt_exp] at h
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at h ⊢
  have : ((2 * Real.pi * Complex.I : ℂ) * w).re = -(2 * Real.pi * w.im) := by simp
  rw [this] at h
  have := Real.pi_pos
  nlinarith

/- English proof (translation)
Establish `: ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d`. Break down `Nat.eq_zero_or_pos D.P.g with h | h` into its components or cases. Conclude with `GlobalTheory.MBLow.DimZero.main κ R D h1 h2 N ν h`. Conclude with `GlobalTheory.T.exists_classicalThetaDescription_abelianPart κ hκ R D h1 h2 N ν h`. Take `⟨e, G, hK⟩` from `this`.

Take `⟨d, rfl⟩` from `GlobalTheory.MBLow.Cl.PsiFrame.exists_cd N D.P.g r bX e (GlobalTheory.MBLow.Cl.cub_of_geo R D h1 h2 N ν _ e ⟨G⟩) (GlobalTheory.MBLow.Cl.sym_of_geo R D h1 h2 N ν _ e ⟨G⟩)`. Conclude with `⟨d, G, hK⟩`.
-/
theorem exists_cd (κ : Rule) (hκ : Rule4 κ) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {r : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) :
    ∃ (d : CD N D.P.g r bX) (_ : Geo ν d.toAB), KeyOK κ ν d.toAB := by
  have : ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
    rcases Nat.eq_zero_or_pos D.P.g with h | h
    · exact GlobalTheory.MBLow.DimZero.main κ R D h1 h2 N ν h
    · exact GlobalTheory.T.exists_classicalThetaDescription_abelianPart κ hκ R D h1 h2 N ν h
  obtain ⟨e, G, hK⟩ := this
  obtain ⟨d, rfl⟩ := GlobalTheory.MBLow.Cl.PsiFrame.exists_cd N D.P.g r bX e (GlobalTheory.MBLow.Cl.cub_of_geo R D h1 h2 N ν _ e ⟨G⟩) (GlobalTheory.MBLow.Cl.sym_of_geo R D h1 h2 N ν _ e ⟨G⟩)
  exact ⟨d, G, hK⟩

/- English proof (translation)
Take `⟨hb, ho, hl, hr⟩` from `hA`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `hW : ∀ j, ∃ W, IsD ν d.toAB W (gm j).b ∧ ∀ l, j = σ.symm (Sum.inr l) → W = 0`. Introduce `j`. Distinguish the cases in `h : ∃ l, j = σ.symm (Sum.inr l)`.

Take `⟨l, rfl⟩` from `h`. Conclude with `⟨0, by rw [(hr l).1]; exact GlobalTheory.MBLow.Cl.DZero.isD_zero R D h1 h2 N ν _ d.toAB, fun _ _ => rfl⟩`. Take `⟨o, hz, hp⟩` from `ho j`. Take `⟨W, hW⟩` from `G.dif (gm j).b (hp.1.symm.trans (congrArg (·.left) hz.1))`. Conclude with `⟨W, hW, fun l e => absurd ⟨l, e⟩ h⟩`.

Use `choose W hW hW0 using hW`. Use `choose Z c₀ hZ hT hJ using fun j => GlobalTheory.MBLow.Cl.jet_family_deriv R D h1 h2 N ν _ r g bX d σ G (gm j) (W j) (ho j) (hW j)`. Establish `hs : ∀ {n : ℕ} (v : Fin n → ℂ), (2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • v = v` using `fun v => inv_smul_smul₀ hne v`. Set `Mx : Matrix (Fin g) (Fin g) ℂ` to `fun j => (2 * Real.pi * Complex.I : ℂ) • Z j`. Set `MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ` to `fun i => (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))`.

Establish `hdet : Mx.det = MB.det`. Use `GlobalTheory.MBLow.Cl.det_eq_det_block _ r g σ Mx MB (fun i => ?_) fun l => ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) (hZ (σ.symm (Sum.inl i)))`. Use `congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) ((hZ (σ.symm (Sum.inr l))).trans (hW0 _ l rfl))` as an intermediate fact. Simplify using `only [smul_zero] at this`.

Conclude with `this`. Use function extensionality and compare the values at `l'`. Establish `e` using `congrArg TrivSqZeroExt.snd (((hT _ (hW0 _ l rfl) (bX l')).symm).trans ((hr l).2 (bX l')))`. Establish `hc : co bX (bX l') = Pi.single l' 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `by_cases hi : i = l' <;> simp [co, hi, Finsupp.single_apply, eq_comm]`. Rewrite `e` using `[hc, single_one_dotProduct]`. Simplify using `only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add, Module.Basis.repr_self] at e`. Use `e.trans ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hi : l' = l <;> simp [hi, Finsupp.single_apply]`.

Take `⟨hd, hv⟩` from `hK vB (fun i => (gm (σ.symm (Sum.inl i))).b) MB k₀ hb hl (fun i => by`. Express the relevant statement in the definitionally equal form `IsD ν d.toAB ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))) _`. Rewrite using `[hs]`. Conclude with `hW _) hk`. Use `⟨Mx, c₀, hdet ▸ hd, hdet ▸ hv, fun j k s f α F hs' hF hY => ?_⟩` and prove the remaining obligations.

Establish `: (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j = Z j` using `hs _`. Rewrite using `[this]`. Conclude with `hJ j k s f α F hs' hF hY`.
-/
theorem exists_vec (κ : Rule) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {g r : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N D.P.g r bX) (G : Geo ν d.toAB) (hK : KeyOK κ ν d.toAB)
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R ℂ))
    (hA : Adapted ν vB bX σ gm) (k₀ : ℂ) (hk : BKey κ ν vB k₀) :
    ∃ (Mx : Matrix (Fin g) (Fin g) ℂ) (c₀ : Fin g → ℂ), Mx.det ≠ 0 ∧ k₀ * d.c ^ 8 = Mx.det ^ 4 ∧
      ∀ j (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F →
        (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) →
        (jc ν s (gm j) α).fst / ν.rg ^ k = F 0 ∧ (jc ν s (gm j) α).snd / ν.rg ^ k =
          fderiv ℂ F 0 ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) + k * c₀ j * F 0 := by
  obtain ⟨hb, ho, hl, hr⟩ := hA
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hW : ∀ j, ∃ W, IsD ν d.toAB W (gm j).b ∧ ∀ l, j = σ.symm (Sum.inr l) → W = 0 := by
    intro j
    by_cases h : ∃ l, j = σ.symm (Sum.inr l)
    · obtain ⟨l, rfl⟩ := h
      exact ⟨0, by rw [(hr l).1]; exact GlobalTheory.MBLow.Cl.DZero.isD_zero R D h1 h2 N ν _ d.toAB, fun _ _ => rfl⟩
    · obtain ⟨o, hz, hp⟩ := ho j
      obtain ⟨W, hW⟩ := G.dif (gm j).b (hp.1.symm.trans (congrArg (·.left) hz.1))
      exact ⟨W, hW, fun l e => absurd ⟨l, e⟩ h⟩
  choose W hW hW0 using hW
  choose Z c₀ hZ hT hJ using fun j => GlobalTheory.MBLow.Cl.jet_family_deriv R D h1 h2 N ν _ r g bX d σ G (gm j) (W j) (ho j) (hW j)
  have hs : ∀ {n : ℕ} (v : Fin n → ℂ), (2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • v = v :=
    fun v => inv_smul_smul₀ hne v
  let Mx : Matrix (Fin g) (Fin g) ℂ := fun j => (2 * Real.pi * Complex.I : ℂ) • Z j
  let MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := fun i => (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))
  have hdet : Mx.det = MB.det := by
    refine GlobalTheory.MBLow.Cl.det_eq_det_block _ r g σ Mx MB (fun i => ?_) fun l => ⟨?_, ?_⟩
    · exact congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) (hZ (σ.symm (Sum.inl i)))
    · have := congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) ((hZ (σ.symm (Sum.inr l))).trans (hW0 _ l rfl))
      simp only [smul_zero] at this
      exact this
    · funext l'
      have e := congrArg TrivSqZeroExt.snd (((hT _ (hW0 _ l rfl) (bX l')).symm).trans ((hr l).2 (bX l')))
      have hc : co bX (bX l') = Pi.single l' 1 := by
        funext i
        by_cases hi : i = l' <;> simp [co, hi, Finsupp.single_apply, eq_comm]
      rw [hc, single_one_dotProduct] at e
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add, Module.Basis.repr_self] at e
      refine e.trans ?_
      by_cases hi : l' = l <;> simp [hi, Finsupp.single_apply]
  obtain ⟨hd, hv⟩ := hK vB (fun i => (gm (σ.symm (Sum.inl i))).b) MB k₀ hb hl (fun i => by
    change IsD ν d.toAB ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))) _
    rw [hs]; exact hW _) hk
  refine ⟨Mx, c₀, hdet ▸ hd, hdet ▸ hv, fun j k s f α F hs' hF hY => ?_⟩
  have : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j = Z j := hs _
  rw [this]
  exact hJ j k s f α F hs' hF hY

/- English proof (translation)
Introduce `κ hκ R _ _ _ _ D h1 h2 _ N ν g r m k hg hm hmk β ζ q hq s hs vB bX σ gm hA k₀ hk`. Establish `hm1 : 1 ≤ m` using `hm.pos`. Take `⟨d, G, hK⟩` from `exists_cd κ hκ h1 h2 ν bX`. Take `⟨Mx, c₀, hdet, hval, hJ⟩` from `exists_vec κ h1 h2 ν d G hK vB σ gm hA k₀ hk`. Take `⟨M, Nn, hrep, hlab⟩` from `GlobalTheory.MBLow.Cl.exists_integral_labels N _ r g bX d σ (m ^ 2) (by positivity) ζ q hq`.

Take `⟨T, hT⟩` from `GlobalTheory.MBLow.Cl.BlockPos.full_posDef N _ r g bX d σ k β`. Take `⟨hdiff, htw⟩` from `GlobalTheory.MBLow.Cl.term_smul_bmat N _ r g bX d σ`. Use `⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun u hu0 hu => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hwu⟩` from `exists_log T u hu0 hu`. Take `⟨hS, hsym, hpos⟩` from `hT w hw`.

Use `set S := w • bmat bX β with hSdef`. Use `set V : Fin g → Fin g → ℂ := fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j with hV`. Establish `key : ∀ a j, ((Summable fun α => ‖(jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧ ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat = d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) ∧ (Summable fun …`. Introduce `a j`. Take `⟨f, hf, hf1, hf0⟩` from `hs a`.

Rewrite `hf1`, `hf0` using `[(hrep a).1]`. Use `set y := ∑ l, tP σ (Nn a) l • bX l with hy`. Take `⟨s1, s2, t1, t2⟩` from `GlobalTheory.MBLow.Cl.term_sum_and_fderiv N _ r g bX d σ S hS hpos m (M a) (Nn a) (V j)`. Establish `on : ∀ χ, _` using `fun χ => hJ j _ (s a) f (y + m • χ) (fun Y => d.c * d.term σ 0 m (M a) (Nn a) χ Y) hf ((hdiff _ _ _ _ _).const_mul _) fun Y h hY => by`. Rewrite using `[hf1, GlobalTheory.MBLow.Cl.evT_eq_term N _ r g bX d σ m hm (M a) (Nn a) (q a) (hrep a) Y h hY χ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `off : ∀ α, (∀ χ, α ≠ y + m • χ) → _` using `fun α hα => hJ j _ (s a) f α (fun _ => 0) hf (differentiable_const _) fun Y h hY => by rw [hf0 α hα]; simp`. Establish `tw : ∀ χ, d.term σ S m (M a) (Nn a) χ = fun Z => d.term σ 0 m (M a) (Nn a) χ Z * u ^ (β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat` using `fun χ => funext fun Z => by`. Rewrite using `[← hwu]`. Conclude with `htw k m β hm1 hmk w (M a) (Nn a) χ Z`.

Establish `A` using `coset_series hm1 y (fun α => (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) (fun χ => d.c * d.term σ S m (M a) (Nn a) χ 0) (fun χ => by simp only [(on χ).1, tw χ]; ring) (fun α hα => by simp only [(off α hα).1, zero_mul]) (by simpa only [norm_mul …`. Establish `B` using `coset_series hm1 y (fun α => (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) (fun χ => d.c * fderiv ℂ (d.term σ S m (M a) (Nn a) χ) 0 (V j) + ((m ^ 2 : ℕ) * c₀ j) * (d.c * d.term σ S m (M a) (Nn a) χ 0)) (fun χ => by`. Simplify using `only [(on χ).2, tw χ]`. Rewrite using `[fderiv_const_mul (hdiff _ _ _ _ _ _), fderiv_mul_const (hdiff _ _ _ _ _ _)]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul, hV]`.

Use the proof step `ring)`. Use the proof step `(fun α hα => by simp [(off α hα).2])`. Use the proof step `(((s2.of_norm.mul_left d.c).add ((s1.of_norm.mul_left d.c).mul_left _)).norm)`. Use `⟨⟨A.1, ?_⟩, B.1, ?_⟩` and prove the remaining obligations. Rewrite using `[A.2, tsum_mul_left, t1]`.

Rewrite using `[B.2, (s2.of_norm.mul_left d.c).tsum_add ((s1.of_norm.mul_left d.c).mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left, t1, t2]`. Establish `hrg : ν.rg ^ (m ^ 2) ≠ 0` using `pow_ne_zero _ (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)`. Establish `hmul : ∀ (x v : N.X → ℂ), (Summable fun α => ‖x α / ν.rg ^ (m ^ 2) * v α‖) → Summable fun α => ‖x α * v α‖`. Introduce `x v h`. Use `(h.mul_left ‖ν.rg ^ (m ^ 2)‖).congr fun α => ?_` and prove the remaining obligations.

Rewrite using `[← norm_mul, ← _root_.mul_assoc, mul_div_cancel₀ _ hrg]`. Use `⟨fun a j => ⟨hmul _ _ (key a j).1.1, hmul _ _ (key a j).2.1⟩, ?_⟩` and prove the remaining obligations. Establish `ha : Half (d.aF σ)` using `fun i => by`. Unfold `CD.aF`. Break down `σ i with i | i` into its components or cases.

Conclude with `d.ha i`. Conclude with `Or.inl rfl`. Establish `hb : Half (d.bF σ)` using `fun i => by`. Unfold `CD.bF`. Break down `σ i with i | i` into its components or cases.

Conclude with `d.hb i`. Conclude with `d.hb2 i`. Take `⟨x₀, hg₀, U, hNF⟩` from `GlobalTheory.MBLow.Cl.exists_keyIn_nf g (d.full σ S) (d.aF σ) (d.bF σ) d.c Mx hg hsym hpos ha hb d.hc hdet`. Take `⟨lev, hlev⟩` from `GlobalTheory.MBLow.LabelLevel.exists_level_of_labels g x₀ hg₀ U _ _ _ _ _ hNF (m ^ 2) (by positivity) ζ hq.1 M Nn hlab`. Use `⟨x₀, hg₀, lev, fun a => d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0, fun a j => (key a j).1.2.symm, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [fun a j => (key a j).2.2]`. Conclude with `GlobalTheory.MBLow.Cl.thJet_of_normalForm g x₀ hg₀ U _ _ _ _ _ hNF m hm _ M Nn _ (fun a => by rw [hlev a, Nat.cast_pow]) _`. Conclude with `mul_right_cancel₀ (pow_ne_zero 8 d.hc) ((GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 g x₀ hg₀ U _ _ _ _ Mx hNF).2.trans hval.symm)`.
-/
theorem arch_of_rule4 : ∀ κ : Rule, Rule4 κ → Arch κ := by
  intro κ hκ R _ _ _ _ D h1 h2 _ N ν g r m k hg hm hmk β ζ q hq s hs vB bX σ gm hA k₀ hk
  have hm1 : 1 ≤ m := hm.pos
  obtain ⟨d, G, hK⟩ := exists_cd κ hκ h1 h2 ν bX
  obtain ⟨Mx, c₀, hdet, hval, hJ⟩ := exists_vec κ h1 h2 ν d G hK vB σ gm hA k₀ hk
  obtain ⟨M, Nn, hrep, hlab⟩ := GlobalTheory.MBLow.Cl.exists_integral_labels N _ r g bX d σ (m ^ 2) (by positivity) ζ q hq
  obtain ⟨T, hT⟩ := GlobalTheory.MBLow.Cl.BlockPos.full_posDef N _ r g bX d σ k β
  obtain ⟨hdiff, htw⟩ := GlobalTheory.MBLow.Cl.term_smul_bmat N _ r g bX d σ
  refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun u hu0 hu => ?_⟩
  obtain ⟨w, hw, hwu⟩ := exists_log T u hu0 hu
  obtain ⟨hS, hsym, hpos⟩ := hT w hw
  set S := w • bmat bX β with hSdef
  set V : Fin g → Fin g → ℂ := fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j with hV
  have key : ∀ a j,
      ((Summable fun α => ‖(jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) ∧
      (Summable fun α => ‖(jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a)) 0 (V j) +
            ((m ^ 2 : ℕ) * c₀ j) * (d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) := by
    intro a j
    obtain ⟨f, hf, hf1, hf0⟩ := hs a
    rw [(hrep a).1] at hf1 hf0
    set y := ∑ l, tP σ (Nn a) l • bX l with hy
    obtain ⟨s1, s2, t1, t2⟩ := GlobalTheory.MBLow.Cl.term_sum_and_fderiv N _ r g bX d σ S hS hpos m (M a) (Nn a) (V j)
    have on : ∀ χ, _ := fun χ => hJ j _ (s a) f (y + m • χ) (fun Y => d.c * d.term σ 0 m (M a) (Nn a) χ Y) hf
      ((hdiff _ _ _ _ _).const_mul _) fun Y h hY => by
        rw [hf1, GlobalTheory.MBLow.Cl.evT_eq_term N _ r g bX d σ m hm (M a) (Nn a) (q a) (hrep a) Y h hY χ]; ring
    have off : ∀ α, (∀ χ, α ≠ y + m • χ) → _ := fun α hα => hJ j _ (s a) f α (fun _ => 0) hf
      (differentiable_const _) fun Y h hY => by rw [hf0 α hα]; simp
    have tw : ∀ χ, d.term σ S m (M a) (Nn a) χ = fun Z => d.term σ 0 m (M a) (Nn a) χ Z *
        u ^ (β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat := fun χ => funext fun Z => by
      rw [← hwu]; exact htw k m β hm1 hmk w (M a) (Nn a) χ Z
    have A := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * d.term σ S m (M a) (Nn a) χ 0)
      (fun χ => by simp only [(on χ).1, tw χ]; ring) (fun α hα => by simp only [(off α hα).1, zero_mul])
      (by simpa only [norm_mul] using s1.mul_left ‖d.c‖)
    have B := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * fderiv ℂ (d.term σ S m (M a) (Nn a) χ) 0 (V j) +
        ((m ^ 2 : ℕ) * c₀ j) * (d.c * d.term σ S m (M a) (Nn a) χ 0))
      (fun χ => by
        simp only [(on χ).2, tw χ]
        rw [fderiv_const_mul (hdiff _ _ _ _ _ _), fderiv_mul_const (hdiff _ _ _ _ _ _)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hV]
        ring)
      (fun α hα => by simp [(off α hα).2])
      (((s2.of_norm.mul_left d.c).add ((s1.of_norm.mul_left d.c).mul_left _)).norm)
    refine ⟨⟨A.1, ?_⟩, B.1, ?_⟩
    · rw [A.2, tsum_mul_left, t1]
    · rw [B.2, (s2.of_norm.mul_left d.c).tsum_add ((s1.of_norm.mul_left d.c).mul_left _), tsum_mul_left, tsum_mul_left,
        tsum_mul_left, t1, t2]
  have hrg : ν.rg ^ (m ^ 2) ≠ 0 := pow_ne_zero _ (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hmul : ∀ (x v : N.X → ℂ), (Summable fun α => ‖x α / ν.rg ^ (m ^ 2) * v α‖) → Summable fun α => ‖x α * v α‖ := by
    intro x v h
    refine (h.mul_left ‖ν.rg ^ (m ^ 2)‖).congr fun α => ?_
    rw [← norm_mul, ← _root_.mul_assoc, mul_div_cancel₀ _ hrg]
  refine ⟨fun a j => ⟨hmul _ _ (key a j).1.1, hmul _ _ (key a j).2.1⟩, ?_⟩
  have ha : Half (d.aF σ) := fun i => by
    unfold CD.aF
    rcases σ i with i | i
    · exact d.ha i
    · exact Or.inl rfl
  have hb : Half (d.bF σ) := fun i => by
    unfold CD.bF
    rcases σ i with i | i
    · exact d.hb i
    · exact d.hb2 i
  obtain ⟨x₀, hg₀, U, hNF⟩ := GlobalTheory.MBLow.Cl.exists_keyIn_nf g (d.full σ S) (d.aF σ) (d.bF σ) d.c Mx hg hsym hpos ha hb d.hc hdet
  obtain ⟨lev, hlev⟩ := GlobalTheory.MBLow.LabelLevel.exists_level_of_labels g x₀ hg₀ U _ _ _ _ _ hNF (m ^ 2) (by positivity) ζ hq.1 M Nn hlab
  refine ⟨x₀, hg₀, lev, fun a => d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0,
    fun a j => (key a j).1.2.symm, ?_, ?_⟩
  · simp only [fun a j => (key a j).2.2]
    exact GlobalTheory.MBLow.Cl.thJet_of_normalForm g x₀ hg₀ U _ _ _ _ _ hNF m hm _ M Nn _ (fun a => by rw [hlev a, Nat.cast_pow]) _
  · exact mul_right_cancel₀ (pow_ne_zero 8 d.hc) ((GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 g x₀ hg₀ U _ _ _ _ Mx hNF).2.trans hval.symm)

end GlobalTheory.MBLow.ArchProof

end
