import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmExistsHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObject
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZeroStatement

namespace GlobalTheory.FlatCore.CMPointExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx`. Establish `hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ` using `(LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2 ((GlobalTheory.T.principalTriple_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1`. Take `⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩` from `LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib`. Take `⟨L, hL, hm⟩` from `LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood`. Establish `hdet` using `LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL`.

Establish `heig` using `LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL`. Take `⟨mm, e, src, U, ℓ⟩` from `L`. Establish `hmm : mm = Dw.mult`. Use function extensionality and compare the values at `b`. Unfold `Datum.mult`.

Use `split_ifs with h`. Conclude with `(hm b).1 h`. Conclude with `(hm b).2 h`. Substitute `hmm` using the available equality. Use `choose w hw hU using hL.2.2.1`.

Take `⟨y, hy, -, -⟩` from `GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i => GlobalTheory.T.isEigenvectorAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by`. Establish `h` using `heig τ i (w (e ⟨τ, i⟩)) (hw _) a`. Rewrite using `[← hoa]`. Conclude with `h))`. Conclude with `⟨y, hy⟩`.
-/
theorem exists_frPt_of_cmObj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∃ y : FrPt Xo c K, y.x = x := by
  intro E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx
  have hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2
      ((GlobalTheory.T.principalTriple_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib
  obtain ⟨L, hL, hm⟩ := LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL
  have heig := LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL
  obtain ⟨mm, e, src, U, ℓ⟩ := L
  have hmm : mm = Dw.mult := by
    funext b
    unfold Datum.mult
    split_ifs with h
    · exact (hm b).1 h
    · exact (hm b).2 h
  subst hmm
  choose w hw hU using hL.2.2.1
  obtain ⟨y, hy, -, -⟩ := GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i =>
    GlobalTheory.T.isEigenvectorAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by
      have h := heig τ i (w (e ⟨τ, i⟩)) (hw _) a
      rw [← hoa]
      exact h))
  exact ⟨y, hy⟩

end GlobalTheory.FlatCore.CMPointExistence

namespace GlobalTheory.FlatCore

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL Z`. Set `σ₀ : c.F →+* ℂ` to `c.F.val.toRingHom`. Establish `hσ₀ : GoodEmb c σ₀` using `rfl`. Take `⟨k, hk⟩` from `framesOn_eq_model E H Dw l Xo c r U x hL Z σ₀ hσ₀`. Establish `hU` using `hL.unf σ₀ hσ₀`.

Establish `hr : 0 < r` using `by rw [hU.1]; have := hL.pos; omega`. Take `⟨D₁, hD₁p, hD₁q⟩` from `hL.line`. Take `⟨x₁, hx₁, lam, h1, h2, h3, h4, h5, h6⟩` from `GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain E r ((U σ₀).X k)`. Set `x₀ : ((U σ₀).X k).dom` to `⟨x₁, hx₁⟩`. Take `⟨W⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k x₀`.

Take `⟨Zl⟩` from `GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero E H Dw l Xo c r (U σ₀) hU hr D₁ hD₁p hD₁q k x₀ W lam h1 h2 h3 h4 h5 h6`. Establish `hfd : FiniteDimensional ℚ c.F` using `c.fin`. Take `⟨K₁, nf, hk1, ρ, X, y, t₀, m, m', -, -, -, -, -, hle, hρ, -, hy, hpt, -⟩` from `GlobalTheory.CM.cmExists_holds E H Dw l Xo W.g _ W.F (W.ik k) W.Pm W.per Zl c.F hfd`. Use `letI : Algebra c.F K₁ := (IntermediateField.inclusion hle).toRingHom.toAlgebra`. Use `letI : StarRing (𝓞 E) := H.starRing`.

Take `⟨Φ⟩` from `GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo K₁ y (by have := hL.pos; omega)`. Take `⟨n, -⟩` from `(GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ Xo.univ.t t₀ Φ.T.t y y (𝟙 _) m Φ.m (Category.id_comp _).symm).1`. Choose the witnesses or unpack the hypotheses as in `⟨mB⟩ : Nonempty (SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁))) := by`. Take `⟨mm, -⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabComp ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubComp E H _ _ _ X.B.t t₀ Φ.T.t _ _ m' n`. Rewrite `mm` using `[Category.id_comp]`.

Conclude with `⟨mm⟩`. Take `⟨yF, hyF⟩` from `GlobalTheory.FlatCore.CMPointExistence.exists_frPt_of_cmObj E H Dw l Xo c (fun _ => rfl) K₁ ρ (algebraMap K₁ ℂ) X (1 + ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖) y Φ mB (fun τ => by show τ (H.rt : E) = H.rt0 ↔ _`. Rewrite using `[← hρ, Subtype.ext_iff]`. Conclude with `Iff.rfl) (fun j τ => by`. Establish `h1 : ‖τ (X.hh j : E)‖ ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `h0 : 0 ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Use the proof step `nlinarith) hy`. Use `⟨K₁, inferInstance, nf, inferInstance, yF, ρ, algebraMap K₁ ℂ, X, t₀, ?_, ⟨hyF ▸ m⟩, ⟨m'⟩, fun τ => ?_⟩` and prove the remaining obligations. Establish `hmem : (⟨k, x₁⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z` using `by rw [hk]; exact ⟨rfl, hx₁⟩`.

Take `⟨h', hon⟩` from `hmem`. Establish `hpt' : ((U σ₀).un k x₀).x = spMap (algebraMap K₁ ℂ) ≫ yF.x` using `by rw [hyF, hpt]; exact W.pt`. Establish `key : ptF ((U σ₀).un k x₀) = spMap (algebraMap K₁ ℂ) ≫ ptF yF`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Unfold `ptF erw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]`.

Conclude with `hpt'`. Unfold `ptF erw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd] erw [← Spec.map_comp]`. Both sides reduce to the same expression. Introduce `s`. Set `s' : Sp (CAt σ₀)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)`.

Establish `h7` using `hon s'`. Express the relevant statement in the definitionally equal form `ptF ((U σ₀).un k x₀) s' ∈ _ at h7`. Rewrite `h7` using `[key]`. Establish `hs : (spMap (algebraMap K₁ ℂ)) s' = s` using `Subsingleton.elim (α := PrimeSpectrum K₁) _ _`. Rewrite using `[← hs]`.

Conclude with `h7`. Conclude with `Subtype.ext (hρ.trans τ.2.symm)`.
-/
theorem exists_cmPt_on_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  let σ₀ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c σ₀ := rfl
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ₀ hσ₀
  have hU := hL.unf σ₀ hσ₀
  have hr : 0 < r := by rw [hU.1]; have := hL.pos; omega
  obtain ⟨D₁, hD₁p, hD₁q⟩ := hL.line
  obtain ⟨x₁, hx₁, lam, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain E r ((U σ₀).X k)
  let x₀ : ((U σ₀).X k).dom := ⟨x₁, hx₁⟩
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k x₀
  obtain ⟨Zl⟩ := GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero E H Dw l Xo c r (U σ₀) hU hr D₁ hD₁p hD₁q k x₀ W lam h1 h2 h3 h4 h5 h6
  have hfd : FiniteDimensional ℚ c.F := c.fin
  obtain ⟨K₁, nf, hk1, ρ, X, y, t₀, m, m', -, -, -, -, -, hle, hρ, -, hy, hpt, -⟩ :=
    GlobalTheory.CM.cmExists_holds E H Dw l Xo W.g _ W.F (W.ik k) W.Pm W.per Zl c.F hfd
  letI : Algebra c.F K₁ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨Φ⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo K₁ y (by have := hL.pos; omega)
  obtain ⟨n, -⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ Xo.univ.t t₀ Φ.T.t y y (𝟙 _) m Φ.m
    (Category.id_comp _).symm).1
  obtain ⟨mB⟩ : Nonempty (SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁))) := by
    obtain ⟨mm, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabComp ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubComp E H _ _ _ X.B.t t₀ Φ.T.t _ _ m' n
    rw [Category.id_comp] at mm
    exact ⟨mm⟩
  obtain ⟨yF, hyF⟩ := GlobalTheory.FlatCore.CMPointExistence.exists_frPt_of_cmObj E H Dw l Xo c (fun _ => rfl) K₁ ρ (algebraMap K₁ ℂ) X
    (1 + ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖) y Φ mB
    (fun τ => by
      show τ (H.rt : E) = H.rt0 ↔ _
      rw [← hρ, Subtype.ext_iff]
      exact Iff.rfl) (fun j τ => by
      have h1 : ‖τ (X.hh j : E)‖ ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        calc ‖τ (X.hh j : E)‖ ≤ ∑ τ' : E →+* ℂ, ‖τ' (X.hh j : E)‖ :=
              Finset.single_le_sum (f := fun τ' : E →+* ℂ => ‖τ' (X.hh j : E)‖) (fun _ _ => norm_nonneg _)
                (Finset.mem_univ τ)
          _ ≤ _ := Finset.single_le_sum (f := fun j' => ∑ τ' : E →+* ℂ, ‖τ' (X.hh j' : E)‖)
                (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      have h0 : 0 ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith) hy
  refine ⟨K₁, inferInstance, nf, inferInstance, yF, ρ, algebraMap K₁ ℂ, X, t₀, ?_, ⟨hyF ▸ m⟩, ⟨m'⟩, fun τ => ?_⟩
  · have hmem : (⟨k, x₁⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z := by rw [hk]; exact ⟨rfl, hx₁⟩
    obtain ⟨h', hon⟩ := hmem
    have hpt' : ((U σ₀).un k x₀).x = spMap (algebraMap K₁ ℂ) ≫ yF.x := by rw [hyF, hpt]; exact W.pt
    have key : ptF ((U σ₀).un k x₀) = spMap (algebraMap K₁ ℂ) ≫ ptF yF := by
      apply Limits.pullback.hom_ext
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
        exact hpt'
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]
        erw [← Spec.map_comp]
        rfl
    intro s
    let s' : Sp (CAt σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h7 := hon s'
    change ptF ((U σ₀).un k x₀) s' ∈ _ at h7
    rw [key] at h7
    have hs : (spMap (algebraMap K₁ ℂ)) s' = s := Subsingleton.elim (α := PrimeSpectrum K₁) _ _
    rw [← hs]
    exact h7
  · exact Subtype.ext (hρ.trans τ.2.symm)

end GlobalTheory.FlatCore
