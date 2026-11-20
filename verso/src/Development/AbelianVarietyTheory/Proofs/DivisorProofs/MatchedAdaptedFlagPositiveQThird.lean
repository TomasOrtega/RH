import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLinTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPlaneEisensteinStrip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanMaxCompactContainedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanConjugateInvariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.LevAutSup

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso S hS hσ c hc hσc j`. Establish `hB` using `hM.triple.base`. Establish `hlt` using `hM.triple.geo.lt`. Establish `hW` using `hM.triple.geo.hW`. Establish `e` using `hM.triple.geo.eBig`.

Establish `hsk` using `GlobalTheory.ThK.DescB.PrimeSplit.skew_sp hσ B hW.skew hH hiso`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ f hf K hK`. Take `⟨π, hπ, -⟩` from `GlobalTheory.PlaneFrame.frame_dual_gram F E σ B _ G.W _ _ d₁ (sp 0) H' i₀ i₁ hB.cm hW hH`.

Establish `hI : IsIsoPlane σ B H' G.W (sp 0)` using `IsIsoPlane.of_adapted hH hW.cartan (GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB _ d₁ G.W (sp 0) H' i₀ i₁ _ _ hW hH π hπ)`. Establish `hz : (a' : ℝ) / 2 < (a : ℝ) / 2`. Establish `: (a' : ℝ) < a` using `by exact_mod_cast hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hf` using `[lev_zero]`.

Unfold `alphaSpan at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f₀, hf₀, fa, fb, hs, h, hh, hex, hx'⟩` from `hx`. Conclude with `GlobalTheory.T.iso_plane_eisenstein_strip hKP F E σ hσ B hB _ _ G.W (sp 0) H' hW.skew hI X.α X.β _ _ hz c hc hσc f₀ (fun K₀ hK₀ => GlobalTheory.T.theta_span_conjugate_invariant hKP F E σ B a a' G X om om' R Rf hM hσ c hc hσc f₀ (hS hf₀) K₀ hK₀) fa fb hs h hh hex x hx' K hK`.

Consider the case `zero => exact isAut_const σ _ K 0`. Consider the case `add x y _ _ hx hy`. Use `GlobalTheory.UAut.AutClosed.isAut_add_smul hx hy 1 1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.

Consider the case `smul r x _ hx`. Use `GlobalTheory.UAut.AutClosed.isAut_add_smul hx (isAut_const σ _ K 0) r 0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Consider the case `succ j ih`.

Introduce `hj f hf K hK`. Establish `hI` using `hiso j (by omega)`. Establish `hz : (a' : ℝ) / 2 < zb a j`. Establish `hn : a' + 2 * (j + 1) < a` using `by omega`. Establish `hr : ((a' + 2 * (j + 1) : ℕ) : ℝ) < a` using `by exact_mod_cast hn`.

Unfold `zb`. Move the coercions through the operations in `at hr ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hf` using `[lev_succ]`. Unfold `alphaSpan at hf`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f₀, hf₀, fa, fb, hs, h, hh, hex, hx'⟩` from `hx`. Conclude with `GlobalTheory.T.iso_plane_eisenstein_strip hKP F E σ hσ B hB _ _ (sp j) (sp (j + 1)) (pl j) (hsk j (by omega)) hI X.α X.β _ _ hz c hc hσc f₀ (ih (by omega) f₀ hf₀) fa fb hs h hh hex x hx' K hK`. Consider the case `zero => exact isAut_const σ _ K 0`.

Consider the case `add x y _ _ hx hy`. Use `GlobalTheory.UAut.AutClosed.isAut_add_smul hx hy 1 1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Consider the case `smul r x _ hx`.

Use `GlobalTheory.UAut.AutClosed.isAut_add_smul hx (isAut_const σ _ K 0) r 0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.
-/
theorem lev_isAut_all : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) →
      ∀ S : Submodule ℂ (UA σ G.W.J → ℂ), S ≤ thetaSpanV B G X om R Rf ⊔ thetaSpanV' B G X om' R Rf →
      ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ j ≤ G.p,
      ∀ f ∈ Lev B X a a' H' sp pl S j,
      ∀ K : Subgroup (GAd σ (c • (sp j).J.map σ)), (∀ x ∈ K, (toGAd hσ (sp j).J hc).symm x ∈ KInf σ (sp j) B.emb) →
        IsAut σ (c • (sp j).J.map σ) K (fun x => f ((toGAd hσ (sp j).J hc).symm x)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso S hS hσ c hc hσc j
  have hB := hM.triple.base
  have hlt := hM.triple.geo.lt
  have hW := hM.triple.geo.hW
  have e := hM.triple.geo.eBig
  have hsk := GlobalTheory.ThK.DescB.PrimeSplit.skew_sp hσ B hW.skew hH hiso
  induction j with
  | zero =>
    intro _ f hf K hK
    obtain ⟨π, hπ, -⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B _ G.W _ _ d₁ (sp 0) H' i₀ i₁ hB.cm hW hH
    have hI : IsIsoPlane σ B H' G.W (sp 0) :=
      IsIsoPlane.of_adapted hH hW.cartan (GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB _ d₁ G.W (sp 0) H' i₀ i₁ _ _ hW hH π hπ)
    have hz : (a' : ℝ) / 2 < (a : ℝ) / 2 := by
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    rw [lev_zero] at hf
    unfold alphaSpan at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, hf₀, fa, fb, hs, h, hh, hex, hx'⟩ := hx
      exact GlobalTheory.T.iso_plane_eisenstein_strip hKP F E σ hσ B hB _ _ G.W (sp 0) H' hW.skew hI
        X.α X.β _ _ hz c hc hσc f₀
        (fun K₀ hK₀ => GlobalTheory.T.theta_span_conjugate_invariant hKP F E σ B a a' G X om om' R Rf hM hσ c hc hσc f₀ (hS hf₀) K₀ hK₀)
        fa fb hs h hh hex x hx' K hK
    | zero => exact isAut_const σ _ K 0
    | add x y _ _ hx hy =>
      convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx hy 1 1 using 1
      funext g
      simp
    | smul r x _ hx =>
      convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx (isAut_const σ _ K 0) r 0 using 1
      funext g
      simp
  | succ j ih =>
    intro hj f hf K hK
    have hI := hiso j (by omega)
    have hz : (a' : ℝ) / 2 < zb a j := by
      have hn : a' + 2 * (j + 1) < a := by omega
      have hr : ((a' + 2 * (j + 1) : ℕ) : ℝ) < a := by exact_mod_cast hn
      unfold zb
      push_cast at hr ⊢
      linarith
    rw [lev_succ] at hf
    unfold alphaSpan at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, hf₀, fa, fb, hs, h, hh, hex, hx'⟩ := hx
      exact GlobalTheory.T.iso_plane_eisenstein_strip hKP F E σ hσ B hB _ _ (sp j) (sp (j + 1)) (pl j) (hsk j (by omega)) hI
        X.α X.β _ _ hz c hc hσc f₀ (ih (by omega) f₀ hf₀) fa fb hs h hh hex x hx' K hK
    | zero => exact isAut_const σ _ K 0
    | add x y _ _ hx hy =>
      convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx hy 1 1 using 1
      funext g
      simp
    | smul r x _ hx =>
      convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx (isAut_const σ _ K 0) r 0 using 1
      funext g
      simp

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso S hS hσ c hc hσc j hj`. Establish `hB` using `hM.triple.base`. Establish `hW` using `hM.triple.geo.hW`. Establish `hsk` using `GlobalTheory.ThK.DescB.PrimeSplit.skew_sp hσ B hW.skew hH hiso`. Establish `hcart : ∀ w, IsCartan (Complex.I • (sp j).J.map (B.emb w).1) ((sp j).θ w)`.

Break down `j with _ | i` into its components or cases. Take `⟨π, hπ, -⟩` from `GlobalTheory.PlaneFrame.frame_dual_gram F E σ B _ G.W _ _ d₁ (sp 0) H' i₀ i₁ hB.cm hW hH`. Conclude with `GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB _ d₁ G.W (sp 0) H' i₀ i₁ _ _ hW hH π hπ`. Conclude with `(hiso i (by omega)).2.2.2.2.2.2.2.cartan`. Take `⟨K, hK, hKle⟩` from `GlobalTheory.T.cartan_max_compact_contained F E σ hσ B hB _ (sp j) (hsk j hj) hcart c hc hσc`.

Conclude with `⟨K, hK, hKle, fun f hf => lev_isAut_all hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso S hS hσ c hc hσc j hj f hf K hKle⟩`.
-/
theorem lev_isAut_maxCpt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) →
      ∀ S : Submodule ℂ (UA σ G.W.J → ℂ), S ≤ thetaSpanV B G X om R Rf ⊔ thetaSpanV' B G X om' R Rf →
      ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ j ≤ G.p,
      ∃ K : Subgroup (GAd σ (c • (sp j).J.map σ)), IsMaxCpt σ (c • (sp j).J.map σ) K ∧
        (∀ x ∈ K, (toGAd hσ (sp j).J hc).symm x ∈ KInf σ (sp j) B.emb) ∧
        ∀ f ∈ Lev B X a a' H' sp pl S j, IsAut σ (c • (sp j).J.map σ) K (fun x => f ((toGAd hσ (sp j).J hc).symm x)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso S hS hσ c hc hσc j hj
  have hB := hM.triple.base
  have hW := hM.triple.geo.hW
  have hsk := GlobalTheory.ThK.DescB.PrimeSplit.skew_sp hσ B hW.skew hH hiso
  have hcart : ∀ w, IsCartan (Complex.I • (sp j).J.map (B.emb w).1) ((sp j).θ w) := by
    rcases j with _ | i
    · obtain ⟨π, hπ, -⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B _ G.W _ _ d₁ (sp 0) H' i₀ i₁ hB.cm hW hH
      exact GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB _ d₁ G.W (sp 0) H' i₀ i₁ _ _ hW hH π hπ
    · exact (hiso i (by omega)).2.2.2.2.2.2.2.cartan
  obtain ⟨K, hK, hKle⟩ := GlobalTheory.T.cartan_max_compact_contained F E σ hσ B hB _ (sp j) (hsk j hj) hcart c hc hσc
  exact ⟨K, hK, hKle, fun f hf => lev_isAut_all hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso
    S hS hσ c hc hσc j hj f hf K hKle⟩

end GlobalTheory.ThK.DescB.LevAutSup

end
