import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedWeightSpaceBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetzStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfComplStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedTopWeightStrandStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedOfTemperedLpSumStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.WeilDeligne.TemperedCharPol

open GlobalTheory.WeilDeligne.PrimDecomp Module

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `map_absSpace_le e.toLinearMap (he (frob h)) _`. Introduce `v hv`. Use `⟨e.symm v, ?_, by simp⟩` and prove the remaining obligations. Conclude with `(mem_absSpace_iff e (he (frob h)) _ (e.symm v)).mp (by rw [LinearEquiv.apply_symm_apply]; exact hv)`.
-/
theorem map_wtSpace {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) (k : ℤ) :
    (wtSpace a k).map (e : V →ₗ[ℂ] V') = wtSpace b k := by
  apply le_antisymm
  · exact map_absSpace_le e.toLinearMap (he (frob h)) _
  · intro v hv
    refine ⟨e.symm v, ?_, by simp⟩
    exact (mem_absSpace_iff e (he (frob h)) _ (e.symm v)).mp (by rw [LinearEquiv.apply_symm_apply]; exact hv)

/- English proof (translation)
Take `⟨-, hNk⟩` from `GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a`. Establish `hpure` using `ha (frob h) deg_frob`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hq0` using `zero_lt_one.trans hq`. Establish `hind : iSupIndep (wtSpace a)`.

Use `iSupIndep_absSpace _ fun i j hij => ?_` and prove the remaining obligations. Rewrite `hij` using `[Real.rpow_right_inj hq0 hq.ne']`. Conclude with `(by linarith : (i : ℝ) = j)` after adjusting the coercions. Establish `htop : ⨆ i, wtSpace a i = ⊤` using `hpure.1`. Establish `hbij : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a i)`.

Introduce `i`. Simplify using `only [wtSpace, Int.cast_neg, Int.cast_natCast]`. Conclude with `hpure.2 i`. Conclude with `GlobalTheory.T.primitive_strand_complement_lefschetz _ (wtSpace a) a.N m hind htop hNk hbij hmtop`.
-/
theorem isCompl_of_tempered {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (ha : a.Tempered) (m : ℕ) (hmtop : ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) :
    IsCompl (strand a.N (wtSpace a (-(m : ℤ))) m) (lowPart (wtSpace a) a.N m) := by
  obtain ⟨-, hNk⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  have hpure := ha (frob h) deg_frob
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  have hind : iSupIndep (wtSpace a) := by
    refine iSupIndep_absSpace _ fun i j hij => ?_
    rw [Real.rpow_right_inj hq0 hq.ne'] at hij
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have htop : ⨆ i, wtSpace a i = ⊤ := hpure.1
  have hbij : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a i) := by
    intro i
    simp only [wtSpace, Int.cast_neg, Int.cast_natCast]
    exact hpure.2 i
  exact GlobalTheory.T.primitive_strand_complement_lefschetz _ (wtSpace a) a.N m hind htop hNk hbij hmtop

/- English proof (translation)
Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Conclude with `WD.sound ⟨e, he, fun v => by rw [Subsingleton.elim v 0]; simp⟩`. Take `⟨m, hm0, hmtop⟩` from `GlobalTheory.T.tempered_weight_space_bound E Ω A w h V a ha hV`. Establish `hmap` using `map_wtSpace a b e he`. Establish `hmtop' : ∀ k : ℤ, (m : ℤ) < k → wtSpace b k = ⊥` using `fun k hk => by`.

Rewrite using `[← hmap, hmtop k hk, Submodule.map_bot]`. Take `⟨hρa, hNa⟩` from `GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a`. Take `⟨hρb, hNb⟩` from `GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ b`. Take `⟨hBa, hCa⟩` from `GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ a m hρa hNa hmtop`. Take `⟨hBb, hCb⟩` from `GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ b m hρb hNb hmtop'`.

Establish `e1a` using `GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ a _ _ hBa hCa (isCompl_of_tempered a ha m hmtop)`. Establish `e1b` using `GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ b _ _ hBb hCb (isCompl_of_tempered b hb m hmtop')`. Establish `e2a` using `GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ a m (fun σ v hv => hρa _ σ v hv) hBa ha hmtop`. Establish `e2b` using `GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ b m (fun σ v hv => hρb _ σ v hv) hBb hb hmtop'`. Establish `hy : WD.mk (restrictρ a (wtSpace a (-(m : ℤ))) (fun σ v hv => hρa _ σ v hv)) = WD.mk (restrictρ b (wtSpace b (-(m : ℤ))) (fun σ v hv => hρb _ σ v hv))`.

Use `WD.sound ⟨(e.submoduleMap (wtSpace a (-(m : ℤ)))).trans (LinearEquiv.ofEq _ _ (hmap _)), fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[he]`. Simplify using the standard rewrite rules. Establish `hB : WD.mk (restrict a _ hBa) = WD.mk (restrict b _ hBb)` using `by rw [e2a, e2b, hy]`.

Establish `hcC : ∀ g, (WD.mk (restrict a _ hCa)).charPol g = (WD.mk (restrict b _ hCb)).charPol g`. Introduce `g`. Establish `hab : (WD.mk a).charPol g = (WD.mk b).charPol g`. Rewrite using `[WD.charPol_mk, WD.charPol_mk, ← LinearEquiv.charpoly_conj e]`. Use `congr 1`.

Use extensionality with `v`. Simplify using `[LinearEquiv.conj_apply, he]`. Rewrite `hab` using `[e1a, e1b, WD.charPol_lpSum, WD.charPol_lpSum, hB]`. Conclude with `mul_left_cancel₀ (WD.charPol_monic _ g).ne_zero hab`. Establish `htC : (WD.mk (restrict a _ hCa)).tempered` using `GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1a, WD.tempered_mk]; exact ha)`.

Establish `htC' : (WD.mk (restrict b _ hCb)).tempered` using `GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1b, WD.tempered_mk]; exact hb)`. Establish `hdim : (WD.mk (restrict a _ hCa)).lpDim < d`. Establish `h1` using `congrArg WD.lpDim e1a`. Rewrite `h1` using `[WD.lpDim_sum, WD.lpDim_mk, hd]`. Establish `hUpos : 0 < finrank ℂ (wtSpace a (-(m : ℤ)))` using `Nat.pos_of_ne_zero fun h0 => hm0 (Submodule.finrank_eq_zero.mp h0)`.

Establish `hBpos : 0 < (WD.mk (restrict a _ hBa)).lpDim`. Rewrite using `[WD.lpDim_mk]`. Conclude with `hUpos.trans_le (Submodule.finrank_mono (le_strand _ _ _))`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1a, e1b, hB, ih _ _ hdim htC htC' hcC]`.
-/
theorem step {d : ℕ}
    (ih : ∀ x y : WD h, x.lpDim < d → x.tempered → y.tempered → (∀ g, x.charPol g = y.charPol g) → x = y)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (hd : finrank ℂ V = d) (ha : a.Tempered) (hb : b.Tempered)
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) : WD.mk a = WD.mk b := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact WD.sound ⟨e, he, fun v => by rw [Subsingleton.elim v 0]; simp⟩
  obtain ⟨m, hm0, hmtop⟩ := GlobalTheory.T.tempered_weight_space_bound E Ω A w h V a ha hV
  have hmap := map_wtSpace a b e he
  have hmtop' : ∀ k : ℤ, (m : ℤ) < k → wtSpace b k = ⊥ := fun k hk => by
    rw [← hmap, hmtop k hk, Submodule.map_bot]
  obtain ⟨hρa, hNa⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  obtain ⟨hρb, hNb⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ b
  obtain ⟨hBa, hCa⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ a m hρa hNa hmtop
  obtain ⟨hBb, hCb⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ b m hρb hNb hmtop'
  have e1a := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ a _ _ hBa hCa (isCompl_of_tempered a ha m hmtop)
  have e1b := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ b _ _ hBb hCb (isCompl_of_tempered b hb m hmtop')
  have e2a := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ a m (fun σ v hv => hρa _ σ v hv) hBa ha hmtop
  have e2b := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ b m (fun σ v hv => hρb _ σ v hv) hBb hb hmtop'

  have hy : WD.mk (restrictρ a (wtSpace a (-(m : ℤ))) (fun σ v hv => hρa _ σ v hv)) =
      WD.mk (restrictρ b (wtSpace b (-(m : ℤ))) (fun σ v hv => hρb _ σ v hv)) := by
    refine WD.sound ⟨(e.submoduleMap (wtSpace a (-(m : ℤ)))).trans (LinearEquiv.ofEq _ _ (hmap _)),
      fun σ v => ?_, fun v => ?_⟩
    · apply Subtype.ext
      simp [he]
    · simp
  have hB : WD.mk (restrict a _ hBa) = WD.mk (restrict b _ hBb) := by rw [e2a, e2b, hy]

  have hcC : ∀ g, (WD.mk (restrict a _ hCa)).charPol g = (WD.mk (restrict b _ hCb)).charPol g := by
    intro g
    have hab : (WD.mk a).charPol g = (WD.mk b).charPol g := by
      rw [WD.charPol_mk, WD.charPol_mk, ← LinearEquiv.charpoly_conj e]
      congr 1
      ext v
      simp [LinearEquiv.conj_apply, he]
    rw [e1a, e1b, WD.charPol_lpSum, WD.charPol_lpSum, hB] at hab
    exact mul_left_cancel₀ (WD.charPol_monic _ g).ne_zero hab
  have htC : (WD.mk (restrict a _ hCa)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1a, WD.tempered_mk]; exact ha)
  have htC' : (WD.mk (restrict b _ hCb)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1b, WD.tempered_mk]; exact hb)
  have hdim : (WD.mk (restrict a _ hCa)).lpDim < d := by
    have h1 := congrArg WD.lpDim e1a
    rw [WD.lpDim_sum, WD.lpDim_mk, hd] at h1
    have hUpos : 0 < finrank ℂ (wtSpace a (-(m : ℤ))) :=
      Nat.pos_of_ne_zero fun h0 => hm0 (Submodule.finrank_eq_zero.mp h0)
    have hBpos : 0 < (WD.mk (restrict a _ hBa)).lpDim := by
      rw [WD.lpDim_mk]
      exact hUpos.trans_le (Submodule.finrank_mono (le_strand _ _ _))
    omega
  rw [e1a, e1b, hB, ih _ _ hdim htC htC' hcC]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h`. Establish `key : ∀ d : ℕ, ∀ x y : WD h, x.lpDim = d → x.tempered → y.tempered → (∀ g, x.charPol g = y.charPol g) → x = y`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`.

Introduce `x y hxd hx hy hc`. Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Proceed by induction on `y using WD.ind with`. Consider the case `hP n' b`.

Rewrite `hx`, `hy` using `[WD.tempered_mk]`. Rewrite `hxd` using `[WD.lpDim_mk]`. Take `⟨e, he⟩` from `GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n' a b (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)`. Conclude with `step (fun x y hxy => ih _ hxy x y rfl) a b hxd hx hy e he`. Conclude with `fun x y => key _ x y rfl`.
-/
theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (∀ g : Weil h, x.charPol g = y.charPol g) → x = y := by
  intro E Ω _ _ _ _ _ A w h
  have key : ∀ d : ℕ, ∀ x y : WD h, x.lpDim = d → x.tempered → y.tempered →
      (∀ g, x.charPol g = y.charPol g) → x = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x y hxd hx hy hc
      induction x using WD.ind with
      | hP n a =>
      induction y using WD.ind with
      | hP n' b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpDim_mk] at hxd
      obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n' a b
        (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
      exact step (fun x y hxy => ih _ hxy x y rfl) a b hxd hx hy e he
  exact fun x y => key _ x y rfl

end GlobalTheory.WeilDeligne.TemperedCharPol
