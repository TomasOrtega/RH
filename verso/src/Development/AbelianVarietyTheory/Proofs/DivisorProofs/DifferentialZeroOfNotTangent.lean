import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.UnifOffOrigin

/- English proof (translation)
Establish `hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥`. Introduce `h`. Apply `𝔠.ne_zero` to reduce the goal to its premises. Conclude with `(FractionalIdeal.coeToSubmodule_eq_bot).mp h`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).mp hne`.

Take `⟨a, ha, hint⟩` from `(𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional`. Take `⟨y, hy⟩` from `hint x hx`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hy0 : (algebraMap (𝓞 F) F y) ≠ 0`. Rewrite using `[hy, Algebra.smul_def]`.

Conclude with `mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0`. Use `⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y`. Rewrite using `[mul_comm a y, mul_smul, ← hy, Algebra.smul_def]`.

Use `show 0 < τ ((a * y) • x)`. Rewrite using `[hval, map_mul]`. Establish `: τ (algebraMap (𝓞 F) F y) ≠ 0` using `(map_ne_zero τ).mpr hy0`. Conclude with `mul_self_pos.mpr this`.
-/
theorem exists_totPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h
    apply 𝔠.ne_zero
    exact (FractionalIdeal.coeToSubmodule_eq_bot).mp h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 := by
    rw [hy, Algebra.smul_def]
    exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0
  refine ⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  intro τ
  have hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y := by
    rw [mul_comm a y, mul_smul, ← hy, Algebra.smul_def]
  show 0 < τ ((a * y) • x)
  rw [hval, map_mul]
  have : τ (algebraMap (𝓞 F) F y) ≠ 0 := (map_ne_zero τ).mpr hy0
  exact mul_self_pos.mpr this

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_totPos 𝔠`. Establish `hL : ((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).IsLB` using `LB.isLB_pull (X.isLB c) _`. Establish `hA` using `isAmpleLB_of_relAmple_of_isAffine X.A hL (X.pos c hc)`. Take `⟨_, -, s, hS, -, ha⟩` from `hA.exists_affine_finite_subset (S := {p, q}) (Set.toFinite _) (U := ⊤) (fun _ _ => trivial)`. Conclude with `⟨_, ha, hS (by simp), hS (by simp)⟩`.
-/
theorem exists_affine_mem_mem {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    (p q : X.A.left) : ∃ W : X.A.left.Opens, IsAffineOpen W ∧ p ∈ W ∧ q ∈ W := by
  obtain ⟨c, hc⟩ := exists_totPos 𝔠
  have hL : ((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).IsLB := LB.isLB_pull (X.isLB c) _
  have hA := isAmpleLB_of_relAmple_of_isAffine X.A hL (X.pos c hc)
  obtain ⟨_, -, s, hS, -, ha⟩ := hA.exists_affine_finite_subset (S := {p, q}) (Set.toFinite _) (U := ⊤)
    (fun _ _ => trivial)
  exact ⟨_, ha, hS (by simp), hS (by simp)⟩

/- English proof (translation)
Introduce `F _ _ 𝔠 X L n u w v hd hv`. Set `pt : PrimeSpectrum ℂ` to `default`. Take `⟨W, hW, hx, h0⟩` from `exists_affine_mem_mem X ((spMap TangentOrigin.fstC ≫ v.left) pt) ((u.ex 0).left pt)`. Establish `hx' : ⊤ ≤ (spMap TangentOrigin.fstC ≫ v.left) ⁻¹ᵁ W` using `(top_le_preimage_iff_mem _ _).2 hx`. Establish `h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W` using `(top_le_preimage_iff_mem _ _).2 h0`.

Establish `hv' : ⊤ ≤ v.left ⁻¹ᵁ W` using `(TangentOrigin.top_le_preimage_iff v.left W).2 hx'`. Establish `hsnd : ∀ f, (TangentOrigin.evalPt (R` using `DualNumber ℂ) v.left W hv' f).snd = (TangentOrigin.jet u w W h0' f).snd := fun f => hd W hv' f`. Establish `hfst : ∀ f, (TangentOrigin.evalPt (R` using `DualNumber ℂ) v.left W hv' f).fst = TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f := fun f => (TangentOrigin.evalPt_spMap_comp _ v.left W hv' hx' f).symm`. Establish `key : ∀ f, (TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f - TangentOrigin.evalPt (u.ex 0).left W h0' f) * (TangentOrigin.jet u w W h0' f).snd = 0`. Introduce `f`.

Establish `e` using `hsnd (f * f)`. Rewrite `e` using `[map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, hsnd f, hfst f, TangentOrigin.jet_fst]`. Take the linear combination `e / 2`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : ∃ h, TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' h ≠ TangentOrigin.evalPt (u.ex 0).left W h0' h := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hv ((TangentOrigin.ext_evalPt hW hx' h0' (RingHom.ext hc)).trans (TangentOrigin.ex_zero_left u))`. Establish `hdh : (TangentOrigin.jet u w W h0' h).snd = 0` using `(mul_eq_zero.1 (key h)).resolve_left (sub_ne_zero.2 hh)`. Establish `hδ : ∀ f, (TangentOrigin.jet u w W h0' f).snd = 0`. Introduce `f`.

Distinguish the cases in `hf : TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f = TangentOrigin.evalPt (u.ex 0).left W h0' f`. Establish `k2` using `key (f + h)`. Rewrite `k2` using `[map_add, map_add, hf, add_sub_add_left_eq_sub]`. Establish `e` using `(mul_eq_zero.1 k2).resolve_left (sub_ne_zero.2 hh)`. Rewrite `e` using `[map_add, TrivSqZeroExt.snd_add, hdh, add_zero]`. Then use the resulting hypothesis.

Conclude with `(mul_eq_zero.1 (key f)).resolve_left (sub_ne_zero.2 hf)`. Establish `ht` using `ArchMetricCompare.isTangent_zero X.A`. Establish `h₁` using `(TangentOrigin.tangent_mem_iff (u := u) ht W).2 h0'`. Use `ArchMetricCompare.eq_zero_of_isDiff u ((TangentOrigin.isDiff_iff ht hW h₁ h0' w).2 (RingHom.ext fun f => TrivSqZeroExt.ext (TangentOrigin.tangent_fst ht h₁ h0' f) ?_))` and prove the remaining obligations. Establish `e` using `ArchMetricCompare.isDiff_zero u W h₁ f`.

Rewrite `e` using `[map_zero]`. Conclude with `e.trans (hδ f).symm`.
-/
theorem eq_zero_of_isDiff_of_not_isTangent : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left) (n : ℕ)
    (u : HolUnif X.A L n) (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A), u.IsDiff w v → ¬ IsTangent v → w = 0 := by
  intro F _ _ 𝔠 X L n u w v hd hv
  let pt : PrimeSpectrum ℂ := default
  obtain ⟨W, hW, hx, h0⟩ := exists_affine_mem_mem X ((spMap TangentOrigin.fstC ≫ v.left) pt) ((u.ex 0).left pt)
  have hx' : ⊤ ≤ (spMap TangentOrigin.fstC ≫ v.left) ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 hx
  have h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 h0
  have hv' : ⊤ ≤ v.left ⁻¹ᵁ W := (TangentOrigin.top_le_preimage_iff v.left W).2 hx'
  have hsnd : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).snd =
      (TangentOrigin.jet u w W h0' f).snd := fun f => hd W hv' f
  have hfst : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).fst =
      TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f := fun f =>
    (TangentOrigin.evalPt_spMap_comp _ v.left W hv' hx' f).symm
  have key : ∀ f, (TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f -
      TangentOrigin.evalPt (u.ex 0).left W h0' f) * (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    have e := hsnd (f * f)
    rw [map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, hsnd f, hfst f,
      TangentOrigin.jet_fst] at e
    linear_combination e / 2
  obtain ⟨h, hh⟩ : ∃ h, TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' h ≠
      TangentOrigin.evalPt (u.ex 0).left W h0' h := by
    by_contra hc
    push_neg at hc
    exact hv ((TangentOrigin.ext_evalPt hW hx' h0' (RingHom.ext hc)).trans (TangentOrigin.ex_zero_left u))
  have hdh : (TangentOrigin.jet u w W h0' h).snd = 0 := (mul_eq_zero.1 (key h)).resolve_left (sub_ne_zero.2 hh)
  have hδ : ∀ f, (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    by_cases hf : TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f =
        TangentOrigin.evalPt (u.ex 0).left W h0' f
    · have k2 := key (f + h)
      rw [map_add, map_add, hf, add_sub_add_left_eq_sub] at k2
      have e := (mul_eq_zero.1 k2).resolve_left (sub_ne_zero.2 hh)
      rwa [map_add, TrivSqZeroExt.snd_add, hdh, add_zero] at e
    · exact (mul_eq_zero.1 (key f)).resolve_left (sub_ne_zero.2 hf)
  have ht := ArchMetricCompare.isTangent_zero X.A
  have h₁ := (TangentOrigin.tangent_mem_iff (u := u) ht W).2 h0'
  refine ArchMetricCompare.eq_zero_of_isDiff u ((TangentOrigin.isDiff_iff ht hW h₁ h0' w).2
    (RingHom.ext fun f => TrivSqZeroExt.ext (TangentOrigin.tangent_fst ht h₁ h0' f) ?_))
  have e := ArchMetricCompare.isDiff_zero u W h₁ f
  rw [map_zero] at e
  exact e.trans (hδ f).symm

end GlobalTheory.UnifOffOrigin
