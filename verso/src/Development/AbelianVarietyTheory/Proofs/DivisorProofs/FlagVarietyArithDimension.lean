import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTotalSpaceIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec

set_option autoImplicit false

namespace GlobalTheory.FlagTop

open TopologicalSpace Limits

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hle : ∀ i, f i ≤ n` using `fun i => h ▸ le_iSup f i`. Consider the cases of `n with`. Consider the case `zero`.

Establish `: ⨆ i, f i ≤ ⊥` using `iSup_le fun i => by`. Use `lt_of_le_of_ne (hle i) (hno i)` as an intermediate fact. Conclude with `(WithBot.lt_zero_iff_eq_bot _).1 (by simpa using this) |>.le`. Rewrite `this` using `[h]`. Simplify using `at this`.

Consider the case `succ d`. Establish `: ⨆ i, f i ≤ (d : WithBot ℕ∞)` using `iSup_le fun i => GlobalTheory.SmoothDimTotal.le_of_le_succ_of_ne (hle i) (hno i)`. Rewrite `this` using `[h]`. Establish `: d + 1 ≤ d` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_eq_of_iSup_eq_nat {ι : Type} (f : ι → WithBot ℕ∞) (n : ℕ) (h : ⨆ i, f i = n) : ∃ i, f i = n := by
  by_contra hno
  push_neg at hno
  have hle : ∀ i, f i ≤ n := fun i => h ▸ le_iSup f i
  cases n with
  | zero =>
    have : ⨆ i, f i ≤ ⊥ := iSup_le fun i => by
      have := lt_of_le_of_ne (hle i) (hno i)
      exact (WithBot.lt_zero_iff_eq_bot _).1 (by simpa using this) |>.le
    rw [h] at this
    simp at this
  | succ d =>
    have : ⨆ i, f i ≤ (d : WithBot ℕ∞) :=
      iSup_le fun i => GlobalTheory.SmoothDimTotal.le_of_le_succ_of_ne (hle i) (hno i)
    rw [h] at this
    have : d + 1 ≤ d := by exact_mod_cast this
    omega

/- English proof (translation)
Use `haveI : Smooth π := SmoothOfRelativeDimension.smooth n π`. Use `haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π`. Rewrite `hB`, the goal using `[GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]`. Rewrite using `[Nat.cast_add]`. Apply `le_antisymm` to reduce the goal to its premises.

Use `iSup_le fun y => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add B Y π y]`. Conclude with `add_le_add (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) (π y)) (GlobalTheory.SmoothDimTotal.fib_le B Y π n y)`. Take `⟨b, hb⟩` from `exists_eq_of_iSup_eq_nat _ d hB`. Take `⟨y₀, rfl⟩` from `hsurj b`.

Take `⟨y, hy, hfib⟩` from `GlobalTheory.SmoothDimTotal.fib_ge B Y π n y₀`. Rewrite `hb` using `[← hy]`. Use `le_iSup_of_le y ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add B Y π y, hb]`. Conclude with `add_le_add le_rfl hfib`.
-/
theorem topologicalKrullDim_eq_add (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n d : ℕ)
    [SmoothOfRelativeDimension n π] (hsurj : Function.Surjective π) (hB : topologicalKrullDim B = (d : ℕ)) :
    topologicalKrullDim Y = (d + n : ℕ) := by
  haveI : Smooth π := SmoothOfRelativeDimension.smooth n π
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk] at hB ⊢
  rw [Nat.cast_add]
  apply le_antisymm
  · refine iSup_le fun y => ?_
    rw [GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add B Y π y]
    exact add_le_add (hB ▸ le_iSup (fun b : B => ringKrullDim (B.presheaf.stalk b)) (π y))
      (GlobalTheory.SmoothDimTotal.fib_le B Y π n y)
  · obtain ⟨b, hb⟩ := exists_eq_of_iSup_eq_nat _ d hB
    obtain ⟨y₀, rfl⟩ := hsurj b
    obtain ⟨y, hy, hfib⟩ := GlobalTheory.SmoothDimTotal.fib_ge B Y π n y₀
    rw [← hy] at hb
    refine le_iSup_of_le y ?_
    rw [GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add B Y π y, hb]
    exact add_le_add le_rfl hfib

/- English proof (translation)
Use `(genericPoint_spec A).image f.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ]`. Conclude with `this.def`.
-/
theorem closure_image_genericPoint {A B : Scheme.{0}} [IrreducibleSpace A] (f : A ⟶ B) :
    closure {f (genericPoint A)} = closure (Set.range f) := by
  have := (genericPoint_spec A).image f.continuous
  rw [Set.image_univ] at this
  exact this.def

/- English proof (translation)
Simplify using `[Nat.choose_two_right]`.
-/
theorem sum_unit (r : ℕ) : (∑ _a : Unit, r * (r - 1) / 2) = r.choose 2 := by
  simp [Nat.choose_two_right]

/- English proof (translation)
Use `GlobalTheory.T.flag_bundle_smooth_relative_dimension X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ` as an intermediate fact. Rewrite `this` using `[sum_unit]`. Then use the resulting hypothesis.
-/
theorem smoothRel {X : Scheme.{0}} {E : X.Modules} {r : ℕ} (hE : VB.IsVB E r) (F : FlagSp E r) :
    SmoothOfRelativeDimension (r.choose 2) F.π := by
  have := GlobalTheory.T.flag_bundle_smooth_relative_dimension X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ
  rwa [sum_unit] at this

/- English proof (translation)
Set `i` to `redι (clo z)`. Establish `hi : Set.range i = closure {z}` using `range_redι (clo z)`. Use `haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme := LocallyOfFiniteType.isLocallyNoetherian i`. Set `F' : FlagSp ((Scheme.Modules.pullback i).obj E) r` to `⟨pullback F.π i, pullback.snd F.π i, GlobalTheory.FlagBaseChange.pullFlag F.π i F.fl, GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag X F.Y _ F.π i Unit _ _ _ F.univ⟩`. Establish `hE'` using `hE.pullback i`.

Use `haveI : IrreducibleSpace (pullback F.π i : Scheme.{0}) := GlobalTheory.T.flag_bundle_total_space_irreducible _ F'.Y F'.π Unit _ _ _ (fun _ => hE') F'.univ`. Use `haveI : SmoothOfRelativeDimension (r.choose 2) (pullback.snd F.π i) := smoothRel hE' F'`. Establish `hs : Function.Surjective (pullback.snd F.π i)` using `GlobalTheory.FlagSurj.isFlagBundle_surjective _ F'.Y F'.π Unit _ _ _ (fun _ => hE') F'.univ`. Set `j` to `pullback.fst F.π i`. Establish `hj : Set.range j = F.π ⁻¹' closure {z}` using `by rw [← hi]; exact Scheme.Pullback.range_fst F.π i`.

Establish `hcl : closure {j (genericPoint (pullback F.π i : Scheme.{0}))} = F.π ⁻¹' closure {z}`. Rewrite using `[closure_image_genericPoint, hj]`. Conclude with `(isClosed_closure.preimage F.π.continuous).closure_eq`. Establish `hπ : F.π (j (genericPoint (pullback F.π i : Scheme.{0}))) = z`. Establish `h1` using `closure_image_genericPoint (j ≫ F.π)`.

Establish `h2 : Set.range (j ≫ F.π) = closure {z}`. Rewrite using `[show j ≫ F.π = pullback.snd F.π i ≫ i from pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, hs.range_comp, hi]`. Rewrite `h1` using `[h2, closure_closure, Scheme.Hom.comp_apply]`. Conclude with `(inseparable_iff_closure_eq.2 h1).eq`. Use `⟨j (genericPoint _), ⟨hπ, fun y' hy' => ?_⟩, hcl, fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[specializes_iff_mem_closure, hcl, Set.mem_preimage, hy']`. Conclude with `subset_closure rfl`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding (hj.trans hcl.symm)]`. Use `topologicalKrullDim_eq_add _ _ (pullback.snd F.π i) _ n hs ?_` and prove the remaining obligations. Rewrite using `[← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hi, hn]`.
-/
theorem exists_isTop {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules} {r : ℕ} (hE : VB.IsVB E r) (F : FlagSp E r)
    (z : X) : ∃ y, F.IsTop z y ∧ closure {y} = F.π ⁻¹' closure {z} ∧ ∀ n : ℕ,
      topologicalKrullDim (closure ({z} : Set X)) = (n : ℕ) →
        topologicalKrullDim (closure ({y} : Set F.Y)) = (n + r.choose 2 : ℕ) := by
  let i := redι (clo z)
  have hi : Set.range i = closure {z} := range_redι (clo z)
  haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i
  let F' : FlagSp ((Scheme.Modules.pullback i).obj E) r :=
    ⟨pullback F.π i, pullback.snd F.π i, GlobalTheory.FlagBaseChange.pullFlag F.π i F.fl,
      GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag X F.Y _ F.π i Unit _ _ _ F.univ⟩
  have hE' := hE.pullback i
  haveI : IrreducibleSpace (pullback F.π i : Scheme.{0}) := GlobalTheory.T.flag_bundle_total_space_irreducible _ F'.Y F'.π Unit _ _ _ (fun _ => hE') F'.univ
  haveI : SmoothOfRelativeDimension (r.choose 2) (pullback.snd F.π i) := smoothRel hE' F'
  have hs : Function.Surjective (pullback.snd F.π i) :=
    GlobalTheory.FlagSurj.isFlagBundle_surjective _ F'.Y F'.π Unit _ _ _ (fun _ => hE') F'.univ
  let j := pullback.fst F.π i
  have hj : Set.range j = F.π ⁻¹' closure {z} := by rw [← hi]; exact Scheme.Pullback.range_fst F.π i
  have hcl : closure {j (genericPoint (pullback F.π i : Scheme.{0}))} = F.π ⁻¹' closure {z} := by
    rw [closure_image_genericPoint, hj]
    exact (isClosed_closure.preimage F.π.continuous).closure_eq
  have hπ : F.π (j (genericPoint (pullback F.π i : Scheme.{0}))) = z := by
    have h1 := closure_image_genericPoint (j ≫ F.π)
    have h2 : Set.range (j ≫ F.π) = closure {z} := by
      rw [show j ≫ F.π = pullback.snd F.π i ≫ i from pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp,
        hs.range_comp, hi]
    rw [h2, closure_closure, Scheme.Hom.comp_apply] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  refine ⟨j (genericPoint _), ⟨hπ, fun y' hy' => ?_⟩, hcl, fun n hn => ?_⟩
  · rw [specializes_iff_mem_closure, hcl, Set.mem_preimage, hy']
    exact subset_closure rfl
  · rw [topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding (hj.trans hcl.symm)]
    refine topologicalKrullDim_eq_add _ _ (pullback.snd F.π i) _ n hs ?_
    rw [← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hi, hn]

/- English proof (translation)
Introduce `k _ X _ _ p d hp E r hE`. Use `⟨?_, fun F => ?_⟩` and prove the remaining obligations. Take `⟨Y, π, fl, h⟩` from `GlobalTheory.T.exists_flag_bundle X Unit (fun _ => E) (fun _ => r) (fun _ => hE)`. Conclude with `⟨⟨Y, π, fl (), h⟩⟩`. Use `haveI := smoothRel hE F`.

Use `haveI : Smooth F.π := SmoothOfRelativeDimension.smooth (r.choose 2) F.π`. Use `⟨?_, this, exists_isTop hE F⟩` and prove the remaining obligations. Use `haveI := hp.isNoetherianRing`. Use `haveI := GlobalTheory.T.flag_bundle_total_space_irreducible X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ`. Use `haveI : IsReduced F.Y := GlobalTheory.isReduced_of_smooth_of_isReduced F.π`.

Use `⟨hp.isDomain, hp.finite, isIntegral_of_irreducibleSpace_of_isReduced F.Y, GlobalTheory.T.flag_bundle_projective_over_base k X F.Y p F.π Unit _ _ _ hp.isProjOver (fun _ => hE) F.univ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Use `hp.flat` as an intermediate fact. Use `infer_instance`. Conclude with `GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective X F.Y F.π _ d (GlobalTheory.FlagSurj.isFlagBundle_surjective X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ) hp.dim_eq`.
-/
theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ), VB.IsVB E r → Nonempty (FlagSp E r) ∧ ∀ F : FlagSp E r, IsArithVar (F.π ≫ p) (d + r.choose 2) ∧ Smooth F.π ∧ ∀ z : X, ∃ y, F.IsTop z y ∧ closure {y} = F.π ⁻¹' closure {z} ∧ ∀ n : ℕ, topologicalKrullDim (closure ({z} : Set X)) = (n : ℕ) → topologicalKrullDim (closure ({y} : Set F.Y)) = (n + r.choose 2 : ℕ) := by
  intro k _ X _ _ p d hp E r hE
  refine ⟨?_, fun F => ?_⟩
  · obtain ⟨Y, π, fl, h⟩ := GlobalTheory.T.exists_flag_bundle X Unit (fun _ => E) (fun _ => r) (fun _ => hE)
    exact ⟨⟨Y, π, fl (), h⟩⟩
  haveI := smoothRel hE F
  haveI : Smooth F.π := SmoothOfRelativeDimension.smooth (r.choose 2) F.π
  refine ⟨?_, this, exists_isTop hE F⟩
  haveI := hp.isNoetherianRing
  haveI := GlobalTheory.T.flag_bundle_total_space_irreducible X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ
  haveI : IsReduced F.Y := GlobalTheory.isReduced_of_smooth_of_isReduced F.π
  refine ⟨hp.isDomain, hp.finite, isIntegral_of_irreducibleSpace_of_isReduced F.Y,
    GlobalTheory.T.flag_bundle_projective_over_base k X F.Y p F.π Unit _ _ _ hp.isProjOver (fun _ => hE) F.univ, ?_, ?_⟩
  · rw [Category.assoc]
    have := hp.flat
    infer_instance
  · exact GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective X F.Y F.π _ d
      (GlobalTheory.FlagSurj.isFlagBundle_surjective X F.Y F.π Unit _ _ _ (fun _ => hE) F.univ) hp.dim_eq

end GlobalTheory.FlagTop
