import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open Filter Topology

noncomputable section

namespace GlobalTheory.PureGlue

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, -, rfl⟩` from `hΦ`. Use `⟨g z • f, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h : (fun i => (a i).2) = z` using `funext ha`.

Use `show f _ * g (fun i => (a i).2) = _`. Rewrite using `[h, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, fun a _ => by simp⟩`. Consider the case `add Φ Ψ _ _ h1 h2`.

Take `⟨f1, hf1⟩` from `h1`. Take `⟨f2, hf2⟩` from `h2`. Conclude with `⟨f1 + f2, fun a ha => by simp [hf1 a ha, hf2 a ha]⟩`. Consider the case `smul c Φ _ h`. Take `⟨f1, hf1⟩` from `h`.

Conclude with `⟨c • f1, fun a ha => by simp [hf1 a ha]⟩`.
-/
theorem exists_slice (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (z : κ → Af F) :
    ∃ f : SInf F κ, ∀ a : κ → AF F, (∀ i, (a i).2 = z i) → Φ a = f (fun i => evI F (a i)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, -, rfl⟩ := hΦ
    refine ⟨g z • f, fun a ha => ?_⟩
    have h : (fun i => (a i).2) = z := funext ha
    show f _ * g (fun i => (a i).2) = _
    rw [h, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    rfl
  | zero => exact ⟨0, fun a _ => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    exact ⟨f1 + f2, fun a ha => by simp [hf1 a ha, hf2 a ha]⟩
  | smul c Φ _ h =>
    obtain ⟨f1, hf1⟩ := h
    exact ⟨c • f1, fun a ha => by simp [hf1 a ha]⟩

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Conclude with `(IsLocallyConstant.const (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (b i))).mul hg.1`. Consider the case `zero => exact IsLocallyConstant.const 0`.

Consider the case `add Φ Ψ _ _ h1 h2 => exact h1.add h2`. Consider the case `smul c Φ _ h => exact h.comp (fun t => c • t)`.
-/
theorem isLocallyConstant_fin (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (b : κ → Ainf F) :
    IsLocallyConstant (fun z : κ → Af F => Φ (fun i => (b i, z i))) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact (IsLocallyConstant.const (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (b i))).mul hg.1
  | zero => exact IsLocallyConstant.const 0
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.comp (fun t => c • t)

def hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) : Af F :=
  g + ∑ v ∈ S, singleFin v (evalV F v y - evalV F v g)

/- English proof (translation)
Unfold `hyb`. Rewrite using `[map_add, map_sum]`. Use `split_ifs with hu`. Rewrite using `[Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h), evalV_singleFin_self]`. Normalize the expressions using the abelian group laws.

Rewrite using `[Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (by rintro rfl; exact hu hv) _), add_zero]`.
-/
theorem evalV_hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (hyb S y g) = if u ∈ S then evalV F u y else evalV F u g := by
  unfold hyb
  rw [map_add, map_sum]
  split_ifs with hu
  · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
      evalV_singleFin_self]
    abel
  · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (by rintro rfl; exact hu hv) _), add_zero]

/- English proof (translation)
Unfold `hyb`. Rewrite using `[Finset.sum_insert hv]`. Normalize the expressions using the abelian group laws.
-/
theorem hyb_insert {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (y g : Af F) :
    hyb (insert v S) y g = hyb S y g + singleFin v (evalV F v y - evalV F v g) := by
  unfold hyb
  rw [Finset.sum_insert hv]
  abel

/- English proof (translation)
Simplify using `[hyb]`.
-/
theorem hyb_empty (y g : Af F) : hyb ∅ y g = g := by simp [hyb]

/- English proof (translation)
The claim follows from `GlobalTheory.AdelicLimit.tendsto_finAdele _ y g (fun T v hv => by have h := evalV_hyb T y g v; rw [if_pos hv] at h; exact h) (fun T v hv => by have h := evalV_hyb T y g v; rw [if_neg hv] at h; exact h)`.
-/
theorem tendsto_hyb (y g : Af F) : Tendsto (fun S => hyb S y g) atTop (𝓝 y) :=
  GlobalTheory.AdelicLimit.tendsto_finAdele _ y g
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_pos hv] at h; exact h)
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_neg hv] at h; exact h)

end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue
variable {F : Type} [Field F] [NumberField F]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).2 = singleFin v a := rfl
/- English proof (translation)
Express the relevant statement in the definitionally equal form `p.1 - (GlobalTheory.LatVac.liftV v a).1 + (GlobalTheory.LatVac.liftV v b).1 = p.1`. Rewrite using `[liftV_fst, liftV_fst, sub_zero, add_zero]`.
-/
theorem fst_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).1 = p.1 := by
  change p.1 - (GlobalTheory.LatVac.liftV v a).1 + (GlobalTheory.LatVac.liftV v b).1 = p.1
  rw [liftV_fst, liftV_fst, sub_zero, add_zero]
/- English proof (translation)
Express the relevant statement in the definitionally equal form `p.2 - (GlobalTheory.LatVac.liftV v a).2 + (GlobalTheory.LatVac.liftV v b).2 = _`. Rewrite using `[liftV_snd, liftV_snd]`.
-/
theorem snd_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).2 = p.2 - singleFin v a + singleFin v b := by
  change p.2 - (GlobalTheory.LatVac.liftV v a).2 + (GlobalTheory.LatVac.liftV v b).2 = _
  rw [liftV_snd, liftV_snd]
end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue

open scoped Classical

/- English proof (translation)
Introduce `F _ _ κ _ vac hvac hcof Φ hΦ hsl`. Use `set T0 : Set (HeightOneSpectrum (𝓞 F)) := {v | ¬ vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1} with hT0`. Establish `hT0f : T0.Finite` using `hcof`. Establish `hex : ∀ v, ∃ ζ : κ → Fv F v, vac v ζ ≠ 0` using `fun v => by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hvac v (funext h)`. Set `ζ : ∀ v, κ → Fv F v` to `fun v => if v ∈ T0 then (hex v).choose else 0`. Establish `hζ1 : ∀ v, v ∉ T0 → vac v (ζ v) = 1`. Introduce `v hv`.

Establish `h : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `not_not.1 hv`. Simplify using `only [ζ, if_neg hv]`. Rewrite using `[h, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]`. Both sides reduce to the same expression. Establish `hζ : ∀ v, vac v (ζ v) ≠ 0`.

Introduce `v`. Distinguish the cases in `hv : v ∈ T0`. Simplify using `only [ζ, if_pos hv]`. Conclude with `(hex v).choose_spec`. Rewrite using `[hζ1 v hv]`.

Conclude with `one_ne_zero`. Set `ξ0 : κ → Af F` to `fun i => ∑ v ∈ hT0f.toFinset, singleFin v (ζ v i)`. Establish `hξ0 : ∀ v i, evalV F v (ξ0 i) = ζ v i`. Introduce `v i`. Simplify using `only [ξ0, map_sum]`.

Distinguish the cases in `hv : v ∈ T0`. Rewrite using `[Finset.sum_eq_single v (fun u _ hu => evalV_singleFin_ne (Ne.symm hu) _) (fun h => absurd (hT0f.mem_toFinset.2 hv) h), evalV_singleFin_self]`. Rewrite using `[Finset.sum_eq_zero (fun u hu => evalV_singleFin_ne (by rintro rfl; exact hv (hT0f.mem_toFinset.1 hu)) _)]`. Simplify using `[ζ, hv]`. Use `set c : ℂ := ∏ v ∈ hT0f.toFinset, vac v (ζ v) with hcdef`.

Establish `hc : c ≠ 0` using `Finset.prod_ne_zero_iff.2 fun v _ => hζ v`. Take `⟨f0, hf0⟩` from `exists_slice Φ hΦ ξ0`. Use `⟨c⁻¹ • f0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `hev : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : AF F), evFin F v a = evalV F v a.2` using `fun _ _ => rfl`.

Set `P : Finset (HeightOneSpectrum (𝓞 F)) → κ → AF F` to `fun S i => ((x i).1, hyb S (x i).2 (ξ0 i))`. Establish `key : ∀ S, Φ (P S) * ∏ v ∈ S, vac v (ζ v) = Φ (P ∅) * ∏ v ∈ S, vac v (fun i => evFin F v (x i))`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert v S hv ih`. Set `y : κ → AF F` to `fun k => P S k - GlobalTheory.LatVac.liftV v (ζ v k)`. Establish `hy : ∀ k, evFin F v (y k) = 0`. Introduce `k`. Simplify using `only [y, map_sub, GlobalTheory.LatVac.evFin_liftV]`.

Rewrite using `[hev]`. Express the relevant statement in the definitionally equal form `evalV F v (hyb S (x k).2 (ξ0 k)) - ζ v k = 0`. Rewrite using `[evalV_hyb, if_neg hv, hξ0, sub_self]`. Take `⟨a, ha⟩` from `hsl v y hy`. Establish `e1 : P S = y + fun k => GlobalTheory.LatVac.liftV v (ζ v k)`.

Use function extensionality and compare the values at `k`. Simplify using `[y]`. Establish `e2 : P (insert v S) = y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))`. Use function extensionality and compare the values at `k`. Establish `hk : (y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))) k = P S k - GlobalTheory.LatVac.liftV v (ζ v k) + GlobalTheory.LatVac.liftV v (evFin F v (x k))` using `rfl`.

Rewrite using `[hk]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[fst_sub_add]`. Rewrite using `[snd_sub_add] show hyb (insert v S) (x k).2 (ξ0 k) = hyb S (x k).2 (ξ0 k) - singleFin v (ζ v k) + singleFin v (evFin F v (x k))`. Rewrite using `[hyb_insert hv, hξ0, map_sub, hev]`.

Normalize the expressions using the abelian group laws. Establish `h1` using `ha (ζ v)`. Establish `h2` using `ha (fun i => evFin F v (x i))`. Rewrite `h1` using `[← e1]`. Rewrite `h2` using `[← e2]`.

Rewrite using `[Finset.prod_insert hv, Finset.prod_insert hv]`. Take the linear combination `(vac v (ζ v) * ∏ u ∈ S, vac u (ζ u)) * h2 - (vac v (fun i => evFin F v (x i)) * ∏ u ∈ S, vac u (ζ u)) * h1 + vac v (fun i => evFin F v (x i)) * ih`. Establish `hlc` using `isLocallyConstant_fin Φ hΦ (fun i => (x i).1)`. Establish `ht : Tendsto (fun S => fun i => hyb S (x i).2 (ξ0 i)) atTop (𝓝 (fun i => (x i).2))` using `tendsto_pi_nhds.2 fun i => tendsto_hyb (x i).2 (ξ0 i)`. Establish `hev1 : ∀ᶠ S in atTop, Φ (P S) = Φ x` using `ht ((hlc.isOpen_fiber (Φ x)).mem_nhds rfl)`.

Establish `hxi : ∀ᶠ v in Filter.cofinite, ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun i => (x i).2.2.mono fun v hv => hv`. Use `set S0 : Set (HeightOneSpectrum (𝓞 F)) := {v | ¬ (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧ ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F)} with hS0`. Establish `hS0f : S0.Finite` using `hcof.and hxi`. Establish `hev2 : ∀ᶠ S in atTop, hS0f.toFinset ∪ hT0f.toFinset ≤ S` using `Filter.eventually_ge_atTop _`. Take `⟨S, hS1, hS2⟩` from `(hev1.and hev2).exists`.

Establish `k` using `key S`. Rewrite `k` using `[hS1]`. Establish `hcS : ∏ v ∈ S, vac v (ζ v) = c`. Use `symm`. Use `Finset.prod_subset (fun v hv => hS2 (Finset.mem_union_right _ hv)) ?_` and prove the remaining obligations.

Introduce `v _ hv`. Conclude with `hζ1 v (fun h => hv (hT0f.mem_toFinset.2 h))`. Establish `hfp : ∏ᶠ v, vac v (fun i => evFin F v (x i)) = ∏ v ∈ S, vac v (fun i => evFin F v (x i))`. Apply `finprod_eq_prod_of_mulSupport_subset` to reduce the goal to its premises. Introduce `v hv`.

Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises. Use `show vac v (fun i => evFin F v (x i)) = 1`. Establish `hn : v ∉ S0` using `fun h => hvS (hS2 (Finset.mem_union_left _ (hS0f.mem_toFinset.2 h)))`. Establish `h'` using `not_not.1 hn`.

Rewrite using `[h'.1, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h'.2)]`. Both sides reduce to the same expression. Establish `hP0 : Φ (P ∅) = f0 (fun i => evI F (x i))` using `hf0 (P ∅) (fun i => by simp [P, hyb_empty])`. Rewrite `k` using `[hcS]`. Use `show Φ x = (c⁻¹ • f0) (fun i => evI F (x i)) * ∏ᶠ v, vac v fun i => evFin F v (x i)`.

Rewrite using `[SchwartzMap.smul_apply, smul_eq_mul, hfp, ← hP0, mul_assoc, ← k, mul_comm (Φ x), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`.
-/
theorem eq_pure_of_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  intro F _ _ κ _ vac hvac hcof Φ hΦ hsl
  set T0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1} with hT0
  have hT0f : T0.Finite := hcof
  have hex : ∀ v, ∃ ζ : κ → Fv F v, vac v ζ ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hvac v (funext h)
  let ζ : ∀ v, κ → Fv F v := fun v => if v ∈ T0 then (hex v).choose else 0
  have hζ1 : ∀ v, v ∉ T0 → vac v (ζ v) = 1 := by
    intro v hv
    have h : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := not_not.1 hv
    simp only [ζ, if_neg hv]
    rw [h, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun i => zero_mem _)]
    rfl
  have hζ : ∀ v, vac v (ζ v) ≠ 0 := by
    intro v
    by_cases hv : v ∈ T0
    · simp only [ζ, if_pos hv]
      exact (hex v).choose_spec
    · rw [hζ1 v hv]
      exact one_ne_zero
  let ξ0 : κ → Af F := fun i => ∑ v ∈ hT0f.toFinset, singleFin v (ζ v i)
  have hξ0 : ∀ v i, evalV F v (ξ0 i) = ζ v i := by
    intro v i
    simp only [ξ0, map_sum]
    by_cases hv : v ∈ T0
    · rw [Finset.sum_eq_single v (fun u _ hu => evalV_singleFin_ne (Ne.symm hu) _)
        (fun h => absurd (hT0f.mem_toFinset.2 hv) h), evalV_singleFin_self]
    · rw [Finset.sum_eq_zero (fun u hu => evalV_singleFin_ne
        (by rintro rfl; exact hv (hT0f.mem_toFinset.1 hu)) _)]
      simp [ζ, hv]
  set c : ℂ := ∏ v ∈ hT0f.toFinset, vac v (ζ v) with hcdef
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hζ v
  obtain ⟨f0, hf0⟩ := exists_slice Φ hΦ ξ0
  refine ⟨c⁻¹ • f0, ?_⟩
  funext x
  have hev : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : AF F), evFin F v a = evalV F v a.2 := fun _ _ => rfl
  let P : Finset (HeightOneSpectrum (𝓞 F)) → κ → AF F := fun S i => ((x i).1, hyb S (x i).2 (ξ0 i))
  have key : ∀ S, Φ (P S) * ∏ v ∈ S, vac v (ζ v) =
      Φ (P ∅) * ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
      let y : κ → AF F := fun k => P S k - GlobalTheory.LatVac.liftV v (ζ v k)
      have hy : ∀ k, evFin F v (y k) = 0 := by
        intro k
        simp only [y, map_sub, GlobalTheory.LatVac.evFin_liftV]
        rw [hev]
        change evalV F v (hyb S (x k).2 (ξ0 k)) - ζ v k = 0
        rw [evalV_hyb, if_neg hv, hξ0, sub_self]
      obtain ⟨a, ha⟩ := hsl v y hy
      have e1 : P S = y + fun k => GlobalTheory.LatVac.liftV v (ζ v k) := by
        funext k
        simp [y]
      have e2 : P (insert v S) = y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k)) := by
        funext k
        have hk : (y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))) k =
            P S k - GlobalTheory.LatVac.liftV v (ζ v k) + GlobalTheory.LatVac.liftV v (evFin F v (x k)) := rfl
        rw [hk]
        refine Prod.ext ?_ ?_
        · rw [fst_sub_add]
        · rw [snd_sub_add]
          show hyb (insert v S) (x k).2 (ξ0 k) =
            hyb S (x k).2 (ξ0 k) - singleFin v (ζ v k) + singleFin v (evFin F v (x k))
          rw [hyb_insert hv, hξ0, map_sub, hev]
          abel
      have h1 := ha (ζ v)
      have h2 := ha (fun i => evFin F v (x i))
      rw [← e1] at h1
      rw [← e2] at h2
      rw [Finset.prod_insert hv, Finset.prod_insert hv]
      linear_combination (vac v (ζ v) * ∏ u ∈ S, vac u (ζ u)) * h2 -
        (vac v (fun i => evFin F v (x i)) * ∏ u ∈ S, vac u (ζ u)) * h1 + vac v (fun i => evFin F v (x i)) * ih
  have hlc := isLocallyConstant_fin Φ hΦ (fun i => (x i).1)
  have ht : Tendsto (fun S => fun i => hyb S (x i).2 (ξ0 i)) atTop (𝓝 (fun i => (x i).2)) :=
    tendsto_pi_nhds.2 fun i => tendsto_hyb (x i).2 (ξ0 i)
  have hev1 : ∀ᶠ S in atTop, Φ (P S) = Φ x :=
    ht ((hlc.isOpen_fiber (Φ x)).mem_nhds rfl)
  have hxi : ∀ᶠ v in Filter.cofinite, ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (x i).2.2.mono fun v hv => hv
  set S0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F)} with hS0
  have hS0f : S0.Finite := hcof.and hxi
  have hev2 : ∀ᶠ S in atTop, hS0f.toFinset ∪ hT0f.toFinset ≤ S := Filter.eventually_ge_atTop _
  obtain ⟨S, hS1, hS2⟩ := (hev1.and hev2).exists
  have k := key S
  rw [hS1] at k
  have hcS : ∏ v ∈ S, vac v (ζ v) = c := by
    symm
    refine Finset.prod_subset (fun v hv => hS2 (Finset.mem_union_right _ hv)) ?_
    intro v _ hv
    exact hζ1 v (fun h => hv (hT0f.mem_toFinset.2 h))
  have hfp : ∏ᶠ v, vac v (fun i => evFin F v (x i)) = ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    apply hv
    show vac v (fun i => evFin F v (x i)) = 1
    have hn : v ∉ S0 := fun h => hvS (hS2 (Finset.mem_union_left _ (hS0f.mem_toFinset.2 h)))
    have h' := not_not.1 hn
    rw [h'.1, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h'.2)]
    rfl
  have hP0 : Φ (P ∅) = f0 (fun i => evI F (x i)) :=
    hf0 (P ∅) (fun i => by simp [P, hyb_empty])
  rw [hcS] at k
  show Φ x = (c⁻¹ • f0) (fun i => evI F (x i)) * ∏ᶠ v, vac v fun i => evFin F v (x i)
  rw [SchwartzMap.smul_apply, smul_eq_mul, hfp, ← hP0, mul_assoc, ← k, mul_comm (Φ x), ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.PureGlue
