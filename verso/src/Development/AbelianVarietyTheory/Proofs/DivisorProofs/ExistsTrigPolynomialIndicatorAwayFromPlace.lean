import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OffVTrig

variable {F : Type} [Field F] [NumberField F]

abbrev ev1 (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Af F := GlobalTheory.AdelicU.singleFin v 1

abbrev gv (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Af F := 1 - ev1 v

/- English proof (translation)
Rewrite using `[ev1, ← GlobalTheory.AdelicU.singleFin_mul, mul_one]`.
-/
theorem finiteAdeleIndicatorAtPlace_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : ev1 v * ev1 v = ev1 v := by
  rw [ev1, ← GlobalTheory.AdelicU.singleFin_mul, mul_one]

/- English proof (translation)
Rewrite using `[gv, mul_sub, mul_one, finiteAdeleIndicatorAtPlace_mul_self, sub_self]`.
-/
theorem finiteAdeleIndicatorAtPlace_mul_awayFromPlace (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : ev1 v * gv v = 0 := by
  rw [gv, mul_sub, mul_one, finiteAdeleIndicatorAtPlace_mul_self, sub_self]

variable {κ : Type} [Fintype κ]

def offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (u : κ → Af F) : κ → Af F := fun i => gv v * u i

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_const.mul (continuous_apply i)`.
-/
theorem continuous_offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (offV (κ := κ) v) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `Prod.ext (show (0 : InfiniteAdeleRing F) = 0 - 0 by rw [sub_zero]) rfl`.
-/
theorem vecFin_sub (u u' : κ → Af F) :
    GlobalTheory.FinTrig.vecFin (u - u') = GlobalTheory.FinTrig.vecFin u - GlobalTheory.FinTrig.vecFin u' := by
  funext i
  exact Prod.ext (show (0 : InfiniteAdeleRing F) = 0 - 0 by rw [sub_zero]) rfl

/- English proof (translation)
Establish `h1 : (fun z : κ → Af F => y + z) ⁻¹' V ∈ nhds (0 : κ → Af F)` using `(hV.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hy)`. Rewrite `h1` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, _, t, ht, hsub⟩` from `h1`. Establish `hW : (⋂ i, t i) ∈ nhds (0 : Af F)` using `Filter.iInter_mem.mpr fun i => ht i`. Take `⟨d, hd0, hd⟩` from `GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW`.

Use `⟨d, hd0, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hd' : (d : F) ≠ 0` using `by exact_mod_cast hd0`. Establish `hmem : ∀ i, u i - y i ∈ ⋂ j, t j`. Introduce `i`. Establish `e : u i - y i = algebraMap F (Af F) (algebraMap (𝓞 F) F d) * (algebraMap F (Af F) ((d : F)⁻¹) * (u i - y i))`.

Rewrite using `[← mul_assoc, ← map_mul]`. Express the relevant statement in the definitionally equal form `_ = algebraMap F (Af F) ((d : F) * (d : F)⁻¹) * _`. Rewrite using `[mul_inv_cancel₀ hd', map_one, one_mul]`. Rewrite using `[e]`. Conclude with `hd _ (hu i)`.

Establish `: (fun z : κ → Af F => y + z) (u - y) ∈ V` using `hsub (fun i _ => Set.mem_iInter.mp (hmem i) i)`. Simplify using `using this`.
-/
theorem exists_lev_subset (y : κ → Af F) (V : Set (κ → Af F)) (hV : IsOpen V) (hy : y ∈ V) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ {u | GlobalTheory.FinTrig.Lev d (u - y)} ⊆ V := by
  have h1 : (fun z : κ → Af F => y + z) ⁻¹' V ∈ nhds (0 : κ → Af F) :=
    (hV.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hy)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, _, t, ht, hsub⟩ := h1
  have hW : (⋂ i, t i) ∈ nhds (0 : Af F) := Filter.iInter_mem.mpr fun i => ht i
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => ?_⟩
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hmem : ∀ i, u i - y i ∈ ⋂ j, t j := by
    intro i
    have e : u i - y i = algebraMap F (Af F) (algebraMap (𝓞 F) F d) *
        (algebraMap F (Af F) ((d : F)⁻¹) * (u i - y i)) := by
      rw [← mul_assoc, ← map_mul]
      change _ = algebraMap F (Af F) ((d : F) * (d : F)⁻¹) * _
      rw [mul_inv_cancel₀ hd', map_one, one_mul]
    rw [e]; exact hd _ (hu i)
  have : (fun z : κ → Af F => y + z) (u - y) ∈ V := hsub (fun i _ => Set.mem_iInter.mp (hmem i) i)
  simpa using this

def Freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Set (κ → AF F) := {b | ∀ i, (b i).1 = 0 ∧ ev1 v * (b i).2 = 0}

/- English proof (translation)
Introduce `i` and use `⟨rfl, show ev1 v * (0 : Af F) = 0 from mul_zero _⟩`.
-/
theorem zero_mem_freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (0 : κ → AF F) ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (0 : Af F) = 0 from mul_zero _⟩

/- English proof (translation)
Introduce `i` and use `⟨show (b i).1 + (b' i).1 = 0 by rw [(h i).1, (h' i).1, add_zero], show ev1 v * ((b i).2 + (b' i).2) = 0 by rw [mul_add, (h i).2, (h' i).2, add_zero]⟩`.
-/
theorem add_mem_freq {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {b b' : κ → AF F} (h : b ∈ Freq v) (h' : b' ∈ Freq v) :
    b + b' ∈ Freq v := fun i =>
  ⟨show (b i).1 + (b' i).1 = 0 by rw [(h i).1, (h' i).1, add_zero],
    show ev1 v * ((b i).2 + (b' i).2) = 0 by rw [mul_add, (h i).2, (h' i).2, add_zero]⟩

def TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Submodule ℂ ((κ → AF F) → ℂ) :=
  Submodule.span ℂ (GlobalTheory.FinTrig.chi ψ '' (Freq v))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨b, hb, rfl⟩`.
-/
theorem chi_mem_TPv (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {b : κ → AF F} (hb : b ∈ Freq v) :
    GlobalTheory.FinTrig.chi ψ b ∈ TPv ψ v :=
  Submodule.subset_span ⟨b, hb, rfl⟩

/- English proof (translation)
Rewrite using `[← GlobalTheory.FinTrig.chi_zero ψ]`. Conclude with `chi_mem_TPv ψ (zero_mem_freq v)`.
-/
theorem one_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (1 : (κ → AF F) → ℂ) ∈ TPv ψ v := by
  rw [← GlobalTheory.FinTrig.chi_zero ψ]; exact chi_mem_TPv ψ (zero_mem_freq v)

/- English proof (translation)
Establish `hle : TPv ψ v * TPv ψ v ≤ TPv (κ` using `κ) ψ v := by`. Rewrite using `[TPv, Submodule.span_mul_span]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩`. Conclude with `⟨q + q', add_mem_freq hq hq', (GlobalTheory.FinTrig.chi_mul ψ q q').symm⟩`.

Conclude with `hle (Submodule.mul_mem_mul hf hg)`.
-/
theorem mul_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {f g : (κ → AF F) → ℂ}
    (hf : f ∈ TPv ψ v) (hg : g ∈ TPv ψ v) : f * g ∈ TPv ψ v := by
  have hle : TPv ψ v * TPv ψ v ≤ TPv (κ := κ) ψ v := by
    rw [TPv, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', add_mem_freq hq hq', (GlobalTheory.FinTrig.chi_mul ψ q q').symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

/- English proof (translation)
The claim follows from `Finset.prod_induction f (· ∈ TPv ψ v) (fun _ _ => mul_mem_TPv ψ v) (one_mem_TPv ψ v) h`.
-/
theorem prod_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {ι : Type} (t : Finset ι)
    (f : ι → (κ → AF F) → ℂ) (h : ∀ a ∈ t, f a ∈ TPv ψ v) : (∏ a ∈ t, f a) ∈ TPv ψ v :=
  Finset.prod_induction f (· ∈ TPv ψ v) (fun _ _ => mul_mem_TPv ψ v) (one_mem_TPv ψ v) h

/- English proof (translation)
Rewrite `h` using `[TPv, Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨l, hl, rfl⟩` from `h`. Use `⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem exists_of_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {P : (κ → AF F) → ℂ}
    (h : P ∈ TPv ψ v) :
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, q ∈ Freq v) ∧
      ∀ x, P x = ∑ q ∈ s, c q * ψ (x ⬝ᵥ q) := by
  rw [TPv, Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rfl

def killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : κ → AF F) : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), gv v * (q i).2)

/- English proof (translation)
Introduce `i` and use `⟨rfl, show ev1 v * (gv v * (q i).2) = 0 by rw [← mul_assoc, finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]⟩`.
-/
theorem killV_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : κ → AF F) : killV v q ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (gv v * (q i).2) = 0 by rw [← mul_assoc, finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]⟩

/- English proof (translation)
Simplify using `only [dotProduct]`. Use `Finset.sum_congr rfl fun i _ => Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (x i).1 * 0 = 0 * (q i).1`. Rewrite using `[mul_zero, zero_mul]`. Use `show (x i).2 * (gv v * (q i).2) = (gv v * (x i).2) * (q i).2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dot_killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q x : κ → AF F) :
    x ⬝ᵥ killV v q = GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2)) ⬝ᵥ q := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => Prod.ext ?_ ?_
  · show (x i).1 * 0 = 0 * (q i).1
    rw [mul_zero, zero_mul]
  · show (x i).2 * (gv v * (q i).2) = (gv v * (x i).2) * (q i).2
    ring

end GlobalTheory.OffVTrig

namespace GlobalTheory.OffVTrig

/- English proof (translation)
Introduce `F _ _ κ _ v ψ hψ _ K hK y V hV hyV`. Take `⟨d, -, hdV⟩` from `exists_lev_subset (fun i => (y i).2) V hV hyV`. Establish `hPc` using `continuous_offV (κ := κ) v`. Establish `hAo : IsOpen {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}` using `(GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).preimage hPc`. Use `set C := offV v '' K ∩ {z | GlobalTheory.FinTrig.Lev d (z - offV v (fun i => (y i).2))}ᶜ with hCdef`.

Establish `hC : IsCompact C` using `(hK.image hPc).inter_right (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).isClosed_compl`. Take `⟨t, htC, hcov⟩` from `hC.elim_nhds_subcover (fun a => {z | GlobalTheory.FinTrig.Lev d (z - a)}) (fun a _ => (GlobalTheory.FinTrig.isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact GlobalTheory.FinTrig.lev_zero d))`. Establish `hsep : ∀ a ∈ C, ∃ q ∈ (GlobalTheory.FinTrig.Q0 : Set (κ → AF F)), ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q) ≠ 1 ∧ ∀ u, GlobalTheory.FinTrig.Lev d u → ψ (GlobalTheory.FinTrig.vecFin u ⬝ᵥ q) = 1` using `fun a ha => GlobalTheory.FinTrig.exists_sep ψ hψ d (a - offV v (fun i => (y i).2)) ha.2`. Use `choose! q _ hq1 hq2 using hsep`. Use `set c : (κ → Af F) → ℂ := fun a => ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q a) with hc`.

Use `set φ : (κ → Af F) → (κ → AF F) → ℂ := fun a => (1 - c a)⁻¹ • (ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) • GlobalTheory.FinTrig.chi ψ (killV v (q a)) - c a • 1) with hφ`. Establish `hφx : ∀ a x, φ a x = (1 - c a)⁻¹ * (ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) - c a)`. Introduce `a x`. Establish `e1 : ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) * ψ (x ⬝ᵥ killV v (q a)) = ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a)`. Rewrite using `[← AddChar.map_add_eq_mul, dot_killV, vecFin_sub, sub_dotProduct, neg_add_eq_sub]`.

Simplify using `only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]`. Rewrite using `[e1]`. Establish `hφmem : ∀ a ∈ t, φ a ∈ TPv ψ v` using `fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem_TPv ψ (killV_mem v (q a)))) (Submodule.smul_mem _ _ (one_mem_TPv ψ v)))`. Take `⟨s, cc, hs, hPs⟩` from `exists_of_mem_TPv ψ v (prod_mem_TPv ψ v t φ hφmem)`. Use `⟨{u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}, s, cc, hAo, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show GlobalTheory.FinTrig.Lev d (offV v (fun i => (y i).2) - offV v (fun i => (y i).2))`. Rewrite using `[sub_self]`. Conclude with `GlobalTheory.FinTrig.lev_zero d`. Introduce `b hb`. Use function extensionality and compare the values at `i`.

Conclude with `Prod.ext (show (0 : InfiniteAdeleRing F) * (b i).1 = 0 from zero_mul _) (show ev1 v * (b i).2 = 0 from (hs b hb i).2)`. Introduce `x z hz`. Establish `hz2 : ∀ i, gv v * (z i).2 = 0`. Introduce `i`. Establish `h1 : ((GlobalTheory.LatVac.liftV v 1 • z) i).2 = ev1 v * (z i).2` using `rfl`.

Rewrite `h1` using `[hz]`. Rewrite using `[h1, ← mul_assoc, mul_comm (gv v), finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]`. Establish `e : offV v (fun i => ((x + z) i).2) = offV v (fun i => (x i).2)`. Use function extensionality and compare the values at `i`. Use `show gv v * ((x i).2 + (z i).2) = gv v * (x i).2`.

Rewrite using `[mul_add, hz2 i, add_zero]`. Use `show GlobalTheory.FinTrig.Lev d (offV v _ - _) ↔ GlobalTheory.FinTrig.Lev d (offV v _ - _)`. Rewrite using `[e]`. Introduce `x hx`. Apply `hdV` to reduce the goal to its premises.

Use `show GlobalTheory.FinTrig.Lev d (_ - _)`. Establish `e : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) - (fun i => (y i).2) = offV v (fun i => (x i).2) - offV v (fun i => (y i).2)`. Use function extensionality and compare the values at `i`. Use `show (x i).2 + (ev1 v * (y i).2 - ev1 v * (x i).2) - (y i).2 = gv v * (x i).2 - gv v * (y i).2`. Simplify using `only [gv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hx`. Introduce `x hxK`. Rewrite using `[← hPs x, Finset.prod_apply]`.

Distinguish the cases in `hxA : GlobalTheory.FinTrig.Lev d (offV v (fun i => (x i).2) - offV v (fun i => (y i).2))`. Rewrite using `[Set.indicator_of_mem (show (fun i => (x i).2) ∈ {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]`. Use `Finset.prod_eq_one fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hφx a x, hq2 a (htC a ha) _ hxA]`. Establish `hne : 1 - c a ≠ 0` using `sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))`.

Conclude with `inv_mul_cancel₀ hne`. Rewrite using `[Set.indicator_of_notMem (show (fun i => (x i).2) ∉ {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]`. Establish `hxC : offV v (fun i => (x i).2) ∈ C` using `⟨⟨_, hxK, rfl⟩, hxA⟩`. Take `⟨a, hat, hxa⟩` from `Set.mem_iUnion₂.mp (hcov hxC)`. Use `Finset.prod_eq_zero hat ?_` and prove the remaining obligations.

Rewrite using `[hφx a x]`. Establish `e : offV v (fun i => (x i).2) - offV v (fun i => (y i).2) = (offV v (fun i => (x i).2) - a) + (a - offV v (fun i => (y i).2))` using `(sub_add_sub_cancel _ _ _).symm`. Rewrite using `[e, GlobalTheory.FinTrig.vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self, mul_zero]`.
-/
theorem exists_offV_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  intro F _ _ κ _ v ψ hψ _ K hK y V hV hyV
  classical
  obtain ⟨d, -, hdV⟩ := exists_lev_subset (fun i => (y i).2) V hV hyV
  have hPc := continuous_offV (κ := κ) v
  have hAo : IsOpen {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} :=
    (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).preimage hPc
  set C := offV v '' K ∩ {z | GlobalTheory.FinTrig.Lev d (z - offV v (fun i => (y i).2))}ᶜ with hCdef
  have hC : IsCompact C :=
    (hK.image hPc).inter_right (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun a => {z | GlobalTheory.FinTrig.Lev d (z - a)})
    (fun a _ => (GlobalTheory.FinTrig.isOpen_lev d a).mem_nhds
      (by simp only [Set.mem_setOf_eq, sub_self]; exact GlobalTheory.FinTrig.lev_zero d))
  have hsep : ∀ a ∈ C, ∃ q ∈ (GlobalTheory.FinTrig.Q0 : Set (κ → AF F)),
      ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, GlobalTheory.FinTrig.Lev d u → ψ (GlobalTheory.FinTrig.vecFin u ⬝ᵥ q) = 1 :=
    fun a ha => GlobalTheory.FinTrig.exists_sep ψ hψ d (a - offV v (fun i => (y i).2)) ha.2
  choose! q _ hq1 hq2 using hsep
  set c : (κ → Af F) → ℂ := fun a => ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q a) with hc
  set φ : (κ → Af F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) •
      GlobalTheory.FinTrig.chi ψ (killV v (q a)) - c a • 1) with hφ
  have hφx : ∀ a x, φ a x = (1 - c a)⁻¹ *
      (ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) - c a) := by
    intro a x
    have e1 : ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) * ψ (x ⬝ᵥ killV v (q a)) =
        ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, dot_killV, vecFin_sub, sub_dotProduct, neg_add_eq_sub]
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TPv ψ v := fun a _ =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem_TPv ψ (killV_mem v (q a))))
      (Submodule.smul_mem _ _ (one_mem_TPv ψ v)))
  obtain ⟨s, cc, hs, hPs⟩ := exists_of_mem_TPv ψ v (prod_mem_TPv ψ v t φ hφmem)
  refine ⟨{u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}, s, cc, hAo, ?_, ?_, ?_, ?_, ?_⟩
  · show GlobalTheory.FinTrig.Lev d (offV v (fun i => (y i).2) - offV v (fun i => (y i).2))
    rw [sub_self]; exact GlobalTheory.FinTrig.lev_zero d
  · intro b hb
    funext i
    exact Prod.ext (show (0 : InfiniteAdeleRing F) * (b i).1 = 0 from zero_mul _)
      (show ev1 v * (b i).2 = 0 from (hs b hb i).2)
  · intro x z hz
    have hz2 : ∀ i, gv v * (z i).2 = 0 := by
      intro i
      have h1 : ((GlobalTheory.LatVac.liftV v 1 • z) i).2 = ev1 v * (z i).2 := rfl
      rw [hz] at h1
      rw [h1, ← mul_assoc, mul_comm (gv v), finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]
    have e : offV v (fun i => ((x + z) i).2) = offV v (fun i => (x i).2) := by
      funext i
      show gv v * ((x i).2 + (z i).2) = gv v * (x i).2
      rw [mul_add, hz2 i, add_zero]
    show GlobalTheory.FinTrig.Lev d (offV v _ - _) ↔ GlobalTheory.FinTrig.Lev d (offV v _ - _)
    rw [e]
  · intro x hx
    apply hdV
    show GlobalTheory.FinTrig.Lev d (_ - _)
    have e : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) - (fun i => (y i).2) =
        offV v (fun i => (x i).2) - offV v (fun i => (y i).2) := by
      funext i
      show (x i).2 + (ev1 v * (y i).2 - ev1 v * (x i).2) - (y i).2 = gv v * (x i).2 - gv v * (y i).2
      simp only [gv]; ring
    rw [e]; exact hx
  · intro x hxK
    rw [← hPs x, Finset.prod_apply]
    by_cases hxA : GlobalTheory.FinTrig.Lev d (offV v (fun i => (x i).2) - offV v (fun i => (y i).2))
    · rw [Set.indicator_of_mem (show (fun i => (x i).2) ∈
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      refine Finset.prod_eq_one fun a ha => ?_
      rw [hφx a x, hq2 a (htC a ha) _ hxA]
      have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
      exact inv_mul_cancel₀ hne
    · rw [Set.indicator_of_notMem (show (fun i => (x i).2) ∉
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      have hxC : offV v (fun i => (x i).2) ∈ C := ⟨⟨_, hxK, rfl⟩, hxA⟩
      obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC)
      refine Finset.prod_eq_zero hat ?_
      rw [hφx a x]
      have e : offV v (fun i => (x i).2) - offV v (fun i => (y i).2) =
          (offV v (fun i => (x i).2) - a) + (a - offV v (fun i => (y i).2)) := (sub_add_sub_cancel _ _ _).symm
      rw [e, GlobalTheory.FinTrig.vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul,
        sub_self, mul_zero]

end GlobalTheory.OffVTrig
