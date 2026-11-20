import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.XTermLattice

open scoped Classical

/- English proof (translation)
Set `p : J × Finset ι → Seminorm ℂ (SchwartzMap V ℂ)` to `fun a => ∑ i ∈ a.2, (normSeminorm ℂ ℂ).comp (T a.1 i).toLinearMap`. Establish `hp : ∀ a f, p a f = ∑ i ∈ a.2, ‖T a.1 i f‖`. Introduce and unpack `⟨j, t⟩ f`. Simplify using `only [p]`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Seminorm.add_apply, ih]`. Both sides reduce to the same expression. Establish `hbdd : ∀ f, BddAbove (Set.range fun a => p a f)`. Introduce `f`.

Use `⟨∑ j, ∑' i, ‖T j i f‖, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [hp]`. Conclude with `((hT a.1 f).sum_le_tsum a.2 fun i _ => norm_nonneg _).trans (Finset.single_le_sum (f := fun j => ∑' i, ‖T j i f‖) (fun j _ => tsum_nonneg fun _ => norm_nonneg _) (Finset.mem_univ a.1))`. Establish `hbdd' : BddAbove (Set.range p)` using `(Seminorm.bddAbove_range_iff).2 hbdd`.

Establish `hpc : ∀ a, Continuous (p a)` using `fun a => by`. Rewrite using `[show ⇑(p a) = fun f => ∑ i ∈ a.2, ‖T a.1 i f‖ from funext (hp a)]`. Conclude with `continuous_finset_sum _ fun i _ => (T a.1 i).continuous.norm`. Establish `hcont : Continuous (⨆ a, p a)` using `Seminorm.continuous_iSup _ hpc hbdd'`. Establish `hS : Continuous ⇑(⨆ a, p a : Seminorm ℂ (SchwartzMap V ℂ))`.

Rewrite using `[Seminorm.coe_iSup_eq hbdd']`. Conclude with `hcont`. Take `⟨s, C, -, hle⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hS`. Use `⟨s, C, fun j f => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ t : Finset ι, ∑ i ∈ t, ‖T j i f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f` using `fun t => by`.

Use `le_trans ?_ (hle f)` and prove the remaining obligations. Rewrite using `[Seminorm.coe_iSup_eq hbdd', iSup_apply, ← hp (j, t) f]`. Conclude with `le_ciSup (f := fun a => p a f) (hbdd f) (j, t)`. Establish `h2` using `(hT j f).tsum_le_of_sum_le h1`. Simplify using `only [← ofReal_norm_eq_enorm]`.

Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hT j f), ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]`. Conclude with `ENNReal.ofReal_le_ofReal h2`.
-/
private theorem tsum_enorm_le_seminorm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [BarrelledSpace ℂ (SchwartzMap V ℂ)]
    {J ι : Type} [Fintype J] (T : J → ι → SchwartzMap V ℂ →L[ℂ] ℂ) (hT : ∀ j f, Summable fun i => ‖T j i f‖) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), ∀ j f,
      ∑' i, ‖T j i f‖ₑ ≤ C * ENNReal.ofReal ((s.sup (schwartzSeminormFamily ℂ V ℂ)) f) := by
  let p : J × Finset ι → Seminorm ℂ (SchwartzMap V ℂ) := fun a =>
    ∑ i ∈ a.2, (normSeminorm ℂ ℂ).comp (T a.1 i).toLinearMap
  have hp : ∀ a f, p a f = ∑ i ∈ a.2, ‖T a.1 i f‖ := by
    rintro ⟨j, t⟩ f
    simp only [p]
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Seminorm.add_apply, ih]; rfl
  have hbdd : ∀ f, BddAbove (Set.range fun a => p a f) := by
    intro f
    refine ⟨∑ j, ∑' i, ‖T j i f‖, ?_⟩
    rintro _ ⟨a, rfl⟩
    simp only [hp]
    exact ((hT a.1 f).sum_le_tsum a.2 fun i _ => norm_nonneg _).trans
      (Finset.single_le_sum (f := fun j => ∑' i, ‖T j i f‖) (fun j _ => tsum_nonneg fun _ => norm_nonneg _)
        (Finset.mem_univ a.1))
  have hbdd' : BddAbove (Set.range p) := (Seminorm.bddAbove_range_iff).2 hbdd
  have hpc : ∀ a, Continuous (p a) := fun a => by
    rw [show ⇑(p a) = fun f => ∑ i ∈ a.2, ‖T a.1 i f‖ from funext (hp a)]
    exact continuous_finset_sum _ fun i _ => (T a.1 i).continuous.norm
  have hcont : Continuous (⨆ a, p a) := Seminorm.continuous_iSup _ hpc hbdd'
  have hS : Continuous ⇑(⨆ a, p a : Seminorm ℂ (SchwartzMap V ℂ)) := by
    rw [Seminorm.coe_iSup_eq hbdd']
    exact hcont
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hS
  refine ⟨s, C, fun j f => ?_⟩
  have h1 : ∀ t : Finset ι, ∑ i ∈ t, ‖T j i f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f := fun t => by
    refine le_trans ?_ (hle f)
    rw [Seminorm.coe_iSup_eq hbdd', iSup_apply, ← hp (j, t) f]
    exact le_ciSup (f := fun a => p a f) (hbdd f) (j, t)
  have h2 := (hT j f).tsum_le_of_sum_le h1
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hT j f), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal h2

/- English proof (translation)
Use `choose T hT using fun (j : Fin m) (ξ : κ → F) => hadm _ (GlobalTheory.RealLift.eval_mem_adm (fun i => algebraMap F (AF F) (ξ i))) (φ j) (hφ j)`. Establish `hT' : ∀ j ξ (f : SInf F κ), A (pureA F f (φ j)) (fun i => algebraMap F (AF F) (ξ i)) = T j ξ f` using `hT`. Use `haveI : BarrelledSpace ℂ (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) := GlobalTheory.schwartzMap_barrelledSpace _`. Take `⟨s, C, hC⟩` from `tsum_enorm_le_seminorm T fun j f => by`. Simplify using `only [← hT']`.

Conclude with `summable_norm_of_mem_schA F (hA _ (Submodule.subset_span ⟨f, φ j, hφ j, rfl⟩))`. Use `⟨s, C, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `le_trans ?_ (Finset.sum_le_sum fun j _ => hC j (f j))` and prove the remaining obligations. Rewrite using `[← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]`.

Use `ENNReal.tsum_le_tsum fun ξ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [hT']`. Conclude with `enorm_sum_le _ _`.
-/
private theorem lattice_sum_le (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (A : Module.End ℂ ((κ → AF F) → ℂ)) (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ)
    (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ A ∈ (adeleClass F).adm κ)
    {m : ℕ} (φ : Fin m → (κ → Af F) → ℂ) (hφ : ∀ j, φ j ∈ SB (κ → Af F)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), ∀ f : Fin m → SInf F κ,
      ∑' ξ : κ → F, ‖A (∑ j, pureA F (f j) (φ j)) (fun i => algebraMap F (AF F) (ξ i))‖ₑ ≤
        C * ∑ j, ENNReal.ofReal ((s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) (f j)) := by
  choose T hT using fun (j : Fin m) (ξ : κ → F) =>
    hadm _ (GlobalTheory.RealLift.eval_mem_adm (fun i => algebraMap F (AF F) (ξ i))) (φ j) (hφ j)
  have hT' : ∀ j ξ (f : SInf F κ), A (pureA F f (φ j)) (fun i => algebraMap F (AF F) (ξ i)) = T j ξ f := hT
  haveI : BarrelledSpace ℂ (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) := GlobalTheory.schwartzMap_barrelledSpace _
  obtain ⟨s, C, hC⟩ := tsum_enorm_le_seminorm T fun j f => by
    simp only [← hT']
    exact summable_norm_of_mem_schA F (hA _ (Submodule.subset_span ⟨f, φ j, hφ j, rfl⟩))
  refine ⟨s, C, fun f => ?_⟩
  rw [Finset.mul_sum]
  refine le_trans ?_ (Finset.sum_le_sum fun j _ => hC j (f j))
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun ξ => ?_
  rw [map_sum, Finset.sum_apply]
  simp only [hT']
  exact enorm_sum_le _ _

end GlobalTheory.XTermLattice

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' om₁ om₁' hT hT₁ Φ hΦ x`. Take `⟨U, hU, hU0⟩` from `GlobalTheory.XTermGen.finsupp hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1`. Take `⟨m, c, φ, hφ, hint⟩` from `GlobalTheory.XTermGen.finite_parts hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1`. Establish `hsp` using `IsUWeilPair.isUSplitting hT₁.weil`. Take `⟨s, C₁, hC₁⟩` from `GlobalTheory.XTermLattice.lattice_sum_le F (om₁ x) (hsp.pres x) (hsp.adm x) φ hφ`.

Use `⟨U, hU, fun N => ?_⟩` and prove the remaining obligations. Use `choose Cj hCj using fun j : Fin m => GlobalTheory.XTermGen.arch_decay hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1 U hU (c j) N s`. Use `⟨C₁ * ENNReal.ofReal (∑ j, |Cj j|), ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩` and prove the remaining obligations. Introduce `k hk l`. Use `set r : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hr`.

Distinguish the cases in `hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U`. Use `choose f hf hfb using fun j => hCj j k hk l hl`. Establish `hD : e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Φ)) = ∑ j, pureA F (f j) (φ j)`. Use function extensionality and compare the values at `x`. Rewrite using `[hint k hk l x, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [pureA, hf j, RingEquiv.symm_apply_apply]`. Establish `hmaj : GlobalTheory.XTermMaj.maj F E N U (l : AE F E) = ENNReal.ofReal r`. Simplify using `only [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, hr]`. Establish `hr0 : 0 ≤ r` using `Real.rpow_nonneg (by positivity) _`.

Rewrite using `[hD, hmaj]`. Use `(hC₁ f).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `gcongr`. Rewrite using `[← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => abs_nonneg _), Finset.sum_mul]`.

Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hr0)]`. Use `Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ((hfb j).trans ?_)` and prove the remaining obligations. Use `gcongr`. Conclude with `le_abs_self _`. Rewrite using `[hU0 k hk l hl]`.

Simplify using `only [map_zero, Pi.zero_apply, enorm_zero, tsum_zero]`. Conclude with `zero_le`.
-/
theorem _root_.GlobalTheory.T.stabilizer_evaluation_triple_case_a : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ N : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ k ∈ K, ∀ l : (AE F E)ˣ,
        ∑' ξ : Fin b × Fin (b + a') → F, ‖om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ))) (fun i => algebraMap F (AF F) (ξ i))‖ₑ ≤
          C * GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
  classical
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' om₁ om₁' hT hT₁ Φ hΦ x
  obtain ⟨U, hU, hU0⟩ := GlobalTheory.XTermGen.finsupp hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1
  obtain ⟨m, c, φ, hφ, hint⟩ := GlobalTheory.XTermGen.finite_parts hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1
  have hsp := IsUWeilPair.isUSplitting hT₁.weil
  obtain ⟨s, C₁, hC₁⟩ := GlobalTheory.XTermLattice.lattice_sum_le F (om₁ x) (hsp.pres x) (hsp.adm x) φ hφ
  refine ⟨U, hU, fun N => ?_⟩
  choose Cj hCj using fun j : Fin m =>
    GlobalTheory.XTermGen.arch_decay hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1 U hU (c j) N s
  refine ⟨C₁ * ENNReal.ofReal (∑ j, |Cj j|), ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro k hk l
  set r : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hr
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · choose f hf hfb using fun j => hCj j k hk l hl
    have hD : e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Φ)) = ∑ j, pureA F (f j) (φ j) := by
      funext x
      rw [hint k hk l x, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pureA, hf j, RingEquiv.symm_apply_apply]
    have hmaj : GlobalTheory.XTermMaj.maj F E N U (l : AE F E) = ENNReal.ofReal r := by
      simp only [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, hr]
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    rw [hD, hmaj]
    refine (hC₁ f).trans ?_
    rw [mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => abs_nonneg _), Finset.sum_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hr0)]
    refine Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ((hfb j).trans ?_)
    gcongr
    exact le_abs_self _
  · rw [hU0 k hk l hl]
    simp only [map_zero, Pi.zero_apply, enorm_zero, tsum_zero]
    exact zero_le
