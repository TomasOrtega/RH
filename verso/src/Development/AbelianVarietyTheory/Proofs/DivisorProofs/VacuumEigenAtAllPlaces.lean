import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocalStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

open scoped Classical

namespace GlobalTheory.VacEig

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Set `b : ContDiffBump (0 : V)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Use `⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((b 0 : ℝ) : ℂ) = 1`. Rewrite using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`.

Simplify using the standard rewrite rules.
-/
theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

/- English proof (translation)
The claim follows from `Filter.eventually_all.mpr fun i => (x i).2.2`.
-/
theorem eventually_int' (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

/- English proof (translation)
Establish `h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1` using `by filter_upwards [hφ, eventually_int' x] with u hu hx`. Rewrite using `[hu]`. Simplify using `[indO, Set.indicator, hx]`. Conclude with `(Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp`.
-/
theorem finite_mulSupport' (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int' x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

/- English proof (translation)
Establish `hfin` using `finite_mulSupport' _ hφ x`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure`. Rewrite using `[← mul_finprod_cond_ne v hfin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pure_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (x : κ → AF F) :
    pure f φ x = φ v (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hfin := finite_mulSupport' _ hφ x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  ring

/- English proof (translation)
Establish `hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u` using `by filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv`. Rewrite using `[Function.update_of_ne hv, hu]`. Rewrite using `[pure_split f _ hφ' v x, Function.update_self]`. Use `congr 2`. Conclude with `finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]`.
-/
theorem pure_update_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  rw [pure_split f _ hφ' v x, Function.update_self]
  congr 2
  exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M ψ hM c hc v γ hγ`. Establish `hvacO : ∀ᶠ u in cofinite, M.vac u = indO u` using `by filter_upwards [hM.std] with u hu`. Rewrite using `[hu]`. Both sides reduce to the same expression. Take `⟨f, hf⟩` from `exists_schwartz_one (Fin n × Fin d → mixedEmbedding.mixedSpace F)`.

Establish `e2` using `hc v γ hγ f`. Rewrite `e2` using `[GlobalTheory.T.weil_rep_pure_tensor_local M ψ v γ (at_latAtV hγ) f M.vac hvacO]`. Use `choose w hw using fun u => Function.ne_iff.mp (hM.vac u).2.1`. Establish `hT : {u | M.vac u ≠ indO u ∧ u ≠ v}.Finite` using `(Filter.eventually_cofinite.mp hvacO).subset fun u hu => hu.1`. Use `set T := hT.toFinset with hTdef`.

Use function extensionality and compare the values at `z`. Use `set y : Fin n × Fin d → Af F := fun i => singleFin v (z i) + ∑ u ∈ T, singleFin u (w u i) with hy`. Use `set x := mkPt (fun _ => (0 : mixedEmbedding.mixedSpace F)) y with hx`. Establish `hxv : (fun i => evFin F v (x i)) = z`. Use function extensionality and compare the values at `i`.

Rewrite using `[hx, evFin_mkPt, hy]`. Simplify using `only [map_add, map_sum, evalV_singleFin_self]`. Rewrite using `[Finset.sum_eq_zero, add_zero]`. Introduce `u hu`. Establish `: u ≠ v` using `(hT.mem_toFinset.mp hu).2`.

Conclude with `evalV_singleFin_ne (Ne.symm this) _`. Establish `hxu : ∀ u, u ≠ v → M.vac u (fun i => evFin F u (x i)) ≠ 0`. Introduce `u huv`. Establish `hcomp : ∀ i, evFin F u (x i) = ∑ u' ∈ T, evalV F u (singleFin u' (w u' i))`. Introduce `i`.

Rewrite using `[hx, evFin_mkPt, hy]`. Simplify using `only [map_add, map_sum, evalV_singleFin_ne huv, zero_add]`. Distinguish the cases in `huT : u ∈ T`. Establish `: (fun i => evFin F u (x i)) = w u`. Use function extensionality and compare the values at `i`.

Rewrite using `[hcomp, Finset.sum_eq_single_of_mem u huT, evalV_singleFin_self]`. Introduce `u' _ hne`. Conclude with `evalV_singleFin_ne (Ne.symm hne) _`. Rewrite using `[this]`. Conclude with `hw u`.

Establish `hstd : M.vac u = indO u`. Assume the negation of the conclusion as `h`. Conclude with `huT (hT.mem_toFinset.mpr ⟨h, huv⟩)`. Establish `: (fun i => evFin F u (x i)) = 0`. Use function extensionality and compare the values at `i`.

Rewrite using `[hcomp, Finset.sum_eq_zero]`. Both sides reduce to the same expression. Introduce `u' hu'`. Establish `hne : u ≠ u'` using `fun h => huT (h ▸ hu')`. Conclude with `evalV_singleFin_ne hne _`.

Rewrite using `[this, hstd]`. Simplify using `[indO, Set.indicator, zero_mem]`. Establish `hR : (f fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), M.vac u (fun i => evFin F u (x i)) ≠ 0`. Use `mul_ne_zero ?_ (finprod_ne_zero fun u => ?_)` and prove the remaining obligations. Establish `: (fun i => evI F (x i)) = 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[hx, evI_mkPt]`. Both sides reduce to the same expression. Rewrite using `[this, hf]`. Conclude with `one_ne_zero`.

Rewrite using `[finprod_eq_if] split_ifs with huv`. Conclude with `hxu u huv`. Conclude with `one_ne_zero`. Establish `h` using `congrFun e2 x`. Rewrite `h` using `[Pi.smul_apply, smul_eq_mul, pure_update_split f M.vac hvacO v _ x, pure_split f M.vac hvacO v x, hxv]`.

Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hR (by linear_combination h)`.
-/
theorem vac_eig : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM c hc v γ hγ
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  obtain ⟨f, hf⟩ := exists_schwartz_one (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  have e2 := hc v γ hγ f
  rw [GlobalTheory.T.weil_rep_pure_tensor_local M ψ v γ (at_latAtV hγ) f M.vac hvacO] at e2
  choose w hw using fun u => Function.ne_iff.mp (hM.vac u).2.1
  have hT : {u | M.vac u ≠ indO u ∧ u ≠ v}.Finite :=
    (Filter.eventually_cofinite.mp hvacO).subset fun u hu => hu.1
  set T := hT.toFinset with hTdef
  funext z
  set y : Fin n × Fin d → Af F := fun i => singleFin v (z i) + ∑ u ∈ T, singleFin u (w u i) with hy
  set x := mkPt (fun _ => (0 : mixedEmbedding.mixedSpace F)) y with hx
  have hxv : (fun i => evFin F v (x i)) = z := by
    funext i
    rw [hx, evFin_mkPt, hy]
    simp only [map_add, map_sum, evalV_singleFin_self]
    rw [Finset.sum_eq_zero, add_zero]
    intro u hu
    have : u ≠ v := (hT.mem_toFinset.mp hu).2
    exact evalV_singleFin_ne (Ne.symm this) _
  have hxu : ∀ u, u ≠ v → M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    intro u huv
    have hcomp : ∀ i, evFin F u (x i) = ∑ u' ∈ T, evalV F u (singleFin u' (w u' i)) := by
      intro i
      rw [hx, evFin_mkPt, hy]
      simp only [map_add, map_sum, evalV_singleFin_ne huv, zero_add]
    by_cases huT : u ∈ T
    · have : (fun i => evFin F u (x i)) = w u := by
        funext i
        rw [hcomp, Finset.sum_eq_single_of_mem u huT, evalV_singleFin_self]
        intro u' _ hne
        exact evalV_singleFin_ne (Ne.symm hne) _
      rw [this]
      exact hw u
    · have hstd : M.vac u = indO u := by
        by_contra h
        exact huT (hT.mem_toFinset.mpr ⟨h, huv⟩)
      have : (fun i => evFin F u (x i)) = 0 := by
        funext i
        rw [hcomp, Finset.sum_eq_zero]
        · rfl
        intro u' hu'
        have hne : u ≠ u' := fun h => huT (h ▸ hu')
        exact evalV_singleFin_ne hne _
      rw [this, hstd]
      simp [indO, Set.indicator, zero_mem]
  have hR : (f fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    refine mul_ne_zero ?_ (finprod_ne_zero fun u => ?_)
    · have : (fun i => evI F (x i)) = 0 := by
        funext i
        rw [hx, evI_mkPt]
        rfl
      rw [this, hf]
      exact one_ne_zero
    · rw [finprod_eq_if]
      split_ifs with huv
      · exact hxu u huv
      · exact one_ne_zero
  have h := congrFun e2 x
  rw [Pi.smul_apply, smul_eq_mul, pure_update_split f M.vac hvacO v _ x, pure_split f M.vac hvacO v x, hxv] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ hR (by linear_combination h)

end GlobalTheory.VacEig
