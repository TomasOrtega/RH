import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw GlobalTheory.Cont

section
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {G : Type} [Group G] [TopologicalSpace G] {Pp Γ : Subgroup G} {ι : GR n →* G}
  {s₀ : ℂ} {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

/- English proof (translation)
Establish `hnull : NullSec ε c (Q - Q')` using `(hS m n ε c t p q e sL ρ hL (Q - Q')).2 (fun y => by simp [map_sub, h y])`. Establish `key` using `hLC m n ε c hL.cpos ((LinearMap.proj g).comp I) (fun a b P => hD.Iinv g a b P) (Q - Q') hnull`. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply, map_sub, Pi.sub_apply] at key`. Conclude with `sub_eq_zero.mp key`.
-/
theorem I_eq_of_sL (hS : SecZero) (hLC : LC) (hL : LocData ε c t p q e sL ρ) (hD : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {Q Q' : PX m n} (h : ∀ y, sL Q y = sL Q' y) (g : G) : I Q g = I Q' g := by
  have hnull : NullSec ε c (Q - Q') :=
    (hS m n ε c t p q e sL ρ hL (Q - Q')).2 (fun y => by simp [map_sub, h y])
  have key := hLC m n ε c hL.cpos ((LinearMap.proj g).comp I) (fun a b P => hD.Iinv g a b P) (Q - Q') hnull
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, map_sub, Pi.sub_apply] at key
  exact sub_eq_zero.mp key

/- English proof (translation)
Take `⟨x', y, S, r, hr, hg, hx⟩` from `hD.split x`. Establish `hs : ∀ Q : PX m n, sec Q x = S * sL Q y` using `fun Q => by`. Rewrite using `[hg]`. Conclude with `(hx y).2 Q`. Simplify using `only [hz]`.

Rewrite using `[hs P, hP y, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hs (QQ j)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hz_comb (hD : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {N : ℕ} {P : PX m n} {QQ : Fin N → PX m n} {cc : Fin N → ℂ}
    (hP : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) (z : ℂ) (x : G) :
    hz Ht sec s₀ z P x = ∑ j, cc j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x', y, S, r, hr, hg, hx⟩ := hD.split x
  have hs : ∀ Q : PX m n, sec Q x = S * sL Q y := fun Q => by
    rw [hg]
    exact (hx y).2 Q
  simp only [hz]
  rw [hs P, hP y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hs (QQ j)]
  ring

end

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulVec_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (j : Fin N) :
    ∑ i, A j i * ∑ l, B i l * v l = ∑ l, (A * B) j l * v l := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `Differentiable.fun_sum fun σ _ => ?_` and prove the remaining obligations. Use `Differentiable.fun_mul (differentiable_const _) ?_` and prove the remaining obligations. Conclude with `Differentiable.fun_finset_prod fun i _ => h (σ i) i`.
-/
private theorem det_diff_lemma {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) : Differentiable ℂ fun w => (A w).det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => ?_
  refine Differentiable.fun_mul (differentiable_const _) ?_
  exact Differentiable.fun_finset_prod fun i _ => h (σ i) i

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Use `det_diff_lemma (A := fun w => (A w).updateRow b (Pi.single a 1)) fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hib : i = b`. Substitute `hib` using the available equality. Simplify using `only [Matrix.updateRow_self]`.

Conclude with `differentiable_const _`. Simplify using `only [Matrix.updateRow_ne hib]`. Conclude with `h i j`.
-/
private theorem adj_diff_lemma_2 {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) (a b : Fin N) :
    Differentiable ℂ fun w => (A w).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  refine det_diff_lemma (A := fun w => (A w).updateRow b (Pi.single a 1)) fun i j => ?_
  by_cases hib : i = b
  · subst hib
    simp only [Matrix.updateRow_self]
    exact differentiable_const _
  · simp only [Matrix.updateRow_ne hib]
    exact h i j

/- English proof (translation)
Break down `(hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨a, ha⟩` from `ha`. Establish `hon : AnalyticOnNhd ℂ f univ` using `fun x _ => hf.analyticAt x`. Conclude with `ha (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h (mem_univ a))`.

Conclude with `h`.
-/
private theorem ev_ne_lemma_3 {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ha : ∃ a, f a ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨a, ha⟩ := ha
    have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
    exact ha (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h (mem_univ a))
  · exact h

/- English proof (translation)
Establish `hdt : Differentiable ℂ fun w => (M' w).det` using `det_diff_lemma hM`. Establish `hadj : ∀ a b, Differentiable ℂ fun w => (M' w).adjugate a b` using `adj_diff_lemma_2 hM`. Establish `hdt0 : (M' s₀).det = 1` using `by rw [hM0, Matrix.det_one]`. Establish `hgb0 : (∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det = Ah j s₀`. Rewrite using `[hdt0, div_one, hM0, Matrix.adjugate_one]`.

Simplify using `[Matrix.one_apply]`. Establish `hDev` using `ev_ne_lemma_3 hD hDne`. Establish `hdtev` using `ev_ne_lemma_3 hdt ⟨s₀, by rw [hdt0]; exact one_ne_zero⟩`. Establish `hne : ∀ z, ∀ᶠ w in 𝓝[≠] z, w ≠ s₀`. Introduce `z`.

Distinguish the cases in `h : z = s₀`. Substitute `h` using the available equality. Conclude with `self_mem_nhdsWithin`. Conclude with `nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds h)`. Set `f : ℂ → ℂ` to `Function.update (fun w => (∑ i, (M' w).adjugate j i * B i w) / (D w * (M' w).det)) s₀ ((∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det)`.

Establish `hnumV : DifferentiableOn ℂ (fun w => ∑ i, (M' w).adjugate j i * Ah i w) V` using `DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hAh i)`. Establish `hgbA : AnalyticAt ℂ (fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det) s₀` using `(hnumV.analyticAt (hVo.mem_nhds hs₀V)).div (hdt.analyticAt s₀) (by rw [hdt0]; exact one_ne_zero)`. Establish `hf_eq : f =ᶠ[𝓝 s₀] fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det`. Establish `h1 : ∀ᶠ w in 𝓝[≠] s₀, f w = (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det` using `by filter_upwards [hDev s₀, hne s₀, nhdsWithin_le_nhds (hUo.mem_nhds hs₀), nhdsWithin_le_nhds (hVo.mem_nhds hs₀V)] with w hDw hw hwU hwV`. Simplify using `only [f, Function.update_of_ne hw]`.

Establish `h2 : ∑ i, (M' w).adjugate j i * B i w = D w * ∑ i, (M' w).adjugate j i * Ah i w`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hBA w hwV hwU hDw i]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, mul_div_mul_left _ _ hDw]`. Use `filter_upwards [eventually_nhdsWithin_iff.mp h1] with w hw`. Distinguish the cases in `h : w = s₀`. Substitute `h` using the available equality. Simplify using `only [f, Function.update_self]`.

Conclude with `hw h`. Establish `hfA : AnalyticAt ℂ f s₀` using `hgbA.congr hf_eq.symm`. Establish `hfM : MeromorphicOn f U`. Introduce `w hw`. Establish `hnum : AnalyticAt ℂ (fun w => ∑ i, (M' w).adjugate j i * B i w) w` using `(DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hB i)).analyticAt (hUo.mem_nhds hw)`.

Establish `hden : AnalyticAt ℂ (fun w => D w * (M' w).det) w` using `(hD.fun_mul hdt).analyticAt w`. Use `(hnum.meromorphicAt.div hden.meromorphicAt).congr ?_` and prove the remaining obligations. Use `filter_upwards [hne w] with v hv`. Simplify using `only [f, Function.update_of_ne hv, Pi.div_apply]`. Establish `hmain` using `hG U f (Ej j) σ s₀ hUo hUr hs₀ hfM hfA hσU (hEd j) ?_`.

Establish `hfs : f s₀ = Ah j s₀`. Simplify using `only [f, Function.update_self]`. Conclude with `hgb0`. Rewrite `hmain` using `[hfs]`. Conclude with `hmain`.

Introduce `z hz`. Establish `hzo : rightOf σ ∈ 𝓝 z` using `(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz`. Use `filter_upwards [hDev z, hdtev z, hne z, nhdsWithin_le_nhds hzo] with w hDw hdw hw hwσ`. Simplify using `only [f, Function.update_of_ne hw]`. Establish `h3 : ∑ i, (M' w).adjugate j i * B i w = D w * ((M' w).det * Ej j w)`.

Establish `h2 : ∑ i, (M' w).adjugate j i * B i w = D w * ∑ i, (M' w).adjugate j i * ∑ l, M' w i l * Ej l w`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hBE w hwσ i]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, mulVec_sum, Matrix.adjugate_mul]`. Simplify using `[Matrix.smul_apply, Matrix.one_apply]`. Rewrite using `[h3, ← mul_assoc, mul_div_cancel_left₀ _ (mul_ne_zero hDw hdw)]`.
-/
private theorem glue_core_lemma_4 (hG : Glue) {N : ℕ} {s₀ : ℂ} {U V : Set ℂ} {σ : ℝ} {D : ℂ → ℂ}
    {M' : ℂ → Matrix (Fin N) (Fin N) ℂ} {B Ah Ej : Fin N → ℂ → ℂ}
    (hUo : IsOpen U) (hUr : IsRightDomain U) (hs₀ : s₀ ∈ U) (hVo : IsOpen V) (hs₀V : s₀ ∈ V)
    (hD : Differentiable ℂ D) (hDne : ∃ a, D a ≠ 0)
    (hM : ∀ i j, Differentiable ℂ fun w => M' w i j) (hM0 : M' s₀ = 1)
    (hB : ∀ i, DifferentiableOn ℂ (B i) U) (hAh : ∀ i, DifferentiableOn ℂ (Ah i) V)
    (hBA : ∀ w ∈ V, w ∈ U → D w ≠ 0 → ∀ i, B i w = D w * Ah i w)
    (hσU : rightOf σ ⊆ U) (hEd : ∀ j, DifferentiableOn ℂ (Ej j) (rightOf σ))
    (hBE : ∀ w ∈ rightOf σ, ∀ i, B i w = D w * ∑ l, M' w i l * Ej l w) (j : Fin N) :
    HolValueAt (Ej j) s₀ (Ah j s₀) := by
  have hdt : Differentiable ℂ fun w => (M' w).det := det_diff_lemma hM
  have hadj : ∀ a b, Differentiable ℂ fun w => (M' w).adjugate a b := adj_diff_lemma_2 hM
  have hdt0 : (M' s₀).det = 1 := by rw [hM0, Matrix.det_one]
  have hgb0 : (∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det = Ah j s₀ := by
    rw [hdt0, div_one, hM0, Matrix.adjugate_one]
    simp [Matrix.one_apply]
  have hDev := ev_ne_lemma_3 hD hDne
  have hdtev := ev_ne_lemma_3 hdt ⟨s₀, by rw [hdt0]; exact one_ne_zero⟩
  have hne : ∀ z, ∀ᶠ w in 𝓝[≠] z, w ≠ s₀ := by
    intro z
    by_cases h : z = s₀
    · subst h
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds h)
  let f : ℂ → ℂ := Function.update
    (fun w => (∑ i, (M' w).adjugate j i * B i w) / (D w * (M' w).det)) s₀
    ((∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det)
  have hnumV : DifferentiableOn ℂ (fun w => ∑ i, (M' w).adjugate j i * Ah i w) V :=
    DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hAh i)
  have hgbA : AnalyticAt ℂ (fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det) s₀ :=
    (hnumV.analyticAt (hVo.mem_nhds hs₀V)).div (hdt.analyticAt s₀) (by rw [hdt0]; exact one_ne_zero)
  have hf_eq : f =ᶠ[𝓝 s₀] fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det := by
    have h1 : ∀ᶠ w in 𝓝[≠] s₀, f w = (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det := by
      filter_upwards [hDev s₀, hne s₀, nhdsWithin_le_nhds (hUo.mem_nhds hs₀),
        nhdsWithin_le_nhds (hVo.mem_nhds hs₀V)] with w hDw hw hwU hwV
      simp only [f, Function.update_of_ne hw]
      have h2 : ∑ i, (M' w).adjugate j i * B i w = D w * ∑ i, (M' w).adjugate j i * Ah i w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hBA w hwV hwU hDw i]
        ring
      rw [h2, mul_div_mul_left _ _ hDw]
    filter_upwards [eventually_nhdsWithin_iff.mp h1] with w hw
    by_cases h : w = s₀
    · subst h
      simp only [f, Function.update_self]
    · exact hw h
  have hfA : AnalyticAt ℂ f s₀ := hgbA.congr hf_eq.symm
  have hfM : MeromorphicOn f U := by
    intro w hw
    have hnum : AnalyticAt ℂ (fun w => ∑ i, (M' w).adjugate j i * B i w) w :=
      (DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hB i)).analyticAt
        (hUo.mem_nhds hw)
    have hden : AnalyticAt ℂ (fun w => D w * (M' w).det) w := (hD.fun_mul hdt).analyticAt w
    refine (hnum.meromorphicAt.div hden.meromorphicAt).congr ?_
    filter_upwards [hne w] with v hv
    simp only [f, Function.update_of_ne hv, Pi.div_apply]
  have hmain := hG U f (Ej j) σ s₀ hUo hUr hs₀ hfM hfA hσU (hEd j) ?_
  · have hfs : f s₀ = Ah j s₀ := by
      simp only [f, Function.update_self]
      exact hgb0
    rw [hfs] at hmain
    exact hmain
  · intro z hz
    have hzo : rightOf σ ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hDev z, hdtev z, hne z, nhdsWithin_le_nhds hzo] with w hDw hdw hw hwσ
    simp only [f, Function.update_of_ne hw]
    have h3 : ∑ i, (M' w).adjugate j i * B i w = D w * ((M' w).det * Ej j w) := by
      have h2 : ∑ i, (M' w).adjugate j i * B i w
          = D w * ∑ i, (M' w).adjugate j i * ∑ l, M' w i l * Ej l w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hBE w hwσ i]
        ring
      rw [h2, mulVec_sum, Matrix.adjugate_mul]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [h3, ← mul_assoc, mul_div_cancel_left₀ _ (mul_ne_zero hDw hdw)]

/- English proof (translation)
Use `⟨∑ r ∈ d.roots.toFinset, ‖r‖, fun z hz h0 => ?_⟩` and prove the remaining obligations. Establish `hmem : z ∈ d.roots.toFinset`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hd]`. Conclude with `h0`. Establish `h1 : ‖z‖ ≤ ∑ r ∈ d.roots.toFinset, ‖r‖` using `Finset.single_le_sum (f := fun r => ‖r‖) (fun r _ => norm_nonneg r) hmem`.

Establish `h2 : z.re ≤ ‖z‖` using `Complex.re_le_norm z`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem poly_ev_lemma_5 {d : Polynomial ℂ} (hd : d ≠ 0) :
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, ‖r‖, fun z hz h0 => ?_⟩
  have hmem : z ∈ d.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hd]
    exact h0
  have h1 : ‖z‖ ≤ ∑ r ∈ d.roots.toFinset, ‖r‖ :=
    Finset.single_le_sum (f := fun r => ‖r‖) (fun r _ => norm_nonneg r) hmem
  have h2 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using holValueAt_const 0 s₀`. Consider the case `insert a T ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a T)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
private theorem hv_sum_lemma_6 {s₀ : ℂ} {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ}
    (h : ∀ i ∈ T, HolValueAt (f i) s₀ (z i)) :
    HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, z i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a T)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hD P g`. Use `letI : MeasurableSpace ↥(KR n) := borel _`. Use `haveI : BorelSpace ↥(KR n) := ⟨rfl⟩`. Take `⟨W, hWfd, hPW, hWst, -⟩` from `hL.kfin P`. Take `⟨ν, κ, hν, hκ, hproj, hlift⟩` from `hP m n ε c t p q e sL ρ hL W hWfd hWst`.

Use `haveI := hν`. Take `⟨N, yy, QQ, cc, M, hQW, hPc, hM0, hMd, hyy, hint⟩` from `hB m n ε c t p q e sL ρ hL W hWfd hWst ν κ hν hκ hproj hlift P hPW`. Take `⟨σf, hEdiff, hsum, hfar⟩` from `hFar m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD`. Take `⟨r, σv, F, hr, -, hFc, hFd, hF0, -, hFhv⟩` from `hV m n ε c t p q e sL ρ hL hGS G Pp Γ ι s₀ Ht sec I Λ hD`. Take `⟨U, d, Ee, σe, hUo, hUr, hs₀U, hd, hEd, hEc, -, hEeq⟩` from `hD.eis`.

Take `⟨σd, hσd⟩` from `poly_ev_lemma_5 hd`. Take `⟨σU, hσU⟩` from `hUr.1`. Establish `hdne : ∃ a, d.eval a ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hd (Polynomial.funext fun a => by simp [h a])`. Establish `hTS : ∀ i x, ∫ k, κ k * I 1 (x * ι (↑k * yy i)) ∂ν = I (QQ i) x` using `fun i x => hT m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD W hWfd hWst ν κ hν hκ hproj hlift x (yy i) (QQ i) (hQW i) (hyy i)`. Establish `hmap : ∀ i, Continuous fun k : ↥(KR n) => g * ι (↑k * yy i)` using `fun i => continuous_const.mul (hD.ιcont.comp ((continuous_mul_right (yy i)).comp continuous_subtype_val))`. Establish `hAh : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν) (Metric.ball s₀ r)`. Introduce `i`.

Use `(hH (↥(KR n)) ν univ isCompact_univ (by simp) (Metric.ball s₀ r) (fun k z => κ k * F z (g * ι (↑k * yy i))) Metric.isOpen_ball ?_ ?_).1` and prove the remaining obligations. Use `ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_` and prove the remaining obligations. Conclude with `hFc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst))) (fun y hy => ⟨hy.2, mem_univ _⟩)`. Conclude with `fun k _ => (hFd _).const_mul _`. Establish `hBd : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν) U`.

Introduce `i`. Use `(hH (↥(KR n)) ν univ isCompact_univ (by simp) U (fun k z => κ k * Ee z (g * ι (↑k * yy i))) hUo ?_ ?_).1` and prove the remaining obligations. Use `ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_` and prove the remaining obligations. Conclude with `hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst))) (fun y hy => ⟨hy.2, mem_univ _⟩)`. Conclude with `fun k _ => (hEd _).const_mul _`.

Establish `hEF : ∀ w ∈ Metric.ball s₀ r, w ∈ U → d.eval w ≠ 0 → ∀ x, Ee w x = d.eval w * F w x`. Introduce `w hwV hwU hdw x`. Establish `hH' : IsExtAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x' => ↑↑(Ht x') ^ (z - s₀) * sec 1 x') x) w (fun z => Ee z x / d.eval z)`. Use `⟨U, hwU, hUr, fun z hz => ?_, ⟨max σe σd, fun z hz => ?_⟩⟩` and prove the remaining obligations. Conclude with `((hEd x).analyticAt (hUo.mem_nhds hz)).meromorphicAt.div ((Polynomial.differentiable d).analyticAt z).meromorphicAt`.

Establish `hz1 : σe < z.re` using `lt_of_le_of_lt (le_max_left _ _) hz`. Establish `hz2 : σd < z.re` using `lt_of_le_of_lt (le_max_right _ _) hz`. Simplify using `only`. Rewrite using `[(hEeq z hz1).2 x, mul_div_cancel_left₀ _ (hσd z hz2)]`. Establish `hv` using `hFhv x w hwV`.

Rewrite `hv` using `[hH'.holValueAt_iff]`. Establish `hcont : ContinuousAt (fun z => Ee z x / d.eval z) w` using `((hEd x).continuousOn.continuousAt (hUo.mem_nhds hwU)).div (Polynomial.continuous d).continuousAt hdw`. Establish `h1 : F w x = Ee w x / d.eval w` using `tendsto_nhds_unique hv (hcont.tendsto.mono_left nhdsWithin_le_nhds)`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.

Establish `key : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀ (∫ k, κ k * F s₀ (g * ι (↑k * yy j)) ∂ν)`. Introduce `j`. Use `glue_core_lemma_4 (σ := max (max σe σf) σU) (D := fun w => d.eval w) (M' := fun w => M (w - s₀)) (B := fun i z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν) (Ah := fun i z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν) (Ej := fun j z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ …` and prove the remaining obligations. Introduce `w hwV hwU hdw i`. Rewrite using `[← MeasureTheory.integral_const_mul]`.

Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hEF w hwV hwU hdw]`. Expand and normalize the polynomial expressions, which then agree. Introduce `l`.

Conclude with `(hEdiff (QQ l) g).mono fun z hz => lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hz`. Introduce `w hw i`. Establish `hwe : σe < w.re` using `lt_of_le_of_lt (le_trans (le_max_left σe σf) (le_max_left _ σU)) hw`. Establish `hwf : σf < w.re` using `lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hw`. Rewrite using `[← hfar ν κ N yy QQ M hν hκ hint w hwf g i, ← MeasureTheory.integral_const_mul]`.

Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[(hEeq w hwe).2]`. Establish `e1 : hz Ht sec s₀ w 1 = fun x => ↑↑(Ht x) ^ (w - s₀) * sec 1 x` using `rfl`. Rewrite using `[e1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key' : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀ (I (QQ j) g)`. Introduce `j`. Establish `h` using `key j`. Simplify using `only [hF0] at h`.

Rewrite `h` using `[hTS]`. Then use the resulting hypothesis. Establish `hIP : I P g = ∑ j, cc j * I (QQ j) g`. Establish `h` using `I_eq_of_sL hS hLC hL hD (Q := P) (Q' := ∑ j, cc j • QQ j) (fun y => by simp [map_sum, map_smul, hPc y]) g`. Rewrite using `[h]`. Simplify using `[map_sum, map_smul]`.

Establish `hsumHV` using `hv_sum_lemma_6 Finset.univ (s₀ := s₀) (f := fun j z => cc j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) (z := fun j => cc j * I (QQ j) g) (fun j _ => (holValueAt_const (cc j) s₀).mul (key' j))`. Rewrite using `[hIP]`. Use `hsumHV.congr ⟨σf, fun z hzr => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ qq : GlobalTheory.Eis.Cosets Pp Γ, GlobalTheory.Eis.term Pp Γ (fun x => ↑↑(Ht x) ^ (z - s₀) * sec P x) g qq = ∑ j, cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq` using `fun qq => hz_comb hD hPc z _`. Establish `hs` using `Summable.tsum_finsetSum (s := Finset.univ) (f := fun j qq => cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq) (fun j _ => (hsum (QQ j) g z hzr).mul_left (cc j))`.

Simplify using `only [GlobalTheory.Eis.cosetSum]`. Rewrite using `[tsum_congr hc, hs]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[tsum_mul_left]`.
-/
theorem absThm_gen (hV : VacOut) (hP : ProjOp) (hT : TSGen) (hB : Basis) (hFar : FarRight) (hS : SecZero) (hLC : LC)
    (hH : HolParam) (hG : Glue) : AbsThm := by
  intro m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hD P g
  letI : MeasurableSpace ↥(KR n) := borel _
  haveI : BorelSpace ↥(KR n) := ⟨rfl⟩
  obtain ⟨W, hWfd, hPW, hWst, -⟩ := hL.kfin P
  obtain ⟨ν, κ, hν, hκ, hproj, hlift⟩ := hP m n ε c t p q e sL ρ hL W hWfd hWst
  haveI := hν
  obtain ⟨N, yy, QQ, cc, M, hQW, hPc, hM0, hMd, hyy, hint⟩ :=
    hB m n ε c t p q e sL ρ hL W hWfd hWst ν κ hν hκ hproj hlift P hPW
  obtain ⟨σf, hEdiff, hsum, hfar⟩ := hFar m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD
  obtain ⟨r, σv, F, hr, -, hFc, hFd, hF0, -, hFhv⟩ :=
    hV m n ε c t p q e sL ρ hL hGS G Pp Γ ι s₀ Ht sec I Λ hD
  obtain ⟨U, d, Ee, σe, hUo, hUr, hs₀U, hd, hEd, hEc, -, hEeq⟩ := hD.eis
  obtain ⟨σd, hσd⟩ := poly_ev_lemma_5 hd
  obtain ⟨σU, hσU⟩ := hUr.1
  have hdne : ∃ a, d.eval a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (Polynomial.funext fun a => by simp [h a])
  have hTS : ∀ i x, ∫ k, κ k * I 1 (x * ι (↑k * yy i)) ∂ν = I (QQ i) x := fun i x =>
    hT m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD W hWfd hWst ν κ hν hκ hproj hlift x (yy i)
      (QQ i) (hQW i) (hyy i)
  have hmap : ∀ i, Continuous fun k : ↥(KR n) => g * ι (↑k * yy i) := fun i =>
    continuous_const.mul (hD.ιcont.comp ((continuous_mul_right (yy i)).comp continuous_subtype_val))
  have hAh : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν) (Metric.ball s₀ r) := by
    intro i
    refine (hH (↥(KR n)) ν univ isCompact_univ (by simp) (Metric.ball s₀ r)
      (fun k z => κ k * F z (g * ι (↑k * yy i))) Metric.isOpen_ball ?_ ?_).1
    · refine ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_
      exact hFc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst)))
        (fun y hy => ⟨hy.2, mem_univ _⟩)
    · exact fun k _ => (hFd _).const_mul _
  have hBd : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν) U := by
    intro i
    refine (hH (↥(KR n)) ν univ isCompact_univ (by simp) U
      (fun k z => κ k * Ee z (g * ι (↑k * yy i))) hUo ?_ ?_).1
    · refine ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_
      exact hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst)))
        (fun y hy => ⟨hy.2, mem_univ _⟩)
    · exact fun k _ => (hEd _).const_mul _
  have hEF : ∀ w ∈ Metric.ball s₀ r, w ∈ U → d.eval w ≠ 0 → ∀ x, Ee w x = d.eval w * F w x := by
    intro w hwV hwU hdw x
    have hH' : IsExtAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x' => ↑↑(Ht x') ^ (z - s₀) * sec 1 x') x) w
        (fun z => Ee z x / d.eval z) := by
      refine ⟨U, hwU, hUr, fun z hz => ?_, ⟨max σe σd, fun z hz => ?_⟩⟩
      · exact ((hEd x).analyticAt (hUo.mem_nhds hz)).meromorphicAt.div
          ((Polynomial.differentiable d).analyticAt z).meromorphicAt
      · have hz1 : σe < z.re := lt_of_le_of_lt (le_max_left _ _) hz
        have hz2 : σd < z.re := lt_of_le_of_lt (le_max_right _ _) hz
        simp only
        rw [(hEeq z hz1).2 x, mul_div_cancel_left₀ _ (hσd z hz2)]
    have hv := hFhv x w hwV
    rw [hH'.holValueAt_iff] at hv
    have hcont : ContinuousAt (fun z => Ee z x / d.eval z) w :=
      ((hEd x).continuousOn.continuousAt (hUo.mem_nhds hwU)).div
        (Polynomial.continuous d).continuousAt hdw
    have h1 : F w x = Ee w x / d.eval w :=
      tendsto_nhds_unique hv (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    rw [h1]
    field_simp
  have key : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀
      (∫ k, κ k * F s₀ (g * ι (↑k * yy j)) ∂ν) := by
    intro j
    refine glue_core_lemma_4 (σ := max (max σe σf) σU) (D := fun w => d.eval w)
      (M' := fun w => M (w - s₀)) (B := fun i z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν)
      (Ah := fun i z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν)
      (Ej := fun j z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g)
      hG hUo hUr hs₀U Metric.isOpen_ball (Metric.mem_ball_self hr) (Polynomial.differentiable d) hdne
      (fun i j => (hMd i j).comp (differentiable_id.sub_const s₀)) (by simp only [sub_self, hM0])
      hBd hAh ?_ (fun z hz' => hσU (by show σU < z.re; exact lt_of_le_of_lt (le_max_right (max σe σf) σU) hz')) ?_ ?_ j
    · intro w hwV hwU hdw i
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [hEF w hwV hwU hdw]
      ring
    · intro l
      exact (hEdiff (QQ l) g).mono fun z hz =>
        lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hz
    · intro w hw i
      have hwe : σe < w.re := lt_of_le_of_lt (le_trans (le_max_left σe σf) (le_max_left _ σU)) hw
      have hwf : σf < w.re := lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hw
      rw [← hfar ν κ N yy QQ M hν hκ hint w hwf g i, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [(hEeq w hwe).2]
      have e1 : hz Ht sec s₀ w 1 = fun x => ↑↑(Ht x) ^ (w - s₀) * sec 1 x := rfl
      rw [e1]
      ring
  have key' : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀
      (I (QQ j) g) := by
    intro j
    have h := key j
    simp only [hF0] at h
    rwa [hTS] at h
  have hIP : I P g = ∑ j, cc j * I (QQ j) g := by
    have h := I_eq_of_sL hS hLC hL hD (Q := P) (Q' := ∑ j, cc j • QQ j)
      (fun y => by simp [map_sum, map_smul, hPc y]) g
    rw [h]
    simp [map_sum, map_smul]
  have hsumHV := hv_sum_lemma_6 Finset.univ (s₀ := s₀)
    (f := fun j z => cc j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g)
    (z := fun j => cc j * I (QQ j) g) (fun j _ => (holValueAt_const (cc j) s₀).mul (key' j))
  rw [hIP]
  refine hsumHV.congr ⟨σf, fun z hzr => ?_⟩
  have hc : ∀ qq : GlobalTheory.Eis.Cosets Pp Γ,
      GlobalTheory.Eis.term Pp Γ (fun x => ↑↑(Ht x) ^ (z - s₀) * sec P x) g qq
        = ∑ j, cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq := fun qq =>
    hz_comb hD hPc z _
  have hs := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun j qq => cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq)
    (fun j _ => (hsum (QQ j) g z hzr).mul_left (cc j))
  simp only [GlobalTheory.Eis.cosetSum]
  rw [tsum_congr hc, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]

end PositivityTheory.Rg.Sw.AbsSt
