import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)

namespace SecNotIn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartMono (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

/- English proof (translation)
Simplify using `[chartMono, segre]`.
-/
theorem eval_chartMono (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : eval x (chartMono i) = segre x i := by
  simp [chartMono, segre]

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hQ`. Establish `hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q))`. Rewrite using `[Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`.

Establish `h` using `ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f` using `h`. Rewrite using `[h', hx f (Ideal.subset_span hf), mul_zero]`. Conclude with `fun f hf => hle hf`.
-/
theorem eval_scale_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf

/- English proof (translation)
Establish `hrad : g * chartMono i ∈ Q.radical`. Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]`. Introduce `x hx`. Establish `hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p` using `fun _ => rfl`. Rewrite using `[hae, map_mul, eval_chartMono]`.

Distinguish the cases in `h0 : segre x i = 0`. Rewrite using `[h0, mul_zero]`. Rewrite using `[h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]`. Rewrite `hrad` using `[hQp.radical]`. Conclude with `(hQp.mem_or_mem hrad).resolve_right hw`.
-/
theorem mem_of_eval_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) {i : (k : K) → ι k}
    (hw : chartMono i ∉ Q) {g : MRingOver ℂ ι}
    (h : ∀ x : (Σ k, ι k) → ℂ, (∀ f ∈ Q, eval x f = 0) → segre x i ≠ 0 → eval x g = 0) : g ∈ Q := by
  have hrad : g * chartMono i ∈ Q.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p := fun _ => rfl
    rw [hae, map_mul, eval_chartMono]
    by_cases h0 : segre x i = 0
    · rw [h0, mul_zero]
    · rw [h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]
  rw [hQp.radical] at hrad
  exact (hQp.mem_or_mem hrad).resolve_right hw

def normAt (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => (x ⟨q.1, i q.1⟩)⁻¹ * x q

/- English proof (translation)
Introduce `h0` and use `h (Finset.prod_eq_zero (Finset.mem_univ k) h0)`.
-/
theorem entry_ne_zero {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (h : segre x i ≠ 0) (k : K) :
    x ⟨k, i k⟩ ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ k) h0)

/- English proof (translation)
Simplify using `only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`. Rewrite using `[div_eq_mul_inv, mul_comm]`.
-/
theorem segre_normAt (i i' : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) :
    segre (normAt i x) i' = segre x i' / segre x i := by
  simp only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩, eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩`.
-/
theorem normAt_mem {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h], funext fun a => (segre_normAt i (σ a) x).symm⟩`.
-/
theorem normAt_mem_chartSet {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ}
    (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    (fun a => segre x (σ a) / segre x i) ∈ chartSet (conePts Q) σ i :=
  ⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h],
    funext fun a => (segre_normAt i (σ a) x).symm⟩

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨C c, 0, fun x _ => by simp⟩`. Consider the case `add f g hf hg`. Take `⟨F, D, hF⟩` from `hf`. Take `⟨G, E, hG⟩` from `hg`.

Use `⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f a hf`. Take `⟨F, D, hF⟩` from `hf`.

Use `⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, eval_chartMono, hF x hx, eval_X]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_homogenise {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Fin m) ℂ) :
    ∃ (F : MRingOver ℂ ι) (D : ℕ), ∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
      eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, fun x _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, D, hF⟩ := hf
    obtain ⟨G, E, hG⟩ := hg
    refine ⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩
    simp only [map_add, map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]
    ring
  | mul_X f a hf =>
    obtain ⟨F, D, hF⟩ := hf
    refine ⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩
    simp only [map_mul, eval_chartMono, hF x hx, eval_X]
    field_simp
    ring

/- English proof (translation)
Establish `back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ), (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 → eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) → F ∈ Q → f ∈ chartIdeal (conePts Q) σ i`. Introduce `f F D hF hFQ`. Rewrite using `[chartIdeal, mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, hz, hz1, rfl⟩`. Establish `h0 : segre z i ≠ 0` using `by rw [hz1]; exact one_ne_zero`.

Establish `h` using `hF z h0`. Rewrite `h` using `[hz.2 F hFQ, hz1]`. Simplify using `using h.symm`. Use `⟨hne, fun {f g} hfg => ?_⟩` and prove the remaining obligations. Take `⟨F, D, hF⟩` from `exists_homogenise σ i f`.

Take `⟨G, E, hG⟩` from `exists_homogenise σ i g`. Establish `hFG : F * G ∈ Q` using `mem_of_eval_eq_zero hQp hw fun x hx h0 => by`. Establish `h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0` using `(mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)`. Rewrite `h1` using `[map_mul]`. Rewrite using `[map_mul, hF x h0, hG x h0]`.

Take the linear combination `(segre x i ^ D * segre x i ^ E) * h1`. Break down `hQp.mem_or_mem hFG with h | h` into its components or cases. Conclude with `Or.inl (back f F D hF h)`. Conclude with `Or.inr (back g G E hG h)`.
-/
theorem chartIdeal_isPrime {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)

/- English proof (translation)
Proceed by induction on `s using MvPolynomial.induction_on with`. Consider the case `C c => simp [chartSection]`. Consider the case `add f g hf hg`. Simplify using `only [chartSection, map_add] at hf hg ⊢`. Rewrite using `[hf, hg]`.

Consider the case `mul_X f q hf`. Simplify using `only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢`. Rewrite using `[hf]`. Both sides reduce to the same expression.
-/
theorem eval_chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (s : MRingOver ℂ ι) : eval x (chartSection σ i s) = eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add f g hf hg =>
    simp only [chartSection, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢
    rw [hf]
    rfl

end SecNotIn

open SecNotIn in

/- English proof (translation)
Introduce `K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem`. Take `⟨-, ⟨hQp, hQh, -⟩, -⟩` from `hQ`. Establish `hJmin` using `mem_chartComponents.1 hJ`. Establish `hprimeJ : J.IsPrime` using `hJmin.1.1`. Establish `hne : chartIdeal (conePts Q) σ i ≠ ⊤` using `fun h => hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))`.

Establish `hw : chartMono i ∉ Q`. Introduce `hwQ`. Apply `hne` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, hz, hz1, rfl⟩`.

Establish `h0` using `hz.2 _ hwQ`. Rewrite `h0` using `[eval_chartMono, hz1]`. Conclude with `absurd h0 one_ne_zero`. Establish `hprime` using `chartIdeal_isPrime hQp hQh σ hw hne`. Establish `hJI : J ≤ chartIdeal (conePts Q) σ i` using `hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2`.

Establish `hI` using `hJI hmem`. Apply `hsQ` to reduce the goal to its premises. Use `mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_` and prove the remaining obligations. Establish `hz1 : segre (normAt i x) i = 1` using `by rw [segre_normAt, div_self h0]`. Establish `hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i` using `⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩`.

Establish `h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0` using `(mem_vanishingIdeal_iff.1 hI) _ hpt`. Establish `hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x`. Use function extensionality and compare the values at `⟨k, j⟩`. Rewrite using `[chartLift_segre_apply σ i _ hz1]`. Establish `: normAt i x ⟨k, i k⟩ = 1` using `inv_mul_cancel₀ (entry_ne_zero h0 k)`.

Rewrite using `[this, inv_one, mul_one]`. Rewrite `h1` using `[eval_chartSection, hlift]`. Establish `hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s` using `ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k) (fun k => (x ⟨k, i k⟩)⁻¹) x`. Rewrite `h1` using `[hsc]`. Use `(mul_eq_zero.1 h1).resolve_left ?_` and prove the remaining obligations.

Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))`.
-/
theorem chartSection_notMem_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  intro K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem
  obtain ⟨-, ⟨hQp, hQh, -⟩, -⟩ := hQ
  have hJmin := mem_chartComponents.1 hJ
  have hprimeJ : J.IsPrime := hJmin.1.1
  have hne : chartIdeal (conePts Q) σ i ≠ ⊤ := fun h =>
    hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))
  have hw : chartMono i ∉ Q := by
    intro hwQ
    apply hne
    rw [Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 := hz.2 _ hwQ
    rw [eval_chartMono, hz1] at h0
    exact absurd h0 one_ne_zero
  have hprime := chartIdeal_isPrime hQp hQh σ hw hne
  have hJI : J ≤ chartIdeal (conePts Q) σ i := hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2
  have hI := hJI hmem
  apply hsQ
  refine mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_
  have hz1 : segre (normAt i x) i = 1 := by rw [segre_normAt, div_self h0]
  have hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i :=
    ⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩
  have h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0 :=
    (mem_vanishingIdeal_iff.1 hI) _ hpt
  have hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i _ hz1]
    have : normAt i x ⟨k, i k⟩ = 1 := inv_mul_cancel₀ (entry_ne_zero h0 k)
    rw [this, inv_one, mul_one]
  rw [eval_chartSection, hlift] at h1
  have hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s :=
    ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k)
      (fun k => (x ⟨k, i k⟩)⁻¹) x
  rw [hsc] at h1
  refine (mul_eq_zero.1 h1).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
