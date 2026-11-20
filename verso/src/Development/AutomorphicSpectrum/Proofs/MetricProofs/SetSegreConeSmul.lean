import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartDim SegreChartDim

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hdim' : ∀ Q' ∈ Q.minimalPrimes, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)`. Introduce `Q' hQ'`. Rewrite `hQ'` using `[Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]`. Rewrite using `[hQ']`. Conclude with `hdim`.

Use `set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal Q i) with hT`. Use `set S := setSegChartSet (conePts Q) σ i with hS`. Establish `hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal Q i, eval y h = 0` using `fun y => by`. Simplify using `[hT, MvPolynomial.mem_zeroLocus_iff]`. Establish `hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S`.

Introduce `y hy`. Take `⟨hc, h1, -⟩` from `ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)`. Conclude with `⟨y, hc, by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1], rfl⟩`. Establish `hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 → chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z`. Introduce `z hz`.

Use function extensionality and compare the values at `q`. Rewrite using `[chartLift_segre_apply σ i z hz q.1 q.2]`. Simplify using `[ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]`. Establish `hliftS : ∀ x ∈ S, chartLift σ i x ∈ T`. Introduce and unpack `_ ⟨z, hz, hzi, rfl⟩`.

Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`. Establish `: segre z i = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`. Rewrite `this` using `[hzi]`. Conclude with `one_ne_zero this`. Rewrite using `[hTmem, hlift_apply z hzi]`.

Conclude with `(ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 hz`. Establish `hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Rewrite using `[segre_chartLift σ i z hzi]`. Establish `hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y`.

Introduce `y hy`. Take `⟨-, h1, -⟩` from `ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)`. Establish `hyi : segre y i = 1` using `by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1]`. Use function extensionality and compare the values at `q`. Rewrite using `[chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]`.

Set `α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ` to `aeval fun a => ∏ k, X ⟨k, σ a k⟩`. Set `β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ` to `aeval fun q => X (σ.symm (Function.update i q.1 q.2))`. Establish `hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f`. Introduce `y f`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C c => simp [α]`. Consider the case `add f g hf hg => simp [hf, hg]`. Consider the case `mul_X f a hf`. Rewrite using `[map_mul, map_mul, map_mul, hf]`. Simplify using `[α, ReciprocityTheory.ChartRestriction.G.Geo.segre, map_prod]`.

Establish `hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g`. Introduce `x g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C c => simp [β]`. Consider the case `add f g hf hg => simp [hf, hg]`.

Consider the case `mul_X f q hf`. Rewrite using `[map_mul, map_mul, map_mul, hf]`. Simplify using `[β, chartLift]`. Establish `hvanS : ∀ f, f ∈ setSegChartIdeal (conePts Q) σ i ↔ ∀ x ∈ S, eval x f = 0` using `fun f => by`. Simplify using `[setSegChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]`.

Establish `hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0` using `fun g => by`. Simplify using `[MvPolynomial.mem_vanishingIdeal_iff]`. Establish `htr` using `minimalPrimes_transfer α.toRingHom β.toRingHom (setSegChartIdeal (conePts Q) σ i) (MvPolynomial.vanishingIdeal ℂ T) (fun f hf => by`. Rewrite using `[Ideal.mem_comap, hvanT]`. Introduce `y hy`.

Use `show eval y (α f) = 0`. Rewrite using `[hα]`. Conclude with `(hvanS f).1 hf _ (hsegT y hy))`. Use the proof step `(fun g hg => by`. Rewrite using `[Ideal.mem_comap, hvanS]`.

Introduce `x hx`. Use `show eval x (β g) = 0`. Rewrite using `[hβ]`. Conclude with `(hvanT g).1 hg _ (hliftS x hx))`. Use the proof step `(fun f => by`.

Rewrite using `[hvanS]`. Introduce `x hx`. Use `show eval x (β (α f) - f) = 0`. Rewrite using `[map_sub, hβ, hα, hsegLift x hx, sub_self])`. Use the proof step `(fun g => by`.

Rewrite using `[hvanT]`. Introduce `y hy`. Use `show eval y (α (β g) - g) = 0`. Rewrite using `[map_sub, hα, hβ, hliftSeg y hy, sub_self])`. Use `J hJ`.

Take `⟨hmin, hd⟩` from `htr`. Rewrite using `[hd]`. Rewrite `hmin` using `[hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes]`. Conclude with `ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim' i hmin`.
-/
theorem segChart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {J : Ideal (MvPolynomial (Fin m) ℂ)}
    (hJ : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hdim' : ∀ Q' ∈ Q.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q' hQ'
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ'
    rw [hQ']
    exact hdim

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal Q i) with hT
  set S := setSegChartSet (conePts Q) σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal Q i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, hc, by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 hz
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, ReciprocityTheory.ChartRestriction.G.Geo.segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ setSegChartIdeal (conePts Q) σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [setSegChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (setSegChartIdeal (conePts Q) σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J hJ
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim' i hmin

/- English proof (translation)
Introduce and unpack `_ ⟨z, hz, rfl⟩ a ha`. Take `⟨z', hz', hseg⟩` from `exists_segre_smul hQ hz ha`. Conclude with `⟨z', hz', funext fun b => by simp [hseg]⟩`.
-/
theorem setSegreCone_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ setSegreCone (conePts Q) σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ setSegreCone (conePts Q) σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := exists_segre_smul hQ hz ha
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩

/- English proof (translation)
Establish `hl : ∀ z : (Σ k, ι k) → ℂ, eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0` using `fun z => by`. Rewrite using `[show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]`. Simplify using the standard rewrite rules. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, h1, rfl⟩`. Conclude with `⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩`. Introduce and unpack `⟨⟨z, hz, rfl⟩, h1⟩`. Conclude with `⟨z, hz, (hl z).symm.trans h1, rfl⟩`.
-/
theorem chart_eq (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    setChartSet S σ Ψ = {x | x ∈ setSegreCone S σ ∧ eval x (linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [setSegChartSet, setSegreCone, Set.mem_ofPred_eq, linForm_single', eval_X]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, h1, rfl⟩`. Conclude with `⟨⟨z, hz, rfl⟩, h1⟩`.

Introduce and unpack `⟨⟨z, hz, rfl⟩, h1⟩`. Conclude with `⟨z, hz, h1, rfl⟩`.
-/
theorem segChart_eq (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    setSegChartSet S σ (σ a) = {x | x ∈ setSegreCone S σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [setSegChartSet, setSegreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

/- English proof (translation)
Establish `hC` using `setSegreCone_smul hQ σ`. Use `set t := psiCoeffs σ Ψ`. Establish `hS : setChartSet (conePts Q) σ Ψ = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (linForm t) = 1}` using `chart_eq _ σ Ψ`. Establish `hJp : J.IsPrime` using `hJ.1.1`. Establish `hIJ : setChartIdeal (conePts Q) σ Ψ ≤ J` using `hJ.1.2`.

Use `set H := vanishingIdeal ℂ (setSegreCone (conePts Q) σ)`. Establish `hH : IsHomogIdeal H` using `ConeVanishingHomog.proof m _ hC`. Establish `hHI : H ≤ setChartIdeal (conePts Q) σ Ψ`. Rewrite using `[setChartIdeal, hS]`. Conclude with `vanishingIdeal_anti_mono fun x hx => hx.1`.

Establish `hℓ1 : linForm t - 1 ∈ setChartIdeal (conePts Q) σ Ψ`. Rewrite using `[setChartIdeal, hS, mem_vanishingIdeal_iff]`. Introduce `x hx`. Simplify using `[hx.2]`. Take `⟨W, hW, hℓW, hWJ, hWcore⟩` from `ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)`.

Establish `hHW : H ≤ W` using `hWcore H hH (hHI.trans hIJ)`. Take `⟨a, ha⟩` from `exists_X_not_mem hℓW`. Use `set u : Fin m → ℂ := Pi.single a 1`. Establish `huW : linForm u ∉ W` using `by rw [linForm_single']; exact ha`. Establish `hT : setSegChartSet (conePts Q) σ (σ a) = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (linForm u) = 1}` using `segChart_eq _ σ a`.

Use `ChartDehomogPrime.proof ℂ m W u hW huW` as an intermediate fact. Establish `hTJ' : setSegChartIdeal (conePts Q) σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1}`. Rewrite using `[setSegChartIdeal, hT]`. Conclude with `ConeSliceIdeal.proof m _ u W hC hHW`. Take `⟨Q₀, hQ₀, hQ₀J'⟩` from `Ideal.exists_minimalPrimes_le hTJ'`.

Establish `hdimQ₀` using `segChart_dim hQp hQ hdim σ (σ a) hQ₀`. Establish `hu1 : linForm u - 1 ∈ setSegChartIdeal (conePts Q) σ (σ a)`. Rewrite using `[setSegChartIdeal, hT, mem_vanishingIdeal_iff]`. Introduce `x hx`. Simplify using `[hx.2]`.

Establish `hHT : H ≤ setSegChartIdeal (conePts Q) σ (σ a)`. Rewrite using `[setSegChartIdeal, hT]`. Conclude with `vanishingIdeal_anti_mono fun x hx => hx.1`. Take `⟨V, hV, huV, hVQ₀, hVcore⟩` from `ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)`. Establish `hHV : H ≤ V` using `hVcore H hH (hHT.trans hQ₀.1.2)`.

Establish `hVW : V ≤ W` using `le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW ((le_sup_left.trans hVQ₀.le).trans hQ₀J')`. Establish `hIV : setChartIdeal (conePts Q) σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1}`. Rewrite using `[setChartIdeal, hS]`. Conclude with `ConeSliceIdeal.proof m _ t V hC hHV`. Establish `hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J` using `sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))`.

Establish `hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes` using `⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩`. Establish `hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes`. Use `hQ₀.1.1` as an intermediate fact. Rewrite using `[hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]`. Both sides reduce to the same expression.

Establish `d₁` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin`. Establish `d₂` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min`. Rewrite `d₁` using `[← d₂, hdimQ₀]`. Conclude with `eq_of_add_one_eq d₁`.
-/
theorem chart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hC := setSegreCone_smul hQ σ
  set t := psiCoeffs σ Ψ
  have hS : setChartSet (conePts Q) σ Ψ = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (linForm t) = 1} := chart_eq _ σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : setChartIdeal (conePts Q) σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (setSegreCone (conePts Q) σ)
  have hH : IsHomogIdeal H := ConeVanishingHomog.proof m _ hC
  have hHI : H ≤ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : linForm t - 1 ∈ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : setSegChartSet (conePts Q) σ (σ a) = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (linForm u) = 1} :=
    segChart_eq _ σ a

  have := ChartDehomogPrime.proof ℂ m W u hW huW
  have hTJ' : setSegChartIdeal (conePts Q) σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1} := by
    rw [setSegChartIdeal, hT]; exact ConeSliceIdeal.proof m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := segChart_dim hQp hQ hdim σ (σ a) hQ₀
  have hu1 : linForm u - 1 ∈ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : setChartIdeal (conePts Q) σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1} := by
    rw [setChartIdeal, hS]; exact ConeSliceIdeal.proof m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end Dim

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
