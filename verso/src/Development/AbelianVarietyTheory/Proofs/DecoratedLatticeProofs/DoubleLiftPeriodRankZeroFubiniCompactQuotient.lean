import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LastSteps

variable {D : D7}

/- English proof (translation)
Establish `hle : flagN d ≤ ⊥`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `g ⟨-, hg⟩`. Establish `hcol : ∀ i : Fin S.rank, ∀ k, subOne S g k i = 0`. Introduce `i k`.

Take `⟨a, ha⟩` from `hg (Pi.single i 1) (Subsingleton.elim _ _)`. Establish `h1` using `congrFun ha k`. Establish `hr : ratV (D` using `D) (Pi.single i (1 : D.host.E)) = Pi.single i 1 := by`. Apply the tactic sequence `funext j; by_cases h : j = i <;> simp [ratV, Pi.single_apply, h]`. Rewrite `h1` using `[hr]`.

Simplify `h1` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hm : (matHom S g).1 = 1`. Establish `: subOne S g = 0` using `by ext k i; exact hcol i k`. Simplify `this` using `[subOne, sub_eq_zero]`. Establish `: matHom S g = 1` using `Units.ext hm`.

Conclude with `Subgroup.mem_bot.2 (Subtype.ext this)`. Conclude with `Subgroup.mem_bot.1 (hle hn)`.
-/
theorem flagN_rank_zero {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    have hcol : ∀ i : Fin S.rank, ∀ k, subOne S g k i = 0 := by
      intro i k
      obtain ⟨a, ha⟩ := hg (Pi.single i 1) (Subsingleton.elim _ _)
      have h1 := congrFun ha k
      have hr : ratV (D := D) (Pi.single i (1 : D.host.E)) = Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [ratV, Pi.single_apply, h]
      rw [hr] at h1
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
    have hm : (matHom S g).1 = 1 := by
      have : subOne S g = 0 := by ext k i; exact hcol i k
      simpa [subOne, sub_eq_zero] using this
    have : matHom S g = 1 := Units.ext hm
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  exact Subgroup.mem_bot.1 (hle hn)

/- English proof (translation)
Unfold `BesLev.per besPer`. Use `congr 1`. Use function extensionality and compare the values at `h`. Establish `e : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ f h n = φ h * f (embA B.d B.o h)`. Introduce `n`.

Establish `hp : ∀ m, psiBes ψ B.d 1 (vecB B.o B.ζ) m = 1` using `fun m => by`. Simplify using `[psiBes, simpleSum, upSum, dotProduct, psiE]`. Rewrite using `[besFun, flagN_rank_zero B.d n.2, one_mul, hp, star_one, mul_one]`. Repeatedly rewrite using `[e]`. Rewrite using `[setIntegral_const]`.

Simplify using `[Measure.real, B.vN.unit.2.2]`.
-/
theorem per_rank_zero (B : BesLev D 0) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ f = ∫ h in B.vA.𝓕, φ h * f (embA B.d B.o h) ∂B.vA.μ := by
  unfold BesLev.per besPer
  congr 1; funext h
  have e : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ f h n = φ h * f (embA B.d B.o h) := by
    intro n
    have hp : ∀ m, psiBes ψ B.d 1 (vecB B.o B.ζ) m = 1 := fun m => by
      simp [psiBes, simpleSum, upSum, dotProduct, psiE]
    rw [besFun, flagN_rank_zero B.d n.2, one_mul, hp, star_one, mul_one]
  simp_rw [e]
  rw [setIntegral_const]
  simp [Measure.real, B.vN.unit.2.2]

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `: IsFiniteMeasure (μ.restrict s)` using `isFiniteMeasure_restrict.2 hs.ne`. Establish `: IsFiniteMeasure (ν.restrict t)` using `isFiniteMeasure_restrict.2 ht.ne`. Conclude with `integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hC p.1 p.2))`.
-/
theorem swap_bdd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] (μ : Measure X) (ν : Measure Y)
    (s : Set X) (t : Set Y) (hs : μ s < ⊤) (ht : ν t < ⊤) (f : X → Y → ℂ) (hf : Continuous (Function.uncurry f))
    (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C) :
    ∫ x in s, ∫ y in t, f x y ∂ν ∂μ = ∫ y in t, ∫ x in s, f x y ∂μ ∂ν := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  have : IsFiniteMeasure (ν.restrict t) := isFiniteMeasure_restrict.2 ht.ne
  exact integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hC p.1 p.2))

/- English proof (translation)
Establish `t0` using `EvalCont.tame_om hom hf hA hT a b ha hb ha' hb'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `t0.1.comp ((continuous_const (y := (1 : GA D T))).prodMk (continuous_id.prodMk (continuous_const (y := (0 : WO S T)))))` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Take `⟨C, hC⟩` from `t0.2 1`.

Conclude with `⟨C, fun x y => by simpa using hC.self_of_nhds ((x, y), 0)⟩`.
-/
theorem om_bdd {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Continuous (fun p : GA D A × GA D T₀ => om (a p.1, b p.2) f 0) ∧ ∃ C : ℝ, ∀ x y, ‖om (a x, b y) f 0‖ ≤ C := by
  have t0 := EvalCont.tame_om hom hf hA hT a b ha hb ha' hb'
  refine ⟨?_, ?_⟩
  · have := t0.1.comp ((continuous_const (y := (1 : GA D T))).prodMk
      (continuous_id.prodMk (continuous_const (y := (0 : WO S T)))))
    simpa [Function.comp_def] using this
  · obtain ⟨C, hC⟩ := t0.2 1
    exact ⟨C, fun x y => by simpa using hC.self_of_nhds ((x, y), 0)⟩

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont

/- English proof (translation)
Rewrite using `[norm_mul]`. Conclude with `mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)`.
-/
theorem bound_mul {x y : ℂ} {C C' : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C') : ‖x * y‖ ≤ C * C' := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

/- English proof (translation)
Establish `: FirstCountableTopology Y` using `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _`. Use `set c : Y → ℂ := fun y => ∫ z in w, b y z * F z ∂κ with hc`. Use `set m : Y → ℂ := fun y => ∫ x in s, φ x * a x y ∂μ with hm`. Establish `hcC : Continuous c` using `Tame.continuous_integral _ _ hw (F := fun y z => b y z * F z) (tame_of_bounded (C := Cb * CF) (hb.mul (hF.comp continuous_snd)) fun y z => bound_mul (hCb y z) (hCF z))`. Establish `hcB : ∀ y, ‖c y‖ ≤ Cb * CF * κ.real w` using `fun y => norm_setIntegral_le_of_norm_le_const hw fun z _ => bound_mul (hCb y z) (hCF z)`.

Establish `hmC : Continuous m` using `Tame.continuous_integral _ _ hs (F := fun y x => φ x * a x y) (tame_of_bounded (C := Cφ * Ca) ((hφ.comp continuous_snd).mul (ha.comp continuous_swap)) fun y x => bound_mul (hCφ x) (hCa x y))`. Establish `hmB : ∀ y, ‖m y‖ ≤ Cφ * Ca * μ.real s` using `fun y => norm_setIntegral_le_of_norm_le_const hs fun x _ => bound_mul (hCφ x) (hCa x y)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[integral_const_mul]`. Use `_ = ∫ y in u, ∫ x in s, φ x * (a x y * c y) ∂μ ∂ν := by`. Use `swap_bdd _ _ _ _ hs hu _ ?_ (Cφ * (Ca * (Cb * CF * κ.real w))) fun x y => bound_mul (hCφ x) (bound_mul (hCa x y) (hcB y))` and prove the remaining obligations. Conclude with `(hφ.comp continuous_fst).mul (ha.mul (hcC.comp continuous_snd))`. Use `_ = ∫ y in u, m y * c y ∂ν := by`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[hm]`. Simplify using `only`. Rewrite using `[← integral_mul_const]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ y in u, ∫ z in w, m y * (b y z * F z) ∂κ ∂ν := by`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[hc]`. Simplify using `only`. Rewrite using `[integral_const_mul]`. Use `_ = ∫ z in w, ∫ y in u, m y * (b y z * F z) ∂ν ∂κ := by`.

Use `swap_bdd _ _ _ _ hu hw _ ?_ (Cφ * Ca * μ.real s * (Cb * CF)) fun y z => bound_mul (hmB y) (bound_mul (hCb y z) (hCF z))` and prove the remaining obligations. Conclude with `(hmC.comp continuous_fst).mul (hb.mul (hF.comp continuous_snd))`. Use `_ = ∫ z in w, F z * ∫ y in u, b y z * m y ∂ν ∂κ := by`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem triple {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology X]
    [SecondCountableTopology Y] [SecondCountableTopology Z] (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    (s : Set X) (u : Set Y) (w : Set Z) (hs : μ s < ⊤) (hu : ν u < ⊤) (hw : κ w < ⊤)
    (φ : X → ℂ) (F : Z → ℂ) (a : X → Y → ℂ) (b : Y → Z → ℂ) (hφ : Continuous φ) (hF : Continuous F)
    (ha : Continuous fun p : X × Y => a p.1 p.2) (hb : Continuous fun p : Y × Z => b p.1 p.2)
    {Cφ CF Ca Cb : ℝ} (hCφ : ∀ x, ‖φ x‖ ≤ Cφ) (hCF : ∀ z, ‖F z‖ ≤ CF) (hCa : ∀ x y, ‖a x y‖ ≤ Ca)
    (hCb : ∀ y z, ‖b y z‖ ≤ Cb) :
    ∫ x in s, φ x * ∫ y in u, a x y * ∫ z in w, b y z * F z ∂κ ∂ν ∂μ =
      ∫ z in w, F z * ∫ y in u, b y z * ∫ x in s, φ x * a x y ∂μ ∂ν ∂κ := by
  have : FirstCountableTopology Y := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  set c : Y → ℂ := fun y => ∫ z in w, b y z * F z ∂κ with hc
  set m : Y → ℂ := fun y => ∫ x in s, φ x * a x y ∂μ with hm
  have hcC : Continuous c :=
    Tame.continuous_integral _ _ hw (F := fun y z => b y z * F z) (tame_of_bounded (C := Cb * CF)
      (hb.mul (hF.comp continuous_snd)) fun y z => bound_mul (hCb y z) (hCF z))
  have hcB : ∀ y, ‖c y‖ ≤ Cb * CF * κ.real w := fun y =>
    norm_setIntegral_le_of_norm_le_const hw fun z _ => bound_mul (hCb y z) (hCF z)
  have hmC : Continuous m :=
    Tame.continuous_integral _ _ hs (F := fun y x => φ x * a x y) (tame_of_bounded (C := Cφ * Ca)
      ((hφ.comp continuous_snd).mul (ha.comp continuous_swap)) fun y x => bound_mul (hCφ x) (hCa x y))
  have hmB : ∀ y, ‖m y‖ ≤ Cφ * Ca * μ.real s := fun y =>
    norm_setIntegral_le_of_norm_le_const hs fun x _ => bound_mul (hCφ x) (hCa x y)
  calc ∫ x in s, φ x * ∫ y in u, a x y * c y ∂ν ∂μ
      = ∫ x in s, ∫ y in u, φ x * (a x y * c y) ∂ν ∂μ := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y in u, ∫ x in s, φ x * (a x y * c y) ∂μ ∂ν := by
        refine swap_bdd _ _ _ _ hs hu _ ?_ (Cφ * (Ca * (Cb * CF * κ.real w))) fun x y =>
          bound_mul (hCφ x) (bound_mul (hCa x y) (hcB y))
        exact (hφ.comp continuous_fst).mul (ha.mul (hcC.comp continuous_snd))
    _ = ∫ y in u, m y * c y ∂ν := by
        congr 1; funext y; rw [hm]; dsimp only; rw [← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ y in u, ∫ z in w, m y * (b y z * F z) ∂κ ∂ν := by
        congr 1; funext y; rw [hc]; dsimp only; rw [integral_const_mul]
    _ = ∫ z in w, ∫ y in u, m y * (b y z * F z) ∂ν ∂κ := by
        refine swap_bdd _ _ _ _ hu hw _ ?_ (Cφ * Ca * μ.real s * (Cb * CF)) fun y z =>
          bound_mul (hmB y) (bound_mul (hCb y z) (hCF z))
        exact (hmC.comp continuous_fst).mul (hb.mul (hF.comp continuous_snd))
    _ = ∫ z in w, F z * ∫ y in u, b y z * m y ∂ν ∂κ := by
        congr 1; funext z; rw [← integral_const_mul]; congr 1; funext y; ring

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont in

/- English proof (translation)
Introduce `D ψ T B t φ Φ₁ Φ₂ F hφ hF hΦ₁ hΦ₂`. Take `⟨-, iA2, -, -, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A`. Take `⟨-, iS2, -, -, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D t.J.W`. Take `⟨-, iT2, -, -, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T`. Establish `: BorelSpace (GA D B.A)` using `⟨rfl⟩`.

Establish `: BorelSpace (GA D t.J.W)` using `⟨rfl⟩`. Establish `: BorelSpace (GA D T)` using `⟨rfl⟩`. Take `⟨Cφ, hCφ⟩` from `bounded_of_contAut B.cpt hφ`. Take `⟨CF, hCF⟩` from `bounded_of_contAut t.cptT hF`. Take `⟨ha, Ca, hCa⟩` from `om_bdd t.s.weil hΦ₁ B.cpt t.cptS (embA B.d B.o) (MonoidHom.id _) (B.d.continuous_embed.comp (continuous_embL B)) continuous_id (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => hγ)`.

Take `⟨hb, Cb, hCb⟩` from `om_bdd t.weil hΦ₂ t.cptS t.cptT (MonoidHom.id _) (MonoidHom.id _) continuous_id continuous_id (fun γ hγ => hγ) (fun γ hγ => hγ)`. Simplify using `only [MonoidHom.id_apply] at ha hCa hb hCb`. Establish `e1 : ∀ h₀, t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁ (embA B.d B.o h₀) = ∫ h in t.s.vW.𝓕, t.s.om (embA B.d B.o h₀, h) Φ₁ 0 * ∫ h' in t.vT.𝓕, t.om (h, h') Φ₂ 0 * F h' ∂t.vT.μ ∂t.s.vW.μ` using `fun h₀ => rfl`. Rewrite using `[per_rank_zero]`. Repeatedly rewrite using `[e1]`.

Conclude with `triple B.vA.μ t.s.vW.μ t.vT.μ B.vA.𝓕 t.s.vW.𝓕 t.vT.𝓕 (vol_lt_top B.cpt B.vA) (vol_lt_top t.cptS t.s.vW) (vol_lt_top t.cptT t.vT) φ F (fun x y => t.s.om (embA B.d B.o x, y) Φ₁ 0) (fun y z => t.om (y, z) Φ₂ 0) hφ.2 hF.2 ha hb hCφ hCF hCa hCb`.
-/
theorem lastLaw : ∀ D : D7, LastLaw D := by
  intro D ψ T B t φ Φ₁ Φ₂ F hφ hF hΦ₁ hΦ₂
  obtain ⟨-, iA2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨-, iS2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D t.J.W
  obtain ⟨-, iT2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (GA D t.J.W) := ⟨rfl⟩
  have : BorelSpace (GA D T) := ⟨rfl⟩
  obtain ⟨Cφ, hCφ⟩ := bounded_of_contAut B.cpt hφ
  obtain ⟨CF, hCF⟩ := bounded_of_contAut t.cptT hF
  obtain ⟨ha, Ca, hCa⟩ := om_bdd t.s.weil hΦ₁ B.cpt t.cptS (embA B.d B.o) (MonoidHom.id _)
    (B.d.continuous_embed.comp (continuous_embL B)) continuous_id
    (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => hγ)
  obtain ⟨hb, Cb, hCb⟩ := om_bdd t.weil hΦ₂ t.cptS t.cptT (MonoidHom.id _) (MonoidHom.id _) continuous_id continuous_id
    (fun γ hγ => hγ) (fun γ hγ => hγ)
  simp only [MonoidHom.id_apply] at ha hCa hb hCb
  have e1 : ∀ h₀, t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁ (embA B.d B.o h₀) =
      ∫ h in t.s.vW.𝓕, t.s.om (embA B.d B.o h₀, h) Φ₁ 0 * ∫ h' in t.vT.𝓕, t.om (h, h') Φ₂ 0 * F h' ∂t.vT.μ ∂t.s.vW.μ :=
    fun h₀ => rfl
  rw [per_rank_zero]
  simp_rw [e1]
  exact triple B.vA.μ t.s.vW.μ t.vT.μ B.vA.𝓕 t.s.vW.𝓕 t.vT.𝓕 (vol_lt_top B.cpt B.vA) (vol_lt_top t.cptS t.s.vW)
    (vol_lt_top t.cptT t.vT) φ F (fun x y => t.s.om (embA B.d B.o x, y) Φ₁ 0) (fun y z => t.om (y, z) Φ₂ 0) hφ.2 hF.2
    ha hb hCφ hCF hCa hCb

end GlobalTheory.Unf.LastSteps

end
