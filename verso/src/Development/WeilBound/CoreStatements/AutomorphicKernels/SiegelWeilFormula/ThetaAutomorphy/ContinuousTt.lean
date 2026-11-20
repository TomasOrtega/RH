import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.CountableMat

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option maxHeartbeats 400000

/- English proof (translation)
Establish `hΨ : d.om x Φ ∈ d.sch` using `d.ok.dbl.weil.2.1.pres x Φ hΦ`. Establish `hΨg : d.S g (d.om x Φ) ∈ d.sch` using `d.ok.dbl.lin.pres g _ hΨ`. Establish `hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch` using `d.ok.dbl.weil.2.1.pres (nb β) _ hΨg`. Rewrite using `[map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]`. Use `tsum_congr fun X => ?_` and prove the remaining obligations.

Rewrite using `[(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]`. Both sides reduce to the same expression.
-/
theorem stepA (hP : TPar) (hT : TTheta) (d : SD σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G}
    (hnb : IsNMap (σ := σ) (Y := d.Y) d.b nb) (x : d.G) (β : nA σ d.Y d.b) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (tr d g X) := by
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl

/- English proof (translation)
The claim follows from `((cont_tr d hf X).enorm.measurable).aemeasurable`.
-/
theorem meas_tr (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    AEMeasurable (fun g => ‖f (tr d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((cont_tr d hf X).enorm.measurable).aemeasurable

/- English proof (translation)
Take `⟨K, hK⟩` from `Kdil.thetaBdd_of hS F E σ d f hf`. Conclude with `⟨K, hK⟩`.
-/
theorem tbdd (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (tr d g X)‖) ∧ ∑' X, ‖f (tr d g X)‖ ≤ K := by
  obtain ⟨K, hK⟩ := Kdil.thetaBdd_of hS F E σ d f hf
  exact ⟨K, hK⟩

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem pt_bdd (d : SD σ) {f : Mx F E d.m d.n → ℂ} (g : UA σ d.A.J) (s : Set (Matrix (Fin d.m) (Fin d.n) E)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (tr d g X)‖)) (hle : ∑' X, ‖f (tr d g X)‖ ≤ K) :
    ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ∑' X, ‖f (tr d g X)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (tr d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (tr d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (tr d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle

/- English proof (translation)
Use `haveI := countable_mat (E := E) d.m d.n`. Take `⟨K, hK⟩` from `tbdd hS d hf`. Establish `hfin : d.μ d.D < ⊤` using `(cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom`. Rewrite using `[← lintegral_tsum (f := fun (X : s) g => ‖f (tr d g X.1)‖ₑ) fun X => meas_tr d hf X.1]`. Conclude with `ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) ((lintegral_mono fun g => pt_bdd d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)`.
-/
theorem lint_fin (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    (s : Set (Matrix (Fin d.m) (Fin d.n) E)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (tr d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  haveI := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := tbdd hS d hf
  have hfin : d.μ d.D < ⊤ := (cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (tr d g X.1)‖ₑ) fun X => meas_tr d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => pt_bdd d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)

/- English proof (translation)
Use `lint_fin hS d hf Set.univ` as an intermediate fact. Rewrite `this` using `[tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ)]`. Then use the resulting hypothesis.
-/
theorem lint_fin_all (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := lint_fin hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ)] at this

/- English proof (translation)
Establish `h1 : Continuous (Algebra.trace (AF F) (AE F E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Conclude with `h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)`.
-/
theorem continuous_tt (d : SD σ) : Continuous (d.tt) := by
  have h1 : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)

/- English proof (translation)
Use `haveI := countable_mat (E := E) d.m d.n`. Establish `hΨ : d.om x Φ ∈ d.sch` using `d.ok.dbl.weil.2.1.pres x Φ hΦ`. Establish `hf : d.T (d.om x Φ) ∈ d.schM` using `(hB F E σ d).1 _ hΨ`. Establish `hen : ∀ a, ‖d.B.ψ a‖ₑ = 1` using `fun a => by`. Rewrite using `[← ofReal_norm_eq_enorm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]`.

Establish `hψc : Continuous d.B.ψ` using `d.std.1`. Use `set f : Mx F E d.m d.n → ℂ := d.T (d.om x Φ) with hfdef`. Use `set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef`. Use `set G : Matrix (Fin d.m) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AE F E) := fun X => d.gram (incM F X) (incM F X) with hG`. Use `set e : nA σ d.Y d.b → Matrix (Fin d.m) (Fin d.n) E → ℂ := fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he`.

Use `set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ`. Use `set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (tr d g X) ∂d.μ with hH`. Establish `hmeas : ∀ X, AEStronglyMeasurable (fun g => f (tr d g X)) (d.μ.restrict d.D)` using `fun X => (cont_tr d hf X).aestronglyMeasurable`. Establish `hcb : Continuous fun β : nA σ d.Y d.b => β.1` using `continuous_subtype_val`. Establish `hec : ∀ X, Continuous fun β => e β X` using `fun X => hψc.comp ((continuous_const.mul ((continuous_tt d).comp (hcb.matrix_mul continuous_const))).neg)`.

Establish `hχc : Continuous χ` using `hψc.comp (((continuous_tt d).comp (continuous_const.matrix_mul hcb)).neg)`. Establish `hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X` using `fun β => by show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _`. Rewrite using `[PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]`. Use `congr 1`. Establish `hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (tr d g X)` using `fun g => stepA hP hT d hΦ hc.1 x β g`.

Simplify using `only [hA']`. Rewrite using `[integral_tsum (f := fun X g => e β X * f (tr d g X)) (fun X => (hmeas X).const_mul _) ?_]`. Conclude with `tsum_congr fun X => integral_const_mul _ _`. Simplify `lint_fin_all hS d hf` using `only [he, enorm_mul, hen, one_mul]`. Establish `hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0` using `fun X => by`.

Take `⟨hm, S₀, hS₀⟩` from `gram_mem d X T`. Simplify using `only [he, hχ, chr_comb]`. Rewrite using `[orth d hc _ hm ⟨S₀, hS₀⟩]`. Simplify using `only [half_eq_iff]`. Both sides reduce to the same expression.

Establish `h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) = c • ∑' X, e β X * χ β * H X` using `fun β => by`. Rewrite using `[hI β, smul_mul_assoc, ← tsum_mul_right]`. Use `congr 1`. Conclude with `tsum_congr fun X => by simp only [hχ, SD.tt]; ring`. Establish `hlam : lam 𝓖 = 1` using `hc.2.2.2`.

Establish `h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤`. Simplify using `only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]`. Use `ne_top_of_le_ne_top (lint_fin_all hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)` and prove the remaining obligations. Conclude with `enorm_integral_le_lintegral_enorm _`. Establish `h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X = ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1` using `by show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1`.

Rewrite using `[tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]`. Conclude with `tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]`. Establish `h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1` using `by haveI : Countable {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := Subtype.countable show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), f (tr d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T …`. Rewrite using `[setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g => f (tr d g X.1)) (fun X => hmeas X.1) (lint_fin hS d hf {X | G X = (-2 : ℤ) • T.1.1})]`. Use `show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _`.

Rewrite using `[integral_congr_ae (Eventually.of_forall h1), integral_smul, integral_tsum (f := fun X β => e β X * χ β * H X) (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]`. Use `congr 1`. Conclude with `tsum_congr fun X => by rw [integral_mul_const, hO X]`.
-/
theorem thetaCoef_at (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) (d : SD σ)
    {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ) := by
  haveI := countable_mat (E := E) d.m d.n
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hf : d.T (d.om x Φ) ∈ d.schM := (hB F E σ d).1 _ hΨ
  have hen : ∀ a, ‖d.B.ψ a‖ₑ = 1 := fun a => by
    rw [← ofReal_norm_eq_enorm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]
  have hψc : Continuous d.B.ψ := d.std.1
  set f : Mx F E d.m d.n → ℂ := d.T (d.om x Φ) with hfdef
  set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef
  set G : Matrix (Fin d.m) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AE F E) :=
    fun X => d.gram (incM F X) (incM F X) with hG
  set e : nA σ d.Y d.b → Matrix (Fin d.m) (Fin d.n) E → ℂ :=
    fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ
  set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (tr d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (tr d g X)) (d.μ.restrict d.D) :=
    fun X => (cont_tr d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : nA σ d.Y d.b => β.1 := continuous_subtype_val
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((continuous_tt d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((continuous_tt d).comp (continuous_const.matrix_mul hcb)).neg)

  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (tr d g X) :=
      fun g => stepA hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (tr d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, enorm_mul, hen, one_mul] using lint_fin_all hS d hf

  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := gram_mem d X T
    simp only [he, hχ, chr_comb]
    rw [orth d hc _ hm ⟨S₀, hS₀⟩]
    simp only [half_eq_iff]
    rfl

  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, SD.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (lint_fin_all hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)
    exact enorm_integral_le_lintegral_enorm _
  have h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X =
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]
    exact tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
  have h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E //
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    haveI : Countable {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} :=
      Subtype.countable
    show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)),
      f (tr d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g =>
      f (tr d g X.1)) (fun X => hmeas X.1) (lint_fin hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x` and use `thetaCoef_at hS hB hP hT d hΦ hc T x`.
-/
theorem thetaCoef (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) : ThetaCoef :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => thetaCoef_at hS hB hP hT d hΦ hc T x

end PositivityTheory.SiegelWeilFormula.Tauto

end
