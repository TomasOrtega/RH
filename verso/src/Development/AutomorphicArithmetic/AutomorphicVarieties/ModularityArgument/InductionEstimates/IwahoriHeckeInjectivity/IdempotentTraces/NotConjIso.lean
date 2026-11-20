import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.NormIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndCOfIndComplex
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section Pow

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

/- English proof (translation)
Rewrite using `[← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]`. Conclude with `h _`.
-/
private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

/- English proof (translation)
Use `⟨fun x hx => Units.ext ?_, ?_⟩` and prove the remaining obligations. Establish `hx' : Valued.v (x : v.adicCompletion K) = 1` using `hx`. Rewrite using `[pow_loc h, FinitePlace.norm_def, hx']`. Simplify using the standard rewrite rules. Establish `hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ)` using `unif_spec v`.

Use `(pow_loc h v (atFin v (unif v))).trans ?_` and prove the remaining obligations. Rewrite using `[FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Establish `e : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a` using `(-1 : ℤ)))) = -1 := rfl`. Establish `e' : normV v = Ideal.absNorm v.asIdeal` using `rfl`. Rewrite using `[e, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast, Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]`.
-/
private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
    have e' : normV v = Ideal.absNorm v.asIdeal := rfl
    rw [e, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal (𝓞 E)`. Conclude with `⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩`.
-/
private theorem exists_place (E : Type) [Field E] [NumberField E] : Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩

/- English proof (translation)
Take `⟨b, hb⟩` from `GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E) (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E) (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)`. Establish `hgen : ∀ z : ℂ, IsPow (GlobalTheory.CuspRep.Model.absC E z) (z * b)` using `fun z y => by`. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _`. Establish `hpos` using `(GroundTheory.Global.IdeleGroup.ideleModule E y).2`. Rewrite using `[hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb1 : b = 1`. Take `⟨w⟩` from `exists_place E`.

Establish `h1` using `(pow_val (hgen 1) w).2`. Establish `e' : normV w = Ideal.absNorm w.asIdeal` using `rfl`. Rewrite `h1` using `[PositivityTheory.Rg.Rs.StrStepB.absC_val, e']`. Establish `h0 : 1 < (Ideal.absNorm w.asIdeal : ℕ)` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `h2` using `congrArg norm h1`.

Rewrite `h2` using `[Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast_cpow_of_pos (by omega), show (-(1 : ℂ)).re = -1 by simp, show (-(1 * (b : ℂ))).re = -b by simp]`. Establish `h3` using `congrArg Real.log h2`. Rewrite `h3` using `[Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ))), Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ)))]`. Establish `h4 : Real.log (Ideal.absNorm w.asIdeal : ℕ) ≠ 0` using `(Real.log_pos (by exact_mod_cast h0)).ne'`. Combine the linear relations using `[mul_right_cancel₀ h4 h3]`.

Simplify `hgen s` using `[hb1]`.
-/
private theorem absC_pow (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (s : ℂ) : IsPow (GlobalTheory.CuspRep.Model.absC E s) s := by
  obtain ⟨b, hb⟩ := GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E)
    (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E)
    (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)
  have hgen : ∀ z : ℂ, IsPow (GlobalTheory.CuspRep.Model.absC E z) (z * b) := fun z y => by
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E y).2
    rw [hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
    congr 1
    push_cast
    ring
  have hb1 : b = 1 := by
    obtain ⟨w⟩ := exists_place E
    have h1 := (pow_val (hgen 1) w).2
    have e' : normV w = Ideal.absNorm w.asIdeal := rfl
    rw [PositivityTheory.Rg.Rs.StrStepB.absC_val, e'] at h1
    have h0 : 1 < (Ideal.absNorm w.asIdeal : ℕ) := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h2 := congrArg norm h1
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast_cpow_of_pos (by omega),
      show (-(1 : ℂ)).re = -1 by simp, show (-(1 * (b : ℂ))).re = -b by simp] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ))),
      Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ)))] at h3
    have h4 : Real.log (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast h0)).ne'
    linarith [mul_right_cancel₀ h4 h3]
  simpa [hb1] using hgen s

/- English proof (translation)
The claim follows from `Subtype.ext (MonoidHom.ext fun x => Units.ext ((h x).trans (absC_pow E s x).symm))`.
-/
private theorem pow_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s) :
    χ = GlobalTheory.CuspRep.Model.absC E s :=
  Subtype.ext (MonoidHom.ext fun x => Units.ext ((h x).trans (absC_pow E s x).symm))

/- English proof (translation)
Rewrite using `[pow_eq h, GlobalTheory.CuspRep.Model.expo_absC]`.
-/
private theorem pow_expo {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s)
    (τ : E →+* ℂ) : expo χ τ = s := by
  rw [pow_eq h, GlobalTheory.CuspRep.Model.expo_absC]

end Pow

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Formalism.L2.Host Formalism.ConjugateSelfDual

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 F)).isMaximal` as an intermediate fact. Conclude with `(Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm`.
-/
private theorem norm_deg (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  exact (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm

/- English proof (translation)
Use `v.isMaximal` as an intermediate fact. Establish `: Fintype (v.asIdeal.primesOver (𝓞 E))` using `(IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype`. Rewrite using `[← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]`. Use `(Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)` and prove the remaining obligations. Use `q.2.1` as an intermediate fact.

Conclude with `Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)`.
-/
private theorem deg_sum (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

/- English proof (translation)
Use `w.isPrime` as an intermediate fact. Use `w'.isPrime` as an intermediate fact. Establish `hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F)` using `(congrArg HeightOneSpectrum.asIdeal hu).symm`. Establish `hs` using `deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}`. Rewrite `hs` using `[Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))]`.

Establish `h3` using `w.asIdeal.inertiaDeg_pos (𝓞 F)`. Establish `h4` using `w'.asIdeal.inertiaDeg_pos (𝓞 F)`. Rewrite using `[norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]`.
-/
private theorem norm_split (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) : normV w = normV (w.under (𝓞 F)) := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F) := (congrArg HeightOneSpectrum.asIdeal hu).symm
  have hs := deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  rw [norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]

/- English proof (translation)
Establish `: Algebra.IsQuadraticExtension F E` using `⟨h2⟩`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Take `⟨y, hy, hy'⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard`. Conclude with `⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩`.
-/
private theorem gal_two (h2 : Module.finrank F E = 2) : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 ∧ ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact ⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩

end Places

section Conj

open Formalism.L2.Host UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Bc

/- English proof (translation)
Introduce `e`. Establish `h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m` using `Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩`. Rewrite `h1` using `[e]`. Take `⟨i, -, hi⟩` from `Multiset.mem_map.1 h1`. Establish `h2 : m' i = m 0` using `Int.cast_injective (add_left_cancel hi)`.

Use `fin_cases i`. Conclude with `absurd (@h 2 0 h2) (by decide)`. Conclude with `absurd (@h 3 0 h2) (by decide)`.
-/
private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
/- English proof (translation)
Introduce `h`. Establish `: Algebra.IsQuadraticExtension K M` using `⟨h2⟩`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Take `⟨m, m', τ, τ', hne, h1, h2', k1, k2, hinj⟩` from `hm φ`. Take `⟨σ₀, hσ⟩` from `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2'.symm)`.

Take `⟨y, -, hy⟩` from `gal_two (F := K) (E := M) h2`. Establish `h0 : σ₀ ≠ 1`. Introduce and unpack `rfl`. Conclude with `hne (RingHom.ext fun x => (RingHom.congr_fun hσ x))`. Take `rfl : σ₀ = σ` from `((hy σ₀).resolve_left h0).trans ((hy σ).resolve_left h1σ).symm`.

Take `⟨s, hs⟩` from `SGalAdEx_holds M σ₀.toRingEquiv`. Take `⟨P', hsp, hiso⟩` from `h s hs`. Take `⟨d, hd, hd'⟩` from `exists_GD _ s hs`. Consider the cases of `P' with`. Consider the case `re π' => exact hiso.elim`.

Consider the case `cx π'`. Establish `e : τ.comp (d.σ.symm : M →+* M) = τ'`. Rewrite using `[hd']`. Conclude with `hσ`. Establish `k3 : π'.HasInfChar τ (infOf m')`.

Use `⟨k2.1, fun u x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : x.1 ∈ (Cusp.cx π').space` using `⟨x, hx, rfl⟩`. Rewrite `hx'` using `[hsp]`. Take `⟨_, ⟨y, hy, rfl⟩, hxy⟩` from `hx'`. Take `rfl : x = pull d 2 y` from `Subtype.ext (by rw [← hxy, ← hd]; rfl)`.

Rewrite using `[cap_pull, e, k2.2 u y hy, map_smul]`. Conclude with `infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))`.
-/
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    (h2 : Module.finrank K M = 2) (π : CuspSub M 2) (hm : MixWtC K π) (σ : M ≃ₐ[K] M) (h1σ : σ ≠ 1) :
    ¬ (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  have : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', hne, h1, h2', k1, k2, hinj⟩ := hm φ
  obtain ⟨σ₀, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2'.symm)
  obtain ⟨y, -, hy⟩ := gal_two (F := K) (E := M) h2
  have h0 : σ₀ ≠ 1 := by
    rintro rfl
    exact hne (RingHom.ext fun x => (RingHom.congr_fun hσ x))
  obtain rfl : σ₀ = σ := ((hy σ₀).resolve_left h0).trans ((hy σ).resolve_left h1σ).symm
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ₀.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))

end Conj

section Main

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

/- English proof (translation)
The claim follows from `GlobalTheory.SphGal.hasSatGL_twist E a π χ w B hu h`.
-/
private theorem satTw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {π : CuspSub E a}
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) {χ : HChar E}
    (hu : χ.UnrAt w) : (CG.mk (π.twist χ)).HasSat w (B.map (· * χ.val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π χ w B hu h

/- English proof (translation)
Introduce `hN K M _ _ hK _ _ hM _ h2 π hm hS`. Establish `hq : Algebra.IsQuadraticExtension K M` using `⟨h2⟩`. Set `μ : Measure (normOneGL M 2)` to `Measure.haar`. Take `⟨χ, ⟨s, hχ⟩, V, hV⟩` from `Dp.exTwist M 2 μ π (by norm_num)`. Take `⟨hex, hpw⟩` from `powTwist K M`.

Take `⟨χ₀, hχ₀⟩` from `(hex s).1`. Take `⟨hi₀, hi, -⟩` from `hpw s χ₀ χ hχ₀ hχ`. Establish `hback` using `((hpw s χ₀ χ hχ₀ hχ).2.2 2 (by norm_num)).2.1 π`. Establish `hCj` using `((hpw (-s) χ₀⁻¹ χ⁻¹ hi₀ hi).2.2 2 (by norm_num)).2.2.2.1`. Establish `hnorm : GlobalTheory.DiscSpec.IsNormalised (π.twist χ)` using `(Dp.normIff M 2 _).2 ((Dp.exSummand M 2 μ _ V).1 hV).1`.

Establish `hnc : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ¬ (UpperTheory.CBC.Cusp.cx (π.twist χ)).ConjIso σ.toRingEquiv` using `fun σ h1 hc => not_conjIso h2 π hm σ h1 (by simpa only [hback] using hCj _ _ hc)`. Establish `hsb : SplitBad K (π.twist χ)` using `fun v hv => ⟨(hS v hv).1, fun w hw =>`. Set `⟨_, hB⟩` to `(hS v hv).2 w hw`. Use the proof step `⟨_, satTw hB (pow_val hχ w).1⟩⟩`. Take `⟨P, hP, hI⟩` from `hN K M h2 (π.twist χ) hnorm hnc hsb`.

Establish `hun : ∀ {w : HeightOneSpectrum (𝓞 M)} {B : Multiset ℂˣ}, (CG.mk (π.twist χ)).HasSat w B → (CG.mk π).HasSat w (B.map (· * χ⁻¹.val w))` using `fun {w B} h => by`. Establish `h1` using `satTw h (pow_val hi w).1`. Rewrite `h1` using `[hback]`. Then use the resulting hypothesis. Establish `hv : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) ^ f` using `fun w f hf => by`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val, (pow_val hi _).2, (pow_val hi₀ _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]`. Use `⟨P.twist χ₀⁻¹, hP.mono fun w hw => ⟨fun w' hne e => ?_, fun hq2 => ?_⟩, fun τ τ' m m' hne hc k1 k2 => ?_⟩` and prove the remaining obligations. Take `⟨B, B', k1, k2, k3⟩` from `hw.1 w' hne e`. Establish `e1 : χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K))` using `(hv w 1 ((norm_split h2 hne e).trans (pow_one _).symm)).trans (pow_one _)`. Establish `e2 : χ⁻¹.val w' = χ₀⁻¹.val (w.under (𝓞 K))`.

Rewrite using `[← e]`. Conclude with `(hv w' 1 ((norm_split h2 hne.symm e.symm).trans (by rw [e, pow_one]))).trans (pow_one _)`. Use `⟨_, _, hun k1, hun k2, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, e2, ← Multiset.map_add]`. Conclude with `satTw k3 (pow_val hi₀ _).1`.

Take `⟨_, B', k1, rfl, k3⟩` from `hw.2 hq2`. Use `⟨_, B'.map (· * χ₀⁻¹.val (w.under (𝓞 K))), ?_, ?_, satTw k3 (pow_val hi₀ _).1⟩` and prove the remaining obligations. Establish `k4` using `hun k1`. Rewrite `k4` using `[hv w 2 hq2]`. Simplify `k4` using `only [Multiset.map_map, Function.comp_def, mul_pow]`.

Simplify using `only [Multiset.map_add, Multiset.map_map, Function.comp_def, neg_mul]`. Establish `k` using `(hI τ τ' _ _ hne hc (k1.twist χ) (k2.twist χ)).twist χ₀⁻¹`. Rewrite `k` using `[pow_expo hχ, pow_expo hχ, pow_expo hi₀, ← Multiset.map_add, Multiset.map_map]`. Simplify using `using k`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs :
    IndNorm → IndCs := by
  intro hN K M _ _ hK _ _ hM _ h2 π hm hS
  have hq : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  let μ : Measure (normOneGL M 2) := Measure.haar
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ := Dp.exTwist M 2 μ π (by norm_num)
  obtain ⟨hex, hpw⟩ := powTwist K M
  obtain ⟨χ₀, hχ₀⟩ := (hex s).1
  obtain ⟨hi₀, hi, -⟩ := hpw s χ₀ χ hχ₀ hχ
  have hback := ((hpw s χ₀ χ hχ₀ hχ).2.2 2 (by norm_num)).2.1 π
  have hCj := ((hpw (-s) χ₀⁻¹ χ⁻¹ hi₀ hi).2.2 2 (by norm_num)).2.2.2.1
  have hnorm : GlobalTheory.DiscSpec.IsNormalised (π.twist χ) :=
    (Dp.normIff M 2 _).2 ((Dp.exSummand M 2 μ _ V).1 hV).1
  have hnc : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ¬ (UpperTheory.CBC.Cusp.cx (π.twist χ)).ConjIso σ.toRingEquiv := fun σ h1 hc =>
    not_conjIso h2 π hm σ h1 (by simpa only [hback] using hCj _ _ hc)
  have hsb : SplitBad K (π.twist χ) := fun v hv => ⟨(hS v hv).1, fun w hw =>
    let ⟨_, hB⟩ := (hS v hv).2 w hw
    ⟨_, satTw hB (pow_val hχ w).1⟩⟩
  obtain ⟨P, hP, hI⟩ := hN K M h2 (π.twist χ) hnorm hnc hsb
  have hun : ∀ {w : HeightOneSpectrum (𝓞 M)} {B : Multiset ℂˣ}, (CG.mk (π.twist χ)).HasSat w B →
      (CG.mk π).HasSat w (B.map (· * χ⁻¹.val w)) := fun {w B} h => by
    have h1 := satTw h (pow_val hi w).1
    rwa [hback] at h1
  have hv : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f →
      χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) ^ f := fun w f hf => by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hi _).2, (pow_val hi₀ _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨P.twist χ₀⁻¹, hP.mono fun w hw => ⟨fun w' hne e => ?_, fun hq2 => ?_⟩, fun τ τ' m m' hne hc k1 k2 => ?_⟩
  · obtain ⟨B, B', k1, k2, k3⟩ := hw.1 w' hne e
    have e1 : χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) :=
      (hv w 1 ((norm_split h2 hne e).trans (pow_one _).symm)).trans (pow_one _)
    have e2 : χ⁻¹.val w' = χ₀⁻¹.val (w.under (𝓞 K)) := by
      rw [← e]
      exact (hv w' 1 ((norm_split h2 hne.symm e.symm).trans (by rw [e, pow_one]))).trans (pow_one _)
    refine ⟨_, _, hun k1, hun k2, ?_⟩
    rw [e1, e2, ← Multiset.map_add]
    exact satTw k3 (pow_val hi₀ _).1
  · obtain ⟨_, B', k1, rfl, k3⟩ := hw.2 hq2
    refine ⟨_, B'.map (· * χ₀⁻¹.val (w.under (𝓞 K))), ?_, ?_, satTw k3 (pow_val hi₀ _).1⟩
    · have k4 := hun k1
      rw [hv w 2 hq2] at k4
      simpa only [Multiset.map_map, Function.comp_def, mul_pow] using k4
    · simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, neg_mul]
  · have k := (hI τ τ' _ _ hne hc (k1.twist χ) (k2.twist χ)).twist χ₀⁻¹
    rw [pow_expo hχ, pow_expo hχ, pow_expo hi₀, ← Multiset.map_add, Multiset.map_map] at k
    simpa using k

end Main
