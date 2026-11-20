import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_int (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

/- English proof (translation)
Establish `h1 : a ∈ (algebraMap (𝓞 F) F).range`. Use `HeightOneSpectrum.mem_integers_of_valuation_le_one F a fun v => ?_` and prove the remaining obligations. Establish `h2 : Valued.v ((a : F) : v.adicCompletion F) ≤ 1` using `h v`. Rewrite `h2` using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Then use the resulting hypothesis. Take `⟨b, rfl⟩` from `h1`.

Establish `h3 : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F b))` using `Algebra.isIntegral_trace b.2`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h3`. Conclude with `⟨n, hn.symm⟩`.
-/
theorem trace_int {a : F} (h : algebraMap F (Af F) a ∈ intAf F) : ∃ n : ℤ, Algebra.trace ℚ F a = n := by
  have h1 : a ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F a fun v => ?_
    have h2 : Valued.v ((a : F) : v.adicCompletion F) ≤ 1 := h v
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  obtain ⟨b, rfl⟩ := h1
  have h3 : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F b)) := Algebra.isIntegral_trace b.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  exact ⟨n, hn.symm⟩

/- English proof (translation)
Introduce `v` and use `by rw [map_sub]; exact sub_mem (ha v) (hb v)`.
-/
theorem int_sub {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a - b ∈ intAf F := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v` and use `by rw [map_add]; exact add_mem (ha v) (hb v)`.
-/
theorem int_add {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a + b ∈ intAf F := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v` and use `by rw [map_zero]; exact zero_mem _`.
-/
theorem int_zero : (0 : Af F) ∈ intAf F := fun v => by
  rw [map_zero]; exact zero_mem _

/- English proof (translation)
Establish `hap : ∀ y : Af F, ∃ a : F, y - algebraMap F (Af F) a ∈ intAf F` using `fun y => by`. Take `⟨a, β, hβ, h⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 y`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[h, one_smul, add_sub_cancel_left]`. Conclude with `hβ`.

Use `choose ap hap using hap`. Set `c : ℂ` to `2 * Real.pi * Complex.I`. Set `f : AF F → ℂ` to `fun x => Complex.exp (c * (((Algebra.trace ℚ F (ap x.2) : ℚ) : ℂ) - t x.1))`. Establish `key : ∀ (x : AF F) (a : F), x.2 - algebraMap F (Af F) a ∈ intAf F → f x = Complex.exp (c * (((Algebra.trace ℚ F a : ℚ) : ℂ) - t x.1))`. Introduce `x a h`.

Establish `h1 : algebraMap F (Af F) (ap x.2 - a) ∈ intAf F`. Use `int_sub h (hap x.2)` as an intermediate fact. Rewrite using `[map_sub]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨n, hn⟩` from `trace_int h1`. Rewrite `hn` using `[map_sub, sub_eq_iff_eq_add]`. Use `show Complex.exp _ = _`. Rewrite using `[hn, Complex.exp_eq_exp_iff_exists_int]`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `f0 : ∀ x : AF F, x.2 ∈ intAf F → f x = Complex.exp (-(c * t x.1))` using `fun x hx => by`. Rewrite using `[key x 0 (by rwa [map_zero, sub_zero])]`. Simplify using the standard rewrite rules.

Establish `fadd : ∀ x y, f (x + y) = f x * f y` using `fun x y => by`. Rewrite using `[key (x + y) (ap x.2 + ap y.2) (by`. Use `int_add (hap x.2) (hap y.2)` as an intermediate fact. Rewrite using `[map_add]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `show x.2 + y.2 - _ = _`. Use the proof step `ring), ← Complex.exp_add]`. Use `congr 1`. Rewrite using `[map_add, show (x + y).1 = x.1 + y.1 from rfl, map_add]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Set `ψ : AddChar (AF F) ℂ` to `{ toFun := f map_zero_eq_one' := by`. Rewrite using `[f0 0 int_zero, show (0 : AF F).1 = 0 from rfl, map_zero]`. Simplify using the standard rewrite rules. Use the proof step `map_add_eq_mul' := fadd }`.

Establish `hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x)` using `fun x => by show f (x, 0) = _`. Rewrite using `[f0 (x, 0) int_zero]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨ψ, ⟨?_, fun x => ?_, fun a => ?_, ?_⟩, hinf⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`. Establish `hU : {x : AF F | x.2 - x₀.2 ∈ intAf F} ∈ nhds x₀` using `((isOpen_int F).preimage (continuous_snd.sub continuous_const)).mem_nhds (by show x₀.2 - x₀.2 ∈ intAf F`. Rewrite using `[sub_self]`.

Conclude with `int_zero)`. Establish `hg : Continuous fun x : AF F => f x₀ * Complex.exp (-(c * t (x.1 - x₀.1)))` using `continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (hc.comp (continuous_fst.sub continuous_const))).neg)`. Use `hg.continuousAt.congr (Filter.eventually_of_mem hU fun x hx => ?_)` and prove the remaining obligations. Use `show _ = f x`. Rewrite using `[← add_sub_cancel x₀ x, fadd, f0 (x - x₀) hx, add_sub_cancel]`.

Both sides reduce to the same expression. Use `show ‖Complex.exp _‖ = 1`. Rewrite using `[Complex.norm_exp]`. Simplify using `[c, hre]`. Use `show f _ = 1`.

Rewrite using `[key _ a (by show algebraMap F (Af F) a - _ ∈ _`. Rewrite using `[sub_self]`. Conclude with `int_zero)]`. Use `show Complex.exp (c * (_ - t (algebraMap F (Ainf F) a))) = 1`. Rewrite using `[ht, sub_self, mul_zero, Complex.exp_zero]`.

Establish `hn : (Module.finrank ℚ F : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Use `⟨pairA F (algebraMap F (Ainf F) (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))) 0, ?_⟩` and prove the remaining obligations. Use `show psiInf F ψ _ ≠ 1`. Rewrite using `[hinf, ht, Algebra.trace_algebraMap, nsmul_eq_mul, show (Module.finrank ℚ F : ℚ) * (1 / (2 * Module.finrank ℚ F)) = 1 / 2 by field_simp, show 2 * (Real.pi : ℂ) * Complex.I * (((-1 : ℤ)) : ℂ) * ((1 / 2 : ℚ) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring, Complex.exp_neg, Complex …`. Evaluate the numerical expressions.
-/
theorem exists_char (t : Ainf F →+ ℂ) (hc : Continuous t) (hre : ∀ x, (t x).im = 0)
    (ht : ∀ a : F, t (algebraMap F (Ainf F) a) = ((Algebra.trace ℚ F a : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := by
  have hap : ∀ y : Af F, ∃ a : F, y - algebraMap F (Af F) a ∈ intAf F := fun y => by
    obtain ⟨a, β, hβ, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 y
    refine ⟨a, ?_⟩
    rw [h, one_smul, add_sub_cancel_left]
    exact hβ
  choose ap hap using hap
  let c : ℂ := 2 * Real.pi * Complex.I
  let f : AF F → ℂ := fun x => Complex.exp (c * (((Algebra.trace ℚ F (ap x.2) : ℚ) : ℂ) - t x.1))
  have key : ∀ (x : AF F) (a : F), x.2 - algebraMap F (Af F) a ∈ intAf F →
      f x = Complex.exp (c * (((Algebra.trace ℚ F a : ℚ) : ℂ) - t x.1)) := by
    intro x a h
    have h1 : algebraMap F (Af F) (ap x.2 - a) ∈ intAf F := by
      have := int_sub h (hap x.2)
      rw [map_sub]
      convert this using 1
      ring
    obtain ⟨n, hn⟩ := trace_int h1
    rw [map_sub, sub_eq_iff_eq_add] at hn
    show Complex.exp _ = _
    rw [hn, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    push_cast
    ring
  have f0 : ∀ x : AF F, x.2 ∈ intAf F → f x = Complex.exp (-(c * t x.1)) := fun x hx => by
    rw [key x 0 (by rwa [map_zero, sub_zero])]
    simp
  have fadd : ∀ x y, f (x + y) = f x * f y := fun x y => by
    rw [key (x + y) (ap x.2 + ap y.2) (by
      have := int_add (hap x.2) (hap y.2)
      rw [map_add]
      convert this using 1
      show x.2 + y.2 - _ = _
      ring), ← Complex.exp_add]
    congr 1
    rw [map_add, show (x + y).1 = x.1 + y.1 from rfl, map_add]
    push_cast
    ring
  let ψ : AddChar (AF F) ℂ :=
    { toFun := f
      map_zero_eq_one' := by
        rw [f0 0 int_zero, show (0 : AF F).1 = 0 from rfl, map_zero]; simp
      map_add_eq_mul' := fadd }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := fun x => by
    show f (x, 0) = _
    rw [f0 (x, 0) int_zero]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, fun x => ?_, fun a => ?_, ?_⟩, hinf⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    have hU : {x : AF F | x.2 - x₀.2 ∈ intAf F} ∈ nhds x₀ :=
      ((isOpen_int F).preimage (continuous_snd.sub continuous_const)).mem_nhds (by
        show x₀.2 - x₀.2 ∈ intAf F
        rw [sub_self]; exact int_zero)
    have hg : Continuous fun x : AF F => f x₀ * Complex.exp (-(c * t (x.1 - x₀.1))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (hc.comp (continuous_fst.sub continuous_const))).neg)
    refine hg.continuousAt.congr (Filter.eventually_of_mem hU fun x hx => ?_)
    show _ = f x
    rw [← add_sub_cancel x₀ x, fadd, f0 (x - x₀) hx, add_sub_cancel]
    rfl
  · show ‖Complex.exp _‖ = 1
    rw [Complex.norm_exp]
    simp [c, hre]
  · show f _ = 1
    rw [key _ a (by
      show algebraMap F (Af F) a - _ ∈ _
      rw [sub_self]; exact int_zero)]
    show Complex.exp (c * (_ - t (algebraMap F (Ainf F) a))) = 1
    rw [ht, sub_self, mul_zero, Complex.exp_zero]
  · have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F (Ainf F) (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))) 0, ?_⟩
    show psiInf F ψ _ ≠ 1
    rw [hinf, ht, Algebra.trace_algebraMap, nsmul_eq_mul,
      show (Module.finrank ℚ F : ℚ) * (1 / (2 * Module.finrank ℚ F)) = 1 / 2 by field_simp,
      show 2 * (Real.pi : ℂ) * Complex.I * (((-1 : ℤ)) : ℂ) * ((1 / 2 : ℚ) : ℂ) = -(Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

end Char

/- English proof (translation)
Take `⟨θ, hθ⟩` from `GlobalTheory.DualPairCompare.exists_infFam D`. Set `t : Ainf D.host.F →+ ℂ` to `AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun x y => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]`. Establish `hts : ∀ x, t x = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ)` using `GlobalTheory.DualPairCompare.sum_infFam θ hθ`. Take `⟨ψ, h1, h2⟩` from `exists_char t (continuous_finset_sum _ fun ρ _ => (hθ ρ).2) (fun x => by rw [hts, Complex.ofReal_im]) (fun a => by show ∑ ρ, θ ρ _ = _`. Rewrite using `[GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])`.

Conclude with `⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => by rw [h2, hts, GlobalTheory.DualPairCompare.sum_infFam θ' hθ']⟩`.
-/
theorem exists_stdChar (D : D7) : ∃ ψ, IsStdChar D ψ (-1) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let t : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)))
    fun x y => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]
  have hts : ∀ x, t x = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ) := GlobalTheory.DualPairCompare.sum_infFam θ hθ
  obtain ⟨ψ, h1, h2⟩ := exists_char t (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
    (fun x => by rw [hts, Complex.ofReal_im]) (fun a => by
      show ∑ ρ, θ ρ _ = _
      rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
  exact ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => by rw [h2, hts, GlobalTheory.DualPairCompare.sum_infFam θ' hθ']⟩

section Lattice

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable (D : D7)

def latA (r : ℕ) : Lt D.host.E r := Submodule.pi Set.univ fun _ => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h a => h a trivial, fun h a _ => h a⟩`.
-/
theorem mem_latA {r : ℕ} {x : Fin r → D.host.E} : x ∈ latA D r ↔ ∀ a, x a ∈ D.host.AA :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

/- English proof (translation)
The claim follows from `FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))`.
-/
theorem AA_fg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
  FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))

/- English proof (translation)
Rewrite using `[mem_latA]`. Introduce `a`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality. Simplify using `using hb`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`.
-/
theorem single_mem {r : ℕ} (i : Fin r) {b : D.host.E} (hb : b ∈ D.host.AA) : Pi.single i b ∈ latA D r := by
  rw [mem_latA]
  intro a
  by_cases h : a = i
  · subst h; simpa using hb
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

/- English proof (translation)
Take `⟨b, hb0, hb⟩` from `exists_ne_zero_mem_isInteger (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)`. Establish `hb1 : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0` using `fun h => hb0 (IsFractionRing.injective (𝓞 D.host.E) D.host.E (h.trans (map_zero _).symm))`. Rewrite using `[eq_top_iff, ← (Pi.basisFun D.host.E (Fin r)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: Pi.basisFun D.host.E (Fin r) i = (algebraMap (𝓞 D.host.E) D.host.E b)⁻¹ • (Pi.single i (algebraMap (𝓞 D.host.E) D.host.E b) : Fin r → D.host.E)`.

Rewrite using `[Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hb1]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (single_mem D i hb))`.
-/
theorem latA_span (r : ℕ) : Submodule.span D.host.E (latA D r : Set (Fin r → D.host.E)) = ⊤ := by
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_mem_isInteger (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  have hb1 : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := fun h => hb0 (IsFractionRing.injective (𝓞 D.host.E) D.host.E (h.trans (map_zero _).symm))
  rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin r)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : Pi.basisFun D.host.E (Fin r) i =
      (algebraMap (𝓞 D.host.E) D.host.E b)⁻¹ • (Pi.single i (algebraMap (𝓞 D.host.E) D.host.E b) : Fin r → D.host.E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hb1]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem D i hb))

/- English proof (translation)
Take `⟨s, hs⟩` from `AA_fg D`. Take `⟨k, hk, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨k.natAbs, Int.natAbs_pos.2 hk, fun a ha => ?_⟩` and prove the remaining obligations. Establish `ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E)` using `by rw [hs]; exact ha`. Establish `: IsIntegral ℤ ((k : D.host.E) * a)` using `by clear ha`.

Proceed by induction on `ha' using Submodule.span_induction with`. Consider the case `mem x hx => simpa using h x hx`. Consider the case `zero => rw [mul_zero]`. Conclude with `isIntegral_zero`. Consider the case `add x y _ _ hx hy => rw [mul_add]`.

Conclude with `hx.add hy`. Consider the case `smul c x _ hx => rw [Algebra.smul_def, mul_left_comm]`. Conclude with `IsIntegral.mul c.2 hx`. Break down `Int.natAbs_eq k with h | h` into its components or cases. Rewrite `this` using `[h]`.

Simplify `this` using `only [Int.cast_natCast]`. Rewrite `this` using `[h]`. Simplify `this.neg` using `only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]`.
-/
theorem exists_den : ∃ n : ℕ, 0 < n ∧ ∀ a ∈ D.host.AA, IsIntegral ℤ ((n : D.host.E) * a) := by
  obtain ⟨s, hs⟩ := AA_fg D
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, fun a ha => ?_⟩
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := by rw [hs]; exact ha
  have : IsIntegral ℤ ((k : D.host.E) * a) := by
    clear ha
    induction ha' using Submodule.span_induction with
    | mem x hx => simpa using h x hx
    | zero => rw [mul_zero]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
    | smul c x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact IsIntegral.mul c.2 hx
  rcases Int.natAbs_eq k with h | h
  · rw [h] at this
    simpa only [Int.cast_natCast] using this
  · rw [h] at this
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] using this.neg

/- English proof (translation)
Unfold `herm`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb.symm]; simp) (by simp), Matrix.diagonal_apply_eq]`.
-/
theorem herm_diag {r : ℕ} (ε : Fin r → D.host.E) (x y : Fin r → D.host.E) :
    herm (Matrix.diagonal ε) x y = ∑ a, x a * ε a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb.symm]; simp) (by simp),
    Matrix.diagonal_apply_eq]

/- English proof (translation)
Establish `hP` using `Formalism.IndefR.Fin.factPrincipalDatum`. Establish `hE : ∀ x y, EF X x y = Algebra.trace ℚ D.host.E (D.host.xi0 * -∑ a, x a * Examples₂.sgn (neg a) * cc (y a))`. Introduce `x y`. Rewrite using `[EF_def, hG, herm_diag, hκ]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ (s : Bool) (b : D.host.E), b ∈ D.host.AA → Examples₂.sgn s * b ∈ D.host.AA`. Introduce `s b hb`. Consider the cases of `s`. Simplify `hb` using `[Examples₂.sgn]`.

Simplify `mem_coe.1 (neg_mem (mem_coe.2 hb))` using `[Examples₂.sgn]`. Use `⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite `hx`, `hy` using `[hΛ, mem_latA]`. Rewrite using `[hE]`. Use `trace_int_of_mem hP D (neg_mem (Submodule.sum_mem _ fun a _ => ?_))` and prove the remaining obligations.

Rewrite using `[mul_comm (x a), cc_eq_conj]`. Conclude with `mem_coe.2 (mul_mem_mul (hs _ _ (hx a)) (conj_mem_AAbar D (hy a)))`. Rewrite `h`, the goal using `[hΛ]`. Rewrite using `[mem_latA]`. Introduce `a`.

Establish `h1 : ∀ b ∈ D.host.AA, ∃ k : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (x a * cc b)) = k`. Introduce `b hb`. Take `⟨k, hk⟩` from `h _ (single_mem D a (hs (neg a) _ (mem_coe.1 (neg_mem (mem_coe.2 hb)))))`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, hE, Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc]; simp [cc]) (by simp), Pi.single_eq_same]`.

Use `congr 2`. Apply the tactic sequence `cases neg a <;> simp [Examples₂.sgn, cc]`. Use `mem_AA_of hP D fun b hb => int_of_xi hP D fun a' ha' j hj => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `int_of_AA_mul hP D ha' hb`. Rewrite using `[mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]`.

Introduce `u hu`. Take `⟨u, rfl⟩` from `(mem_one_iff _).1 hu`. Establish `hm : cc (algebraMap (𝓞 D.host.E) D.host.E (c * u)) * D.host.conj j ∈ D.host.AA` using `mem_coe.1 (Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (⟨_, int_cc D (c * u).2⟩ : 𝓞 D.host.E) (mem_coe.2 (conj_mem_AA D hj)))`. Take `⟨k, hk⟩` from `h1 _ hm`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite `hk` using `[cc_mul, cc_cc, cc_eq_conj, conj_conj, RingHom.map_mul, hc]`. Rewrite using `[Algebra.traceForm_apply, eq_intCast, ← hk]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem selfD {r : ℕ} (X : Data D.host.E r) (neg : Fin r → Bool)
    (hG : X.Gm = Matrix.diagonal fun a => Examples₂.sgn (neg a)) (hΛ : X.Λ = latA D r) (hκ : X.κ0 = 2 * D.host.xi0) :
    SelfD X X.Λ := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hE : ∀ x y, EF X x y = Algebra.trace ℚ D.host.E (D.host.xi0 * -∑ a, x a * Examples₂.sgn (neg a) * cc (y a)) := by
    intro x y
    rw [EF_def, hG, herm_diag, hκ]
    congr 1
    ring
  have hs : ∀ (s : Bool) (b : D.host.E), b ∈ D.host.AA → Examples₂.sgn s * b ∈ D.host.AA := by
    intro s b hb
    cases s
    · simpa [Examples₂.sgn] using hb
    · simpa [Examples₂.sgn] using mem_coe.1 (neg_mem (mem_coe.2 hb))
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · rw [hΛ, mem_latA] at hx hy
    rw [hE]
    refine trace_int_of_mem hP D (neg_mem (Submodule.sum_mem _ fun a _ => ?_))
    rw [mul_comm (x a), cc_eq_conj]
    exact mem_coe.2 (mul_mem_mul (hs _ _ (hx a)) (conj_mem_AAbar D (hy a)))
  · rw [hΛ] at h ⊢
    rw [mem_latA]
    intro a
    have h1 : ∀ b ∈ D.host.AA, ∃ k : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (x a * cc b)) = k := by
      intro b hb
      obtain ⟨k, hk⟩ := h _ (single_mem D a (hs (neg a) _ (mem_coe.1 (neg_mem (mem_coe.2 hb)))))
      refine ⟨k, ?_⟩
      rw [← hk, hE, Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc]; simp [cc]) (by simp),
        Pi.single_eq_same]
      congr 2
      cases neg a <;> simp [Examples₂.sgn, cc]
    refine mem_AA_of hP D fun b hb => int_of_xi hP D fun a' ha' j hj => ?_
    obtain ⟨c, hc⟩ := int_of_AA_mul hP D ha' hb
    rw [mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro u hu
    obtain ⟨u, rfl⟩ := (mem_one_iff _).1 hu
    have hm : cc (algebraMap (𝓞 D.host.E) D.host.E (c * u)) * D.host.conj j ∈ D.host.AA :=
      mem_coe.1 (Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, int_cc D (c * u).2⟩ : 𝓞 D.host.E) (mem_coe.2 (conj_mem_AA D hj)))
    obtain ⟨k, hk⟩ := h1 _ hm
    refine ⟨k, ?_⟩
    rw [cc_mul, cc_cc, cc_eq_conj, conj_conj, RingHom.map_mul, hc] at hk
    rw [Algebra.traceForm_apply, eq_intCast, ← hk]
    congr 1
    ring

end Lattice

/- English proof (translation)
Establish `h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ)` using `((factEmb D.R D.host).2 _).2 (D.eTau τ).2`. Establish `hd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)`. Establish `hN : 0 < (Ideal.absNorm D.host.ccK : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h))`. Establish `h2 : tauE D τ D.host.xi0 = Complex.I * ((1 / (Ideal.absNorm D.host.ccK * Real.sqrt D.host.d) : ℝ) : ℂ)`. Rewrite using `[Host.xi0, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]`.

Establish `: ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hd.ne'`. Establish `: ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Rewrite using `[h2, Complex.I_mul_im, Complex.ofReal_re]`. Check the signs of the components of the expression.
-/
theorem polarization_scalar_im_pos (D : D7) (τ : D.what₂.Tau) : 0 < (tauE D τ D.host.xi0).im := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  have hN : 0 < (Ideal.absNorm D.host.ccK : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have h2 : tauE D τ D.host.xi0 = Complex.I * ((1 / (Ideal.absNorm D.host.ccK * Real.sqrt D.host.d) : ℝ) : ℂ) := by
    rw [Host.xi0, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
    have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
    have : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
    simp
  rw [h2, Complex.I_mul_im, Complex.ofReal_re]
  positivity

def sp (D : D7) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace Examples₂.star_isIntegral (p + q) (fun a => decide (p ≤ (a : ℕ))) p q

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Conclude with `Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral (p + q) (fun a => decide (p ≤ (a : ℕ))) p q i j`.
-/
theorem sp_gram (D : D7) (p q : ℕ) :
    (sp D p q).gram = Matrix.diagonal fun a : Fin (p + q) => Examples₂.sgn (decide (p ≤ (a : ℕ))) := by
  funext i j
  exact Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral (p + q) (fun a => decide (p ≤ (a : ℕ))) p q i j

/- English proof (translation)
Establish `hP` using `Formalism.IndefR.Fin.factPrincipalDatum`. Take `⟨ψ, hψ⟩` from `exists_stdChar D`. Take `⟨θ, hθ⟩` from `GlobalTheory.DualPairCompare.exists_infFam D`. Establish `hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `fun σ => star_star σ`. Set `c : D.what₂.Tau → (D.host.E →+* ℂ)` to `fun τ => ComplexEmbedding.conjugate (tauE D τ)`.

Establish `hci : Function.Injective c` using `fun a b h => GlobalTheory.StdRat.tauE_injective D (by`. Use `congrArg ComplexEmbedding.conjugate h` as an intermediate fact. Rewrite using `[hc, hc] at this)` and apply the resulting hypothesis. Establish `hmem : ∀ σ, σ ∈ Finset.univ.image c ↔ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ` using `fun σ => by`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`.

Conclude with `exists_congr fun τ => ⟨fun h => by rw [← h, hc], fun h => by simp only [c]; rw [h, hc]⟩`. Establish `hsg : ∀ (σ : D.host.E →+* ℂ) (a : Fin (p + q)), σ (Examples₂.sgn (decide (p ≤ (a : ℕ)))) = ((FD.sgn p (a : ℕ) : ℝ) : ℂ)` using `fun σ a => by`. Unfold `Examples₂.sgn FD.sgn`. Distinguish the cases in `h : p ≤ (a : ℕ)`. Simplify using `[h, not_lt.2 h]`.

Simplify using `[h, not_le.1 h]`. Establish `hξ : cc D.host.xi0 = -D.host.xi0`. Choose the witnesses or unpack the hypotheses as in `⟨τ⟩ : Nonempty D.what₂.Tau := by`. Assume the negation of the conclusion as `h0`. Use `GlobalTheory.StdRat.tauE_cm D D.host.φ₀` as an intermediate fact.

Conclude with `(this.not.1 (fun ⟨τ, _⟩ => h0 ⟨τ⟩)) (fun ⟨τ, _⟩ => h0 ⟨τ⟩)`. Establish `h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ)` using `((factEmb D.R D.host).2 _).2 (D.eTau τ).2`. Establish `h2 : cc D.host.sqrtMinusD = -D.host.sqrtMinusD`. Apply `(tauE D τ).injective` to reduce the goal to its premises. Rewrite using `[cc, IsCMField.complexEmbedding_complexConj, map_neg, h1]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[cc]`. Rewrite using `[cc, Host.xi0, map_div₀, map_mul, h2, map_natCast, map_neg, map_one, mul_neg, div_neg]`. Take `⟨N, hN, hNi⟩` from `exists_den D`. Take `⟨k, hk, hki⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic D.host.xi0)).exists_integral_multiple`.

Establish `hk' : IsIntegral ℤ ((k.natAbs : D.host.E) * D.host.xi0)`. Rewrite `hki` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq k with h | h` into its components or cases. Rewrite `hki` using `[h]`. Simplify `hki` using `only [Int.cast_natCast]`.

Rewrite `hki` using `[h]`. Simplify `hki.neg` using `only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]`. Take `⟨X, hΨ, hG, hp, hΛ, -, hκ, -⟩` from `GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E (p + q) p 3 (3 * (k.natAbs * (N * N))) (Finset.univ.image c) (Matrix.diagonal fun a : Fin (p + q) => Examples₂.sgn (decide (p ≤ (a : ℕ)))) (latA D (p + q)) D.host.xi0 (2 * D.host.xi0) (fun σ => by rw [hmem, hmem …`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, cc]`. Conclude with `Examples₂.map_sgn (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) _`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), cc, map_zero])`. Use the proof step `(by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun a _ => Examples₂.sgn_ne_zero _)`. Use the proof step `(Nat.le_add_right p q)`.

Use the proof step `(fun σ _ => ⟨1, by simp, by`. Use extensionality with `a b`. Simplify using `only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using `[apply_ite, hsg]`. Simplify using `[apply_ite, h, Ne.symm h]⟩)`. Use the proof step `(Submodule.fg_pi fun _ => AA_fg D) (latA_span D _) le_rfl hξ (cmHost_imaginaryGenerator_ne_zero hP D) (Or.inl rfl)`. Use the proof step `(fun σ hσ => by`. Take `⟨τ, -, rfl⟩` from `Finset.mem_image.1 hσ`.

Use `polarization_scalar_im_pos D τ` as an intermediate fact. Simplify using `only [c, ComplexEmbedding.conjugate_coe_eq, map_mul, map_ofNat, Complex.mul_im, Complex.conj_im]`. Evaluate the numerical expressions. Conclude with `this)`. Use the proof step `(by have := Int.natAbs_pos.2 hk; positivity)`.

Use the proof step `(fun x hx y hy => by`. Rewrite `hx`, `hy` using `[mem_latA]`. Rewrite using `[herm_diag, Finset.mul_sum]`. Use `IsIntegral.sum _ fun a _ => ?_` and prove the remaining obligations. Establish `h2 : IsIntegral ℤ (2 : D.host.E)` using `by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2`.

Establish `h3 : IsIntegral ℤ (Examples₂.sgn (decide (p ≤ (a : ℕ))) : D.host.E)`. Unfold `Examples₂.sgn`. Use `split_ifs`. Conclude with `isIntegral_one.neg`. Conclude with `isIntegral_one`.

Establish `h4` using `PullbackSections.PfModelLatA.int_cc D (hNi _ (hy a))`. Use `((h2.mul hk').mul ((hNi _ (hx a)).mul h3)).mul h4` as an intermediate fact. Establish `e : ((3 * (k.natAbs * (N * N)) : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (2 * D.host.xi0) * (x a * Examples₂.sgn (decide (p ≤ (a : ℕ))) * cc (y a)) = 2 * ((k.natAbs : D.host.E) * D.host.xi0) * ((N : D.host.E) * x a * Examples₂.sgn (decide (p ≤ (a : ℕ)))) * cc ((N : D.host.E) * y …`. Rewrite using `[Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by norm_num)), PullbackSections.PfModelLatA.cc_mul, show cc (N : D.host.E) = N from map_natCast _ _, Nat.cast_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `this)`. Take `⟨g, bas, idx, hb⟩` from `GlobalTheory.Ker.exists_symplectic_basis_of_selfD _ _ X (selfD D X _ hG hΛ hκ)`. Set `e : D.what₂.Tau ≃ X.Ψ` to `Equiv.ofBijective (fun τ => ⟨c τ, hΨ ▸ Finset.mem_image_of_mem c (Finset.mem_univ τ)⟩) ⟨fun a b h => hci (congrArg Subtype.val h), fun σ => by`. Take `⟨τ, -, h⟩` from `Finset.mem_image.1 (hΨ ▸ σ.2 : σ.1 ∈ Finset.univ.image c)`.

Conclude with `⟨τ, Subtype.ext h⟩⟩`. Set `m : Match (sp D n 0) (sp D p q) X` to `{ gS := by`. Use `(sp_gram D n 0).trans ?_` and prove the remaining obligations. Use `show _ = (1 : Matrix (Fin (n + 0)) (Fin (n + 0)) D.host.E)`. Rewrite using `[← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `: ¬ n ≤ (i : ℕ)` using `not_le.2 i.2`. Simplify using `[Examples₂.sgn, this]`. Use `gT := by rw [sp_gram, hG]; exact (Matrix.diagonal_transpose _).symm`.

Use `e := e`. Use `e_emb := fun _ => rfl`. Use `ka := hκ }`. Use `⟨⟨ψ, hψ, θ, hθ, X, m, g, q, by rw [hp]; rfl, bas, idx, hb, hn⟩, hp, rfl, hΛ, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, gramAt, sp_gram]`.

Use `show (Matrix.diagonal fun a : Fin (p + q) => Examples₂.sgn (decide (p ≤ (a : ℕ)))).map (tauE D τ) = sgnM X`. Rewrite using `[sgnM, hp]`. Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Rewrite using `[Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hsg]`. Rewrite using `[Matrix.map_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]`.
-/
theorem exists_ctx (D : D7) (n p q : ℕ) (hn : Even n) :
    ∃ C : Ctx (sp D n 0) (sp D p q), C.X.p0 = p ∧ C.q0 = q ∧ C.X.Λ = latA D (p + q) ∧ C.IsB fun _ => 1 := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  obtain ⟨ψ, hψ⟩ := exists_stdChar D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  let c : D.what₂.Tau → (D.host.E →+* ℂ) := fun τ => ComplexEmbedding.conjugate (tauE D τ)
  have hci : Function.Injective c := fun a b h => GlobalTheory.StdRat.tauE_injective D (by
    have := congrArg ComplexEmbedding.conjugate h
    rwa [hc, hc] at this)
  have hmem : ∀ σ, σ ∈ Finset.univ.image c ↔ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := fun σ => by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_congr fun τ => ⟨fun h => by rw [← h, hc], fun h => by simp only [c]; rw [h, hc]⟩
  have hsg : ∀ (σ : D.host.E →+* ℂ) (a : Fin (p + q)),
      σ (Examples₂.sgn (decide (p ≤ (a : ℕ)))) = ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := fun σ a => by
    unfold Examples₂.sgn FD.sgn
    by_cases h : p ≤ (a : ℕ)
    · simp [h, not_lt.2 h]
    · simp [h, not_le.1 h]
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
      by_contra h0
      have := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
      exact (this.not.1 (fun ⟨τ, _⟩ => h0 ⟨τ⟩)) (fun ⟨τ, _⟩ => h0 ⟨τ⟩)
    have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
      ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
    have h2 : cc D.host.sqrtMinusD = -D.host.sqrtMinusD := by
      apply (tauE D τ).injective
      rw [cc, IsCMField.complexEmbedding_complexConj, map_neg, h1]
      simp
    rw [cc] at h2
    rw [cc, Host.xi0, map_div₀, map_mul, h2, map_natCast, map_neg, map_one, mul_neg, div_neg]
  obtain ⟨N, hN, hNi⟩ := exists_den D
  obtain ⟨k, hk, hki⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
    (Algebra.IsAlgebraic.isAlgebraic D.host.xi0)).exists_integral_multiple
  have hk' : IsIntegral ℤ ((k.natAbs : D.host.E) * D.host.xi0) := by
    rw [zsmul_eq_mul] at hki
    rcases Int.natAbs_eq k with h | h
    · rw [h] at hki
      simpa only [Int.cast_natCast] using hki
    · rw [h] at hki
      simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] using hki.neg
  obtain ⟨X, hΨ, hG, hp, hΛ, -, hκ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E (p + q) p 3
    (3 * (k.natAbs * (N * N))) (Finset.univ.image c)
    (Matrix.diagonal fun a : Fin (p + q) => Examples₂.sgn (decide (p ≤ (a : ℕ)))) (latA D (p + q))
    D.host.xi0 (2 * D.host.xi0)
    (fun σ => by rw [hmem, hmem, hc, GlobalTheory.StdRat.tauE_cm D σ, not_not])
    (fun a b => by
      by_cases h : a = b
      · subst h
        rw [Matrix.diagonal_apply_eq, cc]
        exact Examples₂.map_sgn (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) _
      · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), cc, map_zero])
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun a _ => Examples₂.sgn_ne_zero _)
    (Nat.le_add_right p q)
    (fun σ _ => ⟨1, by simp, by
      ext a b
      simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : a = b
      · subst h
        simp [apply_ite, hsg]
      · simp [apply_ite, h, Ne.symm h]⟩)
    (Submodule.fg_pi fun _ => AA_fg D) (latA_span D _) le_rfl hξ (cmHost_imaginaryGenerator_ne_zero hP D) (Or.inl rfl)
    (fun σ hσ => by
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hσ
      have := polarization_scalar_im_pos D τ
      simp only [c, ComplexEmbedding.conjugate_coe_eq, map_mul, map_ofNat, Complex.mul_im, Complex.conj_im]
      norm_num
      exact this)
    (by have := Int.natAbs_pos.2 hk; positivity)
    (fun x hx y hy => by
      rw [mem_latA] at hx hy
      rw [herm_diag, Finset.mul_sum]
      refine IsIntegral.sum _ fun a _ => ?_
      have h2 : IsIntegral ℤ (2 : D.host.E) := by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2
      have h3 : IsIntegral ℤ (Examples₂.sgn (decide (p ≤ (a : ℕ))) : D.host.E) := by
        unfold Examples₂.sgn; split_ifs
        · exact isIntegral_one.neg
        · exact isIntegral_one
      have h4 := PullbackSections.PfModelLatA.int_cc D (hNi _ (hy a))
      have := ((h2.mul hk').mul ((hNi _ (hx a)).mul h3)).mul h4
      have e : ((3 * (k.natAbs * (N * N)) : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (2 * D.host.xi0) *
          (x a * Examples₂.sgn (decide (p ≤ (a : ℕ))) * cc (y a)) =
          2 * ((k.natAbs : D.host.E) * D.host.xi0) * ((N : D.host.E) * x a * Examples₂.sgn (decide (p ≤ (a : ℕ)))) *
            cc ((N : D.host.E) * y a) := by
        rw [Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by norm_num)), PullbackSections.PfModelLatA.cc_mul,
          show cc (N : D.host.E) = N from map_natCast _ _, Nat.cast_mul, Nat.cast_mul]
        ring
      rw [e]
      exact this)
  obtain ⟨g, bas, idx, hb⟩ := GlobalTheory.Ker.exists_symplectic_basis_of_selfD _ _ X (selfD D X _ hG hΛ hκ)
  let e : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun τ => ⟨c τ, hΨ ▸ Finset.mem_image_of_mem c (Finset.mem_univ τ)⟩)
    ⟨fun a b h => hci (congrArg Subtype.val h), fun σ => by
      obtain ⟨τ, -, h⟩ := Finset.mem_image.1 (hΨ ▸ σ.2 : σ.1 ∈ Finset.univ.image c)
      exact ⟨τ, Subtype.ext h⟩⟩
  let m : Match (sp D n 0) (sp D p q) X :=
    { gS := by
        refine (sp_gram D n 0).trans ?_
        show _ = (1 : Matrix (Fin (n + 0)) (Fin (n + 0)) D.host.E)
        rw [← Matrix.diagonal_one]
        congr 1
        funext i
        have : ¬ n ≤ (i : ℕ) := not_le.2 i.2
        simp [Examples₂.sgn, this]
      gT := by rw [sp_gram, hG]; exact (Matrix.diagonal_transpose _).symm
      e := e
      e_emb := fun _ => rfl
      ka := hκ }
  refine ⟨⟨ψ, hψ, θ, hθ, X, m, g, q, by rw [hp]; rfl, bas, idx, hb, hn⟩, hp, rfl, hΛ, fun τ => ?_⟩
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, gramAt, sp_gram]
  show (Matrix.diagonal fun a : Fin (p + q) => Examples₂.sgn (decide (p ≤ (a : ℕ)))).map (tauE D τ) = sgnM X
  rw [sgnM, hp]
  ext a b
  by_cases h : a = b
  · subst h
    rw [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hsg]
  · rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

variable {D : D7} {S T : HSp D} (C : Ctx S T)

/- English proof (translation)
Use function extensionality and compare the values at `σ k a`. Take `⟨τ, rfl⟩` from `C.m.e.surjective σ`. Use `show conj (C.θ (C.m.e.symm (C.m.e τ)) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a)) = (C.m.e τ).1 (y k a)`. Rewrite using `[Equiv.symm_apply_apply, (C.inf τ).1, C.m.e_emb]`. Both sides reduce to the same expression.
-/
theorem realPt_rat (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ) = embR C.X y := by
  funext σ k a
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  show conj (C.θ (C.m.e.symm (C.m.e τ)) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a)) = (C.m.e τ).1 (y k a)
  rw [Equiv.symm_apply_apply, (C.inf τ).1, C.m.e_emb]
  rfl

/- English proof (translation)
Introduce `σ`. Take `⟨τ, rfl⟩` from `C.m.e.surjective σ`. Rewrite using `[← h τ]`. Use extensionality with `a b`. Simplify using `only [FD.gram, hermC, FD.col, mat, Ctx.xB, Matrix.of_apply, Equiv.symm_apply_apply, C.m.gT, C.m.e_emb, Matrix.mul_apply, Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Matrix.transpose_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Establish `: conj (tauE D τ (T.gram c d)) = tauE D τ (T.gram d c)`. Rewrite using `[← IsCMField.complexEmbedding_complexConj]`. Conclude with `congrArg _ (GlobalTheory.LatVac.gram_star T c d)`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem isONFr_xB (B : C.Bas) (h : C.IsB B) : IsONFr C.X (C.xB B) := by
  intro σ
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  rw [← h τ]
  ext a b
  simp only [FD.gram, hermC, FD.col, mat, Ctx.xB, Matrix.of_apply, Equiv.symm_apply_apply, C.m.gT, C.m.e_emb,
    Matrix.mul_apply, Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Matrix.transpose_apply,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have : conj (tauE D τ (T.gram c d)) = tauE D τ (T.gram d c) := by
    rw [← IsCMField.complexEmbedding_complexConj]
    exact congrArg _ (GlobalTheory.LatVac.gram_star T c d)
  rw [this]
  rfl

/- English proof (translation)
Simplify using `only [EF_def, C.m.ka, C.m.gT]`. Rewrite using `[← map_sum, ← map_neg, ← Finset.mul_sum, ← neg_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Unfold `GlobalTheory.LatVac.hRat herm`.

Rewrite using `[C.m.gS, inv_one]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply_eq]`.

Use `show x k d * T.gram c d * cc (y k c) = 1 * cc (y k c) * T.gram c d * x k d`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EF_eq (x y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    ∑ k, EF C.X (x k) (y k) = -Algebra.trace ℚ D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T xᵀ yᵀ) := by
  simp only [EF_def, C.m.ka, C.m.gT]
  rw [← map_sum, ← map_neg, ← Finset.mul_sum, ← neg_mul]
  congr 2
  · ring
  · unfold GlobalTheory.LatVac.hRat herm
    rw [C.m.gS, inv_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.one_apply_eq]
    show x k d * T.gram c d * cc (y k c) = 1 * cc (y k c) * T.gram c d * x k d
    ring

end GlobalTheory.Ker.Model

end
