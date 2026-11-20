import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumThetaStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VSetup

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hcc : ∀ x : E, φ (cc x) = conj (φ x)` using `fun x => by`. Simplify using `[cc, IsCMField.complexEmbedding_complexConj]`. Establish `hrt : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq` as an intermediate fact.

Simplify using `using this`. Establish `htw : 2 * (H.w0 : E) = 1 + H.rt`. Use `congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Conclude with `this`.

Establish `hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Simplify using `using congrArg φ hrt`. Establish `hzc : conj (φ (H.rt : E)) = -φ (H.rt : E)` using `by set z := φ (H.rt : E)`. Establish `hz' : conj z ^ 2 = -(H.d : ℂ)`. Rewrite using `[← map_pow, hz]`.

Simplify using the standard rewrite rules. Establish `h1 : (conj z - z) * (conj z + z) = 0`. Take the linear combination `hz' - hz`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `him : z.im = 0`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre` using `congrArg Complex.re hz`.

Simplify using `[sq, him] at hre`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Take the linear combination `h`. Establish `hw : 2 * φ (H.w0 : E) = 1 + φ (H.rt : E)`.

Use `congrArg φ htw` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Conclude with `this`. Establish `hwc : 2 * conj (φ (H.w0 : E)) = 1 + conj (φ (H.rt : E))`. Use `congrArg conj hw` as an intermediate fact.

Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Conclude with `this`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_add, map_one, hcc]`. Take the linear combination `(hw + hwc + hzc) / 2`.
-/
theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hcc : ∀ x : E, φ (cc x) = conj (φ x) := fun x => by
    simp [cc, IsCMField.complexEmbedding_complexConj]
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
    simpa using this
  have htw : 2 * (H.w0 : E) = 1 + H.rt := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, map_ofNat] at this
    exact this
  have hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg φ hrt
  have hzc : conj (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz' : conj z ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hz]; simp
    have h1 : (conj z - z) * (conj z + z) = 0 := by
      linear_combination hz' - hz
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      have him : z.im = 0 := by
        have := congrArg Complex.im h
        simp at this
        linarith
      have hre := congrArg Complex.re hz
      simp [sq, him] at hre
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [mul_self_nonneg z.re]
    · linear_combination h
  have hw : 2 * φ (H.w0 : E) = 1 + φ (H.rt : E) := by
    have := congrArg φ htw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    exact this
  have hwc : 2 * conj (φ (H.w0 : E)) = 1 + conj (φ (H.rt : E)) := by
    have := congrArg conj hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    exact this
  apply φ.injective
  rw [map_add, map_one, hcc]
  linear_combination (hw + hwc + hzc) / 2

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hG hU hr a n hD k x hx`. Use `letI : Algebra c.F ℂ := σ.toAlgebra`. Establish `hn : Even n` using `by unfold Dom at hD; exact hD.2`. Establish `hrpq : r = Dw.p + Dw.q` using `by unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.1`. Establish `hXk : (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0`.

Unfold `Formalism.L2.PjFree.IsUnf at hU`. Conclude with `hU.2.1 k`. Take `⟨W⟩` from `nonempty_uw hU`. Take `⟨-, hSD, hMk, -⟩` from `GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hG hU hr W k`. Take `⟨Dc, hDe, -⟩` from `GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k) a W.e hG hrpq hXk.1 hXk.2 hSD hD`.

Establish `hper : ∀ y v j, pv (U.X k) Dc.idx y v j = perFr (U.X k) y v (relab c σ (W.e j).1) (W.e j).2`. Introduce `y v j`. Rewrite using `[← hDe]`. Conclude with `Dc.per_eq y v j`. Establish `hty : ∀ j, rowType (U.X k) (Dc.idx j) = relab c σ (W.e j).1`.

Introduce `j`. Rewrite using `[← hDe]`. Conclude with `Dc.ty_eq j`. Take `⟨A, hAm, θ, hAr, hM1⟩` from `GlobalTheory.T.analyticFibre_unitFrame_uniformisation E H Dw l Xo c σ r U hG hU hr W k Dc.bas Dc.idx Dc.sympl hper hty x hx`. Establish `hθ` using `GlobalTheory.T.framedPoint_generator_isThetaLevelOne E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A Dc.sympl x.2 hSD θ hAr`.

Establish `hw : (H.w0 : E) + cc (H.w0 : E) = 1` using `hostHalfRoot_add_conj_eq_one H`. Establish `hint : IsIntegral ℤ (H.w0 : E)` using `H.w0.isIntegral_coe`. Take `⟨v, hv⟩` from `(GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD 1 (stdL E n) (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.prod_levelOne_theta_eq_vacuum_theta E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD v hv x.1 x.2 θ hθ`. Establish `hg : W.g = fdeg E * r`.

Establish `hc` using `Fintype.card_congr Dc.idx`. Rewrite `hc` using `[Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi]`. Conclude with `hc`. Conclude with `⟨W, Dc, A, θ, v, κ, hDe, hg, hw, hSD, hMk, hAm, hAr, hθ, hM1, hv, hκ⟩`.
-/
theorem exists_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU hr a n hD k x hx
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := by unfold Dom at hD; exact hD.2
  have hrpq : r = Dw.p + Dw.q := by unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.1
  have hXk : (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0 := by
    unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.2.1 k
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hSD, hMk, -⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hG hU hr W k
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k) a W.e hG hrpq hXk.1 hXk.2 hSD hD
  have hper : ∀ y v j, pv (U.X k) Dc.idx y v j = perFr (U.X k) y v (relab c σ (W.e j).1) (W.e j).2 := by
    intro y v j; rw [← hDe]; exact Dc.per_eq y v j
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = relab c σ (W.e j).1 := by
    intro j; rw [← hDe]; exact Dc.ty_eq j
  obtain ⟨A, hAm, θ, hAr, hM1⟩ :=
    GlobalTheory.T.analyticFibre_unitFrame_uniformisation E H Dw l Xo c σ r U hG hU hr W k Dc.bas Dc.idx Dc.sympl hper hty x hx
  have hθ := GlobalTheory.T.framedPoint_generator_isThetaLevelOne E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A
    Dc.sympl x.2 hSD θ hAr
  have hw : (H.w0 : E) + cc (H.w0 : E) = 1 := hostHalfRoot_add_conj_eq_one H
  have hint : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD 1
    (stdL E n) (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.prod_levelOne_theta_eq_vacuum_theta E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD v hv x.1 x.2 θ hθ
  have hg : W.g = fdeg E * r := by
    have hc := Fintype.card_congr Dc.idx
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
      ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi] at hc
    exact hc
  exact ⟨W, Dc, A, θ, v, κ, hDe, hg, hw, hSD, hMk, hAm, hAr, hθ, hM1, hv, hκ⟩

end GlobalTheory.Dict.VSetup
