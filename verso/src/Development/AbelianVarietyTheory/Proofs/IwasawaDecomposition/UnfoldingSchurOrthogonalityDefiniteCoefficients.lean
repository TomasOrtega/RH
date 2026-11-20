import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetUnfoldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.SchurW

set_option maxHeartbeats 8000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hB t h h' a a'`. Use `haveI : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Use `haveI : BorelSpace (GA D D.sp.X') := ⟨rfl⟩`. Use `haveI : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram`. Establish `hμ` using `hB.models.νX t`.

Use `haveI := hμ.1.1`. Establish `hc` using `hB.models.cX`. Establish `hH` using `hB.models.HX t`. Set `J` to `(levEnv D.sp.X' R.βX (R.datXt t)).J`. Set `χ` to `(levEnv D.sp.X' R.βX (R.datXt t)).χ`.

Set `Ω : Subgroup (GA D D.sp.X')` to `(lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)).comap (finE D.sp.X')`. Establish `hK : ∀ g : GA D D.sp.X', g ∈ Ω ↔ (finHom D.sp.X').rangeRestrict g ∈ J` using `fun g => Iff.rfl`. Establish `hΩo : IsOpen (Ω : Set (GA D D.sp.X'))`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level D.sp.X' R.βX (R.datXt t)] with κ hκ`.

Conclude with `(hK κ).2 hκ.1`. Establish `hΩ1 : R.νX t (Ω : Set (GA D D.sp.X')) = 1` using `GlobalTheory.Mass.Levels.measure_comap_finE hμ.1`. Establish `hF : ∀ x, (R.HX t).e x ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ` using `fun x => by`. Use `LinearMap.mem_range_self (R.HX t).e x` as an intermediate fact. Rewrite `this` using `[hH.2.1]`.

Conclude with `this`. Establish `hinv : ∀ (u : GA D D.sp.X') v, R.cX.ρ u⁻¹ (R.cX.ρ u v) = v` using `fun u v => by`. Use `congrArg (fun T : Module.End ℂ R.cX.W => T v) (show R.cX.ρ u⁻¹ * R.cX.ρ u = 1 by rw [← map_mul, inv_mul_cancel, map_one])` as an intermediate fact. Conclude with `this`. Establish `hext : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ (γ : GA D D.sp.X'), γ ∈ GQ D.sp.X' → ∀ g, R.cX.ext f (γ * g) = R.cX.ext f g`.

Introduce `f hf γ hγ g`. Use `show R.cX.ρ (γ * g)⁻¹ (f ((finHom D.sp.X').rangeRestrict (γ * g))) = R.cX.ρ g⁻¹ (f ((finHom D.sp.X').rangeRestrict g))`. Use `hf ⟨γ, hγ⟩ ((finHom D.sp.X').rangeRestrict g) 1` as an intermediate fact. Simplify using `only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this`. Rewrite using `[map_mul]`.

Use `erw [this]`. Use `show R.cX.ρ (γ * g)⁻¹ (R.cX.ρ γ _) = _`. Rewrite using `[_root_.mul_inv_rev, map_mul]`. Conclude with `congrArg (R.cX.ρ g⁻¹) (hinv γ _)`. Use `choose y' hy'1 hy'2 using fun c => GlobalTheory.DefiniteMult.exists_fin_lift D.sp.X' ((R.B.R t).pres.y c)`.

Establish `hnorm : ∀ k : J, ‖((χ k : ℂˣ) : ℂ)‖ = 1` using `fun k => GlobalTheory.AdelicScalar.norm_levFn _ _ _`. Establish `hloc : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ c, ∀ k (hk : k ∈ Ω), R.cX.ext f (y' c * k) = ((χ ⟨_, (hK k).1 hk⟩ : ℂˣ) : ℂ) • R.cX.ρ k⁻¹ (f ((R.B.R t).pres.y c))`. Introduce `f hf c k hk`. Establish `e1 : (finHom D.sp.X').rangeRestrict (y' c * k) = (R.B.R t).pres.y c * (finHom D.sp.X').rangeRestrict k`. Rewrite using `[MonoidHom.map_mul, hy'2]`.

Establish `e2` using `GlobalTheory.DefiniteMult.adForms_level hf ((R.B.R t).pres.y c) ⟨_, (hK k).1 hk⟩`. Establish `e3 : R.cX.ρ (y' c * k)⁻¹ = R.cX.ρ k⁻¹`. Rewrite using `[_root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem (hy'1 c)), mul_one]`. Use `show R.cX.ρ (y' c * k)⁻¹ (f ((finHom D.sp.X').rangeRestrict (y' c * k))) = _`. Use `(congrArg (R.cX.ρ (y' c * k)⁻¹) ((congrArg f e1).trans e2)).trans ?_` and prove the remaining obligations.

Use `(map_smul _ _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg (_ • ·) (LinearMap.congr_fun e3 _)`. Set `φ : GA D D.sp.X' → ℂ` to `fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ`. Establish `hpt : ∀ c, ∀ k ∈ Ω, φ (y' c * k) = star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ * ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ`. Introduce `c k hk`.

Establish `key : ∀ z p q : ℂ, ‖z‖ = 1 → star (z * p) * (z * q) = star p * q`. Introduce `z p q hz`. Establish `e : star z * z = 1`. Rewrite using `[Complex.star_def, Complex.conj_mul', hz]`. Evaluate the numerical expressions.

Rewrite using `[star_mul']`. Take the linear combination `(star p * q) * e`. Establish `hz` using `hnorm ⟨_, (hK k).1 hk⟩`. Use `(congrArg₂ (fun u v : ℂ => star u * v) (congrArg (inner ℂ a) (hloc _ (hF h) c k hk)) (congrArg (inner ℂ a') (hloc _ (hF h') c k hk))).trans ?_` and prove the remaining obligations. Simplify using `only [inner_smul_right]`.

Conclude with `key _ _ _ hz`. Establish `hmeas : ∀ x y : R.cX.W, Measurable fun g => ⟪x, R.cX.ρ g y⟫_ℂ` using `fun x y => (continuous_const.inner (hc.2.2.1 y)).measurable`. Establish `hirr : ∀ U : Submodule ℂ R.cX.W, (∀ g ∈ Ω, U.map (R.cX.ρ g) ≤ U) → U = ⊥ ∨ U = ⊤`. Introduce `U hU`. Use `hc.2.2.2.2 U fun g => ?_` and prove the remaining obligations.

Take `⟨a0, ha0, k0, hk0, rfl⟩` from `(GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 g`. Rewrite using `[map_mul, hc.1 k0 hk0, mul_one]`. Use `hU a0 ((hK a0).2 ?_)` and prove the remaining obligations. Establish `e : (finHom D.sp.X').rangeRestrict a0 = 1` using `Subtype.ext ha0`. Conclude with `e ▸ J.one_mem`.

Establish `hS` using `fun c => GlobalTheory.T.schur_orthogonality_subgroup_measure_one (R.νX t) Ω hΩo.measurableSet hΩ1 R.cX.ρ hc.2.1 hmeas hirr a a' ((R.HX t).e h ((R.B.R t).pres.y c)) ((R.HX t).e h' ((R.B.R t).pres.y c))`. Establish `huniq : ∀ x : GA D D.sp.X', ∃! i, ∃ γ ∈ GQ D.sp.X', ∃ k ∈ Ω, x = γ * y' i * k`. Introduce `x`. Use `(existsUnique_congr fun i => ?_).1 ((R.B.R t).pres.reps ((finHom D.sp.X').rangeRestrict x))` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, k, e⟩`. Use `⟨γ, γ.2, (γ * y' i)⁻¹ * x, (hK _).2 ?_, by group⟩` and prove the remaining obligations. Establish `e' : (finHom D.sp.X').rangeRestrict ((γ * y' i)⁻¹ * x) = k`. Simplify using `only [map_mul, map_inv, hy'2, e]`. Express the relevant statement in the definitionally equal form `(Bridge.ratF D.sp.X' γ * _)⁻¹ * (Bridge.ratF D.sp.X' γ * _ * k) = _`.

Conclude with `inv_mul_cancel_left _ _`. Conclude with `cast (congrArg (· ∈ J) e').symm k.2`. Introduce and unpack `⟨γ, hγ, k, hk, rfl⟩`. Use `⟨⟨γ, hγ⟩, ⟨_, (hK k).1 hk⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, hy'2]`.

Both sides reduce to the same expression. Establish `hSet : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω} = Subtype.val '' (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c) : Set (GQ D.sp.X'))`. Introduce `c`. Use extensionality with `γ`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨⟨γ, h1⟩, ?_, rfl⟩` and prove the remaining obligations. Use `(hK _).1 h2` as an intermediate fact. Simplify using `only [map_mul, map_inv, hy'2] at this`.

Conclude with `this`. Introduce and unpack `⟨δ, h2, rfl⟩`. Use `⟨δ.2, (hK _).2 ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, hy'2]`. Conclude with `h2`.

Establish `hfinS : ∀ c, Finite (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c))` using `fun c => Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv`. Establish `hfin : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.Finite` using `fun c => by`. Rewrite using `[hSet]`. Use `haveI := hfinS c`. Conclude with `(Set.toFinite _).image _`.

Establish `hcard : ∀ c, ({γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.ncard : ℂ) = (Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)` using `fun c => by`. Establish `e` using `congrArg Set.ncard (hSet c)`. Rewrite `e` using `[Set.ncard_image_of_injective _ Subtype.val_injective]`. Conclude with `(congrArg (Nat.cast : ℕ → ℂ) e).trans (congrArg (Nat.cast : ℕ → ℂ) (Nat.card_coe_set_eq _).symm)`. Establish `hintc : ∀ c, IntegrableOn (fun k => φ (y' c * k)) Ω (R.νX t)` using `fun c => (hS c).1.congr_fun (fun k hk => (hpt c k hk).symm) hΩo.measurableSet`.

Establish `hIc : ∀ c, ∫ k in (Ω : Set (GA D D.sp.X')), φ (y' c * k) ∂(R.νX t) = ∫ k in (Ω : Set (GA D D.sp.X')), star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ * ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ ∂(R.νX t)` using `fun c => setIntegral_congr_fun hΩo.measurableSet fun k hk => hpt c k hk`. Establish `hfl : ∀ γ : GA D D.sp.X', γ ∈ GQ D.sp.X' → ∀ x : GA D D.sp.X', φ (γ * x) = φ x` using `fun γ hγ x => by show star ⟪a, R.cX.ext ((R.HX t).e h) (γ * x)⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') (γ * x)⟫_ℂ = star ⟪a, R.cX.ext ((R.HX t).e h) x⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') x⟫_ℂ`. Conclude with `congrArg₂ (fun u v => star ⟪a, u⟫_ℂ * ⟪a', v⟫_ℂ) (hext _ (hF h) γ hγ x) (hext _ (hF h') γ hγ x)`. Establish `U1` using `GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold (GA D D.sp.X') (R.νX t) (GQ D.sp.X') Ω (R.fdX t) hμ.2 hΩo _ y' huniq hfin φ hfl hintc`. Use `⟨U1.1, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, φ g ∂(R.νX t) = _`. Use `(congrArg (_ * ·) U1.2).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (⟪a', a⟫_ℂ * ·) (hH.2.2 h h').symm)` and prove the remaining obligations. Simplify using `only [Bridge.adInner, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `(congrArg₂ (fun (u v : ℂ) => (Module.finrank ℂ R.cX.W : ℂ) * (u⁻¹ * v)) (hcard c) (hIc c)).trans ?_` and prove the remaining obligations. Take the linear combination `((Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)⁻¹) * (hS c).2`.
-/
theorem schurW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB t h h' a a'
  haveI : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  haveI : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  have hμ := hB.models.νX t
  haveI := hμ.1.1
  have hc := hB.models.cX
  have hH := hB.models.HX t
  let J := (levEnv D.sp.X' R.βX (R.datXt t)).J
  let χ := (levEnv D.sp.X' R.βX (R.datXt t)).χ
  let Ω : Subgroup (GA D D.sp.X') := (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)).comap (finE D.sp.X')
  have hK : ∀ g : GA D D.sp.X', g ∈ Ω ↔ (finHom D.sp.X').rangeRestrict g ∈ J := fun g => Iff.rfl
  have hΩo : IsOpen (Ω : Set (GA D D.sp.X')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level D.sp.X' R.βX (R.datXt t)] with κ hκ
    exact (hK κ).2 hκ.1
  have hΩ1 : R.νX t (Ω : Set (GA D D.sp.X')) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hF : ∀ x, (R.HX t).e x ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ := fun x => by
    have := LinearMap.mem_range_self (R.HX t).e x
    rw [hH.2.1] at this
    exact this
  have hinv : ∀ (u : GA D D.sp.X') v, R.cX.ρ u⁻¹ (R.cX.ρ u v) = v := fun u v => by
    have := congrArg (fun T : Module.End ℂ R.cX.W => T v) (show R.cX.ρ u⁻¹ * R.cX.ρ u = 1 by rw [← map_mul, inv_mul_cancel, map_one])
    exact this
  have hext : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ (γ : GA D D.sp.X'), γ ∈ GQ D.sp.X' →
      ∀ g, R.cX.ext f (γ * g) = R.cX.ext f g := by
    intro f hf γ hγ g
    show R.cX.ρ (γ * g)⁻¹ (f ((finHom D.sp.X').rangeRestrict (γ * g))) = R.cX.ρ g⁻¹ (f ((finHom D.sp.X').rangeRestrict g))
    have := hf ⟨γ, hγ⟩ ((finHom D.sp.X').rangeRestrict g) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [map_mul]
    erw [this]
    show R.cX.ρ (γ * g)⁻¹ (R.cX.ρ γ _) = _
    rw [_root_.mul_inv_rev, map_mul]
    exact congrArg (R.cX.ρ g⁻¹) (hinv γ _)
  choose y' hy'1 hy'2 using fun c => GlobalTheory.DefiniteMult.exists_fin_lift D.sp.X' ((R.B.R t).pres.y c)
  have hnorm : ∀ k : J, ‖((χ k : ℂˣ) : ℂ)‖ = 1 := fun k => GlobalTheory.AdelicScalar.norm_levFn _ _ _
  have hloc : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ c, ∀ k (hk : k ∈ Ω),
      R.cX.ext f (y' c * k) = ((χ ⟨_, (hK k).1 hk⟩ : ℂˣ) : ℂ) • R.cX.ρ k⁻¹ (f ((R.B.R t).pres.y c)) := by
    intro f hf c k hk
    have e1 : (finHom D.sp.X').rangeRestrict (y' c * k) = (R.B.R t).pres.y c * (finHom D.sp.X').rangeRestrict k := by
      rw [MonoidHom.map_mul, hy'2]
    have e2 := GlobalTheory.DefiniteMult.adForms_level hf ((R.B.R t).pres.y c) ⟨_, (hK k).1 hk⟩
    have e3 : R.cX.ρ (y' c * k)⁻¹ = R.cX.ρ k⁻¹ := by
      rw [_root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem (hy'1 c)), mul_one]
    show R.cX.ρ (y' c * k)⁻¹ (f ((finHom D.sp.X').rangeRestrict (y' c * k))) = _
    refine (congrArg (R.cX.ρ (y' c * k)⁻¹) ((congrArg f e1).trans e2)).trans ?_
    refine (map_smul _ _ _).trans ?_
    exact congrArg (_ • ·) (LinearMap.congr_fun e3 _)
  let φ : GA D D.sp.X' → ℂ := fun g =>
    star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ
  have hpt : ∀ c, ∀ k ∈ Ω, φ (y' c * k) = star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
      ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ := by
    intro c k hk
    have key : ∀ z p q : ℂ, ‖z‖ = 1 → star (z * p) * (z * q) = star p * q := by
      intro z p q hz
      have e : star z * z = 1 := by
        rw [Complex.star_def, Complex.conj_mul', hz]; norm_num
      rw [star_mul']
      linear_combination (star p * q) * e
    have hz := hnorm ⟨_, (hK k).1 hk⟩
    refine (congrArg₂ (fun u v : ℂ => star u * v) (congrArg (inner ℂ a) (hloc _ (hF h) c k hk))
      (congrArg (inner ℂ a') (hloc _ (hF h') c k hk))).trans ?_
    simp only [inner_smul_right]
    exact key _ _ _ hz
  have hmeas : ∀ x y : R.cX.W, Measurable fun g => ⟪x, R.cX.ρ g y⟫_ℂ := fun x y =>
    (continuous_const.inner (hc.2.2.1 y)).measurable
  have hirr : ∀ U : Submodule ℂ R.cX.W, (∀ g ∈ Ω, U.map (R.cX.ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun g => ?_
    obtain ⟨a0, ha0, k0, hk0, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 g
    rw [map_mul, hc.1 k0 hk0, mul_one]
    refine hU a0 ((hK a0).2 ?_)
    have e : (finHom D.sp.X').rangeRestrict a0 = 1 := Subtype.ext ha0
    exact e ▸ J.one_mem
  have hS := fun c => GlobalTheory.T.schur_orthogonality_subgroup_measure_one (R.νX t) Ω hΩo.measurableSet hΩ1 R.cX.ρ hc.2.1 hmeas hirr a a'
    ((R.HX t).e h ((R.B.R t).pres.y c)) ((R.HX t).e h' ((R.B.R t).pres.y c))
  have huniq : ∀ x : GA D D.sp.X', ∃! i, ∃ γ ∈ GQ D.sp.X', ∃ k ∈ Ω, x = γ * y' i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 ((R.B.R t).pres.reps ((finHom D.sp.X').rangeRestrict x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * y' i)⁻¹ * x, (hK _).2 ?_, by group⟩
      have e' : (finHom D.sp.X').rangeRestrict ((γ * y' i)⁻¹ * x) = k := by
        simp only [map_mul, map_inv, hy'2, e]
        change (Bridge.ratF D.sp.X' γ * _)⁻¹ * (Bridge.ratF D.sp.X' γ * _ * k) = _
        exact inv_mul_cancel_left _ _
      exact cast (congrArg (· ∈ J) e').symm k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ, hγ⟩, ⟨_, (hK k).1 hk⟩, ?_⟩
      simp only [map_mul, hy'2]
      rfl
  have hSet : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω} =
      Subtype.val '' (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c) : Set (GQ D.sp.X')) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, h1⟩, ?_, rfl⟩
      have := (hK _).1 h2
      simp only [map_mul, map_inv, hy'2] at this
      exact this
    · rintro ⟨δ, h2, rfl⟩
      refine ⟨δ.2, (hK _).2 ?_⟩
      simp only [map_mul, map_inv, hy'2]
      exact h2
  have hfinS : ∀ c, Finite (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) := fun c =>
    Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv
  have hfin : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.Finite := fun c => by
    rw [hSet]
    haveI := hfinS c
    exact (Set.toFinite _).image _
  have hcard : ∀ c, ({γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.ncard : ℂ) =
      (Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ) := fun c => by
    have e := congrArg Set.ncard (hSet c)
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at e
    exact (congrArg (Nat.cast : ℕ → ℂ) e).trans (congrArg (Nat.cast : ℕ → ℂ) (Nat.card_coe_set_eq _).symm)
  have hintc : ∀ c, IntegrableOn (fun k => φ (y' c * k)) Ω (R.νX t) := fun c =>
    (hS c).1.congr_fun (fun k hk => (hpt c k hk).symm) hΩo.measurableSet
  have hIc : ∀ c, ∫ k in (Ω : Set (GA D D.sp.X')), φ (y' c * k) ∂(R.νX t) =
      ∫ k in (Ω : Set (GA D D.sp.X')), star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
        ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ ∂(R.νX t) := fun c =>
    setIntegral_congr_fun hΩo.measurableSet fun k hk => hpt c k hk
  have hfl : ∀ γ : GA D D.sp.X', γ ∈ GQ D.sp.X' → ∀ x : GA D D.sp.X', φ (γ * x) = φ x := fun γ hγ x => by
    show star ⟪a, R.cX.ext ((R.HX t).e h) (γ * x)⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') (γ * x)⟫_ℂ =
      star ⟪a, R.cX.ext ((R.HX t).e h) x⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') x⟫_ℂ
    exact congrArg₂ (fun u v => star ⟪a, u⟫_ℂ * ⟪a', v⟫_ℂ) (hext _ (hF h) γ hγ x) (hext _ (hF h') γ hγ x)
  have U1 := GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold (GA D D.sp.X') (R.νX t) (GQ D.sp.X') Ω (R.fdX t) hμ.2 hΩo _ y' huniq hfin φ hfl hintc
  refine ⟨U1.1, ?_⟩
  change (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, φ g ∂(R.νX t) = _
  refine (congrArg (_ * ·) U1.2).trans ?_
  refine Eq.trans ?_ (congrArg (⟪a', a⟫_ℂ * ·) (hH.2.2 h h').symm)
  simp only [Bridge.adInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (congrArg₂ (fun (u v : ℂ) => (Module.finrank ℂ R.cX.W : ℂ) * (u⁻¹ * v)) (hcard c) (hIc c)).trans ?_
  linear_combination ((Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)⁻¹) * (hS c).2

end GlobalTheory.Mem.SchurW
