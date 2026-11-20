import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.DefiniteSmallIrred
/- English proof (translation)
Introduce `hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨ Φ' hΦ' hder h`. Establish `hw : IsWeilDatumO ψ W₁ X α (α / β) ωB` using `(GlobalTheory.Grid.isWeil_false ψ W₁ X α (α / β) ωB).1 hm.weilB`. Establish `hthA : ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, IsThetaFunO ψ W₁ X Φ`. Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨f, P, hf, rfl⟩` from `hx`. Conclude with `GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P`. Consider the case `zero => exact GlobalTheory.OrientedHeis.theta_zero`. Consider the case `add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy`.

Consider the case `smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx`. Establish `hth : IsThetaFunO ψ W₁ X Ψ` using `hthA Ψ hΨ`. Establish `hpos : ∀ τ, (gramAt D W₁ τ).PosDef` using `fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs₁ τ)`. Take `⟨Gn, hGn⟩` from `GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ W₁ X α (α / β) ωB hw θ hθ τ Y hY`. Establish `hGΨ : ∀ (g : GA D W₁) (k : GA D X), HasDerivAt (fun t : ℝ => thetaKO ωB g (k * oneP θ X τ Y t) Ψ) (thetaKO ωB g k Φ') 0`.

Establish `hG : Gn Ψ = Φ'`. Use function extensionality and compare the values at `z`. Establish `h1` using `(hGn Ψ hth).2.2.2 1 z`. Simplify using `only [one_mul, map_one, Module.End.one_apply] at h1`. Conclude with `h1.unique (hder z)`.

Introduce `g k`. Establish `h1` using `(hGn Ψ hth).2.2.2 (g, k) 0`. Simplify using `only [Prod.mk_mul_mk, mul_one, hG] at h1`. Conclude with `h1`. Set `L : ℂ →ₗ[ℂ] (WO W₁ X → ℂ)` to `LinearMap.toSpanSingleton ℂ _ Ψ`.

Establish `hL : ∀ x, IsThetaFunO ψ W₁ X (L x)` using `fun x => GlobalTheory.OrientedHeis.theta_smul x hth`. Establish `hL1 : L 1 = Ψ` using `by simp [L]`. Take `⟨-, hD⟩` from `GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ W₁ X α (α / β) ωB hw θ hθ hpos ℂ L hL (fun _ => 1) continuous_const (fun _ _ _ => rfl) ν₁ 𝓕₁ hν₁.1 hν₁.2`. Take `⟨L', -, hk, hlift⟩` from `hD τ Y hY`. Establish `hkid : ∀ g k, thetaKO ωB g k (L' 1) = thetaKO ωB g k Φ'`.

Introduce `g k`. Establish `h1` using `hk 1 g k`. Rewrite `h1` using `[hL1]`. Conclude with `h1.unique (hGΨ g k)`. Establish `h2` using `hlift h`.

Simplify using `only [GlobalTheory.DefLift.lift, hL1, hkid] at h2`. Conclude with `h2`.
-/
theorem definite_small_irreducible_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Ψ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
  GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X (fun h => ωB (1, h)) τ Y Ψ Φ' → ∀ h : GA D X,
  HasDerivAt (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) (GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' h) 0 := by
  intro hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨ Φ' hΦ' hder h
  have hw : IsWeilDatumO ψ W₁ X α (α / β) ωB := (GlobalTheory.Grid.isWeil_false ψ W₁ X α (α / β) ωB).1 hm.weilB
  have hthA : ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, IsThetaFunO ψ W₁ X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hth : IsThetaFunO ψ W₁ X Ψ := hthA Ψ hΨ
  have hpos : ∀ τ, (gramAt D W₁ τ).PosDef := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs₁ τ)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ W₁ X α (α / β) ωB hw θ hθ τ Y hY
  have hGΨ : ∀ (g : GA D W₁) (k : GA D X),
      HasDerivAt (fun t : ℝ => thetaKO ωB g (k * oneP θ X τ Y t) Ψ) (thetaKO ωB g k Φ') 0 := by
    have hG : Gn Ψ = Φ' := by
      funext z
      have h1 := (hGn Ψ hth).2.2.2 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at h1
      exact h1.unique (hder z)
    intro g k
    have h1 := (hGn Ψ hth).2.2.2 (g, k) 0
    simp only [Prod.mk_mul_mk, mul_one, hG] at h1
    exact h1
  let L : ℂ →ₗ[ℂ] (WO W₁ X → ℂ) := LinearMap.toSpanSingleton ℂ _ Ψ
  have hL : ∀ x, IsThetaFunO ψ W₁ X (L x) := fun x => GlobalTheory.OrientedHeis.theta_smul x hth
  have hL1 : L 1 = Ψ := by simp [L]
  obtain ⟨-, hD⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ W₁ X α (α / β) ωB hw θ hθ hpos ℂ L hL
    (fun _ => 1) continuous_const (fun _ _ _ => rfl) ν₁ 𝓕₁ hν₁.1 hν₁.2
  obtain ⟨L', -, hk, hlift⟩ := hD τ Y hY
  have hkid : ∀ g k, thetaKO ωB g k (L' 1) = thetaKO ωB g k Φ' := by
    intro g k
    have h1 := hk 1 g k
    rw [hL1] at h1
    exact h1.unique (hGΨ g k)
  have h2 := hlift h
  simp only [GlobalTheory.DefLift.lift, hL1, hkid] at h2
  exact h2
/- English proof (translation)
Introduce `hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂`. Establish `hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree` using `_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hTK hLM`. Use `set S := GlobalTheory.SquareComm.algF ψ θ false A₁ B with hSdef`. Establish `hint` using `GlobalTheory.DefIrred.integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁`. Establish `tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ`.

Introduce `Φ g h k`. Use `show (ωB (g, h) * ωB (1, k)) Φ 0 = _`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one]`. Both sides reduce to the same expression. Establish `tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) → (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ - GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ`.

Introduce `Φ Ψ hΦ hΨ`. Use function extensionality and compare the values at `h`. Establish `e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_sub]`.

Simplify using `only [GlobalTheory.SquareComm.thetaInt, Pi.sub_apply]`. Rewrite using `[e]`. Conclude with `integral_sub (hΦ h) (hΨ h)`. Establish `tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) → (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ + GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ`. Introduce `Φ Ψ hΦ hΨ`.

Use function extensionality and compare the values at `h`. Establish `e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_add]`. Simplify using `only [GlobalTheory.SquareComm.thetaInt, Pi.add_apply]`.

Rewrite using `[e]`. Conclude with `integral_add (hΦ h) (hΨ h)`. Establish `tsmul : ∀ (c : ℂ) Φ, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ`. Introduce `c Φ`. Use function extensionality and compare the values at `h`.

Establish `e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_smul]`. Simplify using `only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[e]`.

Conclude with `integral_const_mul c _`. Set `Kint : Submodule ℂ (WO W₁ X → ℂ)` to `{ carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ = 0} add_mem' := fun {a b} ha hb => ⟨fun h => by`. Establish `e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_add]`.

Rewrite using `[e]`. Conclude with `(ha.1 h).add (hb.1 h),`. Use `by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩`. Use the proof step `zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨fun h => by`.

Establish `e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a`. Use function extensionality and compare the values at `g`. Simplify using `[thetaKO, map_smul]`. Rewrite using `[e]`. Conclude with `(ha.1 h).const_mul c,`.

Use `by rw [tsmul, ha.2, smul_zero]⟩ }`. Set `K : Submodule ℂ (WO W₁ X → ℂ)` to `S ⊓ Kint`. Take `⟨c, hc0, hc⟩` from `hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm`. Establish `hrel` using `_root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁`. Establish `kerp' : GlobalTheory.SquareComm.finRel ωB S ≤ LinearMap.ker p'`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, Ψ, hΨ, rfl⟩`. Simplify using `[map_sub, hm.mapB.invf u hu Ψ hΨ]`. Establish `kill : ∀ Ψ ∈ S, p' Ψ = 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ = 0`. Introduce `Ψ hΨ hp0`.

Take `⟨Φ₀, hΦ₀, hd, -, hI⟩` from `hc Ψ hΨ`. Establish `hp00 : p' Φ₀ = 0`. Use `kerp' hd` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero]`. Conclude with `this`.

Establish `h1` using `hI 0 (zero_mem _) (by rw [map_zero, hp00])`. Establish `h2 : GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 0 = 0` using `by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]`. Rewrite `h1` using `[h2]`. Establish `h3 : GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0` using `(smul_eq_zero.1 h1.symm).resolve_left hc0`. Establish `h4` using `hrel _ hd`.

Rewrite `h4` using `[tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero]`. Conclude with `h4`. Establish `stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p'`. Introduce and unpack `g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩`. Use `⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩` and prove the remaining obligations.

Simplify using `only [tr]`. Conclude with `hΨi (h * g)`. Use function extensionality and compare the values at `h`. Simplify using `only [GlobalTheory.SquareComm.thetaInt, tr]`. Conclude with `congrFun hΨ0 (h * g)`.

Establish `stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p'`. Introduce and unpack `τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩`. Take `⟨Φ', hΦ'S, hder⟩` from `hm.mapB.stabX.2 τ Y hY Ψ hΨS`. Use `⟨Φ', ⟨hΦ'S, hint Φ' hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`.

Establish `hd` using `_root_.GlobalTheory.DefiniteSmallIrred.definite_small_irreducible_lie_derivative hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨS Φ' hΦ'S hder h`. Establish `e0 : (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `t`. Rewrite using `[hΨ0]`. Both sides reduce to the same expression.

Rewrite `hd` using `[e0]`. Conclude with `hd.unique (hasDerivAt_const 0 0)`. Break down `hm.irred.2 (K.map p') stf stl with hbot | htop` into its components or cases. It suffices to derive a contradiction. Establish `: p' Φ₁ ∈ K.map p'` using `⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩`.

Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `hp₁ this`. Establish `: p' Φ₂ ∈ K.map p'` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩` from `this`. Establish `h0` using `kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])`.

Rewrite `h0` using `[tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero]`. Conclude with `h0`.
-/
theorem theta_vanish_all_of_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  intro hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
  have hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hTK hLM
  set S := GlobalTheory.SquareComm.algF ψ θ false A₁ B with hSdef
  have hint := GlobalTheory.DefIrred.integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁
  have tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ := by
    intro Φ g h k
    show (ωB (g, h) * ωB (1, k)) Φ 0 = _
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rfl
  have tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ - GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_sub]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.sub_apply]
    rw [e]
    exact integral_sub (hΦ h) (hΨ h)
  have tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ + GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hΦ h) (hΨ h)
  have tsmul : ∀ (c : ℂ) Φ, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ := by
    intro c Φ; funext h
    have e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul c _
  let Kint : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b := by
            funext g; simp [thetaKO, map_add]
          rw [e]; exact (ha.1 h).add (hb.1 h),
        by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]⟩
      smul_mem' := fun c a ha => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a := by
            funext g; simp [thetaKO, map_smul]
          rw [e]; exact (ha.1 h).const_mul c,
        by rw [tsmul, ha.2, smul_zero]⟩ }
  let K : Submodule ℂ (WO W₁ X → ℂ) := S ⊓ Kint
  obtain ⟨c, hc0, hc⟩ := hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁
  have kerp' : GlobalTheory.SquareComm.finRel ωB S ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [map_sub, hm.mapB.invf u hu Ψ hΨ]
  have kill : ∀ Ψ ∈ S, p' Ψ = 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
    intro Ψ hΨ hp0
    obtain ⟨Φ₀, hΦ₀, hd, -, hI⟩ := hc Ψ hΨ
    have hp00 : p' Φ₀ = 0 := by
      have := kerp' hd
      rw [LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero] at this
      exact this
    have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp00])
    have h2 : GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 0 = 0 := by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]
    rw [h2] at h1
    have h3 : GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0 := (smul_eq_zero.1 h1.symm).resolve_left hc0
    have h4 := hrel _ hd
    rw [tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero] at h4
    exact h4
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p' := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    refine ⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩
    · simp only [tr]; exact hΨi (h * g)
    · funext h
      simp only [GlobalTheory.SquareComm.thetaInt, tr]
      exact congrFun hΨ0 (h * g)
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p' := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    obtain ⟨Φ', hΦ'S, hder⟩ := hm.mapB.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Φ', ⟨hΦ'S, hint Φ' hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩
    funext h
    have hd := _root_.GlobalTheory.DefiniteSmallIrred.definite_small_irreducible_lie_derivative hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨS Φ' hΦ'S hder h
    have e0 : (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) = fun _ => (0 : ℂ) := by
      funext t; rw [hΨ0]; rfl
    rw [e0] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  rcases hm.irred.2 (K.map p') stf stl with hbot | htop
  · exfalso
    have : p' Φ₁ ∈ K.map p' := ⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hp₁ this
  · have : p' Φ₂ ∈ K.map p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩ := this
    have h0 := kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])
    rw [tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero] at h0
    exact h0
end GlobalTheory.DefiniteSmallIrred
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | exact _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | (intros; apply _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.vanishing_of_definite_small_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  first | exact @_root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | exact _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | (intros; apply _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible <;> assumption)
end
