import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearPositionMiddleVertexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselStepPositionOneFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneIsPositionOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilSourceActionAndSmoothStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ μ b hb`. Establish `H` using `GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ`. Establish `E` using `GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ`. Use `⟨GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1, fun Ψ v => rfl, fun Ψ => ?_, fun g Ψ Ψ₁ v hΨ => ?_⟩` and prove the remaining obligations. Take `⟨l', hl', hN⟩` from `E.1 (b Ψ) (hb.1 Ψ)`.

Establish `: (⇑((GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1) Ψ) : A → ℂ) = ⇑l'`. Use function extensionality and compare the values at `v`. Rewrite using `[hl']`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hN`. Express the relevant statement in the definitionally equal form `∫ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) = _ * ∫ u, b Ψ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)`. Set `m : GL n k` to `⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩`. Establish `hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g` using `by ext; simp [m]`. Establish `step : ∀ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b Ψ (σ (rowE c p (m.val.mulVec u)) v)` using `fun u => by`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, GlobalTheory.RootEx.Exchange.rowE_mul_embX, map_mul, Module.End.mul_apply, hb.2 g Ψ Ψ₁ _ hΨ]`. Simplify using `only [step]`. Rewrite using `[integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m (fun u => b Ψ (σ (rowE c p u) v)), hm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_neg_one, ← Real.rpow_add (GlobalTheory.SplitWeil.nabs_pos k _)]`. Use `congr 3`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.PosOne.exUp_bilPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (μ : kˣ →* ℂˣ) (b : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ p σ b → ∃ B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B Ψ v = exUp ν p σ (b Ψ) v) ∧ BilPos ψ μ (p + 1) σ B := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ μ b hb
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  refine ⟨GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1,
    fun Ψ v => rfl, fun Ψ => ?_, fun g Ψ Ψ₁ v hΨ => ?_⟩
  · obtain ⟨l', hl', hN⟩ := E.1 (b Ψ) (hb.1 Ψ)
    have : (⇑((GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b
        fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1) Ψ) : A → ℂ) = ⇑l' := by
      funext v; rw [hl']; rfl
    rw [this]; exact hN
  · change ∫ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      _ * ∫ u, b Ψ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)
    let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    have step : ∀ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
          b Ψ (σ (rowE c p (m.val.mulVec u)) v) := fun u => by
      rw [← Module.End.mul_apply, ← map_mul, GlobalTheory.RootEx.Exchange.rowE_mul_embX, map_mul, Module.End.mul_apply,
        hb.2 g Ψ Ψ₁ _ hΨ]
    simp only [step]
    rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m
      (fun u => b Ψ (σ (rowE c p u) v)), hm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_neg_one, ← Real.rpow_add (GlobalTheory.SplitWeil.nabs_pos k _)]
    congr 3
    push_cast; ring

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ P _ _ b B hbN hB`. Use `haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k`. Establish `H` using `GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ`. Establish `E` using `GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ`. Establish `hBN : ∀ φ, IsNEquiv ψ (p + 1) σ (B φ)` using `fun φ => by`.

Take `⟨l', hl', hN⟩` from `E.1 (b φ) (hbN φ)`. Establish `: (⇑(B φ) : A → ℂ) = ⇑l'` using `by funext v; rw [hl', hB]`. Rewrite using `[this]`. Conclude with `hN`. Establish `integ : ∀ φ v (Φ₀ : SB (n → k)), Integrable (fun β => (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v)) (Measure.pi fun _ => ν)` using `fun φ v Φ₀ => by`.

Establish `hS` using `((H (B φ) v).2 (hBN φ)).1`. Conclude with `GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν ⟨Φ₀.2.1.mul hS.1, Φ₀.2.2.mul_right⟩`. Set `fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ` to `{ toFun := fun φ => LinearMap.mk₂ ℂ (fun v Φ₀ => ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν)) (fun v₁ v₂ Φ₀ => by`. Simplify using `only [map_add, mul_add]`. Conclude with `integral_add (integ φ v₁ Φ₀) (integ φ v₂ Φ₀))`.

Use the proof step `(fun a v Φ₀ => by`. Simplify using `only [map_smul, smul_eq_mul, mul_left_comm _ a]`. Conclude with `integral_const_mul a _)`. Use the proof step `(fun v Φ₀ Φ₀' => by`. Simplify using `only [Submodule.coe_add, Pi.add_apply, add_mul]`.

Conclude with `integral_add (integ φ v Φ₀) (integ φ v Φ₀'))`. Use the proof step `(fun a v Φ₀ => by`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul a _)`. Use the proof step `map_add' := fun φ φ' => by`.

Use extensionality with `v Φ₀`. Simplify using `only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add, mul_add]`. Conclude with `integral_add (integ φ v Φ₀) (integ φ' v Φ₀)`. Use the proof step `map_smul' := fun a φ => by`. Use extensionality with `v Φ₀`.

Simplify using `only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]`. Conclude with `integral_const_mul a _ }`. Use `⟨fj, ⟨hBN, fun φ v Φ₀ => ⟨integ φ v Φ₀, rfl⟩⟩, fun φ v Φ₀ => ?_⟩` and prove the remaining obligations. Establish `hg` using `(H (b φ) v).1 (hbN φ)`. Express the relevant statement in the definitionally equal form `∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν) = _`.

Simplify using `only [hB, hg.2.2]`. Simplify using `only [← integral_const_mul]`. Rewrite using `[integral_integral_swap]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, ← integral_mul_const]`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Use `congr 1`. Use function extensionality and compare the values at `β`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν Φ₀.2`.

Establish `h2` using `GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν hg.1`. Use `(h1.mul_prod h2).norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Conclude with `(Φ₀.2.1.continuous.comp continuous_fst).mul (((continuous_induced_dom.comp hψ).comp ((continuous_snd.dotProduct continuous_fst))).mul (hg.1.1.continuous.comp continuous_snd))`. Take `⟨β, u⟩` from `z`.

Simplify using `only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul, norm_norm, le_refl]`.
-/
theorem GlobalTheory.PosOne.exUp_represents : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P : Type) [AddCommGroup P] [Module ℂ P] (b B : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (∀ φ, IsNEquiv ψ p σ (b φ)) → (∀ φ v, B φ v = exUp ν p σ (b φ) v) → ∃ fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ, Represents ψ ν p σ fj B ∧ ∀ φ v (Φ₀ : SB (n → k)), fj φ v Φ₀ = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ : (n → k) → ℂ) u * b φ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ P _ _ b B hbN hB
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have hBN : ∀ φ, IsNEquiv ψ (p + 1) σ (B φ) := fun φ => by
    obtain ⟨l', hl', hN⟩ := E.1 (b φ) (hbN φ)
    have : (⇑(B φ) : A → ℂ) = ⇑l' := by funext v; rw [hl', hB]
    rw [this]; exact hN
  have integ : ∀ φ v (Φ₀ : SB (n → k)), Integrable (fun β => (Φ₀ : (n → k) → ℂ) β *
      B φ (σ (colE c (p + 1) β) v)) (Measure.pi fun _ => ν) := fun φ v Φ₀ => by
    have hS := ((H (B φ) v).2 (hBN φ)).1
    exact GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν ⟨Φ₀.2.1.mul hS.1, Φ₀.2.2.mul_right⟩
  let fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => LinearMap.mk₂ ℂ
        (fun v Φ₀ => ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν))
        (fun v₁ v₂ Φ₀ => by
          simp only [map_add, mul_add]
          exact integral_add (integ φ v₁ Φ₀) (integ φ v₂ Φ₀))
        (fun a v Φ₀ => by
          simp only [map_smul, smul_eq_mul, mul_left_comm _ a]
          exact integral_const_mul a _)
        (fun v Φ₀ Φ₀' => by
          simp only [Submodule.coe_add, Pi.add_apply, add_mul]
          exact integral_add (integ φ v Φ₀) (integ φ v Φ₀'))
        (fun a v Φ₀ => by
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
          exact integral_const_mul a _)
      map_add' := fun φ φ' => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add, mul_add]
        exact integral_add (integ φ v Φ₀) (integ φ' v Φ₀)
      map_smul' := fun a φ => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
          mul_left_comm _ a]
        exact integral_const_mul a _ }
  refine ⟨fj, ⟨hBN, fun φ v Φ₀ => ⟨integ φ v Φ₀, rfl⟩⟩, fun φ v Φ₀ => ?_⟩
  have hg := (H (b φ) v).1 (hbN φ)
  change ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν) = _
  simp only [hB, hg.2.2]
  simp only [← integral_const_mul]
  rw [integral_integral_swap]
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, ← integral_mul_const]
    congr 1; funext u; congr 1; funext β; ring
  · have h1 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν Φ₀.2
    have h2 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν hg.1
    refine (h1.mul_prod h2).norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · apply Continuous.aestronglyMeasurable
      exact (Φ₀.2.1.continuous.comp continuous_fst).mul
        (((continuous_induced_dom.comp hψ).comp
          ((continuous_snd.dotProduct continuous_fst))).mul (hg.1.1.continuous.comp continuous_snd))
    · obtain ⟨β, u⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul, norm_norm, le_refl]

noncomputable section
namespace GlobalTheory.PosOne

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [om, map_one, inv_one, Units.val_one, mul_one, one_mul, Matrix.mul_one, Matrix.one_mul]`. Establish `: nabs k (1 : kˣ) = 1` using `by simp [nabs]`. Simplify using `only [this, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul, Matrix.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_one_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) : om μ 1 h (om μ g 1 Φ) = om μ g h Φ := by
  funext x
  simp only [om, map_one, inv_one, Units.val_one, mul_one, one_mul, Matrix.mul_one, Matrix.one_mul]
  have : nabs k (1 : kˣ) = 1 := by simp [nabs]
  simp only [this, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul, Matrix.mul_assoc]
  ring

open Classical in

/- English proof (translation)
Apply the tactic sequence `unfold app; split_ifs <;> simp`.
-/
theorem app_eq_dite {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app l f = l (if h : f ∈ SB X then ⟨f, h⟩ else 0) := by
  unfold app; split_ifs <;> simp

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT F ρ₀ hρ₀ Φ₁ Φ₂ e he z hz`. Use `haveI : ν.IsAddHaarMeasure := hν.1`. Establish `hρ1 : 1 ≤ ρ` using `by omega`. Take `⟨⟨ρ₁, hρ₁⟩, hsm⟩` from `GlobalTheory.T.exists_weilSourceAction_and_smooth k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂`. Establish `hρ₁s : IsSmoothRep ρ₁` using `hsm ρ₁ hρ₁`.

Take `⟨b, hb, hb2, hb3⟩` from `GlobalTheory.T.exists_bilinear_position_middle_vertex k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ m₂ G₂ A σ hσ T hT F ρ₁ hρ₁`. Take `⟨B, hB, hBpos⟩` from `GlobalTheory.PosOne.exUp_bilPos k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s μ₁ b hb`. Take `⟨fj, hrep, hfj⟩` from `GlobalTheory.PosOne.exUp_represents k n₁ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s _ b B hb.1 hB`. Take `⟨-, hpos⟩` from `GlobalTheory.T.exchangeToPositionOne_isPositionOne k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s`. Take `⟨B₁, hB₁, -⟩` from `hpos μ₁ hμ₁ b hb`.

Establish `hstep : ∀ g ∈ e.support, IsQuotInt ν m₁ G₁ (ρ + 1) (tInt ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂ (om μ₁ g 1 Φ₁.1)) (z g)`. Introduce `g hg`. Take `⟨w', hw', hFJ⟩` from `hz g hg`. Establish `hΦ' : ((ρ₀ g Φ₁ : SB _) : Matrix _ _ k → ℂ) = om μ₁ g 1 Φ₁.1` using `hρ₀ g Φ₁`. Establish `key : w' = fun h Ψ Φ₀ => fj Ψ (ρ₁ h Φ₂) Φ₀`.

Use function extensionality and compare the values at `h Ψ Φ₀`. Establish `hV : ((ρ₁ h Φ₂ : SB _) : Matrix _ _ k → ℂ) = om μ₂ h 1 Φ₂.1` using `hρ₁ h Φ₂`. Take `⟨-, hav⟩` from `GlobalTheory.T.schwartzBruhat_self_average_heisenberg k n₂ n₁ c ρ hρ1 (by omega) ψ hψ hψ1 ν hν μ₂ hμ₂ (ρ₁ h Φ₂)`. Take `⟨hmem, hE, hL⟩` from `hav Φ₀`. Establish `h1` using `hb2 Ψ ⟨_, hmem⟩`.

Establish `h2` using `hw' h Ψ Φ₀`. Establish `hf : tInt ψ ν μ₂ ρ σ (T Ψ) F (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ₂ ρ Φ₀.1 (ρ₁ h Φ₂).1) = fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂.1)) (σ h' F)`. Use function extensionality and compare the values at `h'`. Simplify using `only [tInt]`. Rewrite using `[hE h', hV, om_one_comp]`.

Rewrite `h1` using `[hf]`. Establish `heq` using `(GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ hρ1 (by omega) ν m₂ G₂ _).1 _ _ h2 h1`. Rewrite using `[heq, hfj, ← GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (b Ψ) ⟨_, hmem⟩]`. Conclude with `hL ρ₁ hρ₁ (b Ψ)`. Rewrite `hFJ` using `[key, ← hΦ']`.

Use `(GlobalTheory.T.fourierJacobi_target_bilinear_form_integral k n₁ n₀ (c + 1) ρ hρ1 hcρ ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ _ ρ₁ hρ₁s fj B hrep hBpos Φ₂ (ρ₀ g Φ₁) (z g)).2 hFJ` as an intermediate fact. Rewrite `this` using `[hΦ']`. Then use the resulting hypothesis. Establish `hone` using `GlobalTheory.T.bessel_step_position_one_finite k n₁ n₀ (c + 1) (ρ + 1) (by omega) (by omega) ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ ρ₀ hρ₀ Φ₁ e he _ ρ₁ hρ₁s B hBpos Φ₂ z hstep`. Use `⟨fun h => B₁.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩` and prove the remaining obligations. Use `hb3 Ψ (ρ₁ h Φ₂)` as an intermediate fact.

Rewrite `this` using `[hρ₁ h Φ₂]`. Simplify `this` using `[hB₁]`. Use `hone using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`. Take `⟨q, rfl⟩ : ∃ q, ρ = q + 1` from `⟨ρ - 1, by omega⟩`.

Simplify using `only [tIntOne, app_eq_dite]`. Rewrite using `[toOne_succ]`. Use `set Ψf := (if hf : opE ψ ν 1 (om μ₁ 1 h Φ₁.1) ∈ SB (Matrix n₁ n₀ k) then ⟨_, hf⟩ else 0 : SB (Matrix n₁ n₀ k))`. Establish `hd : exDown ν (q + 1) ρ₁ (fun v => B Ψf v) = fun v => b Ψf v`. Use function extensionality and compare the values at `v`.

Simplify using `only [exDown, hB]`. Conclude with `(GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n₁ (c + 1) (q + 1) hρ1 (by omega) ψ hψ hψ1 ν hν _ ρ₁ hρ₁s (b Ψf) v).1 (hb.1 Ψf)`. Rewrite using `[hd, LinearMap.flip_apply, hB₁]`.
-/
theorem oneDbl_of_symDbl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₀ : Representation ℂ (GL (n₀ ⊕ Fin (c + 1 + 1)) k) (SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))) (_ : IsSrc μ₁ ρ₀) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (_ : SrcComb ψ ν (ρ + 1) ρ₀ Φ₁ e) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ), (∀ g ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F (om μ₁ g 1 Φ₁.1) Φ₂.1 (z g)) → OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 (comb e z) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT
    F ρ₀ hρ₀ Φ₁ Φ₂ e he z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨⟨ρ₁, hρ₁⟩, hsm⟩ := GlobalTheory.T.exists_weilSourceAction_and_smooth k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂
  have hρ₁s : IsSmoothRep ρ₁ := hsm ρ₁ hρ₁
  obtain ⟨b, hb, hb2, hb3⟩ := GlobalTheory.T.exists_bilinear_position_middle_vertex k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ m₂ G₂ A σ hσ T hT
    F ρ₁ hρ₁
  obtain ⟨B, hB, hBpos⟩ := GlobalTheory.PosOne.exUp_bilPos k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s μ₁ b hb
  obtain ⟨fj, hrep, hfj⟩ := GlobalTheory.PosOne.exUp_represents k n₁ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s _ b B hb.1 hB
  obtain ⟨-, hpos⟩ := GlobalTheory.T.exchangeToPositionOne_isPositionOne k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s
  obtain ⟨B₁, hB₁, -⟩ := hpos μ₁ hμ₁ b hb
  have hstep : ∀ g ∈ e.support, IsQuotInt ν m₁ G₁ (ρ + 1)
      (tInt ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂ (om μ₁ g 1 Φ₁.1)) (z g) := by
    intro g hg
    obtain ⟨w', hw', hFJ⟩ := hz g hg
    have hΦ' : ((ρ₀ g Φ₁ : SB _) : Matrix _ _ k → ℂ) = om μ₁ g 1 Φ₁.1 := hρ₀ g Φ₁
    have key : w' = fun h Ψ Φ₀ => fj Ψ (ρ₁ h Φ₂) Φ₀ := by
      funext h Ψ Φ₀
      have hV : ((ρ₁ h Φ₂ : SB _) : Matrix _ _ k → ℂ) = om μ₂ h 1 Φ₂.1 := hρ₁ h Φ₂
      obtain ⟨-, hav⟩ := GlobalTheory.T.schwartzBruhat_self_average_heisenberg k n₂ n₁ c ρ hρ1 (by omega) ψ hψ hψ1 ν hν μ₂ hμ₂ (ρ₁ h Φ₂)
      obtain ⟨hmem, hE, hL⟩ := hav Φ₀
      have h1 := hb2 Ψ ⟨_, hmem⟩
      have h2 := hw' h Ψ Φ₀
      have hf : tInt ψ ν μ₂ ρ σ (T Ψ) F (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ₂ ρ Φ₀.1 (ρ₁ h Φ₂).1) =
          fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂.1)) (σ h' F) := by
        funext h'
        simp only [tInt]
        rw [hE h', hV, om_one_comp]
      rw [hf] at h1
      have heq := (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ hρ1 (by omega) ν m₂ G₂ _).1 _ _ h2 h1
      rw [heq, hfj, ← GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (b Ψ) ⟨_, hmem⟩]
      exact hL ρ₁ hρ₁ (b Ψ)
    rw [key, ← hΦ'] at hFJ
    have := (GlobalTheory.T.fourierJacobi_target_bilinear_form_integral k n₁ n₀ (c + 1) ρ hρ1 hcρ ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ _ ρ₁ hρ₁s fj B hrep hBpos Φ₂
      (ρ₀ g Φ₁) (z g)).2 hFJ
    rwa [hΦ'] at this
  have hone := GlobalTheory.T.bessel_step_position_one_finite k n₁ n₀ (c + 1) (ρ + 1) (by omega) (by omega) ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ ρ₀ hρ₀ Φ₁ e he
    _ ρ₁ hρ₁s B hBpos Φ₂ z hstep
  refine ⟨fun h => B₁.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
  · have := hb3 Ψ (ρ₁ h Φ₂)
    rw [hρ₁ h Φ₂] at this
    simpa [hB₁] using this
  · convert hone using 1
    funext h
    obtain ⟨q, rfl⟩ : ∃ q, ρ = q + 1 := ⟨ρ - 1, by omega⟩
    simp only [tIntOne, app_eq_dite]
    rw [toOne_succ]
    classical
    set Ψf := (if hf : opE ψ ν 1 (om μ₁ 1 h Φ₁.1) ∈ SB (Matrix n₁ n₀ k) then ⟨_, hf⟩ else 0 : SB (Matrix n₁ n₀ k))
    have hd : exDown ν (q + 1) ρ₁ (fun v => B Ψf v) = fun v => b Ψf v := by
      funext v
      simp only [exDown, hB]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n₁ (c + 1) (q + 1) hρ1 (by omega) ψ hψ hψ1 ν hν _ ρ₁ hρ₁s
        (b Ψf) v).1 (hb.1 Ψf)
    rw [hd, LinearMap.flip_apply, hB₁]

end GlobalTheory.PosOne
