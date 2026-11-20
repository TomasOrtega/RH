import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldClearDenominatorsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩`. Take `⟨_, hMD, hAE, _, hmemHs⟩` from `GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict`. Take `⟨hNT, hid, hunit⟩` from `GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units`. Take `⟨hmapsto, _, _, hmobSL, hmobD, _⟩` from `GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties`. Take `⟨p, u, hu, hpn, hp⟩` from `GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP`.

Use `set n := P.natDegree with hn`. Establish `hR : ∀ i, InR ε.range (p i : ℍ → ℂ)` using `fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2`. Establish `hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs` using `fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))`. Establish `hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z`. Introduce `g z hz`.

Simplify using `[up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]`. Establish `hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ`. Introduce `f τ`. Simplify using `[up]`. Establish `hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero)`.

Rewrite using `[← Filter.Germ.coe_mul, Filter.Germ.coe_eq]`. Use `filter_upwards [(hunit b hb hb0).1] with z hz`. Simplify using `[div_mul_cancel₀ _ hz]`. Establish `hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Polynomial.eval₂_eq_sum_range, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hp i, map_mul, mul_assoc]`. Use `_ = 0 := by rw [hPe, mul_zero]`. Use `set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF`.

Establish `e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i)`. Use function extensionality and compare the values at `z`. Simplify using `[hF, Finset.sum_apply]`. Establish `hFg : (F : Mero) = 0`. Establish `e1 : (F : Mero) = Filter.Germ.coeRingHom _ F` using `rfl`.

Rewrite using `[e1, e2, map_sum]`. Express the relevant statement in the definitionally equal form `∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _`. Simplify using `only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hin : i ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[T.an_io, ← hxb]`. Use `show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)`. Rewrite using `[mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hsum, mul_zero]`. Establish `hFD : DifferentiableOn ℂ F Hs`. Rewrite using `[e2]`. Use `DifferentiableOn.sum fun i _ => ?_` and prove the remaining obligations.

Conclude with `((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))`. Establish `hF0 : ∀ z ∈ Hs, F z = 0`. Use `hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)` as an intermediate fact. Conclude with `this`. Establish `haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ)` using `(hMD _).2 (ha.congr fun z hz => hup a z hz)`.

Establish `hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ)` using `(hMD _).2 (hb.congr fun z hz => hup b z hz)`. Establish `hbne : (fun τ : ℍ => b τ) ≠ 0`. Introduce `h0`. Apply `hb0` to reduce the goal to its premises. Establish `: (b : Mero) = ((0 : ℂ → ℂ) : Mero)` using `hAE b 0 fun z hz => by`.

Simplify using `using congrFun h0 ⟨z, hz⟩`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ)`. Introduce `γ hγ τ`.

Establish `hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs` using `hmobD _`. Establish `hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs` using `fun z hz => hmapsto _ z hz`. Establish `h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs` using `(ha.comp hmD hmap).mul hb`. Establish `h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs` using `ha.mul (hb.comp hmD hmap)`. Use `hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)` as an intermediate fact.

Simplify `this` using `[hmobSL]`. Establish `hpn' : (p n : ℍ → ℂ) ≠ 0`. Introduce `h0`. Apply `hpn` to reduce the goal to its premises. Use `ext1`.

Conclude with `h0`. Establish `hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0`. Introduce `τ`. Use `hF0 τ (hmemHs τ)` as an intermediate fact. Simplify `this` using `[hF, hupT]`.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)`. Take `⟨h, hhR, hh⟩` from `GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne hinvT hR hpn' hsumT`. Set `hr : ring ε.range` to `⟨h, mem_ring_of_inR hhR⟩`. Establish `hio0 : T.io (p n) ≠ 0`. Introduce `h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])`.

Use `⟨T.io hr / T.io (p n), ?_⟩` and prove the remaining obligations. Establish `hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0`. Introduce `h0`. Establish `hinj : Function.Injective T.an` using `T.an.injective`. Apply `hio0` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, T.an_io]`. Conclude with `h0`. Establish `hU : IsUnit (up (p n : ℍ → ℂ) : Mero)` using `(hunit _ (hpD n) hg0).2`. Establish `hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero)`.

Rewrite using `[← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]`. Use `hAE _ _ fun z hz => ?_` and prove the remaining obligations. Establish `e` using `hh ⟨z, hz⟩`. Simplify using `only [Pi.mul_apply]`. Establish `q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩`.

Simplify using `[up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]`. Establish `q2 : up h z = h ⟨z, hz⟩`. Simplify using `[up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]`. Rewrite using `[q1, q2]`. Simplify using `using e`.

Establish `hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero)`. Establish `: T.io hr / T.io (p n) * T.io (p n) = T.io hr` using `div_mul_cancel₀ _ hio0`. Use `congrArg T.an this` as an intermediate fact. Rewrite `this` using `[map_mul, T.an_io, T.an_io]`. Conclude with `this`.

Apply `hU.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hrel, ← hf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨p, u, hu, hpn, hp⟩ := GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl
    rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
