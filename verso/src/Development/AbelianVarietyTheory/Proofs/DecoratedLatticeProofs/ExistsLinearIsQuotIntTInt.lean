import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app app_coe)
open scoped Topology

noncomputable section
namespace GlobalTheory.PosOne.RrLin

/- English proof (translation)
Set `Λ : AddSubgroup M` to `{ carrier := {y | ∀ x, Φ (x + y) = Φ x} zero_mem' := fun x => by simp add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy] neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }`. Use `⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x`. Use `IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2)` using `(hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk (hΦ.1.comp_continuous continuous_snd)`.

Use `filter_upwards [h2.eventually_eq (0, x)] with q hq`. Simplify using `only [Prod.mk.injEq, add_zero] at hq`. Rewrite using `[hq.1, hq.2]`. Establish `h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x`. Establish `ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0)`.

Simplify using `using (continuous_neg (G := M)).tendsto 0`. Conclude with `ht.eventually h1`. Use `filter_upwards [h1, h2] with y hs hs' x`. Distinguish the cases in `hx : x ∈ tsupport Φ`. Conclude with `hs x hx`.

Distinguish the cases in `hx' : x + y ∈ tsupport Φ`. Rewrite using `[← hs' _ hx']`. Simplify using the standard rewrite rules. Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']`.
-/
theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  let Λ : AddSubgroup M :=
    { carrier := {y | ∀ x, Φ (x + y) = Φ x}
      zero_mem' := fun x => by simp
      add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy]
      neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }
  refine ⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩
  have h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x := by
    have ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := M)).tendsto 0
    exact ht.eventually h1
  filter_upwards [h1, h2] with y hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : x + y ∈ tsupport Φ
  · rw [← hs' _ hx']; simp
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

/- English proof (translation)
Establish `hE` using `(opE_SB_and_linear k n n' c p ψ hψ ν).1`. Set `E : GL (n ⊕ Fin c) k → SB (Matrix n n' k)` to `fun h => ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩`. Use `set f := tInt ψ ν μ p σ B F Φ.1 with hf`. Establish `hfE : ∀ h, f h = B (E h) (σ h F)` using `fun h => by`. Rewrite using `[hf, tInt]`.

Conclude with `congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B (E h))`. Establish `hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ)` using `fun g h Ψ => by`. Rewrite using `[← om_mul, one_mul]`. Use `(GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).2 ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `h`. Establish `hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F})` using `((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)`. Establish `ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1)`. Simplify using `using (continuous_const_mul h⁻¹).tendsto h`. Use `filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy`.

Take `⟨u, rfl⟩ : ∃ u, y = h * u` from `⟨h⁻¹ * y, by simp⟩`. Rewrite `hy` using `[inv_mul_cancel_left]`. Establish `h1 : om μ 1 u Φ.1 = Φ.1` using `hy.1`. Establish `h2 : σ u F = F` using `hy.2`. Establish `h3 : E (h * u) = E h` using `Subtype.ext (by show opE ψ ν p (om μ 1 (h * u) Φ.1) = opE ψ ν p (om μ 1 h Φ.1)`.

Rewrite using `[hmul, h1])`. Rewrite using `[hfE h, hfE (h * u), h3, map_mul, Module.End.mul_apply, h2]`. Take `⟨Λ, hΛ, hΛ'⟩` from `exists_open_translations Φ.2`. Take `⟨Ω, hΩ, H⟩` from `opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1) Φ.2.2 Λ hΛ`. Use `⟨Ω, hΩ, fun h hh => ?_⟩` and prove the remaining obligations.

Establish `hne : E h ≠ 0` using `fun h0 => hh (by rw [hfE, h0]; simp)`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (Subtype.ext (funext hc))`.

Conclude with `H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀ (by simpa using hx₀)`. Introduce `x u hu h set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha`. Set `Ψ : SB (Matrix n n' k)` to `⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩`. Establish `h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) = (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))`. Rewrite using `[mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul, opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]`. Use function extensionality and compare the values at `y`. Simplify using `only [om, Pi.smul_apply, smul_eq_mul, ha]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1`. Rewrite using `[← Circle.coe_mul, ← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Establish `h4 : a * a = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ)`. Rewrite using `[ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `hB.1 (E h) u hu (σ h F)`. Establish `h6` using `hB.2 x (E h) Ψ (σ u (σ h F)) rfl`. Rewrite using `[hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]`.

Take the linear combination `(a * a * B (E h) (σ h F)) * h3`.
-/
theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  set f := tInt ψ ν μ p σ B F Φ.1 with hf
  have hfE : ∀ h, f h = B (E h) (σ h F) := fun h => by
    rw [hf, tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B (E h))
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    have h3 : E (h * u) = E h := Subtype.ext (by
      show opE ψ ν p (om μ 1 (h * u) Φ.1) = opE ψ ν p (om μ 1 h Φ.1)
      rw [hmul, h1])
    rw [hfE h, hfE (h * u), h3, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := exists_open_translations Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

end GlobalTheory.PosOne.RrLin

namespace GlobalTheory.PosOne.RrLin
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ'`. Establish `uniq` using `(GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG · |>.1)`. Establish `hE` using `(opE_SB_and_linear k n n' c p ψ hψ ν).1`. Establish `hfE : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) h, tInt ψ ν μ p σ B F Φ.1 h = B ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩ (σ h F)` using `fun Φ h => by`. Rewrite using `[tInt]`.

Conclude with `congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B ⟨_, hE _ (om_mem_SB μ 1 h Φ.2)⟩)`. Establish `hlinf : ∀ (a : ℂ) (Φ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), tInt ψ ν μ p σ B F (a • Φ + Ψ).1 = fun h => a * tInt ψ ν μ p σ B F Φ.1 h + tInt ψ ν μ p σ B F Ψ.1 h`. Introduce `a Φ Ψ`. Use function extensionality and compare the values at `h`. Rewrite using `[hfE, hfE, hfE, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.add_apply, ← map_smul, ← map_add]`.

Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show opE ψ ν p (om μ 1 h (a • Φ.1 + Ψ.1)) = a • opE ψ ν p (om μ 1 h Φ.1) + opE ψ ν p (om μ 1 h Ψ.1)`. Establish `e : om μ 1 h (a • Φ.1 + Ψ.1) = a • om μ 1 h Φ.1 + om μ 1 h Ψ.1`. Use function extensionality and compare the values at `y`.

Simplify using `only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(opE_SB_and_linear k n n' c p ψ hψ ν).2 a _ (om_mem_SB μ 1 h Φ.2) _ (om_mem_SB μ 1 h Ψ.2)`. Establish `hex` using `fun Φ => exists_isQuotInt_tInt hp hpc hψ hψ1 ν hμ μX μG hσ hB F Φ`.

Use `choose Rr hRr using hex`. Establish `hlin : ∀ (a : ℂ) Φ Ψ, Rr (a • Φ + Ψ) = a * Rr Φ + Rr Ψ` using `fun a Φ Ψ => by`. Use `uniq _ _ _ (hRr _) ?_` and prove the remaining obligations. Rewrite using `[hlinf]`. Conclude with `GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n c p hp hpc ν μX μG _ _ a _ _ (hRr Φ) (hRr Ψ)`.

Establish `h0 : Rr 0 = 0` using `by simpa using hlin 1 0 0`. Set `RL : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ` to `{ toFun := Rr map_add' := fun Φ Ψ => by simpa using hlin 1 Φ Ψ map_smul' := fun a Φ => by simpa [h0] using hlin a Φ 0 }`. Use `⟨RL, hRr, fun g hg Φ => ?_⟩` and prove the remaining obligations. Use `show Rr (ρ' g Φ) = (ψ (simpleSum g) : ℂ) * Rr Φ`. Establish `e : tInt ψ ν μ p σ B F (ρ' g Φ).1 = tInt ψ ν μ p σ B F ((ψ (simpleSum g) : ℂ) • Φ + 0).1`.

Use function extensionality and compare the values at `h`. Rewrite using `[hfE, hfE]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show opE ψ ν p (om μ 1 h (ρ' g Φ).1) = opE ψ ν p (om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1 + 0))`.

Establish `e1 : om μ 1 h (om μ g 1 Φ.1) = om μ g 1 (om μ 1 h Φ.1)`. Rewrite using `[← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]`. Rewrite using `[hρ', e1, GlobalTheory.RootExSource.opE_om_source k n n' c p hp hpc ψ ν μ _ g hg, add_zero]`. Establish `e2 : om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1) = (ψ (simpleSum g) : ℂ) • om μ 1 h Φ.1`. Use function extensionality and compare the values at `y`.

Simplify using `only [om, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use function extensionality and compare the values at `x`. Simplify using `only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`.

Establish `e3 : Rr (ρ' g Φ) = Rr ((ψ (simpleSum g) : ℂ) • Φ + 0)` using `uniq _ _ _ (hRr _) (e ▸ hRr _)`. Rewrite using `[e3, hlin, h0, add_zero]`.
-/
theorem exists_linear_isQuotInt_tInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ'), ∃ Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) ∧ IsNEquiv ψ p ρ' Rr := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ'
  have uniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG · |>.1)
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1

  have hfE : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) h,
      tInt ψ ν μ p σ B F Φ.1 h =
        B ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩ (σ h F) := fun Φ h => by
    rw [tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B ⟨_, hE _ (om_mem_SB μ 1 h Φ.2)⟩)

  have hlinf : ∀ (a : ℂ) (Φ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ p σ B F (a • Φ + Ψ).1 = fun h => a * tInt ψ ν μ p σ B F Φ.1 h + tInt ψ ν μ p σ B F Ψ.1 h := by
    intro a Φ Ψ
    funext h
    rw [hfE, hfE, hfE, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.add_apply, ← map_smul, ← map_add]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (a • Φ.1 + Ψ.1)) =
      a • opE ψ ν p (om μ 1 h Φ.1) + opE ψ ν p (om μ 1 h Ψ.1)
    have e : om μ 1 h (a • Φ.1 + Ψ.1) = a • om μ 1 h Φ.1 + om μ 1 h Ψ.1 := by
      funext y; simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact (opE_SB_and_linear k n n' c p ψ hψ ν).2 a _ (om_mem_SB μ 1 h Φ.2) _ (om_mem_SB μ 1 h Ψ.2)
  have hex := fun Φ => exists_isQuotInt_tInt hp hpc hψ hψ1 ν hμ μX μG hσ hB F Φ
  choose Rr hRr using hex
  have hlin : ∀ (a : ℂ) Φ Ψ, Rr (a • Φ + Ψ) = a * Rr Φ + Rr Ψ := fun a Φ Ψ => by
    refine uniq _ _ _ (hRr _) ?_
    rw [hlinf]
    exact GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n c p hp hpc ν μX μG _ _ a _ _ (hRr Φ) (hRr Ψ)
  have h0 : Rr 0 = 0 := by simpa using hlin 1 0 0
  let RL : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := Rr
      map_add' := fun Φ Ψ => by simpa using hlin 1 Φ Ψ
      map_smul' := fun a Φ => by simpa [h0] using hlin a Φ 0 }
  refine ⟨RL, hRr, fun g hg Φ => ?_⟩
  show Rr (ρ' g Φ) = (ψ (simpleSum g) : ℂ) * Rr Φ
  have e : tInt ψ ν μ p σ B F (ρ' g Φ).1 = tInt ψ ν μ p σ B F ((ψ (simpleSum g) : ℂ) • Φ + 0).1 := by
    funext h
    rw [hfE, hfE]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (ρ' g Φ).1) = opE ψ ν p (om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1 + 0))
    have e1 : om μ 1 h (om μ g 1 Φ.1) = om μ g 1 (om μ 1 h Φ.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    rw [hρ', e1, GlobalTheory.RootExSource.opE_om_source k n n' c p hp hpc ψ ν μ _ g hg, add_zero]
    have e2 : om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1) = (ψ (simpleSum g) : ℂ) • om μ 1 h Φ.1 := by
      funext y; simp only [om, Pi.smul_apply, smul_eq_mul]; ring
    rw [e2]
    funext x
    simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  have e3 : Rr (ρ' g Φ) = Rr ((ψ (simpleSum g) : ℂ) • Φ + 0) := uniq _ _ _ (hRr _) (e ▸ hRr _)
  rw [e3, hlin, h0, add_zero]

end GlobalTheory.PosOne.RrLin
