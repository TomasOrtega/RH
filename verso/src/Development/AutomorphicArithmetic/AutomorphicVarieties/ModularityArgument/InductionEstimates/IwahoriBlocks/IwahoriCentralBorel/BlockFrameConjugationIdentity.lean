import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `g`. Use `haveI := he.haar.prob`. Establish `hi : ∀ {p : G1 K n → ℂ}, Continuous p → Integrable (fun k => e k * p (g * arc1 k)) κ`. Introduce `p hp`. Conclude with `(he.cont.mul (hp.comp (continuous_const.mul ha))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Establish `e₁ : (fun k => e k * (f + c • f') (g * arc1 k)) = fun k => e k * f (g * arc1 k) + c * (e k * f' (g * arc1 k))`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e₁, integral_add (hi hf) ((hi hf').const_mul c), integral_const_mul, h₁ g, h₂ g]`.

Simplify using the standard rewrite rules.
-/
private lemma fixA_comb {K : Type} [Field K] [NumberField K] {n : ℕ} {κ : Measure (archCompact K n)}
    {e : archCompact K n → ℂ} (he : IdemA κ e) (hc : CompactSpace (archCompact K n))
    (ha : Continuous (arc1 : archCompact K n → G1 K n)) {f f' : G1 K n → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (c : ℂ) (h₁ : FixA κ e f) (h₂ : FixA κ e f') : FixA κ e (f + c • f') := by
  intro g
  haveI := he.haar.prob
  have hi : ∀ {p : G1 K n → ℂ}, Continuous p → Integrable (fun k => e k * p (g * arc1 k)) κ := by
    intro p hp
    exact (he.cont.mul (hp.comp (continuous_const.mul ha))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e₁ : (fun k => e k * (f + c • f') (g * arc1 k)) =
      fun k => e k * f (g * arc1 k) + c * (e k * f' (g * arc1 k)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e₁, integral_add (hi hf) ((hi hf').const_mul c), integral_const_mul, h₁ g, h₂ g]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma flat_comb {K : Type} [Field K] [NumberField K] (f f' : G1 K (2 + 2) → ℂ) (c : ℂ) :
    flat 0 (f + c • f') = flat 0 f + c • flat 0 f' := by
  funext x
  simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `[mul_assoc]`.
-/
private lemma block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (p : H →* G) (x : G) (a b : H) :
    x * p b * p a = x * p a * p (a⁻¹ * b * a) := by
  simp [mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w => GLnLocal.integralGL (w.adicCompletion K) n, fun w => ⟨⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩, le_rfl⟩⟩`.
-/
private lemma lev_exists (K : Type) [Field K] [NumberField K] (n : ℕ) :
    ∃ U : ∀ w : Pl K, Subgroup (Gw n w), Lev U :=
  ⟨fun w => GLnLocal.integralGL (w.adicCompletion K) n, fun w =>
    ⟨⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩, le_rfl⟩⟩

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

/- English proof (translation)
Introduce `K _ _ _ μ₂ _ τ₁ τ₂ κ e he`. Take `⟨⟨sec0, secLin⟩, secFlat, -, secT⟩` from `secTr μ₂ τ₁ τ₂ κ e he`. Establish `hZero : ∀ S, IsZ τ₁ τ₂ κ e S 0`. Introduce `S`. Take `⟨U, hU⟩` from `lev_exists K (2 + 2)`.

Use `⟨0, sec0, fun g => by simp, ⟨U, hU, fun u _ g => rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[flat]`. Establish `hComb : ∀ S φ φ' (c : ℂ), IsZ τ₁ τ₂ κ e S φ → IsZ τ₁ τ₂ κ e S φ' → IsZ τ₁ τ₂ κ e S (φ + c • φ')`. Introduce and unpack `S _ _ c ⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩ ⟨f', hf', ha', ⟨U', hU', hx'⟩, rfl⟩`.

Take `⟨-, hL, -, hA, hC, -⟩` from `levLaws (K := K) (2 + 2) S`. Take `⟨hLev, hEq⟩` from `hL U U' hU hU'`. Use `⟨f + c • f', secLin f f' hf hf' c, fixA_comb he hC hA hf.cont hf'.cont c ha ha', ⟨_, hLev, ?_⟩, (flat_comb f f' c).symm⟩` and prove the remaining obligations. Rewrite using `[hEq]`. Introduce `u hu g`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, hx u hu.1 g, hx' u hu.2 g]`. Establish `hZ : ∀ S φ, φ ∈ Zs τ₁ τ₂ κ e S ↔ IsZ τ₁ τ₂ κ e S φ`. Introduce `S φ`. Use `⟨fun h => ?_, fun h => Submodule.subset_span h⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`.

Consider the case `mem x hx => exact hx`. Consider the case `zero => exact hZero S`. Consider the case `add x y _ _ hx hy`. Use `hComb S x y 1 hx hy` as an intermediate fact. Simplify using `using this`.

Consider the case `smul c x _ hx`. Use `hComb S 0 x c (hZero S) hx` as an intermediate fact. Simplify using `using this`. Use `⟨hZ, ?_⟩` and prove the remaining obligations. Introduce `r w ι hw hι φ hφ`.

Take `⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩` from `(hZ _ _).1 hφ`. Take `⟨L₁, -, -, -, -, L₂⟩` from `levLaws (K := K) (2 + 2) (im w)`. Establish `hfix : FixF (levOn (im w) U) (flat 0 f)` using `((secFlat f hf.cont).2 _ (L₁ U hU).2).2 hx`. Use `⟨?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hcι : Continuous ι` using `((embEx (K := K) (2 + 2) w hw).2 ι hι).1`.

Establish `hO : IsOpen (ι ⁻¹' (levOn (im w) U : Set (FA K (2 + 2))))` using `(L₁ U hU).1.2.preimage hcι`. Set `T : Subgroup (GS (2 + 2) w)` to `{ carrier := {g | rS ι g (flat 0 f) = flat 0 f} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Use `T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hO.mem_nhds (by simp [one_mem])) ?_)` and prove the remaining obligations. Introduce `g hg`. Use `show rS ι g (flat 0 f) = flat 0 f`.

Use function extensionality and compare the values at `x`. Conclude with `hfix _ hg x`. Take `⟨f', hf', ha', he'⟩` from `secT f (ι g) hf ha`. Take `⟨U', hU', hc⟩` from `L₂ w ι hw hι rfl U hU g`. Establish `hr : rS ι g (flat 0 f) = flat 0 f'`.

Use function extensionality and compare the values at `x`. Rewrite using `[he']`. Both sides reduce to the same expression. Rewrite using `[hr]`. Use `Submodule.subset_span ⟨f', hf', ha', ⟨U', hU', ?_⟩, rfl⟩` and prove the remaining obligations.

Use `((secFlat f' hf'.cont).2 _ (L₁ U' hU').2).1 ?_` and prove the remaining obligations. Introduce `u hu x`. Rewrite using `[he', he', block_frame_conjugation_identity (MultiplicityOne.finProj K (2 + 2)) x (ι g) u]`. Conclude with `hfix _ (hc u hu) (x * fin1 (ι g))`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.zMem :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (∀ S φ, φ ∈ Zs τ₁ τ₂ κ e S ↔ IsZ τ₁ τ₂ κ e S φ) ∧
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι → ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), IsOpen {g | rS ι g φ = φ} ∧ ∀ g, rS ι g φ ∈ Zs τ₁ τ₂ κ e (im w) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e he
  obtain ⟨⟨sec0, secLin⟩, secFlat, -, secT⟩ := secTr μ₂ τ₁ τ₂ κ e he
  have hZero : ∀ S, IsZ τ₁ τ₂ κ e S 0 := by
    intro S
    obtain ⟨U, hU⟩ := lev_exists K (2 + 2)
    refine ⟨0, sec0, fun g => by simp, ⟨U, hU, fun u _ g => rfl⟩, ?_⟩
    funext x
    simp [flat]
  have hComb : ∀ S φ φ' (c : ℂ), IsZ τ₁ τ₂ κ e S φ → IsZ τ₁ τ₂ κ e S φ' → IsZ τ₁ τ₂ κ e S (φ + c • φ') := by
    rintro S _ _ c ⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩ ⟨f', hf', ha', ⟨U', hU', hx'⟩, rfl⟩
    obtain ⟨-, hL, -, hA, hC, -⟩ := levLaws (K := K) (2 + 2) S
    obtain ⟨hLev, hEq⟩ := hL U U' hU hU'
    refine ⟨f + c • f', secLin f f' hf hf' c, fixA_comb he hC hA hf.cont hf'.cont c ha ha',
      ⟨_, hLev, ?_⟩, (flat_comb f f' c).symm⟩
    rw [hEq]
    intro u hu g
    simp only [Pi.add_apply, Pi.smul_apply, hx u hu.1 g, hx' u hu.2 g]
  have hZ : ∀ S φ, φ ∈ Zs τ₁ τ₂ κ e S ↔ IsZ τ₁ τ₂ κ e S φ := by
    intro S φ
    refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact hZero S
    | add x y _ _ hx hy =>
      have := hComb S x y 1 hx hy
      simpa using this
    | smul c x _ hx =>
      have := hComb S 0 x c (hZero S) hx
      simpa using this
  refine ⟨hZ, ?_⟩
  intro r w ι hw hι φ hφ
  obtain ⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩ := (hZ _ _).1 hφ
  obtain ⟨L₁, -, -, -, -, L₂⟩ := levLaws (K := K) (2 + 2) (im w)
  have hfix : FixF (levOn (im w) U) (flat 0 f) := ((secFlat f hf.cont).2 _ (L₁ U hU).2).2 hx
  refine ⟨?_, fun g => ?_⟩
  · have hcι : Continuous ι := ((embEx (K := K) (2 + 2) w hw).2 ι hι).1
    have hO : IsOpen (ι ⁻¹' (levOn (im w) U : Set (FA K (2 + 2)))) := (L₁ U hU).1.2.preimage hcι
    let T : Subgroup (GS (2 + 2) w) :=
      { carrier := {g | rS ι g (flat 0 f) = flat 0 f}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hO.mem_nhds (by simp [one_mem])) ?_)
    intro g hg
    show rS ι g (flat 0 f) = flat 0 f
    funext x
    exact hfix _ hg x
  · obtain ⟨f', hf', ha', he'⟩ := secT f (ι g) hf ha
    obtain ⟨U', hU', hc⟩ := L₂ w ι hw hι rfl U hU g
    have hr : rS ι g (flat 0 f) = flat 0 f' := by
      funext x
      rw [he']
      rfl
    rw [hr]
    refine Submodule.subset_span ⟨f', hf', ha', ⟨U', hU', ?_⟩, rfl⟩
    refine ((secFlat f' hf'.cont).2 _ (L₁ U' hU').2).1 ?_
    intro u hu x
    rw [he', he', block_frame_conjugation_identity (MultiplicityOne.finProj K (2 + 2)) x (ι g) u]
    exact hfix _ (hc u hu) (x * fin1 (ι g))
