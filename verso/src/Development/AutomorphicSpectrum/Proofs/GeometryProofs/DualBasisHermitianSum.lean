import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.KForm

section Embeddings

variable {E : Type} [Field E] [NumberField E]

open Classical in

/- English proof (translation)
Set `ρ : 𝓞 E →+* Module.End ℂ ℂ` to `(Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))`. Establish `hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z` using `fun a z => rfl`. Establish `hmem : (1 : ℂ) ∈ HT.eigSp ρ τ` using `HT.LatBasic.mem_eigSp.2 fun a => by`. Rewrite using `[hρ, smul_eq_mul]`. Establish `hP : HT.eigProj ρ σ 1 = ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E)`.

Simplify using `[HT.eigProj, LinearMap.sum_apply, hρ]`. Rewrite using `[← hP]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `HT.LatBasic.eigProj_of_mem hmem`.

Conclude with `HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem`.
-/
theorem sum_dual_mul (σ τ : E →+* ℂ) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End ℂ ℂ :=
    (Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : ℂ) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

/- English proof (translation)
Use `trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)` as an intermediate fact. Simplify using `using this`.
-/
theorem trace_cast (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ z := by
  have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  simpa using this

end Embeddings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Take `⟨hT, -⟩` from `GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D`. Establish `e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) + (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hh X Y` using `[wK]`. Establish `t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y)`.

Use `congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)` as an intermediate fact. Simplify using `only [trace_cast, map_mul] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)`.

Establish `h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ)` using `by simpa using hT 1 X Y`. Rewrite using `[← trace_cast, h1]`. Simplify using the standard rewrite rules. Establish `hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) = ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) + (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E)`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun τ _ => by ring`. Rewrite using `[e1, map_add, map_mul, map_intCast, map_intCast, hκ, hs]`. Use `push_cast`. Rewrite using `[t1, t0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kappa_form {ε : ℤˣ} {h : D.La → D.La → OK H} {σ : E →+* ℂ} {κ : OK H →+* ℂ}
    (hh : IsKForm D ε h) (hκ : κ (wK H) = σ (H.w0 : E)) (X Y : D.La) :
    κ (h X Y) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) := by
  obtain ⟨hT, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) +
      (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H := by
    apply Subtype.ext
    simpa [wK] using hh X Y
  have t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)
    simp only [trace_cast, map_mul] at this
    rw [this]
    simp
  have t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) := by
    have h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ) := by simpa using hT 1 X Y
    rw [← trace_cast, h1]
    simp
  have hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) +
        (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e1, map_add, map_mul, map_intCast, map_intCast, hκ, hs]
  push_cast
  rw [t1, t0]
  ring

/- English proof (translation)
Introduce `E _ _ _ H D ε h σ κ n e x y hh hκ`. Take `⟨-, -, -, hL, hR, -⟩` from `GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D`. Establish `hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) * (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)))`. Introduce `a c`. Rewrite using `[kappa_form hh hκ]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E))` using `IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)`. Rewrite using `[hL, hR, map_mul, map_mul, hc]`. Expand and normalize the polynomial expressions, which then agree.

Use `set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ => ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef`. Establish `hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0`. Introduce `τ`. Use `sum_dual_mul σ (τ : E →+* ℂ)` as an intermediate fact. Rewrite `this` using `[← Equiv.sum_comp e]`.

Conclude with `this`. Use `set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ => τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef`. Establish `hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ`. Simplify using `only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_congr rfl fun k _ => Finset.sum_comm]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hexp, Finset.sum_eq_single σ.toRatAlgHom]`. Establish `h1 : S σ.toRatAlgHom = 1`. Rewrite using `[hS]`. Conclude with `if_pos (RingHom.ext fun _ => rfl)`. Establish `h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1`.

Establish `h3` using `congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root`. Simplify using `only [map_mul, map_add, map_one, map_ofNat] at h3`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]`. Take the linear combination `-h3`. Rewrite using `[h1, map_one, map_mul, h2]`.

Simplify using `only [hcdef]`. Express the relevant statement in the definitionally equal form `_ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _`. Expand and normalize the polynomial expressions, which then agree. Introduce `τ _ hτ`. Establish `h0 : S τ = 0`.

Rewrite using `[hS]`. Use `if_neg fun hc => hτ (AlgHom.ext fun z => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun f : E →+* ℂ => f z) hc`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.
-/
theorem sigma_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  classical
  intro E _ _ _ H D ε h σ κ n e x y hh hκ
  obtain ⟨-, -, -, hL, hR, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D

  have hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) *
        (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E))) := by
    intro a c
    rw [kappa_form hh hκ]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E)) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)
    rw [hL, hR, map_mul, map_mul, hc]
    ring

  set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef
  have hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0 := by
    intro τ
    have := sum_dual_mul σ (τ : E →+* ℂ)
    rw [← Equiv.sum_comp e] at this
    exact this
  set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef
  have hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) *
        κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) *
        starRingEnd ℂ (σ (HT.dualInt E (e k'))) =
      ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ := by
    simp only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, Finset.sum_eq_single σ.toRatAlgHom]
  · have h1 : S σ.toRatAlgHom = 1 := by
      rw [hS]
      exact if_pos (RingHom.ext fun _ => rfl)
    have h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1 := by
      have h3 := congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add, map_one, map_ofNat] at h3
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
      linear_combination -h3
    rw [h1, map_one, map_mul, h2]
    simp only [hcdef]
    change _ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _
    ring
  · intro τ _ hτ
    have h0 : S τ = 0 := by
      rw [hS]
      refine if_neg fun hc => hτ (AlgHom.ext fun z => ?_)
      exact congrArg (fun f : E →+* ℂ => f z) hc
    rw [h0]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end GlobalTheory.CompanionTheory.Ar.Fl.KForm
