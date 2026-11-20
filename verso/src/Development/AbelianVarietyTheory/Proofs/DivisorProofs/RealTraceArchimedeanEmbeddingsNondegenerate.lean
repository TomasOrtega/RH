import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfTraceNondeg

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Conclude with `InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm x)`.
-/
theorem norm_algebraMap_apply (x : K) (v : InfinitePlace K) :
    ‖(algebraMap K (InfiniteAdeleRing K) x) v‖ = v x := by
  exact InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm x)

/- English proof (translation)
Establish `hc1 : Continuous fun a => ‖χ a‖` using `hχ.norm`. Establish `hc2 : Continuous fun a : InfiniteAdeleRing K => ‖a (InfinitePlace.mk φ)‖` using `(continuous_apply (InfinitePlace.mk φ)).norm`. Use `congrFun ((InfiniteAdeleRing.denseRange_algebraMap K).equalizer hc1 hc2 (funext fun x => ?_)) a` and prove the remaining obligations. Simplify using `only [Function.comp, h, norm_algebraMap_apply, InfinitePlace.apply]`.
-/
theorem norm_eq_of_cont (χ : InfiniteAdeleRing K →+* ℂ) (hχ : Continuous χ) (φ : K →+* ℂ)
    (h : ∀ x, χ (algebraMap K _ x) = φ x) (a : InfiniteAdeleRing K) :
    ‖χ a‖ = ‖a (InfinitePlace.mk φ)‖ := by
  have hc1 : Continuous fun a => ‖χ a‖ := hχ.norm
  have hc2 : Continuous fun a : InfiniteAdeleRing K => ‖a (InfinitePlace.mk φ)‖ :=
    (continuous_apply (InfinitePlace.mk φ)).norm
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap K).equalizer hc1 hc2 (funext fun x => ?_)) a
  simp only [Function.comp, h, norm_algebraMap_apply, InfinitePlace.apply]

end GlobalTheory.InfTraceNondeg

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (D : D7) (ρ : D.what₂.Tau) : Formalism.MainNotions.StandardLattice.embOf D ρ = tauE D ρ := rfl

namespace GlobalTheory.InfTraceNondeg

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D θ hθ a ha`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, a v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `ha (funext h)`.

Take `⟨w, hw⟩` from `InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v`. Take `⟨ρ, hρ⟩` from `(GlobalTheory.VolRatioCheck.place_bijective D).2 w`. Set `χ : D.what₂.Tau → (Ainf D.host.F →+* ℂ)` to `fun σ => (θ σ).comp Algebra.TensorProduct.includeLeftRingHom`. Establish `hχapp : ∀ σ c, χ σ c = θ σ (c ⊗ₜ[D.host.F] (1 : D.host.E))` using `fun _ _ => rfl`. Establish `hχalg : ∀ σ (x : D.host.F), χ σ (algebraMap D.host.F (Ainf D.host.F) x) = ((tauE D σ).comp (algebraMap D.host.F D.host.E)) x`.

Introduce `σ x`. Rewrite using `[hχapp, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', (hθ σ).1]`. Both sides reduce to the same expression. Establish `hnorm : ∀ σ c, ‖χ σ c‖ = ‖c (InfinitePlace.mk ((tauE D σ).comp (algebraMap D.host.F D.host.E)))‖` using `fun σ c => norm_eq_of_cont (χ σ) (hθ σ).2 _ (hχalg σ) c`. Establish `hmul : ∀ x y : Ainf D.host.F, ∀ u, (x * y) u = x u * y u` using `fun _ _ _ => rfl`.

Use `set e : Ainf D.host.F := Pi.single v 1 with he`. Use `set b : Ainf D.host.F := Pi.single v (a v)⁻¹ with hb`. Establish `hab : a * b = e`. Use function extensionality and compare the values at `u`. Rewrite using `[hmul]`.

Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Simplify using `[he, hb, hv]`. Simplify using `[he, hb, Pi.single_apply, hu]`. Establish `hee : e * e = e`.

Use function extensionality and compare the values at `u`. Rewrite using `[hmul]`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Simplify using `[he]`.

Simplify using `[he, Pi.single_apply, hu]`. Establish `hidem : ∀ σ, χ σ e = 0 ∨ χ σ e = 1`. Introduce `σ`. Establish `h1 : χ σ e * χ σ e = χ σ e` using `by rw [← map_mul, hee]`. Establish `h2 : χ σ e * (χ σ e - 1) = 0` using `by rw [mul_sub, h1, mul_one, sub_self]`.

Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (sub_eq_zero.mp h)`. Establish `hplace : InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E)) = v`. Rewrite using `[← InfinitePlace.comap_mk]`.

Express the relevant statement in the definitionally equal form `(InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ)).comap _ = v`. Establish `hρ' : InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ) = w` using `hρ`. Establish `hw' : w.comap (algebraMap D.host.F D.host.E) = v` using `hw`. Rewrite using `[hρ', hw']`. Establish `hρ1 : χ ρ e = 1`.

Break down `hidem ρ with h | h` into its components or cases. It suffices to derive a contradiction. Use `hnorm ρ e` as an intermediate fact. Rewrite `this` using `[h, hplace, he, Pi.single_eq_same, norm_zero, norm_one]`. Conclude with `zero_ne_one this`.

Conclude with `h`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hab, Complex.re_sum]`. Establish `hterm : ∀ σ, 0 ≤ (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re`. Introduce `σ`.

Rewrite using `[← hχapp]`. Apply the tactic sequence `rcases hidem σ with h | h <;> simp [h]`. Establish `hge : (θ ρ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re ≤ ∑ σ, (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re` using `Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ ρ)`. Rewrite `hge` using `[← hχapp, hρ1, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem realTrace_nondeg : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  intro D θ hθ a ha
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 w
  let χ : D.what₂.Tau → (Ainf D.host.F →+* ℂ) := fun σ =>
    (θ σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hχapp : ∀ σ c, χ σ c = θ σ (c ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ _ => rfl
  have hχalg : ∀ σ (x : D.host.F), χ σ (algebraMap D.host.F (Ainf D.host.F) x) =
      ((tauE D σ).comp (algebraMap D.host.F D.host.E)) x := by
    intro σ x
    rw [hχapp, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', (hθ σ).1]
    rfl
  have hnorm : ∀ σ c, ‖χ σ c‖ = ‖c (InfinitePlace.mk ((tauE D σ).comp (algebraMap D.host.F D.host.E)))‖ :=
    fun σ c => norm_eq_of_cont (χ σ) (hθ σ).2 _ (hχalg σ) c
  have hmul : ∀ x y : Ainf D.host.F, ∀ u, (x * y) u = x u * y u := fun _ _ _ => rfl
  set e : Ainf D.host.F := Pi.single v 1 with he
  set b : Ainf D.host.F := Pi.single v (a v)⁻¹ with hb
  have hab : a * b = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu
      simp [he, hb, hv]
    · simp [he, hb, Pi.single_apply, hu]
  have hee : e * e = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu; simp [he]
    · simp [he, Pi.single_apply, hu]
  have hidem : ∀ σ, χ σ e = 0 ∨ χ σ e = 1 := by
    intro σ
    have h1 : χ σ e * χ σ e = χ σ e := by rw [← map_mul, hee]
    have h2 : χ σ e * (χ σ e - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hplace : InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E)) = v := by
    rw [← InfinitePlace.comap_mk]
    change (InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ)).comap _ = v
    have hρ' : InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ) = w := hρ
    have hw' : w.comap (algebraMap D.host.F D.host.E) = v := hw
    rw [hρ', hw']
  have hρ1 : χ ρ e = 1 := by
    rcases hidem ρ with h | h
    · exfalso
      have := hnorm ρ e
      rw [h, hplace, he, Pi.single_eq_same, norm_zero, norm_one] at this
      exact zero_ne_one this
    · exact h
  refine ⟨b, ?_⟩
  rw [hab, Complex.re_sum]
  have hterm : ∀ σ, 0 ≤ (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re := by
    intro σ
    rw [← hχapp]
    rcases hidem σ with h | h <;> simp [h]
  have hge : (θ ρ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re ≤ ∑ σ, (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re :=
    Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ ρ)
  rw [← hχapp, hρ1, Complex.one_re] at hge
  linarith

end GlobalTheory.InfTraceNondeg
