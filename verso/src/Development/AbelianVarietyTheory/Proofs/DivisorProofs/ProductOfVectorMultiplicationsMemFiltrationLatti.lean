import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

/- English proof (translation)
Simplify using `[word, List.ofFn_succ]`.
-/
theorem word_succ {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    {t : ℕ} (u : Fin (t + 1) → Fin N → K) : word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

/- English proof (translation)
Simplify using `[word]`.
-/
theorem word_zero {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by
  simp [word]

/- English proof (translation)
Establish `key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1)`. Introduce `m hm u`. Establish `hu : u ∈ Submodule.span F (Set.range S.w.col)` using `hS.lat.spans ▸ Submodule.mem_top`. Set `L : (Fin S.N → F) →ₗ[F] A` to `(LinearMap.applyₗ (m : A)) ∘ₗ S.mul`. Establish `hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨g, -, hg⟩` from `hS.stable j hj k m hm`. Use `show L (S.w.col k) ∈ S.V (j + 1)`. Simplify using `only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]`.

Rewrite using `[← hg]`. Conclude with `g.2`. Conclude with `hle hu`. Set `P : Submodule F (S.V j)` to `(S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)`. Establish `hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P`.

Rewrite using `[Submodule.span_le]`. Introduce `m hm`. Conclude with `key m hm u`. Establish `hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j))` using `(hS.full j hj.le).span ▸ Submodule.mem_top`. Conclude with `hP hx'`.
-/
theorem mul_mem_V_succ (S : Sys F A) (hS : S.Hyp) {j : ℕ} (hj : j < S.T) (u : Fin S.N → F) {x : A} (hx : x ∈ S.V j) :
    S.mul u x ∈ S.V (j + 1) := by
  have key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1) := by
    intro m hm u
    have hu : u ∈ Submodule.span F (Set.range S.w.col) := hS.lat.spans ▸ Submodule.mem_top
    let L : (Fin S.N → F) →ₗ[F] A := (LinearMap.applyₗ (m : A)) ∘ₗ S.mul
    have hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, -, hg⟩ := hS.stable j hj k m hm
      show L (S.w.col k) ∈ S.V (j + 1)
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]
      rw [← hg]
      exact g.2
    exact hle hu
  let P : Submodule F (S.V j) := (S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)
  have hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P := by
    rw [Submodule.span_le]
    intro m hm
    exact key m hm u
  have hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j)) :=
    (hS.full j hj.le).span ▸ Submodule.mem_top
  exact hP hx'

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Use `⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩` and prove the remaining obligations. Simplify `hx` using `[word_zero]`. Simplify using `[word_zero]`.

Consider the case `succ t ih`. Take `⟨ih1, ih2⟩` from `ih (by omega)`. Establish `hlt : j + t < S.T` using `by omega`. Use `⟨fun u x hx => ?_, fun e x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[word_succ, Module.End.mul_apply]`.

Conclude with `mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)`. Take `⟨g', hg', hg'e⟩` from `ih2 (fun i => e i.succ) x hx`. Take `⟨g, hg, hge⟩` from `hS.stable (j + t) hlt (e 0) g' hg'`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[word_succ, Module.End.mul_apply, hge, hg'e]`.
-/
theorem word_mem (S : Sys F A) (hS : S.Hyp) (j t : ℕ) (hjt : j + t ≤ S.T) :
    (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧
      ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  induction t with
  | zero =>
    refine ⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩
    · simpa [word_zero] using hx
    · simp [word_zero]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : j + t < S.T := by omega
    refine ⟨fun u x hx => ?_, fun e x hx => ?_⟩
    · rw [word_succ, Module.End.mul_apply]
      exact mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)
    · obtain ⟨g', hg', hg'e⟩ := ih2 (fun i => e i.succ) x hx
      obtain ⟨g, hg, hge⟩ := hS.stable (j + t) hlt (e 0) g' hg'
      refine ⟨g, hg, ?_⟩
      rw [word_succ, Module.End.mul_apply, hge, hg'e]

end GlobalTheory.HSShort.Sys

namespace GlobalTheory.HSShort

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ S hS j t hjt` and use `S.word_mem hS j t hjt`.
-/
theorem wordMem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x :=
  fun _ _ _ _ _ _ _ _ S hS j t hjt => S.word_mem hS j t hjt

end GlobalTheory.HSShort
