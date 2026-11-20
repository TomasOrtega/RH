import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis Filter Topology

noncomputable section

namespace GlobalTheory.FinSchrIrred

section General

variable {X : Type} [TopologicalSpace X]

def mult (N : Submodule ℂ (X → ℂ)) : Subalgebra ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ ∀ g ∈ N, f * g ∈ N}
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun g hg => by rw [mul_assoc]; exact ha.2 _ (hb.2 g hg)⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g hg => by rw [add_mul]; exact N.add_mem (ha.2 g hg) (hb.2 g hg)⟩
  algebraMap_mem' := fun c => ⟨IsLocallyConstant.const c, fun g hg => by
    rw [← Algebra.smul_def]; exact N.smul_mem c hg⟩

variable (A : Subalgebra ℂ (X → ℂ)) (hA : ∀ f ∈ A, IsLocallyConstant f)
  (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)

include hA hsep

/- English proof (translation)
Use `hC.induction_on (p := fun s => ∃ e ∈ A, e x = 1 ∧ ∀ y ∈ s, e y = 0) ⟨1, A.one_mem, rfl, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `s t hst ⟨e, he, h1, h0⟩`. Conclude with `⟨e, he, h1, fun y hy => h0 y (hst hy)⟩`. Introduce and unpack `s t ⟨e, he, h1, h0⟩ ⟨e', he', h1', h0'⟩`. Use `⟨e * e', A.mul_mem he he', by simp [h1, h1'], ?_⟩` and prove the remaining obligations.

Introduce and unpack `y (hy | hy)`. Simplify using `[h0 y hy]`. Simplify using `[h0' y hy]`. Introduce `y hy`. Take `⟨f, hf, hne⟩` from `hsep x y (fun h => hx (h ▸ hy))`.

Use `⟨{z | f z = f y}, mem_nhdsWithin_of_mem_nhds (((hA f hf).isOpen_fiber _).mem_nhds rfl), (f x - f y)⁻¹ • (f - algebraMap ℂ (X → ℂ) (f y)), A.smul_mem (A.sub_mem hf (A.algebraMap_mem _)) _, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using inv_mul_cancel₀ (sub_ne_zero.2 hne)`. Introduce `z hz`. Establish `hz' : f z = f y` using `hz`. Simplify using `[hz']`.
-/
theorem exists_one_zero (x : X) {C : Set X} (hC : IsCompact C) (hx : x ∉ C) :
    ∃ e ∈ A, e x = 1 ∧ ∀ y ∈ C, e y = 0 := by
  refine hC.induction_on (p := fun s => ∃ e ∈ A, e x = 1 ∧ ∀ y ∈ s, e y = 0) ⟨1, A.one_mem, rfl, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨e, he, h1, h0⟩
    exact ⟨e, he, h1, fun y hy => h0 y (hst hy)⟩
  · rintro s t ⟨e, he, h1, h0⟩ ⟨e', he', h1', h0'⟩
    refine ⟨e * e', A.mul_mem he he', by simp [h1, h1'], ?_⟩
    rintro y (hy | hy)
    · simp [h0 y hy]
    · simp [h0' y hy]
  · intro y hy
    obtain ⟨f, hf, hne⟩ := hsep x y (fun h => hx (h ▸ hy))
    refine ⟨{z | f z = f y}, mem_nhdsWithin_of_mem_nhds (((hA f hf).isOpen_fiber _).mem_nhds rfl),
      (f x - f y)⁻¹ • (f - algebraMap ℂ (X → ℂ) (f y)), A.smul_mem (A.sub_mem hf (A.algebraMap_mem _)) _, ?_, ?_⟩
    · simpa using inv_mul_cancel₀ (sub_ne_zero.2 hne)
    · intro z hz
      have hz' : f z = f y := hz
      simp [hz']

/- English proof (translation)
Establish `key : ∃ e ∈ A, ∃ g ∈ A, (∀ y ∈ K, e y = 1) ∧ ∀ y ∈ K, g y = e y * φ y`. Use `hK.induction_on (p := fun s => ∃ e ∈ A, ∃ g ∈ A, (∀ y ∈ s, e y = 1) ∧ ∀ y ∈ K, g y = e y * φ y) ⟨0, A.zero_mem, 0, A.zero_mem, by simp, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `s t hst ⟨e, he, g, hg, h1, h0⟩`. Conclude with `⟨e, he, g, hg, fun y hy => h1 y (hst hy), h0⟩`. Introduce and unpack `s t ⟨e, he, g, hg, h1, h0⟩ ⟨e', he', g', hg', h1', h0'⟩`.

Use `⟨e + (1 - e) * e', A.add_mem he (A.mul_mem (A.sub_mem A.one_mem he) he'), g + (1 - e) * g', A.add_mem hg (A.mul_mem (A.sub_mem A.one_mem he) hg'), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `y (hy | hy)`. Simplify using `[h1 y hy]`. Simplify using `[h1' y hy]`. Introduce `y hy`.

Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, h0 y hy, h0' y hy]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x _`. Take `⟨e, he, h1, h0⟩` from `exists_one_zero A hA hsep x (hK.diff (hφ.isOpen_fiber (φ x))) (fun h => h.2 rfl)`. Use `⟨{z | e z = 1}, mem_nhdsWithin_of_mem_nhds (((hA e he).isOpen_fiber _).mem_nhds h1), e, he, φ x • e, A.smul_mem he _, fun y hy => hy, fun y hy => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : φ y = φ x`. Simplify using `[h, mul_comm]`. Simplify using `[h0 y ⟨hy, h⟩]`. Take `⟨e, -, g, hg, h1, h0⟩` from `key`. Conclude with `⟨g, hg, fun y hy => by rw [h0 y hy, h1 y hy, one_mul]⟩`.
-/
theorem exists_eqOn {φ : X → ℂ} (hφ : IsLocallyConstant φ) {K : Set X} (hK : IsCompact K) :
    ∃ f ∈ A, ∀ y ∈ K, f y = φ y := by
  have key : ∃ e ∈ A, ∃ g ∈ A, (∀ y ∈ K, e y = 1) ∧ ∀ y ∈ K, g y = e y * φ y := by
    refine hK.induction_on (p := fun s => ∃ e ∈ A, ∃ g ∈ A, (∀ y ∈ s, e y = 1) ∧ ∀ y ∈ K, g y = e y * φ y)
      ⟨0, A.zero_mem, 0, A.zero_mem, by simp, by simp⟩ ?_ ?_ ?_
    · rintro s t hst ⟨e, he, g, hg, h1, h0⟩
      exact ⟨e, he, g, hg, fun y hy => h1 y (hst hy), h0⟩
    · rintro s t ⟨e, he, g, hg, h1, h0⟩ ⟨e', he', g', hg', h1', h0'⟩
      refine ⟨e + (1 - e) * e', A.add_mem he (A.mul_mem (A.sub_mem A.one_mem he) he'),
        g + (1 - e) * g', A.add_mem hg (A.mul_mem (A.sub_mem A.one_mem he) hg'), ?_, ?_⟩
      · rintro y (hy | hy)
        · simp [h1 y hy]
        · simp [h1' y hy]
      · intro y hy
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, h0 y hy, h0' y hy]
        ring
    · intro x _
      obtain ⟨e, he, h1, h0⟩ := exists_one_zero A hA hsep x (hK.diff (hφ.isOpen_fiber (φ x))) (fun h => h.2 rfl)
      refine ⟨{z | e z = 1}, mem_nhdsWithin_of_mem_nhds (((hA e he).isOpen_fiber _).mem_nhds h1),
        e, he, φ x • e, A.smul_mem he _, fun y hy => hy, fun y hy => ?_⟩
      by_cases h : φ y = φ x
      · simp [h, mul_comm]
      · simp [h0 y ⟨hy, h⟩]
  obtain ⟨e, -, g, hg, h1, h0⟩ := key
  exact ⟨g, hg, fun y hy => by rw [h0 y hy, h1 y hy, one_mul]⟩

omit hA hsep in

/- English proof (translation)
Take `⟨f, hf, he⟩` from `exists_eqOn (mult N) (fun f hf => hf.1) hs hφ (hN hg).2.isCompact`. Establish `: φ * g = f * g`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ tsupport g`. Simplify using `[he y hy]`.

Simplify using `[image_eq_zero_of_notMem_tsupport hy]`. Rewrite using `[this]`. Conclude with `hf.2 g hg`.
-/
theorem mul_mem_of_sep (N : Submodule ℂ (X → ℂ)) (hN : N ≤ SB X)
    (hs : ∀ x y : X, x ≠ y → ∃ f ∈ mult N, f x ≠ f y) {φ : X → ℂ} (hφ : IsLocallyConstant φ) {g : X → ℂ}
    (hg : g ∈ N) : φ * g ∈ N := by
  obtain ⟨f, hf, he⟩ := exists_eqOn (mult N) (fun f hf => hf.1) hs hφ (hN hg).2.isCompact
  have : φ * g = f * g := by
    funext y
    by_cases hy : y ∈ tsupport g
    · simp [he y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [this]
  exact hf.2 g hg

omit hA hsep in

/- English proof (translation)
Use `le_antisymm hN fun h hh => ?_` and prove the remaining obligations. Establish `key : ∃ e ∈ N, ∀ y ∈ tsupport h, e y = 1`. Use `hh.2.isCompact.induction_on (p := fun s => ∃ e ∈ N, ∀ y ∈ s, e y = 1) ⟨0, N.zero_mem, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `s t hst ⟨e, he, h1⟩`. Conclude with `⟨e, he, fun y hy => h1 y (hst hy)⟩`.

Introduce and unpack `s t ⟨e, he, h1⟩ ⟨e', he', h1'⟩`. Use `⟨e + (1 - e) * e', N.add_mem he (mul_mem_of_sep N hN hs ((IsLocallyConstant.const 1).sub (hN he).1) he'), ?_⟩` and prove the remaining obligations. Introduce and unpack `y (hy | hy)`. Simplify using `[h1 y hy]`. Simplify using `[h1' y hy]`.

Introduce `x _`. Take `⟨g, hg, hx⟩` from `hz x`. Use `⟨{z | g z = g x}, mem_nhdsWithin_of_mem_nhds (((hN hg).1.isOpen_fiber _).mem_nhds rfl), (g x)⁻¹ • g, N.smul_mem _ hg, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : g y = g x` using `hy`. Simplify `inv_mul_cancel₀ hx` using `[hy']`.

Take `⟨e, he, h1⟩` from `key`. Establish `: h = h * e`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ tsupport h`. Simplify using `[h1 y hy]`.

Simplify using `[image_eq_zero_of_notMem_tsupport hy]`. Rewrite using `[this]`. Conclude with `mul_mem_of_sep N hN hs hh.1 he`.
-/
theorem eq_SB_of_sep (N : Submodule ℂ (X → ℂ)) (hN : N ≤ SB X)
    (hs : ∀ x y : X, x ≠ y → ∃ f ∈ mult N, f x ≠ f y) (hz : ∀ x : X, ∃ g ∈ N, g x ≠ 0) : N = SB X := by
  refine le_antisymm hN fun h hh => ?_
  have key : ∃ e ∈ N, ∀ y ∈ tsupport h, e y = 1 := by
    refine hh.2.isCompact.induction_on (p := fun s => ∃ e ∈ N, ∀ y ∈ s, e y = 1) ⟨0, N.zero_mem, by simp⟩ ?_ ?_ ?_
    · rintro s t hst ⟨e, he, h1⟩
      exact ⟨e, he, fun y hy => h1 y (hst hy)⟩
    · rintro s t ⟨e, he, h1⟩ ⟨e', he', h1'⟩
      refine ⟨e + (1 - e) * e', N.add_mem he
        (mul_mem_of_sep N hN hs ((IsLocallyConstant.const 1).sub (hN he).1) he'), ?_⟩
      rintro y (hy | hy)
      · simp [h1 y hy]
      · simp [h1' y hy]
    · intro x _
      obtain ⟨g, hg, hx⟩ := hz x
      refine ⟨{z | g z = g x}, mem_nhdsWithin_of_mem_nhds (((hN hg).1.isOpen_fiber _).mem_nhds rfl),
        (g x)⁻¹ • g, N.smul_mem _ hg, fun y hy => ?_⟩
      have hy' : g y = g x := hy
      simpa [hy'] using inv_mul_cancel₀ hx
  obtain ⟨e, he, h1⟩ := key
  have : h = h * e := by
    funext y
    by_cases hy : y ∈ tsupport h
    · simp [h1 y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [this]
  exact mul_mem_of_sep N hN hs hh.1 he

end General

/- English proof (translation)
Take `⟨i, hi⟩ : ∃ i, z i ≠ 0` from `Function.ne_iff.1 hz`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, evalV F v (z i) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hi (GlobalTheory.AdelicU.af_ext fun u => by rw [h u, map_zero])`.

Take `⟨t, ht⟩` from `hnt v`. Use `⟨Pi.single i (GlobalTheory.AdelicU.singleFin v ((evalV F v (z i))⁻¹ * t)), ?_⟩` and prove the remaining obligations. Establish `: z ⬝ᵥ Pi.single i (GlobalTheory.AdelicU.singleFin v ((evalV F v (z i))⁻¹ * t)) = GlobalTheory.AdelicU.singleFin v t`. Rewrite using `[dotProduct_single]`. Use `GlobalTheory.AdelicU.af_ext fun u => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, mul_inv_cancel_left₀ hv]`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]`.

Rewrite using `[this]`. Conclude with `ht`.
-/
theorem exists_pair_ne_one {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (hnt : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1) {z : κ → Af F} (hz : z ≠ 0) :
    ∃ b : κ → Af F, ψ (finA F (z ⬝ᵥ b)) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := Function.ne_iff.1 hz
  obtain ⟨v, hv⟩ : ∃ v, evalV F v (z i) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (GlobalTheory.AdelicU.af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hnt v
  refine ⟨Pi.single i (GlobalTheory.AdelicU.singleFin v ((evalV F v (z i))⁻¹ * t)), ?_⟩
  have : z ⬝ᵥ Pi.single i (GlobalTheory.AdelicU.singleFin v ((evalV F v (z i))⁻¹ * t)) = GlobalTheory.AdelicU.singleFin v t := by
    rw [dotProduct_single]
    refine GlobalTheory.AdelicU.af_ext fun u => ?_
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, mul_inv_cancel_left₀ hv]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
  rw [this]
  exact ht

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ hnt N hN hst`. Use `or_iff_not_imp_left.2 fun hne => eq_SB_of_sep N hN ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Take `⟨b, hb⟩` from `exists_pair_ne_one ψ hnt (sub_ne_zero.2 hxy)`. Use `⟨fun z => GlobalTheory.HeisSchA.finChar ψ (z ⬝ᵥ b), ⟨(GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).comp_continuous (continuous_id.dotProduct continuous_const), fun g hg => ?_⟩, fun h => hb ?_⟩` and prove the remaining obligations.

Use `hst 0 b g hg` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using `only [heisFin, add_zero, Pi.mul_apply]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `GlobalTheory.HeisSchA.finChar ψ ((x - y) ⬝ᵥ b) = 1`. Establish `h' : GlobalTheory.HeisSchA.finChar ψ (x ⬝ᵥ b) = GlobalTheory.HeisSchA.finChar ψ (y ⬝ᵥ b)` using `h`. Rewrite using `[sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul, h', ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Introduce `x`. Take `⟨g, hg, hg0⟩` from `(Submodule.ne_bot_iff N).1 hne`.

Take `⟨y, hy⟩ : ∃ y, g y ≠ 0` from `Function.ne_iff.1 hg0`. Use `⟨_, hst (y - x) 0 g hg, ?_⟩` and prove the remaining obligations. Establish `h0 : finA F 0 = 0` using `rfl`. Simplify `hy` using `[heisFin, h0]`.
-/
theorem schrodinger_irreducible : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    Continuous ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1) →
    ∀ N : Submodule ℂ ((κ → Af F) → ℂ), N ≤ SB (κ → Af F) →
      (∀ (a b : κ → Af F), ∀ g ∈ N, heisFin F ψ a b g ∈ N) → N = ⊥ ∨ N = SB (κ → Af F) := by
  intro F _ _ κ _ ψ hψ hnt N hN hst
  refine or_iff_not_imp_left.2 fun hne => eq_SB_of_sep N hN ?_ ?_
  · intro x y hxy
    obtain ⟨b, hb⟩ := exists_pair_ne_one ψ hnt (sub_ne_zero.2 hxy)
    refine ⟨fun z => GlobalTheory.HeisSchA.finChar ψ (z ⬝ᵥ b), ⟨(GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).comp_continuous
      (continuous_id.dotProduct continuous_const), fun g hg => ?_⟩, fun h => hb ?_⟩
    · have := hst 0 b g hg
      convert this using 1
      funext z
      simp only [heisFin, add_zero, Pi.mul_apply]
      rfl
    · change GlobalTheory.HeisSchA.finChar ψ ((x - y) ⬝ᵥ b) = 1
      have h' : GlobalTheory.HeisSchA.finChar ψ (x ⬝ᵥ b) = GlobalTheory.HeisSchA.finChar ψ (y ⬝ᵥ b) := h
      rw [sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul, h', ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
  · intro x
    obtain ⟨g, hg, hg0⟩ := (Submodule.ne_bot_iff N).1 hne
    obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := Function.ne_iff.1 hg0
    refine ⟨_, hst (y - x) 0 g hg, ?_⟩
    have h0 : finA F 0 = 0 := rfl
    simpa [heisFin, h0] using hy

end GlobalTheory.FinSchrIrred
