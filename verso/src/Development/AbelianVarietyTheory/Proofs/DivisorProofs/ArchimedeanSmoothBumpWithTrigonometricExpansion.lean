import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealAlgSep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchTrigBump

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RealAlgebraCharacters.main`. Consider the case `exact _root_.GlobalTheory.RealAlgebraCharacters.main`. Consider the case `(apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RealAlgebraCharacters.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RealAlgebraCharacters.main ..)`.
-/
theorem exists_bounded_trig {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type} [AddCommGroup B]
    (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b)) (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (hzero : ∀ x, χ 0 x = 1) (hnorm : ∀ a x, ‖χ a x‖ = 1) (hsep : ∀ x y, x ≠ y → ∃ b, χ b x ≠ χ b y)
    (β : X → ℝ) (hβ : Continuous β) (h01 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ), (∀ n x, ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * χ b x) Filter.atTop (nhds (β x : ℂ)) := by
  first
  | exact @_root_.GlobalTheory.RealAlgebraCharacters.main
  | exact _root_.GlobalTheory.RealAlgebraCharacters.main
  | (apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealAlgebraCharacters.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealAlgebraCharacters.main ..)

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.
-/
theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

/- English proof (translation)
Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`.
-/
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

open scoped Classical in

/- English proof (translation)
Set `w : mixedEmbedding.mixedSpace F` to `(fun v => (u.1 v)⁻¹, fun v => (u.2 v)⁻¹)`. Establish `h1 : u * w * u = u`. Use `Prod.ext (funext fun v => ?_) (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 v * (u.1 v)⁻¹ * u.1 v = u.1 v`. Conclude with `mul_inv_mul_cancel _`.

Express the relevant statement in the definitionally equal form `u.2 v * (u.2 v)⁻¹ * u.2 v = u.2 v`. Conclude with `mul_inv_mul_cancel _`. Establish `h2 : IsIdempotentElem (u * w)`. Express the relevant statement in the definitionally equal form `u * w * (u * w) = u * w`. Rewrite using `[← mul_assoc, h1]`.

Use `⟨w, fun h => hu ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Algebra.trace_apply]`. Establish `h3` using `(LinearMap.IsIdempotentElem.trace_eq_zero_iff (h2.map (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F)))).1 h`. Establish `h4` using `LinearMap.congr_fun h3 u`. Simplify using `only [LinearMap.zero_apply] at h4`.

Rewrite using `[← h1]`. Conclude with `h4`.
-/
theorem exists_trace_mul_ne_zero (u : mixedEmbedding.mixedSpace F) (hu : u ≠ 0) :
    ∃ w, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u * w) ≠ 0 := by
  let w : mixedEmbedding.mixedSpace F := (fun v => (u.1 v)⁻¹, fun v => (u.2 v)⁻¹)
  have h1 : u * w * u = u := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · change u.1 v * (u.1 v)⁻¹ * u.1 v = u.1 v
      exact mul_inv_mul_cancel _
    · change u.2 v * (u.2 v)⁻¹ * u.2 v = u.2 v
      exact mul_inv_mul_cancel _
  have h2 : IsIdempotentElem (u * w) := by
    change u * w * (u * w) = u * w
    rw [← mul_assoc, h1]
  refine ⟨w, fun h => hu ?_⟩
  rw [Algebra.trace_apply] at h
  have h3 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff
    (h2.map (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F)))).1 h
  have h4 := LinearMap.congr_fun h3 u
  simp only [LinearMap.zero_apply] at h4
  rw [← h1]
  exact h4

open scoped Classical in

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.1 hxy`. Take `⟨w, hw⟩` from `exists_trace_mul_ne_zero (x i - y i) (sub_ne_zero.2 hi)`. Use `set t := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((x i - y i) * w) with ht`. Use `⟨Pi.single i ((2 * t)⁻¹ • w), fun h => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[dotProduct_single, dotProduct_single]`.

Establish `h1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y i * ((2 * t)⁻¹ • w)) = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) - 1 / 2`. Establish `: (2 * t)⁻¹ * t = 1 / 2` using `by field_simp`. Rewrite using `[← this, mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]`. Use `congr 1`. Rewrite using `[ht, sub_mul, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h1]`. Generalize the expression as in `Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) = a at h`. Establish `h2 : -(2 * Real.pi * Complex.I) * ((a - 1 / 2 : ℝ) : ℂ) = -(2 * Real.pi * Complex.I) * (a : ℂ) + Real.pi * Complex.I` using `by push_cast; ring`. Rewrite `h` using `[h2, Complex.exp_add, Complex.exp_pi_mul_I]`.

Establish `h3` using `Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (a : ℂ))`. Apply `h3` to reduce the goal to its premises. Take the linear combination `h / 2`.
-/
theorem exists_char_ne {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) (hxy : x ≠ y) :
    ∃ w : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w) : ℝ)) ≠
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ w) : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  obtain ⟨w, hw⟩ := exists_trace_mul_ne_zero (x i - y i) (sub_ne_zero.2 hi)
  set t := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((x i - y i) * w) with ht
  refine ⟨Pi.single i ((2 * t)⁻¹ • w), fun h => ?_⟩
  rw [dotProduct_single, dotProduct_single] at h
  have h1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y i * ((2 * t)⁻¹ • w)) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) - 1 / 2 := by
    have : (2 * t)⁻¹ * t = 1 / 2 := by field_simp
    rw [← this, mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    congr 1
    rw [ht, sub_mul, map_sub]
    ring
  rw [h1] at h
  generalize Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) = a at h
  have h2 : -(2 * Real.pi * Complex.I) * ((a - 1 / 2 : ℝ) : ℂ) =
      -(2 * Real.pi * Complex.I) * (a : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I] at h
  have h3 := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (a : ℂ))
  apply h3
  linear_combination h / 2

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ U y hU hy`. Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `P : (κ → Ainf F) → κ → mixedEmbedding.mixedSpace F` to `fun u i => e (u i)`. Set `Q : (κ → mixedEmbedding.mixedSpace F) → κ → Ainf F` to `fun u i => e.symm (u i)`. Establish `hP : Continuous P` using `continuous_pi fun i => continuous_toMixed.comp (continuous_apply i)`.

Establish `hQ : Continuous Q` using `continuous_pi fun i => continuous_ofMixed.comp (continuous_apply i)`. Establish `hQP : ∀ u, Q (P u) = u` using `fun u => funext fun i => e.symm_apply_apply _`. Establish `hU' : IsClosed (Q ⁻¹' U)ᶜ` using `(hU.preimage hQ).isClosed_compl`. Take `⟨f, hf0, hf1, hf⟩` from `exists_continuous_zero_one_of_isClosed hU' (isClosed_singleton (x := P fun i => (y i).1)) (Set.disjoint_singleton_right.2 fun h => h (by rw [Set.mem_preimage, hQP]; exact hy))`. Set `χ : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) → ℂ` to `fun w u => Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ w) : ℝ))`.

Establish `hT : Continuous (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))` using `LinearMap.continuous_of_finiteDimensional _`. Take `⟨s, c, hb, hl⟩` from `exists_bounded_trig 0 χ (fun w => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hT.comp (continuous_id.dotProduct continuous_const))))) (fun a b x => by simp only [χ, dotProduct_add, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]) (fun …`. Set `ι : (κ → mixedEmbedding.mixedSpace F) → κ → AF F` to `fun w i => ((e.symm (w i), 0) : Ainf F × Af F)`. Set `ρ : (κ → AF F) → κ → mixedEmbedding.mixedSpace F` to `fun b i => e (b i).1`. Establish `hρ : ∀ w, ρ (ι w) = w` using `fun w => funext fun i => e.apply_symm_apply _`.

Establish `hι : Function.Injective ι` using `Function.LeftInverse.injective hρ`. Establish `hchar : ∀ (x : κ → AF F) w, ψ (x ⬝ᵥ ι w) = χ w (P fun i => (x i).1)`. Introduce `x w`. Establish `h2 : (x ⬝ᵥ ι w).2 = 0`. Use `map_sum (RingHom.snd (Ainf F) (Af F)) (fun i => x i * ι w i) Finset.univ` as an intermediate fact.

Use `this.trans (Finset.sum_eq_zero fun i _ => ?_)` and prove the remaining obligations. Conclude with `mul_zero (x i).2`. Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x ⬝ᵥ ι w) = (P fun i => (x i).1) ⬝ᵥ w`. Use `map_sum (e.toRingHom.comp (RingHom.fst (Ainf F) (Af F))) (fun i => x i * ι w i) Finset.univ` as an intermediate fact. Use `this.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e ((x i).1 * e.symm (w i)) = _`. Rewrite using `[map_mul, e.apply_symm_apply]`. Rewrite using `[hψ.2.2, h1]`. Introduce `u hu`. Establish `hu1 : u.1 = 0` using `e.injective (hu.trans (map_zero e).symm)`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * (x ⬝ᵥ ι w).1 = 0`. Rewrite using `[hu1, zero_mul]`. Express the relevant statement in the definitionally equal form `u.2 * (x ⬝ᵥ ι w).2 = 0`. Rewrite using `[h2, mul_zero]`.

Establish `hsum : ∀ n (x : κ → AF F), ∑ b ∈ (s n).map ⟨ι, hι⟩, c n (ρ b) * ψ (x ⬝ᵥ b) = ∑ w ∈ s n, c n w * χ w (P fun i => (x i).1)`. Introduce `n x`. Rewrite using `[Finset.sum_map]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Function.Embedding.coeFn_mk, hρ, hchar]`.

Use `⟨fun u => f (P u), f.continuous.comp hP, fun u => hf _, hf1 rfl, fun u hu => ?_, fun n => (s n).map ⟨ι, hι⟩, fun n b => c n (ρ b), 2, ?_, fun n x => ?_, fun x => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hu (hf0 (fun h' => h (by rwa [Set.mem_preimage, hQP] at h')))`. Introduce `n b hb v`. Take `⟨w, -, rfl⟩` from `Finset.mem_map.1 hb`.

Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `zero_mul (e.symm (w i))`. Conclude with `mul_zero (GlobalTheory.LatVac.liftV v 1).2`. Rewrite using `[hsum]`.

Conclude with `hb _ _`. Simplify using `only [hsum]`. Conclude with `hl _`.
-/
theorem arch_bump_trig : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  intro F _ _ κ _ ψ hψ U y hU hy
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let P : (κ → Ainf F) → κ → mixedEmbedding.mixedSpace F := fun u i => e (u i)
  let Q : (κ → mixedEmbedding.mixedSpace F) → κ → Ainf F := fun u i => e.symm (u i)
  have hP : Continuous P := continuous_pi fun i => continuous_toMixed.comp (continuous_apply i)
  have hQ : Continuous Q := continuous_pi fun i => continuous_ofMixed.comp (continuous_apply i)
  have hQP : ∀ u, Q (P u) = u := fun u => funext fun i => e.symm_apply_apply _
  have hU' : IsClosed (Q ⁻¹' U)ᶜ := (hU.preimage hQ).isClosed_compl
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU'
    (isClosed_singleton (x := P fun i => (y i).1))
    (Set.disjoint_singleton_right.2 fun h => h (by rw [Set.mem_preimage, hQP]; exact hy))
  let χ : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) → ℂ := fun w u =>
    Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ w) : ℝ))
  have hT : Continuous (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨s, c, hb, hl⟩ := exists_bounded_trig 0 χ
    (fun w => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hT.comp (continuous_id.dotProduct continuous_const)))))
    (fun a b x => by simp only [χ, dotProduct_add, map_add, Complex.ofReal_add, mul_add, Complex.exp_add])
    (fun x => by simp [χ])
    (fun a x => by simp [χ, Complex.norm_exp])
    exists_char_ne f f.continuous (fun u => hf u)
  let ι : (κ → mixedEmbedding.mixedSpace F) → κ → AF F := fun w i => ((e.symm (w i), 0) : Ainf F × Af F)
  let ρ : (κ → AF F) → κ → mixedEmbedding.mixedSpace F := fun b i => e (b i).1
  have hρ : ∀ w, ρ (ι w) = w := fun w => funext fun i => e.apply_symm_apply _
  have hι : Function.Injective ι := Function.LeftInverse.injective hρ
  have hchar : ∀ (x : κ → AF F) w, ψ (x ⬝ᵥ ι w) = χ w (P fun i => (x i).1) := by
    intro x w
    have h2 : (x ⬝ᵥ ι w).2 = 0 := by
      have := map_sum (RingHom.snd (Ainf F) (Af F)) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_eq_zero fun i _ => ?_)
      exact mul_zero (x i).2
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x ⬝ᵥ ι w) = (P fun i => (x i).1) ⬝ᵥ w := by
      have := map_sum (e.toRingHom.comp (RingHom.fst (Ainf F) (Af F))) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      change e ((x i).1 * e.symm (w i)) = _
      rw [map_mul, e.apply_symm_apply]
    rw [hψ.2.2, h1]
    intro u hu
    have hu1 : u.1 = 0 := e.injective (hu.trans (map_zero e).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * (x ⬝ᵥ ι w).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (x ⬝ᵥ ι w).2 = 0
      rw [h2, mul_zero]
  have hsum : ∀ n (x : κ → AF F), ∑ b ∈ (s n).map ⟨ι, hι⟩, c n (ρ b) * ψ (x ⬝ᵥ b) =
      ∑ w ∈ s n, c n w * χ w (P fun i => (x i).1) := by
    intro n x
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Function.Embedding.coeFn_mk, hρ, hchar]
  refine ⟨fun u => f (P u), f.continuous.comp hP, fun u => hf _, hf1 rfl, fun u hu => ?_,
    fun n => (s n).map ⟨ι, hι⟩, fun n b => c n (ρ b), 2, ?_, fun n x => ?_, fun x => ?_⟩
  · by_contra h
    exact hu (hf0 (fun h' => h (by rwa [Set.mem_preimage, hQP] at h')))
  · intro n b hb v
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hb
    funext i
    refine Prod.ext ?_ ?_
    · exact zero_mul (e.symm (w i))
    · exact mul_zero (GlobalTheory.LatVac.liftV v 1).2
  · rw [hsum]; exact hb _ _
  · simp only [hsum]; exact hl _

end GlobalTheory.ArchTrigBump
