import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PerpCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Use `fin_cases j`. Use `⟨-1, by simp, 1, fun a₀ v => ?_⟩` and prove the remaining obligations. Simplify using `[B4, Pi.single_apply]`. Use `⟨-1, by simp, 0, fun a₀ v => ?_⟩` and prove the remaining obligations. Simplify using `[B4, Pi.single_apply]`.

Use `⟨2, by simp, 2, fun a₀ v => ?_⟩` and prove the remaining obligations. Establish `h2 : rt (2 : F) = (2 : A F)` using `map_ofNat _ 2`. Simplify using `[B4, Pi.single_apply]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨-2 * δ, by simp [hδ], 3, fun a₀ v => ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap F (A F) 2 = (2 : A F)` using `map_ofNat _ 2`. Simplify using `[B4, Pi.single_apply]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem coeffB {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) (j : Fin 4) :
    ∃ c : F, c ≠ 0 ∧ ∃ i : Fin 4, ∀ (a₀ : A F) (v : V4 F), B4 δ (Pi.single i a₀) v = a₀ * (rt c * v j) := by
  fin_cases j
  · refine ⟨-1, by simp, 1, fun a₀ v => ?_⟩
    simp [B4, Pi.single_apply]
  · refine ⟨-1, by simp, 0, fun a₀ v => ?_⟩
    simp [B4, Pi.single_apply]
  · refine ⟨2, by simp, 2, fun a₀ v => ?_⟩
    have h2 : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp [B4, Pi.single_apply]
    rw [h2]
    ring
  · refine ⟨-2 * δ, by simp [hδ], 3, fun a₀ v => ?_⟩
    have h2 : algebraMap F (A F) 2 = (2 : A F) := map_ofNat _ 2
    simp [B4, Pi.single_apply]
    rw [h2]
    ring

/- English proof (translation)
Take `⟨K, hK, hKp⟩` from `perpCpt F Λ`. Use `choose c hc i hi using coeffB δ hδ`. Use `⟨Set.univ.pi fun j => (fun k => (rt (c j)⁻¹ : A F).2 * k) '' K, isCompact_univ_pi fun j => hK.image (continuous_const.mul continuous_id), ?_⟩` and prove the remaining obligations. Introduce `φ hφ v hv j _`. Use `⟨(rt (c j) * v j).2, hKp _ fun a ha1 ha2 => ?_, ?_⟩` and prove the remaining obligations.

Establish `hmem : ∀ l, ((Pi.single (i j) a : V4 F) l).1 = 0 ∧ ((Pi.single (i j) a : V4 F) l).2 ∈ Λ`. Introduce `l`. Distinguish the cases in `hl : l = i j`. Substitute `hl` using the available equality. Simplify using `using ⟨ha1, ha2⟩`.

Simplify using `[Pi.single_eq_of_ne hl, Λ.zero_mem]`. Establish `h` using `(hφ _ hmem v).2`. Rewrite `h` using `[hi j a v]`. Conclude with `mul_right_cancel₀ hv (by rw [h, one_mul])`. Establish `h : rt (c j)⁻¹ * (rt (c j) * v j) = v j`.

Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc j), map_one, one_mul]`. Conclude with `congrArg Prod.snd h`.
-/
private theorem fixCpt {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    ∃ K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K' ∧
      ∀ φ ∈ Fix δ Λ, ∀ v : V4 F, φ.1 v ≠ 0 → (fun j => (v j).2) ∈ K' := by
  obtain ⟨K, hK, hKp⟩ := perpCpt F Λ
  choose c hc i hi using coeffB δ hδ
  refine ⟨Set.univ.pi fun j => (fun k => (rt (c j)⁻¹ : A F).2 * k) '' K,
    isCompact_univ_pi fun j => hK.image (continuous_const.mul continuous_id), ?_⟩
  intro φ hφ v hv j _
  refine ⟨(rt (c j) * v j).2, hKp _ fun a ha1 ha2 => ?_, ?_⟩
  · have hmem : ∀ l, ((Pi.single (i j) a : V4 F) l).1 = 0 ∧ ((Pi.single (i j) a : V4 F) l).2 ∈ Λ := by
      intro l
      by_cases hl : l = i j
      · subst hl
        simpa using ⟨ha1, ha2⟩
      · simp [Pi.single_eq_of_ne hl, Λ.zero_mem]
    have h := (hφ _ hmem v).2
    rw [hi j a v] at h
    exact mul_right_cancel₀ hv (by rw [h, one_mul])
  · have h : rt (c j)⁻¹ * (rt (c j) * v j) = v j := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc j), map_one, one_mul]
    exact congrArg Prod.snd h

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D Λ`. Establish `hδ : D.δ ≠ 0`. Introduce `h`. Establish `h2 : D.θ ^ 2 = 0` using `by rw [D.sq, h, map_zero]`. Establish `h3 : D.θ = 0` using `by simpa using h2`.

Conclude with `D.b.ne_zero 1 (by rw [D.b1, h3])`. Take `⟨K', hK', hKp⟩` from `fixCpt D.δ hδ Λ`. Establish `hU : ∀ y ∈ K', {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ} ∈ 𝓝 y` using `fun y _ => by`. Establish `ho : IsOpen {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ}`. Simplify using `only [Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun i => Λ.isOpen.preimage ((continuous_apply i).sub continuous_const)`. Conclude with `ho.mem_nhds fun i => by simp [Λ.zero_mem]`. Take `⟨t, -, ht⟩` from `hK'.elim_nhds_subcover _ hU`. Set `T : ↥(Vac D.δ ⊓ Fix D.δ Λ) →ₗ[ℂ] (t → ℂ)` to `{ toFun := fun φ y => φ.1.1 (fun i => ((0, y.1 i) : A F)) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ hφ => ?_)` and prove the remaining obligations.

Use `ext1`. Use `ext1`. Use function extensionality and compare the values at `v`. Assume the negation of the conclusion as `hv`. Establish `hv' : φ.1.1 v ≠ 0` using `hv`.

Establish `hmem` using `ht (hKp φ.1 φ.2.2 v hv')`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem`. Take `⟨y, hy, hyv⟩` from `hmem`. Establish `hfix` using `(φ.2.2 (fun i => ((0, (v i).2 - y i) : A F)) (fun i => ⟨rfl, hyv i⟩) (fun i => ((0, y i) : A F))).1`. Establish `hsum : ((fun i => ((0, y i) : A F)) + fun i => ((0, (v i).2 - y i) : A F)) = fun i => ((0, (v i).2) : A F)`.

Use function extensionality and compare the values at `i`. Use `ext1`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hfix' : φ.1.1 (fun i => ((0, (v i).2) : A F)) = φ.1.1 (fun i => ((0, y i) : A F))` using `(congrArg (fun u => φ.1.1 u) hsum).symm.trans hfix`.

Establish `hz : φ.1.1 (fun i => ((0, y i) : A F)) = 0` using `congrFun hφ ⟨y, hy⟩`. Establish `hvac` using `φ.2.1 v (fun i => ((0, (v i).2) : A F)) rfl`. Rewrite `hvac` using `[hfix', hz, zero_mul]`. Conclude with `hv' ((mul_eq_zero.1 hvac).resolve_right (Complex.exp_ne_zero _))`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.vacFd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), FiniteDimensional ℂ ↥(Vac D.δ ⊓ Fix D.δ Λ) := by
  intro F E _ _ _ _ _ _ _ D Λ
  have hδ : D.δ ≠ 0 := by
    intro h
    have h2 : D.θ ^ 2 = 0 := by rw [D.sq, h, map_zero]
    have h3 : D.θ = 0 := by simpa using h2
    exact D.b.ne_zero 1 (by rw [D.b1, h3])
  obtain ⟨K', hK', hKp⟩ := fixCpt D.δ hδ Λ
  have hU : ∀ y ∈ K', {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ} ∈ 𝓝 y := fun y _ => by
    have ho : IsOpen {z : Fin 4 → FiniteAdeleRing (𝓞 F) F | ∀ i, z i - y i ∈ Λ} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i =>
        Λ.isOpen.preimage ((continuous_apply i).sub continuous_const)
    exact ho.mem_nhds fun i => by simp [Λ.zero_mem]
  obtain ⟨t, -, ht⟩ := hK'.elim_nhds_subcover _ hU
  let T : ↥(Vac D.δ ⊓ Fix D.δ Λ) →ₗ[ℂ] (t → ℂ) :=
    { toFun := fun φ y => φ.1.1 (fun i => ((0, y.1 i) : A F))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ hφ => ?_)
  ext1
  ext1
  funext v
  by_contra hv
  have hv' : φ.1.1 v ≠ 0 := hv
  have hmem := ht (hKp φ.1 φ.2.2 v hv')
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem
  obtain ⟨y, hy, hyv⟩ := hmem
  have hfix := (φ.2.2 (fun i => ((0, (v i).2 - y i) : A F)) (fun i => ⟨rfl, hyv i⟩)
    (fun i => ((0, y i) : A F))).1
  have hsum : ((fun i => ((0, y i) : A F)) + fun i => ((0, (v i).2 - y i) : A F)) = fun i => ((0, (v i).2) : A F) := by
    funext i
    ext1
    · simp
    · simp
  have hfix' : φ.1.1 (fun i => ((0, (v i).2) : A F)) = φ.1.1 (fun i => ((0, y i) : A F)) :=
    (congrArg (fun u => φ.1.1 u) hsum).symm.trans hfix
  have hz : φ.1.1 (fun i => ((0, y i) : A F)) = 0 := congrFun hφ ⟨y, hy⟩
  have hvac := φ.2.1 v (fun i => ((0, (v i).2) : A F)) rfl
  rw [hfix', hz, zero_mul] at hvac
  exact hv' ((mul_eq_zero.1 hvac).resolve_right (Complex.exp_ne_zero _))
