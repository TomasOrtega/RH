import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomialStatement

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
The claim follows from `IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)`.
-/
theorem isLocalization_rat_tensor (B : Type) [CommRing B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) :=
  IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)

/- English proof (translation)
Introduce and unpack `_ ⟨n, hn, rfl⟩`. Establish `h : n ≠ 0` using `nonZeroDivisors.ne_zero hn`. Conclude with `mem_nonZeroDivisors_of_ne_zero (by simpa using h)`.
-/
theorem intMap_le_nonZeroDivisors (B : Type) [CommRing B] [IsDomain B] [CharZero B] :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ) ≤ nonZeroDivisors B := by
  rintro _ ⟨n, hn, rfl⟩
  have h : n ≠ 0 := nonZeroDivisors.ne_zero hn
  exact mem_nonZeroDivisors_of_ne_zero (by simpa using h)

noncomputable def ratExtPoint {B : Type} [CommRing B] (x : B →+* ℂ) : ℚ ⊗[ℤ] B →+* ℂ :=
  (Algebra.TensorProduct.lift (algebraMap ℚ ℂ).toIntAlgHom x.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

/- English proof (translation)
Simplify using `[ratExtPoint]`.
-/
theorem ratExtPoint_tmul {B : Type} [CommRing B] (x : B →+* ℂ) (q : ℚ) (b : B) :
    ratExtPoint x (q ⊗ₜ[ℤ] b) = (q : ℂ) * x b := by
  simp [ratExtPoint]

/- English proof (translation)
Introduce `B _ _ _ _`. Use `letI tB : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance`. Introduce `ψ hψ s hs x₀ δ hδ`. Use `letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)`. Use `haveI := isLocalization_rat_tensor B`.

Establish `hle` using `intMap_le_nonZeroDivisors B`. Use `haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors (ℚ ⊗[ℤ] B) hle`. Establish `hinj : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B))` using `IsLocalization.injective _ hle`. Use `set φ : B →+* ℚ ⊗[ℤ] B := algebraMap B (ℚ ⊗[ℤ] B) with hφ`. Establish `hφ' : ∀ b, φ b = (1 : ℚ) ⊗ₜ[ℤ] b` using `fun _ => rfl`.

Take `⟨d, g, hg, hfin⟩` from `exists_finite_inj_algHom_of_fg ℚ (ℚ ⊗[ℤ] B)`. Use `letI : Algebra (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := g.toRingHom.toAlgebra`. Use `haveI : Module.Finite (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := hfin`. Use `letI tB' : TopologicalSpace (ℚ ⊗[ℤ] B →+* ℂ) := TopologicalSpace.induced (fun x : ℚ ⊗[ℤ] B →+* ℂ => (x : ℚ ⊗[ℤ] B → ℂ)) inferInstance`. Establish `hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b` using `fun b => (continuous_apply b).comp continuous_induced_dom`.

Establish `hev' : ∀ b : ℚ ⊗[ℤ] B, Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x b` using `fun b => (continuous_apply b).comp continuous_induced_dom`. Establish `hres : Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x.comp φ` using `continuous_induced_rng.2 (continuous_pi fun b => hev' (φ b))`. Establish `hext : Continuous fun x : B →+* ℂ => ratExtPoint x`. Use `continuous_induced_rng.2 (continuous_pi fun t => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun x : B →+* ℂ => ratExtPoint x t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simpa using continuous_const`. Consider the case `tmul q b => simp only [ratExtPoint_tmul]`. Conclude with `continuous_const.mul (hev b)`. Consider the case `add t u ht hu => simp only [map_add]`.

Conclude with `ht.add hu`. Establish `hcomp : ∀ x : B →+* ℂ, (ratExtPoint x).comp φ = x` using `fun x => by`. Use extensionality with `b`. Simplify using `[hφ', ratExtPoint_tmul]`. Take `⟨W, K, hW, hK, hKs, hb⟩` from `GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial d (ℚ ⊗[ℤ] B) hg (fun x => ψ (x.comp φ)) (hψ.comp hres) (φ s) (fun h => hs (hinj (h.trans (map_zero _).symm))) (ratExtPoint x₀) δ hδ`.

Use `⟨(fun x => ratExtPoint x) ⁻¹' W, (fun x => x.comp φ) '' K, hext.continuousAt.preimage_mem_nhds hW, hK.image hres, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hKs x hx`. Introduce `N f R hR y hy`. Establish `h` using `hb N (φ f) R (fun x hx => hR _ ⟨x, hx, rfl⟩) (ratExtPoint y) hy`.

Establish `h2 : ratExtPoint y (φ f) = y f` using `by rw [← RingHom.comp_apply, hcomp]`. Simplify `h` using `only [hcomp, h2]`.
-/
theorem local_max_principle_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  intro B _ _ _ _
  letI tB : TopologicalSpace (B →+* ℂ) :=
    TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance
  intro ψ hψ s hs x₀ δ hδ
  letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
  haveI := isLocalization_rat_tensor B
  have hle := intMap_le_nonZeroDivisors B
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors (ℚ ⊗[ℤ] B) hle
  have hinj : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hle
  set φ : B →+* ℚ ⊗[ℤ] B := algebraMap B (ℚ ⊗[ℤ] B) with hφ
  have hφ' : ∀ b, φ b = (1 : ℚ) ⊗ₜ[ℤ] b := fun _ => rfl
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℚ (ℚ ⊗[ℤ] B)
  letI : Algebra (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := hfin
  letI tB' : TopologicalSpace (ℚ ⊗[ℤ] B →+* ℂ) :=
    TopologicalSpace.induced (fun x : ℚ ⊗[ℤ] B →+* ℂ => (x : ℚ ⊗[ℤ] B → ℂ)) inferInstance
  have hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hev' : ∀ b : ℚ ⊗[ℤ] B, Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hres : Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x.comp φ :=
    continuous_induced_rng.2 (continuous_pi fun b => hev' (φ b))
  have hext : Continuous fun x : B →+* ℂ => ratExtPoint x := by
    refine continuous_induced_rng.2 (continuous_pi fun t => ?_)
    change Continuous fun x : B →+* ℂ => ratExtPoint x t
    induction t using TensorProduct.induction_on with
    | zero => simpa using continuous_const
    | tmul q b => simp only [ratExtPoint_tmul]; exact continuous_const.mul (hev b)
    | add t u ht hu => simp only [map_add]; exact ht.add hu
  have hcomp : ∀ x : B →+* ℂ, (ratExtPoint x).comp φ = x := fun x => by
    ext b
    simp [hφ', ratExtPoint_tmul]
  obtain ⟨W, K, hW, hK, hKs, hb⟩ := GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial d (ℚ ⊗[ℤ] B) hg (fun x => ψ (x.comp φ))
    (hψ.comp hres) (φ s) (fun h => hs (hinj (h.trans (map_zero _).symm))) (ratExtPoint x₀) δ hδ
  refine ⟨(fun x => ratExtPoint x) ⁻¹' W, (fun x => x.comp φ) '' K,
    hext.continuousAt.preimage_mem_nhds hW, hK.image hres, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hKs x hx
  · intro N f R hR y hy
    have h := hb N (φ f) R (fun x hx => hR _ ⟨x, hx, rfl⟩) (ratExtPoint y) hy
    have h2 : ratExtPoint y (φ f) = y f := by rw [← RingHom.comp_apply, hcomp]
    simpa only [hcomp, h2] using h

end GlobalTheory
