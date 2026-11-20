import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

/- English proof (translation)
Establish `hli : LinearIndependent K (fun a => B.mkQ (φ a))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `h0 : B.mkQ (∑ a, c a • φ a) = 0`. Simplify `hc` using `[map_sum, map_smul]`.

Establish `hc0` using `h c ((Submodule.Quotient.mk_eq_zero B).mp h0)`. Introduce `i`. Simplify using `[hc0]`. Set `e` to `Module.Basis.span hli`. Use `choose ext hext using fun b => LinearMap.exists_extend (e.coord b)`.

Use `⟨fun b => (ext b).comp B.mkQ, fun b x hx => ?_, fun b a => ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]`. Establish `hmem : B.mkQ (φ a) ∈ Submodule.span K (Set.range fun a => B.mkQ (φ a))` using `Submodule.subset_span ⟨a, rfl⟩`. Establish `he : (⟨B.mkQ (φ a), hmem⟩ : Submodule.span K (Set.range fun a => B.mkQ (φ a))) = e a` using `(Module.Basis.span_apply hli a).symm`. Establish `hb` using `LinearMap.congr_fun (hext b) ⟨B.mkQ (φ a), hmem⟩`.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at hb`. Rewrite using `[LinearMap.comp_apply, hb, he, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem exists_dual_family_mod_subspace (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (B : Submodule K V) (g : ℕ) (φ : Fin g → V)
    (h : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) :
    ∃ β : Fin g → Module.Dual K V, (∀ b, B ≤ LinearMap.ker (β b)) ∧
      ∀ b a, β b (φ a) = if a = b then 1 else 0 := by
  classical

  have hli : LinearIndependent K (fun a => B.mkQ (φ a)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : B.mkQ (∑ a, c a • φ a) = 0 := by
      simpa [map_sum, map_smul] using hc
    have hc0 := h c ((Submodule.Quotient.mk_eq_zero B).mp h0)
    intro i
    simp [hc0]

  let e := Module.Basis.span hli
  choose ext hext using fun b => LinearMap.exists_extend (e.coord b)
  refine ⟨fun b => (ext b).comp B.mkQ, fun b x hx => ?_, fun b a => ?_⟩
  · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
  · have hmem : B.mkQ (φ a) ∈ Submodule.span K (Set.range fun a => B.mkQ (φ a)) :=
      Submodule.subset_span ⟨a, rfl⟩
    have he : (⟨B.mkQ (φ a), hmem⟩ : Submodule.span K (Set.range fun a => B.mkQ (φ a))) = e a :=
      (Module.Basis.span_apply hli a).symm
    have hb := LinearMap.congr_fun (hext b) ⟨B.mkQ (φ a), hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hb
    rw [LinearMap.comp_apply, hb, he, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
Introduce `K V _ _ _ B g θ φ hind hsym`. Take `⟨β, hβB, hβφ⟩` from `exists_dual_family_mod_subspace K V B g φ hind`. Establish `key : ∀ α : Module.Dual K V, B ≤ LinearMap.ker α → ∀ b, α (θ b) = ∑ a, α (φ a) * β b (θ a)`. Introduce `α hα b`. Rewrite using `[← hsym α (β b) hα (hβB b)]`.

Simplify using `[hβφ]`. Use `⟨Matrix.of fun b a => β b (θ a), Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Rewrite using `[key (β i) (hβB i) j]`. Simplify using `[hβφ]`.

Simplify using `only [Matrix.of_apply]`. Assume the negation of the conclusion as `hx`. Establish `hq : B.mkQ (θ b - ∑ a, β b (θ a) • φ a) ≠ 0` using `fun h0 => hx ((Submodule.Quotient.mk_eq_zero B).mp h0)`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual K (V ⧸ B), f (B.mkQ (θ b - ∑ a, β b (θ a) • φ a)) ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hq ((Module.forall_dual_apply_eq_zero_iff K _).mp hall)`. Apply `hf` to reduce the goal to its premises. Establish `hα : B ≤ LinearMap.ker (f.comp B.mkQ)` using `fun x hx => by simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]`. Establish `hk` using `key (f.comp B.mkQ) hα b`.

Simplify using `only [LinearMap.comp_apply] at hk`. Simplify using `only [map_sub, map_sum, map_smul, smul_eq_mul, hk]`. Simplify using `[mul_comm]`.
-/
theorem exists_symm_matrix_mod_subspace :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (B : Submodule K V) (g : ℕ) (θ φ : Fin g → V), (∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) → (∀ α β : Module.Dual K V, B ≤ LinearMap.ker α → B ≤ LinearMap.ker β → ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, θ b - ∑ a, Θ b a • φ a ∈ B := by
  intro K V _ _ _ B g θ φ hind hsym
  classical
  obtain ⟨β, hβB, hβφ⟩ := exists_dual_family_mod_subspace K V B g φ hind

  have key : ∀ α : Module.Dual K V, B ≤ LinearMap.ker α →
      ∀ b, α (θ b) = ∑ a, α (φ a) * β b (θ a) := by
    intro α hα b
    rw [← hsym α (β b) hα (hβB b)]
    simp [hβφ]
  refine ⟨Matrix.of fun b a => β b (θ a), Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · simp only [Matrix.of_apply]
    rw [key (β i) (hβB i) j]
    simp [hβφ]
  · simp only [Matrix.of_apply]
    by_contra hx
    have hq : B.mkQ (θ b - ∑ a, β b (θ a) • φ a) ≠ 0 :=
      fun h0 => hx ((Submodule.Quotient.mk_eq_zero B).mp h0)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual K (V ⧸ B), f (B.mkQ (θ b - ∑ a, β b (θ a) • φ a)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff K _).mp hall)
    apply hf
    have hα : B ≤ LinearMap.ker (f.comp B.mkQ) := fun x hx =>
      by simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
    have hk := key (f.comp B.mkQ) hα b
    simp only [LinearMap.comp_apply] at hk
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hk]
    simp [mul_comm]

end GlobalTheory.KS
