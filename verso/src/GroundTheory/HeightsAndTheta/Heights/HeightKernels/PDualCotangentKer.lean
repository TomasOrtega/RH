import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualCotangentKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualCotangentKernel

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

/- English proof (translation)
Introduce `x hx`. Rewrite using `[smul_dotProduct, smul_eq_mul]`. Take `⟨r, hr⟩` from `hφ x hx`. Conclude with `⟨μ * r, by rw [map_mul, hr]⟩`.
-/
theorem smul_mem (F : HermLattice K i) (μ : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (algebraMap (𝓞 K) K μ) • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  obtain ⟨r, hr⟩ := hφ x hx
  exact ⟨μ * r, by rw [map_mul, hr]⟩

def mulMap (F : HermLattice K i) (c : 𝓞 K) : dualLattice F →ₗ[ℤ] dualLattice F where
  toFun χ := ⟨algebraMap (𝓞 K) K c • (χ : Fin i → K), smul_mem F c χ.2⟩
  map_add' χ χ' := by ext1; simp [smul_add]
  map_smul' n χ := by
    ext1
    show algebraMap (𝓞 K) K c • ((n • χ : dualLattice F) : Fin i → K) =
      n • (algebraMap (𝓞 K) K c • (χ : Fin i → K))
    rw [Submodule.coe_smul, smul_comm]

def prodSet (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) : Set (dualLattice F) :=
  {v | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
    (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

/- English proof (translation)
Establish `hle : Submodule.span ℤ (prodSet F ρ) ≤ (Submodule.span ℤ (prodSet F ρ)).comap (mulMap F c)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `v ⟨μ, φ, hμ, hv⟩`. Use `Submodule.subset_span ⟨c * μ, φ, by rw [map_mul, hμ, mul_zero], ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 K) K c • (v : Fin i → K) = _`.

Rewrite using `[hv, smul_smul, ← map_mul]`. Conclude with `hle hχ`.
-/
theorem mulMap_mem (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) (c : 𝓞 K)
    {χ : dualLattice F} (hχ : χ ∈ Submodule.span ℤ (prodSet F ρ)) :
    mulMap F c χ ∈ Submodule.span ℤ (prodSet F ρ) := by
  have hle : Submodule.span ℤ (prodSet F ρ) ≤ (Submodule.span ℤ (prodSet F ρ)).comap (mulMap F c) := by
    rw [Submodule.span_le]
    rintro v ⟨μ, φ, hμ, hv⟩
    refine Submodule.subset_span ⟨c * μ, φ, by rw [map_mul, hμ, mul_zero], ?_⟩
    show algebraMap (𝓞 K) K c • (v : Fin i → K) = _
    rw [hv, smul_smul, ← map_mul]
  exact hle hχ

end DualCotangentKernel

open DualCotangentKernel in

/- English proof (translation)
Introduce `K _ _ i F T _ _b k _ ρ σ hρ hσ hsl ψ hψ`. Express the relevant statement in the definitionally equal form `ψ ∈ Submodule.span ℤ (prodSet F ρ)`. Use `choose φ hφ using fun j : Fin i => hσ (Pi.single j 1)`. Set `w : Option (Fin i) → dualLattice F` to `fun o => o.elim ψ φ`. Establish `hdep : ¬ LinearIndependent K (fun o => (w o : Fin i → K))`.

Introduce `h`. Use `h.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, o, ho⟩` from `Fintype.not_linearIndependent_iff.mp hdep`.

Establish `hJ : RingHom.ker ρ ≠ ⊤` using `RingHom.ker_ne_top ρ`. Take `⟨a, hint, o', -, hnot⟩` from `Ideal.exist_integer_multiples_notMem (A := 𝓞 K) (K := K) hJ Finset.univ g (Finset.mem_univ o) ho`. Use `choose c hc using fun x => hint x (Finset.mem_univ x)`. Set `χ : Option (Fin i) → dualLattice F` to `fun x => mulMap F (c x) (w x)`. Establish `hsum : ∑ x, χ x = 0` using `by ext1`.

Rewrite using `[Submodule.coe_sum, Submodule.coe_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hc x, smul_smul]`.

Use `_ = 0 := by rw [hg, smul_zero]`. Establish `hσχ : ∀ x, σ (χ x) = ρ (c x) • σ (w x)` using `fun x => hsl (c x) (w x) (χ x) rfl`. Establish `hσsum : ∑ x, ρ (c x) • σ (w x) = 0`. Rewrite using `[← map_zero σ, ← hsum, map_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => (hσχ x).symm`.

Establish `hsome : ∀ j, ρ (c (some j)) = 0`. Introduce `j`. Establish `h` using `congrFun hσsum j`. Rewrite `h` using `[Fintype.sum_option]`. Simplify using `only [w, Option.elim_none, Option.elim_some, hψ, smul_zero, zero_add, hφ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h`.

Rewrite `h` using `[Finset.sum_ite_eq]`. Simplify using `using h`. Establish `hnone : ρ (c none) ≠ 0`. Introduce `h0`. Apply `hnot` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Use `⟨c o', ?_, hc o'⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker]`. Consider the cases of `o' with`. Consider the case `none => exact h0`.

Consider the case `some j => exact hsome j`. Establish `hgen : ∀ j, χ (some j) ∈ Submodule.span ℤ (prodSet F ρ)` using `fun j => Submodule.subset_span ⟨c (some j), φ j, hsome j, rfl⟩`. Establish `hχ0 : χ none ∈ Submodule.span ℤ (prodSet F ρ)`. Establish `h : χ none = -∑ j, χ (some j)`. Rewrite `hsum` using `[Fintype.sum_option]`.

Conclude with `eq_neg_of_add_eq_zero_left hsum`. Rewrite using `[h]`. Conclude with `neg_mem (Submodule.sum_mem _ fun j _ => hgen j)`. Take `⟨bb, hbb⟩` from `hρ (ρ (c none))⁻¹`. Establish `hm : ρ (bb * c none - 1) = 0`.

Rewrite using `[map_sub, map_mul, hbb, inv_mul_cancel₀ hnone, map_one, sub_self]`. Establish `h1 : mulMap F bb (χ none) ∈ Submodule.span ℤ (prodSet F ρ)` using `mulMap_mem F ρ bb hχ0`. Establish `h2 : mulMap F (bb * c none - 1) ψ ∈ Submodule.span ℤ (prodSet F ρ)` using `Submodule.subset_span ⟨_, ψ, hm, rfl⟩`. Establish `hψeq : ψ = mulMap F bb (χ none) - mulMap F (bb * c none - 1) ψ` using `by ext1`. Simplify using `only [χ, w, Option.elim_none, mulMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub, smul_smul, ← map_mul, ← sub_smul, map_sub, map_one]`.

Rewrite using `[sub_sub_cancel, one_smul]`. Rewrite using `[hψeq]`. Conclude with `sub_mem h1 h2`.
-/
theorem DualCotangentKer.proof : DualCotangentKer.Statement := by
  intro K _ _ i F T _ _b k _ ρ σ hρ hσ hsl ψ hψ
  classical
  change ψ ∈ Submodule.span ℤ (prodSet F ρ)

  choose φ hφ using fun j : Fin i => hσ (Pi.single j 1)
  let w : Option (Fin i) → dualLattice F := fun o => o.elim ψ φ

  have hdep : ¬ LinearIndependent K (fun o => (w o : Fin i → K)) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hJ : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top ρ
  obtain ⟨a, hint, o', -, hnot⟩ :=
    Ideal.exist_integer_multiples_notMem (A := 𝓞 K) (K := K) hJ Finset.univ g (Finset.mem_univ o) ho
  choose c hc using fun x => hint x (Finset.mem_univ x)

  let χ : Option (Fin i) → dualLattice F := fun x => mulMap F (c x) (w x)
  have hsum : ∑ x, χ x = 0 := by
    ext1
    rw [Submodule.coe_sum, Submodule.coe_zero]
    calc ∑ x, ((χ x : dualLattice F) : Fin i → K) = ∑ x, algebraMap (𝓞 K) K (c x) • (w x : Fin i → K) := rfl
      _ = a • ∑ x, g x • (w x : Fin i → K) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hc x, smul_smul]
      _ = 0 := by rw [hg, smul_zero]
  have hσχ : ∀ x, σ (χ x) = ρ (c x) • σ (w x) := fun x => hsl (c x) (w x) (χ x) rfl
  have hσsum : ∑ x, ρ (c x) • σ (w x) = 0 := by
    rw [← map_zero σ, ← hsum, map_sum]
    exact Finset.sum_congr rfl fun x _ => (hσχ x).symm

  have hsome : ∀ j, ρ (c (some j)) = 0 := by
    intro j
    have h := congrFun hσsum j
    rw [Fintype.sum_option] at h
    simp only [w, Option.elim_none, Option.elim_some, hψ, smul_zero, zero_add, hφ, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h
    rw [Finset.sum_ite_eq] at h
    simpa using h
  have hnone : ρ (c none) ≠ 0 := by
    intro h0
    apply hnot
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨c o', ?_, hc o'⟩
    rw [RingHom.mem_ker]
    cases o' with
    | none => exact h0
    | some j => exact hsome j

  have hgen : ∀ j, χ (some j) ∈ Submodule.span ℤ (prodSet F ρ) := fun j =>
    Submodule.subset_span ⟨c (some j), φ j, hsome j, rfl⟩
  have hχ0 : χ none ∈ Submodule.span ℤ (prodSet F ρ) := by
    have h : χ none = -∑ j, χ (some j) := by
      rw [Fintype.sum_option] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    rw [h]
    exact neg_mem (Submodule.sum_mem _ fun j _ => hgen j)

  obtain ⟨bb, hbb⟩ := hρ (ρ (c none))⁻¹
  have hm : ρ (bb * c none - 1) = 0 := by
    rw [map_sub, map_mul, hbb, inv_mul_cancel₀ hnone, map_one, sub_self]
  have h1 : mulMap F bb (χ none) ∈ Submodule.span ℤ (prodSet F ρ) := mulMap_mem F ρ bb hχ0
  have h2 : mulMap F (bb * c none - 1) ψ ∈ Submodule.span ℤ (prodSet F ρ) :=
    Submodule.subset_span ⟨_, ψ, hm, rfl⟩
  have hψeq : ψ = mulMap F bb (χ none) - mulMap F (bb * c none - 1) ψ := by
    ext1
    simp only [χ, w, Option.elim_none, mulMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
      smul_smul, ← map_mul, ← sub_smul, map_sub, map_one]
    rw [sub_sub_cancel, one_smul]
  rw [hψeq]
  exact sub_mem h1 h2

end

end GroundTheory.Heights₂.Heights
