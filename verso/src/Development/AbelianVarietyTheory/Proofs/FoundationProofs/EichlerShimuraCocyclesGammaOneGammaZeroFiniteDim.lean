import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Simplify using `[GlobalTheory.HeckeFamilyMatrices.slP]`. Rewrite `hp` using `[Polynomial.mem_degreeLT]`. Establish `hn : p.natDegree < w + 1`. Distinguish the cases in `h0 : p = 0`. Simplify using `[h0]`.

Conclude with `(Polynomial.natDegree_lt_iff_degree_lt h0).2 hp`. Use `conv_rhs => rw [p.as_sum_range' (w + 1) hn]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.smul_X_eq_monomial]`.
-/
theorem polySlash_one_of_mem (w : ℕ) (p : Polynomial ℂ) (hp : p ∈ Polynomial.degreeLT ℂ (w + 1)) :
    GlobalTheory.HeckeFamilyMatrices.slP w (1 : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  simp [GlobalTheory.HeckeFamilyMatrices.slP]
  rw [Polynomial.mem_degreeLT] at hp
  have hn : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  conv_rhs => rw [p.as_sum_range' (w + 1) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_X_eq_monomial]

/- English proof (translation)
Take `⟨hdeg, hco⟩` from `z.2`. Establish `hone : (z : Γ → Polynomial ℂ) 1 = 0`. Establish `h` using `hco 1 1`. Rewrite `h` using `[mul_one]`. Establish `hid : GlobalTheory.HeckeFamilyMatrices.slP w (GlobalTheory.HeckeFamilyMatrices.mat (1 : Γ)) ((z : Γ → Polynomial ℂ) 1) = (z : Γ → Polynomial ℂ) 1`.

Establish `: GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1` using `by simp [GlobalTheory.HeckeFamilyMatrices.mat]`. Rewrite using `[this]`. Conclude with `polySlash_one_of_mem w _ (hdeg 1)`. Rewrite `h` using `[hid]`. Establish `: (z : Γ → Polynomial ℂ) 1 + (z : Γ → Polynomial ℂ) 1 - (z : Γ → Polynomial ℂ) 1 = 0`.

Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using this`. Set `K : Subgroup Γ` to `{ carrier := {γ | (z : Γ → Polynomial ℂ) γ = 0} mul_mem' := by`. Introduce `a b ha hb`.

Use `show (z : Γ → Polynomial ℂ) (a * b) = 0`. Rewrite using `[hco, ha.out, hb.out, map_zero, add_zero]`. Use the proof step `one_mem' := hone`. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Use `show (z : Γ → Polynomial ℂ) a⁻¹ = 0`. Establish `h` using `hco a a⁻¹`. Rewrite `h` using `[mul_inv_cancel, hone, ha.out, map_zero, zero_add]`. Conclude with `h.symm }`. Establish `hle : Subgroup.closure S ≤ K` using `(Subgroup.closure_le K).2 hz`.

Rewrite `hle` using `[hS]`. Use function extensionality and compare the values at `γ`. Conclude with `hle (Subgroup.mem_top γ)`.
-/
theorem eichlerShimuraCocycle_eq_zero_of_closure (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (hz : ∀ s ∈ S, (z : Γ → Polynomial ℂ) s = 0) :
    (z : Γ → Polynomial ℂ) = 0 := by
  obtain ⟨hdeg, hco⟩ := z.2
  have hone : (z : Γ → Polynomial ℂ) 1 = 0 := by
    have h := hco 1 1
    rw [mul_one] at h
    have hid : GlobalTheory.HeckeFamilyMatrices.slP w (GlobalTheory.HeckeFamilyMatrices.mat (1 : Γ)) ((z : Γ → Polynomial ℂ) 1) = (z : Γ → Polynomial ℂ) 1 := by
      have : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := by simp [GlobalTheory.HeckeFamilyMatrices.mat]
      rw [this]
      exact polySlash_one_of_mem w _ (hdeg 1)
    rw [hid] at h
    have : (z : Γ → Polynomial ℂ) 1 + (z : Γ → Polynomial ℂ) 1 - (z : Γ → Polynomial ℂ) 1 = 0 := by
      rw [← h]; ring
    simpa using this
  let K : Subgroup Γ :=
    { carrier := {γ | (z : Γ → Polynomial ℂ) γ = 0}
      mul_mem' := by
        intro a b ha hb
        show (z : Γ → Polynomial ℂ) (a * b) = 0
        rw [hco, ha.out, hb.out, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := by
        intro a ha
        show (z : Γ → Polynomial ℂ) a⁻¹ = 0
        have h := hco a a⁻¹
        rw [mul_inv_cancel, hone, ha.out, map_zero, zero_add] at h
        exact h.symm }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).2 hz
  rw [hS] at hle
  funext γ
  exact hle (Subgroup.mem_top γ)

/- English proof (translation)
Take `⟨S, hS⟩` from `(Group.fg_def).1 (inferInstance : Group.FG Γ)`. Use `haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ (w + 1)) := Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (w + 1)).symm`. Set `g : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w →ₗ[ℂ] (S → Polynomial.degreeLT ℂ (w + 1))` to `LinearMap.pi fun s => LinearMap.codRestrict (Polynomial.degreeLT ℂ (w + 1)) ((LinearMap.proj (s : Γ)).comp (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w).subtype) (fun z => z.2.1 s)`. Establish `hg : Function.Injective g`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `z hz`. Establish `h0` using `eichlerShimuraCocycle_eq_zero_of_closure Γ w z (S : Set Γ) hS (fun s hs => by`. Use `congrArg Subtype.val (congrFun hz ⟨s, hs⟩)` as an intermediate fact. Conclude with `this)`. Conclude with `Subtype.ext h0`.

Conclude with `Module.Finite.of_injective g hg`.
-/
theorem eichlerShimuraCocycles_finiteDimensional_of_fg (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ] (w : ℕ) :
    FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) := by
  obtain ⟨S, hS⟩ := (Group.fg_def).1 (inferInstance : Group.FG Γ)
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ (w + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (w + 1)).symm
  let g : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w →ₗ[ℂ] (S → Polynomial.degreeLT ℂ (w + 1)) :=
    LinearMap.pi fun s => LinearMap.codRestrict (Polynomial.degreeLT ℂ (w + 1))
      ((LinearMap.proj (s : Γ)).comp (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w).subtype) (fun z => z.2.1 s)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 := eichlerShimuraCocycle_eq_zero_of_closure Γ w z (S : Set Γ) hS (fun s hs => by
      have := congrArg Subtype.val (congrFun hz ⟨s, hs⟩)
      exact this)
    exact Subtype.ext h0
  exact Module.Finite.of_injective g hg

/- English proof (translation)
Introduce `N l w hN hl`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne'⟩`. Use `haveI : Group.FG SL(2, ℤ) := by`. Rewrite using `[Group.fg_iff]`.

Conclude with `⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩`. Use `haveI : (GlobalTheory.HeckeFamilyMatrices.Lev N l).FiniteIndex := by unfold GlobalTheory.HeckeFamilyMatrices.Lev; infer_instance`. Use `haveI : Group.FG (GlobalTheory.HeckeFamilyMatrices.Lev N l) := Subgroup.fg_of_index_ne_zero _`. Conclude with `eichlerShimuraCocycles_finiteDimensional_of_fg _ w`.
-/
theorem lev_fd : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  intro N l w hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (GlobalTheory.HeckeFamilyMatrices.Lev N l).FiniteIndex := by unfold GlobalTheory.HeckeFamilyMatrices.Lev; infer_instance
  haveI : Group.FG (GlobalTheory.HeckeFamilyMatrices.Lev N l) := Subgroup.fg_of_index_ne_zero _
  exact eichlerShimuraCocycles_finiteDimensional_of_fg _ w

end GlobalTheory.KZ.H3
