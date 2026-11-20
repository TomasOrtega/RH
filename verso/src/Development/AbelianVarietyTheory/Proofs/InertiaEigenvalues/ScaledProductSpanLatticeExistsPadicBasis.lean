import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

/- English proof (translation)
Introduce `l _ Γ _ a m ρs t M h1 h2`. Use `set Λ : Fin m → Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := fun k => Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) with hΛ`. Establish `hsum : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]), ∑ y ∈ t k, zOm l (c y) • y ∈ Λ k`. Introduce `k c`. Use `Submodule.sum_mem _ fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[zOm_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hy)`. Establish `hone : ∀ k, (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ Λ k`. Introduce `k`. Take `⟨c, hc⟩` from `h1 k`.

Rewrite using `[← hc]`. Conclude with `hsum k c`. Establish `hstab : ∀ k g, ∀ x ∈ Λ k, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k`. Introduce `k g x hx`. Use `Submodule.span_induction (p := fun x _ => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations.

Introduce `y hy`. Take `⟨c, hc⟩` from `h2 k g y hy`. Rewrite using `[hc]`. Conclude with `hsum k c`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[Matrix.mul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `c x _ hx`. Rewrite using `[← zOm_smul, Matrix.mul_smul, zOm_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Establish `hsingle : ∀ k, ∀ x ∈ Λ k, Pi.single k x ∈ latL t 0`. Introduce `k x hx`. Establish `: (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) x ∈ latL t 0`. Establish `hle : (Λ k).map (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) ≤ latL t 0`.

Rewrite using `[hΛ, Submodule.map_span, latL]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `Set.mem_iUnion.2 ⟨k, y, hy, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `hle (Submodule.mem_map_of_mem hx)`. Simplify using `using this`. Establish `hT : latT ρs t M ≤ latL t 0`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[show tup ρs g = ∑ k, Pi.single k (tup ρs g k) from (Finset.univ_sum_single _).symm]`. Use `Submodule.sum_mem _ fun k _ => hsingle k _ ?_` and prove the remaining obligations. Use `hstab k g 1 (hone k)` as an intermediate fact. Simplify `this` using `[tup]`.

Rewrite using `[latL, Submodule.span_le]`. Introduce `z hz`. Take `⟨k, y, hy, rfl⟩` from `Set.mem_iUnion.1 hz`. Use `hsingle k _ ?_` and prove the remaining obligations. Establish `: ((l : ℤ_[l]) ^ M) • y ∈ Λ k` using `Submodule.smul_mem _ _ (Submodule.subset_span hy)`.

Rewrite `this` using `[← zOm_smul, map_pow, map_natCast]`. Conclude with `this`. Establish `hfg0 : (latL t (0 : ℕ)).FG`. Rewrite using `[latL]`. Use `Submodule.fg_span ?_` and prove the remaining obligations.

Conclude with `Set.finite_iUnion fun k => (t k).finite_toSet.image _`. Establish `hfg : (latT ρs t M).FG` using `hfg0.of_le hT`. Use `haveI : Module.Finite ℤ_[l] (latT ρs t M) := Module.Finite.iff_fg.2 hfg`. Establish `hinj : Function.Injective (zOm l)` using `(algebraMap ℚ_[l] (Om l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])`. Use `haveI tf0 : Module.IsTorsionFree ℤ_[l] (Om l) := .of_smul_eq_zero fun c x h => by`.

Rewrite `h` using `[← zOm_smul, smul_eq_mul, mul_eq_zero]`. Break down `h with h | h` into its components or cases. Use the proof step `left; exact hinj (by simpa using h)`. Use `right`. Conclude with `h`.

Use `haveI tf1 : Module.IsTorsionFree ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := inferInstanceAs (Module.IsTorsionFree ℤ_[l] (Fin a → Fin a → Om l))`. Use `haveI : Module.IsTorsionFree ℤ_[l] (latT ρs t M) := inferInstance`. Use `haveI : Module.Free ℤ_[l] (latT ρs t M) := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.finBasis ℤ_[l] (latT ρs t M)`. Use `⟨_, fun s => (b s : Fin m → Matrix (Fin a) (Fin a) (Om l)), ?_, fun s => (b s).2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]`. Conclude with `b.linearIndependent.map' (latT ρs t M).subtype (Submodule.ker_subtype _)`. Introduce `x hx`. Use `⟨b.repr ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Simplify using `only [zOm_smul]`. Conclude with `this.symm`.
-/
theorem latT_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  intro l _ Γ _ a m ρs t M h1 h2

  set Λ : Fin m → Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    fun k => Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) with hΛ
  have hsum : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]), ∑ y ∈ t k, zOm l (c y) • y ∈ Λ k := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hone : ∀ k, (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ Λ k := by
    intro k
    obtain ⟨c, hc⟩ := h1 k
    rw [← hc]; exact hsum k c
  have hstab : ∀ k g, ∀ x ∈ Λ k, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k := by
    intro k g x hx
    refine Submodule.span_induction (p := fun x _ => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨c, hc⟩ := h2 k g y hy
      rw [hc]; exact hsum k c
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← zOm_smul, Matrix.mul_smul, zOm_smul]
      exact Submodule.smul_mem _ _ hx

  have hsingle : ∀ k, ∀ x ∈ Λ k, Pi.single k x ∈ latL t 0 := by
    intro k x hx
    have : (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) x ∈ latL t 0 := by
      have hle : (Λ k).map (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) ≤ latL t 0 := by
        rw [hΛ, Submodule.map_span, latL]
        refine Submodule.span_mono ?_
        rintro _ ⟨y, hy, rfl⟩
        refine Set.mem_iUnion.2 ⟨k, y, hy, ?_⟩
        simp
      exact hle (Submodule.mem_map_of_mem hx)
    simpa using this
  have hT : latT ρs t M ≤ latL t 0 := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [show tup ρs g = ∑ k, Pi.single k (tup ρs g k) from (Finset.univ_sum_single _).symm]
      refine Submodule.sum_mem _ fun k _ => hsingle k _ ?_
      have := hstab k g 1 (hone k)
      simpa [tup] using this
    · rw [latL, Submodule.span_le]
      intro z hz
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
      refine hsingle k _ ?_
      have : ((l : ℤ_[l]) ^ M) • y ∈ Λ k := Submodule.smul_mem _ _ (Submodule.subset_span hy)
      rw [← zOm_smul, map_pow, map_natCast] at this
      exact this
  have hfg0 : (latL t (0 : ℕ)).FG := by
    rw [latL]
    refine Submodule.fg_span ?_
    exact Set.finite_iUnion fun k => (t k).finite_toSet.image _
  have hfg : (latT ρs t M).FG := hfg0.of_le hT
  haveI : Module.Finite ℤ_[l] (latT ρs t M) := Module.Finite.iff_fg.2 hfg
  have hinj : Function.Injective (zOm l) :=
    (algebraMap ℚ_[l] (Om l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI tf0 : Module.IsTorsionFree ℤ_[l] (Om l) := .of_smul_eq_zero fun c x h => by
    rw [← zOm_smul, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by simpa using h)
    · right; exact h
  haveI tf1 : Module.IsTorsionFree ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    inferInstanceAs (Module.IsTorsionFree ℤ_[l] (Fin a → Fin a → Om l))
  haveI : Module.IsTorsionFree ℤ_[l] (latT ρs t M) := inferInstance
  haveI : Module.Free ℤ_[l] (latT ρs t M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] (latT ρs t M)
  refine ⟨_, fun s => (b s : Fin m → Matrix (Fin a) (Fin a) (Om l)), ?_, fun s => (b s).2, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
    exact b.linearIndependent.map' (latT ρs t M).subtype (Submodule.ker_subtype _)
  · intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [zOm_smul]
    exact this.symm

end GlobalTheory.TraceConjugationCover
