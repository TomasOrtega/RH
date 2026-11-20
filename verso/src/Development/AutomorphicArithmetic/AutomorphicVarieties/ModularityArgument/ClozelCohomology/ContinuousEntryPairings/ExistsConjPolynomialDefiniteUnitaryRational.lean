import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

/- English proof (translation)
Apply the tactic sequence `have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]`. Unfold `coord`. Use `split_ifs with hτ`. Simplify using `only [Pi.evalRingHom_apply, h, hτ]`. Break down `InfinitePlace.embedding_mk_eq τ with h' | h'` into its components or cases.

Conclude with `absurd h' hτ`. Simplify using `[h, h']`.
-/
private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

/- English proof (translation)
Take `⟨γ₀, h₀⟩` from `Subgroup.mem_subgroupOf.1 hγ`. Use `⟨γ₀.val i j, fun τ => ?_⟩` and prove the remaining obligations. Establish `h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j)` using `rfl`. Establish `h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j)` using `rfl`. Rewrite using `[h1, hk, h2, ← h₀]`.

Conclude with `polyConj_coord_pInf τ _`.
-/
theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

/- English proof (translation)
Introduce `E _ _ _ n σ p hp`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem f hf`. Take `⟨τ, i, j, rfl⟩` from `hf`. Use `⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `exists_cEmb_entry_eq hγ hk i j`. Simplify using `only [hx]`. Both sides reduce to the same expression. Consider the case `algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩`. Consider the case `add f g _ _ hf hg`.

Take `⟨f', hf', hf⟩` from `hf`. Take `⟨g', hg', hg⟩` from `hg`. Use `⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]`. Consider the case `mul f g _ _ hf hg`.

Take `⟨f', hf', hf⟩` from `hf`. Take `⟨g', hg', hg⟩` from `hg`. Use `⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]`.
-/
theorem exists_conj_polyFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  intro E _ _ _ n σ p hp
  induction hp using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    refine ⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk i j
    simp only [hx]
    rfl
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]
  | mul f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]

end GlobalTheory.UnitaryBC
