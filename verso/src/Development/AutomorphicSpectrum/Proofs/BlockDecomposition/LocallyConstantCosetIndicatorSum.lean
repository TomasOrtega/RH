import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section CosetDecomp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `show Multiplicative.ofAdd (a - a) ∈ Lc t c`. Rewrite using `[sub_self, ofAdd_zero]`. Conclude with `(Lc t c).one_mem`.
-/
theorem self_mem_cosetSet_decomp (t : ℕ) (c : k) (a : Fin t → k) : a ∈ cosetSet t c a := by
  show Multiplicative.ofAdd (a - a) ∈ Lc t c
  rw [sub_self, ofAdd_zero]
  exact (Lc t c).one_mem

/- English proof (translation)
Establish `h' : Multiplicative.ofAdd (a - b) ∈ Lc t c` using `h`. Use `show Multiplicative.ofAdd (b - a) ∈ Lc t c`. Rewrite using `[← neg_sub, ofAdd_neg]`. Conclude with `(Lc t c).inv_mem h'`.
-/
theorem cosetSet_symm_decomp {t : ℕ} {c : k} {a b : Fin t → k} (h : a ∈ cosetSet t c b) :
    b ∈ cosetSet t c a := by
  have h' : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  show Multiplicative.ofAdd (b - a) ∈ Lc t c
  rw [← neg_sub, ofAdd_neg]
  exact (Lc t c).inv_mem h'

/- English proof (translation)
Establish `h1 : Multiplicative.ofAdd (a - b) ∈ Lc t c` using `h`. Establish `h2 : Multiplicative.ofAdd (b - d) ∈ Lc t c` using `h'`. Use `show Multiplicative.ofAdd (a - d) ∈ Lc t c`. Rewrite using `[← sub_add_sub_cancel a b d, ofAdd_add]`. Conclude with `(Lc t c).mul_mem h1 h2`.
-/
theorem cosetSet_trans_decomp {t : ℕ} {c : k} {a b d : Fin t → k} (h : a ∈ cosetSet t c b)
    (h' : b ∈ cosetSet t c d) : a ∈ cosetSet t c d := by
  have h1 : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  have h2 : Multiplicative.ofAdd (b - d) ∈ Lc t c := h'
  show Multiplicative.ofAdd (a - d) ∈ Lc t c
  rw [← sub_add_sub_cancel a b d, ofAdd_add]
  exact (Lc t c).mul_mem h1 h2

/- English proof (translation)
Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Conclude with `⟨∅, by simp, by simp⟩`. Introduce `x S _ ih`. Take `⟨A, hcov, huniq⟩` from `ih`. Distinguish the cases in `hex : ∃ a ∈ A, x ∈ cosetSet t c a`.

Use `⟨A, ?_, huniq⟩` and prove the remaining obligations. Introduce `s hs`. Break down `Finset.mem_insert.1 hs with hsx | hsS` into its components or cases. Rewrite using `[hsx]`. Conclude with `hex`.

Conclude with `hcov s hsS`. Use `push_neg at hex`. Use `⟨insert x A, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Break down `Finset.mem_insert.1 hs with hsx | hsS` into its components or cases.

Conclude with `⟨x, Finset.mem_insert_self _ _, hsx ▸ self_mem_cosetSet_decomp t c x⟩`. Take `⟨a, ha, hsa⟩` from `hcov s hsS`. Conclude with `⟨a, Finset.mem_insert_of_mem ha, hsa⟩`. Introduce `a ha b hb hab`. Break down `Finset.mem_insert.1 ha with hax | haA` into its components or cases.

Break down `Finset.mem_insert.1 hb with hbx | hbA` into its components or cases. Rewrite using `[hax, hbx]`. Rewrite `hab` using `[hax]`. Conclude with `absurd hab (hex b hbA)`. Break down `Finset.mem_insert.1 hb with hbx | hbA` into its components or cases.

Rewrite `hab` using `[hbx]`. Conclude with `absurd (cosetSet_symm_decomp hab) (hex a haA)`. Conclude with `huniq a haA b hbA hab`.
-/
theorem exists_coset_reps (t : ℕ) (c : k) (S : Finset (Fin t → k)) :
    ∃ A : Finset (Fin t → k), (∀ s ∈ S, ∃ a ∈ A, s ∈ cosetSet t c a) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ∈ cosetSet t c b → a = b := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨∅, by simp, by simp⟩
  · intro x S _ ih
    obtain ⟨A, hcov, huniq⟩ := ih
    by_cases hex : ∃ a ∈ A, x ∈ cosetSet t c a
    · refine ⟨A, ?_, huniq⟩
      intro s hs
      rcases Finset.mem_insert.1 hs with hsx | hsS
      · rw [hsx]
        exact hex
      · exact hcov s hsS
    · push_neg at hex
      refine ⟨insert x A, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.1 hs with hsx | hsS
        · exact ⟨x, Finset.mem_insert_self _ _, hsx ▸ self_mem_cosetSet_decomp t c x⟩
        · obtain ⟨a, ha, hsa⟩ := hcov s hsS
          exact ⟨a, Finset.mem_insert_of_mem ha, hsa⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with hax | haA
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hax, hbx]
          · rw [hax] at hab
            exact absurd hab (hex b hbA)
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hbx] at hab
            exact absurd (cosetSet_symm_decomp hab) (hex a haA)
          · exact huniq a haA b hbA hab

end CosetDecomp

/- English proof (translation)
Introduce `k _ _ _ _ t Z _ _ φ c _ hφ hinv`. Establish `hval : ∀ a v, v ∈ cosetSet t c a → φ v = φ a`. Introduce `a v hv`. Use `hinv (Multiplicative.ofAdd (v - a)) hv a` as an intermediate fact. Simplify using `using this`.

Establish `hopen : ∀ a, IsOpen (cosetSet t c a)`. Introduce `a`. Use `open ValuativeRel in`. Establish `e : cosetSet t c a = ⋂ j, (fun v : Fin t → k => c * (v j - a j)) ⁻¹' ((𝒪[k] : Subring k) : Set k)`. Use extensionality with `v`.

Simplify using `only [Set.mem_iInter, Set.mem_preimage]`. Conclude with `Iff.rfl`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun j => (SplitWeil.isOpen_int k).preimage (by fun_prop)`. Take `⟨S, hS⟩` from `hφ.elim_finite_subcover (fun a : tsupport φ => cosetSet t c a) (fun a => hopen a) (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, self_mem_cosetSet_decomp t c v⟩)`.

Take `⟨A, hAcov, hAuniq⟩` from `exists_coset_reps t c (S.image Subtype.val)`. Use `⟨A, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : ∃ a ∈ A, v ∈ cosetSet t c a`. Take `⟨a, ha, hva⟩` from `hv`. Rewrite using `[Finset.sum_eq_single a]`.

Rewrite using `[Set.indicator_of_mem hva]`. Conclude with `hval a v hva`. Introduce `b hb hba`. Rewrite using `[Set.indicator_of_notMem]`. Introduce `hvb`.

Conclude with `hba (hAuniq b hb a ha (cosetSet_trans_decomp (cosetSet_symm_decomp hvb) hva))`. Introduce `haA`. Conclude with `absurd ha haA`. Use `push_neg at hv`. Rewrite using `[Finset.sum_eq_zero]`.

Assume the negation of the conclusion as `hne`. Establish `hvs : v ∈ tsupport φ` using `subset_tsupport _ hne`. Take `⟨s, hsS, hvs'⟩` from `Set.mem_iUnion₂.1 (hS hvs)`. Take `⟨a, ha, hsa⟩` from `hAcov s (Finset.mem_image_of_mem _ hsS)`. Conclude with `hv a ha (cosetSet_trans_decomp hvs' hsa)`.

Introduce `a ha`. Conclude with `Set.indicator_of_notMem (hv a ha) _`.
-/
theorem eq_sum_coset_indicators : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  intro k _ _ _ _ t Z _ _ φ c _ hφ hinv
  classical
  have hval : ∀ a v, v ∈ cosetSet t c a → φ v = φ a := by
    intro a v hv
    have := hinv (Multiplicative.ofAdd (v - a)) hv a
    simpa using this
  have hopen : ∀ a, IsOpen (cosetSet t c a) := by
    intro a
    open ValuativeRel in
    have e : cosetSet t c a = ⋂ j, (fun v : Fin t → k => c * (v j - a j)) ⁻¹' ((𝒪[k] : Subring k) : Set k) := by
      ext v
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j => (SplitWeil.isOpen_int k).preimage (by fun_prop)
  obtain ⟨S, hS⟩ := hφ.elim_finite_subcover (fun a : tsupport φ => cosetSet t c a) (fun a => hopen a)
    (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, self_mem_cosetSet_decomp t c v⟩)
  obtain ⟨A, hAcov, hAuniq⟩ := exists_coset_reps t c (S.image Subtype.val)
  refine ⟨A, fun v => ?_⟩
  by_cases hv : ∃ a ∈ A, v ∈ cosetSet t c a
  · obtain ⟨a, ha, hva⟩ := hv
    rw [Finset.sum_eq_single a]
    · rw [Set.indicator_of_mem hva]
      exact hval a v hva
    · intro b hb hba
      rw [Set.indicator_of_notMem]
      intro hvb
      exact hba (hAuniq b hb a ha (cosetSet_trans_decomp (cosetSet_symm_decomp hvb) hva))
    · intro haA
      exact absurd ha haA
  · push_neg at hv
    rw [Finset.sum_eq_zero]
    · by_contra hne
      have hvs : v ∈ tsupport φ := subset_tsupport _ hne
      obtain ⟨s, hsS, hvs'⟩ := Set.mem_iUnion₂.1 (hS hvs)
      obtain ⟨a, ha, hsa⟩ := hAcov s (Finset.mem_image_of_mem _ hsS)
      exact hv a ha (cosetSet_trans_decomp hvs' hsa)
    · intro a ha
      exact Set.indicator_of_notMem (hv a ha) _

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
