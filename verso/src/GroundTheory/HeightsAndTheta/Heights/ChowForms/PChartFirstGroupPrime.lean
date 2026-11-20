import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroup
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

private def firstGroupVars (e n : ℕ) : Fin (e + 1) × Fin n ≃ Fin n ⊕ Fin e × Fin n where
  toFun ij := Fin.cases (motive := fun _ => Fin n ⊕ Fin e × Fin n) (Sum.inl ij.2)
    (fun i => Sum.inr (i, ij.2)) ij.1
  invFun := Sum.elim (fun m => (0, m)) (fun im => (im.1.succ, im.2))
  left_inv := by
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro (m | ⟨i, m⟩) <;> rfl

/- English proof (translation)
Establish `h : (aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive` using `fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) (X ij.2) (fun i => C (X (i, ij.2))) ij.1) : MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] _) = ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))).toAlgHom := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, m⟩`. Apply the tactic sequence `cases i using Fin.cases <;> simp [firstGroupVars]`. Conclude with `DFunLike.congr_fun h g`.
-/
private theorem firstGroup_eq {F : Type*} [Field F] {n e : ℕ} (g : MvPolynomial (Fin (e + 1) × Fin n) F) :
    firstGroup g = ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))) g := by
  have h : (aeval (fun ij : Fin (e + 1) × Fin n =>
      Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
        (X ij.2) (fun i => C (X (i, ij.2))) ij.1) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] _) =
      ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> simp [firstGroupVars]
  exact DFunLike.congr_fun h g

/- English proof (translation)
Introduce `F _ n e I f p _ hI hf`. Take `⟨hf0, hspan⟩` from `isChowForm_iff.mp hf`. Establish `hfp : Prime f`. Use `h₁ F n (e + 1) I hI.isPrime hI.isRelevant` as an intermediate fact. Rewrite `this` using `[hspan]`.

Conclude with `(Ideal.span_singleton_prime hf0).mp this`. Use `set Φ := (renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n)) with hΦ`. Establish `hg : Prime (firstGroup f)`. Rewrite using `[firstGroup_eq]`. Conclude with `(MulEquiv.prime_iff Φ).mpr hfp`.

Establish `hC : ∀ s : MvPolynomial (Fin e × Fin n) F, (C s : MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) = Φ (rename (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) s)`. Introduce `s`. Establish `hcomp : (firstGroupVars e n) ∘ (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) = Sum.inr`. Use function extensionality and compare the values at `im`. Both sides reduce to the same expression.

Rewrite using `[hΦ, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename, hcomp]`. Use `DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr F (Fin n) (Fin e × Fin n)) s` as an intermediate fact. Simplify using `only [AlgHom.coe_comp, Function.comp_apply] at this`. Conclude with `(this.trans (by rw [IsScalarTower.coe_toAlgHom', algebraMap_eq])).symm`. Establish `hdisj : Disjoint ((p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+* MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) : Submonoid _) : Set _) ((Ideal.span {firstGroup f} : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) : Set (MvPolynomial (Fin n) (MvP …`.

Rewrite using `[Set.disjoint_left]`. Introduce `y hy hmem`. Take `⟨s, hs, rfl⟩` from `Submonoid.mem_map.mp hy`. Rewrite `hmem` using `[SetLike.mem_coe, Ideal.mem_span_singleton, hC, firstGroup_eq, map_dvd_iff]`. Establish `hvan` using `(hf.2 _).mpr hmem`.

Establish `hsI : s ∈ incIdeal I e`. Rewrite using `[mem_incIdeal_iff]`. Introduce and unpack `v ⟨x, hx0, hxI, hxv⟩`. Use `hvan (fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) 0 (fun i => v (i, ij.2)) ij.1) ⟨x, hx0, hxI, fun i => by` as an intermediate fact. Consider the cases of `i using Fin.cases with`.

Consider the case `zero => simp`. Consider the case `succ i => simpa using hxv i⟩`. Rewrite `this` using `[aeval_rename]`. Then use the resulting hypothesis. Rewrite `hsI` using `[h₂ F n e I f hI hf, Ideal.mem_bot]`. Conclude with `hs (hsI ▸ p.zero_mem)`.

Use `letI := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := MvPolynomial (Fin e × Fin n) F) (S := Localization.AtPrime p)`. Establish `hprime` using `IsLocalization.isPrime_of_isPrime_disjoint (p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+* MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) (MvPolynomial (Fin n) (Localization.AtPrime p)) _ ((Ideal.span_singleton_prime hg.ne_zero).mpr hg) hdisj`. Rewrite `hprime` using `[Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def]`. Use `(Ideal.span_singleton_prime fun h => hg.ne_zero ?_).mp hprime` and prove the remaining obligations. Conclude with `map_injective _ (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm)`.
-/
theorem ChartFirstGroupPrime.proof (h₁ : IncIdealPrime.Statement) (h₂ : IncIdealBelow.Statement) :
    ChartFirstGroupPrime.Statement := by
  intro F _ n e I f p _ hI hf
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  set Φ := (renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n)) with hΦ
  have hg : Prime (firstGroup f) := by
    rw [firstGroup_eq]
    exact (MulEquiv.prime_iff Φ).mpr hfp

  have hC : ∀ s : MvPolynomial (Fin e × Fin n) F,
      (C s : MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) =
        Φ (rename (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) s) := by
    intro s
    have hcomp : (firstGroupVars e n) ∘ (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) =
        Sum.inr := by
      funext im
      rfl
    rw [hΦ, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename, hcomp]
    have := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr F (Fin n) (Fin e × Fin n)) s
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact (this.trans (by rw [IsScalarTower.coe_toAlgHom', algebraMap_eq])).symm
  have hdisj : Disjoint ((p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) : Submonoid _) : Set _)
      ((Ideal.span {firstGroup f} : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) := by
    rw [Set.disjoint_left]
    intro y hy hmem
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hC, firstGroup_eq, map_dvd_iff] at hmem
    have hvan := (hf.2 _).mpr hmem
    have hsI : s ∈ incIdeal I e := by
      rw [mem_incIdeal_iff]
      rintro v ⟨x, hx0, hxI, hxv⟩
      have := hvan (fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) 0 (fun i => v (i, ij.2)) ij.1)
        ⟨x, hx0, hxI, fun i => by
          cases i using Fin.cases with
          | zero => simp
          | succ i => simpa using hxv i⟩
      rwa [aeval_rename] at this
    rw [h₂ F n e I f hI hf, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ p.zero_mem)
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := MvPolynomial (Fin e × Fin n) F)
    (S := Localization.AtPrime p)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)))
    (MvPolynomial (Fin n) (Localization.AtPrime p)) _
    ((Ideal.span_singleton_prime hg.ne_zero).mpr hg) hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hprime
  refine (Ideal.span_singleton_prime fun h => hg.ne_zero ?_).mp hprime
  exact map_injective _ (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
    (h.trans (map_zero _).symm)

end

end GroundTheory.Heights₂.Heights
