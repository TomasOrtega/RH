import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ListProdFactor

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP l hl h hh f φ φ₁ hφSB hφstd`. Proceed by induction on `l generalizing φ₁ with`. Consider the case `nil`. Introduce `_ hout`. Establish `e : φ₁ = φ` using `funext fun v => hout v (List.not_mem_nil)`.

Substitute `e` using the available equality. Use `show om 1 _ = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Consider the case `cons a l' ih`.

Introduce `hin hout`. Establish `ha : a ∉ l'` using `(List.nodup_cons.1 hl).1`. Establish `hl' : l'.Nodup` using `(List.nodup_cons.1 hl).2`. Set `φ₁' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ` to `fun v => if v ∈ l' then φ₁ v else φ v`. Establish `hφ₁'a : φ₁' a = φ a` using `by simp only [φ₁', if_neg ha]`.

Establish `hIH : om (1, (l'.map h).prod) (pure f φ) = pure f φ₁'`. Use `ih hl' (fun v hv => hh v (List.mem_cons_of_mem a hv)) φ₁' ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Use `hin v (List.mem_cons_of_mem a hv)` as an intermediate fact. Simplify using `only [φ₁', if_pos hv]`.

Conclude with `this`. Introduce `v hv`. Simplify using `only [φ₁', if_neg hv]`. Establish `hSB' : ∀ v, φ₁' v ∈ SB _`. Introduce `v`.

Distinguish the cases in `hv : v ∈ l'`. Simplify using `only [φ₁', if_pos hv]`. Conclude with `(hin v (List.mem_cons_of_mem a hv)).1`. Simplify using `only [φ₁', if_neg hv]`. Conclude with `hφSB v`.

Establish `hstd' : ∀ᶠ v in Filter.cofinite, φ₁' v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Establish `hfin : ∀ᶠ v in Filter.cofinite, v ∉ l'` using `(l'.finite_toSet).compl_mem_cofinite`. Use `filter_upwards [hφstd, hP.good.std, hfin] with v h1 h2 h3`. Simplify using `only [φ₁', if_neg h3]`. Rewrite using `[h1, h2]`.

Establish `hpure` using `GlobalTheory.TensUniq.pure_mem_schA f φ₁' hSB' hstd'`. Establish `hmul` using `fun x => GlobalTheory.PureFactor.mulSupport_finite φ₁' hstd' x`. Establish `hacts : Acts (evFin F a) (om (1, h a)) (φ₁' a) (φ₁ a)`. Rewrite using `[hφ₁'a]`. Conclude with `(hin a List.mem_cons_self).2`.

Establish `hstep` using `GlobalTheory.ThK.LocalOps.acts_pure a (om (1, h a)) f φ₁' (φ₁ a) hpure hmul hacts`. Establish `hupd : Function.update φ₁' a (φ₁ a) = φ₁`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hva : v = a`. Substitute `hva` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hva]`. Distinguish the cases in `hv : v ∈ l'`. Simplify using `only [φ₁', if_pos hv]`. Simplify using `only [φ₁', if_neg hv]`.

Conclude with `(hout v (by simp [hva, hv])).symm`. Establish `hsplit : ((1 : UA σ X.J), ((a :: l').map h).prod) = ((1 : UA σ X.J), h a) * (1, (l'.map h).prod)`. Rewrite using `[List.map_cons, List.prod_cons]`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[hsplit, map_mul, Module.End.mul_apply, hIH, hstep, hupd]`.
-/
theorem om_listProd_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (l : List (Pl F)), l.Nodup → ∀ h : Pl F → UA σ W.J, (∀ v ∈ l, h v ∈ UAt σ W (evFin F v)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      (∀ v ∈ l, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v)) → (∀ v, v ∉ l → φ₁ v = φ v) →
      om (1, (l.map h).prod) (pure f φ) = pure f φ₁ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP l hl h hh f φ φ₁ hφSB hφstd
  classical
  induction l generalizing φ₁ with
  | nil =>
    intro _ hout
    have e : φ₁ = φ := funext fun v => hout v (List.not_mem_nil)
    subst e
    show om 1 _ = _
    rw [map_one]
    rfl
  | cons a l' ih =>
    intro hin hout
    have ha : a ∉ l' := (List.nodup_cons.1 hl).1
    have hl' : l'.Nodup := (List.nodup_cons.1 hl).2
    let φ₁' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if v ∈ l' then φ₁ v else φ v
    have hφ₁'a : φ₁' a = φ a := by simp only [φ₁', if_neg ha]
    have hIH : om (1, (l'.map h).prod) (pure f φ) = pure f φ₁' := by
      refine ih hl' (fun v hv => hh v (List.mem_cons_of_mem a hv)) φ₁' ?_ ?_
      · intro v hv
        have := hin v (List.mem_cons_of_mem a hv)
        simp only [φ₁', if_pos hv]
        exact this
      · intro v hv
        simp only [φ₁', if_neg hv]
    have hSB' : ∀ v, φ₁' v ∈ SB _ := by
      intro v
      by_cases hv : v ∈ l'
      · simp only [φ₁', if_pos hv]; exact (hin v (List.mem_cons_of_mem a hv)).1
      · simp only [φ₁', if_neg hv]; exact hφSB v
    have hstd' : ∀ᶠ v in Filter.cofinite,
        φ₁' v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      have hfin : ∀ᶠ v in Filter.cofinite, v ∉ l' :=
        (l'.finite_toSet).compl_mem_cofinite
      filter_upwards [hφstd, hP.good.std, hfin] with v h1 h2 h3
      simp only [φ₁', if_neg h3]
      rw [h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁' hSB' hstd'
    have hmul := fun x => GlobalTheory.PureFactor.mulSupport_finite φ₁' hstd' x
    have hacts : Acts (evFin F a) (om (1, h a)) (φ₁' a) (φ₁ a) := by
      rw [hφ₁'a]; exact (hin a List.mem_cons_self).2
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure a (om (1, h a)) f φ₁' (φ₁ a) hpure hmul hacts
    have hupd : Function.update φ₁' a (φ₁ a) = φ₁ := by
      funext v
      by_cases hva : v = a
      · subst hva; simp
      · rw [Function.update_of_ne hva]
        by_cases hv : v ∈ l'
        · simp only [φ₁', if_pos hv]
        · simp only [φ₁', if_neg hv]
          exact (hout v (by simp [hva, hv])).symm
    have hsplit : ((1 : UA σ X.J), ((a :: l').map h).prod) = ((1 : UA σ X.J), h a) * (1, (l'.map h).prod) := by
      rw [List.map_cons, List.prod_cons]
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hIH, hstep, hupd]

end GlobalTheory.ListProdFactor
