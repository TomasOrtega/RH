import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
import Lemmata.GeneralBFactRightAltForm.Imports

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module

section

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_alt_form.goal1 .. | (apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption)`.
-/
theorem lretr_den (A : Set V) (y : V) (hy : y ∈ Submodule.span E A) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Submodule.span (𝓞 E) A := by
  first | exact Bl.general_b_fact_right_alt_form.goal1 .. | (apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption)

/- English proof (translation)
Establish `hdE : algebraMap (𝓞 E) E d ≠ 0`. Introduce `h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))`. Rewrite `h` using `[← algebraMap_smul E d, ← algebraMap_smul E d]`. Conclude with `smul_right_injective V hdE h`.
-/
theorem lretr_cancel (d : 𝓞 E) (hd : d ≠ 0) (x y : V) (h : d • x = d • y) : x = y := by
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  rw [← algebraMap_smul E d, ← algebraMap_smul E d] at h
  exact smul_right_injective V hdE h

/- English proof (translation)
Establish `hdE : algebraMap (𝓞 E) E d ≠ 0`. Introduce `h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))`. Rewrite `h` using `[← algebraMap_smul E d]`. Conclude with `(Submodule.smul_mem_iff X hdE).1 h`.
-/
theorem lretr_mem (X : Submodule E V) (d : 𝓞 E) (hd : d ≠ 0) (x : V) (h : d • x ∈ X) : x ∈ X := by
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  rw [← algebraMap_smul E d] at h
  exact (Submodule.smul_mem_iff X hdE).1 h

/- English proof (translation)
Set `N : Submodule (𝓞 E) Λ` to `(X.restrictScalars (𝓞 E)).comap Λ.subtype`. Establish `hmemN : ∀ l : Λ, l ∈ N ↔ (l : V) ∈ X` using `fun l => Iff.rfl`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 hfg`. Establish `: Module.IsTorsionFree (𝓞 E) (Λ ⧸ N)`. Apply `Module.IsTorsionFree.of_smul_eq_zero` to reduce the goal to its premises.

Introduce `r m hrm`. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`. Take `⟨l, rfl⟩` from `N.mkQ_surjective m`.

Rewrite `hrm` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]`. Conclude with `lretr_mem X r hr _ hrm`. Establish `: Module.FinitePresentation (𝓞 E) (Λ ⧸ N)` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) (Λ ⧸ N)` using `Module.Flat.projective_of_finitePresentation`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective`. Use `⟨LinearMap.id - s ∘ₗ N.mkQ, fun l => ?_, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[← hmemN, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply] show N.mkQ (l - s (N.mkQ l)) = 0`. Use `LinearMap.congr_fun hs (N.mkQ l)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`.

Rewrite using `[map_sub, this, sub_self]`. Establish `h0 : N.mkQ l = 0` using `by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]; exact hl`. Simplify using `[h0]`.
-/
theorem lretr_rho (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ l : Λ, ((ρ l : Λ) : V) ∈ X) ∧ ∀ l : Λ, (l : V) ∈ X → ρ l = l := by
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have hmemN : ∀ l : Λ, l ∈ N ↔ (l : V) ∈ X := fun l => Iff.rfl
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  have : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨l, rfl⟩ := N.mkQ_surjective m
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]
      exact lretr_mem X r hr _ hrm
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  refine ⟨LinearMap.id - s ∘ₗ N.mkQ, fun l => ?_, fun l hl => ?_⟩
  · rw [← hmemN, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    show N.mkQ (l - s (N.mkQ l)) = 0
    have := LinearMap.congr_fun hs (N.mkQ l)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [map_sub, this, sub_self]
  · have h0 : N.mkQ l = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]; exact hl
    simp [h0]

end

/- English proof (translation)
Introduce `E _ _ _ S Λ X hΛ`. Take `⟨ρ, hρX, hρid⟩` from `lretr_rho Λ hΛ.fg X`. Take `⟨b, hbΛ, hbs, hbi⟩` from `exists_linearIndependent E (Λ : Set S.V)`. Establish `hspan : Submodule.span E b = ⊤` using `by rw [hbs]; exact hΛ.span_eq_top`. Set `B : Basis b E S.V` to `Basis.mk hbi (by rw [Subtype.range_coe]; exact hspan.ge)`.

Establish `hB : ∀ i : b, B i = (i : S.V)` using `fun i => by simp [B]`. Set `P : S.V →ₗ[E] S.V` to `B.constr E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V))`. Establish `hPb : ∀ i : b, P (i : S.V) = ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V)` using `fun i => by`. Establish `h` using `B.constr_basis E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V)) i`. Rewrite `h` using `[hB i]`.

Conclude with `h`. Establish `hPsm : ∀ (d : 𝓞 E) (y : S.V), P (d • y) = d • P y` using `fun d y => by`. Rewrite using `[← algebraMap_smul E d, map_smul, algebraMap_smul]`. Establish `hPspan : ∀ y (hy : y ∈ Submodule.span (𝓞 E) b) (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V)`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => intro hyΛ`. Conclude with `hPb ⟨x, hx⟩`. Consider the case `zero`. Introduce `hyΛ`.

Establish `: (⟨0, hyΛ⟩ : Λ) = 0` using `rfl`. Rewrite using `[this, map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy ihx ihy`. Introduce `hyΛ`.

Establish `hxΛ : x ∈ Λ` using `Submodule.span_le.2 hbΛ hx`. Establish `hyΛ' : y ∈ Λ` using `Submodule.span_le.2 hbΛ hy`. Establish `: (⟨x + y, hyΛ⟩ : Λ) = ⟨x, hxΛ⟩ + ⟨y, hyΛ'⟩` using `rfl`. Rewrite using `[this, map_add, map_add, ihx hxΛ, ihy hyΛ']`. Both sides reduce to the same expression.

Consider the case `smul c x hx ihx`. Introduce `hyΛ`. Establish `hxΛ : x ∈ Λ` using `Submodule.span_le.2 hbΛ hx`. Establish `: (⟨c • x, hyΛ⟩ : Λ) = c • ⟨x, hxΛ⟩` using `rfl`. Rewrite using `[hPsm, this, map_smul, ihx hxΛ]`.

Both sides reduce to the same expression. Establish `hPΛ : ∀ y (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V)`. Introduce `y hyΛ`. Take `⟨d, hd, hdy⟩` from `lretr_den (b : Set S.V) y (by rw [hspan]; trivial)`. Apply `lretr_cancel d hd` to reduce the goal to its premises.

Rewrite using `[← hPsm, hPspan _ hdy (Λ.smul_mem d hyΛ)]`. Establish `: (⟨d • y, Λ.smul_mem d hyΛ⟩ : Λ) = d • ⟨y, hyΛ⟩` using `rfl`. Rewrite using `[this, map_smul]`. Both sides reduce to the same expression. Establish `hden : ∀ y : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ`.

Introduce `y`. Take `⟨d, hd, hdy⟩` from `lretr_den (b : Set S.V) y (by rw [hspan]; trivial)`. Conclude with `⟨d, hd, Submodule.span_le.2 hbΛ hdy⟩`. Use `⟨P, fun x hx => ?_, fun y => ?_, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, hdx⟩` from `hden x`.

Apply `lretr_cancel d hd` to reduce the goal to its premises. Rewrite using `[← hPsm, hPΛ _ hdx, hρid ⟨d • x, hdx⟩ (by show d • x ∈ X`. Rewrite using `[← algebraMap_smul E d]`. Conclude with `X.smul_mem _ hx)]`. Take `⟨d, hd, hdy⟩` from `hden y`.

Apply `lretr_mem X d hd` to reduce the goal to its premises. Rewrite using `[← hPsm, hPΛ _ hdy]`. Conclude with `hρX _`. Rewrite using `[hPΛ l hl]`. Conclude with `(ρ ⟨l, hl⟩).2`.
-/
theorem l_retr : IntegralRetraction := by
  intro E _ _ _ S Λ X hΛ
  obtain ⟨ρ, hρX, hρid⟩ := lretr_rho Λ hΛ.fg X
  obtain ⟨b, hbΛ, hbs, hbi⟩ := exists_linearIndependent E (Λ : Set S.V)
  have hspan : Submodule.span E b = ⊤ := by rw [hbs]; exact hΛ.span_eq_top
  let B : Basis b E S.V := Basis.mk hbi (by rw [Subtype.range_coe]; exact hspan.ge)
  have hB : ∀ i : b, B i = (i : S.V) := fun i => by simp [B]
  let P : S.V →ₗ[E] S.V := B.constr E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V))
  have hPb : ∀ i : b, P (i : S.V) = ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V) := fun i => by
    have h := B.constr_basis E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V)) i
    rw [hB i] at h
    exact h
  have hPsm : ∀ (d : 𝓞 E) (y : S.V), P (d • y) = d • P y := fun d y => by
    rw [← algebraMap_smul E d, map_smul, algebraMap_smul]

  have hPspan : ∀ y (hy : y ∈ Submodule.span (𝓞 E) b) (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hyΛ; exact hPb ⟨x, hx⟩
    | zero =>
      intro hyΛ
      have : (⟨0, hyΛ⟩ : Λ) = 0 := rfl
      rw [this, map_zero, map_zero]; rfl
    | add x y hx hy ihx ihy =>
      intro hyΛ
      have hxΛ : x ∈ Λ := Submodule.span_le.2 hbΛ hx
      have hyΛ' : y ∈ Λ := Submodule.span_le.2 hbΛ hy
      have : (⟨x + y, hyΛ⟩ : Λ) = ⟨x, hxΛ⟩ + ⟨y, hyΛ'⟩ := rfl
      rw [this, map_add, map_add, ihx hxΛ, ihy hyΛ']; rfl
    | smul c x hx ihx =>
      intro hyΛ
      have hxΛ : x ∈ Λ := Submodule.span_le.2 hbΛ hx
      have : (⟨c • x, hyΛ⟩ : Λ) = c • ⟨x, hxΛ⟩ := rfl
      rw [hPsm, this, map_smul, ihx hxΛ]; rfl
  have hPΛ : ∀ y (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V) := by
    intro y hyΛ
    obtain ⟨d, hd, hdy⟩ := lretr_den (b : Set S.V) y (by rw [hspan]; trivial)
    apply lretr_cancel d hd
    rw [← hPsm, hPspan _ hdy (Λ.smul_mem d hyΛ)]
    have : (⟨d • y, Λ.smul_mem d hyΛ⟩ : Λ) = d • ⟨y, hyΛ⟩ := rfl
    rw [this, map_smul]; rfl
  have hden : ∀ y : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ := by
    intro y
    obtain ⟨d, hd, hdy⟩ := lretr_den (b : Set S.V) y (by rw [hspan]; trivial)
    exact ⟨d, hd, Submodule.span_le.2 hbΛ hdy⟩
  refine ⟨P, fun x hx => ?_, fun y => ?_, fun l hl => ?_⟩
  · obtain ⟨d, hd, hdx⟩ := hden x
    apply lretr_cancel d hd
    rw [← hPsm, hPΛ _ hdx, hρid ⟨d • x, hdx⟩ (by
      show d • x ∈ X
      rw [← algebraMap_smul E d]; exact X.smul_mem _ hx)]
  · obtain ⟨d, hd, hdy⟩ := hden y
    apply lretr_mem X d hd
    rw [← hPsm, hPΛ _ hdy]
    exact hρX _
  · rw [hPΛ l hl]
    exact (ρ ⟨l, hl⟩).2

end Formalism.MainNotions.BridgeLemma

end
