import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)

noncomputable section

open Matrix

namespace GlobalTheory.FlagZ.Univ

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`. Use `set b := stalkStd X N x`. Use `set c : Fin N → X.presheaf.stalk x := (g⁻¹).1 *ᵥ (b.repr v) with hc`. Establish `hgc : g.1 *ᵥ c = b.repr v`.

Rewrite using `[hc, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `key : ∀ i, ∑ j, c j * g.1 i j = b.repr v i`. Introduce `i`. Use `congrFun hgc i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, mul_comm]`.

Establish `hv : v = ∑ j, c j • ∑ i, g.1 i j • b i`. Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, key]`. Conclude with `(b.sum_repr v).symm`.

Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)`.
-/
theorem colSpan_units_top {X : Scheme.{0}} {N : ℕ} {x : X} (g : GL (Fin N) (X.presheaf.stalk x)) :
    colSpan g.1 N = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  set b := stalkStd X N x
  set c : Fin N → X.presheaf.stalk x := (g⁻¹).1 *ᵥ (b.repr v) with hc
  have hgc : g.1 *ᵥ c = b.repr v := by
    rw [hc, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have key : ∀ i, ∑ j, c j * g.1 i j = b.repr v i := by
    intro i
    have := congrFun hgc i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  have hv : v = ∑ j, c j • ∑ i, g.1 i j • b i := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, key]
    exact (b.sum_repr v).symm
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)

variable (ι : Type) [Fintype ι] (N : ℕ)

/- English proof (translation)
Simplify using `[stalkStep, colSpan_units_top]`.
-/
theorem stalkStep_self (τ : ι) (y : Fl ι N) : stalkStep ι N τ N y = ⊤ := by
  simp [stalkStep, colSpan_units_top]

/- English proof (translation)
Introduce `x hx`. Establish `e : stalkStep ι N τ (Fin.last N : ℕ) x = ⊤` using `by rw [Fin.val_last, stalkStep_self]`. Use `show _ ∈ stalkStep ι N τ (Fin.last N : ℕ) x`. Rewrite using `[e]`. Conclude with `Submodule.mem_top`.
-/
theorem mem_sub_last (τ : ι) (V : (Fl ι N).Opens) (s : Γ(freeModule (Fl ι N) (Fin N), V)) :
    s ∈ (sub ι N τ (Fin.last N)).sec V := by
  intro x hx
  have e : stalkStep ι N τ (Fin.last N : ℕ) x = ⊤ := by rw [Fin.val_last, stalkStep_self]
  show _ ∈ stalkStep ι N τ (Fin.last N : ℕ) x
  rw [e]
  exact Submodule.mem_top

instance isIso_sub_incl_last (τ : ι) : IsIso (sub ι N τ (Fin.last N)).incl := by
  refine ⟨⟨(sub ι N τ (Fin.last N)).lift (𝟙 _) (fun V s => mem_sub_last ι N τ V _), ?_,
    VB.Sub.lift_incl _ _ _⟩⟩
  rw [← cancel_mono (sub ι N τ (Fin.last N)).incl, Category.assoc, VB.Sub.lift_incl, Category.comp_id,
    Category.id_comp]

/- English proof (translation)
Introduce `ι _ N τ`. Establish `h` using `isIso_sub_incl_last ι N τ`. Unfold `incl`. Conclude with `@IsIso.comp_isIso _ _ _ _ _ _ _ h _`.
-/
theorem isIso_incl_last : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (incl ι N τ (Fin.last N)) := by
  intro ι _ N τ
  have h := isIso_sub_incl_last ι N τ
  unfold incl
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h _

end GlobalTheory.FlagZ.Univ
