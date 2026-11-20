import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

/- English proof (translation)
Introduce `x hx`. Establish `h0 : ϖ ≠ 0` using `Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ`. Use `set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg`. Establish `hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Unfold `Formalism.UG.diagJ`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[i.2]`. Simplify using `[Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]`.

Establish `hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g` using `fun a => by`. Use extensionality with `: 1`. Rewrite using `[Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]`. Simplify using the standard rewrite rules. Establish `hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w n) g`.

Unfold `Formalism.UG.Tj Formalism.UG.dosetInd`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, b, hb, e⟩`. Conclude with `⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Rewrite using `[hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]`. Simplify using the standard rewrite rules. Introduce `γ hγ`. Rewrite using `[Finset.mem_singleton.1 hγ]`. Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩`.

Introduce `y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hy`. Use `⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩` and prove the remaining obligations. Establish `: g⁻¹ * (a * g * b) = a * b`. Rewrite using `[← hcomm a]`.

Use `group`. Rewrite using `[this]`. Conclude with `(GlobalTheory.LFun.KGL w n).mul_mem ha hb`.
-/
theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w n) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem ha hb

end GlobalTheory.LFun
