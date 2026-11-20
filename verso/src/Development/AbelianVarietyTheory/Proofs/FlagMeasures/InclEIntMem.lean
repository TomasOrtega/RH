import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists

open NumberField
open scoped TensorProduct

noncomputable section
open Classical

namespace GlobalTheory.VectorInclusion

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)

/- English proof (translation)
Unfold `Formalism.MainNotions.S.IntAf Formalism.UG.tensInt`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Use `⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecIncl, map_add]`.
-/
theorem vecIncl_add (x y : Fin n → E) :
    vecIncl (F := F) (x + y) = vecIncl (F := F) x + vecIncl (F := F) y := by
  funext i; simp [vecIncl, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecIncl]`.
-/
theorem vecIncl_zero : vecIncl (F := F) (0 : Fin n → E) = 0 := by
  funext i; simp [vecIncl]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [vecIncl, Pi.smul_apply]`. Rewrite using `[Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem vecIncl_smul (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `hL`. Use `⟨s.image (vecIncl (F := F)), ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `y hy`.

Simplify using `only [Finset.coe_image, Set.mem_image] at hy`. Take `⟨x, hx, rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Establish `hxL : x ∈ L` using `hs ▸ Submodule.subset_span hx`. Conclude with `⟨⟨x, hxL⟩, rfl⟩`.

Unfold `Formalism.MainNotions.S.lamAf`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨⟨x, hx⟩, rfl⟩`. Establish `key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)), vecIncl (F` using `F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E) ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [Finset.coe_image]`. Conclude with `⟨z, hz, rfl⟩`.

Consider the case `zero => rw [vecIncl_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [vecIncl_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [vecIncl_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`. Rewrite `hx` using `[← hs]`. Conclude with `key x hx`.
-/
theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx

/- English proof (translation)
Introduce `L hL` and use `lamAf_fg L hL`.
-/
theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) :=
  fun L hL => lamAf_fg L hL

end GlobalTheory.VectorInclusion

end
