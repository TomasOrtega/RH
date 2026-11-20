import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`.
-/
theorem incl_mem_lamAf (L : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ L) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, rfl⟩` from `hy`. Conclude with `⟨x, x.2, 0, zero_mem _, by simp⟩`. Consider the case `zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨x, hx, z, hz, rfl⟩` from `ha`. Take `⟨x', hx', z', hz', rfl⟩` from `hb`. Use `⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul s a _ ha`. Take `⟨x, hx, z, hz, rfl⟩` from `ha`. Take `⟨r, hr, w, hw, e⟩` from `Formalism.UG.P.csSpan_approx (F := F) (E := E) Formalism.UG.P.csGlob_intAdApprox (g : 𝓞 F) (Nat.cast_ne_zero.2 (by omega)) s.2`.

Rewrite `e` using `[GlobalTheory.AutInhab.levelafC_natCast]`. Use `⟨(⟨r, hr⟩ : 𝓞 E) • x, L.smul_mem _ hx, (⟨w, hw⟩ : IntAf F E) • (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + s • z, add_mem (Submodule.smul_mem _ _ (incl_mem_lamAf L hx)) (Submodule.smul_mem _ _ hz), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show (s : E ⊗[F] Af F) * (Formalism.UG.inclE (F := F) (Af F) (x i) + (g : E ⊗[F] Af F) * z i) = Formalism.UG.inclE (F := F) (Af F) (r * x i) + (g : E ⊗[F] Af F) * (w * Formalism.UG.inclE (F := F) (Af F) (x i) + (s : E ⊗[F] Af F) * z i)`. Rewrite using `[map_mul]`.

Take the linear combination `Formalism.UG.inclE (F := F) (Af F) (x i) * e`.
-/
theorem exists_approx (L : Submodule (𝓞 E) (Fin n → E)) (g : ℕ) (hg : 1 ≤ g)
    (y : Fin n → E ⊗[F] Af F) (hy : y ∈ lamAf (F := F) L) :
    ∃ x ∈ L, ∃ z ∈ lamAf (F := F) L,
      y = (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + (g : E ⊗[F] Af F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, x.2, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨x', hx', z', hz', rfl⟩ := hb
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring
  | smul s a _ ha =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨r, hr, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := F) (E := E) Formalism.UG.P.csGlob_intAdApprox
      (g : 𝓞 F) (Nat.cast_ne_zero.2 (by omega)) s.2
    rw [GlobalTheory.AutInhab.levelafC_natCast] at e
    refine ⟨(⟨r, hr⟩ : 𝓞 E) • x, L.smul_mem _ hx,
      (⟨w, hw⟩ : IntAf F E) • (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + s • z,
      add_mem (Submodule.smul_mem _ _ (incl_mem_lamAf L hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    funext i
    show (s : E ⊗[F] Af F) * (Formalism.UG.inclE (F := F) (Af F) (x i) + (g : E ⊗[F] Af F) * z i) =
      Formalism.UG.inclE (F := F) (Af F) (r * x i) + (g : E ⊗[F] Af F) *
        (w * Formalism.UG.inclE (F := F) (Af F) (x i) + (s : E ⊗[F] Af F) * z i)
    rw [map_mul]
    linear_combination Formalism.UG.inclE (F := F) (Af F) (x i) * e

/- English proof (translation)
Use `⟨fun h => ?_, incl_mem_lamAf L⟩` and prove the remaining obligations. Rewrite using `[← Formalism.UG.P.global_lattice_one_holds F E (Fin n) L (Module.Finite.iff_fg.2 hfg) hspan]`. Use `show ((1⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.UG.latS (F := F) (Af F) (IntAf F E) L`. Rewrite using `[inv_one, Units.val_one, one_mulVec]`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨y, y.2, rfl⟩`.
-/
theorem incl_mem_iff (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L ↔ x ∈ L := by
  refine ⟨fun h => ?_, incl_mem_lamAf L⟩
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) L (Module.Finite.iff_fg.2 hfg) hspan]
  show ((1⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.UG.latS (F := F) (Af F) (IntAf F E) L
  rw [inv_one, Units.val_one, one_mulVec]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨y, rfl⟩
  exact ⟨y, y.2, rfl⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨m, hm, hy⟩` from `GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hspan y`. Take `⟨u, hu⟩` from `GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) m hm`. Establish `: y = ((u⁻¹ : (E ⊗[F] Af F)ˣ) : E ⊗[F] Af F) • ((m : E ⊗[F] Af F) • y)`.

Rewrite using `[smul_smul, ← hu, Units.inv_mul, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hy)`.
-/
theorem span_lamAf (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (E ⊗[F] Af F) (lamAf (F := F) L : Set (Fin n → E ⊗[F] Af F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hy⟩ := GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hspan y
  obtain ⟨u, hu⟩ := GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) m hm
  have : y = ((u⁻¹ : (E ⊗[F] Af F)ˣ) : E ⊗[F] Af F) • ((m : E ⊗[F] Af F) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

/- English proof (translation)
Introduce `I g hg` and use `⟨exists_approx I.L g hg, incl_mem_iff I.L I.L_fg I.L_span, span_lamAf I.L I.L_span, GlobalTheory.AutInhab.lamAf_fg I.L I.L_fg, GlobalTheory.AutInhab.lamAf_absorbs I.L I.L_span⟩`.
-/
theorem adelicLattice_spec : ∀ (I : AutInst) (g : ℕ), 1 ≤ g → (∀ y ∈ I.Lf, ∃ x ∈ I.L, ∃ z ∈ I.Lf, y = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) + (g : (I.E ⊗[I.F] Af I.F)) • z) ∧ (∀ x : Fin I.n → I.E, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∈ I.Lf ↔ x ∈ I.L) ∧ Submodule.span (I.E ⊗[I.F] Af I.F) (I.Lf : Set (Fin I.n → (I.E ⊗[I.F] Af I.F))) = ⊤ ∧ I.Lf.FG ∧ ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 1 ≤ m ∧ (m : (I.E ⊗[I.F] Af I.F)) • y ∈ I.Lf :=
  fun I g hg => ⟨exists_approx I.L g hg, incl_mem_iff I.L I.L_fg I.L_span, span_lamAf I.L I.L_span,
    GlobalTheory.AutInhab.lamAf_fg I.L I.L_fg, GlobalTheory.AutInhab.lamAf_absorbs I.L I.L_span⟩

end GlobalTheory.AdelicLattice
