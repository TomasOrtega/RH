import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJumpStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpsFinite

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D HW l _ K s LL h T hcrys`. Establish `hP` using `GlobalTheory.NL.Points.points D HW l K s LL h`. Establish `hfin : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[hP.2.2.2.1]`.

Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2`. Conclude with `Module.finrank_pos.ne'`. Establish `hsub : Jumps (PD` using `(D.loc l).PD K) T ⊆ ⋃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, {a | IsJumpV ((D.loc l).PD K) T.ρ τ a} := by`. Introduce and unpack `a ⟨τ, hτ⟩`. Conclude with `Set.mem_iUnion.2 ⟨τ, hτ⟩`.

Use `(Set.finite_iUnion fun τ => ?_).subset hsub` and prove the remaining obligations. Take `⟨i, ζ, hpt⟩` from `hP.2.2.1 τ`. Take `⟨-, hemb, ι, hcomp⟩` from `hP.2.1 i ζ τ hpt`. Establish `hC` using `GlobalTheory.NL.CompD.component D HW l K s LL h T hcrys i ζ τ ι hcomp hemb`. Establish `hrank` using `hC.2.2.2`.

Use `set Dm := Di (HW l) h T i with hDm`. Establish `hDfin : FiniteDimensional ↥LL.1 ↥Dm`. Break down `Nat.eq_zero_or_pos (Module.finrank ↥LL.1 T.V) with h0 | hpos` into its components or cases. Establish `hV : Subsingleton T.V` using `Module.finrank_zero_iff.1 h0`. Establish `hVB : Subsingleton (T.V ⊗[ℚ_[l]] (D.loc l).R.B)`.

Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ z : T.V ⊗[ℚ_[l]] (D.loc l).R.B, z = 0`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`.

Consider the case `tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Rewrite using `[hz x, hz y]`. Use `infer_instance`. Conclude with `Module.finite_of_finrank_pos (hrank ▸ hpos)`.

Set `S : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B)` to `fun a => Dm ⊓ (FilAt ((D.loc l).PD K) T τ a).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))`. Establish `hSanti : Antitone S`. Use `antitone_int_of_succ_le fun a => inf_le_inf_left _ (Submodule.comap_mono ?_)` and prove the remaining obligations. Conclude with `sup_le_sup_right (GlobalTheory.Pst.filDR_succ_le ((D.loc l).PD K) T.ρ τ a) _`. Set `f : ℤ → ℕ` to `fun a => Module.finrank ↥LL.1 ↥(S a)`.

Establish `hfS : ∀ a, Module.finrank ↥LL.1 ↥(S a) ≤ Module.finrank ↥LL.1 ↥Dm` using `fun a => Submodule.finrank_mono inf_le_left`. Establish `hlt : ∀ a b, IsJumpV ((D.loc l).PD K) T.ρ τ a → a < b → f b < f a`. Introduce `a b ha hab`. Take `⟨d, hd, h1, h2⟩` from `GlobalTheory.T.exists_crystallineLetter_of_hodgeJump D HW l K s LL h T hcrys i ζ τ hpt a ha`. Establish `hle : S b ≤ S (a + 1)` using `hSanti (by omega)`.

Establish `hlt' : S (a + 1) < S a`. Use `lt_of_le_of_ne (hSanti (by omega)) fun heq => h2 ?_` and prove the remaining obligations. Establish `: d ∈ S a` using `⟨hd, h1⟩`. Rewrite `this` using `[← heq]`. Conclude with `this.2`.

Use `haveI : FiniteDimensional ↥LL.1 ↥(S a) := Submodule.finiteDimensional_of_le (inf_le_left : S a ≤ Dm)`. Conclude with `lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt')`. Use `Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (Module.finrank ↥LL.1 ↥Dm)).subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`. Conclude with `hfS a`.

Introduce `a ha b hb hab`. Break down `lt_trichotomy a b with hh | hh | hh` into its components or cases. Conclude with `absurd hab (hlt a b ha hh).ne'`. Conclude with `hh`. Conclude with `absurd hab (hlt b a hb hh).ne`.
-/
theorem jumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
    (Jumps (PD := (D.loc l).PD K) T).Finite := by
  intro D HW l _ K s LL h T hcrys
  have hP := GlobalTheory.NL.Points.points D HW l K s LL h
  have hfin : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hP.2.2.2.1]
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    exact Module.finrank_pos.ne'
  have hsub : Jumps (PD := (D.loc l).PD K) T ⊆
      ⋃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, {a | IsJumpV ((D.loc l).PD K) T.ρ τ a} := by
    rintro a ⟨τ, hτ⟩
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  refine (Set.finite_iUnion fun τ => ?_).subset hsub
  obtain ⟨i, ζ, hpt⟩ := hP.2.2.1 τ
  obtain ⟨-, hemb, ι, hcomp⟩ := hP.2.1 i ζ τ hpt
  have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hcrys i ζ τ ι hcomp hemb
  have hrank := hC.2.2.2
  set Dm := Di (HW l) h T i with hDm
  have hDfin : FiniteDimensional ↥LL.1 ↥Dm := by
    rcases Nat.eq_zero_or_pos (Module.finrank ↥LL.1 T.V) with h0 | hpos
    · have hV : Subsingleton T.V := Module.finrank_zero_iff.1 h0
      have hVB : Subsingleton (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : T.V ⊗[ℚ_[l]] (D.loc l).R.B, z = 0 := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz x, hz y]
      infer_instance
    · exact Module.finite_of_finrank_pos (hrank ▸ hpos)
  let S : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := fun a =>
    Dm ⊓ (FilAt ((D.loc l).PD K) T τ a).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
  have hSanti : Antitone S := by
    refine antitone_int_of_succ_le fun a => inf_le_inf_left _ (Submodule.comap_mono ?_)
    exact sup_le_sup_right (GlobalTheory.Pst.filDR_succ_le ((D.loc l).PD K) T.ρ τ a) _
  let f : ℤ → ℕ := fun a => Module.finrank ↥LL.1 ↥(S a)
  have hfS : ∀ a, Module.finrank ↥LL.1 ↥(S a) ≤ Module.finrank ↥LL.1 ↥Dm := fun a =>
    Submodule.finrank_mono inf_le_left
  have hlt : ∀ a b, IsJumpV ((D.loc l).PD K) T.ρ τ a → a < b → f b < f a := by
    intro a b ha hab
    obtain ⟨d, hd, h1, h2⟩ := GlobalTheory.T.exists_crystallineLetter_of_hodgeJump D HW l K s LL h T hcrys i ζ τ hpt a ha
    have hle : S b ≤ S (a + 1) := hSanti (by omega)
    have hlt' : S (a + 1) < S a := by
      refine lt_of_le_of_ne (hSanti (by omega)) fun heq => h2 ?_
      have : d ∈ S a := ⟨hd, h1⟩
      rw [← heq] at this
      exact this.2
    haveI : FiniteDimensional ↥LL.1 ↥(S a) :=
      Submodule.finiteDimensional_of_le (inf_le_left : S a ≤ Dm)
    exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt')
  refine Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (Module.finrank ↥LL.1 ↥Dm)).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact hfS a
  · intro a ha b hb hab
    rcases lt_trichotomy a b with hh | hh | hh
    · exact absurd hab (hlt a b ha hh).ne'
    · exact hh
    · exact absurd hab (hlt b a hb hh).ne

end GlobalTheory.NL.JumpsFinite
