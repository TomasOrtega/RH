import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagInv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Use `show (F.fl.Xa j).map (a : S.V →ₗ[E] S.V) ≤ F.fl.Xa j`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Unfold `Formalism.MainNotions.S.FlagG.Xa`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Simplify using `only [Set.mem_setOf_eq] at hi`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]`. Establish `hb` using `h (Fin.castSucc i)`. Establish `hf : frame F (Fin.castSucc i) = F.fl.e i`. Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec]`.

Rewrite `hb` using `[hf]`. Establish `hmono : Xflag F (Fin.castSucc i).val ≤ F.fl.Xa j` using `by show F.fl.Xa i.val ≤ F.fl.Xa j`. Unfold `Formalism.MainNotions.S.FlagG.Xa`. Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises.

Introduce `k hk`. Simplify using `only [Set.mem_setOf_eq] at hk ⊢`. Use linear arithmetic over natural numbers and integers. Establish `he : F.fl.e i ∈ F.fl.Xa j`. Unfold `Formalism.MainNotions.S.FlagG.Xa`.

Conclude with `Submodule.subset_span ⟨i, hi, rfl⟩`. Use `Submodule.add_mem _ (hmono hb) he` as an intermediate fact. Unfold `Formalism.MainNotions.S.FlagG.Xa at this`. Simplify using `using this`.
-/
theorem map_Xflag_le (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) ≤ Xflag F j := by
  show (F.fl.Xa j).map (a : S.V →ₗ[E] S.V) ≤ F.fl.Xa j
  rw [Submodule.map_le_iff_le_comap]
  unfold Formalism.MainNotions.S.FlagG.Xa
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq] at hi
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
  have hb := h (Fin.castSucc i)
  have hf : frame F (Fin.castSucc i) = F.fl.e i := by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  rw [hf] at hb
  have hmono : Xflag F (Fin.castSucc i).val ≤ F.fl.Xa j := by
    show F.fl.Xa i.val ≤ F.fl.Xa j
    unfold Formalism.MainNotions.S.FlagG.Xa
    apply Submodule.span_mono
    apply Set.image_mono
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    omega
  have he : F.fl.e i ∈ F.fl.Xa j := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have := Submodule.add_mem _ (hmono hb) he
  unfold Formalism.MainNotions.S.FlagG.Xa at this
  simpa using this

/- English proof (translation)
Use `haveI : FiniteDimensional E (Xflag F j) := by show FiniteDimensional E (Submodule.span E (F.fl.e '' {i | i.1 < j}))`. Conclude with `FiniteDimensional.span_of_finite E (Set.toFinite _)`. Conclude with `Submodule.eq_of_le_of_finrank_eq (map_Xflag_le F a h j) (LinearEquiv.finrank_map_eq a _)`.
-/
theorem map_Xflag_eq (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) = Xflag F j := by
  haveI : FiniteDimensional E (Xflag F j) := by
    show FiniteDimensional E (Submodule.span E (F.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite E (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq (map_Xflag_le F a h j) (LinearEquiv.finrank_map_eq a _)

/- English proof (translation)
Rewrite `hx` using `[← map_Xflag_eq F a h j]`. Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`.
-/
theorem symm_mem_Xflag (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) {x : S.V}
    (hx : x ∈ Xflag F j) : a.symm x ∈ Xflag F j := by
  rw [← map_Xflag_eq F a h j] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

/- English proof (translation)
Introduce `E _ _ _ S r T F a h b`. Establish `hm` using `symm_mem_Xflag F a h b.val (h b)`. Establish `key : a⁻¹ (frame F b) - frame F b = -(a.symm (a (frame F b) - frame F b))` using `by show a.symm (frame F b) - frame F b = _`. Simplify using `[map_sub]`. Rewrite using `[key]`.

Conclude with `Submodule.neg_mem _ hm`.
-/
theorem inv_moves : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  intro E _ _ _ S r T F a h b
  have hm := symm_mem_Xflag F a h b.val (h b)
  have key : a⁻¹ (frame F b) - frame F b = -(a.symm (a (frame F b) - frame F b)) := by
    show a.symm (frame F b) - frame F b = _
    simp [map_sub]
  rw [key]
  exact Submodule.neg_mem _ hm

end GlobalTheory.FlagInv
