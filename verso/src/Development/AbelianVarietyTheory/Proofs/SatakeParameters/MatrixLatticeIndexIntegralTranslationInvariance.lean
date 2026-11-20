import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_intVec]`. Introduce `i`. Express the relevant statement in the definitionally equal form `(∑ j, M i j * v j) ∈ Formalism.UG.intL L`. Conclude with `sum_mem fun j _ => mul_mem (hM i j) (hv j)`.
-/
theorem mulVec_mem_intVec_of_int {a b : ℕ} {M : Matrix (Fin a) (Fin b) L}
    (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) {v : Fin b → L} (hv : v ∈ intVec L b) :
    M.mulVec v ∈ intVec L a := by
  rw [mem_intVec] at hv ⊢
  intro i
  change (∑ j, M i j * v j) ∈ Formalism.UG.intL L
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

/- English proof (translation)
Take `⟨g0, rfl⟩` from `hg`. Conclude with `((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2`.
-/
theorem entry_mem_of_mem_GLint {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

/- English proof (translation)
Establish `hf : (fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) = fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)`. Use function extensionality and compare the values at `v`. Rewrite using `[Matrix.add_mulVec, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]`. Unfold `latIdx`. Rewrite using `[hf]`.
-/
theorem latIdx_add_int {a b : ℕ} (x u : Matrix (Fin a) (Fin b) L) (hu : u ∈ intMat L a b) :
    latIdx (x + u) = latIdx x := by
  have hf : (fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) =
      fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    funext v
    rw [Matrix.add_mulVec, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]
  unfold latIdx
  rw [hf]

def quotMul {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    (Fin a → L) ⧸ intVec L a →+ (Fin a → L) ⧸ intVec L a :=
  QuotientAddGroup.map (intVec L a) (intVec L a) (Matrix.mulVecLin M).toAddMonoidHom
    fun _ hv => mulVec_mem_intVec_of_int hM hv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotMul_mk {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) (v : Fin a → L) :
    quotMul M hM (QuotientAddGroup.mk v) = QuotientAddGroup.mk (M.mulVec v) := rfl

/- English proof (translation)
Establish `h1` using `entry_mem_of_mem_GLint hh`. Establish `h2` using `entry_mem_of_mem_GLint (inv_mem hh)`. Establish `hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1)`. Establish `hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2) (quotMul (h : Matrix (Fin a) (Fin a) L) h1)`. Introduce `q`.

Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H v`. Rewrite using `[quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `hl.injective`. Establish `hr : (Set.range fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) = quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : F …`.

Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp_apply, quotMul_mk, Matrix.mulVec_mulVec]`. Unfold `latIdx`.

Rewrite using `[hr, Nat.card_image_of_injective hinj]`.
-/
theorem latIdx_GLint_mul {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) (h : GL (Fin a) L)
    (hh : h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = latIdx x := by
  have h1 := entry_mem_of_mem_GLint hh
  have h2 := entry_mem_of_mem_GLint (inv_mem hh)
  have hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
    have hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2)
        (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H v =>
        rw [quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    exact hl.injective
  have hr : (Set.range fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) :
        (Fin a → L) ⧸ intVec L a)) =
      quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b =>
        (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    rw [← Set.range_comp]
    congr 1
    funext v
    simp only [Function.comp_apply, quotMul_mk, Matrix.mulVec_mulVec]
  unfold latIdx
  rw [hr, Nat.card_image_of_injective hinj]

/- English proof (translation)
Introduce `_ _ _ _ _ x` and use `⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩`.
-/
theorem latIdx_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x :=
  fun _ _ _ _ _ x => ⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩

end GlobalTheory.Hk3.HoweDuality

end
