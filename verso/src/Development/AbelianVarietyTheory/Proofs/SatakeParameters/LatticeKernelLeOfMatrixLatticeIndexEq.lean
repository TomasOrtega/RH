import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu`. Establish `hfin` using `finite_range_latIdx hU x`. Use `set Sx := Set.range fun u : intVec L n => (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx`. Use `set Sy := Set.range fun u : intVec L n => (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy`. Set `h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n'` to `fun c => if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0`.

Establish `key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) = (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n')`. Introduce `w`. Establish `hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))` using `⟨w, rfl⟩`. Simplify using `only [h, dif_pos hc]`. Establish `he` using `hc.choose_spec`.

Use `set u' := hc.choose`. Rewrite `he` using `[QuotientAddGroup.eq]`. Rewrite using `[QuotientAddGroup.eq]`. Establish `hd` using `hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i)) (fun i => by`. Use `he i` as an intermediate fact.

Rewrite using `[Matrix.mulVec_sub]`. Simplify `this)` using `[neg_add_eq_sub]`. Introduce `i`. Use `hd i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_sub]`.

Simplify `this` using `[neg_add_eq_sub]`. Establish `himg : h '' Sx = Sy`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨w, (key w).symm⟩`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨_, ⟨w, rfl⟩, key w⟩`. Establish `hcard : (h '' Sx).ncard = Sx.ncard`. Rewrite using `[himg]`. Unfold `latIdx at hidx`.

Rewrite `hidx` using `[← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]`. Conclude with `hidx`. Establish `hinj : Set.InjOn h Sx` using `(Set.ncard_image_iff hfin).1 hcard`. Set `u0 : intVec L n` to `⟨u, hu⟩`. Establish `h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L)))`.

Rewrite using `[key, key]`. Simplify using `only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).2 hyu`. Establish `h1` using `hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0`. Simplify using `only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1`.

Conclude with `(QuotientAddGroup.eq_zero_iff _).1 h1`.
-/
theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
