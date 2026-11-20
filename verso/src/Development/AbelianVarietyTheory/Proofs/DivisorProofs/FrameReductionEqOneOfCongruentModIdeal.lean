import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.FrameCong

/- English proof (translation)
Use `Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Use `Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_` and prove the remaining obligations. Introduce `a ha u hu i`. Establish `hu' : (fun k => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨u, hu, rfl⟩`.

Establish `t` using `(hβ _).1 hu' i`. Use `⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩` and prove the remaining obligations. Establish `e : (fun k => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) ((a • u) k)) = (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by`. Use function extensionality and compare the values at `k`. Use `show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) = (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Introduce `m1 m2 h1 h2 i`.

Take `⟨s1, hs1, e1⟩` from `h1 i`. Take `⟨s2, hs2, e2⟩` from `h2 i`. Use `⟨s1 + s2, add_mem hs1 hs2, ?_⟩` and prove the remaining obligations. Establish `: (fun k => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) = (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) + (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by`. Use function extensionality and compare the values at `k`.

Simplify using `[map_add]`. Rewrite using `[this, Matrix.mulVec_add, Pi.add_apply, e1, e2]`. Both sides reduce to the same expression. Introduce `i`. Conclude with `⟨0, zero_mem _, by simp⟩`.

Introduce `a b _ _ ha hb i`. Take `⟨s1, hs1, e1⟩` from `ha i`. Take `⟨s2, hs2, e2⟩` from `hb i`. Use `⟨s1 + s2, add_mem hs1 hs2, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, Pi.add_apply, e1, e2]`.

Both sides reduce to the same expression. Introduce `c a _ ha i`. Take `⟨s, hs, e⟩` from `ha i`. Use `⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]`.

Both sides reduce to the same expression.
-/
theorem coord_mem_idS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (I : Ideal (𝓞 E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) :
    ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F) := by
  refine Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I,
    (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I,
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_
    · intro a ha u hu i
      have hu' : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨u, hu, rfl⟩
      have t := (hβ _).1 hu' i
      refine ⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have e : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k)) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by
        funext k
        show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · intro m1 m2 h1 h2 i
      obtain ⟨s1, hs1, e1⟩ := h1 i
      obtain ⟨s2, hs2, e2⟩ := h2 i
      refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
      have : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) =
          (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) +
            (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by
        funext k; simp [map_add]
      rw [this, Matrix.mulVec_add, Pi.add_apply, e1, e2]
      rfl
  · intro i
    exact ⟨0, zero_mem _, by simp⟩
  · intro a b _ _ ha hb i
    obtain ⟨s1, hs1, e1⟩ := ha i
    obtain ⟨s2, hs2, e2⟩ := hb i
    refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply, e1, e2]
    rfl
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP`. Take `⟨y, rfl⟩` from `hx`. Rewrite using `[redFn_frGL]`. Use `set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY`. Establish `e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1` using `rfl`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F` using `F) Λ := by`. Use `(hβ _).2 fun k => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `Subring.one_mem _`. Rewrite using `[Pi.single_eq_of_ne hkj]`.

Conclude with `Subring.zero_mem _`. Take `⟨s, hs, es⟩` from `coord_mem_idS β Λ hβ I _ (hcong _ hv) i`. Establish `hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) - β.1 *ᵥ (Pi.single j 1 : Fin n → E …`. Establish `hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Rewrite using `[e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul, Matrix.sub_mulVec, Matrix.one_mulVec]`. Rewrite `es` using `[hcomp, Matrix.mulVec_single_one, Matrix.col_apply]`. Establish `e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> rfl`. Establish `hs' : (y.1 - 1) i j = s` using `Subtype.ext (e5.trans es)`. Establish `hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal` using `hs' ▸ Ideal.map_mono hPP hs`. Establish `e6 : resS F PP ((y.1 - 1) i j) = 0`. Unfold `resS`.

Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]`. Use `show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j`. Rewrite `e6` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[e6, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem redFn_eq_one_of_congr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ →
    x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) →
    ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  intro F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP
  classical
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  apply Units.ext
  ext i j
  have hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine (hβ _).2 fun k => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  obtain ⟨s, hs, es⟩ := coord_mem_idS β Λ hβ I _ (hcong _ hv) i
  have hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) -
        β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) = (Y - 1) *ᵥ Pi.single j 1 := by
    have hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hcomp, Matrix.mulVec_single_one, Matrix.col_apply] at es
  have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hs' : (y.1 - 1) i j = s := Subtype.ext (e5.trans es)
  have hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal := hs' ▸ Ideal.map_mono hPP hs
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FrameCong
