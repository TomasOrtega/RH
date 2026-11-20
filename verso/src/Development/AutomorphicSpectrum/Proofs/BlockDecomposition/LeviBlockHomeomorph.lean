import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviIso

/- English proof (translation)
Introduce `k _ _ _ _ α _ _ N m _ _ e β hβ`. Establish `hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j → (x : Matrix (Fin N) (Fin N) k) i j = 0`. Introduce `x hx i j hij`. Simplify using `only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases.

Conclude with `hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))`. Conclude with `hx.1 ((hβ j i).2 h)`. Establish `hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j → ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0`. Introduce `g i j hij`. Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`.

Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`. Establish `hab : a ≠ b` using `by simpa [blk] using hij`. Conclude with `leviEmb_apply_ne k e g hab i' j'`. Establish `hent : ∀ (g : Levi k m) (a : α) (i j : m a), ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j`. Introduce `g a i j`.

Conclude with `leviEmb_apply_same k e g a i j`. Establish `hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β`. Introduce `g`. Simplify using `only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]`. Prove the components needed by the constructor for the conclusion.

Introduce `i j h`. Conclude with `hzE g i j ((hβ j i).1 h).ne'`. Introduce `i j h`. Conclude with `hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne`. Establish `hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β → Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) = (x : Matrix (Fin N) (Fin N) k).submatrix e e`.

Introduce `x hx`. Use extensionality with `⟨a, i⟩ ⟨b, j⟩`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]`.

Rewrite using `[Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply, hz x hx _ _ (by simpa [blk] using hab)]`. Establish `hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α, Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a * Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a = Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) …`. Introduce `x y hx hy a`. Rewrite using `[Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k) (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]`. Simplify using `only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']`.

Establish `hcont : ∀ f : Levi k m → Levi k m, (∀ a, Continuous fun g => ((f g a : GL (m a) k) : Matrix (m a) (m a) k)) → Continuous fun g => ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)`. Introduce `f hf`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `only [hent]`. Conclude with `(hf a).matrix_elem i' j'`. Establish `h0 : ∀ g, ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i'⟩) (e ⟨b, j'⟩) = 0` using `fun g => hzE _ _ _ (by simpa [blk] using hab)`.

Simplify using `only [h0]`. Conclude with `continuous_const`. Establish `hLE : Continuous (leviEmb k e)` using `continuous_leviEmb k e`. Set `ψ : levi k N β → Levi k m` to `fun x => (fun a => ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a, Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a, by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one, Matri …`. Use `⟨{ toFun := fun g => ⟨leviEmb k e g, hmem g⟩ invFun := ψ left_inv := ?_ right_inv := ?_ map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g`. Use `funext fun a => ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]`.

Conclude with `hent g a i j`. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`. Distinguish the cases in `hab : a = b`. Substitute `hab dsimp only` using the available equality. Rewrite using `[hent]`.

Simplify using `only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]`. Establish `h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩)` using `by simpa [blk] using hab dsimp only`. Rewrite using `[hzE _ _ _ h', hz _ x.2 _ _ h']`. Introduce `g h`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `map_mul (leviEmb k e) g h`. Conclude with `hLE.subtype_mk hmem`. Express the relevant statement in the definitionally equal form `Continuous ψ`. Use `continuous_pi fun a => ?_` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`.

Prove the components needed by the constructor for the conclusion. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]`. Conclude with `(Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Simplify using `only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]`. Conclude with `(Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _`.
-/
theorem leviEquiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ
  have hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j →
      (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro x hx i j hij
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))
    · exact hx.1 ((hβ j i).2 h)
  have hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j →
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro g i j hij
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : a ≠ b := by simpa [blk] using hij
    exact leviEmb_apply_ne k e g hab i' j'
  have hent : ∀ (g : Levi k m) (a : α) (i j : m a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    exact leviEmb_apply_same k e g a i j
  have hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β := by
    intro g
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    constructor
    · intro i j h
      exact hzE g i j ((hβ j i).1 h).ne'
    · intro i j h
      exact hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne
  have hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β →
      Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) =
        (x : Matrix (Fin N) (Fin N) k).submatrix e e := by
    intro x hx
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply,
        hz x hx _ _ (by simpa [blk] using hab)]
  have hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α,
      Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a *
          Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a =
        Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a := by
    intro x y hx hy a
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k)
      (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]
    simp only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']
  have hcont : ∀ f : Levi k m → Levi k m,
      (∀ a, Continuous fun g => ((f g a : GL (m a) k) : Matrix (m a) (m a) k)) →
        Continuous fun g => ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp only [hent]
      exact (hf a).matrix_elem i' j'
    · have h0 : ∀ g, ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
          (e ⟨a, i'⟩) (e ⟨b, j'⟩) = 0 := fun g => hzE _ _ _ (by simpa [blk] using hab)
      simp only [h0]
      exact continuous_const
  have hLE : Continuous (leviEmb k e) := continuous_leviEmb k e
  let ψ : levi k N β → Levi k m := fun x => (fun a =>
      ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl,
        by rw [hmul _ _ (inv_mem x.2) x.2, inv_mul_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl⟩ : ∀ a, GL (m a) k)
  refine ⟨{
      toFun := fun g => ⟨leviEmb k e g, hmem g⟩
      invFun := ψ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩
  · intro g
    refine funext fun a => ?_
    apply Units.ext
    ext i j
    simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    exact hent g a i j
  · intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      dsimp only
      rw [hent]
      simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    · have h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩) := by simpa [blk] using hab
      dsimp only
      rw [hzE _ _ _ h', hz _ x.2 _ _ h']
  · intro g h
    apply Subtype.ext
    exact map_mul (leviEmb k e) g h
  · exact hLE.subtype_mk hmem
  · change Continuous ψ
    refine continuous_pi fun a => ?_
    rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => ?_
      simp only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      simp only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _

end GlobalTheory.CompanionTheory.LeviIso
