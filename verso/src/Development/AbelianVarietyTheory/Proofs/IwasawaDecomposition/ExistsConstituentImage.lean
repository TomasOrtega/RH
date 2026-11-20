import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.ConstituentImage

/- English proof (translation)
Introduce `Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV`. Take `⟨W', hW'i, hc⟩` from `hss V hV.2.1`. Use `set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef`. Establish `hpV : ∀ x, p x ∈ V` using `fun x => (Submodule.linearProjOfIsCompl V W' hc x).2`. Establish `hpid : ∀ x ∈ V, p x = x` using `fun x hx => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)`.

Establish `hp0 : ∀ x ∈ W', p x = 0` using `fun x hx => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)`. Establish `hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v)`. Introduce `g v`. Use `set q := v - p v`. Establish `hq : q ∈ W'`.

Rewrite using `[← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]`. Use `Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩` as an intermediate fact. Rewrite using `[this, sub_eq_zero]`. Both sides reduce to the same expression. Establish `hv : v = p v + q` using `by simp [q]`.

Use `conv_lhs => rw [hv]`. Rewrite using `[Matrix.mulVec_add, map_add, hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]`. Use `set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ`. Establish `hπv : ∀ v, π.mulVec v = p v` using `fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]`. Establish `hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L)`.

Introduce `g`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]`. Use `set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM`.

Establish `hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L)`. Introduce `g`. Rewrite using `[hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]`. Establish `hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v)`. Introduce `g v`.

Rewrite using `[Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]`. Establish `hMV : ∀ v, M.mulVec v ∈ V` using `fun v => by`. Rewrite using `[hM, ← Matrix.mulVec_mulVec, hπv]`. Conclude with `hpV _`. Establish `hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨x, hxV, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hV.1`. Establish `hsup : Submodule.map M.mulVecLin ⊤ = ⊥`. Rewrite using `[← hVs, Submodule.map_iSup]`.

Simplify using `[hne]`. Establish `hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤` using `⟨_, Submodule.mem_top, rfl⟩`. Rewrite `hmem` using `[hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV]`. Conclude with `hx0 hmem`. Take `⟨j, hj⟩` from `hex`.

Use `⟨j, M, hMc, ?_, ?_⟩` and prove the remaining obligations. Establish `hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j))`. Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Use `⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply]`.

Conclude with `(hMv g v).symm`. Establish `hle : Submodule.map M.mulVecLin (Vs j) ≤ V`. Introduce and unpack `_ ⟨v, _, rfl⟩`. Conclude with `hMV v`. Break down `hV.2.2 _ hle hinv with h | h` into its components or cases.

Conclude with `absurd h hj`. Conclude with `h`. Establish `hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j)`. Introduce and unpack `g v ⟨hk, hv⟩`. Use `⟨?_, (hirr j).2.1 g v hv⟩` and prove the remaining obligations.

Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢`. Rewrite using `[← hMv, hk, Matrix.mulVec_zero]`. Break down `(hirr j).2.2 _ inf_le_right hinv with h | h` into its components or cases. Conclude with `disjoint_iff.2 h`. It suffices to derive a contradiction.

Apply `hj` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `hk : v ∈ LinearMap.ker M.mulVecLin` using `(h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv`. Simplify using `using hk`.
-/
theorem exists_constituent_image : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  intro Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV
  obtain ⟨W', hW'i, hc⟩ := hss V hV.2.1
  set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef
  have hpV : ∀ x, p x ∈ V := fun x => (Submodule.linearProjOfIsCompl V W' hc x).2
  have hpid : ∀ x ∈ V, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hp0 : ∀ x ∈ W', p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  have hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v) := by
    intro g v
    set q := v - p v
    have hq : q ∈ W' := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]
      have := Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩
      rw [this, sub_eq_zero]; rfl
    have hv : v = p v + q := by simp [q]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, map_add, hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]
  set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ
  have hπv : ∀ v, π.mulVec v = p v := fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]
  have hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]
  set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM
  have hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    rw [hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]
  have hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v) := by
    intro g v
    rw [Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]
  have hMV : ∀ v, M.mulVec v ∈ V := fun v => by
    rw [hM, ← Matrix.mulVec_mulVec, hπv]; exact hpV _

  have hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.1
    have hsup : Submodule.map M.mulVecLin ⊤ = ⊥ := by
      rw [← hVs, Submodule.map_iSup]; simp [hne]
    have hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤ :=
      ⟨_, Submodule.mem_top, rfl⟩
    rw [hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV] at hmem
    exact hx0 hmem
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, M, hMc, ?_, ?_⟩
  · have hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j)) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact (hMv g v).symm
    have hle : Submodule.map M.mulVecLin (Vs j) ≤ V := by
      rintro _ ⟨v, _, rfl⟩; exact hMV v
    rcases hV.2.2 _ hle hinv with h | h
    · exact absurd h hj
    · exact h
  · have hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j) := by
      rintro g v ⟨hk, hv⟩
      refine ⟨?_, (hirr j).2.1 g v hv⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      rw [← hMv, hk, Matrix.mulVec_zero]
    rcases (hirr j).2.2 _ inf_le_right hinv with h | h
    · exact disjoint_iff.2 h
    · exfalso
      apply hj
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      have hk : v ∈ LinearMap.ker M.mulVecLin := (h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv
      simpa using hk

end GlobalTheory.ConstituentImage
