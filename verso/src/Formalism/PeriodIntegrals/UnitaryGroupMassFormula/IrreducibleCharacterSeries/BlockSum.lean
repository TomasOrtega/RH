import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ClassFnOfIsIrrChar

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

section Gen
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/- English proof (translation)
Use `⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩` and prove the remaining obligations. Use `letI : Invertible (p : Matrix ι ι K) := Units.invertible p`. Use `Matrix.blockTriangular_inv_of_blockTriangular (M := (p : Matrix ι ι K)) (b := b) h` as an intermediate fact. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `this`.
-/
theorem mem_parab_iff {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (p : GL ι K) :
    p ∈ parab K b ↔ IsBlockUT K b (p : Matrix ι ι K) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  letI : Invertible (p : Matrix ι ι K) := Units.invertible p
  have := Matrix.blockTriangular_inv_of_blockTriangular (M := (p : Matrix ι ι K)) (b := b) h
  rw [Matrix.coe_units_inv]
  exact this

end Gen

/- English proof (translation)
Rewrite using `[← sum_card_fibers b]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [Fintype.card_congr (e j), Fintype.card_fin]`.
-/
theorem sum_c_eq {r s : ℕ} (b : Fin r → Fin s) (c : Fin s → ℕ) (e : ∀ j, {i // b i = j} ≃ Fin (c j)) :
    ∑ j, c j = r := by
  rw [← sum_card_fibers b]
  exact Finset.sum_congr rfl fun j _ => by rw [Fintype.card_congr (e j), Fintype.card_fin]

section Perm
variable {r s : ℕ} (b : Fin r → Fin s) (c : Fin s → ℕ) (e : ∀ j, {i // b i = j} ≃ Fin (c j))

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem e_val_eq (j : Fin s) (i : Fin r) (h : b i = j) : (e (b i) ⟨i, rfl⟩).val = (e j ⟨i, h⟩).val := by
  subst h; rfl

/- English proof (translation)
Unfold `IsBaseBlockVar at h h'`. Break down `lt_trichotomy j j' with hl | hl | hl` into its components or cases. Use `offs_add_le c hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hl`.

Use `offs_add_le c hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem block_membership_unique {j j' : Fin s} {x : ℕ} (h : IsBaseBlockVar c j x) (h' : IsBaseBlockVar c j' x) : j = j' := by
  unfold IsBaseBlockVar at h h'
  rcases lt_trichotomy j j' with hl | hl | hl
  · have := offs_add_le c hl; omega
  · exact hl
  · have := offs_add_le c hl; omega

def tauFun (i : Fin r) : Fin r :=
  ⟨offs c (b i) + (e (b i) ⟨i, rfl⟩).val, by
    have h1 := offs_add_le_sum c (b i)
    have h2 := (e (b i) ⟨i, rfl⟩).isLt
    rw [sum_c_eq b c e] at h1
    omega⟩

/- English proof (translation)
Unfold `IsBaseBlockVar tauFun`. Establish `h2` using `(e (b i) ⟨i, rfl⟩).isLt`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem block_membership_permutation (i : Fin r) : IsBaseBlockVar c (b i) (tauFun b c e i).val := by
  unfold IsBaseBlockVar tauFun
  have h2 := (e (b i) ⟨i, rfl⟩).isLt
  simp only
  omega

/- English proof (translation)
Introduce `i i' h`. Establish `hb : b i' = b i` using `block_membership_unique c (h ▸ block_membership_permutation b c e i') (block_membership_permutation b c e i)`. Establish `hv : (e (b i) ⟨i, rfl⟩).val = (e (b i) ⟨i', hb⟩).val`. Establish `h3` using `congrArg Fin.val h`. Unfold `tauFun at h3`.

Simplify using `only at h3`. Rewrite `h3` using `[e_val_eq b c e (b i) i' hb, hb]`. Use linear arithmetic over natural numbers and integers. Establish `h4 : e (b i) ⟨i, rfl⟩ = e (b i) ⟨i', hb⟩` using `Fin.ext hv`. Establish `h5` using `congrArg Subtype.val ((e (b i)).injective h4)`.

Conclude with `h5`.
-/
theorem tauFun_injective : Function.Injective (tauFun b c e) := by
  intro i i' h
  have hb : b i' = b i := block_membership_unique c (h ▸ block_membership_permutation b c e i') (block_membership_permutation b c e i)
  have hv : (e (b i) ⟨i, rfl⟩).val = (e (b i) ⟨i', hb⟩).val := by
    have h3 := congrArg Fin.val h
    unfold tauFun at h3
    simp only at h3
    rw [e_val_eq b c e (b i) i' hb, hb] at h3
    omega
  have h4 : e (b i) ⟨i, rfl⟩ = e (b i) ⟨i', hb⟩ := Fin.ext hv
  have h5 := congrArg Subtype.val ((e (b i)).injective h4)
  exact h5

def tau : Fin r ≃ Fin r :=
  Equiv.ofBijective (tauFun b c e) (Finite.injective_iff_bijective.mp (tauFun_injective b c e))

end Perm

end PI.SerBridgeGLW
