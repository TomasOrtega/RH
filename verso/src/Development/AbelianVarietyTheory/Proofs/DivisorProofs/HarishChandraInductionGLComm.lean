import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic

noncomputable section

namespace GlobalTheory.HCCommF

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

def aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (M.submatrix Fin.revPerm Fin.revPerm).transpose

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aflip_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) : aflip M i j = M j.rev i.rev := rfl

/- English proof (translation)
Unfold `aflip`. Rewrite using `[← Matrix.transpose_mul, Matrix.submatrix_mul_equiv]`.
-/
theorem aflip_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) F) : aflip (M * N) = aflip N * aflip M := by
  unfold aflip
  rw [← Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Unfold `aflip`. Rewrite using `[Matrix.submatrix_one_equiv, Matrix.transpose_one]`.
-/
theorem aflip_one {n : ℕ} : aflip (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  unfold aflip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[aflip_apply]`.
-/
theorem aflip_aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : aflip (aflip M) = M := by
  ext i j; simp [aflip_apply]

/- English proof (translation)
Take `⟨P, hP, h⟩` from `GlobalTheory.SimilarTranspose.main F (Fin n) (M.submatrix Fin.revPerm Fin.revPerm)`. Set `Q : Matrix (Fin n) (Fin n) F` to `(1 : Matrix (Fin n) (Fin n) F).submatrix Fin.revPerm (Equiv.refl _)`. Establish `hQ : IsUnit Q`. Establish `: Q * (1 : Matrix (Fin n) (Fin n) F).submatrix (Equiv.refl _) Fin.revPerm = 1`. Simplify using `only [Q]`.

Rewrite using `[Matrix.submatrix_mul_equiv, mul_one, Matrix.submatrix_one_equiv]`. Conclude with `IsUnit.of_mul_eq_one _ this`. Establish `hQM : Q * M = M.submatrix Fin.revPerm Fin.revPerm * Q`. Establish `h1 : Q * M = Q * M.submatrix (Equiv.refl _) (Equiv.refl _)` using `rfl`. Rewrite using `[h1]`.

Simplify using `only [Q]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, one_mul, mul_one]`. Use `⟨P * Q, hP.mul hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hQM, ← mul_assoc, h, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem aflip_similar {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ P : Matrix (Fin n) (Fin n) F, IsUnit P ∧ P * M = aflip M * P := by
  obtain ⟨P, hP, h⟩ := GlobalTheory.SimilarTranspose.main F (Fin n) (M.submatrix Fin.revPerm Fin.revPerm)
  let Q : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.revPerm (Equiv.refl _)
  have hQ : IsUnit Q := by
    have : Q * (1 : Matrix (Fin n) (Fin n) F).submatrix (Equiv.refl _) Fin.revPerm = 1 := by
      simp only [Q]
      rw [Matrix.submatrix_mul_equiv, mul_one, Matrix.submatrix_one_equiv]
    exact IsUnit.of_mul_eq_one _ this
  have hQM : Q * M = M.submatrix Fin.revPerm Fin.revPerm * Q := by
    have h1 : Q * M = Q * M.submatrix (Equiv.refl _) (Equiv.refl _) := rfl
    rw [h1]
    simp only [Q]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, one_mul, mul_one]
  refine ⟨P * Q, hP.mul hQ, ?_⟩
  rw [mul_assoc, hQM, ← mul_assoc, h, mul_assoc]
  rfl

def aflipG {n : ℕ} (x : GL (Fin n) F) : GL (Fin n) F where
  val := aflip (x : Matrix (Fin n) (Fin n) F)
  inv := aflip ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  val_inv := by rw [← aflip_mul, Units.inv_mul, aflip_one]
  inv_val := by rw [← aflip_mul, Units.mul_inv, aflip_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aflipG_coe {n : ℕ} (x : GL (Fin n) F) :
    ((aflipG x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aflip (x : Matrix (Fin n) (Fin n) F) := rfl

/- English proof (translation)
The claim follows from `Units.ext (by simp only [aflipG_coe, Units.val_mul, aflip_mul])`.
-/
theorem aflipG_mul {n : ℕ} (x y : GL (Fin n) F) : aflipG (x * y) = aflipG y * aflipG x :=
  Units.ext (by simp only [aflipG_coe, Units.val_mul, aflip_mul])

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem aflipG_inv {n : ℕ} (x : GL (Fin n) F) : aflipG x⁻¹ = (aflipG x)⁻¹ := Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext (aflip_aflip _)`.
-/
theorem aflipG_aflipG {n : ℕ} (x : GL (Fin n) F) : aflipG (aflipG x) = x := Units.ext (aflip_aflip _)

def aflipE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F := ⟨aflipG, aflipG, aflipG_aflipG, aflipG_aflipG⟩

/- English proof (translation)
Take `⟨P, hP, h⟩` from `aflip_similar (x : Matrix (Fin n) (Fin n) F)`. Use `⟨hP.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Conclude with `Units.ext (by simp only [Units.val_mul, aflipG_coe, IsUnit.unit_spec, h])`.
-/
theorem aflipG_conj {n : ℕ} (x : GL (Fin n) F) : ∃ p : GL (Fin n) F, aflipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, h⟩ := aflip_similar (x : Matrix (Fin n) (Fin n) F)
  refine ⟨hP.unit, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (by simp only [Units.val_mul, aflipG_coe, IsUnit.unit_spec, h])

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos x.isUnit]`. Conclude with `Units.ext (IsUnit.unit_spec _)`.
-/
theorem toG_coe' {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Use `hα x p⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem cl_conj {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (p x : GL (Fin n) F) :
    α (p * x * p⁻¹) = α x := by
  have := hα x p⁻¹
  rwa [inv_inv] at this

/- English proof (translation)
Distinguish the cases in `h : IsUnit M`. Take `⟨x, rfl⟩` from `h`. Take `⟨p, hp⟩` from `aflipG_conj x`. Establish `h1 : toG (aflip (x : Matrix (Fin n) (Fin n) F)) = aflipG x` using `toG_coe' (aflipG x)`. Rewrite using `[h1, toG_coe', hp, cl_conj hα]`.

Establish `h' : ¬ IsUnit (aflip M)`. Introduce and unpack `⟨x, hx⟩`. Conclude with `h ⟨aflipG x, by rw [aflipG_coe, hx, aflip_aflip]⟩`. Unfold `toG`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem class_aflip {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (M : Matrix (Fin n) (Fin n) F) :
    α (toG (aflip M)) = α (toG M) := by
  by_cases h : IsUnit M
  · obtain ⟨x, rfl⟩ := h
    obtain ⟨p, hp⟩ := aflipG_conj x
    have h1 : toG (aflip (x : Matrix (Fin n) (Fin n) F)) = aflipG x := toG_coe' (aflipG x)
    rw [h1, toG_coe', hp, cl_conj hα]
  · have h' : ¬ IsUnit (aflip M) := by
      rintro ⟨x, hx⟩
      exact h ⟨aflipG x, by rw [aflipG_coe, hx, aflip_aflip]⟩
    unfold toG
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hj hi`. Use `h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)` as an intermediate fact. Simplify `this` using `[aflipG_coe, aflip_apply]`. Introduce `h i j hj hi`.

Rewrite using `[aflipG_coe, aflip_apply]`. Conclude with `h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)`.
-/
theorem inPar_aflip {a b : ℕ} (y : GL (Fin (a + b)) F) : InPar b (aflipG y) ↔ InPar a y := by
  constructor
  · intro h i j hj hi
    have := h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
    simpa [aflipG_coe, aflip_apply] using this
  · intro h i j hj hi
    rw [aflipG_coe, aflip_apply]
    exact h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[aflip_apply]`. Unfold `tl br ent`.

Rewrite using `[dif_pos (by omega), dif_pos (by simp only [Fin.val_rev]; omega), aflip_apply]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega`.
-/
theorem tl_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl b (aflip M) = aflip (br a b M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dif_pos (by omega), dif_pos (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[aflip_apply]`. Unfold `tl br ent`.

Rewrite using `[dif_pos (by omega), dif_pos (by simp only [Fin.val_rev]; omega), aflip_apply]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega`.
-/
theorem br_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br b a (aflip M) = aflip (tl a M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dif_pos (by omega), dif_pos (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gal]`.
-/
theorem gal_id (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

/- English proof (translation)
Introduce `F _ _ a b n α β hα hβ hn`. Substitute `hn` using the available equality. Use function extensionality and compare the values at `x`. Take `⟨p, hp⟩` from `aflipG_conj x`. Unfold `hc hcTw`.

Simplify using `only [gal_id]`. Use `congr 1`. Use `congr 2`. Conclude with `Nat.card_congr ((aflipE (a + b)).subtypeEquiv fun y => (inPar_aflip y).symm)`. Use `symm`.

Rewrite using `[← finsum_comp_equiv (((aflipE (a + b)).trans (Equiv.mulRight p)).trans (Equiv.inv _))]`. Use `symm`. Use `congr 1`. Use function extensionality and compare the values at `y`. Establish `h1 : (((aflipE (a + b)).trans (Equiv.mulRight p)).trans (Equiv.inv _)) y = (aflipG y * p)⁻¹` using `rfl`.

Establish `h2 : ((aflipG y * p)⁻¹)⁻¹ * x * (aflipG y * p)⁻¹ = aflipG (y⁻¹ * x * y)`. Rewrite using `[aflipG_mul, aflipG_mul, aflipG_inv, hp]`. Use `group`. Rewrite using `[h1, h2]`. Unfold `tlG brG`.

Rewrite using `[aflipG_coe, tl_aflip, br_aflip]`. Simplify using `only [inPar_aflip, class_aflip hα, class_aflip hβ, mul_comm (β _)]`.
-/
theorem main : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ),
    IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  obtain ⟨p, hp⟩ := aflipG_conj x
  unfold hc hcTw
  simp only [gal_id]
  congr 1
  · congr 2
    exact Nat.card_congr ((aflipE (a + b)).subtypeEquiv fun y => (inPar_aflip y).symm)
  · symm
    rw [← finsum_comp_equiv (((aflipE (a + b)).trans (Equiv.mulRight p)).trans (Equiv.inv _))]
    symm
    congr 1
    funext y
    have h1 : (((aflipE (a + b)).trans (Equiv.mulRight p)).trans (Equiv.inv _)) y = (aflipG y * p)⁻¹ := rfl
    have h2 : ((aflipG y * p)⁻¹)⁻¹ * x * (aflipG y * p)⁻¹ = aflipG (y⁻¹ * x * y) := by
      rw [aflipG_mul, aflipG_mul, aflipG_inv, hp]; group
    rw [h1, h2]
    unfold tlG brG
    rw [aflipG_coe, tl_aflip, br_aflip]
    simp only [inPar_aflip, class_aflip hα, class_aflip hβ, mul_comm (β _)]

end GlobalTheory.HCCommF
