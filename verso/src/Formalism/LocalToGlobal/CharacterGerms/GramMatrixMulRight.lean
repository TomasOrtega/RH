import Formalism.LocalToGlobal.CharacterGerms.RowTieMemC

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

abbrev AA (r : T → ℕ) (tau : Orb → ZMod 2 → T) (N : ℕ) : Type := Fin N × Σ o, IIs r tau o

def eW (N : ℕ) : (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ≃ AA r tau N × Fin 2 where
  toFun y := ((y.1, ⟨y.2.1, y.2.2.2⟩), y.2.2.1)
  invFun z := (z.1.1, ⟨z.1.2.1, ⟨z.2, z.1.2.2⟩⟩)
  left_inv := by rintro ⟨ρ, ⟨o, ⟨g, c⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨ρ, ⟨o, c⟩⟩, g⟩; rfl

def lam (z : AA r tau N × Fin 2) : Letter T r n := ⟨tau z.1.2.1 z.1.2.2.1, z.1.2.2.2, plc (z.1.1, z.2)⟩

variable {r tau}

/- English proof (translation)
Introduce and unpack `⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h`. Simplify using `only [lam, Sigma.mk.inj_iff] at h`. Take `⟨h1, h2⟩` from `h`. Establish `h3` using `inj (a₁ := (o, t)) (a₂ := (o', t')) h1`. Simplify using `only [Prod.mk.injEq] at h3`.

Take `⟨rfl, rfl⟩` from `h3`. Establish `h4` using `eq_of_heq h2`. Simplify using `only [Prod.mk.injEq] at h4`. Take `⟨rfl, h5⟩` from `h4`. Establish `h6` using `plc.injective h5`.

Simplify using `only [Prod.mk.injEq] at h6`. Take `⟨rfl, rfl⟩` from `h6`. Both sides reduce to the same expression.
-/
theorem lam_inj (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h
  simp only [lam, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := inj (a₁ := (o, t)) (a₂ := (o', t')) h1
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, h5⟩ := h4
  have h6 := plc.injective h5
  simp only [Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rfl

variable (r tau)

def Gm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 α.2.2.1 col g

def Mm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 (α.2.2.1 + 1) col (1 - g)

variable {r tau gm}

/- English proof (translation)
Establish `h` using `gm_hyp α.2.1 α.2.2.1 (1 - g') g`. Unfold `Mm Gm`. Rewrite using `[h]`. Use `clear h`. Apply the tactic sequence `fin_cases g <;> fin_cases g' <;> simp`.
-/
theorem gram_matrix_mul_right (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  have h := gm_hyp α.2.1 α.2.2.1 (1 - g') g
  unfold Mm Gm
  rw [h]
  clear h
  fin_cases g <;> fin_cases g' <;> simp

/- English proof (translation)
Establish `hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1`. Use extensionality with `g' g`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `gram_matrix_mul_right gm_hyp α g g'`. Establish `hBA` using `mul_eq_one_comm.1 hAB`.

Use `congrFun (congrFun hBA col') col` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`.
-/
theorem gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

variable (r tau gm)

def coS (ℓ : Letter T r n) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) : C :=
  ∑ col, if ℓ = lam r tau plc ((eW r tau N y).1, col) then Mm r tau gm (eW r tau N y).1 col (eW r tau N y).2 else 0

variable {r tau gm}

/- English proof (translation)
Unfold `coS`. Rewrite using `[Equiv.apply_symm_apply]`. Simplify using `only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]`. Distinguish the cases in `h : α = α'`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem coS_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm r tau gm α col g else 0 := by
  unfold coS
  rw [Equiv.apply_symm_apply]
  simp only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]
  by_cases h : α = α'
  · subst h
    simp
  · simp [h]

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_eq_single α]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[coS_lam plc inj, if_pos rfl]`. Introduce `α' _ hne`.

Use `Finset.sum_eq_zero fun g _ => ?_` and prove the remaining obligations. Rewrite using `[coS_lam plc inj, if_neg (Ne.symm hne), h0]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_coS (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  rw [← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single α]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [coS_lam plc inj, if_pos rfl]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [coS_lam plc inj, if_neg (Ne.symm hne), h0]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `subG`. Rewrite using `[MvPolynomial.aeval_X]`. Both sides reduce to the same expression.
-/
theorem subG_X (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl

/- English proof (translation)
Establish `h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) = AlgHom.id C _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]`. Simplify using `only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]`.

Establish `hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) * (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) = ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW …` using `fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)`. Simplify using `only [hs, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) * (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) = MvPolynomia …`. Introduce `g`.

Rewrite using `[← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun col _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h2]`.

Rewrite using `[Finset.sum_eq_single (eW r tau N y).2]`. Simplify using the standard rewrite rules. Introduce `g _ hg`. Simplify using `[hg]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Conclude with `congrArg (fun φ => φ Q) h`.
-/
theorem back_subG (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) *
      (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) =
      AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y
    rw [AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) *
        (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) =
        ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :=
      fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
        (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) *
          (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :
            MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) =
        MvPolynomial.C (if g = (eW r tau N y).2 then 1 else 0) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) := by
      intro g
      rw [← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [map_mul]; ring
    simp only [h2]
    rw [Finset.sum_eq_single (eW r tau N y).2]
    · simp
    · intro g _ hg; simp [hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact congrArg (fun φ => φ Q) h

end Formalism.L2.FormalSeriesBounds.RF
