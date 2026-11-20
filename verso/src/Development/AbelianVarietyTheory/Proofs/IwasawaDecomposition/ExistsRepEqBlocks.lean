import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine

open MeasureTheory Topology

noncomputable section

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

def eqBlocks (j t : ℕ) : (Σ _ : Fin j, Fin t) ≃ Fin (j * t) :=
  (Equiv.sigmaEquivProd (Fin j) (Fin t)).trans finProdFinEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_eqBlocks {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) = s + t * a := rfl

/- English proof (translation)
Rewrite using `[val_eqBlocks, Nat.add_mul_div_left _ _ s.pos, Nat.div_eq_of_lt s.2, zero_add]`.
-/
theorem eqBlocks_div {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) / t = a := by
  rw [val_eqBlocks, Nat.add_mul_div_left _ _ s.pos, Nat.div_eq_of_lt s.2, zero_add]

/- English proof (translation)
Rewrite using `[val_eqBlocks, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.2]`.
-/
theorem eqBlocks_mod {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) % t = s := by
  rw [val_eqBlocks, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.2]

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b => a < b) = Finset.Ioi a` using `by ext; simp`. Establish `h2 : (Finset.univ.filter fun b => b < a) = Finset.Iio a` using `by ext; simp`. Rewrite using `[modExp, h1, h2, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]`. Use `a.2` as an intermediate fact. Rewrite using `[show ((j - 1 - a : ℕ) : ℤ) = j - 1 - (a : ℕ) by omega]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem modExp_eqBlocks {j t : ℕ} (a : Fin j) :
    modExp (fun _ : Fin j => Fin t) a = (j * t : ℤ) - t - 2 * (a : ℕ) * t := by
  have h1 : (Finset.univ.filter fun b => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b => b < a) = Finset.Iio a := by ext; simp
  rw [modExp, h1, h2, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul]
  have := a.2
  rw [show ((j - 1 - a : ℕ) : ℤ) = j - 1 - (a : ℕ) by omega]
  ring

/- English proof (translation)
Use `mem_parab_iff.2 fun a a' s s' h => hb _ _ ?_` and prove the remaining obligations. Rewrite using `[Fin.lt_def, val_eqBlocks, val_eqBlocks]`. Establish `h1 : t * (a' + 1) ≤ t * a` using `Nat.mul_le_mul_left _ h`. Use `s'.2` as an intermediate fact. Rewrite `h1` using `[mul_add, mul_one]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mem_parab_eqBlocks {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) : b ∈ parab R (eqBlocks j t) := by
  refine mem_parab_iff.2 fun a a' s s' h => hb _ _ ?_
  rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
  have h1 : t * (a' + 1) ≤ t * a := Nat.mul_le_mul_left _ h
  have := s'.2
  rw [mul_add, mul_one] at h1
  omega

/- English proof (translation)
Use `ext`. Rewrite using `[GeneralLinearGroup.val_det_apply, det_of_upperTriangular, Units.coe_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => (hu _).symm`. Introduce `s s' h`. Use `hb _ _ ?_` and prove the remaining obligations.

Rewrite using `[Fin.lt_def, val_eqBlocks, val_eqBlocks]`. Conclude with `Nat.add_lt_add_right h _`.
-/
theorem det_block {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) (u : Fin (j * t) → Rˣ) (hu : ∀ x, (u x : R) = b.val x x) (a : Fin j) :
    GeneralLinearGroup.det (leviProj R (eqBlocks j t) ⟨b, mem_parab_eqBlocks hb⟩ a) =
      ∏ s, u (eqBlocks j t ⟨a, s⟩) := by
  ext
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular, Units.coe_prod]
  · exact Finset.prod_congr rfl fun s _ => (hu _).symm
  · intro s s' h
    refine hb _ _ ?_
    rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
    exact Nat.add_lt_add_right h _

/- English proof (translation)
Take `⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6⟩` from `exists_rep_blocks k (eqBlocks j t) (fun a => ν a) (fun a => hu a) (fun a => hν a) H`. Use `⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, h4, φ, κ, fun b u hb hbu g => ?_, h6⟩` and prove the remaining obligations. Rewrite using `[h5 ⟨b, mem_parab_eqBlocks hb⟩ g, ← val_deltaHalf, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib, ← (eqBlocks j t).prod_comp, Fintype.prod_sigma]`. Use `congr 1`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[det_block hb u hbu, map_prod, map_prod, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[eqBlocks_div, mul_comm, ← val_absPow_ofReal, modExp_eqBlocks]`. Use `congr 3`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_rep_eqBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (j t : ℕ) [MeasurableSpace (GL (Fin (j * t)) k)]
    [BorelSpace (GL (Fin (j * t)) k)] (ν : ℕ → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (ρ : H × GL (Fin (j * t)) k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k (Fin (j * t)), ρ (h, x) v = v) ∧
        ∃ (φ : GL (Fin (j * t)) k → ℂ) (κ : Measure (GL (Fin (j * t)) k)),
          (∀ (b : GL (Fin (j * t)) k) (u : Fin (j * t) → kˣ), (∀ x y, y < x → b.val x y = 0) →
            (∀ x, (u x : k) = b.val x x) → ∀ g, φ (b * g) = (∏ x : Fin (j * t), (ν (x / t) (u x) : ℂ) *
              (nabs k (u x) ^ ((((j * t : ℕ) : ℝ) - t) / 2 - ((x / t : ℕ) : ℝ) * t) : ℝ)) * φ g) ∧
          (∀ x, ∀ y ∈ KO k (Fin (j * t)), φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧
          κ (KO k (Fin (j * t))) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k (Fin (j * t)) : Set (GL (Fin (j * t)) k)), φ (x * g) ∂κ := by
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6⟩ :=
    exists_rep_blocks k (eqBlocks j t) (fun a => ν a) (fun a => hu a) (fun a => hν a) H
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, h4, φ, κ, fun b u hb hbu g => ?_, h6⟩
  rw [h5 ⟨b, mem_parab_eqBlocks hb⟩ g, ← val_deltaHalf, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib,
    ← (eqBlocks j t).prod_comp, Fintype.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [det_block hb u hbu, map_prod, map_prod, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [eqBlocks_div, mul_comm, ← val_absPow_ofReal, modExp_eqBlocks]
  congr 3
  push_cast
  ring

end GlobalTheory.SphCyclic
