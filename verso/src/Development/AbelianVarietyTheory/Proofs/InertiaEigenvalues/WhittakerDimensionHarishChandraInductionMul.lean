import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDoubleCosetMulCardInter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueShuffle
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WhittakerTermEqZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfUniUp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShuffleNoDescentIffOpen

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.WhMul

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `entN`. Use `split_ifs with h`. Use `set i : Fin n := ⟨k, h.1⟩ set j : Fin n := ⟨k + 1, h.2⟩`. Establish `hij : i ≠ j` using `by simp [i, j, Fin.ext_iff]`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add i j hij]`.

Rewrite using `[(hM i i).2 rfl, (hN j j).2 rfl, one_mul, mul_one, add_comm]`. Introduce and unpack `c ⟨hci, hcj⟩`. Distinguish the cases in `hc : c < i`. Rewrite using `[(hM i c).1 hc, zero_mul]`. Establish `: j < c`.

Rewrite `hc`, the goal using `[Fin.lt_def]`. Establish `h1 : (c : ℕ) ≠ k` using `fun e => hci (Fin.ext e)`. Establish `h2 : (c : ℕ) ≠ k + 1` using `fun e => hcj (Fin.ext e)`. Simplify using `only [i, j] at hc ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[(hN c j).1 this, mul_zero]`. Simplify using `only [add_zero]`.
-/
theorem entN_mul_succ {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) (k : ℕ) :
    entN (M * N) k (k + 1) = entN M k (k + 1) + entN N k (k + 1) := by
  unfold entN
  split_ifs with h
  · set i : Fin n := ⟨k, h.1⟩
    set j : Fin n := ⟨k + 1, h.2⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [(hM i i).2 rfl, (hN j j).2 rfl, one_mul, mul_one, add_comm]
    · rintro c ⟨hci, hcj⟩
      by_cases hc : c < i
      · rw [(hM i c).1 hc, zero_mul]
      · have : j < c := by
          rw [Fin.lt_def] at hc ⊢
          have h1 : (c : ℕ) ≠ k := fun e => hci (Fin.ext e)
          have h2 : (c : ℕ) ≠ k + 1 := fun e => hcj (Fin.ext e)
          simp only [i, j] at hc ⊢
          omega
        rw [(hN c j).1 this, mul_zero]
  · simp only [add_zero]

/- English proof (translation)
Unfold `supFrom`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => entN_mul_succ M N hM hN k`.
-/
theorem supFrom_mul {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) :
    supFrom 0 (M * N) = supFrom 0 M + supFrom 0 N := by
  unfold supFrom
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => entN_mul_succ M N hM hN k

/- English proof (translation)
Unfold `supFrom`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Unfold `entN`. Use `split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`.

Simplify using `[Fin.ext_iff]`. Both sides reduce to the same expression.
-/
theorem supFrom_one (n : ℕ) : supFrom 0 (1 : Mt g n) = 0 := by
  unfold supFrom
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold entN
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    simp [Fin.ext_iff]
  · rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[ParBasic.tl_apply, Matrix.one_apply, Matrix.one_apply]`. Simplify using `[Fin.ext_iff]`.
-/
theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.tl_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[ParBasic.br_apply, Matrix.one_apply, Matrix.one_apply]`. Simplify using `[Fin.ext_iff]`.
-/
theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.br_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

/- English proof (translation)
Introduce `g _ ψ hψ a b n hn Φ hΦ1 hΦ2`. Take `⟨⟨P, hP⟩, ⟨U, hU⟩, -, -, -, -⟩` from `ParBasic.par_basic g a b n hn`. Substitute `hn` using the available equality. Establish `hl : ∀ h ∈ U, ∀ x ∈ U, (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (h * x * h⁻¹) = (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) x`. Introduce `h hh x hx`.

Establish `hh'` using `(hU h).1 hh`. Establish `hx'` using `(hU x).1 hx`. Establish `hi'` using `(hU h⁻¹).1 (U.inv_mem hh)`. Establish `e1 : supFrom 0 ((h : Mt g (a + b)) * ((h⁻¹ : Gn g (a + b)) : Mt g (a + b))) = 0`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, supFrom_one]`.

Rewrite `e1` using `[supFrom_mul _ _ hh' hi']`. Establish `hxh` using `ParBasic.isUniUp_mul _ _ hh' hx'`. Simplify using `only [Units.val_mul]`. Rewrite using `[supFrom_mul _ _ hxh hi', supFrom_mul _ _ hh' hx']`. Use `congr 2`.

Take the linear combination `e1`. Establish `hφ : ∀ k ∈ P, ∀ x ∈ P, (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) (k * x * k⁻¹) = (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) x`. Introduce `k hk x hx`. Establish `hk'` using `(hP k).1 hk`. Establish `hx'` using `(hP x).1 hx`.

Establish `hi'` using `(hP k⁻¹).1 (P.inv_mem hk)`. Establish `hkx` using `(hP (k * x)).1 (P.mul_mem hk hx)`. Take `⟨uk, vk⟩` from `ParBasic.isUnit_blocks k hk'`. Take `⟨ux, vx⟩` from `ParBasic.isUnit_blocks x hx'`. Establish `m1` using `ParBasic.blocks_mul _ _ hk' hi'`.

Establish `m2` using `ParBasic.blocks_mul _ _ hk' hx'`. Establish `m3` using `ParBasic.blocks_mul _ _ hkx hi'`. Establish `hkxk` using `(hP (k * x * k⁻¹)).1 (P.mul_mem (P.mul_mem hk hx) (P.inv_mem hk))`. Take `⟨uc, vc⟩` from `ParBasic.isUnit_blocks _ hkxk`. Establish `e1 : ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = (k : Mt g (a + b)) * (x : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b))`.

Simplify using `only [Units.val_mul]`. Establish `e0 : (k : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `iA : (((toG (tl a (k : Mt g (a + b))))⁻¹ : Gn g a) : Mt g a) = tl a ((k⁻¹ : Gn g (a + b)) : Mt g (a + b))`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises.

Rewrite using `[OpenCell.coe_toG uk, ← m1.2.1, e0, tl_one]`. Establish `iB : (((toG (br a b (k : Mt g (a + b))))⁻¹ : Gn g b) : Mt g b) = br a b ((k⁻¹ : Gn g (a + b)) : Mt g (a + b))`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[OpenCell.coe_toG vk, ← m1.2.2, e0, br_one]`. Establish `cA : toG (tl a ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) = toG (tl a (k : Mt g (a + b))) * toG (tl a (x : Mt g (a + b))) * (toG (tl a (k : Mt g (a + b))))⁻¹`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[OpenCell.coe_toG uc]`. Simplify using `only [Units.val_mul] at m3 ⊢`. Rewrite using `[iA, OpenCell.coe_toG uk, OpenCell.coe_toG ux, m3.2.1, m2.2.1]`. Establish `cB : toG (br a b ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) = toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[OpenCell.coe_toG vc]`. Simplify using `only [Units.val_mul] at m3 ⊢`. Rewrite using `[iB, OpenCell.coe_toG vk, OpenCell.coe_toG vx, m3.2.2, m2.2.2]`. Use `show Φ _ _ = Φ _ _`.

Rewrite using `[cA, cB]`. Establish `h1` using `hΦ1 (toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹) (toG (tl a (x : Mt g (a + b)))) (toG (tl a (k : Mt g (a + b))))`. Establish `h2` using `hΦ2 (toG (tl a (x : Mt g (a + b)))) (toG (br a b (x : Mt g (a + b)))) (toG (br a b (k : Mt g (a + b))))`. Simplify using `only at h1 h2`. Rewrite using `[h1, h2]`.

Use `set R : Finset (Equiv.Perm (Fin (a + b))) := Finset.univ.filter fun σ => ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j with hR`. Establish `hRu : ∀ x : Gn g (a + b), ∃! σ, σ ∈ R ∧ ∃ h ∈ U, ∃ k ∈ P, x = h * pm g σ * k`. Introduce `x`. Take `⟨σ, ⟨hσ, u, p, hu, hp, hx⟩, huniq⟩` from `Shuffle.existsUnique_shuffle g a (a + b) (Nat.le_add_right a b) x`. Use `⟨σ, ⟨by simpa [hR] using hσ, u, (hU u).2 hu, p, (hP p).2 hp, hx⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `τ ⟨hτ, u', hu', p', hp', hx'⟩`. Conclude with `huniq τ ⟨by simpa [hR] using hτ, u', p', (hU u').1 hu', (hP p').1 hp', hx'⟩`. Establish `M` using `mackey_doubleCoset_pairing (Gn g (a + b)) U P _ R (pm g) hRu (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) hl hφ`. Establish `cU : (Nat.card U : ℂ) = ((Finset.univ.filter fun u : Gn g (a + b) => IsUniUp (u : Mt g (a + b))).card : ℂ)`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`.

Simplify using `only [hU]`. Establish `cP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Simplify using `only [hP]`. Use `Eq.trans ?_ (M.trans ?_)` and prove the remaining obligations.

Rewrite using `[OpenCell.wh_eq, cU, cP, ← Finset.sum_filter]`. Simplify using `only [hU, hP]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨σ₀, h0⟩ : ∃ σ₀ : Equiv.Perm (Fin (a + b)), ∀ j : Fin (a + b), (σ₀ j : ℕ) = if (j : ℕ) < a then b + j else j - a := by`. Apply the tactic sequence `let f : Fin (a + b) → Fin (a + b) := fun j => ⟨if (j : ℕ) < a then b + j else j - a, by have := j.2; split_ifs <;> omega⟩`.

Establish `hf : Function.Injective f`. Introduce `i j h`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [f, Fin.mk.injEq] at h`.

Use `ext`. Apply the tactic sequence `split_ifs at h <;> omega`. Conclude with `⟨Equiv.ofBijective f hf.bijective_of_finite, fun j => rfl⟩`. Establish `h0R : σ₀ ∈ R`. Simplify using `only [hR, Finset.mem_filter, Finset.mem_univ, true_and]`.

Introduce `i j hij hb`. Rewrite `hij`, the goal using `[Fin.lt_def]`. Rewrite using `[h0, h0]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[Finset.sum_eq_single_of_mem σ₀ h0R]`.

Simplify using `only [hU, hP]`. Conclude with `OpenCell.openCell g ψ a b (a + b) σ₀ Φ rfl h0`. Introduce `σ hσ hne`. Establish `hσ' : ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j`. Simplify `hσ` using `[hR]`.

Establish `hnd : ¬ ∀ i j : Fin (a + b), (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Conclude with `Equiv.ext fun j => Fin.ext (by rw [(shuffle_noDescent_iff_open a b (a + b) σ rfl hσ').1 h j, h0 j])`. Use `push Not at hnd`.

Take `⟨i, j, hi, hj, hij⟩` from `hnd`. Simplify using `only [hU, hP]`. Rewrite using `[NonOpenCell.whittaker_term_eq_zero g ψ hψ a b (a + b) σ Φ i j rfl hi hj hij, mul_zero]`.
-/
theorem wh_hcT : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) →
      wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  intro g _ ψ hψ a b n hn Φ hΦ1 hΦ2
  obtain ⟨⟨P, hP⟩, ⟨U, hU⟩, -, -, -, -⟩ := ParBasic.par_basic g a b n hn
  subst hn

  have hl : ∀ h ∈ U, ∀ x ∈ U, (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (h * x * h⁻¹) =
      (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) x := by
    intro h hh x hx
    have hh' := (hU h).1 hh
    have hx' := (hU x).1 hx
    have hi' := (hU h⁻¹).1 (U.inv_mem hh)
    have e1 : supFrom 0 ((h : Mt g (a + b)) * ((h⁻¹ : Gn g (a + b)) : Mt g (a + b))) = 0 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, supFrom_one]
    rw [supFrom_mul _ _ hh' hi'] at e1
    have hxh := ParBasic.isUniUp_mul _ _ hh' hx'
    simp only [Units.val_mul]
    rw [supFrom_mul _ _ hxh hi', supFrom_mul _ _ hh' hx']
    congr 2
    linear_combination e1

  have hφ : ∀ k ∈ P, ∀ x ∈ P,
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) (k * x * k⁻¹) =
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) x := by
    intro k hk x hx
    have hk' := (hP k).1 hk
    have hx' := (hP x).1 hx
    have hi' := (hP k⁻¹).1 (P.inv_mem hk)
    have hkx := (hP (k * x)).1 (P.mul_mem hk hx)
    obtain ⟨uk, vk⟩ := ParBasic.isUnit_blocks k hk'
    obtain ⟨ux, vx⟩ := ParBasic.isUnit_blocks x hx'
    have m1 := ParBasic.blocks_mul _ _ hk' hi'
    have m2 := ParBasic.blocks_mul _ _ hk' hx'
    have m3 := ParBasic.blocks_mul _ _ hkx hi'
    have hkxk := (hP (k * x * k⁻¹)).1 (P.mul_mem (P.mul_mem hk hx) (P.inv_mem hk))
    obtain ⟨uc, vc⟩ := ParBasic.isUnit_blocks _ hkxk
    have e1 : ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = (k : Mt g (a + b)) * (x : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      simp only [Units.val_mul]
    have e0 : (k : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have iA : (((toG (tl a (k : Mt g (a + b))))⁻¹ : Gn g a) : Mt g a) = tl a ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG uk, ← m1.2.1, e0, tl_one]
    have iB : (((toG (br a b (k : Mt g (a + b))))⁻¹ : Gn g b) : Mt g b) = br a b ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG vk, ← m1.2.2, e0, br_one]
    have cA : toG (tl a ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (tl a (k : Mt g (a + b))) * toG (tl a (x : Mt g (a + b))) * (toG (tl a (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG uc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iA, OpenCell.coe_toG uk, OpenCell.coe_toG ux, m3.2.1, m2.2.1]
    have cB : toG (br a b ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG vc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iB, OpenCell.coe_toG vk, OpenCell.coe_toG vx, m3.2.2, m2.2.2]
    show Φ _ _ = Φ _ _
    rw [cA, cB]
    have h1 := hΦ1 (toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹)
      (toG (tl a (x : Mt g (a + b)))) (toG (tl a (k : Mt g (a + b))))
    have h2 := hΦ2 (toG (tl a (x : Mt g (a + b)))) (toG (br a b (x : Mt g (a + b)))) (toG (br a b (k : Mt g (a + b))))
    simp only at h1 h2
    rw [h1, h2]
  set R : Finset (Equiv.Perm (Fin (a + b))) := Finset.univ.filter fun σ =>
    ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j with hR
  have hRu : ∀ x : Gn g (a + b), ∃! σ, σ ∈ R ∧ ∃ h ∈ U, ∃ k ∈ P, x = h * pm g σ * k := by
    intro x
    obtain ⟨σ, ⟨hσ, u, p, hu, hp, hx⟩, huniq⟩ :=
      Shuffle.existsUnique_shuffle g a (a + b) (Nat.le_add_right a b) x
    refine ⟨σ, ⟨by simpa [hR] using hσ, u, (hU u).2 hu, p, (hP p).2 hp, hx⟩, ?_⟩
    rintro τ ⟨hτ, u', hu', p', hp', hx'⟩
    exact huniq τ ⟨by simpa [hR] using hτ, u', p', (hU u').1 hu', (hP p').1 hp', hx'⟩
  have M := mackey_doubleCoset_pairing (Gn g (a + b)) U P _ R (pm g) hRu
    (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹)
    (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) hl hφ
  have cU : (Nat.card U : ℂ) = ((Finset.univ.filter fun u : Gn g (a + b) => IsUniUp (u : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hU]
  have cP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hP]
  refine Eq.trans ?_ (M.trans ?_)
  · rw [OpenCell.wh_eq, cU, cP, ← Finset.sum_filter]
    simp only [hU, hP]
    rfl
  obtain ⟨σ₀, h0⟩ : ∃ σ₀ : Equiv.Perm (Fin (a + b)),
      ∀ j : Fin (a + b), (σ₀ j : ℕ) = if (j : ℕ) < a then b + j else j - a := by
    let f : Fin (a + b) → Fin (a + b) := fun j =>
      ⟨if (j : ℕ) < a then b + j else j - a, by have := j.2; split_ifs <;> omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have := i.2
      have := j.2
      simp only [f, Fin.mk.injEq] at h
      ext
      split_ifs at h <;> omega
    exact ⟨Equiv.ofBijective f hf.bijective_of_finite, fun j => rfl⟩
  have h0R : σ₀ ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i j hij hb
    rw [Fin.lt_def] at hij ⊢
    rw [h0, h0]
    split_ifs <;> omega
  rw [Finset.sum_eq_single_of_mem σ₀ h0R]
  · simp only [hU, hP]
    exact OpenCell.openCell g ψ a b (a + b) σ₀ Φ rfl h0
  · intro σ hσ hne
    have hσ' : ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j := by
      simpa [hR] using hσ
    have hnd : ¬ ∀ i j : Fin (a + b), (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1 := by
      intro h
      apply hne
      exact Equiv.ext fun j => Fin.ext (by rw [(shuffle_noDescent_iff_open a b (a + b) σ rfl hσ').1 h j, h0 j])
    push Not at hnd
    obtain ⟨i, j, hi, hj, hij⟩ := hnd
    simp only [hU, hP]
    rw [NonOpenCell.whittaker_term_eq_zero g ψ hψ a b (a + b) σ Φ i j rfl hi hj hij, mul_zero]

end GlobalTheory.GLq.WhMul
