import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement

noncomputable section

namespace GlobalTheory.GLm.HcAssoc

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos (Units.isUnit x)]`. Conclude with `Units.ext (IsUnit.unit_spec _)`.
-/
theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos (Units.isUnit x)]
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos h]`. Conclude with `IsUnit.unit_spec h`.
-/
theorem coe_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dif_pos h]
  exact IsUnit.unit_spec h

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, coe_toG (h.mul h'), coe_toG h, coe_toG h']`.
-/
theorem toG_mul {n : ℕ} {M N : Mt g n} (h : IsUnit M) (h' : IsUnit N) : toG (M * N) = toG M * toG N := by
  apply Units.ext
  rw [Units.val_mul, coe_toG (h.mul h'), coe_toG h, coe_toG h']

/- English proof (translation)
Repeatedly rewrite using `[h]`. Conclude with `Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun y => by simp [mul_assoc])`.
-/
theorem sum_conj {G : Type} [Group G] [Fintype G] (F F' : G → ℂ) (s x : G)
    (h : ∀ z, F z = F' (s⁻¹ * z * s)) : ∑ y, F (y⁻¹ * x * y) = ∑ y, F' (y⁻¹ * x * y) := by
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun y => by simp [mul_assoc])

/- English proof (translation)
Unfold `ParBasic.blkM`. Rewrite using `[Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
private lemma blkM_one_zero_one {a b : ℕ} : ParBasic.blkM (1 : Mt g a) 0 (1 : Mt g b) = 1 := by
  unfold ParBasic.blkM
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

/- English proof (translation)
Rewrite using `[← ParBasic.blkM_eq hz]`. Simplify using `only [ParBasic.blkM_mul, ParBasic.tl_blkM, ParBasic.br_blkM, and_true]`. Conclude with `ParBasic.inPar_blkM _ _ _`.
-/
private lemma conj_lemma_2 {a b : ℕ} (A A' : Mt g a) (D D' : Mt g b) {z : Mt g (a + b)} (hz : InPar a z) :
    InPar a (ParBasic.blkM A' 0 D' * z * ParBasic.blkM A 0 D) ∧
      tl a (ParBasic.blkM A' 0 D' * z * ParBasic.blkM A 0 D) = A' * tl a z * A ∧
      br a b (ParBasic.blkM A' 0 D' * z * ParBasic.blkM A 0 D) = D' * br a b z * D := by
  rw [← ParBasic.blkM_eq hz]
  simp only [ParBasic.blkM_mul, ParBasic.tl_blkM, ParBasic.br_blkM, and_true]
  exact ParBasic.inPar_blkM _ _ _

/- English proof (translation)
Establish `hsu : IsUnit (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b))` using `(ParBasic.isUnit_blkM _ _ _).2 ⟨h₁.isUnit, h₂.isUnit⟩`. Establish `htu : IsUnit (ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b))` using `(ParBasic.isUnit_blkM _ _ _).2 ⟨h₁⁻¹.isUnit, h₂⁻¹.isUnit⟩`. Use `⟨toG (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)), coe_toG hsu, ?_⟩` and prove the remaining obligations. Establish `hts : toG (ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b)) * toG (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)) = 1`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, coe_toG htu, coe_toG hsu, ParBasic.blkM_mul, Units.val_one, Units.inv_mul, Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Conclude with `blkM_one_zero_one`. Rewrite using `[← eq_inv_of_mul_eq_one_left hts, coe_toG htu]`.
-/
private lemma exists_blockDiagonal_unit_with_inv {a b : ℕ} (h₁ : Gn g a) (h₂ : Gn g b) : ∃ s : Gn g (a + b),
    (s : Mt g (a + b)) = ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b) ∧
      ((s⁻¹ : Gn g (a + b)) : Mt g (a + b)) =
        ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b) := by
  have hsu : IsUnit (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)) :=
    (ParBasic.isUnit_blkM _ _ _).2 ⟨h₁.isUnit, h₂.isUnit⟩
  have htu : IsUnit (ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b)) :=
    (ParBasic.isUnit_blkM _ _ _).2 ⟨h₁⁻¹.isUnit, h₂⁻¹.isUnit⟩
  refine ⟨toG (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)), coe_toG hsu, ?_⟩
  have hts : toG (ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b)) *
      toG (ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)) = 1 := by
    apply Units.ext
    rw [Units.val_mul, coe_toG htu, coe_toG hsu, ParBasic.blkM_mul, Units.val_one, Units.inv_mul,
      Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact blkM_one_zero_one
  rw [← eq_inv_of_mul_eq_one_left hts, coe_toG htu]

/- English proof (translation)
Establish `e : ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) = ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b) * (z : Mt g (a + b)) * ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b)`. Rewrite using `[Units.val_mul, Units.val_mul, hinv, hsv]`. Distinguish the cases in `hz : InPar a (z : Mt g (a + b))`. Take `⟨u1, u2⟩` from `(GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b (a + b) rfl).2.2.1 z hz`. Take `⟨c1, c2, c3⟩` from `conj_lemma_2 (h₁ : Mt g a) ((h₁⁻¹ : Gn g a) : Mt g a) (h₂ : Mt g b) ((h₂⁻¹ : Gn g b) : Mt g b) hz`.

Rewrite using `[e, if_pos hz, if_pos c1, c2, c3, toG_mul (h₁⁻¹.isUnit.mul u1) h₁.isUnit, toG_mul h₁⁻¹.isUnit u1, toG_mul (h₂⁻¹.isUnit.mul u2) h₂.isUnit, toG_mul h₂⁻¹.isUnit u2]`. Simplify using `only [toG_coe]`. Establish `hw : ¬ InPar a ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b))`. Introduce `hw`. Apply `hz` to reduce the goal to its premises.

Establish `e2 : (z : Mt g (a + b)) = ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b) * ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) * ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b)`. Rewrite using `[← hinv, ← hsv, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Rewrite using `[e2]`.

Conclude with `(conj_lemma_2 _ _ _ _ hw).1`. Rewrite using `[if_neg hz, if_neg hw]`.
-/
private lemma conj_indicator_inPar_eq {a b : ℕ} (Φ : Gn g a → Gn g b → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) (s z : Gn g (a + b))
    (hsv : (s : Mt g (a + b)) = ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b))
    (hinv : ((s⁻¹ : Gn g (a + b)) : Mt g (a + b)) =
      ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b)) :
    (if InPar a (z : Mt g (a + b)) then
      Φ (h₁⁻¹ * toG (tl a (z : Mt g (a + b))) * h₁) (h₂⁻¹ * toG (br a b (z : Mt g (a + b))) * h₂) else 0) =
    (if InPar a ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) then
      Φ (toG (tl a ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b))))
        (toG (br a b ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)))) else 0) := by
  have e : ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) =
      ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b) * (z : Mt g (a + b)) *
        ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b) := by
    rw [Units.val_mul, Units.val_mul, hinv, hsv]
  by_cases hz : InPar a (z : Mt g (a + b))
  · obtain ⟨u1, u2⟩ := (GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b (a + b) rfl).2.2.1 z hz
    obtain ⟨c1, c2, c3⟩ := conj_lemma_2 (h₁ : Mt g a) ((h₁⁻¹ : Gn g a) : Mt g a) (h₂ : Mt g b)
      ((h₂⁻¹ : Gn g b) : Mt g b) hz
    rw [e, if_pos hz, if_pos c1, c2, c3, toG_mul (h₁⁻¹.isUnit.mul u1) h₁.isUnit, toG_mul h₁⁻¹.isUnit u1,
      toG_mul (h₂⁻¹.isUnit.mul u2) h₂.isUnit, toG_mul h₂⁻¹.isUnit u2]
    simp only [toG_coe]
  · have hw : ¬ InPar a ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) := by
      intro hw
      apply hz
      have e2 : (z : Mt g (a + b)) = ParBasic.blkM (h₁ : Mt g a) 0 (h₂ : Mt g b) *
          ((s⁻¹ * z * s : Gn g (a + b)) : Mt g (a + b)) *
            ParBasic.blkM ((h₁⁻¹ : Gn g a) : Mt g a) 0 ((h₂⁻¹ : Gn g b) : Mt g b) := by
        rw [← hinv, ← hsv, ← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      rw [e2]
      exact (conj_lemma_2 _ _ _ _ hw).1
    rw [if_neg hz, if_neg hw]

/- English proof (translation)
Substitute `hn` using the available equality. Use function extensionality and compare the values at `x`. Take `⟨s, hsv, hinv⟩` from `exists_blockDiagonal_unit_with_inv h₁ h₂`. Establish `key` using `sum_conj (fun w : Gn g (a + b) => if InPar a (w : Mt g (a + b)) then Φ (h₁⁻¹ * toG (tl a (w : Mt g (a + b))) * h₁) (h₂⁻¹ * toG (br a b (w : Mt g (a + b))) * h₂) else 0) (fun w : Gn g (a + b) => if InPar a (w : Mt g (a + b)) then Φ (toG (tl a (w : Mt g (a + b)))) (toG (br a b (w : …`. Use `beta_reduce at key`.

Unfold `hcT`. Use `beta_reduce`. Rewrite using `[key]`.
-/
theorem hcT_conj {a b n : ℕ} (hn : n = a + b) (Φ : Gn g a → Gn g b → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) :
    hcT a b (fun u v => Φ (h₁⁻¹ * u * h₁) (h₂⁻¹ * v * h₂)) n = hcT a b Φ n := by
  subst hn
  funext x
  obtain ⟨s, hsv, hinv⟩ := exists_blockDiagonal_unit_with_inv h₁ h₂
  have key := sum_conj
    (fun w : Gn g (a + b) => if InPar a (w : Mt g (a + b)) then
      Φ (h₁⁻¹ * toG (tl a (w : Mt g (a + b))) * h₁) (h₂⁻¹ * toG (br a b (w : Mt g (a + b))) * h₂) else 0)
    (fun w : Gn g (a + b) => if InPar a (w : Mt g (a + b)) then
      Φ (toG (tl a (w : Mt g (a + b)))) (toG (br a b (w : Mt g (a + b)))) else 0) s x
    (fun z => conj_indicator_inPar_eq Φ h₁ h₂ s z hsv hinv)
  beta_reduce at key
  unfold hcT
  beta_reduce
  rw [key]

/- English proof (translation)
Unfold `hcT`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `hP : InPar a ((y⁻¹ * x * y : Gn g n) : Mt g n)`.

Simplify using `only [hP, ↓reduceIte, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Simplify using `only [hP, ↓reduceIte, mul_zero, Finset.sum_const_zero]`.
-/
theorem hcT_sum {a b n : ℕ} {ι : Type} [Fintype ι] (c : ℂ) (Φ : ι → Gn g a → Gn g b → ℂ) (x : Gn g n) :
    hcT a b (fun u v => c * ∑ i, Φ i u v) n x = c * ∑ i, hcT a b (Φ i) n x := by
  unfold hcT
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hP : InPar a ((y⁻¹ * x * y : Gn g n) : Mt g n)
  · simp only [hP, ↓reduceIte, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [hP, ↓reduceIte, mul_zero, Finset.sum_const_zero]

def ext0 (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) (z : Gn g n) : ℂ :=
  if InPar a (z : Mt g n) then α (toG (tl a (z : Mt g n))) * β (toG (br a b (z : Mt g n))) else 0

def cP (g : ℕ) [Fact g.Prime] (a n : ℕ) : ℂ :=
  ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hc_eq (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) (x : Gn g n) :
    hc a b α β n x = cP g a n * ∑ y : Gn g n, ext0 a b α β n (y⁻¹ * x * y) := rfl

/- English proof (translation)
Substitute `hn` using the available equality. Unfold `cP`. Rewrite using `[(GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b (a + b) rfl).2.2.2.2.2, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]`.
-/
theorem indicatorIdempotent_eq_add_sum {a b n : ℕ} (hn : n = a + b) :
    cP g a n = ((Fintype.card (Gn g a) : ℂ) * (Fintype.card (Gn g b) : ℂ) * (g : ℂ) ^ (a * b))⁻¹ := by
  subst hn
  unfold cP
  rw [(GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b (a + b) rfl).2.2.2.2.2, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]

/- English proof (translation)
Establish `e1 : (fun (u : Gn g m) (v : Gn g c) => F u * γ v) = fun u v => k * ∑ h : Gn g m, φ (h⁻¹ * u * h) * γ v`. Use function extensionality and compare the values at `u v`. Simplify using `only [hF, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun h _ => by ring`. Establish `e2` using `hcT_sum (a := m) (b := c) (n := n) k (fun h u v => φ (h⁻¹ * u * h) * γ v) x`.

Use `beta_reduce at e2`. Establish `e3 : ∀ h : Gn g m, hcT m c (fun u v => φ (h⁻¹ * u * h) * γ v) n x = hcT m c (fun u v => φ u * γ v) n x`. Introduce `h`. Use `congrFun (hcT_conj hn (fun u v => φ u * γ v) h 1) x` as an intermediate fact. Simplify using `only [inv_one, one_mul, mul_one] at this`.

Conclude with `this`. Unfold `hc`. Rewrite using `[e1, e2]`. Simplify using `only [e3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stage_left {m c n : ℕ} (hn : n = m + c) (k : ℂ) (φ F : Gn g m → ℂ) (γ : Gn g c → ℂ)
    (hF : ∀ u, F u = k * ∑ h : Gn g m, φ (h⁻¹ * u * h)) (x : Gn g n) :
    hc m c F γ n x = k * (Fintype.card (Gn g m) : ℂ) * hc m c φ γ n x := by
  have e1 : (fun (u : Gn g m) (v : Gn g c) => F u * γ v) =
      fun u v => k * ∑ h : Gn g m, φ (h⁻¹ * u * h) * γ v := by
    funext u v
    simp only [hF, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e2 := hcT_sum (a := m) (b := c) (n := n) k (fun h u v => φ (h⁻¹ * u * h) * γ v) x
  beta_reduce at e2
  have e3 : ∀ h : Gn g m, hcT m c (fun u v => φ (h⁻¹ * u * h) * γ v) n x =
      hcT m c (fun u v => φ u * γ v) n x := by
    intro h
    have := congrFun (hcT_conj hn (fun u v => φ u * γ v) h 1) x
    simp only [inv_one, one_mul, mul_one] at this
    exact this
  unfold hc
  rw [e1, e2]
  simp only [e3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/- English proof (translation)
Establish `e1 : (fun (u : Gn g a) (v : Gn g m) => α u * F v) = fun u v => k * ∑ h : Gn g m, α u * φ (h⁻¹ * v * h)`. Use function extensionality and compare the values at `u v`. Simplify using `only [hF, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun h _ => by ring`. Establish `e2` using `hcT_sum (a := a) (b := m) (n := n) k (fun h u v => α u * φ (h⁻¹ * v * h)) x`.

Use `beta_reduce at e2`. Establish `e3 : ∀ h : Gn g m, hcT a m (fun u v => α u * φ (h⁻¹ * v * h)) n x = hcT a m (fun u v => α u * φ v) n x`. Introduce `h`. Use `congrFun (hcT_conj hn (fun u v => α u * φ v) 1 h) x` as an intermediate fact. Simplify using `only [inv_one, one_mul, mul_one] at this`.

Conclude with `this`. Unfold `hc`. Rewrite using `[e1, e2]`. Simplify using `only [e3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stage_right {a m n : ℕ} (hn : n = a + m) (k : ℂ) (φ F : Gn g m → ℂ) (α : Gn g a → ℂ)
    (hF : ∀ u, F u = k * ∑ h : Gn g m, φ (h⁻¹ * u * h)) (x : Gn g n) :
    hc a m α F n x = k * (Fintype.card (Gn g m) : ℂ) * hc a m α φ n x := by
  have e1 : (fun (u : Gn g a) (v : Gn g m) => α u * F v) =
      fun u v => k * ∑ h : Gn g m, α u * φ (h⁻¹ * v * h) := by
    funext u v
    simp only [hF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e2 := hcT_sum (a := a) (b := m) (n := n) k (fun h u v => α u * φ (h⁻¹ * v * h)) x
  beta_reduce at e2
  have e3 : ∀ h : Gn g m, hcT a m (fun u v => α u * φ (h⁻¹ * v * h)) n x =
      hcT a m (fun u v => α u * φ v) n x := by
    intro h
    have := congrFun (hcT_conj hn (fun u v => α u * φ v) 1 h) x
    simp only [inv_one, one_mul, mul_one] at this
    exact this
  unfold hc
  rw [e1, e2]
  simp only [e3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[entN, dif_pos ⟨hi, hj⟩]`. Both sides reduce to the same expression.
-/
theorem entN_tl {m n : ℕ} (M : Mt g n) {i j : ℕ} (hi : i < m) (hj : j < m) :
    entN (tl m M) i j = entN M i j := by
  rw [entN, dif_pos ⟨hi, hj⟩]
  rfl

/- English proof (translation)
Rewrite using `[entN, dif_pos ⟨hi, hj⟩]`. Both sides reduce to the same expression.
-/
theorem entN_br {a m n : ℕ} (M : Mt g n) {i j : ℕ} (hi : i < m) (hj : j < m) :
    entN (br a m M) i j = entN M (a + i) (a + j) := by
  rw [entN, dif_pos ⟨hi, hj⟩]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hi hj hai`. Establish `hjn : j < n` using `by omega`. Unfold `InPar at h`. Unfold `entN`.

Rewrite using `[dif_pos ⟨hi, hjn⟩]`. Conclude with `h ⟨i, hi⟩ ⟨j, hjn⟩ hj hai`. Introduce `h`. Unfold `InPar`. Introduce `i j hj hai`.

Use `h i j i.2 hj hai` as an intermediate fact. Unfold `entN at this`. Rewrite `this` using `[dif_pos ⟨i.2, j.2⟩]`. Then use the resulting hypothesis.
-/
theorem inPar_iff {a n : ℕ} (M : Mt g n) :
    InPar a M ↔ ∀ i j : ℕ, i < n → j < a → a ≤ i → entN M i j = 0 := by
  constructor
  · intro h i j hi hj hai
    have hjn : j < n := by omega
    unfold InPar at h
    unfold entN
    rw [dif_pos ⟨hi, hjn⟩]
    exact h ⟨i, hi⟩ ⟨j, hjn⟩ hj hai
  · intro h
    unfold InPar
    intro i j hj hai
    have := h i j i.2 hj hai
    unfold entN at this
    rwa [dif_pos ⟨i.2, j.2⟩] at this

/- English proof (translation)
Rewrite using `[inPar_iff, inPar_iff, inPar_iff, inPar_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i j hi hj hai => ?_, fun i j hi hj hbi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hab : i < a + b`.

Rewrite using `[← entN_tl (i := i) (j := j) M hab (by omega)]`. Conclude with `h2 i j hab hj hai`. Conclude with `h1 i j hi (by omega) (by omega)`. Rewrite using `[entN_br (i := i) (j := j) M hi (by omega)]`. Conclude with `h1 (a + i) (a + j) (by omega) (by omega) (by omega)`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i j hi hj hi' => ?_, fun i j hi hj hai => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hja : j < a`. Conclude with `h1 i j hi hja (by omega)`. Establish `h3` using `h2 (i - a) (j - a) (by omega) (by omega) (by omega)`.

Rewrite `h3` using `[entN_br (i := i - a) (j := j - a) M (by omega) (by omega)]`. Rewrite `h3` using `[show a + (i - a) = i by omega, show a + (j - a) = j by omega]`. Then use the resulting hypothesis. Rewrite using `[entN_tl (i := i) (j := j) M hi (by omega)]`. Conclude with `h1 i j (by omega) hj hai`.
-/
theorem par_par {a b c n : ℕ} (hn : n = a + b + c) (M : Mt g n) :
    (InPar (a + b) M ∧ InPar a (tl (a + b) M)) ↔ (InPar a M ∧ InPar b (br a (b + c) M)) := by
  rw [inPar_iff, inPar_iff, inPar_iff, inPar_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hi hj hai => ?_, fun i j hi hj hbi => ?_⟩
    · by_cases hab : i < a + b
      · rw [← entN_tl (i := i) (j := j) M hab (by omega)]
        exact h2 i j hab hj hai
      · exact h1 i j hi (by omega) (by omega)
    · rw [entN_br (i := i) (j := j) M hi (by omega)]
      exact h1 (a + i) (a + j) (by omega) (by omega) (by omega)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hi hj hi' => ?_, fun i j hi hj hai => ?_⟩
    · by_cases hja : j < a
      · exact h1 i j hi hja (by omega)
      · have h3 := h2 (i - a) (j - a) (by omega) (by omega) (by omega)
        rw [entN_br (i := i - a) (j := j - a) M (by omega) (by omega)] at h3
        rwa [show a + (i - a) = i by omega, show a + (j - a) = j by omega] at h3
    · rw [entN_tl (i := i) (j := j) M hi (by omega)]
      exact h1 i j (by omega) hj hai

/- English proof (translation)
Use extensionality with `i j`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Use `show entN (tl m M) i j = entN M i j`. Conclude with `entN_tl M (by omega) (by omega)`.
-/
private lemma tl_tl_of_le {a m n : ℕ} (h : a ≤ m) (M : Mt g n) : tl a (tl m M) = tl a M := by
  ext i j
  have := i.2
  have := j.2
  show entN (tl m M) i j = entN M i j
  exact entN_tl M (by omega) (by omega)

/- English proof (translation)
Use extensionality with `i j`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Use `show entN (tl m M) (a + i) (a + j) = entN (br a k M) i j`. Rewrite using `[entN_tl (i := a + i) (j := a + j) M (by omega) (by omega), entN_br (i := i) (j := j) M (by omega) (by omega)]`.
-/
private lemma br_tl_eq_tl_br {a b m k n : ℕ} (h : a + b ≤ m) (hk : b ≤ k) (M : Mt g n) :
    br a b (tl m M) = tl b (br a k M) := by
  ext i j
  have := i.2
  have := j.2
  show entN (tl m M) (a + i) (a + j) = entN (br a k M) i j
  rw [entN_tl (i := a + i) (j := a + j) M (by omega) (by omega),
    entN_br (i := i) (j := j) M (by omega) (by omega)]

/- English proof (translation)
Use extensionality with `i j`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Use `show entN M (a + b + i) (a + b + j) = entN (br a (b + c) M) (b + i) (b + j)`. Rewrite using `[entN_br (i := b + i) (j := b + j) M (by omega) (by omega), Nat.add_assoc, Nat.add_assoc]`.
-/
private lemma br_add_eq_br_br {a b c n : ℕ} (M : Mt g n) : br (a + b) c M = br b c (br a (b + c) M) := by
  ext i j
  have := i.2
  have := j.2
  show entN M (a + b + i) (a + b + j) = entN (br a (b + c) M) (b + i) (b + j)
  rw [entN_br (i := b + i) (j := b + j) M (by omega) (by omega), Nat.add_assoc, Nat.add_assoc]

/- English proof (translation)
Take `⟨-, -, hu1, -, -, -⟩` from `GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g (a + b) c n hn`. Take `⟨-, -, hu2, -, -, -⟩` from `GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a (b + c) n (by omega)`. Establish `hpp` using `par_par hn (z : Mt g n)`. Unfold `ext0`. Apply the tactic sequence `by_cases hA : InPar (a + b) (z : Mt g n) <;> by_cases hB : InPar a (z : Mt g n)`.

Rewrite using `[coe_toG (hu1 z hA).1, coe_toG (hu2 z hB).2]`. Distinguish the cases in `hX : InPar a (tl (a + b) (z : Mt g n))`. Establish `hY` using `(hpp.1 ⟨hA, hX⟩).2`. Rewrite using `[if_pos hA, if_pos hB, if_pos hX, if_pos hY, tl_tl_of_le (Nat.le_add_right a b), br_tl_eq_tl_br (le_refl (a + b)) (Nat.le_add_right b c), br_add_eq_br_br]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hY : ¬ InPar b (br a (b + c) (z : Mt g n))` using `fun hY => hX (hpp.2 ⟨hB, hY⟩).2`. Rewrite using `[if_pos hA, if_pos hB, if_neg hX, if_neg hY]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX : ¬ InPar a (tl (a + b) (z : Mt g n))` using `fun hX => hB (hpp.1 ⟨hA, hX⟩).1`. Rewrite using `[coe_toG (hu1 z hA).1, if_pos hA, if_neg hB, if_neg hX]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hY : ¬ InPar b (br a (b + c) (z : Mt g n))` using `fun hY => hA (hpp.2 ⟨hB, hY⟩).1`. Rewrite using `[coe_toG (hu2 z hB).2, if_neg hA, if_pos hB, if_neg hY]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hA, if_neg hB]`.
-/
theorem blockParabolicProductExtendedByZero_assoc {a b c n : ℕ} (hn : n = a + b + c) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ)
    (z : Gn g n) :
    ext0 (a + b) c (ext0 a b α β (a + b)) γ n z = ext0 a (b + c) α (ext0 b c β γ (b + c)) n z := by
  obtain ⟨-, -, hu1, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g (a + b) c n hn
  obtain ⟨-, -, hu2, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a (b + c) n (by omega)
  have hpp := par_par hn (z : Mt g n)
  unfold ext0
  by_cases hA : InPar (a + b) (z : Mt g n) <;> by_cases hB : InPar a (z : Mt g n)
  · rw [coe_toG (hu1 z hA).1, coe_toG (hu2 z hB).2]
    by_cases hX : InPar a (tl (a + b) (z : Mt g n))
    · have hY := (hpp.1 ⟨hA, hX⟩).2
      rw [if_pos hA, if_pos hB, if_pos hX, if_pos hY, tl_tl_of_le (Nat.le_add_right a b),
        br_tl_eq_tl_br (le_refl (a + b)) (Nat.le_add_right b c), br_add_eq_br_br]
      ring
    · have hY : ¬ InPar b (br a (b + c) (z : Mt g n)) := fun hY => hX (hpp.2 ⟨hB, hY⟩).2
      rw [if_pos hA, if_pos hB, if_neg hX, if_neg hY]
      ring
  · have hX : ¬ InPar a (tl (a + b) (z : Mt g n)) := fun hX => hB (hpp.1 ⟨hA, hX⟩).1
    rw [coe_toG (hu1 z hA).1, if_pos hA, if_neg hB, if_neg hX]
    ring
  · have hY : ¬ InPar b (br a (b + c) (z : Mt g n)) := fun hY => hA (hpp.2 ⟨hB, hY⟩).1
    rw [coe_toG (hu2 z hB).2, if_neg hA, if_pos hB, if_neg hY]
    ring
  · rw [if_neg hA, if_neg hB]

/- English proof (translation)
Introduce `g _ a b c n α β γ _ _ _ hn`. Use function extensionality and compare the values at `x`. Establish `hL` using `stage_left (m := a + b) (c := c) (n := n) hn (cP g a (a + b)) (ext0 a b α β (a + b)) (hc a b α β (a + b)) γ (fun u => hc_eq a b α β (a + b) u) x`. Establish `hR` using `stage_right (a := a) (m := b + c) (n := n) (by omega) (cP g b (b + c)) (ext0 b c β γ (b + c)) (hc b c β γ (b + c)) α (fun u => hc_eq b c β γ (b + c) u) x`. Rewrite using `[hL, hR, hc_eq, hc_eq]`.

Simplify using `only [blockParabolicProductExtendedByZero_assoc hn α β γ]`. Rewrite using `[indicatorIdempotent_eq_add_sum (a := a) (b := b) rfl, indicatorIdempotent_eq_add_sum (a := b) (b := c) rfl, indicatorIdempotent_eq_add_sum (a := a + b) (b := c) hn, indicatorIdempotent_eq_add_sum (a := a) (b := b + c) (by omega)]`. Establish `h1 : (Fintype.card (Gn g a) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `h2 : (Fintype.card (Gn g b) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `h3 : (Fintype.card (Gn g c) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`.

Establish `h4 : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `h5 : (Fintype.card (Gn g (b + c)) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hg : (g : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hc_assoc : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ),
    IsClass α → IsClass β → IsClass γ → n = a + b + c →
      hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n := by
  intro g _ a b c n α β γ _ _ _ hn
  funext x
  have hL := stage_left (m := a + b) (c := c) (n := n) hn (cP g a (a + b)) (ext0 a b α β (a + b))
    (hc a b α β (a + b)) γ (fun u => hc_eq a b α β (a + b) u) x
  have hR := stage_right (a := a) (m := b + c) (n := n) (by omega) (cP g b (b + c)) (ext0 b c β γ (b + c))
    (hc b c β γ (b + c)) α (fun u => hc_eq b c β γ (b + c) u) x
  rw [hL, hR, hc_eq, hc_eq]
  simp only [blockParabolicProductExtendedByZero_assoc hn α β γ]
  rw [indicatorIdempotent_eq_add_sum (a := a) (b := b) rfl, indicatorIdempotent_eq_add_sum (a := b) (b := c) rfl, indicatorIdempotent_eq_add_sum (a := a + b) (b := c) hn,
    indicatorIdempotent_eq_add_sum (a := a) (b := b + c) (by omega)]
  have h1 : (Fintype.card (Gn g a) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : (Fintype.card (Gn g b) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h3 : (Fintype.card (Gn g c) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h4 : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h5 : (Fintype.card (Gn g (b + c)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  field_simp
  ring

end GlobalTheory.GLm.HcAssoc
