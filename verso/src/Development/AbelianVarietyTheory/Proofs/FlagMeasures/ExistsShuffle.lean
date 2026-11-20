import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParCoset

open GlobalTheory.FinGL Formalism.L2.DIV Finset

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Apply the tactic sequence `apply h <;> (dsimp only at hij; split_ifs at hij <;> omega)`. Introduce `h i j hj hi`. Apply `h` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[if_pos hj, if_neg (by omega)]`. Conclude with `Nat.zero_lt_one`.
-/
theorem inPar_iff (a : ℕ) (M : Mt g n) :
    InPar a M ↔ M.BlockTriangular (fun i : Fin n => if (i : ℕ) < a then 0 else 1) := by
  constructor
  · intro h i j hij
    apply h <;> (dsimp only at hij; split_ifs at hij <;> omega)
  · intro h i j hj hi
    apply h
    dsimp only
    rw [if_pos hj, if_neg (by omega)]
    exact Nat.zero_lt_one

/- English proof (translation)
Rewrite `*` using `[inPar_iff]`. Conclude with `hx.mul hy`.
-/
theorem inPar_mul {a : ℕ} {x y : Gn g n} (hx : InPar a (x : Mt g n)) (hy : InPar a (y : Mt g n)) :
    InPar a ((x * y : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  exact hx.mul hy

/- English proof (translation)
Rewrite `*` using `[inPar_iff]`. Rewrite using `[Matrix.coe_units_inv]`. Use `haveI := x.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hx`.
-/
theorem inPar_inv {a : ℕ} {x : Gn g n} (hx : InPar a (x : Mt g n)) : InPar a ((x⁻¹ : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  rw [Matrix.coe_units_inv]
  haveI := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

def pMat (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Mt g n := fun r j => if r = σ j then 1 else 0

/- English proof (translation)
Use extensionality with `r j`. Simplify using `[pMat, Matrix.mul_apply]`. Reduce the equality to equality of the corresponding arguments.
-/
theorem pMat_mul (σ τ : Equiv.Perm (Fin n)) : pMat g σ * pMat g τ = pMat g (σ * τ) := by
  ext r j
  simp [pMat, Matrix.mul_apply]
  congr

/- English proof (translation)
Use extensionality with `r j`. Simplify using `[pMat, Matrix.one_apply]`. Reduce the equality to equality of the corresponding arguments.
-/
theorem pMat_one : pMat g (1 : Equiv.Perm (Fin n)) = 1 := by
  ext r j
  simp [pMat, Matrix.one_apply]
  congr

def pU (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Gn g n :=
  ⟨pMat g σ, pMat g σ⁻¹, by rw [pMat_mul, mul_inv_cancel, pMat_one], by rw [pMat_mul, inv_mul_cancel, pMat_one]⟩

/- English proof (translation)
The claim follows from `Units.ext (pMat_mul σ τ).symm`.
-/
theorem pU_mul (σ τ : Equiv.Perm (Fin n)) : pU g (σ * τ) = pU g σ * pU g τ :=
  Units.ext (pMat_mul σ τ).symm

/- English proof (translation)
Introduce `i j hj hi`. Establish `: i ≠ τ j`. Introduce and unpack `rfl`. Use `(h j).2 hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `if_neg this`.
-/
theorem inPar_pU {a : ℕ} {τ : Equiv.Perm (Fin n)} (h : ∀ j, (τ j : ℕ) < a ↔ (j : ℕ) < a) :
    InPar a ((pU g τ : Gn g n) : Mt g n) := by
  intro i j hj hi
  have : i ≠ τ j := by
    rintro rfl
    have := (h j).2 hj
    omega
  exact if_neg this

noncomputable def rk (a c : ℕ) (M : Mt g n) : ℕ :=
  (Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) * M *
    Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0)).rank

/- English proof (translation)
Unfold `rk`. Use `set F : Mt g n := Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) with hF`. Use `set E : Mt g n := Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) with hE`. Establish `h1 : F * p = F * p * F`. Use extensionality with `i j`.

Simplify using `only [hF, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `split_ifs with h h'`. Simplify using the standard rewrite rules. Rewrite using `[hp i j (by omega) h]; simp`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish `h2 : q * E = E * (q * E)`. Use extensionality with `i j`. Simplify using `only [hE, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `split_ifs with h h'`.

Simplify using the standard rewrite rules. Rewrite using `[hq i j h (by omega)]; simp`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `h3 : F * (p * M * q) * E = (F * p) * ((F * M * E) * (q * E))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`. Conclude with `(Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)`.
-/
theorem rk_le {a c : ℕ} {p q : Mt g n} (hp : InPar c p) (hq : InPar a q) (M : Mt g n) :
    rk a c (p * M * q) ≤ rk a c M := by
  unfold rk
  set F : Mt g n := Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) with hF
  set E : Mt g n := Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) with hE
  have h1 : F * p = F * p * F := by
    ext i j
    simp only [hF, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hp i j (by omega) h]; simp
    · simp
    · simp
  have h2 : q * E = E * (q * E) := by
    ext i j
    simp only [hE, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hq i j h (by omega)]; simp
    · simp
    · simp
  have h3 : F * (p * M * q) * E = (F * p) * ((F * M * E) * (q * E)) := by
    calc F * (p * M * q) * E = (F * p) * M * (q * E) := by simp only [Matrix.mul_assoc]
      _ = (F * p * F) * M * (E * (q * E)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

/- English proof (translation)
Use `le_antisymm (rk_le hp hq _) ?_` and prove the remaining obligations. Establish `h` using `rk_le (inPar_inv hp) (inPar_inv hq) ((p * x * q : Gn g n) : Mt g n)`. Rewrite `h` using `[← Units.val_mul, ← Units.val_mul]`. Establish `e : p⁻¹ * (p * x * q) * q⁻¹ = x` using `by group`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem rk_eq {a c : ℕ} {p q : Gn g n} (hp : InPar c (p : Mt g n)) (hq : InPar a (q : Mt g n)) (x : Gn g n) :
    rk a c ((p * x * q : Gn g n) : Mt g n) = rk a c (x : Mt g n) := by
  refine le_antisymm (rk_le hp hq _) ?_
  have h := rk_le (inPar_inv hp) (inPar_inv hq) ((p * x * q : Gn g n) : Mt g n)
  rw [← Units.val_mul, ← Units.val_mul] at h
  have e : p⁻¹ * (p * x * q) * q⁻¹ = x := by group
  rwa [e] at h

/- English proof (translation)
Unfold `rk`. Establish `h : Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) * ((pU g σ : Gn g n) : Mt g n) * Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) = ((pU g σ : Gn g n) : Mt g n) * Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a ∧ ¬ (σ j : …`. Use extensionality with `r j`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, pU, pMat]`. Distinguish the cases in `hr : r = σ j`.

Substitute `hr` using the available equality. Apply the tactic sequence `by_cases h1 : (j : ℕ) < a <;> by_cases h2 : c ≤ (σ j : ℕ) <;> simp [h1, h2]`. Simplify using `[hr]`. Rewrite using `[h, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _), Matrix.rank_diagonal, Fintype.card_subtype]`. Use `congr 1`.

Use extensionality with `j`. Simplify using the standard rewrite rules.
-/
theorem rk_pU (a c : ℕ) (σ : Equiv.Perm (Fin n)) :
    rk a c ((pU g σ : Gn g n) : Mt g n) = #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} := by
  unfold rk
  have h : Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) *
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) =
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c then (1 : ZMod g) else 0) := by
    ext r j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, pU, pMat]
    by_cases hr : r = σ j
    · subst hr
      by_cases h1 : (j : ℕ) < a <;> by_cases h2 : c ≤ (σ j : ℕ) <;> simp [h1, h2]
    · simp [hr]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _), Matrix.rank_diagonal,
    Fintype.card_subtype]
  congr 1
  ext j
  simp

/- English proof (translation)
Establish `h : #{j : Fin n | (σ j : ℕ) < a} = #{j : Fin n | (j : ℕ) < a}` using `Finset.card_equiv σ (by simp)`. Rewrite using `[h, Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_lt {a : ℕ} (ha : a ≤ n) (σ : Equiv.Perm (Fin n)) : #{j : Fin n | (σ j : ℕ) < a} = a := by
  have h : #{j : Fin n | (σ j : ℕ) < a} = #{j : Fin n | (j : ℕ) < a} :=
    Finset.card_equiv σ (by simp)
  rw [h, Fin.card_filter_val_lt]
  omega

/- English proof (translation)
Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_lt' {a : ℕ} (ha : a ≤ n) : #{j : Fin n | (j : ℕ) < a} = a := by
  rw [Fin.card_filter_val_lt]
  omega

/- English proof (translation)
Rewrite using `[← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not]`.
-/
theorem card_split (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | P j ∧ ¬ Q j} = #{j : Fin n | P j} := by
  rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not]

/- English proof (translation)
Rewrite using `[← card_split Q P]`. Simplify using `only [and_comm]`.
-/
theorem card_split' (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | ¬ P j ∧ Q j} = #{j : Fin n | Q j} := by
  rw [← card_split Q P]
  simp only [and_comm]

/- English proof (translation)
Rewrite using `[Finset.card_filter_add_card_filter_not]`. Simplify using the standard rewrite rules.
-/
theorem card_not (P : Fin n → Prop) [DecidablePred P] :
    #{j : Fin n | P j} + #{j : Fin n | ¬ P j} = n := by
  rw [Finset.card_filter_add_card_filter_not]
  simp

/- English proof (translation)
Set `f : Equiv.Perm (Fin n) → Fin n → Bool × Bool` to `fun τ j => (decide ((j : ℕ) < a), decide ((τ j : ℕ) < c))`. Establish `hcard : ∀ y, Fintype.card {j // f σ j = y} = Fintype.card {j // f s j = y}`. Establish `e1` using `card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`. Establish `e2` using `card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)`. Establish `e3` using `card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`.

Establish `e4` using `card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)`. Establish `e5` using `card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`. Establish `e6` using `card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (s j : ℕ) < c)`. Rewrite `e3`, `e4` using `[card_lt hc]`. Introduce and unpack `⟨y₁, y₂⟩`.

Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Apply the tactic sequence `cases y₁ <;> cases y₂ <;>`. Apply the tactic sequence `simp only [f, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega`. Set `t₂ : Equiv.Perm (Fin n)` to `Equiv.ofFiberEquiv fun y => Fintype.equivOfCardEq (hcard y)`. Establish `ht : ∀ j, f s (t₂ j) = f σ j` using `fun j => Equiv.ofFiberEquiv_map _ j`.

Use `⟨σ * t₂⁻¹ * s⁻¹, t₂, fun j => ?_, fun j => ?_, by group⟩` and prove the remaining obligations. Use `congrArg Prod.snd (ht (t₂⁻¹ (s⁻¹ j)))` as an intermediate fact. Simplify `this.symm` using `[f]`. Use `congrArg Prod.fst (ht j)` as an intermediate fact. Simplify `this` using `[f]`.
-/
theorem exists_young {a c : ℕ} (ha : a ≤ n) (hc : c ≤ n) (σ s : Equiv.Perm (Fin n))
    (h : #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} = #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c}) :
    ∃ t₁ t₂ : Equiv.Perm (Fin n), (∀ j, (t₁ j : ℕ) < c ↔ (j : ℕ) < c) ∧ (∀ j, (t₂ j : ℕ) < a ↔ (j : ℕ) < a) ∧
      σ = t₁ * s * t₂ := by
  let f : Equiv.Perm (Fin n) → Fin n → Bool × Bool := fun τ j => (decide ((j : ℕ) < a), decide ((τ j : ℕ) < c))
  have hcard : ∀ y, Fintype.card {j // f σ j = y} = Fintype.card {j // f s j = y} := by
    have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e2 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e4 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e6 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    rw [card_lt hc] at e3 e4
    rintro ⟨y₁, y₂⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases y₁ <;> cases y₂ <;>
      simp only [f, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  let t₂ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun y => Fintype.equivOfCardEq (hcard y)
  have ht : ∀ j, f s (t₂ j) = f σ j := fun j => Equiv.ofFiberEquiv_map _ j
  refine ⟨σ * t₂⁻¹ * s⁻¹, t₂, fun j => ?_, fun j => ?_, by group⟩
  · have := congrArg Prod.snd (ht (t₂⁻¹ (s⁻¹ j)))
    simpa [f] using this.symm
  · have := congrArg Prod.fst (ht j)
    simpa [f] using this

/- English proof (translation)
Set `f : Fin n → Fin n` to `fun j => ⟨sigI a c i j, by`. Use `j.2` as an intermediate fact. Unfold `sigI`. Apply the tactic sequence `split_ifs <;> omega⟩`. Establish `hf : Function.Injective f`.

Introduce `j k h`. Establish `h' : sigI a c i j = sigI a c i k` using `congrArg Fin.val h`. Apply `Fin.ext` to reduce the goal to its premises. Unfold `sigI at h'`. Apply the tactic sequence `split_ifs at h' <;> omega`.

Set `s : Equiv.Perm (Fin n)` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)`. Establish `hs : ∀ j, (s j : ℕ) = sigI a c i j` using `fun _ => rfl`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun r j : Fin n => if (r : ℕ) = sigI a c i j then (1 : ZMod g) else 0) = ((pU g s : Gn g n) : Mt g n)`. Use function extensionality and compare the values at `r j`.

Simplify using `only [pU, pMat, ← hs, Fin.val_inj]`. Unfold `wI toG`. Rewrite using `[e, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]`. Establish `e1` using `card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)`. Establish `e2 : #{j : Fin n | (j : ℕ) < a ∧ (s j : ℕ) < c} = #{j : Fin n | (j : ℕ) < i}`.

Use `congr 1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hs, sigI]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `e3` using `card_lt' (a := a) (n := n) (by omega)`.

Establish `e4` using `card_lt' (a := i) (n := n) (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_shuffle {a b c i : ℕ} (hn : n = a + b) (hia : i ≤ a) (hic : i ≤ c) (hb : c - i ≤ b) :
    ∃ s : Equiv.Perm (Fin n), wI g a c i n = pU g s ∧
      #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c} = a - i := by
  let f : Fin n → Fin n := fun j => ⟨sigI a c i j, by
    have := j.2
    unfold sigI
    split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro j k h
    have h' : sigI a c i j = sigI a c i k := congrArg Fin.val h
    apply Fin.ext
    unfold sigI at h'
    split_ifs at h' <;> omega
  let s : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hs : ∀ j, (s j : ℕ) = sigI a c i j := fun _ => rfl
  refine ⟨s, ?_, ?_⟩
  · have e : (fun r j : Fin n => if (r : ℕ) = sigI a c i j then (1 : ZMod g) else 0) =
        ((pU g s : Gn g n) : Mt g n) := by
      funext r j
      simp only [pU, pMat, ← hs, Fin.val_inj]
    unfold wI toG
    rw [e, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e2 : #{j : Fin n | (j : ℕ) < a ∧ (s j : ℕ) < c} = #{j : Fin n | (j : ℕ) < i} := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs, sigI]
      split_ifs <;> omega
    have e3 := card_lt' (a := a) (n := n) (by omega)
    have e4 := card_lt' (a := i) (n := n) (by omega)
    omega

/- English proof (translation)
Take `⟨m, u, hu, u', hu', h⟩` from `Bruhat.exists_decomp x`. Establish `hup : ∀ (e : ℕ) (v : Gn g n), v ∈ unip (ZMod g) n → InPar e (v : Mt g n)` using `fun e v hv i j hj hi => unip_lower hv (show j < i from Fin.lt_def.2 (by omega))`. Set `D : Gn g n` to `⟨Matrix.diagonal fun j => (m.2 j : ZMod g), Matrix.diagonal fun j => ((m.2 j)⁻¹ : (ZMod g)ˣ), by simp only [Matrix.diagonal_mul_diagonal, Units.mul_inv, Matrix.diagonal_one], by simp only [Matrix.diagonal_mul_diagonal, Units.inv_mul, Matrix.diagonal_one]⟩`. Establish `hD : InPar a (D : Mt g n)` using `fun i j hj hi => Matrix.diagonal_apply_ne _ (by rintro rfl; omega)`. Use `⟨m.1, u, D * u', hup c u hu, inPar_mul hD (hup a u' hu'), Units.ext ?_⟩` and prove the remaining obligations.

Establish `e : Bruhat.mono m = ((pU g m.1 : Gn g n) : Mt g n) * (D : Mt g n)`. Use extensionality with `r j`. Simplify using `[Bruhat.mono, pU, pMat, D, Matrix.mul_diagonal]`. Rewrite using `[h, e]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`.
-/
theorem exists_perm (a c : ℕ) (x : Gn g n) : ∃ σ : Equiv.Perm (Fin n), ∃ p q : Gn g n,
    InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * pU g σ * q := by
  obtain ⟨m, u, hu, u', hu', h⟩ := Bruhat.exists_decomp x
  have hup : ∀ (e : ℕ) (v : Gn g n), v ∈ unip (ZMod g) n → InPar e (v : Mt g n) := fun e v hv i j hj hi =>
    unip_lower hv (show j < i from Fin.lt_def.2 (by omega))
  let D : Gn g n := ⟨Matrix.diagonal fun j => (m.2 j : ZMod g), Matrix.diagonal fun j => ((m.2 j)⁻¹ : (ZMod g)ˣ),
    by simp only [Matrix.diagonal_mul_diagonal, Units.mul_inv, Matrix.diagonal_one],
    by simp only [Matrix.diagonal_mul_diagonal, Units.inv_mul, Matrix.diagonal_one]⟩
  have hD : InPar a (D : Mt g n) := fun i j hj hi =>
    Matrix.diagonal_apply_ne _ (by rintro rfl; omega)
  refine ⟨m.1, u, D * u', hup c u hu, inPar_mul hD (hup a u' hu'), Units.ext ?_⟩
  have e : Bruhat.mono m = ((pU g m.1 : Gn g n) : Mt g n) * (D : Mt g n) := by
    ext r j
    simp [Bruhat.mono, pU, pMat, D, Matrix.mul_diagonal]
  rw [h, e]
  simp only [Units.val_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `g _ a b c d n hab hcd x`. Establish `key : ∀ i : ℕ, (i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n, InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q) → i = a - rk a c (x : Mt g n)`. Introduce and unpack `i ⟨hi, p, q, hp, hq, rfl⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hi`. Take `⟨s, hs, hc⟩` from `exists_shuffle (g := g) hab (by omega : i ≤ a) hi.2.1 hi.2.2`.

Rewrite using `[rk_eq hp hq, hs, rk_pU, hc]`. Use linear arithmetic over natural numbers and integers. Use `existsUnique_of_exists_of_unique ?_ fun i j hi hj => (key i hi).trans (key j hj).symm` and prove the remaining obligations. Take `⟨σ, p, q, hp, hq, rfl⟩` from `exists_perm a c x`. Establish `e1` using `card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`.

Establish `e3` using `card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`. Establish `e5` using `card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)`. Establish `e6` using `card_not (fun j : Fin n => (j : ℕ) < a)`. Establish `e7` using `card_lt' (a := a) (n := n) (by omega)`. Rewrite `e3` using `[card_lt (by omega)]`.

Take `⟨i, hi⟩ : ∃ i, i = #{j : Fin n | (j : ℕ) < a ∧ (σ j : ℕ) < c}` from `⟨_, rfl⟩`. Take `⟨s, hs, hc⟩` from `exists_shuffle (g := g) (i := i) (c := c) hab (by omega) (by omega) (by omega)`. Take `⟨t₁, t₂, h₁, h₂, ht⟩` from `exists_young (a := a) (c := c) (by omega) (by omega) σ s (by omega)`. Use `⟨i, ?_, p * pU g t₁, pU g t₂ * q, inPar_mul hp (inPar_pU h₁), inPar_mul (inPar_pU h₂) hq, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_range]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hs, ht, pU_mul, pU_mul] group`.
-/
theorem doubleCoset : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ x : Gn g n, ∃! i : ℕ, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n, InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q := by
  intro g _ a b c d n hab hcd x
  have key : ∀ i : ℕ, (i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n,
      InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q) →
      i = a - rk a c (x : Mt g n) := by
    rintro i ⟨hi, p, q, hp, hq, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) hab (by omega : i ≤ a) hi.2.1 hi.2.2
    rw [rk_eq hp hq, hs, rk_pU, hc]
    omega
  refine existsUnique_of_exists_of_unique ?_ fun i j hi hj => (key i hi).trans (key j hj).symm
  obtain ⟨σ, p, q, hp, hq, rfl⟩ := exists_perm a c x
  have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e6 := card_not (fun j : Fin n => (j : ℕ) < a)
  have e7 := card_lt' (a := a) (n := n) (by omega)
  rw [card_lt (by omega)] at e3
  obtain ⟨i, hi⟩ : ∃ i, i = #{j : Fin n | (j : ℕ) < a ∧ (σ j : ℕ) < c} := ⟨_, rfl⟩
  obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) (i := i) (c := c) hab (by omega) (by omega) (by omega)
  obtain ⟨t₁, t₂, h₁, h₂, ht⟩ := exists_young (a := a) (c := c) (by omega) (by omega) σ s (by omega)
  refine ⟨i, ?_, p * pU g t₁, pU g t₂ * q, inPar_mul hp (inPar_pU h₁), inPar_mul (inPar_pU h₂) hq, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [hs, ht, pU_mul, pU_mul]
    group

end GlobalTheory.GLm.ParCoset
