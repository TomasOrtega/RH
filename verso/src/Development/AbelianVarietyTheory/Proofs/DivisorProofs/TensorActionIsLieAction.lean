import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.TLie

variable {R S : ℕ}

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `y`. Take `⟨⟨c, d⟩, h'⟩` from `x`. Simplify using `only [adP, eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single c]`.

Distinguish the cases in `hbd : b = d`. Simplify using `[hbd]`. Simplify using `[hbd, Ne.symm hbd]`. Introduce `j _ hj`. Simplify using `[Ne.symm hj]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single d]`. Distinguish the cases in `hac : a = c`. Simplify using `[hac]`. Simplify using `[hac, Ne.symm hac]`.

Introduce `j _ hj`. Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
lemma adCoeff_eq (Z : Mat R S) (y x : NC R S) :
    adP Z y x = (Z * eNC x - eNC x * Z) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  obtain ⟨⟨c, d⟩, h'⟩ := x
  simp only [adP, eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [Finset.sum_eq_single c]
    · by_cases hbd : b = d
      · simp [hbd]
      · simp [hbd, Ne.symm hbd]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [Finset.sum_eq_single d]
    · by_cases hac : a = c
      · simp [hac]
      · simp [hac, Ne.symm hac]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> cases c <;> first | trivial | exact h1.elim | exact h2.elim`.
-/
lemma same_trans {a b c : Ix R S} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> first | trivial | exact h1.elim | exact h2.elim

/- English proof (translation)
Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun p : Ix R S × Ix R S => ¬ sameBlock p.1 p.2) (fun p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)) f]`. Conclude with `Finset.sum_filter_of_ne fun p _ hp hs => hp (hf p hs)`.
-/
lemma sum_NC (f : Ix R S × Ix R S → ℂ) (hf : ∀ p, sameBlock p.1 p.2 → f p = 0) :
    ∑ x : NC R S, f x.1 = ∑ p, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Ix R S × Ix R S => ¬ sameBlock p.1 p.2)
    (fun p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)) f]
  exact Finset.sum_filter_of_ne fun p _ hp hs => hp (hf p hs)

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_comm]`.

Simplify using `[mul_comm]`.
-/
lemma sum_all {ι : Type} [Fintype ι] [DecidableEq ι] (Y M : Matrix ι ι ℂ) (a b : ι) :
    ∑ p : ι × ι, (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2 =
      (Y * M - M * Y) a b := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp [mul_comm]

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `y`. Use `Eq.trans ?_ (sum_all Y M a b)` and prove the remaining obligations. Use `sum_NC (fun p => (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2) ?_` and prove the remaining obligations. Introduce and unpack `⟨c, d⟩ hs`. Establish `e1 : Y a c * (if b = d then 1 else 0) = 0` using `by split_ifs with hbd`.

Substitute `hbd` using the available equality. Rewrite using `[hY a c (fun hac => h (same_trans hac hs)), zero_mul]`. Conclude with `mul_zero _`. Establish `e2 : (if a = c then 1 else 0) * Y d b = 0` using `by split_ifs with hac`. Substitute `hac` using the available equality.

Rewrite using `[hY d b (fun hdb => h (same_trans hs hdb)), mul_zero]`. Conclude with `zero_mul _`. Simplify using `only [e1, e2, sub_zero, zero_mul]`.
-/
lemma sum_adP {Y : Mat R S} (hY : IsKC Y) (M : Mat R S) (y : NC R S) :
    ∑ x : NC R S, adP Y y x * M x.1.1 x.1.2 = (Y * M - M * Y) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  refine Eq.trans ?_ (sum_all Y M a b)
  refine sum_NC (fun p =>
    (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2) ?_
  rintro ⟨c, d⟩ hs
  have e1 : Y a c * (if b = d then 1 else 0) = 0 := by
    split_ifs with hbd
    · subst hbd
      rw [hY a c (fun hac => h (same_trans hac hs)), zero_mul]
    · exact mul_zero _
  have e2 : (if a = c then 1 else 0) * Y d b = 0 := by
    split_ifs with hac
    · subst hac
      rw [hY d b (fun hdb => h (same_trans hs hdb)), mul_zero]
    · exact zero_mul _
  simp only [e1, e2, sub_zero, zero_mul]

/- English proof (translation)
Establish `h1` using `sum_adP hY (Z * eNC w - eNC w * Z) y`. Establish `h2` using `sum_adP hZ (Y * eNC w - eNC w * Y) y`. Simplify using `only [← adCoeff_eq] at h1 h2`. Rewrite using `[h1, h2, adCoeff_eq, ← Matrix.sub_apply]`. Use `congrFun (congrFun ?_ _) _` and prove the remaining obligations.

Simplify using `only [mul_sub, sub_mul, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
lemma adCoeff_commutator {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) (y w : NC R S) :
    adP (Y * Z - Z * Y) y w = ∑ x, adP Y y x * adP Z x w - ∑ x, adP Z y x * adP Y x w := by
  have h1 := sum_adP hY (Z * eNC w - eNC w * Z) y
  have h2 := sum_adP hZ (Y * eNC w - eNC w * Y) y
  simp only [← adCoeff_eq] at h1 h2
  rw [h1, h2, adCoeff_eq, ← Matrix.sub_apply]
  refine congrFun (congrFun ?_ _) _
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma factorOp_apply (k : ℕ) (i : Fin k) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    factorOp k i Z Ψ g = ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := rfl

/- English proof (translation)
Use `LinearMap.ext fun Ψ => funext fun g => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, factorOp_apply, Function.update_self, Function.update_idem, adCoeff_commutator hY hZ, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Apply the tactic sequence `congr 1 <;> exact Finset.sum_comm`.
-/
lemma factorOp_commutator (k : ℕ) (i : Fin k) {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) :
    (factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k i Y * factorOp k i Z - factorOp k i Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, factorOp_apply,
    Function.update_self, Function.update_idem, adCoeff_commutator hY hZ, sub_smul, Finset.sum_sub_distrib,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  congr 1 <;> exact Finset.sum_comm

/- English proof (translation)
Use `LinearMap.ext fun Ψ => funext fun g => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, factorOp_apply, Function.update_of_ne hij, Function.update_of_ne hij.symm, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, Function.update_comm hij]`.
-/
lemma factorOp_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (Y Z : Mat R S) :
    (factorOp k i Y * factorOp k j Z : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k j Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [Module.End.mul_apply, factorOp_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, Function.update_comm hij]

def ptOp (k : ℕ) (A : Module.End ℂ W) : Module.End ℂ ((Fin k → NC R S) → W) :=
  LinearMap.pi (fun g => A ∘ₗ LinearMap.proj g)

/- English proof (translation)
Use `LinearMap.ext fun Ψ => funext fun g => ?_` and prove the remaining obligations. Simplify using `[ptOp, factorOp_apply]`.
-/
lemma ptOp_comm_factorOp (k : ℕ) (i : Fin k) (A : Module.End ℂ W) (Z : Mat R S) :
    (ptOp k A * factorOp k i Z : Module.End ℂ ((Fin k → NC R S) → W)) = factorOp k i Z * ptOp k A := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp [ptOp, factorOp_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma tAct_eq (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) :
    tAct k actW Z = ptOp k (actW Z) + ∑ i, factorOp k i Z := rfl

/- English proof (translation)
Introduce `Y Z hY hZ`. Establish `hp : (ptOp k (actW (Y * Z - Z * Y)) : Module.End ℂ ((Fin k → NC R S) → W)) = ptOp k (actW Y) * ptOp k (actW Z) - ptOp k (actW Z) * ptOp k (actW Y)`. Rewrite using `[h Y Z hY hZ]`. Use `LinearMap.ext fun Ψ => funext fun g => ?_` and prove the remaining obligations. Simplify using `[ptOp]`.

Establish `hs : (∑ i, factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) = (∑ i, factorOp k i Y) * (∑ i, factorOp k i Z) - (∑ i, factorOp k i Z) * (∑ i, factorOp k i Y)`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun i j => (factorOp k i Z * factorOp k j Y : Module.End ℂ ((Fin k → NC R S) → W))), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single i, factorOp_commutator k i hY hZ]`. Introduce `j _ hj`.

Rewrite using `[factorOp_comm_of_ne k hj.symm, sub_self]`. Simplify using the standard rewrite rules. Establish `hc : ∀ (A : Module.End ℂ W) (X : Mat R S), (ptOp k A * (∑ i, factorOp k i X) : Module.End ℂ ((Fin k → NC R S) → W)) = (∑ i, factorOp k i X) * ptOp k A`. Introduce `A X`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => ptOp_comm_factorOp k i A X`. Rewrite using `[tAct_eq, tAct_eq, tAct_eq, hp, hs]`. Simplify using `only [add_mul, mul_add, hc]`. Normalize the expressions using the abelian group laws.
-/
theorem isKLieAct_tAct (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (h : IsKLieAct actW) : IsKLieAct (tAct k actW) := by
  intro Y Z hY hZ
  have hp : (ptOp k (actW (Y * Z - Z * Y)) : Module.End ℂ ((Fin k → NC R S) → W)) =
      ptOp k (actW Y) * ptOp k (actW Z) - ptOp k (actW Z) * ptOp k (actW Y) := by
    rw [h Y Z hY hZ]
    refine LinearMap.ext fun Ψ => funext fun g => ?_
    simp [ptOp]
  have hs : (∑ i, factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      (∑ i, factorOp k i Y) * (∑ i, factorOp k i Z) - (∑ i, factorOp k i Z) * (∑ i, factorOp k i Y) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun i j => (factorOp k i Z * factorOp k j Y :
        Module.End ℂ ((Fin k → NC R S) → W))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, factorOp_commutator k i hY hZ]
    · intro j _ hj
      rw [factorOp_comm_of_ne k hj.symm, sub_self]
    · simp
  have hc : ∀ (A : Module.End ℂ W) (X : Mat R S),
      (ptOp k A * (∑ i, factorOp k i X) : Module.End ℂ ((Fin k → NC R S) → W)) =
        (∑ i, factorOp k i X) * ptOp k A := by
    intro A X
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => ptOp_comm_factorOp k i A X
  rw [tAct_eq, tAct_eq, tAct_eq, hp, hs]
  simp only [add_mul, mul_add, hc]
  abel

end GlobalTheory.SteepMult.TLie
