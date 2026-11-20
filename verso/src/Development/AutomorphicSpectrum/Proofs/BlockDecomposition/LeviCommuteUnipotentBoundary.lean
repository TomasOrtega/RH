import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CanonicalAnticommutationRelationsConsequence

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open Formalism.REAL (GlRel)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvComm

section RingId

variable {R : Type} [Ring R]

/- English proof (translation)
Establish `e1 : u * x = -(x * u)` using `eq_neg_of_add_eq_zero_left hu`. Establish `e2 : v * x = -(x * v)` using `eq_neg_of_add_eq_zero_left hv`. Use `show u * v * x = x * (u * v)`. Rewrite using `[mul_assoc, e2, mul_neg, ← mul_assoc, e1, neg_mul, neg_neg, mul_assoc]`.
-/
theorem anti_comm {u v x : R} (hu : u * x + x * u = 0) (hv : v * x + x * v = 0) :
    Commute (u * v) x := by
  have e1 : u * x = -(x * u) := eq_neg_of_add_eq_zero_left hu
  have e2 : v * x = -(x * v) := eq_neg_of_add_eq_zero_left hv
  show u * v * x = x * (u * v)
  rw [mul_assoc, e2, mul_neg, ← mul_assoc, e1, neg_mul, neg_neg, mul_assoc]

/- English proof (translation)
Establish `hXc : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (c' a b)` using `fun a b => (hLc p q a b).add_left (Commute.sub_left (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _)) (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _)))`. Establish `hXd : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (d' a b)` using `fun a b => (hLd p q a b).add_left (Commute.sub_left (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _)) (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _)))`. Establish `hXL : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (L' a b)` using `fun a b => (hLL p q a b).add_left (Commute.sub_left (Commute.sum_left _ _ _ fun r _ => ((hMd a b p r).symm).mul_left (hMc a b q r).symm) (Commute.sum_left _ _ _ fun r _ => ((hMd a b r q).symm).mul_left (hMc a b r p).symm))`. Conclude with `Commute.add_right (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (hXL a b).mul_right (hXc a b)) (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun e _ => ((hXd a e).mul_right (hXc b e)).mul_right (hXc a b))`.
-/
theorem cross {n : ℕ} {c d c' d' L L' : Fin n → Fin n → R} (p q : Fin n)
    (hcc : ∀ a b a' b', c a b * c' a' b' + c' a' b' * c a b = 0)
    (hcd : ∀ a b a' b', c a b * d' a' b' + d' a' b' * c a b = 0)
    (hdc : ∀ a b a' b', d a b * c' a' b' + c' a' b' * d a b = 0)
    (hdd : ∀ a b a' b', d a b * d' a' b' + d' a' b' * d a b = 0)
    (hLL : ∀ a b a' b', Commute (L a b) (L' a' b'))
    (hLc : ∀ a b a' b', Commute (L a b) (c' a' b'))
    (hLd : ∀ a b a' b', Commute (L a b) (d' a' b'))
    (hMc : ∀ a b a' b', Commute (L' a b) (c a' b'))
    (hMd : ∀ a b a' b', Commute (L' a b) (d a' b')) :
    Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p))
      ((∑ a, ∑ b, L' a b * c' a b) + ∑ a, ∑ b, ∑ e, d' a e * c' b e * c' a b) := by
  have hXc : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (c' a b) :=
    fun a b => (hLc p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _))
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _)))
  have hXd : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (d' a b) :=
    fun a b => (hLd p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _))
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _)))
  have hXL : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (L' a b) :=
    fun a b => (hLL p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => ((hMd a b p r).symm).mul_left (hMc a b q r).symm)
      (Commute.sum_left _ _ _ fun r _ => ((hMd a b r q).symm).mul_left (hMc a b r p).symm))
  exact Commute.add_right
    (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      (hXL a b).mul_right (hXc a b))
    (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      Commute.sum_right _ _ _ fun e _ => ((hXd a e).mul_right (hXc b e)).mul_right (hXc a b))

variable [Algebra ℂ R]

/- English proof (translation)
Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]`. Use `module`.
-/
theorem anti_comb (x0 x1 y0 y1 : R) (σ ρ : ℂ) :
    (x0 + σ • x1) * (y0 + ρ • y1) + (y0 + ρ • y1) * (x0 + σ • x1)
      = (x0 * y0 + y0 * x0) + ρ • (x0 * y1 + y1 * x0) + σ • (x1 * y0 + y0 * x1)
        + (σ * ρ) • (x1 * y1 + y1 * x1) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  module

/- English proof (translation)
Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]`. Use `module`.
-/
theorem half_three (z0 z1 y0 y1 x0 x1 : R) :
    ((1 / 2 : ℂ) • (z0 + (1 : ℂ) • z1)) * (y0 + (1 : ℂ) • y1) * (x0 + (1 : ℂ) • x1)
      + ((1 / 2 : ℂ) • (z0 + (-1 : ℂ) • z1)) * (y0 + (-1 : ℂ) • y1) * (x0 + (-1 : ℂ) • x1)
      = z0 * y1 * x1 + z1 * y0 * x1 + (z1 * y1 * x0 + z0 * y0 * x0) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]
  module

/- English proof (translation)
Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]`. Use `module`.
-/
theorem half_two (z0 z1 y0 y1 : R) :
    ((1 / 2 : ℂ) • (z0 + (1 : ℂ) • z1)) * (y0 + (1 : ℂ) • y1)
      + ((1 / 2 : ℂ) • (z0 + (-1 : ℂ) • z1)) * (y0 + (-1 : ℂ) • y1)
      = z1 * y1 + z0 * y0 := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]
  module

end RingId

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type' (f := g), ← Finset.sum_filter_of_ne (s := univ) (f := fun y : Fin n × Fin n => g y.1 y.2) (p := fun y => y.1 < y.2) (fun y _ hy => by_contra fun t => hy (h _ _ t))]`. Conclude with `Finset.sum_subtype _ (by simp) _`.
-/
theorem sum_pos' {n : ℕ} {M : Type*} [AddCommMonoid M] (g : Fin n → Fin n → M) (h : ∀ a b, ¬a < b → g a b = 0) :
    ∑ a, ∑ b, g a b = ∑ i : Pos n, g i.1.1 i.1.2 := by
  rw [← Fintype.sum_prod_type' (f := g),
    ← Finset.sum_filter_of_ne (s := univ) (f := fun y : Fin n × Fin n => g y.1 y.2) (p := fun y => y.1 < y.2)
      (fun y _ hy => by_contra fun t => hy (h _ _ t))]
  exact Finset.sum_subtype _ (by simp) _

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Conclude with `sum_congr rfl fun s _ => (sum_pos' (F s) (h s)).symm`.
-/
theorem sum_lt {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Bool → Fin n → Fin n → M)
    (h : ∀ s a b, ¬a < b → F s a b = 0) :
    ∑ l : Lt n, F l.1 l.2.1.1 l.2.1.2 = ∑ s, ∑ a, ∑ b, F s a b := by
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun s _ => (sum_pos' (F s) (h s)).symm

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev tau (lev : Fin n → ℕ) (a b : Fin n) : Prop := a < b ∧ lev a < lev b

def cT (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : tau lev a b then annL (s, ⟨(a, b), h.1⟩) else 0

def dT (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : tau lev a b then creL (s, ⟨(a, b), h.1⟩) else 0

def cE (lev : Fin n → ℕ) (σ : ℂ) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  cT lev false a b + σ • cT lev true a b

def dE (lev : Fin n → ℕ) (σ : ℂ) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (dT lev false a b + σ • dT lev true a b)

abbrev LT (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ (Cq n V) := liftL n (E a b)

def Dd (lev : Fin n → ℕ) (σ : ℂ) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ a, ∑ b, LT E a b * cE lev σ a b) + ∑ a, ∑ b, ∑ e, dE lev σ a e * cE lev σ b e * cE lev σ a b

def Aa (lev : Fin n → ℕ) (σ : ℂ) (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  LT E p q + (∑ r, dE lev σ p r * cE lev σ q r - ∑ r, dE lev σ r q * cE lev σ r p)

variable {lev : Fin n → ℕ}

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem cT_pos {s : Bool} {a b : Fin n} (h : tau lev a b) :
    (cT lev s a b : Module.End ℂ (Cq n V)) = annL (s, ⟨(a, b), h.1⟩) := dif_pos h

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem dT_pos {s : Bool} {a b : Fin n} (h : tau lev a b) :
    (dT lev s a b : Module.End ℂ (Cq n V)) = creL (s, ⟨(a, b), h.1⟩) := dif_pos h

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
theorem cT_neg {s : Bool} {a b : Fin n} (h : ¬tau lev a b) :
    (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := dif_neg h

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
theorem dT_neg {s : Bool} {a b : Fin n} (h : ¬tau lev a b) :
    (dT lev s a b : Module.End ℂ (Cq n V)) = 0 := dif_neg h

/- English proof (translation)
Distinguish the cases in `h : tau lev a b`. Distinguish the cases in `h' : tau lev a' b'`. Rewrite using `[cT_pos h, cT_pos h']`. Conclude with `annL_annL _ _`. Rewrite using `[cT_neg h']`.

Simplify using the standard rewrite rules. Rewrite using `[cT_neg h]`. Simplify using the standard rewrite rules.
-/
theorem cT_cT (s t : Bool) (a b a' b' : Fin n) :
    (cT lev s a b * cT lev t a' b' + cT lev t a' b' * cT lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [cT_pos h, cT_pos h']; exact annL_annL _ _
    · rw [cT_neg h']; simp
  · rw [cT_neg h]; simp

/- English proof (translation)
Distinguish the cases in `h : tau lev a b`. Distinguish the cases in `h' : tau lev a' b'`. Rewrite using `[dT_pos h, dT_pos h']`. Conclude with `creL_creL _ _`. Rewrite using `[dT_neg h']`.

Simplify using the standard rewrite rules. Rewrite using `[dT_neg h]`. Simplify using the standard rewrite rules.
-/
theorem dT_dT (s t : Bool) (a b a' b' : Fin n) :
    (dT lev s a b * dT lev t a' b' + dT lev t a' b' * dT lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [dT_pos h, dT_pos h']; exact creL_creL _ _
    · rw [dT_neg h']; simp
  · rw [dT_neg h]; simp

/- English proof (translation)
Distinguish the cases in `h : tau lev a b`. Distinguish the cases in `h' : tau lev a' b'`. Rewrite using `[cT_pos h, dT_pos h', annL_creL]`. Distinguish the cases in `e : s = t ∧ a = a' ∧ b = b'`. Take `⟨rfl, rfl, rfl⟩` from `e`.

Simplify using `[h]`. Rewrite using `[if_neg, if_neg]`. Conclude with `fun t => e ⟨t.1, t.2.1, t.2.2.1⟩`. Introduce `t`. Simplify using `only [Prod.mk.injEq, Subtype.mk.injEq] at t`.

Conclude with `e t`. Rewrite using `[dT_neg h', if_neg]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨-, rfl, rfl, t⟩`. Conclude with `h' t`.

Rewrite using `[cT_neg h, if_neg (fun t => h t.2.2.2)]`. Simplify using the standard rewrite rules.
-/
theorem cT_dT (s t : Bool) (a b a' b' : Fin n) :
    (cT lev s a b * dT lev t a' b' + dT lev t a' b' * cT lev s a b : Module.End ℂ (Cq n V))
      = if s = t ∧ a = a' ∧ b = b' ∧ tau lev a b then 1 else 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [cT_pos h, dT_pos h', annL_creL]
      by_cases e : s = t ∧ a = a' ∧ b = b'
      · obtain ⟨rfl, rfl, rfl⟩ := e
        simp [h]
      · rw [if_neg, if_neg]
        · exact fun t => e ⟨t.1, t.2.1, t.2.2.1⟩
        · intro t
          simp only [Prod.mk.injEq, Subtype.mk.injEq] at t
          exact e t
    · rw [dT_neg h', if_neg]
      · simp
      · rintro ⟨-, rfl, rfl, t⟩
        exact h' t
  · rw [cT_neg h, if_neg (fun t => h t.2.2.2)]; simp

/- English proof (translation)
Simplify using `only [cE]`. Rewrite using `[anti_comb, cT_cT, cT_cT, cT_cT, cT_cT]`. Simplify using the standard rewrite rules.
-/
theorem cE_cE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (cE lev σ a b * cE lev ρ a' b' + cE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [cE]
  rw [anti_comb, cT_cT, cT_cT, cT_cT, cT_cT]
  simp

/- English proof (translation)
Simplify using `only [dE, smul_mul_assoc, mul_smul_comm, ← smul_add]`. Rewrite using `[anti_comb, dT_dT, dT_dT, dT_dT, dT_dT]`. Simplify using the standard rewrite rules.
-/
theorem dE_dE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (dE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * dE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [dE, smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [anti_comb, dT_dT, dT_dT, dT_dT, dT_dT]
  simp

/- English proof (translation)
Simplify using `only [cE, dE, smul_mul_assoc, mul_smul_comm, ← smul_add]`. Rewrite using `[anti_comb, cT_dT, cT_dT, cT_dT, cT_dT]`. Simplify using `only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, if_false, smul_zero, add_zero, ite_false]`. Use `module`.
-/
theorem cE_dE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (cE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V))
      = ((1 + σ * ρ) / 2) • (if a = a' ∧ b = b' ∧ tau lev a b then 1 else 0) := by
  simp only [cE, dE, smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [anti_comb, cT_dT, cT_dT, cT_dT, cT_dT]
  simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, if_false, smul_zero, add_zero,
    ite_false]
  module

/- English proof (translation)
Distinguish the cases in `h : tau lev a' b'`. Rewrite using `[cT_pos h]`. Conclude with `liftL_annL _ _`. Rewrite using `[cT_neg h]`. Conclude with `Commute.zero_right _`.
-/
theorem LT_cT (E : Fin n → Fin n → Module.End ℂ V) (a b a' b' : Fin n) (s : Bool) :
    Commute (LT E a b) (cT lev s a' b') := by
  by_cases h : tau lev a' b'
  · rw [cT_pos h]; exact liftL_annL _ _
  · rw [cT_neg h]; exact Commute.zero_right _

/- English proof (translation)
Distinguish the cases in `h : tau lev a' b'`. Rewrite using `[dT_pos h]`. Conclude with `liftL_creL _ _`. Rewrite using `[dT_neg h]`. Conclude with `Commute.zero_right _`.
-/
theorem LT_dT (E : Fin n → Fin n → Module.End ℂ V) (a b a' b' : Fin n) (s : Bool) :
    Commute (LT E a b) (dT lev s a' b') := by
  by_cases h : tau lev a' b'
  · rw [dT_pos h]; exact liftL_creL _ _
  · rw [dT_neg h]; exact Commute.zero_right _

/- English proof (translation)
The claim follows from `(LT_cT E a b a' b' false).add_right ((LT_cT E a b a' b' true).smul_right σ)`.
-/
theorem LT_cE (E : Fin n → Fin n → Module.End ℂ V) (σ : ℂ) (a b a' b' : Fin n) :
    Commute (LT E a b) (cE lev σ a' b') :=
  (LT_cT E a b a' b' false).add_right ((LT_cT E a b a' b' true).smul_right σ)

/- English proof (translation)
The claim follows from `((LT_dT E a b a' b' false).add_right ((LT_dT E a b a' b' true).smul_right σ)).smul_right _`.
-/
theorem LT_dE (E : Fin n → Fin n → Module.End ℂ V) (σ : ℂ) (a b a' b' : Fin n) :
    Commute (LT E a b) (dE lev σ a' b') :=
  ((LT_dT E a b a' b' false).add_right ((LT_dT E a b a' b' true).smul_right σ)).smul_right _

/- English proof (translation)
Use `LinearMap.ext fun y => funext fun A => ?_` and prove the remaining obligations. Establish `e` using `LinearMap.congr_fun (hE p q a b) (y A)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at e`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, liftL_apply]`. Rewrite using `[e]`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem glRel_LT {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (p q a b : Fin n) :
    LT E p q * LT E a b - LT E a b * LT E p q =
      (if q = a then LT E p b else 0) - (if b = p then LT E a q else 0) := by
  refine LinearMap.ext fun y => funext fun A => ?_
  have e := LinearMap.congr_fun (hE p q a b) (y A)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, liftL_apply]
  rw [e]
  split_ifs <;> rfl

/- English proof (translation)
Use `LinearMap.ext fun y => funext fun A => ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (h a b c d) (y A)`.
-/
theorem LT_LT {E E' : Fin n → Fin n → Module.End ℂ V} (h : ∀ a b c d, E a b * E' c d = E' c d * E a b)
    (a b c d : Fin n) : Commute (LT E a b) (LT E' c d) := by
  refine LinearMap.ext fun y => funext fun A => ?_
  exact LinearMap.congr_fun (h a b c d) (y A)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩, fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩`.
-/
theorem tau_left (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (b : Fin n) :
    tau lev p b ↔ tau lev q b :=
  ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩,
    fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩, fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩`.
-/
theorem tau_right (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (a : Fin n) :
    tau lev a p ↔ tau lev a q :=
  ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩,
    fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac n (Module.End ℂ (Cq n V)) (tau lev) (cE lev σ) (dE lev σ) (LT E) p q (fun a b a' b' => cE_cE σ σ a b a' b') (fun a b a' b' => dE_dE σ σ a b a' b') (fun a b a' b' => by rw [cE_dE, hσ] have : ((1 + 1) / 2 : ℂ) = 1 := …`.
-/
theorem comm_same (hm : Monotone lev) {σ : ℂ} (hσ : σ * σ = 1) {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {p q : Fin n} (hpq : lev p = lev q) :
    Commute (Aa lev σ E p q) (Dd lev σ E) :=
  GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac n (Module.End ℂ (Cq n V)) (tau lev)
    (cE lev σ) (dE lev σ) (LT E) p q
    (fun a b a' b' => cE_cE σ σ a b a' b') (fun a b a' b' => dE_dE σ σ a b a' b')
    (fun a b a' b' => by
      rw [cE_dE, hσ]
      have : ((1 + 1) / 2 : ℂ) = 1 := by norm_num
      rw [this, one_smul])
    (fun a b h => by simp only [cE, cT_neg h, smul_zero, add_zero])
    (fun a b h => by simp only [dE, dT_neg h, smul_zero, add_zero])
    (tau_left hm hpq) (tau_right hm hpq)
    (fun a b a' b' => LT_cE E σ a b a' b') (fun a b a' b' => LT_dE E σ a b a' b')
    (fun a b => glRel_LT hE p q a b)

/- English proof (translation)
Establish `hz : ∀ {σ ρ : ℂ}, σ * ρ = -1 → ∀ a b a' b', (cE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V)) = 0`. Introduce `σ ρ hs a b a' b'`. Rewrite using `[cE_dE, hs]`. Simplify using the standard rewrite rules. Establish `hz' : σ * ρ = -1 → ρ * σ = -1` using `fun e => by rw [mul_comm]; exact e`.

Conclude with `cross p q (fun a b a' b' => cE_cE σ ρ a b a' b') (hz hσ) (fun a b a' b' => by rw [add_comm]; exact hz (hz' hσ) a' b' a b) (fun a b a' b' => dE_dE σ ρ a b a' b') (LT_LT h) (fun a b a' b' => LT_cE E ρ a b a' b') (fun a b a' b' => LT_dE E ρ a b a' b') (fun a b a' b' => LT_cE E' σ a …`.
-/
theorem comm_cross {σ ρ : ℂ} (hσ : σ * ρ = -1) {E E' : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b c d, E a b * E' c d = E' c d * E a b) (p q : Fin n) :
    Commute (Aa lev σ E p q) (Dd lev ρ E') := by
  have hz : ∀ {σ ρ : ℂ}, σ * ρ = -1 → ∀ a b a' b',
      (cE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
    intro σ ρ hs a b a' b'
    rw [cE_dE, hs]
    simp
  have hz' : σ * ρ = -1 → ρ * σ = -1 := fun e => by rw [mul_comm]; exact e
  exact cross p q (fun a b a' b' => cE_cE σ ρ a b a' b') (hz hσ)
    (fun a b a' b' => by rw [add_comm]; exact hz (hz' hσ) a' b' a b)
    (fun a b a' b' => dE_dE σ ρ a b a' b') (LT_LT h)
    (fun a b a' b' => LT_cE E ρ a b a' b') (fun a b a' b' => LT_dE E ρ a b a' b')
    (fun a b a' b' => LT_cE E' σ a b a' b') (fun a b a' b' => LT_dE E' σ a b a' b')

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => funext fun _ => rfl`.
-/
theorem lift_k (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (liftL n (kA E1 E2 a b) : Module.End ℂ (Cq n V)) = LT E1 a b + LT E2 a b :=
  LinearMap.ext fun _ => funext fun _ => rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => funext fun _ => rfl`.
-/
theorem lift_p (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (liftL n (pA E1 E2 a b) : Module.End ℂ (Cq n V)) = LT E1 a b - LT E2 a b :=
  LinearMap.ext fun _ => funext fun _ => rfl

/- English proof (translation)
Simplify using `only [cE, cT_neg (fun u : tau lev a b => h u.1), smul_zero, add_zero]`.
-/
theorem cE_zero (σ : ℂ) {a b : Fin n} (h : ¬a < b) : (cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [cE, cT_neg (fun u : tau lev a b => h u.1), smul_zero, add_zero]

/- English proof (translation)
Rewrite using `[sum_pos' (fun a b => LT E1 a b * cE lev 1 a b) (fun a b h => by rw [cE_zero _ h, mul_zero]), sum_pos' (fun a b => LT E2 a b * cE lev (-1) a b) (fun a b h => by rw [cE_zero _ h, mul_zero]), ← sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, hab⟩` from `i`. Establish `x1 : xL E1 E2 (true, ⟨(a, b), hab⟩) = pA E1 E2 a b` using `by simp [xL]`. Establish `x0 : xL E1 E2 (false, ⟨(a, b), hab⟩) = kA E1 E2 a b` using `by simp [xL]`.

Distinguish the cases in `hi : lev a < lev b`. Establish `ht : tau lev a b` using `⟨hab, hi⟩`. Establish `e1 : inUU lev ((true, ⟨(a, b), hab⟩) : Lt n)` using `hi`. Establish `e0 : inUU lev ((false, ⟨(a, b), hab⟩) : Lt n)` using `hi`. Rewrite using `[if_pos e1, if_pos e0, x1, x0, lift_p, lift_k]`.

Simplify using `only [cE, cT_pos ht, one_smul, neg_smul]`. Use `noncomm_ring`. Establish `e1 : ¬inUU lev ((true, ⟨(a, b), hab⟩) : Lt n)` using `hi`. Establish `e0 : ¬inUU lev ((false, ⟨(a, b), hab⟩) : Lt n)` using `hi`. Establish `ht : ¬tau lev a b` using `fun u => hi u.2`.

Rewrite using `[if_neg e1, if_neg e0]`. Simplify using `only [cE, cT_neg ht, smul_zero, add_zero, mul_zero]`.
-/
theorem bd_one (E1 E2 : Fin n → Fin n → Module.End ℂ V) {dec : ∀ l : Lt n, Decidable (inUU lev l)} :
    (∑ l : Lt n, @ite _ (inUU lev l) (dec l) ((liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l) 0)
      = (∑ a, ∑ b, LT E1 a b * cE lev 1 a b) + ∑ a, ∑ b, LT E2 a b * cE lev (-1) a b := by
  rw [sum_pos' (fun a b => LT E1 a b * cE lev 1 a b) (fun a b h => by rw [cE_zero _ h, mul_zero]),
    sum_pos' (fun a b => LT E2 a b * cE lev (-1) a b) (fun a b h => by rw [cE_zero _ h, mul_zero]),
    ← sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have x1 : xL E1 E2 (true, ⟨(a, b), hab⟩) = pA E1 E2 a b := by simp [xL]
  have x0 : xL E1 E2 (false, ⟨(a, b), hab⟩) = kA E1 E2 a b := by simp [xL]
  by_cases hi : lev a < lev b
  · have ht : tau lev a b := ⟨hab, hi⟩
    have e1 : inUU lev ((true, ⟨(a, b), hab⟩) : Lt n) := hi
    have e0 : inUU lev ((false, ⟨(a, b), hab⟩) : Lt n) := hi
    rw [if_pos e1, if_pos e0, x1, x0, lift_p, lift_k]
    simp only [cE, cT_pos ht, one_smul, neg_smul]
    noncomm_ring
  · have e1 : ¬inUU lev ((true, ⟨(a, b), hab⟩) : Lt n) := hi
    have e0 : ¬inUU lev ((false, ⟨(a, b), hab⟩) : Lt n) := hi
    have ht : ¬tau lev a b := fun u => hi u.2
    rw [if_neg e1, if_neg e0]
    simp only [cE, cT_neg ht, smul_zero, add_zero, mul_zero]

/- English proof (translation)
Take `⟨s, ⟨a, b⟩, hab⟩` from `l`. Take `⟨t, ⟨b', e⟩, hbe⟩` from `m`. Simplify using `only at *`. Distinguish the cases in `h : b = b'`. Use `swap`.

Rewrite using `[if_neg h]`. Conclude with `sum_eq_zero fun k _ => if_neg (fun u => h u.2.2.1)`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`. Distinguish the cases in `hl : lev a < lev b`.

Use `swap`. Rewrite using `[cT_neg (lev := lev) (a := a) (b := b) (fun u => hl u.2), mul_zero]`. Conclude with `sum_eq_zero fun k _ => if_neg (fun u => hl u.1)`. Distinguish the cases in `hr : lev b < lev e`. Use `swap`.

Rewrite using `[cT_neg (lev := lev) (a := b) (b := e) (fun u => hr u.2), mul_zero, zero_mul]`. Conclude with `sum_eq_zero fun k _ => if_neg (fun u => hr u.2.1)`. Establish `hlt : a < e` using `hab.trans hbe`. Establish `hlv : lev a < lev e` using `hl.trans hr`. Rewrite using `[dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := b) (b := e) ⟨hbe, hr⟩, cT_pos (lev := lev) (a := a) (b := b) ⟨hab, hl⟩, sum_eq_single (xor s t, ⟨(a, e), hlt⟩)]`.

Rewrite using `[if_pos ⟨hl, hr, rfl, rfl, rfl, rfl⟩]`. Introduce `k _ hk`. Rewrite using `[if_neg]`. Introduce and unpack `⟨-, -, -, e1, e2, e3⟩`. Conclude with `hk (Prod.ext e1 (Subtype.ext (Prod.ext e2 e3)))`.

Simplify using the standard rewrite rules.
-/
theorem tri_sum (l m : Lt n)
    {dec : ∀ k : Lt n, Decidable (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)} :
    (∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec k) (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = if l.2.1.2 = m.2.1.1 then
          dT lev (xor l.1 m.1) l.2.1.1 m.2.1.2 * cT lev m.1 m.2.1.1 m.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2
        else 0 := by
  obtain ⟨s, ⟨a, b⟩, hab⟩ := l
  obtain ⟨t, ⟨b', e⟩, hbe⟩ := m
  dsimp only at *
  by_cases h : b = b'
  swap
  · rw [if_neg h]
    exact sum_eq_zero fun k _ => if_neg (fun u => h u.2.2.1)
  subst h
  rw [if_pos rfl]
  by_cases hl : lev a < lev b
  swap
  · rw [cT_neg (lev := lev) (a := a) (b := b) (fun u => hl u.2), mul_zero]
    exact sum_eq_zero fun k _ => if_neg (fun u => hl u.1)
  by_cases hr : lev b < lev e
  swap
  · rw [cT_neg (lev := lev) (a := b) (b := e) (fun u => hr u.2), mul_zero, zero_mul]
    exact sum_eq_zero fun k _ => if_neg (fun u => hr u.2.1)
  have hlt : a < e := hab.trans hbe
  have hlv : lev a < lev e := hl.trans hr
  rw [dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := b) (b := e) ⟨hbe, hr⟩,
    cT_pos (lev := lev) (a := a) (b := b) ⟨hab, hl⟩, sum_eq_single (xor s t, ⟨(a, e), hlt⟩)]
  · rw [if_pos ⟨hl, hr, rfl, rfl, rfl, rfl⟩]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨-, -, -, e1, e2, e3⟩
    exact hk (Prod.ext e1 (Subtype.ext (Prod.ext e2 e3)))
  · simp

/- English proof (translation)
Establish `h1 : ∀ l : Lt n, (∑ m : Lt n, ∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec l m k) (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0) = ∑ t, ∑ e, dT lev (xor l.1 t) l.2.1.1 e * cT lev t l.2.1.2 …`. Introduce `l`. Rewrite using `[sum_congr rfl fun m _ => tri_sum l m]`. Use `(sum_lt (fun t b' e => if l.2.1.2 = b' then dT lev (xor l.1 t) l.2.1.1 e * cT lev t b' e * cT lev l.1 l.2.1.1 l.2.1.2 else 0) ?_).trans ?_` and prove the remaining obligations. Introduce `t b' e h`.

Establish `hc : (cT lev t b' e : Module.End ℂ (Cq n V)) = 0` using `cT_neg (fun u => h u.1)`. Simplify using `[hc]`. Use `sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_single l.2.1.2 (fun b _ hb => sum_eq_zero fun e _ => if_neg (Ne.symm hb)) (by simp)]`. Conclude with `sum_congr rfl fun e _ => if_pos rfl`.

Rewrite using `[sum_congr rfl fun l _ => h1 l]`. Use `(sum_lt (fun s a b => ∑ t, ∑ e, dT lev (xor s t) a e * cT lev t b e * cT lev s a b) ?_).trans ?_` and prove the remaining obligations. Introduce `s a b h`. Establish `hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0` using `cT_neg (fun u => h u.1)`. Simplify using `[hc]`.

Simplify using `only [Fintype.sum_bool, ← sum_add_distrib]`. Use `sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Simplify using `only [dE, cE]`. Rewrite using `[half_three]`. Both sides reduce to the same expression.
-/
theorem bd_two
    {dec : ∀ l m k : Lt n, Decidable (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)} :
    (∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧
      k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec l m k)
        (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = (∑ a, ∑ b, ∑ e, dE lev 1 a e * cE lev 1 b e * cE lev 1 a b)
        + ∑ a, ∑ b, ∑ e, dE lev (-1) a e * cE lev (-1) b e * cE lev (-1) a b := by
  have h1 : ∀ l : Lt n, (∑ m : Lt n, ∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧
      k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec l m k)
        (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = ∑ t, ∑ e, dT lev (xor l.1 t) l.2.1.1 e * cT lev t l.2.1.2 e * cT lev l.1 l.2.1.1 l.2.1.2 := by
    intro l
    rw [sum_congr rfl fun m _ => tri_sum l m]
    refine (sum_lt (fun t b' e => if l.2.1.2 = b' then
      dT lev (xor l.1 t) l.2.1.1 e * cT lev t b' e * cT lev l.1 l.2.1.1 l.2.1.2 else 0) ?_).trans ?_
    · intro t b' e h
      have hc : (cT lev t b' e : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun t _ => ?_
      rw [sum_eq_single l.2.1.2 (fun b _ hb => sum_eq_zero fun e _ => if_neg (Ne.symm hb)) (by simp)]
      exact sum_congr rfl fun e _ => if_pos rfl
  rw [sum_congr rfl fun l _ => h1 l]
  refine (sum_lt (fun s a b => ∑ t, ∑ e, dT lev (xor s t) a e * cT lev t b e * cT lev s a b) ?_).trans ?_
  · intro s a b h
    have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
    simp [hc]
  · simp only [Fintype.sum_bool, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun e _ => ?_
    simp only [dE, cE]
    rw [half_three]
    rfl

/- English proof (translation)
Unfold `bdL`. Use `(congrArg₂ (· + ·) (bd_one (lev := lev) E1 E2) (bd_two (lev := lev))).trans ?_` and prove the remaining obligations. Simplify using `only [Dd]`. Normalize the expressions using the abelian group laws.
-/
theorem bdL_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    bdL (inUU lev) E1 E2 = Dd lev 1 E1 + Dd lev (-1) E2 := by
  unfold bdL
  refine (congrArg₂ (· + ·) (bd_one (lev := lev) E1 E2) (bd_two (lev := lev))).trans ?_
  simp only [Dd]
  abel

/- English proof (translation)
Take `⟨s, ⟨a, b⟩, hab⟩` from `l`. Distinguish the cases in `hl : lev a < lev b`. Use `swap`. Establish `hS : ¬inUU lev ((s, ⟨(a, b), hab⟩) : Lt n)` using `hl`. Establish `hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0` using `cT_neg (fun u => hl u.2)`.

Rewrite using `[sum_eq_zero fun k _ => if_neg hS]`. Simplify using `only`. Rewrite using `[hc]`. Simplify using the standard rewrite rules. Establish `hS : inUU lev ((s, ⟨(a, b), hab⟩) : Lt n)` using `hl`.

Rewrite using `[sum_congr rfl fun k _ => if_pos hS]`. Simplify using `only [adCL, sub_smul, sum_sub_distrib]`. Rewrite using `[cT_pos (lev := lev) (s := s) (a := a) (b := b) ⟨hab, hl⟩]`. Use `congr 1`. Distinguish the cases in `h : q = a`.

Establish `hlv : lev p < lev b` using `by rw [hpq, h]; exact hl`. Establish `hlt : p < b` using `hm.reflect_lt hlv`. Rewrite using `[if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(p, b), hlt⟩)]`. Rewrite using `[if_pos ⟨h, by simp, rfl⟩, one_smul]`. Introduce `k _ hk`.

Rewrite using `[if_neg, zero_smul]`. Introduce and unpack `⟨-, e1, e2⟩`. Conclude with `hk (Prod.ext (by simpa using e1) (Subtype.ext e2))`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`.

Conclude with `sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]`. Distinguish the cases in `h : b = p`. Establish `hlv : lev a < lev q` using `by rw [← hpq, ← h]; exact hl`. Establish `hlt : a < q` using `hm.reflect_lt hlv`. Rewrite using `[if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(a, q), hlt⟩)]`.

Rewrite using `[if_pos ⟨h, by simp, rfl⟩, one_smul]`. Introduce `k _ hk`. Rewrite using `[if_neg, zero_smul]`. Introduce and unpack `⟨-, e1, e2⟩`. Conclude with `hk (Prod.ext (by simpa using e1) (Subtype.ext e2))`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Conclude with `sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]`.
-/
theorem adLL_term (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (l : Lt n) :
    (∑ k : Lt n, if inUU lev l then adCL false p q l k • (creL k * annL l : Module.End ℂ (Cq n V)) else 0)
      = (if q = l.2.1.1 then dT lev l.1 p l.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2 else 0)
        - (if l.2.1.2 = p then dT lev l.1 l.2.1.1 q * cT lev l.1 l.2.1.1 l.2.1.2 else 0) := by
  obtain ⟨s, ⟨a, b⟩, hab⟩ := l
  by_cases hl : lev a < lev b
  swap
  · have hS : ¬inUU lev ((s, ⟨(a, b), hab⟩) : Lt n) := hl
    have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => hl u.2)
    rw [sum_eq_zero fun k _ => if_neg hS]
    dsimp only
    rw [hc]
    simp
  have hS : inUU lev ((s, ⟨(a, b), hab⟩) : Lt n) := hl
  rw [sum_congr rfl fun k _ => if_pos hS]
  simp only [adCL, sub_smul, sum_sub_distrib]
  rw [cT_pos (lev := lev) (s := s) (a := a) (b := b) ⟨hab, hl⟩]
  congr 1
  · by_cases h : q = a
    · have hlv : lev p < lev b := by rw [hpq, h]; exact hl
      have hlt : p < b := hm.reflect_lt hlv
      rw [if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(p, b), hlt⟩)]
      · rw [if_pos ⟨h, by simp, rfl⟩, one_smul]
      · intro k _ hk
        rw [if_neg, zero_smul]
        rintro ⟨-, e1, e2⟩
        exact hk (Prod.ext (by simpa using e1) (Subtype.ext e2))
      · simp
    · rw [if_neg h]
      exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]
  · by_cases h : b = p
    · have hlv : lev a < lev q := by rw [← hpq, ← h]; exact hl
      have hlt : a < q := hm.reflect_lt hlv
      rw [if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(a, q), hlt⟩)]
      · rw [if_pos ⟨h, by simp, rfl⟩, one_smul]
      · intro k _ hk
        rw [if_neg, zero_smul]
        rintro ⟨-, e1, e2⟩
        exact hk (Prod.ext (by simpa using e1) (Subtype.ext e2))
      · simp
    · rw [if_neg h]
      exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]

/- English proof (translation)
Establish `e1 : (∑ l : Lt n, if q = l.2.1.1 then (dT lev l.1 p l.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0) = ∑ s, ∑ r, dT lev s p r * cT lev s q r`. Use `(sum_lt (fun s a b => if q = a then dT lev s p b * cT lev s a b else 0) ?_).trans ?_` and prove the remaining obligations. Introduce `s a b h`. Establish `hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0` using `cT_neg (fun u => h u.1)`. Simplify using `[hc]`.

Use `sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_single q (fun a _ ha => sum_eq_zero fun b _ => if_neg (Ne.symm ha)) (by simp)]`. Conclude with `sum_congr rfl fun r _ => if_pos rfl`. Establish `e2 : (∑ l : Lt n, if l.2.1.2 = p then (dT lev l.1 l.2.1.1 q * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0) = ∑ s, ∑ r, dT lev s r q * cT lev s r p`. Use `(sum_lt (fun s a b => if b = p then dT lev s a q * cT lev s a b else 0) ?_).trans ?_` and prove the remaining obligations.

Introduce `s a b h`. Establish `hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0` using `cT_neg (fun u => h u.1)`. Simplify using `[hc]`. Use `sum_congr rfl fun s _ => sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_single p (fun b _ hb => if_neg hb) (by simp)]`.

Conclude with `if_pos rfl`. Unfold `adLL`. Rewrite using `[sum_congr rfl fun l _ => adLL_term hm hpq l, sum_sub_distrib, e1, e2, sum_sub_distrib]`.
-/
theorem adLL_eq (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) :
    (adLL lev false p q : Module.End ℂ (Cq n V))
      = ∑ s, (∑ r, dT lev s p r * cT lev s q r - ∑ r, dT lev s r q * cT lev s r p) := by
  have e1 : (∑ l : Lt n, if q = l.2.1.1 then
      (dT lev l.1 p l.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0)
      = ∑ s, ∑ r, dT lev s p r * cT lev s q r := by
    refine (sum_lt (fun s a b => if q = a then dT lev s p b * cT lev s a b else 0) ?_).trans ?_
    · intro s a b h
      have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun s _ => ?_
      rw [sum_eq_single q (fun a _ ha => sum_eq_zero fun b _ => if_neg (Ne.symm ha)) (by simp)]
      exact sum_congr rfl fun r _ => if_pos rfl
  have e2 : (∑ l : Lt n, if l.2.1.2 = p then
      (dT lev l.1 l.2.1.1 q * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0)
      = ∑ s, ∑ r, dT lev s r q * cT lev s r p := by
    refine (sum_lt (fun s a b => if b = p then dT lev s a q * cT lev s a b else 0) ?_).trans ?_
    · intro s a b h
      have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => ?_
      rw [sum_eq_single p (fun b _ hb => if_neg hb) (by simp)]
      exact if_pos rfl
  unfold adLL
  rw [sum_congr rfl fun l _ => adLL_term hm hpq l, sum_sub_distrib, e1, e2, sum_sub_distrib]

/- English proof (translation)
Establish `s1 : (∑ r, dE lev 1 p r * cE lev 1 q r + ∑ r, dE lev (-1) p r * cE lev (-1) q r : Module.End ℂ (Cq n V)) = ∑ r, dT lev true p r * cT lev true q r + ∑ r, dT lev false p r * cT lev false q r`. Simplify using `only [← sum_add_distrib]`. Use `sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [dE, cE]`. Conclude with `half_two _ _ _ _`.

Establish `s2 : (∑ r, dE lev 1 r q * cE lev 1 r p + ∑ r, dE lev (-1) r q * cE lev (-1) r p : Module.End ℂ (Cq n V)) = ∑ r, dT lev true r q * cT lev true r p + ∑ r, dT lev false r q * cT lev false r p`. Simplify using `only [← sum_add_distrib]`. Use `sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [dE, cE]`. Conclude with `half_two _ _ _ _`.

Unfold `Lv Aa`. Rewrite using `[adLL_eq hm hpq, lift_k, Fintype.sum_bool]`. Establish `e : ∀ L1 L2 X1 X2 Y1 Y2 : Module.End ℂ (Cq n V), L1 + (X1 - Y1) + (L2 + (X2 - Y2)) = L1 + L2 + ((X1 + X2) - (Y1 + Y2))` using `by intros; abel`. Rewrite using `[e, s1, s2]`. Normalize the expressions using the abelian group laws.
-/
theorem Lv_eq (hm : Monotone lev) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n}
    (hpq : lev p = lev q) :
    Lv lev E1 E2 p q = Aa lev 1 E1 p q + Aa lev (-1) E2 p q := by
  have s1 : (∑ r, dE lev 1 p r * cE lev 1 q r + ∑ r, dE lev (-1) p r * cE lev (-1) q r
      : Module.End ℂ (Cq n V))
      = ∑ r, dT lev true p r * cT lev true q r + ∑ r, dT lev false p r * cT lev false q r := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    simp only [dE, cE]
    exact half_two _ _ _ _
  have s2 : (∑ r, dE lev 1 r q * cE lev 1 r p + ∑ r, dE lev (-1) r q * cE lev (-1) r p
      : Module.End ℂ (Cq n V))
      = ∑ r, dT lev true r q * cT lev true r p + ∑ r, dT lev false r q * cT lev false r p := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    simp only [dE, cE]
    exact half_two _ _ _ _
  unfold Lv Aa
  rw [adLL_eq hm hpq, lift_k, Fintype.sum_bool]
  have e : ∀ L1 L2 X1 X2 Y1 Y2 : Module.End ℂ (Cq n V),
      L1 + (X1 - Y1) + (L2 + (X2 - Y2)) = L1 + L2 + ((X1 + X2) - (Y1 + Y2)) := by
    intros; abel
  rw [e, s1, s2]
  abel

/- English proof (translation)
Introduce `n lev V _ _ E1 E2 hm hE p q hpq`. Take `⟨h1, h2, h12⟩` from `hE`. Establish `hs : ((1 : ℂ) * 1 = 1) ∧ ((-1 : ℂ) * -1 = 1) ∧ ((1 : ℂ) * -1 = -1) ∧ ((-1 : ℂ) * 1 = -1)`. Evaluate the numerical expressions. Rewrite using `[Lv_eq hm E1 E2 hpq, bdL_eq]`.

Conclude with `(Commute.add_left (Commute.add_right (comm_same hm hs.1 h1 hpq) (comm_cross hs.2.2.1 h12 p q)) (Commute.add_right (comm_cross hs.2.2.2 (fun a b c d => (h12 c d a b).symm) p q) (comm_same hm hs.2.1 h2 hpq))).eq`.
-/
theorem lv_bd_comm : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → IsPairA E1 E2 → ∀ p q : Fin n, lev p = lev q →
      (Lv lev E1 E2 p q * bdL (inUU lev) E1 E2 : Module.End ℂ (Cq n V)) = bdL (inUU lev) E1 E2 * Lv lev E1 E2 p q := by
  intro n lev V _ _ E1 E2 hm hE p q hpq
  obtain ⟨h1, h2, h12⟩ := hE
  have hs : ((1 : ℂ) * 1 = 1) ∧ ((-1 : ℂ) * -1 = 1) ∧ ((1 : ℂ) * -1 = -1) ∧ ((-1 : ℂ) * 1 = -1) := by
    norm_num
  rw [Lv_eq hm E1 E2 hpq, bdL_eq]
  exact (Commute.add_left
    (Commute.add_right (comm_same hm hs.1 h1 hpq) (comm_cross hs.2.2.1 h12 p q))
    (Commute.add_right (comm_cross hs.2.2.2 (fun a b c d => (h12 c d a b).symm) p q)
      (comm_same hm hs.2.1 h2 hpq))).eq

end GlobalTheory.CompanionTheory.LvComm
