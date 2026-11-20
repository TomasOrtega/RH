import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsDetermineMultiset

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.Kost

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open CompanionTheory.D.LK (Pos Cn Sup Wt bd lift allT Ft InN ev evK evd Ref wt cpt om)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open Formalism.REAL (GlRel KHighest IsWeight etr)

variable {n : ℕ}

def chiOf (τ : Fin n → ℝ) : Fin n → ℂ := fun c => ((τ c - rhoV n c : ℝ) : ℂ)

def chiHW (ν : Fin n → ℝ) : Fin n → ℂ := fun c => ((ν c + rhoV n c : ℝ) : ℂ)

section HC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def nSub (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V where
  carrier := {y | InN (allT n) E y}
  add_mem' := by
    rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c x ⟨u, rfl⟩
    refine ⟨c • u, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

/- English proof (translation)
Use `⟨Pi.single ⟨(p, q), h⟩ x, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (⟨(p, q), h⟩ : Pos n)]`. Simplify using `[cpt]`. Introduce `i _ hi`. Simplify using `[cpt, Pi.single_eq_of_ne hi]`.

Simplify using the standard rewrite rules.
-/
theorem e_mem (E : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (h : p < q) (x : V) : E p q x ∈ nSub E := by
  classical
  refine ⟨Pi.single ⟨(p, q), h⟩ x, ?_⟩
  rw [Finset.sum_eq_single (⟨(p, q), h⟩ : Pos n)]
  · simp [cpt]
  · intro i _ hi
    simp [cpt, Pi.single_eq_of_ne hi]
  · simp

/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero => simp [Formalism.REAL.epow]`. Consider the case `succ k ih`. Establish `hs : ∀ (k : ℕ) (a b : Fin n), Formalism.REAL.epow E (k + 1) a b = ∑ c, Formalism.REAL.epow E k a c * E c b` using `fun _ _ _ => rfl`. Rewrite using `[hs (k + 1)]`.

Simplify using `only [ih, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← ih c b, hs k, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun d _ => mul_assoc _ _ _`.
-/
theorem epow_left {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E (k + 1) a b = ∑ c, E a c * Formalism.REAL.epow E k c b := by
  induction k generalizing a b with
  | zero => simp [Formalism.REAL.epow]
  | succ k ih =>
    have hs : ∀ (k : ℕ) (a b : Fin n), Formalism.REAL.epow E (k + 1) a b = ∑ c, Formalism.REAL.epow E k a c * E c b :=
      fun _ _ _ => rfl
    rw [hs (k + 1)]
    simp only [ih, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← ih c b, hs k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => mul_assoc _ _ _

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (Formalism.REAL.epowCov _ n E hE k c q p c) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> (try simp only [LinearMap.zero_apply]) <;> abel`.
-/
theorem cov_apply {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (k : ℕ) (p c q : Fin n) (x : V) :
    E p c (Formalism.REAL.epow E k c q x) = Formalism.REAL.epow E k c q (E p c x) + Formalism.REAL.epow E k p q x - (if q = p then Formalism.REAL.epow E k c c x else 0) := by
  have h := LinearMap.congr_fun (Formalism.REAL.epowCov _ n E hE k c q p c) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  split_ifs <;> (try simp only [LinearMap.zero_apply]) <;> abel

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `p q h x`. Simplify using `[Formalism.REAL.epow, h.ne]`. Consider the case `succ k ih`.

Introduce `p q h x`. Rewrite using `[epow_left, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`. Break down `lt_or_ge p c with hc | hc` into its components or cases.

Conclude with `e_mem E hc _`. Rewrite using `[cov_apply hE, if_neg h.ne', sub_zero]`. Conclude with `Submodule.add_mem _ (ih c q (lt_of_le_of_lt hc h) _) (ih p q h x)`.
-/
theorem upper_mem {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (k : ℕ) :
    ∀ (p q : Fin n), p < q → ∀ x : V, Formalism.REAL.epow E k p q x ∈ nSub E := by
  induction k with
  | zero =>
    intro p q h x
    simp [Formalism.REAL.epow, h.ne]
  | succ k ih =>
    intro p q h x
    rw [epow_left, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Module.End.mul_apply]
    rcases lt_or_ge p c with hc | hc
    · exact e_mem E hc _
    · rw [cov_apply hE, if_neg h.ne', sub_zero]
      exact Submodule.add_mem _ (ih c q (lt_of_le_of_lt hc h) _) (ih p q h x)

def bk (n k : ℕ) : Fin n → FreeAlgebra ℂ (Fin n) :=
  Nat.rec (fun _ => 1) (fun _ f a => f a * (FreeAlgebra.ι ℂ a + algebraMap ℂ _ ((a : ℕ) : ℂ)) -
    ∑ c ∈ Finset.Iio a, f c) k

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bk_zero (a : Fin n) : bk n 0 a = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bk_succ (k : ℕ) (a : Fin n) : bk n (k + 1) a =
    bk n k a * (FreeAlgebra.ι ℂ a + algebraMap ℂ _ ((a : ℕ) : ℂ)) - ∑ c ∈ Finset.Iio a, bk n k c := rfl

/- English proof (translation)
Establish `h : (Finset.univ : Finset (Fin n)) = insert a (Finset.Iio a ∪ Finset.Ioi a)`. Use extensionality with `c`. Simplify using `only [mem_univ, mem_insert, mem_union, mem_Iio, mem_Ioi, true_iff]`. Apply the tactic sequence `rcases lt_trichotomy c a with h | h | h <;> tauto`. Rewrite using `[h, Finset.sum_insert (by simp), Finset.sum_union (Finset.disjoint_left.2 fun c h1 h2 => lt_asymm (mem_Iio.1 h1) (mem_Ioi.1 h2))]`.

Normalize the expressions using the abelian group laws.
-/
theorem sum_three {M : Type} [AddCommMonoid M] (f : Fin n → M) (a : Fin n) :
    ∑ c, f c = ∑ c ∈ Finset.Iio a, f c + f a + ∑ c ∈ Finset.Ioi a, f c := by
  have h : (Finset.univ : Finset (Fin n)) = insert a (Finset.Iio a ∪ Finset.Ioi a) := by
    ext c
    simp only [mem_univ, mem_insert, mem_union, mem_Iio, mem_Ioi, true_iff]
    rcases lt_trichotomy c a with h | h | h <;> tauto
  rw [h, Finset.sum_insert (by simp), Finset.sum_union (Finset.disjoint_left.2 fun c h1 h2 => lt_asymm (mem_Iio.1 h1) (mem_Ioi.1 h2))]
  abel

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `a x`. Simplify using `[Formalism.REAL.epow, bk_zero]`. Consider the case `succ k ih`.

Introduce `a x`. Use `set B : Fin n → Module.End ℂ V := fun c => evd (fun c => E c c) (bk n k c) with hB`. Establish `hb : evd (fun c => E c c) (bk n (k + 1) a) x = B a (E a a x) + ((a : ℕ) : ℂ) • B a x - ∑ c ∈ Finset.Iio a, B c x`. Simplify using `[bk_succ, evd, hB, LinearMap.sum_apply]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Establish `h1 : ∀ c ∈ Finset.Iio a, E a c (Formalism.REAL.epow E k c a x) = Formalism.REAL.epow E k c a (E a c x) + Formalism.REAL.epow E k a a x - Formalism.REAL.epow E k c c x` using `fun c _ => by`. Rewrite using `[cov_apply hE, if_pos rfl]`. Establish `h2 : E a a (Formalism.REAL.epow E k a a x) = Formalism.REAL.epow E k a a (E a a x)`. Rewrite using `[cov_apply hE, if_pos rfl]`. Normalize the expressions using the abelian group laws.

Establish `e : Formalism.REAL.epow E (k + 1) a a x - evd (fun c => E c c) (bk n (k + 1) a) x = ∑ c ∈ Finset.Iio a, Formalism.REAL.epow E k c a (E a c x) + (Formalism.REAL.epow E k a a (E a a x) - B a (E a a x)) + ∑ c ∈ Finset.Ioi a, E a c (Formalism.REAL.epow E k c a x) + ((a : ℕ) : ℂ) • (F …`. Rewrite using `[hb, epow_left, LinearMap.sum_apply]`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[sum_three _ a, Finset.sum_congr rfl h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Fin.card_Iio, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun c hc => upper_mem hE k c a (mem_Iio.1 hc) _) (ih a _)) (Submodule.sum_mem _ fun c hc => e_mem E (mem_Ioi.1 hc) _)) (Submodule.smul_mem _ _ (ih a x))) (Submodule.sum_mem _ f …` and prove the remaining obligations.
-/
theorem diag_mem {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (k : ℕ) :
    ∀ (a : Fin n) (x : V), Formalism.REAL.epow E k a a x - evd (fun c => E c c) (bk n k a) x ∈ nSub E := by
  induction k with
  | zero =>
    intro a x
    simp [Formalism.REAL.epow, bk_zero]
  | succ k ih =>
    intro a x
    set B : Fin n → Module.End ℂ V := fun c => evd (fun c => E c c) (bk n k c) with hB
    have hb : evd (fun c => E c c) (bk n (k + 1) a) x =
        B a (E a a x) + ((a : ℕ) : ℂ) • B a x - ∑ c ∈ Finset.Iio a, B c x := by
      simp [bk_succ, evd, hB, LinearMap.sum_apply]
      rw [Nat.cast_smul_eq_nsmul]
    have h1 : ∀ c ∈ Finset.Iio a, E a c (Formalism.REAL.epow E k c a x) =
        Formalism.REAL.epow E k c a (E a c x) + Formalism.REAL.epow E k a a x - Formalism.REAL.epow E k c c x := fun c _ => by
      rw [cov_apply hE, if_pos rfl]
    have h2 : E a a (Formalism.REAL.epow E k a a x) = Formalism.REAL.epow E k a a (E a a x) := by
      rw [cov_apply hE, if_pos rfl]
      abel
    have e : Formalism.REAL.epow E (k + 1) a a x - evd (fun c => E c c) (bk n (k + 1) a) x =
        ∑ c ∈ Finset.Iio a, Formalism.REAL.epow E k c a (E a c x) + (Formalism.REAL.epow E k a a (E a a x) - B a (E a a x)) +
          ∑ c ∈ Finset.Ioi a, E a c (Formalism.REAL.epow E k c a x) + ((a : ℕ) : ℂ) • (Formalism.REAL.epow E k a a x - B a x) -
          ∑ c ∈ Finset.Iio a, (Formalism.REAL.epow E k c c x - B c x) := by
      rw [hb, epow_left, LinearMap.sum_apply]
      simp only [Module.End.mul_apply]
      rw [sum_three _ a, Finset.sum_congr rfl h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Fin.card_Iio, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun c hc => upper_mem hE k c a (mem_Iio.1 hc) _) (ih a _))
      (Submodule.sum_mem _ fun c hc => e_mem E (mem_Ioi.1 hc) _)) (Submodule.smul_mem _ _ (ih a x)))
      (Submodule.sum_mem _ fun c _ => ih c x)

/- English proof (translation)
Use `set A := Formalism.REAL.Amat (fun c => chiOf τ c + ((n : ℂ) - 1) / 2) with hA`. Proceed by induction on `k generalizing a with`. Consider the case `zero`. Simplify using `[bk_zero, Matrix.one_apply]`. Consider the case `succ k ih`.

Establish `hd : chiOf τ a + ((n : ℂ) - 1) / 2 = (τ a : ℂ) + ((a : ℕ) : ℂ)`. Simplify using `only [chiOf, rhoV]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : ∀ b, (A ^ (k + 1)) b a = ∑ c, (A ^ k) b c * A c a` using `fun b => by`.

Rewrite using `[pow_succ, Matrix.mul_apply]`. Simplify using `only [e]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← ih]`. Rewrite using `[sum_three _ a]`.

Establish `h1 : ∀ c ∈ Finset.Ioi a, FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c) * A c a = 0` using `fun c hc => by`. Use `mem_Ioi.1 hc` as an intermediate fact. Simplify using `[hA, Formalism.REAL.Amat, this.ne', this.not_gt]`. Establish `h2 : ∀ c ∈ Finset.Iio a, FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c) * A c a = -FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c)` using `fun c hc => by`. Use `mem_Iio.1 hc` as an intermediate fact.

Simplify using `[hA, Formalism.REAL.Amat, this.ne, this]`. Establish `h3 : A a a = (τ a : ℂ) + ((a : ℕ) : ℂ)`. Simplify using `[hA, Formalism.REAL.Amat, hd]`. Rewrite using `[Finset.sum_eq_zero h1, Finset.sum_congr rfl h2, h3, Finset.sum_neg_distrib]`. Simplify using `[bk_succ, map_sum, sub_eq_add_neg, add_comm]`.
-/
theorem bk_val (τ : Fin n → ℝ) (k : ℕ) (a : Fin n) :
    FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k a) =
      ∑ b, (Formalism.REAL.Amat (fun c => chiOf τ c + ((n : ℂ) - 1) / 2) ^ k) b a := by
  set A := Formalism.REAL.Amat (fun c => chiOf τ c + ((n : ℂ) - 1) / 2) with hA
  induction k generalizing a with
  | zero =>
    simp [bk_zero, Matrix.one_apply]
  | succ k ih =>
    have hd : chiOf τ a + ((n : ℂ) - 1) / 2 = (τ a : ℂ) + ((a : ℕ) : ℂ) := by
      simp only [chiOf, rhoV]
      push_cast
      ring
    have e : ∀ b, (A ^ (k + 1)) b a = ∑ c, (A ^ k) b c * A c a := fun b => by
      rw [pow_succ, Matrix.mul_apply]
    simp only [e]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← ih]
    rw [sum_three _ a]
    have h1 : ∀ c ∈ Finset.Ioi a, FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c) * A c a = 0 := fun c hc => by
      have := mem_Ioi.1 hc
      simp [hA, Formalism.REAL.Amat, this.ne', this.not_gt]
    have h2 : ∀ c ∈ Finset.Iio a, FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c) * A c a =
        -FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) (bk n k c) := fun c hc => by
      have := mem_Iio.1 hc
      simp [hA, Formalism.REAL.Amat, this.ne, this]
    have h3 : A a a = (τ a : ℂ) + ((a : ℕ) : ℂ) := by
      simp [hA, Formalism.REAL.Amat, hd]
    rw [Finset.sum_eq_zero h1, Finset.sum_congr rfl h2, h3, Finset.sum_neg_distrib]
    simp [bk_succ, map_sum, sub_eq_add_neg, add_comm]

end HC

/- English proof (translation)
Use `⟨∑ a, bk n m a, fun V _ _ E hE x => ?_, fun τ => ?_⟩` and prove the remaining obligations. Establish `e : etr E m x - evd (fun c => E c c) (∑ a, bk n m a) x = ∑ a, (Formalism.REAL.epow E m a a x - evd (fun c => E c c) (bk n m a) x)`. Simplify using `[etr, map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem (nSub E) fun a _ => diag_mem hE m a x`.

Simplify using `only [map_sum, bk_val, GlobalTheory.Dec.gelfVal]`. Conclude with `Finset.sum_comm`.
-/
theorem trHC (n m : ℕ) : ∃ b : FreeAlgebra ℂ (Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      ∀ x : V, InN (allT n) E (etr E m x - evd (fun c => E c c) b x)) ∧
    ∀ τ : Fin n → ℝ, FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) b = GlobalTheory.Dec.gelfVal (chiOf τ) m := by
  refine ⟨∑ a, bk n m a, fun V _ _ E hE x => ?_, fun τ => ?_⟩
  · have e : etr E m x - evd (fun c => E c c) (∑ a, bk n m a) x =
        ∑ a, (Formalism.REAL.epow E m a a x - evd (fun c => E c c) (bk n m a) x) := by
      simp [etr, map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]
    rw [e]
    exact Submodule.sum_mem (nSub E) fun a _ => diag_mem hE m a x
  · simp only [map_sum, bk_val, GlobalTheory.Dec.gelfVal]
    exact Finset.sum_comm

section Kill

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b x hx`. Apply the tactic sequence `by_cases h : a = b <;> simp [Formalism.REAL.epow, h, hx]`. Consider the case `succ k ih`.

Introduce `a b x hx`. Establish `hs : Formalism.REAL.epow E (k + 1) a b = ∑ c, Formalism.REAL.epow E k a c * E c b` using `rfl`. Rewrite using `[hs, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun c _ => ih a c _ (hU c b rfl x hx)`.
-/
theorem epow_stab {E : Fin n → Fin n → Module.End ℂ V} {U : Submodule ℂ V} (hU : KStab (allT n) E U) (k : ℕ) :
    ∀ (a b : Fin n), ∀ x ∈ U, Formalism.REAL.epow E k a b x ∈ U := by
  induction k with
  | zero =>
    intro a b x hx
    by_cases h : a = b <;> simp [Formalism.REAL.epow, h, hx]
  | succ k ih =>
    intro a b x hx
    have hs : Formalism.REAL.epow E (k + 1) a b = ∑ c, Formalism.REAL.epow E k a c * E c b := rfl
    rw [hs, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun c _ => ih a c _ (hU c b rfl x hx)

/- English proof (translation)
Rewrite using `[etr, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun a _ => epow_stab hU k a a x hx`.
-/
theorem etr_stab {E : Fin n → Fin n → Module.End ℂ V} {U : Submodule ℂ V} (hU : KStab (allT n) E U) (k : ℕ)
    {x : V} (hx : x ∈ U) : etr E k x ∈ U := by
  rw [etr, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun a _ => epow_stab hU k a a x hx

end Kill

/- English proof (translation)
Establish `hK : KRel (allT n) E` using `fun a b c d _ _ => hE a b c d`. Proceed by induction on `hm : Module.finrank ℂ S using Nat.strong_induction_on generalizing S with`. Consider the case `_ m ih`. Distinguish the cases in `hbot : S = ⊥`. Use `⟨[], by simp, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[hbot]`. Simplify using `using (Submodule.mem_bot ℂ).1 hx`. Take `⟨y, hyS, hy0, ν, hy⟩` from `Formalism.REAL.highestWeightExists_holds V n (allT n) E S hS hK hU hSt hbot`. Take `⟨L, hLS, hyL, hL, hirr, -, -⟩` from `CompanionTheory.D.DSIC.hLowSpan n (allT n) V E ν y S hK hU hy0 hy hS hSt hyS`. Establish `: FiniteDimensional ℂ L` using `Submodule.finiteDimensional_of_le hLS`.

Establish `hL'` using `GlobalTheory.CompanionTheory.KLowSpan.kstab_orthogonal hU hL`. Establish `hdis : ∀ u ∈ L, u ∈ Lᗮ → u = 0` using `fun u h1 h2 => inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 u h1)`. Take `⟨mm, s, hs, hys⟩` from `hbad ν y hy0 hy`. Use `set T : Module.End ℂ V := etr E mm - s • (1 : Module.End ℂ V) with hT`. Establish `hTE : ∀ a b x, T (E a b x) = E a b (T x)` using `fun a b x => by`.

Use `LinearMap.congr_fun (Formalism.REAL.etrCentral _ n E hE mm a b) x` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Simplify using `[hT, this]`. Establish `hkL : ∀ x ∈ L, T x = 0`. Establish `hst : KStab (allT n) E (L ⊓ LinearMap.ker T)` using `fun a b he v hv => ⟨hL a b he v hv.1, by`.

Establish `h2 : T v = 0` using `hv.2`. Use `show T (E a b v) = 0`. Rewrite using `[hTE, h2, map_zero]⟩`. Establish `hy1 : y ∈ L ⊓ LinearMap.ker T` using `⟨hyL, by show T y = 0`. Simplify using `[hT, hys]⟩`.

Break down `hirr _ inf_le_left hst with h | h` into its components or cases. Rewrite `hy1` using `[h]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 hy1) hy0`. Introduce `x hx`. Establish `: x ∈ L ⊓ LinearMap.ker T` using `by rw [h]; exact hx`.

Conclude with `this.2`. Establish `hlt : S ⊓ Lᗮ < S` using `lt_of_le_of_ne inf_le_left fun h => hy0 (hdis y hyL (h.ge hyS).2)`. Take `⟨L₁, hL₁, hk₁⟩` from `ih _ (hm ▸ Submodule.finrank_lt_finrank_of_lt hlt) (S ⊓ Lᗮ) inferInstance (fun a b he v hv => ⟨hSt a b he v hv.1, hL' a b he v hv.2⟩) rfl`. Use `⟨L₁ ++ [(mm, s)], fun p hp => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Break down `List.mem_append.1 hp with h | h` into its components or cases.

Conclude with `hL₁ p h`. Rewrite using `[List.mem_singleton.1 h]`. Conclude with `hs`. Take `⟨p, hp, q, hq, hpq⟩` from `Submodule.exists_add_mem_mem_orthogonal (K := L) x`. Establish `hqS : q ∈ S`.

Establish `: q = x - p` using `by rw [hpq]; abel`. Rewrite using `[this]`. Conclude with `S.sub_mem hx (hLS hp)`. Establish `hTq : T q ∈ S ⊓ Lᗮ`. Establish `hstab : ∀ U : Submodule ℂ V, KStab (allT n) E U → ∀ v ∈ U, T v ∈ U` using `fun U hU' v hv => U.sub_mem (etr_stab hU' mm hv) (by simpa using U.smul_mem s hv)`.

Conclude with `⟨hstab S hSt q hqS, hstab _ hL' q hq⟩`. Establish `e : (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) (L₁ ++ [(mm, s)])).prod x = (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) L₁).prod (T q)`. Rewrite using `[List.map_append, List.prod_append]`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply]`. Rewrite using `[← hT, hpq, map_add, hkL p hp, zero_add]`.

Rewrite using `[e]`. Conclude with `hk₁ _ hTq`.
-/
theorem kill_list {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (hU : KUnit (allT n) E) (c : ℕ → ℂ)
    (hbad : ∀ (ν : Fin n → ℝ) (y : V), y ≠ 0 → KHighest (allT n) E ν y → ∃ m s, s ≠ c m ∧ etr E m y = s • y)
    (S : Submodule ℂ V) (hS : FiniteDimensional ℂ S) (hSt : KStab (allT n) E S) :
    ∃ L : List (ℕ × ℂ), (∀ p ∈ L, p.2 ≠ c p.1) ∧
      ∀ x ∈ S, (L.map fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)).prod x = 0 := by
  have hK : KRel (allT n) E := fun a b c d _ _ => hE a b c d
  induction hm : Module.finrank ℂ S using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hbot : S = ⊥
    · refine ⟨[], by simp, fun x hx => ?_⟩
      rw [hbot] at hx
      simpa using (Submodule.mem_bot ℂ).1 hx
    obtain ⟨y, hyS, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n (allT n) E S hS hK hU hSt hbot
    obtain ⟨L, hLS, hyL, hL, hirr, -, -⟩ := CompanionTheory.D.DSIC.hLowSpan n (allT n) V E ν y S hK hU hy0 hy hS hSt hyS
    have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLS
    have hL' := GlobalTheory.CompanionTheory.KLowSpan.kstab_orthogonal hU hL
    have hdis : ∀ u ∈ L, u ∈ Lᗮ → u = 0 := fun u h1 h2 =>
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 u h1)
    obtain ⟨mm, s, hs, hys⟩ := hbad ν y hy0 hy
    set T : Module.End ℂ V := etr E mm - s • (1 : Module.End ℂ V) with hT
    have hTE : ∀ a b x, T (E a b x) = E a b (T x) := fun a b x => by
      have := LinearMap.congr_fun (Formalism.REAL.etrCentral _ n E hE mm a b) x
      simp only [Module.End.mul_apply] at this
      simp [hT, this]
    have hkL : ∀ x ∈ L, T x = 0 := by
      have hst : KStab (allT n) E (L ⊓ LinearMap.ker T) := fun a b he v hv =>
        ⟨hL a b he v hv.1, by
          have h2 : T v = 0 := hv.2
          show T (E a b v) = 0
          rw [hTE, h2, map_zero]⟩
      have hy1 : y ∈ L ⊓ LinearMap.ker T := ⟨hyL, by
        show T y = 0
        simp [hT, hys]⟩
      rcases hirr _ inf_le_left hst with h | h
      · rw [h] at hy1
        exact absurd ((Submodule.mem_bot ℂ).1 hy1) hy0
      · intro x hx
        have : x ∈ L ⊓ LinearMap.ker T := by rw [h]; exact hx
        exact this.2
    have hlt : S ⊓ Lᗮ < S := lt_of_le_of_ne inf_le_left fun h => hy0 (hdis y hyL (h.ge hyS).2)
    obtain ⟨L₁, hL₁, hk₁⟩ := ih _ (hm ▸ Submodule.finrank_lt_finrank_of_lt hlt) (S ⊓ Lᗮ) inferInstance
      (fun a b he v hv => ⟨hSt a b he v hv.1, hL' a b he v hv.2⟩) rfl
    refine ⟨L₁ ++ [(mm, s)], fun p hp => ?_, fun x hx => ?_⟩
    · rcases List.mem_append.1 hp with h | h
      · exact hL₁ p h
      · rw [List.mem_singleton.1 h]
        exact hs
    · obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) x
      have hqS : q ∈ S := by
        have : q = x - p := by rw [hpq]; abel
        rw [this]
        exact S.sub_mem hx (hLS hp)
      have hTq : T q ∈ S ⊓ Lᗮ := by
        have hstab : ∀ U : Submodule ℂ V, KStab (allT n) E U → ∀ v ∈ U, T v ∈ U := fun U hU' v hv =>
          U.sub_mem (etr_stab hU' mm hv) (by simpa using U.smul_mem s hv)
        exact ⟨hstab S hSt q hqS, hstab _ hL' q hq⟩
      have e : (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) (L₁ ++ [(mm, s)])).prod x =
          (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) L₁).prod (T q) := by
        rw [List.map_append, List.prod_append]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply]
        rw [← hT, hpq, map_add, hkL p hp, zero_add]
      rw [e]
      exact hk₁ _ hTq

/- English proof (translation)
Establish `hc : ∀ c : M, Fintype.card {a // f a = c} = Fintype.card {b // g b = c}` using `fun c => by`. Establish `h1` using `congrArg (Multiset.count c) h`. Rewrite `h1` using `[Multiset.count_map, Multiset.count_map]`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Simplify `h1` using `[Finset.card, Finset.filter_val, eq_comm]`.

Set `e : ∀ c : M, {a // f a = c} ≃ {b // g b = c}` to `fun c => Fintype.equivOfCardEq (hc c)`. Conclude with `⟨Equiv.ofFiberEquiv e, fun a => Equiv.ofFiberEquiv_map e a⟩`.
-/
theorem exists_perm_of_map_eq {M : Type} [DecidableEq M] (f g : Fin n → M)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) : ∃ w : Equiv.Perm (Fin n), ∀ a, g (w a) = f a := by
  have hc : ∀ c : M, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := fun c => by
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using h1
  let e : ∀ c : M, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => Equiv.ofFiberEquiv_map e a⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h1 : (univ.filter fun b : Fin n => levB n a < levB n b).card = n - 1 - (a : ℕ)`. Establish `: (univ.filter fun b : Fin n => levB n a < levB n b) = Finset.Ioi a`. Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, mem_Ioi]`.

Conclude with `Iff.rfl`. Rewrite using `[this, Fin.card_Ioi]`. Establish `h2 : (univ.filter fun b : Fin n => levB n b < levB n a).card = (a : ℕ)`. Establish `: (univ.filter fun b : Fin n => levB n b < levB n a) = Finset.Iio a`. Use extensionality with `b`.

Simplify using `only [mem_filter, mem_univ, true_and, mem_Iio]`. Conclude with `Iff.rfl`. Rewrite using `[this, Fin.card_Iio]`. Establish `hlt` using `a.2`. Simplify using `only [muQ, rhoU, m0, h1, h2]`.

Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem muQ_levB (lam : Fin n → ℤ) : muQ lam (levB n) = m0 lam := by
  funext a
  have h1 : (univ.filter fun b : Fin n => levB n a < levB n b).card = n - 1 - (a : ℕ) := by
    have : (univ.filter fun b : Fin n => levB n a < levB n b) = Finset.Ioi a := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_Ioi]
      exact Iff.rfl
    rw [this, Fin.card_Ioi]
  have h2 : (univ.filter fun b : Fin n => levB n b < levB n a).card = (a : ℕ) := by
    have : (univ.filter fun b : Fin n => levB n b < levB n a) = Finset.Iio a := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_Iio]
      exact Iff.rfl
    rw [this, Fin.card_Iio]
  have hlt := a.2
  simp only [muQ, rhoU, m0, h1, h2]
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

def bOf (B : Finset (Pos n)) : Finset (Fin n × Fin n) := B.map (Function.Embedding.subtype _)

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [wtB, wt, bOf, Finset.filter_map, Finset.card_map]`. Both sides reduce to the same expression.
-/
theorem wtB_bOf (B : Finset (Pos n)) : wtB (bOf B) = wt B := by
  funext c
  simp only [wtB, wt, bOf, Finset.filter_map, Finset.card_map]
  rfl

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_perm_of_map_eq _ _ (GlobalTheory.GelfandInj.gelfVal_multiset_eq n _ _ fun k => hm (k + 1))`. Use `⟨bOf B, hB.map, fun p hp => ?_, fun c d hcd => ?_, w, ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_map.1 hp`. Conclude with `i.2`. Establish `h1` using `hdom c d hcd`.

Establish `h2 : ((c : ℕ) : ℝ) < (d : ℕ)` using `by exact_mod_cast hcd`. Simplify using `only [Pi.add_apply, rhoV]`. Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `a`. Establish `h1 : ν a + rhoV n a = (m0 lam + (2 : ℝ) • rhoV n - wt B) (w a) - rhoV n (w a)`.

Use `hw a` as an intermediate fact. Simplify using `only [chiOf, chiHW] at this`. Conclude with `(Complex.ofReal_injective this).symm`. Simplify using `only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, muQ_levB, wtB_bOf] at h1 ⊢`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem not_weight_of_kostant (lam : Fin n → ℤ) (B : Finset (Pos n)) (hB : B.Nonempty) (ν : Fin n → ℝ)
    (hdom : ∀ c d : Fin n, c < d → ν d ≤ ν c)
    (hm : ∀ k, GlobalTheory.Dec.gelfVal (chiHW ν) k = GlobalTheory.Dec.gelfVal (chiOf (m0 lam + (2 : ℝ) • rhoV n - wt B)) k) :
    IsSecondTypeWeight lam (levB n) ν := by
  classical
  obtain ⟨w, hw⟩ := exists_perm_of_map_eq _ _ (GlobalTheory.GelfandInj.gelfVal_multiset_eq n _ _ fun k => hm (k + 1))
  refine ⟨bOf B, hB.map, fun p hp => ?_, fun c d hcd => ?_, w, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hp
    exact i.2
  · have h1 := hdom c d hcd
    have h2 : ((c : ℕ) : ℝ) < (d : ℕ) := by exact_mod_cast hcd
    simp only [Pi.add_apply, rhoV]
    linarith
  · funext a
    have h1 : ν a + rhoV n a = (m0 lam + (2 : ℝ) • rhoV n - wt B) (w a) - rhoV n (w a) := by
      have := hw a
      simp only [chiOf, chiHW] at this
      exact (Complex.ofReal_injective this).symm
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, muQ_levB, wtB_bOf] at h1 ⊢
    rw [h1]
    ring

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def xl (n : ℕ) : Fin n → Fin n → FreeAlgebra ℂ (Fin n × Fin n) := fun a b => FreeAlgebra.ι ℂ (a, b)

/- English proof (translation)
Proceed by induction on `k generalizing a b with`. Consider the case `zero => simp only [Formalism.REAL.epow]; split_ifs <;> simp`. Consider the case `succ k ih => simp only [Formalism.REAL.epow, map_sum, map_mul, ih]`.
-/
theorem map_epow {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B)
    (X : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    f (Formalism.REAL.epow X k a b) = Formalism.REAL.epow (fun p q => f (X p q)) k a b := by
  induction k generalizing a b with
  | zero => simp only [Formalism.REAL.epow]; split_ifs <;> simp
  | succ k ih => simp only [Formalism.REAL.epow, map_sum, map_mul, ih]

/- English proof (translation)
Simplify using `only [etr, map_sum, map_epow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `p q`. Simplify using `[evK, xl]`.
-/
theorem evK_etr (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) : evK (allT n) E (etr (xl n) m) = etr E m := by
  simp only [etr, map_sum, map_epow]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext p q
  simp [evK, xl]

/- English proof (translation)
Introduce `a b c d` and use `h a b c d rfl rfl`.
-/
theorem glRel_of_k {E : Fin n → Fin n → Module.End ℂ V} (h : KRel (allT n) E) : GlRel E :=
  fun a b c d => h a b c d rfl rfl

/- English proof (translation)
Introduce `a b c d _ _` and use `h a b c d`.
-/
theorem k_of_glRel {E : Fin n → Fin n → Module.End ℂ V} (h : GlRel E) : KRel (allT n) E :=
  fun a b c d _ _ => h a b c d

/- English proof (translation)
Proceed by induction on `b using FreeAlgebra.induction with`. Consider the case `grade0 r => simp [evd, Algebra.algebraMap_eq_smul_one]`. Consider the case `grade1 c => simp [evd]`. Conclude with `hz c`. Consider the case `mul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]`.

Consider the case `add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]`.
-/
theorem evd_wt (E : Fin n → Fin n → Module.End ℂ V) (τ : Fin n → ℝ) (z : Cn n V) (hz : Wt (allT n) E τ z)
    (b : FreeAlgebra ℂ (Fin n)) :
    evd (Ft (allT n) E) b z = FreeAlgebra.lift ℂ (fun c => (τ c : ℂ)) b • z := by
  induction b using FreeAlgebra.induction with
  | grade0 r => simp [evd, Algebra.algebraMap_eq_smul_one]
  | grade1 c => simp [evd]; exact hz c
  | mul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]

/- English proof (translation)
Introduce `_ _ _ _ h` and use `h`.
-/
theorem ref_all (x : Cn n V) : Ref (allT n) (allT n) x := fun _ _ _ _ h => h

/- English proof (translation)
Take `⟨b, hN, hv⟩` from `trHC n m`. Take `⟨w, hw1, hw2⟩` from `CompanionTheory.D.LK.hGenCO n (allT n) (allT n) (etr (xl n) m) b (fun _ _ _ => rfl) (fun V _ _ E hK => by`. Establish `hG` using `glRel_of_k hK`. Use `⟨fun i _ => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[evK_etr]`.

Conclude with `(Formalism.REAL.etrCentral _ n E hG m _ _).symm`. Rewrite using `[evK_etr]`. Conclude with `hN V E hG x) V E (k_of_glRel hE) ∅ j z hz (ref_all z) hb`. Use `⟨w, hw1, ?_⟩` and prove the remaining obligations. Rewrite `hw2` using `[evK_etr, evd_wt E τ z hw b, hv τ]`.

Conclude with `hw2`.
-/
theorem etr_cycle (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (m j : ℕ) (τ : Fin n → ℝ) (z : Cn n V)
    (hz : Sup (allT n) ∅ j z) (hw : Wt (allT n) E τ z) (hb : bd (allT n) E z = 0) :
    ∃ w : Cn n V, Sup (allT n) ∅ (j + 1) w ∧
      lift n (etr E m) z - GlobalTheory.Dec.gelfVal (chiOf τ) m • z = bd (allT n) E w := by
  obtain ⟨b, hN, hv⟩ := trHC n m
  obtain ⟨w, hw1, hw2⟩ := CompanionTheory.D.LK.hGenCO n (allT n) (allT n) (etr (xl n) m) b (fun _ _ _ => rfl)
    (fun V _ _ E hK => by
      have hG := glRel_of_k hK
      refine ⟨fun i _ => ?_, fun x => ?_⟩
      · rw [evK_etr]
        exact (Formalism.REAL.etrCentral _ n E hG m _ _).symm
      · rw [evK_etr]
        exact hN V E hG x) V E (k_of_glRel hE) ∅ j z hz (ref_all z) hb
  refine ⟨w, hw1, ?_⟩
  rw [evK_etr, evd_wt E τ z hw b, hv τ] at hw2
  exact hw2

end

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h1 : (univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a).card = n - 1 - (a : ℕ)`. Establish `: (univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a) = Finset.Ioi a`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Rewrite using `[this, Fin.card_Ioi]`. Establish `h2 : (univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a).card = (a : ℕ)`. Establish `: (univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a) = Finset.Iio a`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Rewrite using `[this, Fin.card_Iio]`. Establish `hlt` using `a.2`. Use `show (((univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a).card : ℝ) - ((univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a).card : ℝ)) / 2 = _`. Rewrite using `[h1, h2, rhoV, Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoC_allT : PI.UpqRep.rhoC (allT n) = rhoV n := by
  funext a
  have h1 : (univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a).card = n - 1 - (a : ℕ) := by
    have : (univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a) = Finset.Ioi a := by
      ext b; simp
    rw [this, Fin.card_Ioi]
  have h2 : (univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a).card = (a : ℕ) := by
    have : (univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a) = Finset.Iio a := by
      ext b; simp
    rw [this, Fin.card_Iio]
  have hlt := a.2
  show (((univ.filter fun b : Fin n => a < b ∧ allT n b = allT n a).card : ℝ) -
    ((univ.filter fun b : Fin n => b < a ∧ allT n b = allT n a).card : ℝ)) / 2 = _
  rw [h1, h2, rhoV, Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `i`. Simplify using `[om, cpt]`.
-/
theorem om_allT : om (allT n) = univ := by
  ext i; simp [om, cpt]

/- English proof (translation)
Take `⟨h1, h2⟩` from `CompanionTheory.D.LK.top_degree_cycle n (allT n) V E ν y`. Take `⟨hc, hw⟩` from `h2 hy`. Establish `hs : Sup (allT n) ∅ (univ : Finset (Pos n)).card (Pi.single (om (allT n)) y : Cn n V)`. Introduce `A hA`. Establish `hA' : A = univ`.

Assume the negation of the conclusion as `h`. Conclude with `hA (by rw [om_allT]; exact Pi.single_eq_of_ne h _)`. Substitute `hA'` using the available equality. Simplify using `[cpt]`. Take `⟨w, hw1, hw2⟩` from `etr_cycle E hE m _ _ _ hs hw hc`.

Establish `hw0 : w = 0`. Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `h`. Use `(hw1 A h).2` as an intermediate fact. Establish `h3 : (A.filter (cpt (allT n))).card ≤ (univ : Finset (Pos n)).card` using `card_le_card (subset_univ _)`.

Simplify using `only [Pi.zero_apply] at *`. Use linear arithmetic over natural numbers and integers. Rewrite `hw2` using `[hw0, map_zero]`. Establish `h5` using `congrFun hw2 (om (allT n))`. Establish `hχ : chiOf (ν + (2 : ℝ) • PI.UpqRep.rhoC (allT n)) = chiHW ν`.

Use function extensionality and compare the values at `c`. Rewrite using `[rhoC_allT]`. Simplify using `only [chiOf, chiHW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h5` using `[hχ]`. Simplify `h5` using `[sub_eq_zero]`.
-/
theorem etr_hw (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℝ) (y : V)
    (hy : KHighest (allT n) E ν y) (m : ℕ) : etr E m y = GlobalTheory.Dec.gelfVal (chiHW ν) m • y := by
  obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.top_degree_cycle n (allT n) V E ν y
  obtain ⟨hc, hw⟩ := h2 hy
  have hs : Sup (allT n) ∅ (univ : Finset (Pos n)).card (Pi.single (om (allT n)) y : Cn n V) := by
    intro A hA
    have hA' : A = univ := by
      by_contra h
      exact hA (by rw [om_allT]; exact Pi.single_eq_of_ne h _)
    subst hA'
    simp [cpt]
  obtain ⟨w, hw1, hw2⟩ := etr_cycle E hE m _ _ _ hs hw hc
  have hw0 : w = 0 := by
    funext A
    by_contra h
    have := (hw1 A h).2
    have h3 : (A.filter (cpt (allT n))).card ≤ (univ : Finset (Pos n)).card := card_le_card (subset_univ _)
    simp only [Pi.zero_apply] at *
    omega
  rw [hw0, map_zero] at hw2
  have h5 := congrFun hw2 (om (allT n))
  have hχ : chiOf (ν + (2 : ℝ) • PI.UpqRep.rhoC (allT n)) = chiHW ν := by
    funext c
    rw [rhoC_allT]
    simp only [chiOf, chiHW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    ring
  rw [hχ] at h5
  simpa [sub_eq_zero] using h5

/- English proof (translation)
Introduce `A h` and use `by by_cases h1 : x A = 0 · exact hy A fun h2 => h (by simp [h1, h2]) · exact hx A h1`.
-/
theorem sup_add {j : ℕ} {x y : Cn n V} (hx : Sup (allT n) ∅ j x) (hy : Sup (allT n) ∅ j y) :
    Sup (allT n) ∅ j (x + y) := fun A h => by
  by_cases h1 : x A = 0
  · exact hy A fun h2 => h (by simp [h1, h2])
  · exact hx A h1

/- English proof (translation)
The claim follows from `CompanionTheory.D.LK.sup_of_supp hx fun A h => by simp [h]`.
-/
theorem sup_smul {j : ℕ} {x : Cn n V} (c : ℂ) (hx : Sup (allT n) ∅ j x) : Sup (allT n) ∅ j (c • x) :=
  CompanionTheory.D.LK.sup_of_supp hx fun A h => by simp [h]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Use `⟨1, 0, one_ne_zero, fun A h => absurd rfl h, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `A`. Simplify using the standard rewrite rules.

Consider the case `cons p L ih`. Take `⟨κ, w, hκ, hw1, hw2⟩` from `ih fun q hq => hL q (List.mem_cons_of_mem _ hq)`. Take `⟨w', hw1', hw2'⟩` from `etr_cycle E hE p.1 j τ z hz hw hb`. Use `set T : Module.End ℂ V := etr E p.1 - p.2 • (1 : Module.End ℂ V) with hT`. Use `set c := GlobalTheory.Dec.gelfVal (chiOf τ) p.1 with hc`.

Establish `hTE : ∀ (i : Pos n), cpt (allT n) i → ∀ x, T (E i.1.1 i.1.2 x) = E i.1.1 i.1.2 (T x)` using `fun i _ x => by`. Use `LinearMap.congr_fun (Formalism.REAL.etrCentral _ n E hE p.1 i.1.1 i.1.2) x` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Simplify using `[hT, this]`. Establish `hz1 : lift n T z = (c - p.2) • z + bd (allT n) E w'`.

Rewrite using `[← hw2']`. Use function extensionality and compare the values at `A`. Simplify using `[hT, sub_smul]`. Use `⟨κ * (c - p.2), κ • w' + lift n T w, mul_ne_zero hκ (sub_ne_zero.2 (hL p (by simp)).symm), sup_add (sup_smul κ hw1') (CompanionTheory.D.LK.sup_of_supp hw1 fun A h => by simp [h]), ?_⟩` and prove the remaining obligations. Establish `e : lift n ((List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) (p :: L)).prod) z = lift n T (lift n (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) L).prod z)`.

Use function extensionality and compare the values at `A`. Simplify using `[hT]`. Rewrite using `[e, hw2, map_add, map_smul, hz1, CompanionTheory.D.LK.lift_bd T E E hTE, map_add, map_smul, smul_add, smul_smul, add_assoc]`.
-/
theorem chain_list (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (j : ℕ) (τ : Fin n → ℝ) (z : Cn n V)
    (hz : Sup (allT n) ∅ j z) (hw : Wt (allT n) E τ z) (hb : bd (allT n) E z = 0) (L : List (ℕ × ℂ))
    (hL : ∀ p ∈ L, p.2 ≠ GlobalTheory.Dec.gelfVal (chiOf τ) p.1) :
    ∃ (κ : ℂ) (w : Cn n V), κ ≠ 0 ∧ Sup (allT n) ∅ (j + 1) w ∧
      lift n (L.map fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)).prod z = κ • z + bd (allT n) E w := by
  induction L with
  | nil =>
    refine ⟨1, 0, one_ne_zero, fun A h => absurd rfl h, ?_⟩
    funext A
    simp
  | cons p L ih =>
    obtain ⟨κ, w, hκ, hw1, hw2⟩ := ih fun q hq => hL q (List.mem_cons_of_mem _ hq)
    obtain ⟨w', hw1', hw2'⟩ := etr_cycle E hE p.1 j τ z hz hw hb
    set T : Module.End ℂ V := etr E p.1 - p.2 • (1 : Module.End ℂ V) with hT
    set c := GlobalTheory.Dec.gelfVal (chiOf τ) p.1 with hc
    have hTE : ∀ (i : Pos n), cpt (allT n) i → ∀ x, T (E i.1.1 i.1.2 x) = E i.1.1 i.1.2 (T x) := fun i _ x => by
      have := LinearMap.congr_fun (Formalism.REAL.etrCentral _ n E hE p.1 i.1.1 i.1.2) x
      simp only [Module.End.mul_apply] at this
      simp [hT, this]
    have hz1 : lift n T z = (c - p.2) • z + bd (allT n) E w' := by
      rw [← hw2']
      funext A
      simp [hT, sub_smul]
    refine ⟨κ * (c - p.2), κ • w' + lift n T w, mul_ne_zero hκ (sub_ne_zero.2 (hL p (by simp)).symm),
      sup_add (sup_smul κ hw1') (CompanionTheory.D.LK.sup_of_supp hw1 fun A h => by simp [h]), ?_⟩
    have e : lift n ((List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) (p :: L)).prod) z =
        lift n T (lift n (List.map (fun p => etr E p.1 - p.2 • (1 : Module.End ℂ V)) L).prod z) := by
      funext A
      simp [hT]
    rw [e, hw2, map_add, map_smul, hz1, CompanionTheory.D.LK.lift_bd T E E hTE, map_add, map_smul, smul_add, smul_smul, add_assoc]

end

open CompanionTheory.D.LK (LocFin) in

/- English proof (translation)
Introduce `n lam hlam V _ _ E1 E2 h B j z hB hz hwt hb`. Establish `hE : GlRel (kF E1 E2)` using `fun a b c d => by`. Establish `e1` using `h.gl1 a b c d`. Establish `e2` using `h.gl2 a b c d`. Establish `c1` using `h.comm a b c d`.

Establish `c2` using `h.comm c d a b`. Establish `e3 : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b = (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b)`. Simplify using `only [kF, add_mul, mul_add]`. Rewrite using `[c1, ← c2]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e3, e1, e2]`. Simplify using `only [kF]`. Apply the tactic sequence `split_ifs <;> abel`. Establish `hU : KUnit (allT n) (kF E1 E2)` using `fun a b _ x y => h.unitK a b x y`. Establish `hF : LocFin (allT n) (kF E1 E2)` using `fun x => by`.

Take `⟨S, h1, h2, h3⟩` from `h.locFin x`. Conclude with `⟨S, h1, fun a b _ w hw => h3 a b w hw, h2⟩`. Use `set τ : Fin n → ℝ := m0 lam + (2 : ℝ) • rhoV n - wt B with hτ`. Establish `hbad : ∀ (ν : Fin n → ℝ) (y : V), y ≠ 0 → KHighest (allT n) (kF E1 E2) ν y → ∃ m s, s ≠ GlobalTheory.Dec.gelfVal (chiOf τ) m ∧ etr (kF E1 E2) m y = s • y`. Introduce `ν y hy0 hy`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `hm : ∀ k, GlobalTheory.Dec.gelfVal (chiHW ν) k = GlobalTheory.Dec.gelfVal (chiOf τ) k` using `fun k => by`. Assume the negation of the conclusion as `hne`. Conclude with `hc k _ hne (etr_hw _ hE ν y hy k)`.

Establish `hdom : ∀ c d : Fin n, c < d → ν d ≤ ν c` using `fun c d hcd => by`. Establish `h2` using `GlobalTheory.CompanionTheory.KWeightMajor.norm_identity (ε := allT n) (a := c) (b := d) (k_of_glRel hE) hU rfl hy.1`. Rewrite `h2` using `[hy.2 c d hcd rfl, norm_zero]`. Establish `h3 : 0 < ‖y‖ ^ 2` using `by positivity`. Assume the negation of the conclusion as `h4`.

Establish `h5 : 0 < (ν d - ν c) * ‖y‖ ^ 2` using `mul_pos (by linarith [not_le.1 h4]) h3`. Use polynomial arithmetic with `[sq_nonneg ‖kF E1 E2 d c y‖]`. Establish `hbot` using `h.no_second_type_weight ν (not_weight_of_kostant lam B hB ν hdom hm)`. Establish `hmem : y ∈ hwSp E1 E2 ν` using `hy`. Rewrite `hmem` using `[hbot]`.

Conclude with `hy0 ((Submodule.mem_bot ℂ).1 hmem)`. Use `choose S hS hSt hmem using hF`. Set `W : Submodule ℂ V` to `⨆ A, S (z A)`. Use `haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _`. Establish `hWs : KStab (allT n) (kF E1 E2) W` using `fun a b h v hv => (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (kF E1 E2 a b)) hv`.

Take `⟨L, hL, hkill⟩` from `kill_list (kF E1 E2) hE hU _ hbad W inferInstance hWs`. Take `⟨κ, w, hκ, hw1, hw2⟩` from `chain_list (kF E1 E2) hE j τ z hz hwt hb L hL`. Establish `h0 : lift n (L.map fun p => etr (kF E1 E2) p.1 - p.2 • (1 : Module.End ℂ V)).prod z = 0`. Use function extensionality and compare the values at `A`. Conclude with `hkill _ (Submodule.mem_iSup_of_mem A (hmem _))`.

Rewrite `hw2` using `[h0]`. Establish `h1 : bd (allT n) (kF E1 E2) (-κ⁻¹ • w) = z`. Establish `e : bd (allT n) (kF E1 E2) w = -(κ • z)` using `eq_neg_of_add_eq_zero_right hw2.symm`. Rewrite using `[map_smul, e, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hκ, one_smul]`. Take `⟨t, ht1, ht2, ht3⟩` from `GlobalTheory.CompanionTheory.LKWtProj.wtProj n (allT n) (allT n) V (kF E1 E2) (k_of_glRel hE) hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd (allT n) (kF E1 E2)) (CompanionTheory.D.LK.differential_commutes_weight_operator n _ _ V _ (fun _ _ _ => rfl) (k_of_glRel hE)) τ _ (h1.symm ▸ …`.

Conclude with `⟨t, CompanionTheory.D.LK.sup_of_supp (sup_smul _ hw1) fun A h => ht3 A (by simpa using h), ht1, ht2.trans h1⟩`.
-/
theorem vanKostant : VanKostant := by
  intro n lam hlam V _ _ E1 E2 h B j z hB hz hwt hb
  have hE : GlRel (kF E1 E2) := fun a b c d => by
    have e1 := h.gl1 a b c d
    have e2 := h.gl2 a b c d
    have c1 := h.comm a b c d
    have c2 := h.comm c d a b
    have e3 : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [c1, ← c2]
      abel
    rw [e3, e1, e2]
    simp only [kF]
    split_ifs <;> abel
  have hU : KUnit (allT n) (kF E1 E2) := fun a b _ x y => h.unitK a b x y
  have hF : LocFin (allT n) (kF E1 E2) := fun x => by
    obtain ⟨S, h1, h2, h3⟩ := h.locFin x
    exact ⟨S, h1, fun a b _ w hw => h3 a b w hw, h2⟩
  set τ : Fin n → ℝ := m0 lam + (2 : ℝ) • rhoV n - wt B with hτ
  have hbad : ∀ (ν : Fin n → ℝ) (y : V), y ≠ 0 → KHighest (allT n) (kF E1 E2) ν y →
      ∃ m s, s ≠ GlobalTheory.Dec.gelfVal (chiOf τ) m ∧ etr (kF E1 E2) m y = s • y := by
    intro ν y hy0 hy
    by_contra hc
    push Not at hc
    have hm : ∀ k, GlobalTheory.Dec.gelfVal (chiHW ν) k = GlobalTheory.Dec.gelfVal (chiOf τ) k := fun k => by
      by_contra hne
      exact hc k _ hne (etr_hw _ hE ν y hy k)
    have hdom : ∀ c d : Fin n, c < d → ν d ≤ ν c := fun c d hcd => by
      have h2 := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity (ε := allT n) (a := c) (b := d) (k_of_glRel hE) hU rfl hy.1
      rw [hy.2 c d hcd rfl, norm_zero] at h2
      have h3 : 0 < ‖y‖ ^ 2 := by positivity
      by_contra h4
      have h5 : 0 < (ν d - ν c) * ‖y‖ ^ 2 := mul_pos (by linarith [not_le.1 h4]) h3
      nlinarith [sq_nonneg ‖kF E1 E2 d c y‖]
    have hbot := h.no_second_type_weight ν (not_weight_of_kostant lam B hB ν hdom hm)
    have hmem : y ∈ hwSp E1 E2 ν := hy
    rw [hbot] at hmem
    exact hy0 ((Submodule.mem_bot ℂ).1 hmem)
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab (allT n) (kF E1 E2) W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (kF E1 E2 a b)) hv
  obtain ⟨L, hL, hkill⟩ := kill_list (kF E1 E2) hE hU _ hbad W inferInstance hWs
  obtain ⟨κ, w, hκ, hw1, hw2⟩ := chain_list (kF E1 E2) hE j τ z hz hwt hb L hL
  have h0 : lift n (L.map fun p => etr (kF E1 E2) p.1 - p.2 • (1 : Module.End ℂ V)).prod z = 0 := by
    funext A
    exact hkill _ (Submodule.mem_iSup_of_mem A (hmem _))
  rw [h0] at hw2
  have h1 : bd (allT n) (kF E1 E2) (-κ⁻¹ • w) = z := by
    have e : bd (allT n) (kF E1 E2) w = -(κ • z) := eq_neg_of_add_eq_zero_right hw2.symm
    rw [map_smul, e, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.CompanionTheory.LKWtProj.wtProj n (allT n) (allT n) V (kF E1 E2) (k_of_glRel hE) hU
    (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd (allT n) (kF E1 E2))
    (CompanionTheory.D.LK.differential_commutes_weight_operator n _ _ V _ (fun _ _ _ => rfl) (k_of_glRel hE)) τ _ (h1.symm ▸ hwt)
  exact ⟨t, CompanionTheory.D.LK.sup_of_supp (sup_smul _ hw1) fun A h => ht3 A (by simpa using h), ht1, ht2.trans h1⟩

end GlobalTheory.CompanionTheory.RealMult.Kost
