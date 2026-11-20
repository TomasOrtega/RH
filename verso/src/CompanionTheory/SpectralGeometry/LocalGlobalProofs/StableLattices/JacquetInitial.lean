import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEvalAtOfMem

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgStartOne

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

section Quot

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def stabD (P : Submodule ℂ (Module.Dual ℂ V)) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ φ ∈ P, T.dualMap φ ∈ P}
  mul_mem' := fun {a b} ha hb φ hφ => hb _ (ha φ hφ)
  add_mem' := fun {a b} ha hb φ hφ => by
    have : (a + b).dualMap φ = a.dualMap φ + b.dualMap φ := by ext x; simp
    rw [this]
    exact P.add_mem (ha φ hφ) (hb φ hφ)
  algebraMap_mem' := fun r φ hφ => by
    have : (algebraMap ℂ (Module.End ℂ V) r).dualMap φ = r • φ := by
      ext x
      simp [Module.algebraMap_end_apply]
    rw [this]
    exact P.smul_mem r hφ

abbrev ZQ (S W' : Submodule ℂ (Module.Dual ℂ V)) := ↥S ⧸ W'.comap S.subtype

def zop (S W' : Submodule ℂ (Module.Dual ℂ V)) (T : ↥(stabD S ⊓ stabD W')) : Module.End ℂ (ZQ S W') :=
  (W'.comap S.subtype).mapQ (W'.comap S.subtype)
    ((T : Module.End ℂ V).dualMap.restrict fun φ hφ => (Algebra.mem_inf.1 T.2).1 φ hφ)
    fun x hx => (Algebra.mem_inf.1 T.2).2 _ hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zop_mk (S W' : Submodule ℂ (Module.Dual ℂ V)) (T : ↥(stabD S ⊓ stabD W')) (x : ↥S) :
    zop S W' T (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(T : Module.End ℂ V).dualMap x, (Algebra.mem_inf.1 T.2).1 _ x.2⟩ := rfl

def rho (S W' : Submodule ℂ (Module.Dual ℂ V)) : ↥(stabD S ⊓ stabD W') →ₗ[ℂ] Module.End ℂ (ZQ S W') where
  toFun := zop S W'
  map_add' T T' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [LinearMap.add_apply, Submodule.mkQ_apply, zop_mk, zop_mk, zop_mk, ← Submodule.Quotient.mk_add]
    refine congrArg (Submodule.Quotient.mk (p := W'.comap S.subtype)) (Subtype.ext ?_)
    ext y
    simp
  map_smul' c T := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [LinearMap.smul_apply, Submodule.mkQ_apply, zop_mk, RingHom.id_apply, zop_mk, ← Submodule.Quotient.mk_smul]
    refine congrArg (Submodule.Quotient.mk (p := W'.comap S.subtype)) (Subtype.ext ?_)
    ext y
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho_mk (S W' : Submodule ℂ (Module.Dual ℂ V)) (T : ↥(stabD S ⊓ stabD W')) (x : ↥S) :
    rho S W' T (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(T : Module.End ℂ V).dualMap x, (Algebra.mem_inf.1 T.2).1 _ x.2⟩ := rfl

/- English proof (translation)
Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ q`. Both sides reduce to the same expression.
-/
theorem rho_mul (S W' : Submodule ℂ (Module.Dual ℂ V)) (T T' : ↥(stabD S ⊓ stabD W')) :
    rho S W' (T * T') = rho S W' T' * rho S W' T := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

/- English proof (translation)
Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ q`. Both sides reduce to the same expression.
-/
theorem rho_one (S W' : Submodule ℂ (Module.Dual ℂ V)) : rho S W' 1 = 1 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [rho_one]`. Consider the case `succ m ih => rw [pow_succ, rho_mul, ih, pow_succ']`.
-/
theorem rho_pow (S W' : Submodule ℂ (Module.Dual ℂ V)) (T : ↥(stabD S ⊓ stabD W')) (m : ℕ) :
    rho S W' (T ^ m) = rho S W' T ^ m := by
  induction m with
  | zero => simp [rho_one]
  | succ m ih => rw [pow_succ, rho_mul, ih, pow_succ']

/- English proof (translation)
Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ q`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (h x x.2)`.
-/
theorem rho_eq_zero (S W' : Submodule ℂ (Module.Dual ℂ V)) (T : ↥(stabD S ⊓ stabD W'))
    (h : ∀ φ ∈ S, (T : Module.End ℂ V).dualMap φ ∈ W') : rho S W' T = 0 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  exact (Submodule.Quotient.mk_eq_zero _).2 (h x x.2)

end Quot

/- English proof (translation)
Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_` and prove the remaining obligations. Set `ℓ' : M →ₗ[ℂ] ℂ` to `ℓ ∘ₗ P.mkQ`. Set `p : Polynomial ℂ` to `∑ k ∈ Finset.range l, Polynomial.C (ℓ' (c k)) * Polynomial.X ^ k`. Establish `hp : p = 0`.

Use `Polynomial.funext fun t => ?_` and prove the remaining obligations. Establish `e : ℓ' (∑ j ∈ Finset.range l, t ^ j • c j) = 0` using `by show ℓ (P.mkQ _) = 0`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 (h t), map_zero]`. Simplify using `only [map_sum, map_smul, smul_eq_mul] at e`. Simplify using `only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]`.

Rewrite using `[← e]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `e3` using `congrArg (fun q => Polynomial.coeff q j) hp`. Simplify `e3` using `[p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj, ℓ']`.
-/
theorem coef_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (P : Submodule ℂ M) (l : ℕ) (c : ℕ → M)
    (h : ∀ t : ℂ, ∑ j ∈ Finset.range l, t ^ j • c j ∈ P) (j : ℕ) (hj : j < l) : c j ∈ P := by
  classical
  rw [← Submodule.Quotient.mk_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let ℓ' : M →ₗ[ℂ] ℂ := ℓ ∘ₗ P.mkQ
  let p : Polynomial ℂ := ∑ k ∈ Finset.range l, Polynomial.C (ℓ' (c k)) * Polynomial.X ^ k
  have hp : p = 0 := by
    refine Polynomial.funext fun t => ?_
    have e : ℓ' (∑ j ∈ Finset.range l, t ^ j • c j) = 0 := by
      show ℓ (P.mkQ _) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 (h t), map_zero]
    simp only [map_sum, map_smul, smul_eq_mul] at e
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← e]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have e3 := congrArg (fun q => Polynomial.coeff q j) hp
  simpa [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj, ℓ'] using e3

/- English proof (translation)
Use `GlobalTheory.CapelliUniv.qdet_map B.val (fun a b => (⟨E a b, hE a b⟩ : B)) u` as an intermediate fact. Simplify using `only [Subalgebra.coe_val] at this`. Rewrite using `[this]`. Conclude with `(qdet (fun a b => (⟨E a b, hE a b⟩ : B)) u).2`.
-/
theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) {m : ℕ} (E : Fin m → Fin m → A)
    (hE : ∀ a b, E a b ∈ B) (u : ℂ) : qdet E u ∈ B := by
  have := GlobalTheory.CapelliUniv.qdet_map B.val (fun a b => (⟨E a b, hE a b⟩ : B)) u
  simp only [Subalgebra.coe_val] at this
  rw [this]
  exact (qdet (fun a b => (⟨E a b, hE a b⟩ : B)) u).2

section Grade

variable {n : ℕ} {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Establish `: (0 : Module.End ℂ V).dualMap φ = 0` using `by ext x; simp`. Rewrite using `[this]`. Conclude with `P.zero_mem`.
-/
theorem dual_map_zero_mem {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ (Module.Dual ℂ V))
    (φ : Module.Dual ℂ V) : (0 : Module.End ℂ V).dualMap φ ∈ P := by
  have : (0 : Module.End ℂ V).dualMap φ = 0 := by ext x; simp
  rw [this]
  exact P.zero_mem

/- English proof (translation)
Establish `h1 : ∀ a b, X.E a b ∈ stabD P` using `fun a b φ hφ => by`. Use `P.neg_mem (hst a b φ hφ)` as an intermediate fact. Simplify `this` using `[contraE]`. Unfold `actM`. Conclude with `Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => Subalgebra.smul_mem _ (h1 a b) _`.
-/
theorem actM_mem_stabD (X : GMod n) (P : Submodule ℂ (Module.Dual ℂ X.V))
    (hst : ∀ a b, ∀ φ ∈ P, contraE X a b φ ∈ P) (Y : Matrix (Fin n) (Fin n) ℂ) : actM X.E Y ∈ stabD P := by
  have h1 : ∀ a b, X.E a b ∈ stabD P := fun a b φ hφ => by
    have := P.neg_mem (hst a b φ hφ)
    simpa [contraE] using this
  unfold actM
  exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => Subalgebra.smul_mem _ (h1 a b) _

def dZ : Fin 3 → ℤ := ![-1, 0, 1]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [dZ]`.
-/
theorem dZ_cast (i : Fin 3) : ((dZ i : ℤ) : ℂ) = (![-1, 0, 1] : Fin 3 → ℂ) i := by
  fin_cases i <;> simp [dZ]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem dZ_lt : ∀ i j : Fin 3, i < j → dZ i - dZ j ≤ -1 := by decide

/- English proof (translation)
Use `open GlobalTheory.CompanionTheory.PolyNilGrad in`. Establish `hc : A * (B.U * Matrix.single p q 1 * B.Ui) - (B.U * Matrix.single p q 1 * B.Ui) * A = (dG B p - dG B q) • (B.U * Matrix.single p q 1 * B.Ui)` using `by set Y := B.U * Matrix.single p q 1 * B.Ui with hY`. Establish `hD1 : Matrix.diagonal (dG B) * Matrix.single p q (1 : ℂ) = dG B p • Matrix.single p q (1 : ℂ)`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`.

Use `split_ifs with hh`. Rewrite using `[hh.1]`. Simplify using the standard rewrite rules. Establish `hD2 : Matrix.single p q (1 : ℂ) * Matrix.diagonal (dG B) = dG B q • Matrix.single p q (1 : ℂ)`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Use `split_ifs with hh`. Rewrite using `[hh.2, one_mul, mul_one]`. Simplify using the standard rewrite rules. Establish `e1 : A * Y = dG B p • Y`.

Establish `e0 : A * Y = (B.U * Matrix.diagonal (dG B) * B.Ui) * Y` using `congrArg (· * Y) (A_eq B)`. Rewrite using `[e0, hY, conj_mul, hD1, Matrix.mul_smul, Matrix.smul_mul]`. Establish `e2 : Y * A = dG B q • Y`. Establish `e0 : Y * A = Y * (B.U * Matrix.diagonal (dG B) * B.Ui)` using `congrArg (Y * ·) (A_eq B)`. Rewrite using `[e0, hY, conj_mul, hD2, Matrix.mul_smul, Matrix.smul_mul]`.

Rewrite using `[e1, e2, sub_smul]`. Rewrite using `[hc]`. Use `congr 1`. Use `push_cast`. Rewrite using `[dZ_cast, dZ_cast]`.

Both sides reduce to the same expression.
-/
theorem ad_unit (B : GradBasis A) (p q : Fin n) :
    A * (B.U * Matrix.single p q 1 * B.Ui) - (B.U * Matrix.single p q 1 * B.Ui) * A =
      ((dZ (bl B p) - dZ (bl B q) : ℤ) : ℂ) • (B.U * Matrix.single p q 1 * B.Ui) := by
  classical
  open GlobalTheory.CompanionTheory.PolyNilGrad in
  have hc : A * (B.U * Matrix.single p q 1 * B.Ui) - (B.U * Matrix.single p q 1 * B.Ui) * A =
      (dG B p - dG B q) • (B.U * Matrix.single p q 1 * B.Ui) := by
    set Y := B.U * Matrix.single p q 1 * B.Ui with hY
    have hD1 : Matrix.diagonal (dG B) * Matrix.single p q (1 : ℂ) = dG B p • Matrix.single p q (1 : ℂ) := by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with hh
      · rw [hh.1]
      · simp
    have hD2 : Matrix.single p q (1 : ℂ) * Matrix.diagonal (dG B) = dG B q • Matrix.single p q (1 : ℂ) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with hh
      · rw [hh.2, one_mul, mul_one]
      · simp
    have e1 : A * Y = dG B p • Y := by
      have e0 : A * Y = (B.U * Matrix.diagonal (dG B) * B.Ui) * Y := congrArg (· * Y) (A_eq B)
      rw [e0, hY, conj_mul, hD1, Matrix.mul_smul, Matrix.smul_mul]
    have e2 : Y * A = dG B q • Y := by
      have e0 : Y * A = Y * (B.U * Matrix.diagonal (dG B) * B.Ui) := congrArg (Y * ·) (A_eq B)
      rw [e0, hY, conj_mul, hD2, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, e2, sub_smul]
  rw [hc]
  congr 1
  push_cast
  rw [dZ_cast, dZ_cast]
  rfl

/- English proof (translation)
The claim follows from `F.shift _ _ (ad_unit B p q) s u hu`.
-/
theorem shift_Eb (F : Filt X A) (B : GradBasis A) (p q : Fin n) (s : ℝ) (u : X.V) (hu : u ∈ F.N s) :
    Eb X B p q u ∈ F.N (s + ((dZ (bl B p) - dZ (bl B q) : ℤ) : ℝ)) :=
  F.shift _ _ (ad_unit B p q) s u hu

/- English proof (translation)
Establish `key : ∀ m : ℕ, ∀ φ : Module.Dual ℂ X.V, (∀ u ∈ F.N (s0 - m), φ u = 0) → φ ∉ W' → ∃ φ ∈ W F, φ ∉ W' ∧ ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W'`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `φ hφ hn`.

It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Establish `: φ = 0`. Use extensionality with `u`. Conclude with `hφ u (by simp [hs0])`.

Rewrite using `[this]`. Conclude with `W'.zero_mem`. Consider the case `succ m ih`. Introduce `φ hφ hn`. Distinguish the cases in `hall : ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W'`.

Conclude with `⟨φ, ⟨_, hφ⟩, hn, hall⟩`. Use `push_neg at hall`. Take `⟨p, q, hpq, hnot⟩` from `hall`. Use `ih _ (fun u hu => ?_) hnot` and prove the remaining obligations. Use `hφ _ (F.mono _ _ ?_ (shift_Eb F B p q _ u hu))` and prove the remaining obligations.

Establish `h1 : ((dZ (bl B p) - dZ (bl B q) : ℤ) : ℝ) ≤ -1` using `by exact_mod_cast dZ_lt _ _ hpq`. Move the coercions through the operations in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨φ, ⟨s, hs⟩, hn⟩` from `SetLike.exists_of_lt (lt_of_le_of_ne hle hne)`. Take `⟨m, hm⟩` from `exists_nat_ge (s0 - s)`.

Conclude with `key m φ (fun u hu => hs u (F.mono _ _ (by linarith) hu)) hn`.
-/
theorem exists_killed (F : Filt X A) (B : GradBasis A) (W' : Submodule ℂ (Module.Dual ℂ X.V))
    (hle : W' ≤ W F) (hne : W' ≠ W F) (s0 : ℝ) (hs0 : F.N s0 = ⊤) :
    ∃ φ ∈ W F, φ ∉ W' ∧ ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W' := by
  have key : ∀ m : ℕ, ∀ φ : Module.Dual ℂ X.V, (∀ u ∈ F.N (s0 - m), φ u = 0) → φ ∉ W' →
      ∃ φ ∈ W F, φ ∉ W' ∧ ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W' := by
    intro m
    induction m with
    | zero =>
      intro φ hφ hn
      exfalso
      apply hn
      have : φ = 0 := by
        ext u
        exact hφ u (by simp [hs0])
      rw [this]
      exact W'.zero_mem
    | succ m ih =>
      intro φ hφ hn
      by_cases hall : ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W'
      · exact ⟨φ, ⟨_, hφ⟩, hn, hall⟩
      · push_neg at hall
        obtain ⟨p, q, hpq, hnot⟩ := hall
        refine ih _ (fun u hu => ?_) hnot
        refine hφ _ (F.mono _ _ ?_ (shift_Eb F B p q _ u hu))
        have h1 : ((dZ (bl B p) - dZ (bl B q) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast dZ_lt _ _ hpq
        push_cast at h1 ⊢
        linarith
  obtain ⟨φ, ⟨s, hs⟩, hn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  obtain ⟨m, hm⟩ := exists_nat_ge (s0 - s)
  exact key m φ (fun u hu => hs u (F.mono _ _ (by linarith) hu)) hn

def Sk (F : Filt X A) (B : GradBasis A) (W' : Submodule ℂ (Module.Dual ℂ X.V)) : Submodule ℂ (Module.Dual ℂ X.V) where
  carrier := {φ | φ ∈ W F ∧ ∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W'}
  add_mem' := fun {φ ψ} h1 h2 => ⟨(W F).add_mem h1.1 h2.1, fun p q h => by
    rw [map_add]; exact W'.add_mem (h1.2 p q h) (h2.2 p q h)⟩
  zero_mem' := ⟨(W F).zero_mem, fun p q h => by rw [map_zero]; exact W'.zero_mem⟩
  smul_mem' := fun c φ h1 => ⟨(W F).smul_mem c h1.1, fun p q h => by
    rw [map_smul]; exact W'.smul_mem c (h1.2 p q h)⟩

/- English proof (translation)
Introduce and unpack `φ ⟨⟨s, hs⟩, hk⟩`. Use `⟨⟨s, fun u hu => ?_⟩, fun c e hce => ?_⟩` and prove the remaining obligations. Use `hs _ ?_` and prove the remaining obligations. Use `shift_Eb F B p q s u hu` as an intermediate fact. Simplify `this` using `[hpq]`.

Establish `hE : ∀ c e, Eb X B c e ∈ stabD W'` using `fun c e => actM_mem_stabD X W' hst _`. Establish `hg` using `GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B p q c e`. Establish `e1 : Eb X B p q * Eb X B c e = Eb X B c e * Eb X B p q + ((if q = c then Eb X B p e else 0) - (if e = p then Eb X B c q else 0))`. Rewrite using `[← hg]`. Normalize the expressions using the abelian group laws.

Establish `e2 : (Eb X B c e).dualMap ((Eb X B p q).dualMap φ) = (Eb X B p q * Eb X B c e).dualMap φ` using `rfl`. Establish `e3 : (Eb X B c e * Eb X B p q).dualMap φ = (Eb X B p q).dualMap ((Eb X B c e).dualMap φ)` using `rfl`. Establish `e4 : ∀ T T' : Module.End ℂ X.V, (T + T').dualMap φ = T.dualMap φ + T'.dualMap φ`. Introduce `T T'`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `e5 : ∀ T T' : Module.End ℂ X.V, (T - T').dualMap φ = T.dualMap φ - T'.dualMap φ`. Introduce `T T'`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[e2, e1, e4, e5, e3]`. Use `W'.add_mem (hE _ _ _ (hk c e hce)) (W'.sub_mem ?_ ?_)` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `hk p e (by rw [hpq, h]; exact hce)`. Conclude with `dual_map_zero_mem W' φ`.

Use `split_ifs with h`. Conclude with `hk c q (by rw [← hpq, ← h]; exact hce)`. Conclude with `dual_map_zero_mem W' φ`.
-/
theorem levi_stab (F : Filt X A) (B : GradBasis A) (W' : Submodule ℂ (Module.Dual ℂ X.V))
    (hst : ∀ a b, ∀ φ ∈ W', contraE X a b φ ∈ W') (p q : Fin n) (hpq : bl B p = bl B q) :
    Eb X B p q ∈ stabD (Sk F B W') := by
  rintro φ ⟨⟨s, hs⟩, hk⟩
  refine ⟨⟨s, fun u hu => ?_⟩, fun c e hce => ?_⟩
  · refine hs _ ?_
    have := shift_Eb F B p q s u hu
    simpa [hpq] using this
  · have hE : ∀ c e, Eb X B c e ∈ stabD W' := fun c e => actM_mem_stabD X W' hst _
    have hg := GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B p q c e
    have e1 : Eb X B p q * Eb X B c e = Eb X B c e * Eb X B p q +
        ((if q = c then Eb X B p e else 0) - (if e = p then Eb X B c q else 0)) := by
      rw [← hg]; abel
    have e2 : (Eb X B c e).dualMap ((Eb X B p q).dualMap φ) = (Eb X B p q * Eb X B c e).dualMap φ := rfl
    have e3 : (Eb X B c e * Eb X B p q).dualMap φ = (Eb X B p q).dualMap ((Eb X B c e).dualMap φ) := rfl
    have e4 : ∀ T T' : Module.End ℂ X.V, (T + T').dualMap φ = T.dualMap φ + T'.dualMap φ := by
      intro T T'; ext x; simp
    have e5 : ∀ T T' : Module.End ℂ X.V, (T - T').dualMap φ = T.dualMap φ - T'.dualMap φ := by
      intro T T'; ext x; simp
    rw [e2, e1, e4, e5, e3]
    refine W'.add_mem (hE _ _ _ (hk c e hce)) (W'.sub_mem ?_ ?_)
    · split_ifs with h
      · exact hk p e (by rw [hpq, h]; exact hce)
      · exact dual_map_zero_mem W' φ
    · split_ifs with h
      · exact hk c q (by rw [← hpq, ← h]; exact hce)
      · exact dual_map_zero_mem W' φ

/- English proof (translation)
Introduce `φ hφ`. Establish `hE : ∀ c e, Eb X B c e ∈ stabD W'` using `fun c e => actM_mem_stabD X W' hst _`. Establish `hX : GlRel (Eb X B)` using `GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B`. Set `E' : Fin n → Fin n → ↥(stabD W')` to `fun p q => ⟨Eb X B p q, hE p q⟩`. Establish `hE' : GlRel E'` using `fun a b c d => Subtype.ext (by`.

Use `hX a b c d` as an intermediate fact. Simplify using `only [E']`. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa using this)`. Establish `key` using `GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal ↥(stabD W') (dims n B.j) B.hj E' hE' Y`. Use `set D := qdet (Eb X B) (Y + ((n : ℂ) - 1) / 2) with hD`.

Use `set b := (List.ofFn fun i : Fin 3 => Qb X B i Y).prod with hb`. Establish `hval : ∀ y ∈ Submodule.span ℂ {y : ↥(stabD W') | ∃ (p q : Fin n) (w : ↥(stabD W')), blk (stdBlocks (dims n B.j) B.hj) p < blk (stdBlocks (dims n B.j) B.hj) q ∧ y = E' p q * w}, ((y : Module.End ℂ X.V)).dualMap φ ∈ W'`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨p, q, w, hpq, rfl⟩` from `hy`. Conclude with `w.2 _ (hφ.2 p q hpq)`. Consider the case `zero => exact dual_map_zero_mem W' φ`. Consider the case `add a c _ _ ha hc`. Establish `: ((a + c : ↥(stabD W')) : Module.End ℂ X.V).dualMap φ = (a : Module.End ℂ X.V).dualMap φ + (c : Module.End ℂ X.V).dualMap φ` using `by ext x; simp`.

Rewrite using `[this]`. Conclude with `W'.add_mem ha hc`. Consider the case `smul r a _ ha`. Establish `: ((r • a : ↥(stabD W')) : Module.End ℂ X.V).dualMap φ = r • (a : Module.End ℂ X.V).dualMap φ`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `W'.smul_mem r ha`. Establish `hDb : (D - b).dualMap φ ∈ W'`. Establish `h1` using `hval _ key`.

Establish `e1 : ((qdet E' (Y + ((n : ℂ) - 1) / 2) : ↥(stabD W')) : Module.End ℂ X.V) = D` using `(GlobalTheory.CapelliUniv.qdet_map (stabD W').val E' _).symm`. Establish `e2 : (((List.ofFn fun i : Fin 3 => qdet (fun p q : Fin (dims n B.j i) => E' (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩)) (Y + ((dims n B.j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2)).prod : ↥(stabD W')) : Module.End ℂ X.V) = …`. Use `map_list_prod (stabD W').val (List.ofFn fun i : Fin 3 => qdet (fun p q : Fin (dims n B.j i) => E' (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩)) (Y + ((dims n B.j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[List.map_ofFn, hb]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `(GlobalTheory.CapelliUniv.qdet_map (stabD W').val _ _).symm`. Rewrite `h1` using `[Subalgebra.coe_sub, e1, e2]`. Conclude with `h1`.

Establish `hC : D = qdet X.E (Y + ((n : ℂ) - 1) / 2)` using `GlobalTheory.CompanionTheory.RgConjQdet.conjQdet n X B.U B.Ui B.hU B.hUi _`. Establish `hDc : Commute D b`. Use `Commute.list_prod_right _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hy`. Conclude with `GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun p q => Formalism.REAL.qDetCentral _ _ (Eb X B) hX _ _ _) _`.

Set `Fb : Module.End ℂ X.V` to `b - Formalism.QuantumDeterminants.capP χ Y • 1`. Set `Dz : Module.End ℂ X.V` to `D - Formalism.QuantumDeterminants.capP χ Y • 1`. Establish `hs : ∀ z : Module.End ℂ X.V, Commute z (Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V))` using `fun z => (Commute.one_right z).smul_right _`. Establish `hc : Commute Fb Dz` using `(hDc.symm.sub_right (hs _)).sub_left ((hs D).symm.sub_right (hs _))`. Establish `e2` using `hc.mul_geom_sum₂ k`.

Establish `hz : Dz ^ k = 0` using `by show (D - _) ^ k = 0`. Rewrite using `[hC]`. Conclude with `hk`. Rewrite `e2` using `[hz, sub_zero]`. Establish `hFb : Fb ∈ stabD W'` using `Subalgebra.sub_mem _ (Subalgebra.list_prod_mem _ fun y hy => by`.

Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hy`. Conclude with `qdet_mem _ _ (fun p q => hE _ _) _) (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)`. Establish `hDz : Dz ∈ stabD W'` using `Subalgebra.sub_mem _ (qdet_mem _ _ hE _) (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)`. Establish `hG : ∑ i ∈ Finset.range k, Fb ^ i * Dz ^ (k - 1 - i) ∈ stabD W'` using `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hFb _) (Subalgebra.pow_mem _ hDz _)`. Use `show (Fb ^ k).dualMap φ ∈ W'`.

Rewrite using `[← e2]`. Use `show (∑ i ∈ Finset.range k, Fb ^ i * Dz ^ (k - 1 - i)).dualMap ((Fb - Dz).dualMap φ) ∈ W'`. Use `hG _ ?_` and prove the remaining obligations. Establish `e3 : Fb - Dz = -(D - b)` using `by simp [Fb, Dz]`. Rewrite using `[e3]`.

Establish `: (-(D - b)).dualMap φ = -((D - b).dualMap φ)` using `by ext x; simp`. Rewrite using `[this]`. Conclude with `W'.neg_mem hDb`.
-/
theorem nil_key (F : Filt X A) (B : GradBasis A) (W' : Submodule ℂ (Module.Dual ℂ X.V))
    (hst : ∀ a b, ∀ φ ∈ W', contraE X a b φ ∈ W') (χ : Fin n → ℂ) (k : ℕ) (Y : ℂ)
    (hk : (qdet X.E (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) ^ k = 0) :
    ∀ φ ∈ Sk F B W', (((List.ofFn fun i : Fin 3 => Qb X B i Y).prod -
      Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) ^ k).dualMap φ ∈ W' := by
  intro φ hφ
  have hE : ∀ c e, Eb X B c e ∈ stabD W' := fun c e => actM_mem_stabD X W' hst _
  have hX : GlRel (Eb X B) := GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B
  let E' : Fin n → Fin n → ↥(stabD W') := fun p q => ⟨Eb X B p q, hE p q⟩
  have hE' : GlRel E' := fun a b c d => Subtype.ext (by
    have := hX a b c d
    simp only [E']
    split_ifs at this ⊢ <;> simpa using this)
  have key := GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal ↥(stabD W') (dims n B.j) B.hj E' hE' Y
  set D := qdet (Eb X B) (Y + ((n : ℂ) - 1) / 2) with hD
  set b := (List.ofFn fun i : Fin 3 => Qb X B i Y).prod with hb
  have hval : ∀ y ∈ Submodule.span ℂ {y : ↥(stabD W') | ∃ (p q : Fin n) (w : ↥(stabD W')),
      blk (stdBlocks (dims n B.j) B.hj) p < blk (stdBlocks (dims n B.j) B.hj) q ∧ y = E' p q * w},
      ((y : Module.End ℂ X.V)).dualMap φ ∈ W' := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, w, hpq, rfl⟩ := hy
      exact w.2 _ (hφ.2 p q hpq)
    | zero => exact dual_map_zero_mem W' φ
    | add a c _ _ ha hc =>
      have : ((a + c : ↥(stabD W')) : Module.End ℂ X.V).dualMap φ = (a : Module.End ℂ X.V).dualMap φ +
          (c : Module.End ℂ X.V).dualMap φ := by ext x; simp
      rw [this]; exact W'.add_mem ha hc
    | smul r a _ ha =>
      have : ((r • a : ↥(stabD W')) : Module.End ℂ X.V).dualMap φ = r • (a : Module.End ℂ X.V).dualMap φ := by
        ext x; simp
      rw [this]; exact W'.smul_mem r ha
  have hDb : (D - b).dualMap φ ∈ W' := by
    have h1 := hval _ key
    have e1 : ((qdet E' (Y + ((n : ℂ) - 1) / 2) : ↥(stabD W')) : Module.End ℂ X.V) = D :=
      (GlobalTheory.CapelliUniv.qdet_map (stabD W').val E' _).symm
    have e2 : (((List.ofFn fun i : Fin 3 => qdet (fun p q : Fin (dims n B.j i) =>
        E' (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩))
        (Y + ((dims n B.j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2)).prod : ↥(stabD W')) :
        Module.End ℂ X.V) = b := by
      have := map_list_prod (stabD W').val (List.ofFn fun i : Fin 3 => qdet (fun p q : Fin (dims n B.j i) =>
        E' (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩))
        (Y + ((dims n B.j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2))
      refine this.trans ?_
      rw [List.map_ofFn, hb]
      congr 2
      funext i
      exact (GlobalTheory.CapelliUniv.qdet_map (stabD W').val _ _).symm
    rw [Subalgebra.coe_sub, e1, e2] at h1
    exact h1
  have hC : D = qdet X.E (Y + ((n : ℂ) - 1) / 2) :=
    GlobalTheory.CompanionTheory.RgConjQdet.conjQdet n X B.U B.Ui B.hU B.hUi _
  have hDc : Commute D b := by
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun p q => Formalism.REAL.qDetCentral _ _ (Eb X B) hX _ _ _) _
  let Fb : Module.End ℂ X.V := b - Formalism.QuantumDeterminants.capP χ Y • 1
  let Dz : Module.End ℂ X.V := D - Formalism.QuantumDeterminants.capP χ Y • 1
  have hs : ∀ z : Module.End ℂ X.V, Commute z (Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) :=
    fun z => (Commute.one_right z).smul_right _
  have hc : Commute Fb Dz := (hDc.symm.sub_right (hs _)).sub_left ((hs D).symm.sub_right (hs _))
  have e2 := hc.mul_geom_sum₂ k
  have hz : Dz ^ k = 0 := by
    show (D - _) ^ k = 0
    rw [hC]; exact hk
  rw [hz, sub_zero] at e2
  have hFb : Fb ∈ stabD W' := Subalgebra.sub_mem _ (Subalgebra.list_prod_mem _ fun y hy => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact qdet_mem _ _ (fun p q => hE _ _) _) (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
  have hDz : Dz ∈ stabD W' := Subalgebra.sub_mem _ (qdet_mem _ _ hE _) (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
  have hG : ∑ i ∈ Finset.range k, Fb ^ i * Dz ^ (k - 1 - i) ∈ stabD W' :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hFb _) (Subalgebra.pow_mem _ hDz _)
  show (Fb ^ k).dualMap φ ∈ W'
  rw [← e2]
  show (∑ i ∈ Finset.range k, Fb ^ i * Dz ^ (k - 1 - i)).dualMap ((Fb - Dz).dualMap φ) ∈ W'
  refine hG _ ?_
  have e3 : Fb - Dz = -(D - b) := by simp [Fb, Dz]
  rw [e3]
  have : (-(D - b)).dualMap φ = -((D - b).dualMap φ) := by ext x; simp
  rw [this]
  exact W'.neg_mem hDb

end Grade

section Lin

open Polynomial

/- English proof (translation)
Use `open GlobalTheory.CompanionTheory.PolyNilGrad in`. Establish `hA : A * A + A = B.U * Matrix.diagonal (fun p => dG B p * dG B p + dG B p) * B.Ui`. Establish `e1 : A * A = B.U * (Matrix.diagonal (dG B) * Matrix.diagonal (dG B)) * B.Ui` using `by conv_lhs => rw [A_eq B]`. Rewrite using `[conj_mul]`. Establish `e2 : A = B.U * Matrix.diagonal (dG B) * B.Ui` using `A_eq B`.

Rewrite `e1` using `[Matrix.diagonal_mul_diagonal]`. Use `(congrArg₂ (· + ·) e1 e2).trans ?_` and prove the remaining obligations. Simplify using `only [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]`. Establish `htr : (A * A + A).trace = 2 * (B.j : ℂ)`. Rewrite using `[hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, B.hUi, Matrix.one_mul, Matrix.trace_diagonal]`.

Rewrite using `[← Equiv.sum_comp (stdBlocks (dims n B.j) B.hj), Fintype.sum_sigma, Fin.sum_univ_three]`. Establish `hb : ∀ (i : Fin 3) (p : Fin (dims n B.j i)), GlobalTheory.CompanionTheory.PolyNilGrad.dG B (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) = (![-1, 0, 1] : Fin 3 → ℂ) i`. Introduce `i p`. Simplify using `[GlobalTheory.CompanionTheory.PolyNilGrad.dG, bl]`. Simplify using `only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Establish `h0 : (![-1, 0, 1] : Fin 3 → ℂ) 0 = -1` using `rfl`. Establish `h1 : (![-1, 0, 1] : Fin 3 → ℂ) 1 = 0` using `rfl`. Establish `h2 : (![-1, 0, 1] : Fin 3 → ℂ) 2 = 1` using `rfl`. Establish `h3 : dims n B.j 2 = B.j` using `rfl`. Rewrite using `[h0, h1, h2, h3]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hj : (((1 / 2 : ℂ) • (A * A + A)).trace).re = B.j`. Rewrite using `[Matrix.trace_smul, htr]`. Simplify using the standard rewrite rules. Unfold `rhoA`.

Simplify using `only [hj]`.
-/
theorem rhoA_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) :
    rhoA A = (B.j : ℝ) * ((n : ℝ) - B.j) := by
  classical
  open GlobalTheory.CompanionTheory.PolyNilGrad in
  have hA : A * A + A = B.U * Matrix.diagonal (fun p => dG B p * dG B p + dG B p) * B.Ui := by
    have e1 : A * A = B.U * (Matrix.diagonal (dG B) * Matrix.diagonal (dG B)) * B.Ui := by
      conv_lhs => rw [A_eq B]
      rw [conj_mul]
    have e2 : A = B.U * Matrix.diagonal (dG B) * B.Ui := A_eq B
    rw [Matrix.diagonal_mul_diagonal] at e1
    refine (congrArg₂ (· + ·) e1 e2).trans ?_
    simp only [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  have htr : (A * A + A).trace = 2 * (B.j : ℂ) := by
    rw [hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, B.hUi, Matrix.one_mul, Matrix.trace_diagonal]
    rw [← Equiv.sum_comp (stdBlocks (dims n B.j) B.hj), Fintype.sum_sigma, Fin.sum_univ_three]
    have hb : ∀ (i : Fin 3) (p : Fin (dims n B.j i)),
        GlobalTheory.CompanionTheory.PolyNilGrad.dG B (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) = (![-1, 0, 1] : Fin 3 → ℂ) i := by
      intro i p
      simp [GlobalTheory.CompanionTheory.PolyNilGrad.dG, bl]
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h0 : (![-1, 0, 1] : Fin 3 → ℂ) 0 = -1 := rfl
    have h1 : (![-1, 0, 1] : Fin 3 → ℂ) 1 = 0 := rfl
    have h2 : (![-1, 0, 1] : Fin 3 → ℂ) 2 = 1 := rfl
    have h3 : dims n B.j 2 = B.j := rfl
    rw [h0, h1, h2, h3]
    ring
  have hj : (((1 / 2 : ℂ) • (A * A + A)).trace).re = B.j := by
    rw [Matrix.trace_smul, htr]
    simp
  unfold rhoA
  simp only [hj]

/- English proof (translation)
Proceed by induction on `r using Polynomial.induction_on with`. Consider the case `C a`. Establish `: (aeval T (C a)).dualMap φ - (C a).eval z • φ = 0`. Use extensionality with `x`. Simplify using `[Module.algebraMap_end_apply]`.

Rewrite using `[this]`. Conclude with `W'.zero_mem`. Consider the case `add p q hp hq`. Establish `: (aeval T (p + q)).dualMap φ - (p + q).eval z • φ = ((aeval T p).dualMap φ - p.eval z • φ) + ((aeval T q).dualMap φ - q.eval z • φ)`. Use extensionality with `x`.

Simplify using `only [map_add, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply, eval_add, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `W'.add_mem hp hq`. Consider the case `monomial k a ih`.

Establish `e : (aeval T (C a * X ^ (k + 1))).dualMap φ - (C a * X ^ (k + 1)).eval z • φ = T.dualMap ((aeval T (C a * X ^ k)).dualMap φ - (C a * X ^ k).eval z • φ) + (C a * X ^ k).eval z • (T.dualMap φ - z • φ)`. Establish `h1 : aeval T (C a * X ^ (k + 1)) = aeval T (C a * X ^ k) * T`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, aeval_X]`. Rewrite using `[h1]`. Use extensionality with `x`.

Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply, Module.End.mul_apply, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul, map_sub, map_smul, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `W'.add_mem (hT _ ih) (W'.smul_mem _ hz)`.
-/
theorem aeval_dual_mem {V : Type} [AddCommGroup V] [Module ℂ V] (W' : Submodule ℂ (Module.Dual ℂ V))
    (T : Module.End ℂ V) (hT : T ∈ stabD W') (φ : Module.Dual ℂ V) (z : ℂ) (hz : T.dualMap φ - z • φ ∈ W')
    (r : ℂ[X]) : (aeval T r).dualMap φ - r.eval z • φ ∈ W' := by
  induction r using Polynomial.induction_on with
  | C a =>
    have : (aeval T (C a)).dualMap φ - (C a).eval z • φ = 0 := by
      ext x
      simp [Module.algebraMap_end_apply]
    rw [this]
    exact W'.zero_mem
  | add p q hp hq =>
    have : (aeval T (p + q)).dualMap φ - (p + q).eval z • φ =
        ((aeval T p).dualMap φ - p.eval z • φ) + ((aeval T q).dualMap φ - q.eval z • φ) := by
      ext x
      simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply,
        eval_add, smul_eq_mul]
      ring
    rw [this]
    exact W'.add_mem hp hq
  | monomial k a ih =>
    have e : (aeval T (C a * X ^ (k + 1))).dualMap φ - (C a * X ^ (k + 1)).eval z • φ =
        T.dualMap ((aeval T (C a * X ^ k)).dualMap φ - (C a * X ^ k).eval z • φ) +
          (C a * X ^ k).eval z • (T.dualMap φ - z • φ) := by
      have h1 : aeval T (C a * X ^ (k + 1)) = aeval T (C a * X ^ k) * T := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [h1]
      ext x
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply,
        Module.End.mul_apply, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul, map_sub, map_smul, pow_succ]
      ring
    rw [e]
    exact W'.add_mem (hT _ ih) (W'.smul_mem _ hz)

/- English proof (translation)
Take `⟨t, ht⟩` from `hφ`. Establish `ht0 : t < s0`. Assume the negation of the conclusion as `hc`. Apply `hn` to reduce the goal to its premises. Establish `: φ = 0`.

Use extensionality with `u`. Use `ht u (F.mono _ _ (not_lt.1 hc) ?_)` and prove the remaining obligations. Simplify using `[hs0]`. Rewrite using `[this]`. Conclude with `W'.zero_mem`.

Use `set T := actM M.E A with hTdef`. Establish `hT : T ∈ stabD W'` using `actM_mem_stabD M W' hst A`. Establish `hex : ∃ m : ℕ, ∃ q : ℂ[X], q.Monic ∧ q.natDegree = m ∧ ∀ u, aeval T q u ∈ F.N t`. Take `⟨q, hq, hu⟩` from `hLF t`. Conclude with `⟨_, q, hq, rfl, hu⟩`.

Take `⟨q, hqm, hqd, hqu⟩` from `Nat.find_spec hex`. Establish `hmin` using `fun m => Nat.find_min hex (m := m)`. Establish `hroot : q.eval z = 0`. Assume the negation of the conclusion as `h0`. Apply `hn` to reduce the goal to its premises.

Establish `h1` using `aeval_dual_mem W' T hT φ z hz q`. Establish `h2 : (aeval T q).dualMap φ = 0`. Use extensionality with `u`. Conclude with `ht _ (hqu u)`. Rewrite `h1` using `[h2, zero_sub]`.

Establish `h3` using `W'.smul_mem (-(q.eval z)⁻¹) h1`. Establish `e : -(q.eval z)⁻¹ • -(q.eval z • φ) = φ`. Rewrite using `[smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Establish `hdvd : X - C z ∣ q` using `Polynomial.dvd_iff_isRoot.2 hroot`.

Take `⟨q₁, hq₁⟩` from `hdvd`. Establish `hq₁m : q₁.Monic` using `(monic_X_sub_C z).of_mul_monic_left (hq₁ ▸ hqm)`. Establish `hdeg : q.natDegree = q₁.natDegree + 1`. Rewrite using `[hq₁, (monic_X_sub_C z).natDegree_mul hq₁m, natDegree_X_sub_C]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnot` using `hmin q₁.natDegree (by omega)`. Use `push_neg at hnot`. Take `⟨u, hu⟩` from `hnot q₁ hq₁m rfl`. Use `(F.eig s0 t ht0 hs0 z _ hu ?_).2` and prove the remaining obligations. Use `hqu u` as an intermediate fact.

Rewrite `this` using `[hq₁, map_mul, map_sub, aeval_X, aeval_C]`. Simplify `this` using `[Module.algebraMap_end_apply, Module.End.mul_apply]`.
-/
theorem re_lt {n : ℕ} {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A)
    (W' : Submodule ℂ (Module.Dual ℂ M.V)) (φ : Module.Dual ℂ M.V) (z : ℂ) (s0 : ℝ)
    (hLF : LocFinA F) (hs0 : F.N s0 = ⊤) (hst : ∀ a b, ∀ ψ ∈ W', contraE M a b ψ ∈ W')
    (hφ : φ ∈ W F) (hn : φ ∉ W') (hz : φ ∘ₗ actM M.E A - z • φ ∈ W') : z.re < s0 := by
  classical
  obtain ⟨t, ht⟩ := hφ
  have ht0 : t < s0 := by
    by_contra hc
    apply hn
    have : φ = 0 := by
      ext u
      refine ht u (F.mono _ _ (not_lt.1 hc) ?_)
      simp [hs0]
    rw [this]
    exact W'.zero_mem
  set T := actM M.E A with hTdef
  have hT : T ∈ stabD W' := actM_mem_stabD M W' hst A
  have hex : ∃ m : ℕ, ∃ q : ℂ[X], q.Monic ∧ q.natDegree = m ∧ ∀ u, aeval T q u ∈ F.N t := by
    obtain ⟨q, hq, hu⟩ := hLF t
    exact ⟨_, q, hq, rfl, hu⟩
  obtain ⟨q, hqm, hqd, hqu⟩ := Nat.find_spec hex
  have hmin := fun m => Nat.find_min hex (m := m)
  have hroot : q.eval z = 0 := by
    by_contra h0
    apply hn
    have h1 := aeval_dual_mem W' T hT φ z hz q
    have h2 : (aeval T q).dualMap φ = 0 := by
      ext u
      exact ht _ (hqu u)
    rw [h2, zero_sub] at h1
    have h3 := W'.smul_mem (-(q.eval z)⁻¹) h1
    have e : -(q.eval z)⁻¹ • -(q.eval z • φ) = φ := by
      rw [smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rwa [e] at h3
  have hdvd : X - C z ∣ q := Polynomial.dvd_iff_isRoot.2 hroot
  obtain ⟨q₁, hq₁⟩ := hdvd
  have hq₁m : q₁.Monic := (monic_X_sub_C z).of_mul_monic_left (hq₁ ▸ hqm)
  have hdeg : q.natDegree = q₁.natDegree + 1 := by
    rw [hq₁, (monic_X_sub_C z).natDegree_mul hq₁m, natDegree_X_sub_C]
    ring
  have hnot := hmin q₁.natDegree (by omega)
  push_neg at hnot
  obtain ⟨u, hu⟩ := hnot q₁ hq₁m rfl
  refine (F.eig s0 t ht0 hs0 z _ hu ?_).2
  have := hqu u
  rw [hq₁, map_mul, map_sub, aeval_X, aeval_C] at this
  simpa [Module.algebraMap_end_apply, Module.End.mul_apply] using this

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg hp`. Use `⟨fun _ => 0, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.filter_empty, Finset.prod_empty] at hp ⊢`.

Establish `hd` using `congrArg natDegree hp`. Rewrite `hd` using `[natDegree_prod_of_monic _ _ fun i _ => hg i, natDegree_one]`. Use `(Finset.sum_eq_zero_iff.1 hd) i (Finset.mem_univ i)` as an intermediate fact. Conclude with `(hg i).natDegree_eq_zero.1 this`. Consider the case `insert a T ha ih`.

Introduce `g hg hp`. Rewrite `hp` using `[Finset.prod_insert ha]`. Establish `hroot : (∏ i, g i).eval (-χ a) = 0`. Rewrite using `[hp]`. Simplify using the standard rewrite rules.

Rewrite `hroot` using `[eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `hroot`. Establish `hdvd : X - C (-χ a) ∣ g i` using `Polynomial.dvd_iff_isRoot.2 hi`. Rewrite `hdvd` using `[map_neg, sub_neg_eq_add]`. Take `⟨g', hg'⟩` from `hdvd`.

Establish `hXm : (X + C (χ a)).Monic` using `monic_X_add_C _`. Establish `hg'm : g'.Monic` using `hXm.of_mul_monic_left (hg' ▸ hg i)`. Establish `hgu : ∀ j, (Function.update g i g' j).Monic`. Introduce `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `using hg'm`. Simplify `hg j` using `[hj]`. Establish `hprod : ∏ j, Function.update g i g' j = ∏ s ∈ T, (X + C (χ s))`. Use `mul_left_cancel₀ hXm.ne_zero ?_` and prove the remaining obligations.

Rewrite using `[← hp]`. Establish `e : ∏ j, g j = g i * ∏ j ∈ Finset.univ.erase i, g j` using `(Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm`. Establish `e2 : ∏ j, Function.update g i g' j = g' * ∏ j ∈ Finset.univ.erase i, g j`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj)]`. Rewrite using `[e, e2, hg', mul_assoc]`. Take `⟨L, hL⟩` from `ih _ hgu hprod`. Use `⟨Function.update L a i, fun j => ?_⟩` and prove the remaining obligations.

Establish `hfil : T.filter (fun s => Function.update L a i s = j) = T.filter (fun s => L s = j)`. Use `Finset.filter_congr fun s hs => ?_` and prove the remaining obligations. Establish `: s ≠ a` using `fun e => ha (e ▸ hs)`. Rewrite using `[Function.update_of_ne this]`. Rewrite using `[Finset.filter_insert, hfil]`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self, if_true]`. Rewrite using `[Finset.prod_insert (by simp [ha]), ← hL, Function.update_self, hg']`. Establish `: ¬ i = j` using `fun e => hj e.symm`.

Simplify using `only [Function.update_self, this, if_false]`. Rewrite using `[← hL, Function.update_of_ne hj]`.
-/
theorem label_of_prod {ι : Type} [DecidableEq ι] (χ : ι → ℂ) (T : Finset ι) :
    ∀ g : Fin 3 → ℂ[X], (∀ i, (g i).Monic) → ∏ i, g i = ∏ s ∈ T, (X + C (χ s)) →
      ∃ L : ι → Fin 3, ∀ i, g i = ∏ s ∈ T.filter (fun s => L s = i), (X + C (χ s)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro g hg hp
    refine ⟨fun _ => 0, fun i => ?_⟩
    simp only [Finset.filter_empty, Finset.prod_empty] at hp ⊢
    have hd := congrArg natDegree hp
    rw [natDegree_prod_of_monic _ _ fun i _ => hg i, natDegree_one] at hd
    have := (Finset.sum_eq_zero_iff.1 hd) i (Finset.mem_univ i)
    exact (hg i).natDegree_eq_zero.1 this
  | insert a T ha ih =>
    intro g hg hp
    rw [Finset.prod_insert ha] at hp
    have hroot : (∏ i, g i).eval (-χ a) = 0 := by
      rw [hp]
      simp
    rw [eval_prod, Finset.prod_eq_zero_iff] at hroot
    obtain ⟨i, -, hi⟩ := hroot
    have hdvd : X - C (-χ a) ∣ g i := Polynomial.dvd_iff_isRoot.2 hi
    rw [map_neg, sub_neg_eq_add] at hdvd
    obtain ⟨g', hg'⟩ := hdvd
    have hXm : (X + C (χ a)).Monic := monic_X_add_C _
    have hg'm : g'.Monic := hXm.of_mul_monic_left (hg' ▸ hg i)
    have hgu : ∀ j, (Function.update g i g' j).Monic := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hg'm
      · simpa [hj] using hg j
    have hprod : ∏ j, Function.update g i g' j = ∏ s ∈ T, (X + C (χ s)) := by
      refine mul_left_cancel₀ hXm.ne_zero ?_
      rw [← hp]
      have e : ∏ j, g j = g i * ∏ j ∈ Finset.univ.erase i, g j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      have e2 : ∏ j, Function.update g i g' j = g' * ∏ j ∈ Finset.univ.erase i, g j := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [e, e2, hg', mul_assoc]
    obtain ⟨L, hL⟩ := ih _ hgu hprod
    refine ⟨Function.update L a i, fun j => ?_⟩
    have hfil : T.filter (fun s => Function.update L a i s = j) = T.filter (fun s => L s = j) := by
      refine Finset.filter_congr fun s hs => ?_
      have : s ≠ a := fun e => ha (e ▸ hs)
      rw [Function.update_of_ne this]
    rw [Finset.filter_insert, hfil]
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, if_true]
      rw [Finset.prod_insert (by simp [ha]), ← hL, Function.update_self, hg']
    · have : ¬ i = j := fun e => hj e.symm
      simp only [Function.update_self, this, if_false]
      rw [← hL, Function.update_of_ne hj]

end Lin

section Joint

open Polynomial
open GlobalTheory.CompanionTheory.Dblock.CentreBlocks (sumPoly sumPoly_monic sumPoly_coeff sumPoly_eval)

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a`. Establish `: aeval T (C a) x = a • x` using `by simp [Module.algebraMap_end_apply]`. Rewrite using `[this]`. Conclude with `I.smul_mem a hx`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `I.add_mem hp hq`. Consider the case `monomial k a ih`. Establish `h1 : aeval T (C a * X ^ (k + 1)) = T * aeval T (C a * X ^ k)`.

Rewrite using `[show (C a * X ^ (k + 1) : ℂ[X]) = X * (C a * X ^ k) by ring, map_mul, aeval_X]`. Rewrite using `[h1, Module.End.mul_apply]`. Conclude with `hI _ ih`.
-/
theorem aeval_mem (I : Submodule ℂ Z) (T : Module.End ℂ Z) (hI : ∀ x ∈ I, T x ∈ I) (p : ℂ[X]) (x : Z) (hx : x ∈ I) :
    aeval T p x ∈ I := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : aeval T (C a) x = a • x := by simp [Module.algebraMap_end_apply]
    rw [this]
    exact I.smul_mem a hx
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact I.add_mem hp hq
  | monomial k a ih =>
    have h1 : aeval T (C a * X ^ (k + 1)) = T * aeval T (C a * X ^ k) := by
      rw [show (C a * X ^ (k + 1) : ℂ[X]) = X * (C a * X ^ k) by ring, map_mul, aeval_X]
    rw [h1, Module.End.mul_apply]
    exact hI _ ih

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `q hd hq x _ hx0 hqx`. It suffices to derive a contradiction.

Take `⟨c, rfl⟩` from `natDegree_eq_zero.1 hd`. Establish `hc : c ≠ 0` using `fun h => hq (by simp [h])`. Establish `: c • x = 0` using `by simpa [Module.algebraMap_end_apply] using hqx`. Conclude with `(smul_ne_zero hc hx0) this`. Consider the case `succ m ih`.

Introduce `q hd hq x hx hx0 hqx`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_root q (by`. Rewrite using `[degree_eq_natDegree hq, hd]`. Conclude with `Nat.succ_ne_zero m)` after adjusting the coercions. Take `⟨q₁, rfl⟩` from `Polynomial.dvd_iff_isRoot.2 hr`.

Establish `hq₁ : q₁ ≠ 0` using `fun h => hq (by simp [h])`. Establish `hdeg : q₁.natDegree = m`. Rewrite `hd` using `[natDegree_mul (X_sub_C_ne_zero r) hq₁, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hy : aeval T q₁ x = 0`.

Conclude with `ih q₁ hdeg hq₁ x hx hx0 hy`. Use `⟨r, _, aeval_mem I T hI q₁ x hx, hy, ?_⟩` and prove the remaining obligations. Rewrite `hqx` using `[map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply]`. Simplify `hqx` using `[Module.algebraMap_end_apply, sub_eq_zero]`.
-/
theorem exists_eig_of_poly (I : Submodule ℂ Z) (T : Module.End ℂ Z) (hI : ∀ x ∈ I, T x ∈ I) :
    ∀ (m : ℕ) (q : ℂ[X]), q.natDegree = m → q ≠ 0 → ∀ x ∈ I, x ≠ 0 → aeval T q x = 0 →
      ∃ r : ℂ, ∃ y ∈ I, y ≠ 0 ∧ T y = r • y := by
  intro m
  induction m with
  | zero =>
    intro q hd hq x _ hx0 hqx
    exfalso
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.1 hd
    have hc : c ≠ 0 := fun h => hq (by simp [h])
    have : c • x = 0 := by simpa [Module.algebraMap_end_apply] using hqx
    exact (smul_ne_zero hc hx0) this
  | succ m ih =>
    intro q hd hq x hx hx0 hqx
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q (by
      rw [degree_eq_natDegree hq, hd]
      exact_mod_cast Nat.succ_ne_zero m)
    obtain ⟨q₁, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hr
    have hq₁ : q₁ ≠ 0 := fun h => hq (by simp [h])
    have hdeg : q₁.natDegree = m := by
      rw [natDegree_mul (X_sub_C_ne_zero r) hq₁, natDegree_X_sub_C] at hd
      omega
    by_cases hy : aeval T q₁ x = 0
    · exact ih q₁ hdeg hq₁ x hx hx0 hy
    · refine ⟨r, _, aeval_mem I T hI q₁ x hx, hy, ?_⟩
      rw [map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply] at hqx
      simpa [Module.algebraMap_end_apply, sub_eq_zero] using hqx

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `I hI _`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff I).1 hI`. Conclude with `⟨x, hx, hx0, by simp⟩`.

Consider the case `insert a s ha ih`. Introduce `I hI hst`. Take `⟨q, hqm, hq0⟩` from `hi a (Finset.mem_insert_self a s)`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff I).1 hI`. Establish `hq1 : aeval (T a) q x = 0`.

Rewrite using `[aeval_def, hq0]`. Both sides reduce to the same expression. Take `⟨r, y, hy, hy0, hTy⟩` from `exists_eig_of_poly I (T a) (hst a) _ q rfl hqm.ne_zero x hx hx0 hq1`. Set `I' : Submodule ℂ Z` to `I ⊓ LinearMap.ker (T a - r • (1 : Module.End ℂ Z))`. Establish `hI' : I' ≠ ⊥` using `(Submodule.ne_bot_iff I').2 ⟨y, ⟨hy, by simp [hTy]⟩, hy0⟩`.

Establish `hst' : ∀ j, ∀ x ∈ I', T j x ∈ I'`. Introduce and unpack `j x ⟨hx1, hx2⟩`. Use `⟨hst j x hx1, ?_⟩` and prove the remaining obligations. Establish `h2 : T a x = r • x` using `by simpa [sub_eq_zero] using hx2`. Establish `e` using `LinearMap.congr_fun (hc a j).eq x`.

Simplify using `only [Module.End.mul_apply] at e`. Simplify using `[e, h2]`. Take `⟨v, hv, hv0, hθ⟩` from `ih (fun i hi' => hi i (Finset.mem_insert_of_mem hi')) I' hI' hst'`. Use `⟨v, hv.1, hv0, fun i hi' => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi' with rfl | hi'` into its components or cases.

Use `⟨r, ?_⟩` and prove the remaining obligations. Use `hv.2` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Conclude with `hθ i hi'`.
-/
theorem exists_joint_eig {ι : Type} [DecidableEq ι] (T : ι → Module.End ℂ Z) (hc : ∀ i j, Commute (T i) (T j))
    (s : Finset ι) (hi : ∀ i ∈ s, IsIntegral ℂ (T i)) :
    ∀ I : Submodule ℂ Z, I ≠ ⊥ → (∀ j, ∀ x ∈ I, T j x ∈ I) →
      ∃ v ∈ I, v ≠ 0 ∧ ∀ i ∈ s, ∃ θ : ℂ, T i v = θ • v := by
  induction s using Finset.induction_on with
  | empty =>
    intro I hI _
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI
    exact ⟨x, hx, hx0, by simp⟩
  | insert a s ha ih =>
    intro I hI hst
    obtain ⟨q, hqm, hq0⟩ := hi a (Finset.mem_insert_self a s)
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI
    have hq1 : aeval (T a) q x = 0 := by
      rw [aeval_def, hq0]; rfl
    obtain ⟨r, y, hy, hy0, hTy⟩ := exists_eig_of_poly I (T a) (hst a) _ q rfl hqm.ne_zero x hx hx0 hq1
    let I' : Submodule ℂ Z := I ⊓ LinearMap.ker (T a - r • (1 : Module.End ℂ Z))
    have hI' : I' ≠ ⊥ := (Submodule.ne_bot_iff I').2 ⟨y, ⟨hy, by simp [hTy]⟩, hy0⟩
    have hst' : ∀ j, ∀ x ∈ I', T j x ∈ I' := by
      rintro j x ⟨hx1, hx2⟩
      refine ⟨hst j x hx1, ?_⟩
      have h2 : T a x = r • x := by simpa [sub_eq_zero] using hx2
      have e := LinearMap.congr_fun (hc a j).eq x
      simp only [Module.End.mul_apply] at e
      simp [e, h2]
    obtain ⟨v, hv, hv0, hθ⟩ := ih (fun i hi' => hi i (Finset.mem_insert_of_mem hi')) I' hI' hst'
    refine ⟨v, hv.1, hv0, fun i hi' => ?_⟩
    rcases Finset.mem_insert.1 hi' with rfl | hi'
    · refine ⟨r, ?_⟩
      have := hv.2
      simpa [sub_eq_zero] using this
    · exact hθ i hi'

/- English proof (translation)
Use `natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [sumPoly_coeff, if_pos (by omega), h]; exact one_ne_zero)` and prove the remaining obligations. Use `natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_` and prove the remaining obligations. Rewrite using `[sumPoly_coeff, if_neg (by omega)]`.
-/
theorem natDegree_sumPoly (θ : ℕ → ℂ) (m : ℕ) (h : θ m = 1) : (sumPoly θ m).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [sumPoly_coeff, if_pos (by omega), h]; exact one_ne_zero)
  refine natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_
  rw [sumPoly_coeff, if_neg (by omega)]

/- English proof (translation)
Establish `e1 : (sumPoly θ (e + 1)).comp (X + C c) = ∑ k ∈ Finset.range (e + 1 + 1), C (θ k) * (X + C c) ^ k`. Use `map_sum (Polynomial.compRingHom (X + C c)) (fun k => C (θ k) * X ^ k) (Finset.range (e + 1 + 1))` as an intermediate fact. Simplify `this` using `[sumPoly, Polynomial.coe_compRingHom_apply]`. Rewrite using `[e1, finset_sum_coeff, Finset.sum_range_succ, Finset.sum_range_succ]`. Establish `e2 : ∑ x ∈ Finset.range e, (C (θ x) * (X + C c) ^ x).coeff e = 0`.

Use `Finset.sum_eq_zero fun k hk => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hk)]`. Simplify using the standard rewrite rules. Rewrite using `[e2, coeff_C_mul, coeff_C_mul, coeff_X_add_C_pow, coeff_X_add_C_pow, h]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_sumPoly_comp (θ : ℕ → ℂ) (e : ℕ) (h : θ (e + 1) = 1) (c : ℂ) :
    ((sumPoly θ (e + 1)).comp (X + C c)).coeff e = θ e + ((e : ℂ) + 1) * c := by
  have e1 : (sumPoly θ (e + 1)).comp (X + C c) = ∑ k ∈ Finset.range (e + 1 + 1), C (θ k) * (X + C c) ^ k := by
    have := map_sum (Polynomial.compRingHom (X + C c)) (fun k => C (θ k) * X ^ k) (Finset.range (e + 1 + 1))
    simpa [sumPoly, Polynomial.coe_compRingHom_apply] using this
  rw [e1, finset_sum_coeff, Finset.sum_range_succ, Finset.sum_range_succ]
  have e2 : ∑ x ∈ Finset.range e, (C (θ x) * (X + C c) ^ x).coeff e = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hk)]
    simp
  rw [e2, coeff_C_mul, coeff_C_mul, coeff_X_add_C_pow, coeff_X_add_C_pow, h]
  simp
  ring

/- English proof (translation)
Set `s : Set (Module.End ℂ Z)` to `Set.range fun p : Fin 3 × ℕ => a p.1 p.2`. Establish `hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x`. Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨q, rfl⟩`. Conclude with `(hcomm _ _ _ _).eq`. Establish `hint : ∀ i k, k < d i + 1 → IsIntegral ℂ (a i k)`.

Use `letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs`. Establish `hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s` using `fun i k => Algebra.subset_adjoin ⟨(i, k), rfl⟩`. Set `Pp : Fin 3 → (Algebra.adjoin ℂ s)[X]` to `fun i => sumPoly (fun k => ⟨a i k, hamem i k⟩) (d i)`. Establish `hPm : ∀ i, (Pp i).Monic` using `fun i => sumPoly_monic _ _ (Subtype.ext (ha1 i))`. Establish `hprod : ∀ u : ℂ, IsIntegral ℂ (∏ i ∈ Finset.univ, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s) (u + sh i)))`.

Introduce `u`. Take `⟨m, hm⟩` from `hnil u`. Generalize the expression as in `(∏ s, (u + χ s)) = Pu at hm`. Set `D : Fin 3 → Algebra.adjoin ℂ s` to `fun i => ∑ k ∈ Finset.range (d i + 1), (u + sh i) ^ k • ⟨a i k, hamem i k⟩`. Establish `hev : ∀ i, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s) (u + sh i)) = D i`.

Introduce `i`. Rewrite using `[sumPoly_eval]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_pow, mul_comm]`. Repeatedly rewrite using `[hev]`.

Establish `hD : ∀ i, (D i : Module.End ℂ Z) = ∑ k ∈ Finset.range (d i + 1), (u + sh i) ^ k • a i k` using `fun i => by`. Simplify using `[D]`. Set `b : Algebra.adjoin ℂ s` to `D 0 * D 1 * D 2`. Establish `hb : ∏ i ∈ Finset.univ, D i = b` using `Fin.prod_univ_three D`. Rewrite using `[hb]`.

Establish `hpow : (b - algebraMap ℂ _ Pu) ^ m = 0`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `e : (((b - algebraMap ℂ _ Pu) ^ m : Algebra.adjoin ℂ s) : Module.End ℂ Z) = (((D 0 : Module.End ℂ Z) * (D 1 : Module.End ℂ Z) * (D 2 : Module.End ℂ Z)) - Pu • (1 : Module.End ℂ Z)) ^ m`. Simplify using `[b, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e, hD, hD, hD, hm]`.

Both sides reduce to the same expression. Use `⟨(X - C Pu) ^ m, (monic_X_sub_C _).pow m, ?_⟩` and prove the remaining obligations. Simplify `hpow` using `[eval₂_pow, eval₂_sub, eval₂_X, eval₂_C]`. Establish `hcoef` using `GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.isIntegral_coeff_of_shifted_prod Pp sh Finset.univ (fun i _ => hPm i) hprod`. Introduce `i k hk`.

Use `hcoef i (Finset.mem_univ i) k` as an intermediate fact. Simplify using `only [Pp, sumPoly_coeff] at this`. Rewrite `this` using `[if_pos hk]`. Conclude with `this.map (Algebra.adjoin ℂ s).val`. Take `⟨v, -, hv0, hθ'⟩` from `exists_joint_eig (fun p : (_ : Fin 3) × ℕ => a p.1 p.2) (fun p q => hcomm _ _ _ _) (Finset.univ.sigma fun i => Finset.range (d i + 1)) (fun p hp => hint _ _ (Finset.mem_range.1 (Finset.mem_sigma.1 hp).2)) ⊤ top_ne_bot (fun _ _ _ => Submodule.mem_top)`.

Establish `hθ'' : ∀ i k, ∃ θ : ℂ, k < d i + 1 → a i k v = θ • v`. Introduce `i k`. Distinguish the cases in `hk : k < d i + 1`. Take `⟨θ, h⟩` from `hθ' ⟨i, k⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ i, Finset.mem_range.2 hk⟩)`. Conclude with `⟨θ, fun _ => h⟩`.

Conclude with `⟨0, fun h => absurd h hk⟩`. Use `choose θ hθ using hθ''`. Establish `hθd : ∀ i, θ i (d i) = 1`. Introduce `i`. Establish `h` using `hθ i (d i) (by omega)`.

Rewrite `h` using `[ha1, Module.End.one_apply]`. Establish `h2 : (θ i (d i) - 1) • v = 0` using `by rw [sub_smul, one_smul, ← h, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv0)`. Set `g : Fin 3 → ℂ[X]` to `fun i => (sumPoly (θ i) (d i)).comp (X + C (sh i))`. Establish `hgm : ∀ i, (g i).Monic` using `fun i => (sumPoly_monic _ _ (hθd i)).comp_X_add_C _`.

Establish `hgd : ∀ i, (g i).natDegree = d i` using `fun i => by`. Simplify using `only [g]`. Rewrite using `[natDegree_comp, natDegree_X_add_C, mul_one, natDegree_sumPoly _ _ (hθd i)]`. Establish `hDv : ∀ i (Y : ℂ), (∑ k ∈ Finset.range (d i + 1), (Y + sh i) ^ k • a i k) v = (g i).eval Y • v`. Introduce `i Y`.

Simplify using `only [g, eval_comp, sumPoly_eval, eval_add, eval_X, eval_C, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[hθ i k (Finset.mem_range.1 hk), smul_smul, mul_comm]`. Establish `hprodY : ∀ Y : ℂ, ∏ i, (g i).eval Y = ∏ s, (Y + χ s)`. Introduce `Y`.

Take `⟨m, hm⟩` from `hnil Y`. Use `set c : ℂ := (g 0).eval Y * (g 1).eval Y * (g 2).eval Y - ∏ s, (Y + χ s) with hcdef`. Use `set Op := (∑ k ∈ Finset.range (d 0 + 1), (Y + sh 0) ^ k • a 0 k) * (∑ k ∈ Finset.range (d 1 + 1), (Y + sh 1) ^ k • a 1 k) * (∑ k ∈ Finset.range (d 2 + 1), (Y + sh 2) ^ k • a 2 k) - (∏ s, (Y + χ s)) • (1 : Module.End ℂ Z) with hOp`. Establish `h1 : Op v = c • v`. Simplify using `only [hOp, hcdef, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul, hDv, map_smul, smul_smul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ m : ℕ, (Op ^ m) v = c ^ m • v`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ, mul_comm]`. Establish `h3` using `h2 m`. Rewrite `h3` using `[hm, LinearMap.zero_apply]`. Establish `h4 : c ^ m = 0` using `(smul_eq_zero.1 h3.symm).resolve_right hv0`.

Establish `h5 : c = 0`. Assume the negation of the conclusion as `hc`. Conclude with `pow_ne_zero m hc h4`. Rewrite using `[Fin.prod_univ_three]`. Conclude with `sub_eq_zero.1 h5`.

Establish `hpoly : ∏ i, g i = ∏ s ∈ (Finset.univ : Finset (Fin n)), (X + C (χ s))`. Use `Polynomial.funext fun Y => ?_` and prove the remaining obligations. Rewrite using `[eval_prod, eval_prod, hprodY]`. Simplify using the standard rewrite rules. Take `⟨L, hL⟩` from `label_of_prod χ Finset.univ g hgm hpoly`.

Use `⟨v, L, hv0, fun i => ?_, fun i Y => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `hgd i` as an intermediate fact. Rewrite `this` using `[hL i, natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]`. Simplify using `using this`. Rewrite using `[hDv, hL i, eval_prod]`.

Simplify using the standard rewrite rules. Take `⟨e, he⟩ : ∃ e, d i = e + 1` from `⟨d i - 1, by omega⟩`. Establish `h1 : (g i).nextCoeff = ∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s`. Rewrite using `[hL i, Monic.nextCoeff_prod _ _ fun s _ => monic_X_add_C _]`. Conclude with `Finset.sum_congr rfl fun s _ => nextCoeff_X_add_C _`.

Establish `h2 : (g i).nextCoeff = θ i e + ((e : ℂ) + 1) * sh i`. Rewrite using `[nextCoeff_of_natDegree_pos (by rw [hgd, he]; omega), hgd, he]`. Simplify using `only [g, he, Nat.add_sub_cancel]`. Conclude with `coeff_sumPoly_comp _ _ (he ▸ hθd i) _`. Rewrite using `[he, Nat.add_sub_cancel, hθ i e (by omega), ← h1, h2]`.

Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem joint_label {n : ℕ} [Nontrivial Z] (χ : Fin n → ℂ) (d : Fin 3 → ℕ)
    (sh : Fin 3 → ℂ) (a : Fin 3 → ℕ → Module.End ℂ Z) (ha1 : ∀ i, a i (d i) = 1)
    (hcomm : ∀ i j k l, Commute (a i k) (a j l))
    (hnil : ∀ Y : ℂ, ∃ m : ℕ, ((∑ k ∈ Finset.range (d 0 + 1), (Y + sh 0) ^ k • a 0 k) *
      (∑ k ∈ Finset.range (d 1 + 1), (Y + sh 1) ^ k • a 1 k) *
      (∑ k ∈ Finset.range (d 2 + 1), (Y + sh 2) ^ k • a 2 k) -
      (∏ s, (Y + χ s)) • (1 : Module.End ℂ Z)) ^ m = 0) :
    ∃ (v : Z) (L : Fin n → Fin 3), v ≠ 0 ∧ (∀ i, (Finset.univ.filter fun s => L s = i).card = d i) ∧
      (∀ i (Y : ℂ), (∑ k ∈ Finset.range (d i + 1), (Y + sh i) ^ k • a i k) v =
        (∏ s ∈ Finset.univ.filter (fun s => L s = i), (Y + χ s)) • v) ∧
      ∀ i, 1 ≤ d i → a i (d i - 1) v =
        (∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s - (d i : ℂ) * sh i) • v := by
  classical
  let s : Set (Module.End ℂ Z) := Set.range fun p : Fin 3 × ℕ => a p.1 p.2
  have hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hcomm _ _ _ _).eq
  have hint : ∀ i k, k < d i + 1 → IsIntegral ℂ (a i k) := by
    letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs
    have hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s := fun i k => Algebra.subset_adjoin ⟨(i, k), rfl⟩
    let Pp : Fin 3 → (Algebra.adjoin ℂ s)[X] := fun i => sumPoly (fun k => ⟨a i k, hamem i k⟩) (d i)
    have hPm : ∀ i, (Pp i).Monic := fun i => sumPoly_monic _ _ (Subtype.ext (ha1 i))
    have hprod : ∀ u : ℂ, IsIntegral ℂ (∏ i ∈ Finset.univ, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s) (u + sh i))) := by
      intro u
      obtain ⟨m, hm⟩ := hnil u
      generalize (∏ s, (u + χ s)) = Pu at hm
      let D : Fin 3 → Algebra.adjoin ℂ s := fun i => ∑ k ∈ Finset.range (d i + 1), (u + sh i) ^ k • ⟨a i k, hamem i k⟩
      have hev : ∀ i, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s) (u + sh i)) = D i := by
        intro i
        rw [sumPoly_eval]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def, map_pow, mul_comm]
      simp_rw [hev]
      have hD : ∀ i, (D i : Module.End ℂ Z) = ∑ k ∈ Finset.range (d i + 1), (u + sh i) ^ k • a i k := fun i => by
        simp [D]
      let b : Algebra.adjoin ℂ s := D 0 * D 1 * D 2
      have hb : ∏ i ∈ Finset.univ, D i = b := Fin.prod_univ_three D
      rw [hb]
      have hpow : (b - algebraMap ℂ _ Pu) ^ m = 0 := by
        refine Subtype.ext ?_
        have e : (((b - algebraMap ℂ _ Pu) ^ m : Algebra.adjoin ℂ s) : Module.End ℂ Z) =
            (((D 0 : Module.End ℂ Z) * (D 1 : Module.End ℂ Z) * (D 2 : Module.End ℂ Z)) -
              Pu • (1 : Module.End ℂ Z)) ^ m := by
          simp [b, Algebra.algebraMap_eq_smul_one]
        rw [e, hD, hD, hD, hm]
        rfl
      refine ⟨(X - C Pu) ^ m, (monic_X_sub_C _).pow m, ?_⟩
      simpa [eval₂_pow, eval₂_sub, eval₂_X, eval₂_C] using hpow
    have hcoef := GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.isIntegral_coeff_of_shifted_prod Pp sh Finset.univ
      (fun i _ => hPm i) hprod
    intro i k hk
    have := hcoef i (Finset.mem_univ i) k
    simp only [Pp, sumPoly_coeff] at this
    rw [if_pos hk] at this
    exact this.map (Algebra.adjoin ℂ s).val
  obtain ⟨v, -, hv0, hθ'⟩ := exists_joint_eig (fun p : (_ : Fin 3) × ℕ => a p.1 p.2)
    (fun p q => hcomm _ _ _ _) (Finset.univ.sigma fun i => Finset.range (d i + 1))
    (fun p hp => hint _ _ (Finset.mem_range.1 (Finset.mem_sigma.1 hp).2)) ⊤ top_ne_bot (fun _ _ _ => Submodule.mem_top)
  have hθ'' : ∀ i k, ∃ θ : ℂ, k < d i + 1 → a i k v = θ • v := by
    intro i k
    by_cases hk : k < d i + 1
    · obtain ⟨θ, h⟩ := hθ' ⟨i, k⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ i, Finset.mem_range.2 hk⟩)
      exact ⟨θ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose θ hθ using hθ''
  have hθd : ∀ i, θ i (d i) = 1 := by
    intro i
    have h := hθ i (d i) (by omega)
    rw [ha1, Module.End.one_apply] at h
    have h2 : (θ i (d i) - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv0)
  let g : Fin 3 → ℂ[X] := fun i => (sumPoly (θ i) (d i)).comp (X + C (sh i))
  have hgm : ∀ i, (g i).Monic := fun i => (sumPoly_monic _ _ (hθd i)).comp_X_add_C _
  have hgd : ∀ i, (g i).natDegree = d i := fun i => by
    simp only [g]
    rw [natDegree_comp, natDegree_X_add_C, mul_one, natDegree_sumPoly _ _ (hθd i)]
  have hDv : ∀ i (Y : ℂ), (∑ k ∈ Finset.range (d i + 1), (Y + sh i) ^ k • a i k) v = (g i).eval Y • v := by
    intro i Y
    simp only [g, eval_comp, sumPoly_eval, eval_add, eval_X, eval_C, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hθ i k (Finset.mem_range.1 hk), smul_smul, mul_comm]
  have hprodY : ∀ Y : ℂ, ∏ i, (g i).eval Y = ∏ s, (Y + χ s) := by
    intro Y
    obtain ⟨m, hm⟩ := hnil Y
    set c : ℂ := (g 0).eval Y * (g 1).eval Y * (g 2).eval Y - ∏ s, (Y + χ s) with hcdef
    set Op := (∑ k ∈ Finset.range (d 0 + 1), (Y + sh 0) ^ k • a 0 k) *
      (∑ k ∈ Finset.range (d 1 + 1), (Y + sh 1) ^ k • a 1 k) *
      (∑ k ∈ Finset.range (d 2 + 1), (Y + sh 2) ^ k • a 2 k) -
      (∏ s, (Y + χ s)) • (1 : Module.End ℂ Z) with hOp
    have h1 : Op v = c • v := by
      simp only [hOp, hcdef, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_smul, hDv, map_smul, smul_smul]
      congr 2
      ring
    have h2 : ∀ m : ℕ, (Op ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have h3 := h2 m
    rw [hm, LinearMap.zero_apply] at h3
    have h4 : c ^ m = 0 := (smul_eq_zero.1 h3.symm).resolve_right hv0
    have h5 : c = 0 := by
      by_contra hc
      exact pow_ne_zero m hc h4
    rw [Fin.prod_univ_three]
    exact sub_eq_zero.1 h5
  have hpoly : ∏ i, g i = ∏ s ∈ (Finset.univ : Finset (Fin n)), (X + C (χ s)) := by
    refine Polynomial.funext fun Y => ?_
    rw [eval_prod, eval_prod, hprodY]
    simp
  obtain ⟨L, hL⟩ := label_of_prod χ Finset.univ g hgm hpoly
  refine ⟨v, L, hv0, fun i => ?_, fun i Y => ?_, fun i hi => ?_⟩
  · have := hgd i
    rw [hL i, natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _] at this
    simpa using this
  · rw [hDv, hL i, eval_prod]
    simp
  · obtain ⟨e, he⟩ : ∃ e, d i = e + 1 := ⟨d i - 1, by omega⟩
    have h1 : (g i).nextCoeff = ∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s := by
      rw [hL i, Monic.nextCoeff_prod _ _ fun s _ => monic_X_add_C _]
      exact Finset.sum_congr rfl fun s _ => nextCoeff_X_add_C _
    have h2 : (g i).nextCoeff = θ i e + ((e : ℂ) + 1) * sh i := by
      rw [nextCoeff_of_natDegree_pos (by rw [hgd, he]; omega), hgd, he]
      simp only [g, he, Nat.add_sub_cancel]
      exact coeff_sumPoly_comp _ _ (he ▸ hθd i) _
    rw [he, Nat.add_sub_cancel, hθ i e (by omega), ← h1, h2]
    push_cast
    ring_nf

end Joint

section MainPart

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin 3 => (0 : Fin 3) < b) = {1, 2}` using `by decide`. Establish `h2 : (Finset.univ.filter fun b : Fin 3 => b < (0 : Fin 3)) = ∅` using `by decide`. Simplify using `[modExp, h1, h2]`.
-/
theorem modExp_zero (d : Fin 3 → ℕ) : modExp (fun i => Fin (d i)) 0 = (d 1 : ℤ) + d 2 := by
  have h1 : (Finset.univ.filter fun b : Fin 3 => (0 : Fin 3) < b) = {1, 2} := by decide
  have h2 : (Finset.univ.filter fun b : Fin 3 => b < (0 : Fin 3)) = ∅ := by decide
  simp [modExp, h1, h2]

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin 3 => (2 : Fin 3) < b) = ∅` using `by decide`. Establish `h2 : (Finset.univ.filter fun b : Fin 3 => b < (2 : Fin 3)) = {0, 1}` using `by decide`. Simplify using `[modExp, h1, h2]`.
-/
theorem modExp_two (d : Fin 3 → ℕ) : modExp (fun i => Fin (d i)) 2 = -((d 0 : ℤ) + d 1) := by
  have h1 : (Finset.univ.filter fun b : Fin 3 => (2 : Fin 3) < b) = ∅ := by decide
  have h2 : (Finset.univ.filter fun b : Fin 3 => b < (2 : Fin 3)) = {0, 1} := by decide
  simp [modExp, h1, h2]

/- English proof (translation)
Rewrite using `[modExp_zero, modExp_two]`. Establish `h0 : dims n j 0 = j` using `rfl`. Establish `h2 : dims n j 2 = j` using `rfl`. Establish `h1 : (dims n j 1 : ℂ) = (n : ℂ) - 2 * j`. Establish `: dims n j 0 + dims n j 1 + dims n j 2 = n` using `by rw [← Fin.sum_univ_three]; exact hj`.

Rewrite `this` using `[h0, h2]`. Establish `e : ((j + dims n j 1 + j : ℕ) : ℂ) = n` using `by rw [this]`. Move the coercions through the operations in `at e`. Take the linear combination `e`. Use `push_cast`.

Rewrite using `[h0, h2, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degree_eq (n j : ℕ) (hj : ∑ i, dims n j i = n) (c0 c2 : ℂ) :
    (-(c0 - (dims n j 0 : ℂ) * (((dims n j 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n j i)) 0 : ℂ) / 2) +
      (dims n j 0 : ℂ) * ((dims n j 0 : ℂ) - 1) / 2) +
      (c2 - (dims n j 2 : ℂ) * (((dims n j 2 : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n j i)) 2 : ℂ) / 2) +
      (dims n j 2 : ℂ) * ((dims n j 2 : ℂ) - 1) / 2)) = c2 - c0 - (j : ℂ) * ((n : ℂ) - j) := by
  rw [modExp_zero, modExp_two]
  have h0 : dims n j 0 = j := rfl
  have h2 : dims n j 2 = j := rfl
  have h1 : (dims n j 1 : ℂ) = (n : ℂ) - 2 * j := by
    have : dims n j 0 + dims n j 1 + dims n j 2 = n := by rw [← Fin.sum_univ_three]; exact hj
    rw [h0, h2] at this
    have e : ((j + dims n j 1 + j : ℕ) : ℂ) = n := by rw [this]
    push_cast at e
    linear_combination e
  push_cast
  rw [h0, h2, h1]
  ring

end MainPart

section Assemble

variable {n : ℕ}

def Xb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (i : Fin 3) (p q : Fin (dims n B.j i)) :
    Module.End ℂ X.V :=
  Eb X B (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩)

def shB (n j : ℕ) (i : Fin 3) : ℂ :=
  ((dims n j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n j i)) i : ℂ) / 2

/- English proof (translation)
Unfold `Qb shB`. Rewrite using `[add_sub_assoc]`. Both sides reduce to the same expression.
-/
theorem Qb_eq (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (i : Fin 3) (Y : ℂ) :
    Qb X B i Y = qdet (Xb X B i) (Y + shB n B.j i) := by
  unfold Qb shB
  rw [add_sub_assoc]
  rfl

/- English proof (translation)
Establish `hX : GlRel (Eb X B)` using `GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B`. Establish `hinj : ∀ i : Fin 3, Function.Injective fun p : Fin (dims n B.j i) => stdBlocks (dims n B.j) B.hj ⟨i, p⟩` using `fun i => (stdBlocks (dims n B.j) B.hj).injective.comp sigma_mk_injective`. Establish `hne : ∀ (i j : Fin 3) (p : Fin (dims n B.j i)) (r : Fin (dims n B.j j)), i ≠ j → stdBlocks (dims n B.j) B.hj ⟨i, p⟩ ≠ stdBlocks (dims n B.j) B.hj ⟨j, r⟩`. Introduce `i j p r hij e`. Conclude with `hij (congrArg Sigma.fst ((stdBlocks (dims n B.j) B.hj).injective e))`.

Establish `hglr : ∀ i, GlRel (Xb X B i)` using `fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)`. Establish `hcm : ∀ i j, i ≠ j → ∀ p q r v, Commute (Xb X B i p q) (Xb X B j r v)`. Introduce `i j hij p q r v`. Use `hX (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩) (stdBlocks (dims n B.j) B.hj ⟨j, r⟩) (stdBlocks (dims n B.j) B.hj ⟨j, v⟩)` as an intermediate fact. Rewrite `this` using `[if_neg (hne _ _ _ _ hij), if_neg (hne _ _ _ _ (Ne.symm hij)), sub_self]`.

Conclude with `sub_eq_zero.1 this`. Conclude with `GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute X.V 3 (dims n B.j) (Xb X B) hglr hcm`.
-/
theorem exists_coefs (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) :
    ∃ a : Fin 3 → ℕ → Module.End ℂ X.V, (∀ i, a i (dims n B.j i) = 1) ∧
      (∀ i (u : ℂ), qdet (Xb X B i) u = ∑ k ∈ Finset.range (dims n B.j i + 1), u ^ k • a i k) ∧
      (∀ i, 1 ≤ dims n B.j i → a i (dims n B.j i - 1) = ∑ p, Xb X B i p p -
        ((dims n B.j i : ℂ) * ((dims n B.j i : ℂ) - 1) / 2) • 1) ∧
      ∀ i j k l, Commute (a i k) (a j l) := by
  have hX : GlRel (Eb X B) := GlobalTheory.CompanionTheory.PolyNilGrad.glRel_Eb X B
  have hinj : ∀ i : Fin 3, Function.Injective fun p : Fin (dims n B.j i) => stdBlocks (dims n B.j) B.hj ⟨i, p⟩ :=
    fun i => (stdBlocks (dims n B.j) B.hj).injective.comp sigma_mk_injective
  have hne : ∀ (i j : Fin 3) (p : Fin (dims n B.j i)) (r : Fin (dims n B.j j)), i ≠ j →
      stdBlocks (dims n B.j) B.hj ⟨i, p⟩ ≠ stdBlocks (dims n B.j) B.hj ⟨j, r⟩ := by
    intro i j p r hij e
    exact hij (congrArg Sigma.fst ((stdBlocks (dims n B.j) B.hj).injective e))
  have hglr : ∀ i, GlRel (Xb X B i) := fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)
  have hcm : ∀ i j, i ≠ j → ∀ p q r v, Commute (Xb X B i p q) (Xb X B j r v) := by
    intro i j hij p q r v
    have := hX (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩)
      (stdBlocks (dims n B.j) B.hj ⟨j, r⟩) (stdBlocks (dims n B.j) B.hj ⟨j, v⟩)
    rw [if_neg (hne _ _ _ _ hij), if_neg (hne _ _ _ _ (Ne.symm hij)), sub_self] at this
    exact sub_eq_zero.1 this
  exact GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute X.V 3 (dims n B.j) (Xb X B) hglr hcm

/- English proof (translation)
Introduce `n X A F B χ hLF hχ hs0 W' hle hst hne`. Take `⟨kc, hkc⟩` from `hχ`. Take `⟨a, ha1, hform, htr, hcomm⟩` from `exists_coefs X B`. Establish `hE : ∀ c e, Eb X B c e ∈ stabD W'` using `fun c e => actM_mem_stabD X W' hst _`. Set `S` to `Sk F B W'`.

Set `Bb : Subalgebra ℂ (Module.End ℂ X.V)` to `stabD S ⊓ stabD W'`. Establish `hXi : ∀ i p q, Xb X B i p q ∈ Bb` using `fun i p q => Algebra.mem_inf.2 ⟨levi_stab F B W' hst _ _ (by simp [bl]), hE _ _⟩`. Establish `hq : ∀ i t, qdet (Xb X B i) t ∈ Bb` using `fun i t => qdet_mem Bb _ (hXi i) t`. Establish `ha : ∀ i k, k < dims n B.j i + 1 → a i k ∈ Bb` using `fun i k hk => coef_mem (Subalgebra.toSubmodule Bb) _ (a i) (fun t => by rw [← hform]; exact hq i t) k hk`. Set `aB : Fin 3 → ℕ → ↥Bb` to `fun i k => if h : a i k ∈ Bb then ⟨a i k, h⟩ else 0`.

Establish `haB : ∀ i k, k < dims n B.j i + 1 → (aB i k : Module.End ℂ X.V) = a i k` using `fun i k hk => by`. Simplify using `only [aB]`. Rewrite using `[dif_pos (ha i k hk)]`. Establish `hcomB : ∀ i j k l, Commute (aB i k) (aB j l)`. Introduce `i j k l`.

Simplify using `only [aB]`. Use `split_ifs with h1 h2`. Conclude with `Subtype.ext (hcomm i j k l).eq`. Conclude with `Commute.zero_right _`. Conclude with `Commute.zero_left _`.

Conclude with `Commute.zero_left _`. Set `a' : Fin 3 → ℕ → Module.End ℂ (ZQ S W')` to `fun i k => rho S W' (aB i k)`. Set `qB : Fin 3 → ℂ → ↥Bb` to `fun i Y => ∑ k ∈ Finset.range (dims n B.j i + 1), (Y + shB n B.j i) ^ k • aB i k`. Establish `hqB : ∀ i Y, (qB i Y : Module.End ℂ X.V) = Qb X B i Y` using `fun i Y => by`. Rewrite using `[Qb_eq, hform]`.

Simplify using `only [qB, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul]`. Conclude with `Finset.sum_congr rfl fun k hk => by rw [haB i k (Finset.mem_range.1 hk)]`. Establish `hD : ∀ i Y, ∑ k ∈ Finset.range (dims n B.j i + 1), (Y + shB n B.j i) ^ k • a' i k = rho S W' (qB i Y)` using `fun i Y => by simp only [qB, map_sum, map_smul, a']`. Establish `hcq : ∀ i j Y, Commute (qB i Y) (qB j Y)` using `fun i j Y => Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ((hcomB i j k l).smul_left _).smul_right _`. Establish `hcomm' : ∀ i j k l, Commute (a' i k) (a' j l)` using `fun i j k l => by show rho S W' _ * rho S W' _ = rho S W' _ * rho S W' _`.

Rewrite using `[← rho_mul, ← rho_mul, (hcomB i j k l).eq]`. Establish `ha1' : ∀ i, a' i (dims n B.j i) = 1` using `fun i => by`. Establish `e : aB i (dims n B.j i) = 1` using `Subtype.ext (by rw [haB i _ (by omega), ha1]; rfl)`. Simplify using `only [a', e, rho_one]`. Establish `hnil : ∀ Y : ℂ, ∃ m : ℕ, ((∑ k ∈ Finset.range (dims n B.j 0 + 1), (Y + shB n B.j 0) ^ k • a' 0 k) * (∑ k ∈ Finset.range (dims n B.j 1 + 1), (Y + shB n B.j 1) ^ k • a' 1 k) * (∑ k ∈ Finset.range (dims n B.j 2 + 1), (Y + shB n B.j 2) ^ k • a' 2 k) - (∏ s, (Y + χ s)) • (1 : Module.E …`.

Introduce `Y`. Use `⟨kc, ?_⟩` and prove the remaining obligations. Rewrite using `[hD, hD, hD]`. Establish `e : rho S W' (qB 0 Y) * rho S W' (qB 1 Y) * rho S W' (qB 2 Y) - (∏ s, (Y + χ s)) • (1 : Module.End ℂ (ZQ S W')) = rho S W' (qB 2 Y * (qB 1 Y * qB 0 Y) - (∏ s, (Y + χ s)) • (1 : ↥Bb))`. Rewrite using `[map_sub, map_smul, rho_one, rho_mul, rho_mul]`.

Rewrite using `[e, ← rho_pow]`. Use `rho_eq_zero S W' _ fun φ hφ => ?_` and prove the remaining obligations. Establish `hk` using `nil_key F B W' hst χ kc Y (hkc Y) φ hφ`. Establish `e2 : qB 2 Y * (qB 1 Y * qB 0 Y) = qB 0 Y * (qB 1 Y * qB 2 Y)`. Rewrite using `[← mul_assoc, (hcq 2 1 Y).eq, mul_assoc, (hcq 2 0 Y).eq, ← mul_assoc, (hcq 1 0 Y).eq, mul_assoc]`.

Establish `e3 : (((qB 2 Y * (qB 1 Y * qB 0 Y) - (∏ s, (Y + χ s)) • (1 : ↥Bb)) ^ kc : ↥Bb) : Module.End ℂ X.V) = ((List.ofFn fun i : Fin 3 => Qb X B i Y).prod - Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) ^ kc`. Rewrite using `[e2]`. Simplify using `only [SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_smul, OneMemClass.coe_one, hqB, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]`. Both sides reduce to the same expression. Rewrite using `[e3]`.

Conclude with `hk`. Use `haveI : Nontrivial (ZQ S W') := by`. Take `⟨φ, hφ, hn, hk⟩` from `exists_killed F B W' hle hne _ hs0`. Use `⟨⟨Submodule.Quotient.mk ⟨φ, hφ, hk⟩, 0, fun h => hn ?_⟩⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.mk_eq_zero (W'.comap S.subtype)).1 h`.

Take `⟨v, L, hv0, hcard, hev, hlast⟩` from `joint_label χ (dims n B.j) (shB n B.j) a' ha1' hcomm' hnil`. Take `⟨⟨φ, hφ⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Establish `hφn : φ ∉ W'` using `fun h => hv0 ((Submodule.Quotient.mk_eq_zero _).2 h)`. Establish `hevW : ∀ (T : ↥Bb) (c : ℂ), rho S W' T (Submodule.Quotient.mk ⟨φ, hφ⟩) = c • Submodule.Quotient.mk ⟨φ, hφ⟩ → (T : Module.End ℂ X.V).dualMap φ - c • φ ∈ W'`. Introduce `T c h`.

Rewrite `h` using `[rho_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Conclude with `h`. Establish `hQ : ∀ i Y, φ ∘ₗ Qb X B i Y - plab χ L i Y • φ ∈ W'` using `fun i Y => by`. Establish `h1` using `hev i Y`. Rewrite `h1` using `[hD]`.

Establish `h2` using `hevW _ _ h1`. Rewrite `h2` using `[hqB]`. Conclude with `h2`. Set `τ : Fin 3 → ℂ` to `fun i => ∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s - (dims n B.j i : ℂ) * shB n B.j i + (dims n B.j i : ℂ) * ((dims n B.j i : ℂ) - 1) / 2`. Establish `hτ : ∀ i, (∑ p, Xb X B i p p).dualMap φ - τ i • φ ∈ W'`.

Introduce `i`. Distinguish the cases in `h0 : 1 ≤ dims n B.j i`. Establish `h1` using `hevW _ _ (hlast i h0)`. Rewrite `h1` using `[haB i _ (by omega), htr i h0]`. Establish `e : (∑ p, Xb X B i p p).dualMap φ - τ i • φ = (∑ p, Xb X B i p p - ((dims n B.j i : ℂ) * ((dims n B.j i : ℂ) - 1) / 2) • (1 : Module.End ℂ X.V)).dualMap φ - (∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s - (dims n B.j i : ℂ) * shB n B.j i) • φ`.

Use extensionality with `x`. Simplify using `only [τ, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply, map_sub, map_smul, Module.End.one_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`.

Establish `hz : dims n B.j i = 0` using `by omega`. Establish `hemp : IsEmpty (Fin (dims n B.j i))` using `by rw [hz]; infer_instance`. Establish `h2 : Finset.univ.filter (fun s => L s = i) = ∅`. Use `hcard i` as an intermediate fact. Rewrite `this` using `[hz]`.

Conclude with `Finset.card_eq_zero.1 this`. Establish `e : (∑ p, Xb X B i p p).dualMap φ - τ i • φ = 0`. Use extensionality with `x`. Simplify using `[τ, h2, hz]`. Rewrite using `[e]`.

Conclude with `W'.zero_mem`. Set `z : ℂ` to `-τ 0 + τ 2`. Establish `hact : actM X.E A = -(∑ p, Xb X B 0 p p) + ∑ p, Xb X B 2 p p`. Establish `h1 : actM X.E A = CompanionTheory.RgExh.Dec.L.actM X A` using `rfl`. Rewrite using `[h1, GlobalTheory.CompanionTheory.PolyNilGrad.actM_grading X B, Fin.sum_univ_three]`.

Simplify using `[Xb]`. Establish `hz : φ ∘ₗ actM X.E A - z • φ ∈ W'`. Establish `e : φ ∘ₗ actM X.E A - z • φ = -((∑ p, Xb X B 0 p p).dualMap φ - τ 0 • φ) + ((∑ p, Xb X B 2 p p).dualMap φ - τ 2 • φ)`. Use extensionality with `x`. Simplify using `only [z, hact, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.dualMap_apply, map_add, map_neg, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `W'.add_mem (W'.neg_mem (hτ 0)) (hτ 2)`. Establish `hre : z.re < -rhoA A` using `re_lt F W' φ z _ hLF hs0 hst hφ.1 hφn hz`. Establish `hzd : z = deg χ L - (((B.j : ℝ) * ((n : ℝ) - B.j) : ℝ) : ℂ)`.

Use `degree_eq n B.j B.hj (∑ s ∈ Finset.univ.filter (fun s => L s = 0), χ s) (∑ s ∈ Finset.univ.filter (fun s => L s = 2), χ s)` as an intermediate fact. Simplify using `only [z, τ, shB, deg]`. Use `push_cast`. Conclude with `this`. Establish `hdeg : (deg χ L).re < 0`.

Rewrite `hre` using `[hzd, rhoA_eq B, Complex.sub_re, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨φ, hφ.1, hφn, hφ.2, L, ⟨hcard, hdeg⟩, hcard, hQ⟩`.
-/
theorem start1 : Start1 := by
  intro n X A F B χ hLF hχ hs0 W' hle hst hne
  classical
  obtain ⟨kc, hkc⟩ := hχ
  obtain ⟨a, ha1, hform, htr, hcomm⟩ := exists_coefs X B
  have hE : ∀ c e, Eb X B c e ∈ stabD W' := fun c e => actM_mem_stabD X W' hst _
  let S := Sk F B W'
  let Bb : Subalgebra ℂ (Module.End ℂ X.V) := stabD S ⊓ stabD W'
  have hXi : ∀ i p q, Xb X B i p q ∈ Bb := fun i p q => Algebra.mem_inf.2
    ⟨levi_stab F B W' hst _ _ (by simp [bl]), hE _ _⟩
  have hq : ∀ i t, qdet (Xb X B i) t ∈ Bb := fun i t => qdet_mem Bb _ (hXi i) t
  have ha : ∀ i k, k < dims n B.j i + 1 → a i k ∈ Bb := fun i k hk =>
    coef_mem (Subalgebra.toSubmodule Bb) _ (a i) (fun t => by rw [← hform]; exact hq i t) k hk
  let aB : Fin 3 → ℕ → ↥Bb := fun i k => if h : a i k ∈ Bb then ⟨a i k, h⟩ else 0
  have haB : ∀ i k, k < dims n B.j i + 1 → (aB i k : Module.End ℂ X.V) = a i k := fun i k hk => by
    simp only [aB]
    rw [dif_pos (ha i k hk)]
  have hcomB : ∀ i j k l, Commute (aB i k) (aB j l) := by
    intro i j k l
    simp only [aB]
    split_ifs with h1 h2
    · exact Subtype.ext (hcomm i j k l).eq
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  let a' : Fin 3 → ℕ → Module.End ℂ (ZQ S W') := fun i k => rho S W' (aB i k)
  let qB : Fin 3 → ℂ → ↥Bb := fun i Y => ∑ k ∈ Finset.range (dims n B.j i + 1), (Y + shB n B.j i) ^ k • aB i k
  have hqB : ∀ i Y, (qB i Y : Module.End ℂ X.V) = Qb X B i Y := fun i Y => by
    rw [Qb_eq, hform]
    simp only [qB, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul]
    exact Finset.sum_congr rfl fun k hk => by rw [haB i k (Finset.mem_range.1 hk)]
  have hD : ∀ i Y, ∑ k ∈ Finset.range (dims n B.j i + 1), (Y + shB n B.j i) ^ k • a' i k = rho S W' (qB i Y) :=
    fun i Y => by simp only [qB, map_sum, map_smul, a']
  have hcq : ∀ i j Y, Commute (qB i Y) (qB j Y) := fun i j Y =>
    Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ =>
      ((hcomB i j k l).smul_left _).smul_right _
  have hcomm' : ∀ i j k l, Commute (a' i k) (a' j l) := fun i j k l => by
    show rho S W' _ * rho S W' _ = rho S W' _ * rho S W' _
    rw [← rho_mul, ← rho_mul, (hcomB i j k l).eq]
  have ha1' : ∀ i, a' i (dims n B.j i) = 1 := fun i => by
    have e : aB i (dims n B.j i) = 1 := Subtype.ext (by rw [haB i _ (by omega), ha1]; rfl)
    simp only [a', e, rho_one]
  have hnil : ∀ Y : ℂ, ∃ m : ℕ, ((∑ k ∈ Finset.range (dims n B.j 0 + 1), (Y + shB n B.j 0) ^ k • a' 0 k) *
      (∑ k ∈ Finset.range (dims n B.j 1 + 1), (Y + shB n B.j 1) ^ k • a' 1 k) *
      (∑ k ∈ Finset.range (dims n B.j 2 + 1), (Y + shB n B.j 2) ^ k • a' 2 k) -
      (∏ s, (Y + χ s)) • (1 : Module.End ℂ (ZQ S W'))) ^ m = 0 := by
    intro Y
    refine ⟨kc, ?_⟩
    rw [hD, hD, hD]
    have e : rho S W' (qB 0 Y) * rho S W' (qB 1 Y) * rho S W' (qB 2 Y) - (∏ s, (Y + χ s)) • (1 : Module.End ℂ (ZQ S W')) =
        rho S W' (qB 2 Y * (qB 1 Y * qB 0 Y) - (∏ s, (Y + χ s)) • (1 : ↥Bb)) := by
      rw [map_sub, map_smul, rho_one, rho_mul, rho_mul]
    rw [e, ← rho_pow]
    refine rho_eq_zero S W' _ fun φ hφ => ?_
    have hk := nil_key F B W' hst χ kc Y (hkc Y) φ hφ
    have e2 : qB 2 Y * (qB 1 Y * qB 0 Y) = qB 0 Y * (qB 1 Y * qB 2 Y) := by
      rw [← mul_assoc, (hcq 2 1 Y).eq, mul_assoc, (hcq 2 0 Y).eq, ← mul_assoc, (hcq 1 0 Y).eq, mul_assoc]
    have e3 : (((qB 2 Y * (qB 1 Y * qB 0 Y) - (∏ s, (Y + χ s)) • (1 : ↥Bb)) ^ kc : ↥Bb) : Module.End ℂ X.V) =
        ((List.ofFn fun i : Fin 3 => Qb X B i Y).prod - Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) ^ kc := by
      rw [e2]
      simp only [SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_smul,
        OneMemClass.coe_one, hqB, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      rfl
    rw [e3]
    exact hk
  haveI : Nontrivial (ZQ S W') := by
    obtain ⟨φ, hφ, hn, hk⟩ := exists_killed F B W' hle hne _ hs0
    refine ⟨⟨Submodule.Quotient.mk ⟨φ, hφ, hk⟩, 0, fun h => hn ?_⟩⟩
    exact (Submodule.Quotient.mk_eq_zero (W'.comap S.subtype)).1 h
  obtain ⟨v, L, hv0, hcard, hev, hlast⟩ := joint_label χ (dims n B.j) (shB n B.j) a' ha1' hcomm' hnil
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hφn : φ ∉ W' := fun h => hv0 ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hevW : ∀ (T : ↥Bb) (c : ℂ), rho S W' T (Submodule.Quotient.mk ⟨φ, hφ⟩) = c • Submodule.Quotient.mk ⟨φ, hφ⟩ →
      (T : Module.End ℂ X.V).dualMap φ - c • φ ∈ W' := by
    intro T c h
    rw [rho_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h
    exact h
  have hQ : ∀ i Y, φ ∘ₗ Qb X B i Y - plab χ L i Y • φ ∈ W' := fun i Y => by
    have h1 := hev i Y
    rw [hD] at h1
    have h2 := hevW _ _ h1
    rw [hqB] at h2
    exact h2
  let τ : Fin 3 → ℂ := fun i => ∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s -
    (dims n B.j i : ℂ) * shB n B.j i + (dims n B.j i : ℂ) * ((dims n B.j i : ℂ) - 1) / 2
  have hτ : ∀ i, (∑ p, Xb X B i p p).dualMap φ - τ i • φ ∈ W' := by
    intro i
    by_cases h0 : 1 ≤ dims n B.j i
    · have h1 := hevW _ _ (hlast i h0)
      rw [haB i _ (by omega), htr i h0] at h1
      have e : (∑ p, Xb X B i p p).dualMap φ - τ i • φ =
          (∑ p, Xb X B i p p - ((dims n B.j i : ℂ) * ((dims n B.j i : ℂ) - 1) / 2) • (1 : Module.End ℂ X.V)).dualMap φ -
            (∑ s ∈ Finset.univ.filter (fun s => L s = i), χ s - (dims n B.j i : ℂ) * shB n B.j i) • φ := by
        ext x
        simp only [τ, LinearMap.sub_apply, LinearMap.dualMap_apply, LinearMap.smul_apply, map_sub, map_smul,
          Module.End.one_apply, smul_eq_mul]
        ring
      rw [e]
      exact h1
    · have hz : dims n B.j i = 0 := by omega
      have hemp : IsEmpty (Fin (dims n B.j i)) := by rw [hz]; infer_instance
      have h2 : Finset.univ.filter (fun s => L s = i) = ∅ := by
        have := hcard i
        rw [hz] at this
        exact Finset.card_eq_zero.1 this
      have e : (∑ p, Xb X B i p p).dualMap φ - τ i • φ = 0 := by
        ext x
        simp [τ, h2, hz]
      rw [e]
      exact W'.zero_mem
  let z : ℂ := -τ 0 + τ 2
  have hact : actM X.E A = -(∑ p, Xb X B 0 p p) + ∑ p, Xb X B 2 p p := by
    have h1 : actM X.E A = CompanionTheory.RgExh.Dec.L.actM X A := rfl
    rw [h1, GlobalTheory.CompanionTheory.PolyNilGrad.actM_grading X B, Fin.sum_univ_three]
    simp [Xb]
  have hz : φ ∘ₗ actM X.E A - z • φ ∈ W' := by
    have e : φ ∘ₗ actM X.E A - z • φ = -((∑ p, Xb X B 0 p p).dualMap φ - τ 0 • φ) +
        ((∑ p, Xb X B 2 p p).dualMap φ - τ 2 • φ) := by
      ext x
      simp only [z, hact, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
        LinearMap.smul_apply, LinearMap.dualMap_apply, map_add, map_neg, smul_eq_mul]
      ring
    rw [e]
    exact W'.add_mem (W'.neg_mem (hτ 0)) (hτ 2)
  have hre : z.re < -rhoA A := re_lt F W' φ z _ hLF hs0 hst hφ.1 hφn hz
  have hzd : z = deg χ L - (((B.j : ℝ) * ((n : ℝ) - B.j) : ℝ) : ℂ) := by
    have := degree_eq n B.j B.hj (∑ s ∈ Finset.univ.filter (fun s => L s = 0), χ s)
      (∑ s ∈ Finset.univ.filter (fun s => L s = 2), χ s)
    simp only [z, τ, shB, deg]
    push_cast
    exact this
  have hdeg : (deg χ L).re < 0 := by
    rw [hzd, rhoA_eq B, Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  exact ⟨φ, hφ.1, hφn, hφ.2, L, ⟨hcard, hdeg⟩, hcard, hQ⟩

end Assemble

end GlobalTheory.CompanionTheory.RgStartOne
