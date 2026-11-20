import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeAgreeOfTrivialAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneSubSmulPeirceCut

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.VacuumScalar

section Groups

variable {G : Type} [AddCommGroup G]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `h1 : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ≠ 1`. Introduce `h1`. Rewrite `h1` using `[AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff]`. Conclude with `hx h1`.

Take `⟨q, hq, hd⟩` from `Nat.exists_prime_and_dvd h1`. Take `⟨m, hm, hT⟩` from `h q hq`. Establish `: addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ∣ m`. Rewrite using `[addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `hT`.

Conclude with `(Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm (hd.trans this)`.
-/
theorem mem_of_local (T : AddSubgroup G) (x : G)
    (h : ∀ q : ℕ, q.Prime → ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ T) : x ∈ T := by
  by_contra hx
  have h1 : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ≠ 1 := by
    intro h1
    rw [AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff] at h1
    exact hx h1
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, hm, hT⟩ := h q hq
  have : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ∣ m := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hT
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm (hd.trans this)

def Nr (q : ℕ) (B C : AddSubgroup G) : Prop := ∀ x ∈ B, ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ C

/- English proof (translation)
Establish `e : B = C ⊔ (K ⊓ B)` using `le_antisymm h2 (sup_le h1 inf_le_right)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIndex_eq_of_le_sup {K C B : AddSubgroup G} (h1 : C ≤ B) (h2 : B ≤ C ⊔ (K ⊓ B)) :
    K.relIndex C = K.relIndex B := by
  have e : B = C ⊔ (K ⊓ B) := le_antisymm h2 (sup_le h1 inf_le_right)
  calc K.relIndex C = (K ⊓ C).relIndex C := (AddSubgroup.inf_relIndex_right _ _).symm
    _ = ((K ⊓ B) ⊓ C).relIndex C := by rw [inf_assoc, inf_eq_right.2 h1]
    _ = (K ⊓ B).relIndex C := AddSubgroup.inf_relIndex_right _ _
    _ = (K ⊓ B).relIndex (C ⊔ (K ⊓ B)) := (AddSubgroup.relIndex_sup_right _ _).symm
    _ = (K ⊓ B).relIndex B := by rw [← e]
    _ = K.relIndex B := AddSubgroup.inf_relIndex_right _ _

/- English proof (translation)
Introduce `x hx`. Use `mem_of_local _ x fun q hq => ?_` and prove the remaining obligations. Break down `h q hq with h | h` into its components or cases. Take `⟨m, hm, hC⟩` from `h x hx`. Conclude with `⟨m, hm, AddSubgroup.mem_sup_left ⟨B.nsmul_mem hx m, hC⟩⟩`.

Take `⟨m, hm, hC⟩` from `h x hx`. Conclude with `⟨m, hm, AddSubgroup.mem_sup_right ⟨hC, B.nsmul_mem hx m⟩⟩`.
-/
theorem le_sup_of_local {B C K : AddSubgroup G} (h : ∀ q : ℕ, q.Prime → Nr q B C ∨ Nr q B K) :
    B ≤ (B ⊓ C) ⊔ (K ⊓ B) := by
  intro x hx
  refine mem_of_local _ x fun q hq => ?_
  rcases h q hq with h | h
  · obtain ⟨m, hm, hC⟩ := h x hx
    exact ⟨m, hm, AddSubgroup.mem_sup_left ⟨B.nsmul_mem hx m, hC⟩⟩
  · obtain ⟨m, hm, hC⟩ := h x hx
    exact ⟨m, hm, AddSubgroup.mem_sup_right ⟨hC, B.nsmul_mem hx m⟩⟩

/- English proof (translation)
Introduce `x hx`. Use `mem_of_local _ x fun q hq => ?_` and prove the remaining obligations. Break down `h q hq with h | h` into its components or cases. Conclude with `h x hx.1`. Conclude with `h x hx.2`.
-/
theorem inf_le_of_local {B C K : AddSubgroup G} (h : ∀ q : ℕ, q.Prime → Nr q B K ∨ Nr q C K) :
    B ⊓ C ≤ K := by
  intro x hx
  refine mem_of_local _ x fun q hq => ?_
  rcases h q hq with h | h
  · exact h x hx.1
  · exact h x hx.2

/- English proof (translation)
Apply the tactic sequence `have h1 : A0 ⊓ A ≤ As := inf_le_of_local fun q hq => by rcases h q hq with h | h <;> tauto`. Apply the tactic sequence `have h2 : Ai ⊓ As ≤ A0 := inf_le_of_local fun q hq => by rcases h q hq with h | h <;> tauto`. Apply the tactic sequence `have h3 : As ≤ (As ⊓ A) ⊔ (A0 ⊓ As) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto`. Apply the tactic sequence `have h4 : A ≤ (A ⊓ Ai) ⊔ (As ⊓ A) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto`. Apply the tactic sequence `have h5 : Ai ≤ (Ai ⊓ A) ⊔ (A0 ⊓ Ai) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto`.

Establish `e1 : A0.relIndex A = (A0 ⊓ As).relIndex A`. Rewrite using `[← AddSubgroup.inf_relIndex_right A0 A, ← AddSubgroup.inf_relIndex_right (A0 ⊓ As) A]`. Use `congr 1`. Conclude with `le_antisymm (le_inf (le_inf inf_le_left h1) inf_le_right) (inf_le_inf_right _ inf_le_left)`. Establish `e2 : As.relIndex (A ⊓ Ai) = A0.relIndex (Ai ⊓ A)`.

Rewrite using `[inf_comm Ai A, ← AddSubgroup.inf_relIndex_right As, ← AddSubgroup.inf_relIndex_right A0]`. Use `congr 1`. Use `le_antisymm (le_inf ?_ inf_le_right) (le_inf ?_ inf_le_right)` and prove the remaining obligations. Conclude with `fun x hx => h2 ⟨hx.2.2, hx.1⟩`. Conclude with `fun x hx => h1 ⟨hx.1, hx.2.1⟩`.

Rewrite using `[e1, ← AddSubgroup.relIndex_inf_mul_relIndex, relIndex_eq_of_le_sup inf_le_left h3, ← relIndex_eq_of_le_sup inf_le_left h4, e2, relIndex_eq_of_le_sup inf_le_left h5, mul_comm]`.
-/
theorem index_mul {A A0 As Ai : AddSubgroup G}
    (h : ∀ q : ℕ, q.Prime → (Nr q As A0 ∧ Nr q A0 As ∧ Nr q A Ai ∧ Nr q Ai A) ∨
      (Nr q As A ∧ Nr q A As ∧ Nr q Ai A0 ∧ Nr q A0 Ai)) :
    A0.relIndex A = A0.relIndex Ai * A0.relIndex As := by
  have h1 : A0 ⊓ A ≤ As := inf_le_of_local fun q hq => by rcases h q hq with h | h <;> tauto
  have h2 : Ai ⊓ As ≤ A0 := inf_le_of_local fun q hq => by rcases h q hq with h | h <;> tauto
  have h3 : As ≤ (As ⊓ A) ⊔ (A0 ⊓ As) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto
  have h4 : A ≤ (A ⊓ Ai) ⊔ (As ⊓ A) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto
  have h5 : Ai ≤ (Ai ⊓ A) ⊔ (A0 ⊓ Ai) := le_sup_of_local fun q hq => by rcases h q hq with h | h <;> tauto
  have e1 : A0.relIndex A = (A0 ⊓ As).relIndex A := by
    rw [← AddSubgroup.inf_relIndex_right A0 A, ← AddSubgroup.inf_relIndex_right (A0 ⊓ As) A]
    congr 1
    exact le_antisymm (le_inf (le_inf inf_le_left h1) inf_le_right) (inf_le_inf_right _ inf_le_left)
  have e2 : As.relIndex (A ⊓ Ai) = A0.relIndex (Ai ⊓ A) := by
    rw [inf_comm Ai A, ← AddSubgroup.inf_relIndex_right As, ← AddSubgroup.inf_relIndex_right A0]
    congr 1
    refine le_antisymm (le_inf ?_ inf_le_right) (le_inf ?_ inf_le_right)
    · exact fun x hx => h2 ⟨hx.2.2, hx.1⟩
    · exact fun x hx => h1 ⟨hx.1, hx.2.1⟩
  rw [e1, ← AddSubgroup.relIndex_inf_mul_relIndex, relIndex_eq_of_le_sup inf_le_left h3,
    ← relIndex_eq_of_le_sup inf_le_left h4, e2, relIndex_eq_of_le_sup inf_le_left h5, mul_comm]

end Groups

section Cut

variable {R : Type} [CommRing R]

def cut {A : Type} [Ring A] [Algebra R A] (e : R) (he : e * e = e) : A →* A := GlobalTheory.PeirceDecompositionCut.peirceCut A e he

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cut_apply {A : Type} [Ring A] [Algebra R A] (e : R) (he : e * e = e) (a : A) :
    cut e he a = e • a + (1 - e) • 1 := rfl

/- English proof (translation)
Take the linear combination `he`.
-/
theorem compl_idem {e : R} (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination he

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`. Establish `h2` using `compl_idem he`. Apply the tactic sequence `constructor <;>`. Simplify using `only [cut_apply, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, he, h1, mul_comm (1 - e) e, h2, zero_smul, add_zero, zero_add, mul_one, one_mul]`. Rewrite using `[← add_smul]`.

Simplify using the standard rewrite rules.
-/
theorem cut_mul_cut {A : Type} [Ring A] [Algebra R A] (e : R) (he : e * e = e) (a : A) :
    cut e he a * cut (1 - e) (compl_idem he) a = a ∧ cut (1 - e) (compl_idem he) a * cut e he a = a := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 := compl_idem he
  constructor <;>
  · simp only [cut_apply, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, he, h1, mul_comm (1 - e) e, h2,
      zero_smul, add_zero, zero_add, mul_one, one_mul]
    rw [← add_smul]; simp

/- English proof (translation)
Establish `key : ∀ (f : R), f * f = f → ∀ X Y : Matrix n n R, f • X = f • Y → f * X.det = f * Y.det`. Introduce `f hf X Y h`. Establish `hp : ∀ k : ℕ, f * f ^ k = f`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ← mul_assoc, ih, hf]`. Use `congrArg (fun Z => f * Matrix.det Z) h` as an intermediate fact. Simplify `this` using `only [Matrix.det_smul, ← mul_assoc, hp]`. Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`.

Establish `a` using `key e he (cut e he M) M (by simp only [cut_apply, smul_add, smul_smul, he, h1, zero_smul, add_zero])`. Establish `b` using `key (1 - e) (compl_idem he) (cut e he M) 1 (by`. Simplify using `only [cut_apply, smul_add, smul_smul, compl_idem he, mul_comm (1 - e) e, h1, zero_smul, zero_add])`. Rewrite using `[cut_apply e he M.det, smul_eq_mul, smul_eq_mul, ← a]`. Rewrite `b` using `[Matrix.det_one]`.

Rewrite using `[← b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_cut {n : Type} [Fintype n] [DecidableEq n] (e : R) (he : e * e = e) (M : Matrix n n R) :
    (cut e he M).det = cut e he M.det := by
  have key : ∀ (f : R), f * f = f → ∀ X Y : Matrix n n R, f • X = f • Y → f * X.det = f * Y.det := by
    intro f hf X Y h
    have hp : ∀ k : ℕ, f * f ^ k = f := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mul_assoc, ih, hf]
    have := congrArg (fun Z => f * Matrix.det Z) h
    simpa only [Matrix.det_smul, ← mul_assoc, hp] using this
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have a := key e he (cut e he M) M (by simp only [cut_apply, smul_add, smul_smul, he, h1, zero_smul, add_zero])
  have b := key (1 - e) (compl_idem he) (cut e he M) 1 (by
    simp only [cut_apply, smul_add, smul_smul, compl_idem he, mul_comm (1 - e) e, h1, zero_smul, zero_add])
  rw [cut_apply e he M.det, smul_eq_mul, smul_eq_mul, ← a]
  rw [Matrix.det_one] at b
  rw [← b]; ring

/- English proof (translation)
Establish `h` using `congrArg (cut e he) h`. Rewrite `h` using `[map_mul, map_one]`. Use `Eq.trans ?_ h` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[cut_apply, hs, Matrix.one_apply, eq_comm, apply_ite σ]`.
-/
theorem cut_unitary {n : Type} [Fintype n] [DecidableEq n] (σ : R →+* R) (e : R) (he : e * e = e) (hs : σ e = e)
    (M : Matrix n n R) (h : (M.map σ).transpose * M = 1) :
    ((cut e he M).map σ).transpose * cut e he M = 1 := by
  have h := congrArg (cut e he) h
  rw [map_mul, map_one] at h
  refine Eq.trans ?_ h
  congr 1
  ext i j
  simp [cut_apply, hs, Matrix.one_apply, eq_comm, apply_ite σ]

end Cut

section Theta

variable {D : D7} {T : Tor D} {N N' : ℕ}

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]`.
-/
theorem Hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]`.
-/
theorem Hf_add_right (x y z : VC D N N') : Hf D T z (x + y) = Hf D T z x + Hf D T z y := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

def Wl (T : Tor D) (x : VC D N N') : Module.End ℂ (VC D N N' → ℂ) where
  toFun := Wd D T x
  map_add' F G := by funext z; simp only [Wd, U, Pi.add_apply]; ring
  map_smul' a F := by funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Wl_apply (x : VC D N N') (F : VC D N N' → ℂ) : Wl T x F = Wd D T x F := rfl

/- English proof (translation)
Establish `hne : wdPh D T (x + y) ≠ 0` using `Complex.exp_ne_zero _`. Use `⟨wdPh D T x * wdPh D T y / wdPh D T (x + y) * Complex.exp (-(Real.pi : ℂ) * Hf D T x y + (Real.pi : ℂ) * (Hf D T x y + Hf D T y x) / 2), ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun F => funext fun z => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, Wl_apply, Pi.smul_apply, smul_eq_mul, Wd, U, Hf_add_left, Hf_add_right, add_assoc]`. Establish `e : Complex.exp (-(Real.pi : ℂ) * (Hf D T z y + Hf D T x y) - (Real.pi : ℂ) * Hf D T y y / 2) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = Complex.exp (-(Real.pi : ℂ) * Hf D T x y + (Real.pi : ℂ) * (Hf D T x y + Hf D T y x) / 2) * Complex.exp (-( …`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ a b w f E₁ E₂ E₃ E₄ : ℂ, w ≠ 0 → E₁ * E₂ = E₃ * E₄ → a * (b * (f * E₁) * E₂) = a * b / w * E₃ * (w * (f * E₄))`. Introduce `a b w f E₁ E₂ E₃ E₄ hw h`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `a * b * f * h`. Conclude with `key _ _ _ _ _ _ _ _ hne e`.
-/
theorem Wl_mul (x y : VC D N N') : ∃ κ : ℂ, Wl T x * Wl T y = κ • Wl T (x + y) := by
  have hne : wdPh D T (x + y) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨wdPh D T x * wdPh D T y / wdPh D T (x + y) *
    Complex.exp (-(Real.pi : ℂ) * Hf D T x y + (Real.pi : ℂ) * (Hf D T x y + Hf D T y x) / 2), ?_⟩
  refine LinearMap.ext fun F => funext fun z => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Wl_apply, Pi.smul_apply, smul_eq_mul, Wd, U, Hf_add_left,
    Hf_add_right, add_assoc]
  have e : Complex.exp (-(Real.pi : ℂ) * (Hf D T z y + Hf D T x y) - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T x y + (Real.pi : ℂ) * (Hf D T x y + Hf D T y x) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z x + Hf D T z y) -
        (Real.pi : ℂ) * (Hf D T x x + (Hf D T y x + (Hf D T x y + Hf D T y y))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have key : ∀ a b w f E₁ E₂ E₃ E₄ : ℂ, w ≠ 0 → E₁ * E₂ = E₃ * E₄ →
      a * (b * (f * E₁) * E₂) = a * b / w * E₃ * (w * (f * E₄)) := by
    intro a b w f E₁ E₂ E₃ E₄ hw h
    field_simp
    linear_combination a * b * f * h
  exact key _ _ _ _ _ _ _ _ hne e

/- English proof (translation)
Take `⟨κ, hκ⟩` from `Wl_mul (T := T) x y`. Establish `h` using `LinearMap.congr_fun hκ G`. Rewrite `h` using `[Module.End.mul_apply, hfix y hy, hfix x hx, LinearMap.smul_apply, hfix _ (A.add_mem hx hy)]`. Establish `: κ = 1`. Establish `h2 : (κ - 1) • G = 0` using `by rw [sub_smul, one_smul, ← h, sub_self]`.

Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hG)`. Rewrite using `[hκ, this, one_smul]`.
-/
theorem Wl_add {A : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ} (hG : G ≠ 0) (hfix : ∀ x ∈ A, Wl T x G = G)
    {x y : VC D N N'} (hx : x ∈ A) (hy : y ∈ A) : Wl T (x + y) = Wl T x * Wl T y := by
  obtain ⟨κ, hκ⟩ := Wl_mul (T := T) x y
  have h := LinearMap.congr_fun hκ G
  rw [Module.End.mul_apply, hfix y hy, hfix x hx, LinearMap.smul_apply, hfix _ (A.add_mem hx hy)] at h
  have : κ = 1 := by
    have h2 : (κ - 1) • G = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hG)
  rw [hκ, this, one_smul]

/- English proof (translation)
Unfold `Wd U Hf`. Use `fun_prop`.
-/
theorem Wd_differentiable (x : VC D N N') {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (Wd D T x F) := by
  unfold Wd U Hf
  fun_prop

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[Iop, U]`.
-/
theorem Iop_zero (A B : AddSubgroup (VC D N N')) : Iop D T A B 0 = 0 := by
  funext z; simp [Iop, U]

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Establish `h0' : (A.addSubgroupOf B).index = 0` using `h0`. Simplify using `[Iop, h0']`.
-/
theorem index_ne_zero {A B : AddSubgroup (VC D N N')} {F : VC D N N' → ℂ} (h : Iop D T A B F ≠ 0) :
    A.relIndex B ≠ 0 := by
  intro h0
  apply h
  funext z
  have h0' : (A.addSubgroupOf B).index = 0 := h0
  simp [Iop, h0']

/- English proof (translation)
Establish `: (A.addSubgroupOf B).FiniteIndex` using `⟨h⟩`. Establish `: Fintype (B ⧸ A.addSubgroupOf B)` using `Fintype.ofFinite _`. Establish `e : (B ⧸ A.addSubgroupOf B) ≃ Fin (A.relIndex B)` using `Finite.equivFinOfCardEq rfl`. Use `⟨fun j => ((Quotient.out (e.symm j) : B) : VC D N N'), fun j => Subtype.property _, fun F => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Simplify using `only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, LinearMap.sum_apply, Finset.sum_apply, Wl_apply]`. Use `congr 1`. Rewrite using `[← e.symm.sum_comp]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hW _ (Subtype.property _)]`.
-/
theorem Iop_eq {A B : AddSubgroup (VC D N N')} (h : A.relIndex B ≠ 0)
    (hW : ∀ x ∈ B, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) :
    ∃ x : Fin (A.relIndex B) → VC D N N', (∀ j, x j ∈ B) ∧
      ∀ F, Iop D T A B F = ((Real.sqrt (A.relIndex B : ℝ) : ℂ))⁻¹ • (∑ j, Wl T (x j)) F := by
  have : (A.addSubgroupOf B).FiniteIndex := ⟨h⟩
  have : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
  have e : (B ⧸ A.addSubgroupOf B) ≃ Fin (A.relIndex B) := Finite.equivFinOfCardEq rfl
  refine ⟨fun j => ((Quotient.out (e.symm j) : B) : VC D N N'), fun j => Subtype.property _, fun F => ?_⟩
  funext z
  simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, LinearMap.sum_apply, Finset.sum_apply, Wl_apply]
  congr 1
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hW _ (Subtype.property _)]

end Theta

section Scalar

/- English proof (translation)
Establish `hr : ((Real.sqrt n : ℝ) : ℂ) ≠ 0`. Rewrite using `[Complex.ofReal_ne_zero, Real.sqrt_ne_zero (Nat.cast_nonneg n)]`. Conclude with `hn0` after adjusting the coercions. Establish `hSe : S e = ((Real.sqrt n : ℝ) : ℂ) • G` using `by rw [hG, smul_smul, mul_inv_cancel₀ hr, one_smul]`. Establish `hm : ((Real.sqrt n : ℝ) : ℂ) = ((Real.sqrt n₁ : ℝ) : ℂ) * ((Real.sqrt n₂ : ℝ) : ℂ)`.

Rewrite using `[hn, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]`. Establish `h3` using `congrArg S h`. Rewrite `h3` using `[map_smul, map_smul, hS, ← Module.End.mul_apply S S₁, h₁.eq, Module.End.mul_apply, ← Module.End.mul_apply S S₂, h₂.eq, Module.End.mul_apply, hSe, map_smul, hS₂, map_smul, map_smul, hS₁, smul_smul, smul_smul, smul_smul, smul_smul]`. Establish `h4` using `smul_left_injective ℂ hG0 h3`. Establish `hr'` using `hr`.

Rewrite `hr'`, `h4` using `[hm]`. Establish `hnc : (n : ℂ) ≠ 0` using `by exact_mod_cast hn0`. Establish `hn' : (n : ℂ) = n₁ * n₂` using `by exact_mod_cast hn`. Apply `mul_right_cancel₀ hnc` to reduce the goal to its premises. Rewrite using `[h4, hn']`.

Establish `a1` using `left_ne_zero_of_mul hr'`. Establish `a2` using `right_ne_zero_of_mul hr'`. Clear the denominators using the available nonvanishing facts.
-/
theorem scalar_eq {X : Type} [AddCommGroup X] [Module ℂ X] (S S₁ S₂ : Module.End ℂ X) (e G : X) (n n₁ n₂ : ℕ) (c a : ℂ)
    (hn : n = n₁ * n₂) (hn0 : n ≠ 0) (hG0 : G ≠ 0) (hG : G = ((Real.sqrt n : ℝ) : ℂ)⁻¹ • S e)
    (hS : S G = (n : ℂ) • G) (hS₁ : S₁ G = (n₁ : ℂ) • G) (hS₂ : S₂ G = (n₂ : ℂ) • G)
    (h₁ : Commute S S₁) (h₂ : Commute S S₂)
    (h : c • G = (a * ((Real.sqrt n₁ : ℝ) : ℂ)⁻¹ * ((Real.sqrt n₂ : ℝ) : ℂ)⁻¹) • S₁ (S₂ e)) : c = a := by
  have hr : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero (Nat.cast_nonneg n)]; exact_mod_cast hn0
  have hSe : S e = ((Real.sqrt n : ℝ) : ℂ) • G := by rw [hG, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hm : ((Real.sqrt n : ℝ) : ℂ) = ((Real.sqrt n₁ : ℝ) : ℂ) * ((Real.sqrt n₂ : ℝ) : ℂ) := by
    rw [hn, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  have h3 := congrArg S h
  rw [map_smul, map_smul, hS, ← Module.End.mul_apply S S₁, h₁.eq, Module.End.mul_apply,
    ← Module.End.mul_apply S S₂, h₂.eq, Module.End.mul_apply, hSe, map_smul, hS₂, map_smul, map_smul, hS₁,
    smul_smul, smul_smul, smul_smul, smul_smul] at h3
  have h4 := smul_left_injective ℂ hG0 h3
  have hr' := hr
  rw [hm] at hr' h4
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hn' : (n : ℂ) = n₁ * n₂ := by exact_mod_cast hn
  apply mul_right_cancel₀ hnc
  rw [h4, hn']
  have a1 := left_ne_zero_of_mul hr'
  have a2 := right_ne_zero_of_mul hr'
  field_simp

end Scalar

section Adeles

open GlobalTheory.NormSum.VacMove

variable {D : D7}

def vanish (D : D7) (q : ℕ) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  zero_mem' := fun k => ⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨m, hm, hc, s, hs, h⟩ := hx k
    obtain ⟨m', hm', hc', s', hs', h'⟩ := hy k
    refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hc hc', m' * s + m * s',
      add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
    push_cast
    linear_combination (m' : AE D) * h + (m : AE D) * h'
  smul_mem' := fun c x hx => by
    have := zeroAt_mul D hq hx c
    rwa [mul_comm] at this

/- English proof (translation)
Use `(GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 x fun n hn => ?_` and prove the remaining obligations. Establish `: x ∈ (OhE D).toAddSubgroup.map (AddMonoidHom.mulLeft (n : AE D))`. Use `mem_of_local _ x fun q hq => ?_` and prove the remaining obligations. Take `⟨a, n', hn', rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one`. Take `⟨m, -, hc, s, hs, h⟩` from `h q hq a`.

Use `⟨m * n', Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, s, hs, ?_⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul]`. Use `push_cast`. Take the linear combination `-(n' : AE D) * h`. Take `⟨w, hw, h⟩` from `this`.

Conclude with `⟨w, hw, h.symm⟩`.
-/
theorem eq_zero_of_zeroAt (x : AE D) (h : ∀ q : ℕ, q.Prime → ZeroAt D q x) : x = 0 := by
  refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 x fun n hn => ?_
  have : x ∈ (OhE D).toAddSubgroup.map (AddMonoidHom.mulLeft (n : AE D)) := by
    refine mem_of_local _ x fun q hq => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    obtain ⟨m, -, hc, s, hs, h⟩ := h q hq a
    refine ⟨m * n', Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, s, hs, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
    push_cast
    linear_combination -(n' : AE D) * h
  obtain ⟨w, hw, h⟩ := this
  exact ⟨w, hw, h.symm⟩

/- English proof (translation)
Establish `h1 : (Ideal.Quotient.mk (vanish D q hq)).mapMatrix (g : Matrix (Fin N) (Fin N) (AE D)) = (Ideal.Quotient.mk (vanish D q hq)).mapMatrix 1`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq.2 (h i j)`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[← RingHom.map_det, ← RingHom.map_det, Matrix.det_one]`.

Conclude with `Ideal.Quotient.eq.1 h2`.
-/
theorem zeroAt_det {N q : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (h : TrivAt D q g) :
    ZeroAt D q (((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) - 1) := by
  have h1 : (Ideal.Quotient.mk (vanish D q hq)).mapMatrix (g : Matrix (Fin N) (Fin N) (AE D)) =
      (Ideal.Quotient.mk (vanish D q hq)).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

def cutG {N : ℕ} (e : AE D) (he : e * e = e) (hs : sgA D e = e) (g : GA D N) : GA D N :=
  ⟨Units.map (cut e he) (g : GL (Fin N) (AE D)),
    (PtsMem.mem_GA D _).2 (cut_unitary (sgA D) e he hs _ ((PtsMem.mem_GA D _).1 g.2))⟩

/- English proof (translation)
Rewrite using `[map_sub, map_one, hs]`.
-/
theorem compl_fixed {e : AE D} (hs : sgA D e = e) : sgA D (1 - e) = 1 - e := by rw [map_sub, map_one, hs]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subtype.ext (Units.ext (cut_mul_cut e he _).1), Subtype.ext (Units.ext (cut_mul_cut e he _).2)⟩`.
-/
theorem cutG_mul {N : ℕ} (e : AE D) (he : e * e = e) (hs : sgA D e = e) (g : GA D N) :
    cutG e he hs g * cutG (1 - e) (compl_idem he) (compl_fixed hs) g = g ∧
      cutG (1 - e) (compl_idem he) (compl_fixed hs) g * cutG e he hs g = g :=
  ⟨Subtype.ext (Units.ext (cut_mul_cut e he _).1), Subtype.ext (Units.ext (cut_mul_cut e he _).2)⟩

/- English proof (translation)
Introduce `i j`. Use `zeroAt_mul D hq h (((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(cut e he ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j - _ = _`. Simplify using `only [cut_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trivAt_cutG {N q : ℕ} (hq : q.Prime) (e : AE D) (he : e * e = e) (hs : sgA D e = e) (g : GA D N)
    (h : ZeroAt D q e) : TrivAt D q ((cutG e he hs g : GA D N) : GL (Fin N) (AE D)) := by
  intro i j
  convert zeroAt_mul D hq h (((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
    (1 : Matrix (Fin N) (Fin N) (AE D)) i j) using 1
  change (cut e he ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j - _ = _
  simp only [cut_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `det_cut e he ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))` as an intermediate fact. Rewrite `this` using `[cut_apply e he (Matrix.det _), smul_eq_mul, smul_eq_mul, mul_one]`. Conclude with `this`.
-/
theorem det_cutG {N : ℕ} (e : AE D) (he : e * e = e) (hs : sgA D e = e) (g : GA D N) :
    ((Matrix.GeneralLinearGroup.det ((cutG e he hs g : GA D N) : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) =
      e * ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) + (1 - e) := by
  have := det_cut e he ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  rw [cut_apply e he (Matrix.det _), smul_eq_mul, smul_eq_mul, mul_one] at this
  exact this

end Adeles

section Core

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

def TTs (T : Tor D) (N N' : ℕ) : Submodule ℂ (VC D N N' → ℂ) where
  carrier := TT D T N N'
  zero_mem' := ⟨differentiable_const 0, 1, one_pos, fun x _ => map_zero (Wl T _)⟩
  add_mem' := by
    rintro F G ⟨hF, m, hm, h⟩ ⟨hG, m', hm', h'⟩
    refine ⟨hF.add hG, m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩
    have a := h _ (AddSubgroup.nsmul_mem _ hx m')
    have b := h' _ (AddSubgroup.nsmul_mem _ hx m)
    rw [smul_smul] at a b
    rw [mul_comm] at b
    rw [← Wl_apply, map_add, Wl_apply, Wl_apply, a, b]
  smul_mem' := by
    rintro c F ⟨hF, m, hm, h⟩
    refine ⟨hF.const_smul c, m, hm, fun x hx => ?_⟩
    rw [← Wl_apply, map_smul, Wl_apply, h x hx]

def OmL {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') :
    TTs (tor0 D cc δ) N N' →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun F := W.Om g g' F
  map_add' F G := W.add g g' F F.2 G G.2
  map_smul' a F := W.smul g g' a F F.2

/- English proof (translation)
Use `(OmL W g g').map_smul a (∑ j, ⟨F j, hF j⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Use `Eq.trans ?_ this` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = W.Om g g' _`. Use `congr 1`.

Simplify using the standard rewrite rules.
-/
theorem Om_sum {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') {k : ℕ} (a : ℂ)
    (F : Fin k → VC D N N' → ℂ) (hF : ∀ j, F j ∈ TT D (tor0 D cc δ) N N') :
    W.Om g g' (a • ∑ j, F j) = a • ∑ j, W.Om g g' (F j) := by
  have := (OmL W g g').map_smul a (∑ j, ⟨F j, hF j⟩)
  rw [map_sum] at this
  refine Eq.trans ?_ this
  change _ = W.Om g g' _
  congr 1
  simp

/- English proof (translation)
Take `⟨Lt, h, h1, -⟩` from `exists_lattice_of_adelic_point D N`. Rewrite using `[← h1]`. Conclude with `(h 1).1`.
-/
theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h1]; exact (h 1).1

/- English proof (translation)
Take `⟨Lt, h, -⟩` from `exists_lattice_of_adelic_point D N`. Establish `: L = Lt g` using `by ext x; rw [hL x, (h g).1 x]`. Rewrite using `[this]`. Conclude with `(h g).2`.
-/
theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by ext x; rw [hL x, (h g).1 x]
  rw [this]; exact (h g).2

/- English proof (translation)
Take `⟨Lt, h, -⟩` from `exists_lattice_of_adelic_point D N`. Conclude with `⟨_, (h g).1⟩`.
-/
theorem exists_moves (g : GA D N) : ∃ L, Moves D (g : GL (Fin N) (AE D)) L := by
  obtain ⟨Lt, h, -⟩ := exists_lattice_of_adelic_point D N
  exact ⟨_, (h g).1⟩

/- English proof (translation)
Establish `hg1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩`. Establish `k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L')` using `Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩`. Take `⟨-, hTh, -, hII⟩` from `GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he`. Establish `w0` using `(GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k0).2.1`.

Establish `w1` using `(GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k1).2.1`. Establish `hne : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 ≠ 0`. Introduce `h`. Rewrite `hII` using `[h, Iop_zero]`. Conclude with `h0 hII.symm`.

Establish `hfix : ∀ x ∈ La D (tor0 D cc δ) L L', Wl (tor0 D cc δ) x (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) = Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0`. Introduce `x hx`. Rewrite using `[Wl_apply, w1 x hx]`. Conclude with `funext (hTh.2 x hx)`. Take `⟨x, hx, hI⟩` from `Iop_eq (index_ne_zero hne) w1`.

Use `⟨hne, hfix, fun x hx y hy => Wl_add hne hfix hx hy, index_ne_zero (hII.symm ▸ h0), index_ne_zero hne, fun x hx => ?_, x, hx, hI e0⟩` and prove the remaining obligations. Rewrite using `[Wl_apply, w0 x hx]`. Conclude with `funext (he.2 x hx)`.
-/
theorem lattice_facts (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (h0 : e0 ≠ 0) {g : GA D N} {g' : GA D N'} {L L'}
    (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 ≠ 0 ∧
    (∀ x ∈ La D (tor0 D cc δ) L L', Wl (tor0 D cc δ) x
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) =
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) ∧
    (∀ x ∈ La D (tor0 D cc δ) L L', ∀ y ∈ La D (tor0 D cc δ) L L',
      Wl (tor0 D cc δ) (x + y) = Wl (tor0 D cc δ) x * Wl (tor0 D cc δ) y) ∧
    (La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N') ≠ 0 ∧
    (La0 D (tor0 D cc δ) N N').relIndex (La D (tor0 D cc δ) L L') ≠ 0 ∧
    (∀ x ∈ La0 D (tor0 D cc δ) N N', Wl (tor0 D cc δ) x e0 = e0) ∧
    ∃ x : Fin ((La0 D (tor0 D cc δ) N N').relIndex (La D (tor0 D cc δ) L L')) → VC D N N',
      (∀ j, x j ∈ La D (tor0 D cc δ) L L') ∧
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 =
        ((Real.sqrt ((La0 D (tor0 D cc δ) N N').relIndex (La D (tor0 D cc δ) L L') : ℝ) : ℂ))⁻¹ •
          (∑ j, Wl (tor0 D cc δ) (x j)) e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, hII⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  have w0 := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k0).2.1
  have w1 := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k1).2.1
  have hne : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 ≠ 0 := by
    intro h; rw [h, Iop_zero] at hII; exact h0 hII.symm
  have hfix : ∀ x ∈ La D (tor0 D cc δ) L L', Wl (tor0 D cc δ) x
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) =
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
    intro x hx
    rw [Wl_apply, w1 x hx]
    exact funext (hTh.2 x hx)
  obtain ⟨x, hx, hI⟩ := Iop_eq (index_ne_zero hne) w1
  refine ⟨hne, hfix, fun x hx y hy => Wl_add hne hfix hx hy, index_ne_zero (hII.symm ▸ h0), index_ne_zero hne,
    fun x hx => ?_, x, hx, hI e0⟩
  rw [Wl_apply, w0 x hx]
  exact funext (he.2 x hx)

/- English proof (translation)
Simplify using `[LinearMap.sum_apply, h, Nat.cast_smul_eq_nsmul]`.
-/
theorem sum_fix {X : Type} [AddCommGroup X] [Module ℂ X] {k : ℕ} (S : Fin k → Module.End ℂ X) (G : X)
    (h : ∀ j, S j G = G) : (∑ j, S j) G = (k : ℂ) • G := by
  simp [LinearMap.sum_apply, h, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Establish `hg1` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨a1, a2, a3, -, a5, a6, x, hx, hI⟩` from `lattice_facts hc he W.nz hL hL'`. Take `⟨-, -, s3, -, -, -, xs, hxs, hIs⟩` from `lattice_facts hc he W.nz hLs hLs'`. Take `⟨-, -, i3, i4, -, -, xi, hxi, hIi⟩` from `lattice_facts hc he W.nz hLi hLi'`. Establish `hloc : ∀ q : ℕ, q.Prime → (Nr q (La D (tor0 D cc δ) Ls Ls') (La0 D (tor0 D cc δ) N N') ∧ Nr q (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) Ls Ls') ∧ Nr q (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) Li Li') ∧ Nr q (La D (tor0 D cc δ) Li Li') (La D (tor0 D cc δ) L L')) ∨ (Nr q …`.

Introduce `q hq`. Distinguish the cases in `hin : InertQ D q`. Establish `u` using `GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q 1 gs 1 gs' _ Ls _ Ls' (hs q hq hin) (hs' q hq hin) (moves_one D N) (moves_one D N') (by rwa [one_mul]) (by rwa [one_mul])`. Establish `v` using `GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q gi gs gi' gs' Li L Li' L' (hs q hq hin) (hs' q hq hin) hLi hLi' (by rwa [h2]) (by rwa [h2'])`. Conclude with `Or.inl ⟨u.2, u.1, v.2, v.1⟩`.

Establish `u` using `GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q 1 gi 1 gi' _ Li _ Li' (hi q hq hin) (hi' q hq hin) (moves_one D N) (moves_one D N') (by rwa [one_mul]) (by rwa [one_mul])`. Establish `v` using `GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q gs gi gs' gi' Ls L Ls' L' (hi q hq hin) (hi' q hq hin) hLs hLs' (by rwa [h1]) (by rwa [h1'])`. Conclude with `Or.inr ⟨v.1, v.2, u.2, u.1⟩`. Establish `hidx` using `index_mul hloc`. Establish `heT : e0 ∈ TT D (tor0 D cc δ) N N'` using `⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩`.

Establish `hWT : ∀ j, Wd D (tor0 D cc δ) (xi j) e0 ∈ TT D (tor0 D cc δ) N N'`. Introduce `j`. Use `⟨Wd_differentiable _ he.1, _, Nat.pos_of_ne_zero i4, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hm` using `AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) Li Li') hy`. Rewrite using `[← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← i3 _ hm _ (hxi j), add_comm, i3 _ (hxi j) _ hm, Module.End.mul_apply, a6 _ (AddSubgroup.nsmul_mem _ hy _)]`.

Establish `hmove` using `fun j => GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice D hg1 cc δ hc.1.1 N N' e0 W gs gi gs' gi' Li L Li' L' hLi hLi' (by rwa [h1]) (by rwa [h1']) (xi j) (hxi j) e0 heT`. Use `choose y hy hyW using hmove`. Establish `hrep : ∀ j, ∃ u ∈ La D (tor0 D cc δ) L L', Wl (tor0 D cc δ) (xs j) e0 = Wl (tor0 D cc δ) u e0`. Introduce `j`. Use `le_sup_of_local (B := La D (tor0 D cc δ) Ls Ls') (C := La D (tor0 D cc δ) L L') (K := La0 D (tor0 D cc δ) N N') (fun q hq => (hloc q hq).elim (fun h => Or.inr h.1) fun h => Or.inl h.1) (hxs j)` as an intermediate fact.

Take `⟨u, hu, v, hv, huv⟩` from `AddSubgroup.mem_sup.1 this`. Conclude with `⟨u, hu.2, by rw [← huv, s3 u hu.1 v hv.2, Module.End.mul_apply, a6 v hv.1]⟩`. Use `choose u hu huW using hrep`. Establish `hcomm : ∀ {k k' : ℕ} (a : Fin k → VC D N N') (b : Fin k' → VC D N N'), (∀ j, a j ∈ La D (tor0 D cc δ) L L') → (∀ j, b j ∈ La D (tor0 D cc δ) L L') → Commute (∑ j, Wl (tor0 D cc δ) (a j)) (∑ j, Wl (tor0 D cc δ) (b j))`. Introduce `k k' a b ha hb`.

Use `Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Commute, SemiconjBy, ← a3 _ (ha i) _ (hb j), ← a3 _ (hb j) _ (ha i), add_comm]`. Use `scalar_eq _ (∑ j, Wl (tor0 D cc δ) (y j)) (∑ j, Wl (tor0 D cc δ) (u j)) e0 _ _ _ _ c (ci * cs) hidx a5 a1 hI (sum_fix _ _ fun j => a2 _ (hx j)) (sum_fix _ _ fun j => a2 _ (hy j)) (sum_fix _ _ fun j => a2 _ (hu j)) (hcomm _ _ hx hy) (hcomm _ _ hx hu) ?_` and prove the remaining obligations. Establish `hs2 : (∑ j, Wl (tor0 D cc δ) (xs j)) e0 = (∑ j, Wl (tor0 D cc δ) (u j)) e0`. Simplify using `only [LinearMap.sum_apply, huW]`.

Rewrite using `[← hO, ← h1, ← h1', W.mul _ _ _ _ _ heT, hOi, hIi, smul_smul, LinearMap.sum_apply]`. Simplify using `only [Wl_apply]`. Rewrite using `[Om_sum W _ _ _ _ hWT]`. Simplify using `only [hyW, hOs, hIs, hs2]`. Simplify using `only [← Wl_apply, map_smul]`.

Rewrite using `[← Finset.smul_sum, ← Finset.smul_sum, ← LinearMap.sum_apply, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scalar_mul (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    {g gs gi : GA D N} {g' gs' gi' : GA D N'} (h1 : gs * gi = g) (h2 : gi * gs = g) (h1' : gs' * gi' = g')
    (h2' : gi' * gs' = g') (hs : SuppSplit D (gs : GL (Fin N) (AE D))) (hs' : SuppSplit D (gs' : GL (Fin N') (AE D)))
    (hi : SuppInert D (gi : GL (Fin N) (AE D))) (hi' : SuppInert D (gi' : GL (Fin N') (AE D)))
    {L L' Ls Ls' Li Li'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L')
    (hLs : Moves D (gs : GL (Fin N) (AE D)) Ls) (hLs' : Moves D (gs' : GL (Fin N') (AE D)) Ls')
    (hLi : Moves D (gi : GL (Fin N) (AE D)) Li) (hLi' : Moves D (gi' : GL (Fin N') (AE D)) Li') {c cs ci : ℂ}
    (hO : W.Om g g' e0 = c • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0)
    (hOs : W.Om gs gs' e0 = cs • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) Ls Ls') e0)
    (hOi : W.Om gi gi' e0 = ci • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) Li Li') e0) :
    c = ci * cs := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨a1, a2, a3, -, a5, a6, x, hx, hI⟩ := lattice_facts hc he W.nz hL hL'
  obtain ⟨-, -, s3, -, -, -, xs, hxs, hIs⟩ := lattice_facts hc he W.nz hLs hLs'
  obtain ⟨-, -, i3, i4, -, -, xi, hxi, hIi⟩ := lattice_facts hc he W.nz hLi hLi'
  have hloc : ∀ q : ℕ, q.Prime →
      (Nr q (La D (tor0 D cc δ) Ls Ls') (La0 D (tor0 D cc δ) N N') ∧
        Nr q (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) Ls Ls') ∧
        Nr q (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) Li Li') ∧
        Nr q (La D (tor0 D cc δ) Li Li') (La D (tor0 D cc δ) L L')) ∨
      (Nr q (La D (tor0 D cc δ) Ls Ls') (La D (tor0 D cc δ) L L') ∧
        Nr q (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) Ls Ls') ∧
        Nr q (La D (tor0 D cc δ) Li Li') (La0 D (tor0 D cc δ) N N') ∧
        Nr q (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) Li Li')) := by
    intro q hq
    by_cases hin : InertQ D q
    · have u := GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q 1 gs 1 gs' _ Ls _ Ls' (hs q hq hin) (hs' q hq hin)
        (moves_one D N) (moves_one D N') (by rwa [one_mul]) (by rwa [one_mul])
      have v := GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q gi gs gi' gs' Li L Li' L' (hs q hq hin) (hs' q hq hin)
        hLi hLi' (by rwa [h2]) (by rwa [h2'])
      exact Or.inl ⟨u.2, u.1, v.2, v.1⟩
    · have u := GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q 1 gi 1 gi' _ Li _ Li' (hi q hq hin) (hi' q hq hin)
        (moves_one D N) (moves_one D N') (by rwa [one_mul]) (by rwa [one_mul])
      have v := GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime D hg1 cc δ hc.1.1 N N' q gs gi gs' gi' Ls L Ls' L' (hi q hq hin) (hi' q hq hin)
        hLs hLs' (by rwa [h1]) (by rwa [h1'])
      exact Or.inr ⟨v.1, v.2, u.2, u.1⟩
  have hidx := index_mul hloc
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hWT : ∀ j, Wd D (tor0 D cc δ) (xi j) e0 ∈ TT D (tor0 D cc δ) N N' := by
    intro j
    refine ⟨Wd_differentiable _ he.1, _, Nat.pos_of_ne_zero i4, fun y hy => ?_⟩
    have hm := AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) Li Li') hy
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← i3 _ hm _ (hxi j), add_comm, i3 _ (hxi j) _ hm,
      Module.End.mul_apply, a6 _ (AddSubgroup.nsmul_mem _ hy _)]
  have hmove := fun j => GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice D hg1 cc δ hc.1.1 N N' e0 W gs gi gs' gi' Li L Li' L' hLi hLi'
    (by rwa [h1]) (by rwa [h1']) (xi j) (hxi j) e0 heT
  choose y hy hyW using hmove
  have hrep : ∀ j, ∃ u ∈ La D (tor0 D cc δ) L L', Wl (tor0 D cc δ) (xs j) e0 = Wl (tor0 D cc δ) u e0 := by
    intro j
    have := le_sup_of_local (B := La D (tor0 D cc δ) Ls Ls') (C := La D (tor0 D cc δ) L L')
      (K := La0 D (tor0 D cc δ) N N') (fun q hq => (hloc q hq).elim (fun h => Or.inr h.1) fun h => Or.inl h.1) (hxs j)
    obtain ⟨u, hu, v, hv, huv⟩ := AddSubgroup.mem_sup.1 this
    exact ⟨u, hu.2, by rw [← huv, s3 u hu.1 v hv.2, Module.End.mul_apply, a6 v hv.1]⟩
  choose u hu huW using hrep
  have hcomm : ∀ {k k' : ℕ} (a : Fin k → VC D N N') (b : Fin k' → VC D N N'), (∀ j, a j ∈ La D (tor0 D cc δ) L L') →
      (∀ j, b j ∈ La D (tor0 D cc δ) L L') →
      Commute (∑ j, Wl (tor0 D cc δ) (a j)) (∑ j, Wl (tor0 D cc δ) (b j)) := by
    intro k k' a b ha hb
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
    rw [Commute, SemiconjBy, ← a3 _ (ha i) _ (hb j), ← a3 _ (hb j) _ (ha i), add_comm]
  refine scalar_eq _ (∑ j, Wl (tor0 D cc δ) (y j)) (∑ j, Wl (tor0 D cc δ) (u j)) e0 _ _ _ _ c (ci * cs) hidx a5 a1 hI
    (sum_fix _ _ fun j => a2 _ (hx j)) (sum_fix _ _ fun j => a2 _ (hy j)) (sum_fix _ _ fun j => a2 _ (hu j))
    (hcomm _ _ hx hy) (hcomm _ _ hx hu) ?_
  have hs2 : (∑ j, Wl (tor0 D cc δ) (xs j)) e0 = (∑ j, Wl (tor0 D cc δ) (u j)) e0 := by
    simp only [LinearMap.sum_apply, huW]
  rw [← hO, ← h1, ← h1', W.mul _ _ _ _ _ heT, hOi, hIi, smul_smul, LinearMap.sum_apply]
  simp only [Wl_apply]
  rw [Om_sum W _ _ _ _ hWT]
  simp only [hyW, hOs, hIs, hs2]
  simp only [← Wl_apply, map_smul]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← LinearMap.sum_apply, smul_smul, smul_smul]
  congr 1
  ring

end Core

section Main

open GlobalTheory.NormSum.VacMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

/- English proof (translation)
Take `⟨Ls, hLs⟩` from `exists_moves (cutG e h1 h2 g)`. Take `⟨Ls', hLs'⟩` from `exists_moves (cutG e h1 h2 g')`. Take `⟨Li, hLi⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)`. Take `⟨Li', hLi'⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')`. Establish `hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)`.

Establish `hi : ∀ {n : ℕ} (k : GA D n), SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)`. Conclude with `⟨_, scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1 (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO (W.split _ _ x x' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨hx q hq h, hx' q hq h⟩) hd hd' hLs hLs') (GlobalT …`.
-/
theorem scalar_formula (hc : Crv D cc δ) (hev : Even (N * N')) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') {c : ℂ}
    (hO : W.Om g g' e0 = fun z => c *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 z)
    {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
    (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))
    {x x' : (AE D)ˣ} (hx : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1))
    (hx' : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1))
    (hd : x = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D x)
    (hd' : x' = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g' : GA D N') : GL (Fin N') (AE D)) * sgU D x') :
    ∃ k : ℕ, c = (-1) ^ k * ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) := by
  obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
  obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
  obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
  obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
  have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
  have hi : ∀ {n : ℕ} (k : GA D n),
      SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
  exact ⟨_, scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
    (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
    (W.split _ _ x x' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨hx q hq h, hx' q hq h⟩) hd hd' hLs hLs')
    (GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D cc δ hc N N' hev e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')⟩

/- English proof (translation)
Use `set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef`. Establish `hzv : (z : AE D) = e * d + (1 - e)`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_zeroAt _ fun q hq => ?_` and prove the remaining obligations. Distinguish the cases in `hi : InertQ D q`.

Establish `: ZeroAt D q _` using `(vanish D q hq).add_mem ((hz q hq).1 hi) (zeroAt_mul D hq ((h3 q hq).1 hi) (1 - d))`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `: ZeroAt D q ((z : AE D) - d + _)` using `(vanish D q hq).add_mem ((hz q hq).2 hi) (zeroAt_mul D hq ((h3 q hq).2 hi) (d - 1))`. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `hxv : (x : AE D) = (e * d + (1 - e)) * sgA D x`. Rewrite using `[← hzv]`. Conclude with `congrArg Units.val hx`. Use `⟨Units.map (cut e h1) x, fun q hq hi => ?_, Units.ext ?_, fun χ => ?_⟩` and prove the remaining obligations.

Use `zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `e * x + (1 - e) * 1 - 1 = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Units.val_mul, det_cutG, ← hdef]`. Express the relevant statement in the definitionally equal form `e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)`.

Rewrite using `[map_add, map_mul, map_mul, map_sub, map_one, h2]`. Take the linear combination `e * hxv + (d - 1) * h1`. Establish `hsplit : x = Units.map (cut e h1) x * Units.map (cut (1 - e) (compl_idem h1)) x` using `Units.ext (cut_mul_cut e h1 (x : AE D)).1.symm`. Establish `hfix : sgU D (Units.map (cut (1 - e) (compl_idem h1)) x) = Units.map (cut (1 - e) (compl_idem h1)) x`. Use `Units.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `sgA D ((1 - e) * x + (1 - (1 - e)) * 1) = (1 - e) * x + (1 - (1 - e)) * 1`. Simplify using `only [map_add, map_mul, map_sub, map_one, h2]`. Take the linear combination `-(1 - e) * hxv + (d - 1) * sgA D x * h1`. Use `conv_rhs => rw [hsplit, map_mul, mul_pow, χ.sq_AF _ hfix, mul_one]`.
-/
theorem exists_trivial_inert {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
    (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))
    (g : GA D N) {z x : (AE D)ˣ} (hz : SplitComp D (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) z)
    (hx : x = z * sgU D x) : ∃ y : (AE D)ˣ, (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1)) ∧
      y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D y ∧
      ∀ {n : ℕ} (χ : HeckeU D n), χ.f y ^ 2 = χ.f x ^ 2 := by
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hzv : (z : AE D) = e * d + (1 - e) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_zeroAt _ fun q hq => ?_
    by_cases hi : InertQ D q
    · have : ZeroAt D q _ := (vanish D q hq).add_mem ((hz q hq).1 hi) (zeroAt_mul D hq ((h3 q hq).1 hi) (1 - d))
      convert this using 1
      ring
    · have : ZeroAt D q ((z : AE D) - d + _) :=
        (vanish D q hq).add_mem ((hz q hq).2 hi) (zeroAt_mul D hq ((h3 q hq).2 hi) (d - 1))
      convert this using 1
      ring
  have hxv : (x : AE D) = (e * d + (1 - e)) * sgA D x := by
    rw [← hzv]; exact congrArg Units.val hx
  refine ⟨Units.map (cut e h1) x, fun q hq hi => ?_, Units.ext ?_, fun χ => ?_⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1
    change e * x + (1 - e) * 1 - 1 = _
    ring
  · rw [Units.val_mul, det_cutG, ← hdef]
    change e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)
    rw [map_add, map_mul, map_mul, map_sub, map_one, h2]
    linear_combination e * hxv + (d - 1) * h1
  · have hsplit : x = Units.map (cut e h1) x * Units.map (cut (1 - e) (compl_idem h1)) x :=
      Units.ext (cut_mul_cut e h1 (x : AE D)).1.symm
    have hfix : sgU D (Units.map (cut (1 - e) (compl_idem h1)) x) = Units.map (cut (1 - e) (compl_idem h1)) x := by
      refine Units.ext ?_
      change sgA D ((1 - e) * x + (1 - (1 - e)) * 1) = (1 - e) * x + (1 - (1 - e)) * 1
      simp only [map_add, map_mul, map_sub, map_one, h2]
      linear_combination -(1 - e) * hxv + (d - 1) * sgA D x * h1
    conv_rhs => rw [hsplit, map_mul, mul_pow, χ.sq_AF _ hfix, mul_one]

/- English proof (translation)
Establish `hn` using `det_norm D g`. Use `set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef`. Establish `hx : ((1 - ε) + ε * d) * ((1 - ε) + ε * sgA D d) = 1`. Take the linear combination `(1 - d - sgA D d + d * sgA D d) * a1 + ε * hn`. Use `⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, Units.ext ?_, fun q hq h => ?_, fun q hq h => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, det_cutG, ← hdef]`. Establish `a3 : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, a1]`. Express the relevant statement in the definitionally equal form `(1 - ε) + ε * d = _ * sgA D ((1 - ε) + ε * d)`. Rewrite using `[map_add, map_mul, map_sub, map_one]`. Take the linear combination `(-(1 - d - sgA D d + d * sgA D d)) * (a3 + a2) - sgA D ε * hn`.

Use `zeroAt_mul D hq h (ε * (d - 1)) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(1 - ε) + ε * d - 1 = _`. Take the linear combination `(1 - d) * (a1 + a2)`. Use `zeroAt_mul D hq (zeroAt_det hq h) ε using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(1 - ε) + ε * d - 1 = (d - 1) * ε`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_solution {ε : AE D} (a1 : ε * ε = ε) (a2 : ε * sgA D ε = 0) (h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε)
    (h2 : sgA D (ε + sgA D ε) = ε + sgA D ε) (g : GA D N) :
    ∃ x : (AE D)ˣ, x = Matrix.GeneralLinearGroup.det ((cutG _ h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D x ∧
      (∀ q : ℕ, q.Prime → ZeroAt D q (ε + sgA D ε) → ZeroAt D q ((x : AE D) - 1)) ∧
      ∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → ZeroAt D q ((x : AE D) - 1) := by
  have hn := det_norm D g
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hx : ((1 - ε) + ε * d) * ((1 - ε) + ε * sgA D d) = 1 := by
    linear_combination (1 - d - sgA D d + d * sgA D d) * a1 + ε * hn
  refine ⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, Units.ext ?_, fun q hq h => ?_, fun q hq h => ?_⟩
  · rw [Units.val_mul, det_cutG, ← hdef]
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    change (1 - ε) + ε * d = _ * sgA D ((1 - ε) + ε * d)
    rw [map_add, map_mul, map_sub, map_one]
    linear_combination (-(1 - d - sgA D d + d * sgA D d)) * (a3 + a2) - sgA D ε * hn
  · convert zeroAt_mul D hq h (ε * (d - 1)) using 1
    change (1 - ε) + ε * d - 1 = _
    linear_combination (1 - d) * (a1 + a2)
  · convert zeroAt_mul D hq (zeroAt_det hq h) ε using 1
    change (1 - ε) + ε * d - 1 = (d - 1) * ε
    ring

def UnitAt {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ) : Prop := c ∈ Qbar ∧ ‖lamC lam c‖ = 1

/- English proof (translation)
Take `⟨ha, ha'⟩` from `ha`. Take `⟨hb, hb'⟩` from `hb`. Use `⟨mul_mem ha hb, ?_⟩` and prove the remaining obligations. Simplify using `only [lamC, ha, hb, mul_mem ha hb, dif_pos] at ha' hb' ⊢`. Establish `: (⟨a * b, mul_mem ha hb⟩ : Qbar) = ⟨a, ha⟩ * ⟨b, hb⟩` using `rfl`.

Rewrite using `[this, map_mul, norm_mul, ha', hb', one_mul]`.
-/
theorem UnitAt.mul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {a b : ℂ} (ha : UnitAt lam a) (hb : UnitAt lam b) :
    UnitAt lam (a * b) := by
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  refine ⟨mul_mem ha hb, ?_⟩
  simp only [lamC, ha, hb, mul_mem ha hb, dif_pos] at ha' hb' ⊢
  have : (⟨a * b, mul_mem ha hb⟩ : Qbar) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul, norm_mul, ha', hb', one_mul]

/- English proof (translation)
Take `⟨ha, ha'⟩` from `ha`. Use `⟨zpow_mem ha k, ?_⟩` and prove the remaining obligations. Simplify using `only [lamC, ha, zpow_mem ha k, dif_pos] at ha' ⊢`. Establish `: (⟨a ^ k, zpow_mem ha k⟩ : Qbar) = ⟨a, ha⟩ ^ k` using `rfl`. Rewrite using `[this, map_zpow₀, norm_zpow, ha', one_zpow]`.
-/
theorem UnitAt.zpow {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {a : ℂ} (ha : UnitAt lam a) (k : ℤ) :
    UnitAt lam (a ^ k) := by
  obtain ⟨ha, ha'⟩ := ha
  refine ⟨zpow_mem ha k, ?_⟩
  simp only [lamC, ha, zpow_mem ha k, dif_pos] at ha' ⊢
  have : (⟨a ^ k, zpow_mem ha k⟩ : Qbar) = ⟨a, ha⟩ ^ k := rfl
  rw [this, map_zpow₀, norm_zpow, ha', one_zpow]

/- English proof (translation)
Establish `h : (-1 : ℂ) ∈ Qbar` using `neg_mem (one_mem _)`. Use `⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [lamC, h, dif_pos]`. Establish `: (⟨-1, h⟩ : Qbar) = -1` using `rfl`. Rewrite using `[this, map_neg, map_one, norm_neg, norm_one]`.
-/
theorem unitAt_neg_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : UnitAt lam (-1) := by
  have h : (-1 : ℂ) ∈ Qbar := neg_mem (one_mem _)
  refine ⟨h, ?_⟩
  simp only [lamC, h, dif_pos]
  have : (⟨-1, h⟩ : Qbar) = -1 := rfl
  rw [this, map_neg, map_one, norm_neg, norm_one]

end Main

open GlobalTheory.NormSum.VacMove in

/- English proof (translation)
Introduce `D cc δ hc N N' hev e0 he _ W g g' L L' c hL hL' hO`. Take `⟨ε, -, a1, a2, h3⟩` from `exists_half_idem D`. Establish `h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε`. Establish `a3 : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, a1]`. Take the linear combination `a1 + a3 + 2 * a2`.

Establish `h2 : sgA D (ε + sgA D ε) = ε + sgA D ε` using `by rw [map_add, sgA_sgA, add_comm]`. Use `⟨fun z z' x x' hz hz' hx hx' => ?_, fun p hp lam hg hg' => ?_⟩` and prove the remaining obligations. Take `⟨y, b1, b2, b3⟩` from `exists_trivial_inert h1 h2 h3 g hz hx`. Take `⟨y', c1, c2, c3⟩` from `exists_trivial_inert h1 h2 h3 g' hz' hx'`. Take `⟨k, hk⟩` from `scalar_formula hc hev he W hL hL' hO h1 h2 h3 b1 c1 b2 c2`.

Use `⟨1, Or.inl rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, ← b3, ← c3, ← Units.val_pow_eq_pow_val, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm W.ep, mul_comm W.ep']`. Take `⟨y, b1, b2, b3⟩` from `exists_solution a1 a2 h1 h2 g`. Take `⟨y', c1, c2, c3⟩` from `exists_solution a1 a2 h1 h2 g'`. Take `⟨k, hk⟩` from `scalar_formula hc hev he W hL hL' hO h1 h2 h3 (fun q hq hi => b2 q hq ((h3 q hq).1 hi)) (fun q hq hi => c2 q hq ((h3 q hq).1 hi)) b1 c1`.

Establish `hu : ∀ {n : ℕ} (χ : HeckeU D n) (x : (AE D)ˣ), ZeroAt D p ((x : AE D) - 1) → UnitAt lam ((χ.f x : ℂˣ) : ℂ)`. Introduce `n χ x hx`. Take `⟨⟨m, -⟩, -, u⟩` from `GlobalTheory.HeckeVal.hecke_values D n χ x`. Conclude with `⟨m, u p lam ⟨1, ⟨by simp, by simp⟩, by rwa [mul_one]⟩⟩`. Express the relevant statement in the definitionally equal form `UnitAt lam c`.

Rewrite using `[hk, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← zpow_natCast]`. Conclude with `((unitAt_neg_one lam).zpow _).mul (((hu _ _ (c3 p hp.out hg')).zpow _).mul ((hu _ _ (b3 p hp.out hg)).zpow _))`.
-/
theorem vacuum_scalar : ∀ D : D7, odd4 D := by
  intro D cc δ hc N N' hev e0 he _ W g g' L L' c hL hL' hO
  obtain ⟨ε, -, a1, a2, h3⟩ := exists_half_idem D
  have h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε := by
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    linear_combination a1 + a3 + 2 * a2
  have h2 : sgA D (ε + sgA D ε) = ε + sgA D ε := by rw [map_add, sgA_sgA, add_comm]
  refine ⟨fun z z' x x' hz hz' hx hx' => ?_, fun p hp lam hg hg' => ?_⟩
  · obtain ⟨y, b1, b2, b3⟩ := exists_trivial_inert h1 h2 h3 g hz hx
    obtain ⟨y', c1, c2, c3⟩ := exists_trivial_inert h1 h2 h3 g' hz' hx'
    obtain ⟨k, hk⟩ := scalar_formula hc hev he W hL hL' hO h1 h2 h3 b1 c1 b2 c2
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [hk, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, ← b3, ← c3, ← Units.val_pow_eq_pow_val,
      mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      ← zpow_mul, mul_comm W.ep, mul_comm W.ep']
  · obtain ⟨y, b1, b2, b3⟩ := exists_solution a1 a2 h1 h2 g
    obtain ⟨y', c1, c2, c3⟩ := exists_solution a1 a2 h1 h2 g'
    obtain ⟨k, hk⟩ := scalar_formula hc hev he W hL hL' hO h1 h2 h3 (fun q hq hi => b2 q hq ((h3 q hq).1 hi))
      (fun q hq hi => c2 q hq ((h3 q hq).1 hi)) b1 c1
    have hu : ∀ {n : ℕ} (χ : HeckeU D n) (x : (AE D)ˣ), ZeroAt D p ((x : AE D) - 1) →
        UnitAt lam ((χ.f x : ℂˣ) : ℂ) := by
      intro n χ x hx
      obtain ⟨⟨m, -⟩, -, u⟩ := GlobalTheory.HeckeVal.hecke_values D n χ x
      exact ⟨m, u p lam ⟨1, ⟨by simp, by simp⟩, by rwa [mul_one]⟩⟩
    change UnitAt lam c
    rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← zpow_natCast]
    exact ((unitAt_neg_one lam).zpow _).mul (((hu _ _ (c3 p hp.out hg')).zpow _).mul ((hu _ _ (b3 p hp.out hg)).zpow _))

end GlobalTheory.VacuumScalar
