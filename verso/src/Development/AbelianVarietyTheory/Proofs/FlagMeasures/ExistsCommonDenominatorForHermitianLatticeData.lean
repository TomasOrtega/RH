import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulMemLattice
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DenClear

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ringOfIntegers_smul_eq {E : Type} [Field E] [NumberField E] (o : 𝓞 E) (x : E) :
    o • x = (o : E) * x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeO_mul {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a * b : 𝓞 E) : E) = (a : E) * b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeO_add {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a + b : 𝓞 E) : E) = (a : E) + b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeO_int {E : Type} [Field E] [NumberField E] (k : ℤ) : ((k : 𝓞 E) : E) = (k : E) := by
  rfl

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {e}`. Establish `h` using `hy e (Finset.mem_singleton_self e)`. Rewrite `h` using `[zsmul_eq_mul]`. Conclude with `⟨y, hy0, ⟨(y : E) * e, h⟩, rfl⟩`.
-/
theorem exists_int_mul_eq {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ o : 𝓞 E, (m : E) * e = o := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  rw [zsmul_eq_mul] at h
  exact ⟨y, hy0, ⟨(y : E) * e, h⟩, rfl⟩

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Take `⟨o, ho⟩` from `he`. Use `⟨(k : 𝓞 E) * o, ?_⟩` and prove the remaining obligations. Rewrite using `[coeO_mul, coeO_int, ← ho]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem clear_of_dvd {E : Type} [Field E] [NumberField E] {m D : ℤ} (h : m ∣ D) {e : E}
    (he : ∃ o : 𝓞 E, (m : E) * e = o) : ∃ o : 𝓞 E, (D : E) * e = o := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨o, ho⟩ := he
  refine ⟨(k : 𝓞 E) * o, ?_⟩
  rw [coeO_mul, coeO_int, ← ho]
  push_cast
  ring

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice`. Consider the case `exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice`. Consider the case `(apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice ..)`.
-/
theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice
  | exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice
  | (apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice ..)

/- English proof (translation)
Introduce `E _ _ n ι κ _ _ v g Hm sg Λ hΛ`. Use `choose mv hmv0 hmv using fun i => exists_int_mul_eq (v i)`. Use `choose mg hmg0 hmg using fun l => exists_int_smul_mem Λ hΛ (g l)`. Take `⟨s, hs⟩` from `Submodule.IsLattice.fg (A := E) (M := Λ)`. Use `choose mp hmp0 hmp using fun (p : κ × (Fin n → E)) => exists_int_mul_eq (∑ a, ∑ b, p.2 a * Hm a b * sg (g p.1 b))`.

Set `T : Finset (κ × (Fin n → E))` to `Finset.univ ×ˢ s`. Set `A : ℤ` to `∏ i, mv i`. Set `B : ℤ` to `∏ l, mg l`. Set `C : ℤ` to `∏ p ∈ T, mp p`. Establish `hA : A ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hmv0 i`.

Establish `hB : B ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hmg0 i`. Establish `hC : C ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hmp0 i`. Establish `dA : ∀ i, mv i ∣ A * B * C` using `fun i => ((Finset.dvd_prod_of_mem mv (Finset.mem_univ i)).mul_right B).mul_right C`. Establish `dB : ∀ l, mg l ∣ A * B * C` using `fun l => ((Finset.dvd_prod_of_mem mg (Finset.mem_univ l)).mul_left A).mul_right C`. Establish `dC : ∀ p ∈ T, mp p ∣ A * B * C` using `fun p hp => (Finset.dvd_prod_of_mem mp hp).mul_left _`.

Use `⟨A * B * C, mul_ne_zero (mul_ne_zero hA hB) hC, fun i => clear_of_dvd (dA i) (hmv i), ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx l`. Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Conclude with `clear_of_dvd (dC (l, x) (Finset.mem_product.2 ⟨Finset.mem_univ l, hx⟩)) (hmp (l, x))`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨o₁, h₁⟩` from `hx`. Take `⟨o₂, h₂⟩` from `hy`.

Use `⟨o₁ + o₂, ?_⟩` and prove the remaining obligations. Rewrite using `[coeO_add, ← h₁, ← h₂, ← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c x _ hx`. Take `⟨o, h⟩` from `hx`.

Use `⟨c * o, ?_⟩` and prove the remaining obligations. Rewrite using `[coeO_mul, ← h]`. Simplify using `only [Pi.smul_apply, ringOfIntegers_smul_eq, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Introduce `l`.

Take `⟨k, hk⟩` from `dB l`. Establish `: ((A * B * C : ℤ) : 𝓞 E) • g l = (k : 𝓞 E) • ((mg l : 𝓞 E) • g l)`. Rewrite using `[smul_smul, hk]`. Use `push_cast`. Rewrite using `[mul_comm]`.

Rewrite using `[this]`. Conclude with `Λ.smul_mem _ (hmg l)`.
-/
theorem den_clear : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  intro E _ _ n ι κ _ _ v g Hm sg Λ hΛ
  choose mv hmv0 hmv using fun i => exists_int_mul_eq (v i)
  choose mg hmg0 hmg using fun l => exists_int_smul_mem Λ hΛ (g l)
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := E) (M := Λ)
  choose mp hmp0 hmp using fun (p : κ × (Fin n → E)) =>
    exists_int_mul_eq (∑ a, ∑ b, p.2 a * Hm a b * sg (g p.1 b))
  let T : Finset (κ × (Fin n → E)) := Finset.univ ×ˢ s
  let A : ℤ := ∏ i, mv i
  let B : ℤ := ∏ l, mg l
  let C : ℤ := ∏ p ∈ T, mp p
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmv0 i
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmg0 i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmp0 i
  have dA : ∀ i, mv i ∣ A * B * C := fun i =>
    ((Finset.dvd_prod_of_mem mv (Finset.mem_univ i)).mul_right B).mul_right C
  have dB : ∀ l, mg l ∣ A * B * C := fun l =>
    ((Finset.dvd_prod_of_mem mg (Finset.mem_univ l)).mul_left A).mul_right C
  have dC : ∀ p ∈ T, mp p ∣ A * B * C := fun p hp =>
    (Finset.dvd_prod_of_mem mp hp).mul_left _
  refine ⟨A * B * C, mul_ne_zero (mul_ne_zero hA hB) hC, fun i => clear_of_dvd (dA i) (hmv i),
    ?_, ?_⟩
  · intro x hx l
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact clear_of_dvd (dC (l, x) (Finset.mem_product.2 ⟨Finset.mem_univ l, hx⟩)) (hmp (l, x))
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      rw [coeO_add, ← h₁, ← h₂, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply]
      ring
    | smul c x _ hx =>
      obtain ⟨o, h⟩ := hx
      refine ⟨c * o, ?_⟩
      rw [coeO_mul, ← h]
      simp only [Pi.smul_apply, ringOfIntegers_smul_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · intro l
    obtain ⟨k, hk⟩ := dB l
    have : ((A * B * C : ℤ) : 𝓞 E) • g l = (k : 𝓞 E) • ((mg l : 𝓞 E) • g l) := by
      rw [smul_smul, hk]
      push_cast
      rw [mul_comm]
    rw [this]
    exact Λ.smul_mem _ (hmg l)

end GlobalTheory.DenClear
