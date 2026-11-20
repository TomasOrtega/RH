import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import GroundTheory.LocalFields.FilteredSurj

noncomputable section

open Polynomial Formalism.UG

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Valued.v (σ x) ≤ 1`. Rewrite using `[hσ]`. Conclude with `hx`.
-/
theorem mem_intL_of {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]; exact hx

def sigO (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  σ.restrict (intL L) (intL L) fun _ hx => mem_intL_of hσ hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_sigO (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (x : intL L) :
    ((sigO σ hσ x : intL L) : L) = σ x := rfl

def piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : intL L :=
  ⟨ϖ, by
    change Valued.v ϖ ≤ 1
    rw [h.2.2.2.1]
    exact_mod_cast (WithZero.coe_le_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1))⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : ((piO h : intL L) : L) = ϖ := rfl

def unitFil {R : Type} [CommRing R] (I : Ideal R) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : Rˣ) : R) - 1 = (a : R) * ((b : R) - 1) + ((a : R) - 1) := by push_cast; ring
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e]; exact I.add_mem (I.mul_mem_left _ hb) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : Rˣ) : R) - 1 = -((a⁻¹ : Rˣ) : R) * ((a : R) - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [e]; exact I.mul_mem_left _ ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_unitFil {R : Type} [CommRing R] {I : Ideal R} {u : Rˣ} : u ∈ unitFil I ↔ (u : R) - 1 ∈ I := Iff.rfl

def piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (m : ℕ) :
    Ideal (GlobalTheory.UTr.Alg P) :=
  Ideal.span {algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ^ m}

def filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (m : ℕ) :
    Subgroup (GlobalTheory.UTr.Alg P)ˣ :=
  unitFil (piPow h P m)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (sigO σ h.2.1)} {m : ℕ}
    {u : (GlobalTheory.UTr.Alg P)ˣ} : u ∈ filt h P m ↔ (u : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P m := Iff.rfl

/- English proof (translation)
Introduce `a b hab` and use `by unfold piPow rw [Ideal.span_singleton_le_span_singleton] exact pow_dvd_pow _ hab`.
-/
theorem piPow_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) :
    Antitone (piPow h P) := fun a b hab => by
  unfold piPow
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow _ hab

/- English proof (translation)
Introduce `a b hab _ hu` and use `piPow_antitone h P hab hu`.
-/
theorem filt_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) :
    Antitone (filt h P) := fun a b hab _ hu => piPow_antitone h P hab hu

/- English proof (translation)
Use extensionality with `u`. Simplify using `[filt, mem_unitFil, piPow]`.
-/
theorem filt_zero {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) :
    filt h P 0 = ⊤ := by
  ext u; simp [filt, mem_unitFil, piPow]

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Assume the negation of the conclusion as `hϖ`. Take `⟨y, i, hi, e⟩` from `hM.exists_inv hϖ`. Establish `hlt : Valued.v ((y : L) * ϖ) < 1`. Rewrite using `[map_mul, h.2.2.2.1]`. Establish `hy : Valued.v (y : L) ≤ 1` using `y.2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `(WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))` after adjusting the coercions. Establish `hi1 : (i : L) = 1 - (y : L) * ϖ`. Use `congrArg Subtype.val e` as an intermediate fact.

Simplify using `only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this`. Take the linear combination `this`. Establish `hv : Valued.v (i : L) = 1` using `by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt`. Establish `hi0 : (i : L) ≠ 0`. Introduce `h0`.

Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`. Establish `hinv : (i : L)⁻¹ ∈ intL L`. Express the relevant statement in the definitionally equal form `Valued.v ((i : L)⁻¹) ≤ 1`. Rewrite using `[map_inv₀, hv, inv_one]`.

Establish `hu : IsUnit i` using `isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩`. Conclude with `hM.ne_top (M.eq_top_of_isUnit_mem hi hu)`.
-/
theorem piO_mem_of_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by
  by_contra hϖ
  obtain ⟨y, i, hi, e⟩ := hM.exists_inv hϖ
  have hlt : Valued.v ((y : L) * ϖ) < 1 := by
    rw [map_mul, h.2.2.2.1]
    have hy : Valued.v (y : L) ≤ 1 := y.2
    calc Valued.v (y : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
  have hi1 : (i : L) = 1 - (y : L) * ϖ := by
    have := congrArg Subtype.val e
    simp only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this
    linear_combination this
  have hv : Valued.v (i : L) = 1 := by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt
  have hi0 : (i : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (i : L)⁻¹ ∈ intL L := by
    change Valued.v ((i : L)⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hu : IsUnit i := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩
  exact hM.ne_top (M.eq_top_of_isUnit_mem hi hu)

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Take `⟨M, hM, hxM⟩` from `Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `hmax` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := intL L) M`. Establish `hϖ : algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ∈ M` using `piO_mem_of_isMaximal h hmax`. Establish `h1 : 1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a ∈ M` using `hxM (Ideal.mem_span_singleton_self _)`.

Establish `: (1 : GlobalTheory.UTr.Alg P) ∈ M`. Use `M.sub_mem h1 (M.mul_mem_right a hϖ)` as an intermediate fact. Simplify using `using this`. Conclude with `hM.ne_top ((Ideal.eq_top_iff_one M).2 this)`.
-/
theorem isUnit_one_add_piO_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) :
    IsUnit (1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a) := by
  by_contra hn
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := intL L) M
  have hϖ : algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ∈ M := piO_mem_of_isMaximal h hmax
  have h1 : 1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a ∈ M := hxM (Ideal.mem_span_singleton_self _)
  have : (1 : GlobalTheory.UTr.Alg P) ∈ M := by
    have := M.sub_mem h1 (M.mul_mem_right a hϖ)
    simpa using this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 this)

/- English proof (translation)
Establish `hx1 : x - 1 ∈ piPow h P 1` using `piPow_antitone h P hm hx`. Unfold `piPow at hx1`. Rewrite `hx1` using `[pow_one, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `hx1`. Use `isUnit_one_add_piO_mul h P a` as an intermediate fact.

Rewrite `this` using `[mul_comm, ha, add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem isUnit_of_sub_one_mem {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) {m : ℕ} (hm : 1 ≤ m) {x : GlobalTheory.UTr.Alg P} (hx : x - 1 ∈ piPow h P m) :
    IsUnit x := by
  have hx1 : x - 1 ∈ piPow h P 1 := piPow_antitone h P hm hx
  unfold piPow at hx1
  rw [pow_one, Ideal.mem_span_singleton'] at hx1
  obtain ⟨a, ha⟩ := hx1
  have := isUnit_one_add_piO_mul h P a
  rwa [mul_comm, ha, add_sub_cancel] at this

end GlobalTheory.NormEq
