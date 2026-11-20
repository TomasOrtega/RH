import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ValuationIntCastLtOneIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lamv (l : ℕ) [Fact l.Prime] (m : ℕ) (s : G ℚ Ω) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((((cycZ (F := ℚ) (Ω := Ω) l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) - 1) / (l : Qbar l) ^ m

def HTCoAt (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg (m - c₀) (Z m s y) (h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

/- English proof (translation)
Establish `: CharZero (Qbar l)` using `charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Qbar l)).injective`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`.
-/
theorem natCast_ne_zero : (l : Qbar l) ≠ 0 := by
  have : CharZero (Qbar l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Qbar l)).injective
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_natCast_lt_one : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Rewrite using `[lamv, mul_div_cancel₀ _ (pow_ne_zero m natCast_ne_zero), map_sub, map_one]`.
-/
theorem pow_mul_lamv (m : ℕ) (s : G ℚ Ω) :
    (l : Qbar l) ^ m * lamv l m s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  rw [lamv, mul_div_cancel₀ _ (pow_ne_zero m natCast_ne_zero), map_sub, map_one]

/- English proof (translation)
Simplify using `[lamv]`.
-/
@[simp] theorem lamv_one (m : ℕ) : lamv l m (1 : G ℚ Ω) = 0 := by
  simp [lamv]

/- English proof (translation)
Apply `mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l)))` to reduce the goal to its premises. Establish `hs` using `pow_mul_lamv (l := l) m s`. Establish `ht` using `pow_mul_lamv (l := l) m t`. Rewrite using `[pow_mul_lamv, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]`. Take the linear combination `(-(algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]))) * hs - ((l : Qbar l) ^ m * lamv l m s + 1) * ht`.
-/
theorem lamv_mul (m : ℕ) (s t : G ℚ Ω) :
    lamv l m (s * t) = lamv l m s + lamv l m t + (l : Qbar l) ^ m * lamv l m s * lamv l m t := by
  apply mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l)))
  have hs := pow_mul_lamv (l := l) m s
  have ht := pow_mul_lamv (l := l) m t
  rw [pow_mul_lamv, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]
  linear_combination (-(algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]))) * hs -
    ((l : Qbar l) ^ m * lamv l m s + 1) * ht

/- English proof (translation)
Establish `h1 : PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Simplify `congrArg Units.val hs` using `[cycMod]`. Establish `h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m))`. Rewrite using `[RingHom.mem_ker, map_sub, h1, map_one, sub_self]`. Rewrite `h2` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`.

Take `⟨a, ha⟩` from `h2`. Establish `h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a` using `by rw [← ha]; ring`. Use `⟨a, h3, mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l))) ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul_lamv, h3, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]`. Simplify using the standard rewrite rules.
-/
theorem exists_lamv_eq {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) :
    ∃ a : ℤ_[l], ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a ∧ lamv l m s = algebraMap ℤ_[l] (Qbar l) a := by
  have h1 : PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa [cycMod] using congrArg Units.val hs
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, h1, map_one, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨a, ha⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  refine ⟨a, h3, mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l))) ?_⟩
  rw [pow_mul_lamv, h3, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  simp

/- English proof (translation)
Establish `hi : IsIntegral ℤ_[l] a` using `(Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val`. Establish `hq : IsIntegral ℚ_[l] a` using `Algebra.IsIntegral.isIntegral a`. Express the relevant statement in the definitionally equal form `spectralValue (minpoly ℚ_[l] a) ≤ 1`. Rewrite using `[spectralValue_le_one_iff (minpoly.monic hq)]`. Introduce `k`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]`. Conclude with `PadicInt.norm_le_one _`.
-/
theorem norm_le_one_of_mem {c : Coef l} {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
Take `⟨a, -, ha⟩` from `exists_lamv_eq hs`. Rewrite using `[ha, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']`. Conclude with `a.2`.
-/
theorem norm_lamv_le_one {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : ‖lamv l m s‖ ≤ 1 := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

def cob (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) : Submodule c.O (G ℚ Ω → Qbar l) :=
  Submodule.span c.O {f | ∃ w ∈ A, f = fun s : G ℚ Ω => j (s w) - j w}

section Cob

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨w, hw, rfl⟩`.
-/
theorem sub_mem_cob {w : Ω} (hw : w ∈ A) : (fun s : G ℚ Ω => j (s w) - j w) ∈ cob c A j :=
  Submodule.subset_span ⟨w, hw, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf`. Take `⟨q, o, g, hg⟩` from `Submodule.mem_span_set'.1 hf`. Use `choose w hw hgw using fun i => (g i).2`. Use `⟨q, fun i => o i, w, fun i => ⟨(o i).2, hw i⟩, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hg, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hgw i]`. Both sides reduce to the same expression. Introduce and unpack `⟨q, o, w, h, hf⟩`.

Establish `e : f = ∑ i, (⟨o i, (h i).1⟩ : c.O) • fun s : G ℚ Ω => j (s (w i)) - j (w i)`. Use function extensionality and compare the values at `s`. Rewrite using `[hf s, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (sub_mem_cob (h i).2)`.
-/
theorem mem_cob_iff {f : G ℚ Ω → Qbar l} : f ∈ cob c A j ↔ ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω),
    (∀ i, o i ∈ c.O ∧ w i ∈ A) ∧ ∀ s, f s = ∑ i, o i * (j (s (w i)) - j (w i)) := by
  constructor
  · intro hf
    obtain ⟨q, o, g, hg⟩ := Submodule.mem_span_set'.1 hf
    choose w hw hgw using fun i => (g i).2
    refine ⟨q, fun i => o i, w, fun i => ⟨(o i).2, hw i⟩, fun s => ?_⟩
    rw [← hg, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgw i]; rfl
  · rintro ⟨q, o, w, h, hf⟩
    have e : f = ∑ i, (⟨o i, (h i).1⟩ : c.O) • fun s : G ℚ Ω => j (s (w i)) - j (w i) := by
      funext s; rw [hf s, Finset.sum_apply]; rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (sub_mem_cob (h i).2)

/- English proof (translation)
The claim follows from `(cob c A j).smul_mem ⟨a, ha⟩ hf`.
-/
theorem mul_mem_cob {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) {a : Qbar l} (ha : a ∈ c.O) :
    (fun s => a * f s) ∈ cob c A j :=
  (cob c A j).smul_mem ⟨a, ha⟩ hf

/- English proof (translation)
Take `⟨q, o, w, -, h⟩` from `mem_cob_iff.1 hf`. Simplify using `[h]`.
-/
theorem apply_one_of_mem_cob {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) : f 1 = 0 := by
  obtain ⟨q, o, w, -, h⟩ := mem_cob_iff.1 hf
  simp [h]

/- English proof (translation)
Take `⟨q, o, w, h, hf⟩` from `mem_cob_iff.1 hf`. Use `⟨∑ i, o i * j (w i), ?_, fun σ s hs hσ => ?_⟩` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (norm_le_one_of_mem (h i).1) (norm_nonneg _) ((hj _).1 (h i).2)`.

Rewrite using `[hf s, map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hσ _ (h i).1, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_sub_of_mem_cob (hj : ReciprocityTheory.Neutral.Cmp.Compat l A j) {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) :
    ∃ x : Qbar l, ‖x‖ ≤ 1 ∧ ∀ (σ : Qbar l ≃+* Qbar l) (s : G ℚ Ω), (∀ w, j (s w) = σ (j w)) → (∀ a ∈ c.O, σ a = a) →
      f s = σ x - x := by
  obtain ⟨q, o, w, h, hf⟩ := mem_cob_iff.1 hf
  refine ⟨∑ i, o i * j (w i), ?_, fun σ s hs hσ => ?_⟩
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (norm_le_one_of_mem (h i).1) (norm_nonneg _) ((hj _).1 (h i).2)
  · rw [hf s, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hσ _ (h i).1, hs]
    ring

end Cob

def HTCoIn (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ReciprocityTheory.Neutral.Cmp.Compat l A j ∧ ∃ f ∈ cob c A j, ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) (Z m s y) (h * lamv l m s + f s)

section Co

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l} {Z Z' : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
  {m c₀ : ℕ} {y : (ZMod (l ^ m))ˣ} {h h' : Qbar l}

namespace HTCoIn

/- English proof (translation)
The claim follows from `H.1`.
-/
theorem compat (H : HTCoIn c A j Z m c₀ y h) : ReciprocityTheory.Neutral.Cmp.Compat l A j := H.1

/- English proof (translation)
Take `⟨hj, f, hf, H⟩` from `H`. Use `⟨hj, f, hf, fun s hs hm => (H s hs hm).trans ?_⟩` and prove the remaining obligations. Rewrite using `[norm_pow, norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_lt_one.le (by omega)`.
-/
theorem mono (H : HTCoIn c A j Z m c₀ y h) {c₁ : ℕ} (hc : c₀ ≤ c₁) : HTCoIn c A j Z m c₁ y h := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, f, hf, fun s hs hm => (H s hs hm).trans ?_⟩
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_lt_one.le (by omega)

/- English proof (translation)
Take `⟨hj, f, hf, H⟩` from `H`. Take `⟨-, f', hf', H'⟩` from `H'`. Use `⟨hj, f + f', add_mem hf hf', fun s hs hm => ?_⟩` and prove the remaining obligations. Establish `e : Z m s y + Z' m s y - ((h + h') * lamv l m s + (f + f') s) = (Z m s y - (h * lamv l m s + f s)) + (Z' m s y - (h' * lamv l m s + f' s))`. Rewrite using `[Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `Cg`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) (H' s hs hm))`.
-/
theorem add (H : HTCoIn c A j Z m c₀ y h) (H' : HTCoIn c A j Z' m c₀ y h') :
    HTCoIn c A j (fun r s x => Z r s x + Z' r s x) m c₀ y (h + h') := by
  obtain ⟨hj, f, hf, H⟩ := H
  obtain ⟨-, f', hf', H'⟩ := H'
  refine ⟨hj, f + f', add_mem hf hf', fun s hs hm => ?_⟩
  have e : Z m s y + Z' m s y - ((h + h') * lamv l m s + (f + f') s) =
      (Z m s y - (h * lamv l m s + f s)) + (Z' m s y - (h' * lamv l m s + f' s)) := by
    rw [Pi.add_apply]; ring
  unfold Cg
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) (H' s hs hm))

/- English proof (translation)
Take `⟨hj, f, hf, H⟩` from `H`. Use `⟨hj, _, mul_mem_cob hf ha, fun s hs hm => ?_⟩` and prove the remaining obligations. Establish `e : a * Z m s y - (a * h * lamv l m s + a * f s) = a * (Z m s y - (h * lamv l m s + f s))` using `by ring`. Unfold `Cg`. Rewrite using `[e, norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem ha)).trans (H s hs hm)`.
-/
theorem mul_left (H : HTCoIn c A j Z m c₀ y h) {a : Qbar l} (ha : a ∈ c.O) :
    HTCoIn c A j (fun r s x => a * Z r s x) m c₀ y (a * h) := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, _, mul_mem_cob hf ha, fun s hs hm => ?_⟩
  have e : a * Z m s y - (a * h * lamv l m s + a * f s) = a * (Z m s y - (h * lamv l m s + f s)) := by ring
  unfold Cg
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem ha)).trans (H s hs hm)

/- English proof (translation)
Simplify `H.add (H'.mul_left (c.O.neg_mem c.O.one_mem))` using `[sub_eq_add_neg]`.
-/
theorem sub (H : HTCoIn c A j Z m c₀ y h) (H' : HTCoIn c A j Z' m c₀ y h') :
    HTCoIn c A j (fun r s x => Z r s x - Z' r s x) m c₀ y (h - h') := by
  simpa [sub_eq_add_neg] using H.add (H'.mul_left (c.O.neg_mem c.O.one_mem))

/- English proof (translation)
Take `⟨hj, f, hf, H⟩` from `H`. Use `⟨hj, f + g, add_mem hf hg, fun s hs hm => ?_⟩` and prove the remaining obligations. Establish `e : Z' m s y' - (h' * lamv l m s + (f + g) s) = (Z' m s y' - (Z m s y + g s)) + ((Z m s y - (h * lamv l m s + f s)) + (h - h') * lamv l m s)`. Rewrite using `[Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `Cg`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hZ s hs hm) ?_)` and prove the remaining obligations. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (norm_lamv_le_one hm)).trans hh`.
-/
theorem congr (H : HTCoIn c A j Z m c₀ y h) {y' : (ZMod (l ^ m))ˣ} {g : G ℚ Ω → Qbar l} (hg : g ∈ cob c A j)
    (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Cg (m - c₀) (Z' m s y') (Z m s y + g s)) (hh : Cg (m - c₀) h h') :
    HTCoIn c A j Z' m c₀ y' h' := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, f + g, add_mem hf hg, fun s hs hm => ?_⟩
  have e : Z' m s y' - (h' * lamv l m s + (f + g) s) =
      (Z' m s y' - (Z m s y + g s)) + ((Z m s y - (h * lamv l m s + f s)) + (h - h') * lamv l m s) := by
    rw [Pi.add_apply]; ring
  unfold Cg
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hZ s hs hm) ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) ?_)
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_lamv_le_one hm)).trans hh

/- English proof (translation)
Take `⟨-, f, hf, H⟩` from `H`. Simplify `H 1 (one_mem _) (map_one _)` using `[apply_one_of_mem_cob hf]`.
-/
theorem cg_one (H : HTCoIn c A j Z m c₀ y h) : Cg (m - c₀) (Z m 1 y) 0 := by
  obtain ⟨-, f, hf, H⟩ := H
  simpa [apply_one_of_mem_cob hf] using H 1 (one_mem _) (map_one _)

end HTCoIn

/- English proof (translation)
Assemble the required witnesses or components as `⟨hj, f, hf, fun _ _ _ => by simp [Cg]⟩`.
-/
theorem htCoIn_lamv (hj : ReciprocityTheory.Neutral.Cmp.Compat l A j) {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : HTCoIn c A j (fun r s _ => h * lamv l r s + f s) m c₀ y h :=
  ⟨hj, f, hf, fun _ _ _ => by simp [Cg]⟩

end Co

/- English proof (translation)
Take `⟨j, hj⟩` from `ReciprocityTheory.Neutral.Cmp.exists_compat (p := l) ℚ A hA`. Conclude with `⟨j, fun m y => by simpa using htCoIn_lamv hj (sub_mem_cob (c := c) hw) m 0 y 1⟩`.
-/
example [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (w : Ω) (hw : w ∈ A) :
    ∃ j : Ω →+* Qbar l, ∀ (m : ℕ) (y : (ZMod (l ^ m))ˣ),
      HTCoIn c A j (fun r s _ => lamv l r s + (j (s w) - j w)) m 0 y 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat (p := l) ℚ A hA
  exact ⟨j, fun m y => by simpa using htCoIn_lamv hj (sub_mem_cob (c := c) hw) m 0 y 1⟩

/- English proof (translation)
Introduce `H`. Establish `h1` using `H.cg_one`. Rewrite `h1` using `[Cg, sub_zero, norm_one, norm_pow]`. Conclude with `absurd (pow_lt_one₀ (norm_nonneg _) norm_natCast_lt_one (by omega)) (not_lt.2 h1)`.
-/
example (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) {m c₀ : ℕ} (hm : c₀ < m) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) :
    ¬ HTCoIn c A j (fun _ _ _ => 1) m c₀ y h := by
  intro H
  have h1 := H.cg_one
  rw [Cg, sub_zero, norm_one, norm_pow] at h1
  exact absurd (pow_lt_one₀ (norm_nonneg _) norm_natCast_lt_one (by omega)) (not_lt.2 h1)

/- English proof (translation)
Introduce `H`. Establish `h1` using `(H.compat ((l : Ω)⁻¹)).1 trivial`. Rewrite `h1` using `[map_inv₀, map_natCast, norm_inv, inv_le_one₀ (norm_pos_iff.2 natCast_ne_zero)]`. Conclude with `absurd norm_natCast_lt_one (not_lt.2 h1)`.
-/
example (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ)
    (h : Qbar l) : ¬ HTCoIn c ⊤ j Z m c₀ y h := by
  intro H
  have h1 := (H.compat ((l : Ω)⁻¹)).1 trivial
  rw [map_inv₀, map_natCast, norm_inv, inv_le_one₀ (norm_pos_iff.2 natCast_ne_zero)] at h1
  exact absurd norm_natCast_lt_one (not_lt.2 h1)

end GlobalTheory.LambdaValuationPowers
