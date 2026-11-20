import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

abbrev FilB (P : LocPrime l) (a : ℤ) : Submodule ↥(botExt l).1 P.R.BdR := (P.PD (botExt l)).Fil a

abbrev qB (P : LocPrime l) : ℚ_[l] →+* P.R.BdR := algebraMap ℚ_[l] P.R.BdR

abbrev oB (P : LocPrime l) : Om l →+* P.R.BdR := algebraMap (Om l) P.R.BdR

abbrev tD (P : LocPrime l) : P.R.BdR := P.ιB P.tB

abbrev frK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) := (P.PD K).σ

def NearZ (P : LocPrime l) (M : ℕ) (b : P.R.BdR) : Prop :=
  ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - b ∈ FilB P (M : ℤ)

def primeTo (l s : ℕ) : Finset ℕ := (Finset.range (l ^ s)).filter (fun a => ¬ l ∣ a)

def levSum (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) : Om l :=
  ∑ i ∈ Finset.range s, (l : Om l) ^ (j * i) *
      ∑ a ∈ T, (((frK P K ^ i) (c a) : ↥(K0 K)) : Om l) * (m a : Om l) ^ j * P.ζQ s ^ (m a * l ^ i) +
    (l : Om l) ^ (s * j) * (d : Om l)

def cycVal (P : LocPrime l) (K : FinExt l) (s e : ℕ) (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)) : Om l :=
  ∑ i ∈ Finset.range s, (l : Om l) ^ (e * i) *
      ∑ a ∈ primeTo l s, (((frK P K ^ i) (lam a) : ↥(K0 K)) : Om l) * P.ζQ s ^ (a * l ^ i) +
    (l : Om l) ^ (s * e) * (d : Om l)

variable {P : LocPrime l} (AI : LocAinf l P)

def io : Ainf l →+* P.R.BdR := (P.ιB : P.R.B →+* P.R.BdR).comp AI.ιA

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem io_apply (a : Ainf l) : io AI a = P.ιB (AI.ιA a) := rfl

def Lat (M n : ℕ) : AddSubgroup P.R.BdR where
  carrier := {b | ∃ a : Ainf l, b - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P (M : ℤ)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro b b' ⟨a, ha⟩ ⟨a', ha'⟩
    refine ⟨a + a', ?_⟩
    have := add_mem ha ha'
    rw [mul_add, map_add]
    convert this using 1
    ring
  neg_mem' := by
    rintro b ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have := neg_mem ha
    rw [mul_neg, map_neg]
    convert this using 1
    ring

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Lat {M n : ℕ} {b : P.R.BdR} :
    b ∈ Lat AI M n ↔ ∃ a : Ainf l, b - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P (M : ℤ) := Iff.rfl

def Lifts (K : FinExt l) (w : Ainf l) (c : ↥(K0 K)) : Prop :=
  AI.ιA w = algebraMap ↥(K0 K) P.R.B c

def epsT (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s)

def Step (g : GQ l) (U : ℤ_[l]) (x : Ainf l) (k : ℕ) (p r : Ainf l) : Prop :=
  algebraMap ℤ_[l] (Ainf l) U * AI.actW g p * x ^ k - AI.actW g x ^ k * p = AI.actW g x ^ k * r

def Solv (K : FinExt l) (s : ℕ) (g : GQ l) (U : ℤ_[l]) (q₀ : Ainf l) : Prop :=
  ∃ p q : ℕ → Ainf l, q 0 = q₀ ∧ (∀ k, ∀ h ∈ Hinf K, AI.actW h (p k) = p k) ∧
    ∀ k, Step AI g U AI.μ (k + 1) (p k) (AI.μ * q k - ((l : ℕ) : Ainf l) ^ s * q (k + 1))

/- English proof (translation)
The claim follows from `(P.PD (botExt l)).Fil_mul a b x y hx hy`.
-/
theorem FilB_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ FilB P a) (hy : y ∈ FilB P b) :
    x * y ∈ FilB P (a + b) := (P.PD (botExt l)).Fil_mul a b x y hx hy

/- English proof (translation)
Simplify using `using FilB_mul hx hy`.
-/
theorem FilB_zero_mul {b : ℤ} {x y : P.R.BdR} (hx : x ∈ FilB P 0) (hy : y ∈ FilB P b) :
    x * y ∈ FilB P b := by simpa using FilB_mul hx hy

/- English proof (translation)
The claim follows from `(P.PD (botExt l)).one_mem`.
-/
theorem one_mem_FilB : (1 : P.R.BdR) ∈ FilB P 0 := (P.PD (botExt l)).one_mem

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using one_mem_FilB`. Consider the case `succ n ih`. Use `FilB_mul ih hx` as an intermediate fact. Rewrite using `[pow_succ]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FilB_pow {a : ℤ} {x : P.R.BdR} (hx : x ∈ FilB P a) (n : ℕ) : x ^ n ∈ FilB P (n * a) := by
  induction n with
  | zero => simpa using one_mem_FilB
  | succ n ih =>
    have := FilB_mul ih hx
    rw [pow_succ]
    convert this using 2
    push_cast
    ring

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.exists_add_of_le h`. Use `clear h`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Use `le_trans ?_ ih` and prove the remaining obligations. Use `(P.PD (botExt l)).Fil_anti (a + k)` as an intermediate fact. Rewrite `this` using `[add_assoc, ← Nat.cast_succ]`. Then use the resulting hypothesis.
-/
theorem FilB_anti {a b : ℤ} (h : a ≤ b) : FilB P b ≤ FilB P a := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans ?_ ih
    have := (P.PD (botExt l)).Fil_anti (a + k)
    rwa [add_assoc, ← Nat.cast_succ] at this

/- English proof (translation)
Use `(FilB P a).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 c) hx` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, Algebra.smul_def]`. Then use the resulting hypothesis.
-/
theorem qB_mul_mem {a : ℤ} {x : P.R.BdR} (c : ℚ_[l]) (hx : x ∈ FilB P a) : qB P c * x ∈ FilB P a := by
  have := (FilB P a).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 c) hx
  rwa [algebraMap_smul, Algebra.smul_def] at this

/- English proof (translation)
Simplify using `using qB_mul_mem c (one_mem_FilB (P := P))`.
-/
theorem qB_mem (c : ℚ_[l]) : qB P c ∈ FilB P 0 := by simpa using qB_mul_mem c (one_mem_FilB (P := P))

/- English proof (translation)
Rewrite using `[← P.PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩]`. Conclude with `(P.PD (botExt l)).Fil_G _ a _ hx`.
-/
theorem act_mem {a : ℤ} {x : P.R.BdR} (g : GQ l) (hx : x ∈ FilB P a) : P.actQdR g x ∈ FilB P a := by
  rw [← P.PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩]
  exact (P.PD (botExt l)).Fil_G _ a _ hx

/- English proof (translation)
Use `(P.PD (botExt l)).mem_filtration_one` as an intermediate fact. Rewrite `this` using `[P.PD_ι, P.period_datum_t_eq]`. Then use the resulting hypothesis.
-/
theorem tD_mem : tD P ∈ FilB P 1 := by
  have := (P.PD (botExt l)).mem_filtration_one
  rwa [P.PD_ι, P.period_datum_t_eq] at this

/- English proof (translation)
Establish `h3` using `(P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ b`. Rewrite `h3` using `[P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR]`. Then use the resulting hypothesis.
-/
theorem ιB_act (g : GQ l) (b : P.R.B) : P.ιB (P.actQ g b) = P.actQdR g (P.ιB b) := by
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ b
  rwa [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3

/- English proof (translation)
Establish `h` using `(P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩`. Rewrite `h` using `[P.PD_actB, P.period_datum_t_eq, P.PD_χ]`. Rewrite using `[← ιB_act, h, map_smul, Algebra.smul_def]`.
-/
theorem act_tD (g : GQ l) : P.actQdR g (tD P) = qB P (P.χQ g : ℚ_[l]) * tD P := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  rw [← ιB_act, h, map_smul, Algebra.smul_def]

/- English proof (translation)
The claim follows from `AI.ainf_image_mem_filtration_zero (botExt l) a`.
-/
theorem io_mem (a : Ainf l) : io AI a ∈ FilB P 0 := AI.ainf_image_mem_filtration_zero (botExt l) a

/- English proof (translation)
The claim follows from `(AI.ainf_image_mem_filtration_one_iff (botExt l) AI.ξ).mpr ⟨1, (mul_one _).symm⟩`.
-/
theorem io_ξ_mem : io AI AI.ξ ∈ FilB P 1 := (AI.ainf_image_mem_filtration_one_iff (botExt l) AI.ξ).mpr ⟨1, (mul_one _).symm⟩

/- English proof (translation)
Rewrite using `[io_apply, io_apply, ← ιB_act]`. Conclude with `congrArg P.ιB (AI.ιA_act g a)`.
-/
theorem io_act (g : GQ l) (a : Ainf l) : io AI (AI.actW g a) = P.actQdR g (io AI a) := by
  rw [io_apply, io_apply, ← ιB_act]
  exact congrArg P.ιB (AI.ιA_act g a)

/- English proof (translation)
Introduce `a b h`. Apply `AI.ιA_inj` to reduce the goal to its premises. Apply `(P.PD (botExt l)).ι_inj` to reduce the goal to its premises. Rewrite using `[P.PD_ι, P.PD_ι]`. Conclude with `h`.
-/
theorem io_injective : Function.Injective (io AI) := by
  intro a b h
  apply AI.ιA_inj
  apply (P.PD (botExt l)).ι_inj
  rw [P.PD_ι, P.PD_ι]
  exact h

/- English proof (translation)
Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[T.zB, T.ιA]`. Conclude with `GlobalTheory.RingIface.aB_algebraMap_padicInt l z`.
-/
theorem ιA_zl (T : LocTied l P AI) (z : ℤ_[l]) :
    AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  apply T.eB.injective
  rw [T.zB, T.ιA]
  exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

/- English proof (translation)
Rewrite using `[io_apply, ιA_zl AI T, AlgHom.commutes]`.
-/
theorem io_zl (T : LocTied l P AI) (z : ℤ_[l]) :
    io AI (algebraMap ℤ_[l] (Ainf l) z) = qB P (z : ℚ_[l]) := by
  rw [io_apply, ιA_zl AI T, AlgHom.commutes]

/- English proof (translation)
The claim follows from `map_zlW l _ z`.
-/
theorem actW_zl (g : GQ l) (z : ℤ_[l]) :
    AI.actW g (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := map_zlW l _ z

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simpa using hb⟩`.
-/
theorem FilB_le_Lat {M n : ℕ} {b : P.R.BdR} (hb : b ∈ FilB P (M : ℤ)) : b ∈ Lat AI M n :=
  ⟨0, by simpa using hb⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, by simp⟩`.
-/
theorem io_mem_Lat (M n : ℕ) (a : Ainf l) : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ Lat AI M n :=
  ⟨a, by simp⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hb`. Use `add_mem (FilB_anti (Int.natCast_nonneg M) ha) (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))` as an intermediate fact. Simplify using `using this`.
-/
theorem Lat_mem_zero {M n : ℕ} {b : P.R.BdR} (hb : b ∈ Lat AI M n) : b ∈ FilB P 0 := by
  obtain ⟨a, ha⟩ := hb
  have := add_mem (FilB_anti (Int.natCast_nonneg M) ha) (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  simpa using this

/- English proof (translation)
Take `⟨a, ha⟩` from `hb`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Conclude with `⟨((l : ℕ) : Ainf l) ^ k * a, by rwa [← mul_assoc, ← pow_add]⟩`.
-/
theorem Lat_anti {M n n' : ℕ} (h : n ≤ n') {b : P.R.BdR} (hb : b ∈ Lat AI M n') : b ∈ Lat AI M n := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨((l : ℕ) : Ainf l) ^ k * a, by rwa [← mul_assoc, ← pow_add]⟩

/- English proof (translation)
Establish `h0` using `Lat_mem_zero AI hb'`. Take `⟨a, ha⟩` from `hb`. Take `⟨a', ha'⟩` from `hb'`. Use `⟨a * a', ?_⟩` and prove the remaining obligations. Use `add_mem (FilB_zero_mul h0 ha) (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * a)) ha')` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Lat_mul {M n n' : ℕ} {b b' : P.R.BdR} (hb : b ∈ Lat AI M n) (hb' : b' ∈ Lat AI M n') :
    b * b' ∈ Lat AI M (n + n') := by
  have h0 := Lat_mem_zero AI hb'
  obtain ⟨a, ha⟩ := hb
  obtain ⟨a', ha'⟩ := hb'
  refine ⟨a * a', ?_⟩
  have := add_mem (FilB_zero_mul h0 ha) (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * a)) ha')
  convert this using 1
  simp only [map_mul, map_pow, pow_add]
  ring

/- English proof (translation)
Use `Lat_mul AI (io_mem_Lat AI M 0 a) hb` as an intermediate fact. Simplify using `using this`.
-/
theorem io_mul_mem_Lat {M n : ℕ} (a : Ainf l) {b : P.R.BdR} (hb : b ∈ Lat AI M n) :
    io AI a * b ∈ Lat AI M n := by
  have := Lat_mul AI (io_mem_Lat AI M 0 a) hb
  simpa using this

/- English proof (translation)
Take `⟨a, ha⟩` from `hb`. Use `⟨AI.actW g a, ?_⟩` and prove the remaining obligations. Use `act_mem g ha` as an intermediate fact. Rewrite `this` using `[map_sub, ← io_act, map_mul, map_pow, map_natCast]`. Conclude with `this`.
-/
theorem act_mem_Lat {M n : ℕ} (g : GQ l) {b : P.R.BdR} (hb : b ∈ Lat AI M n) :
    P.actQdR g b ∈ Lat AI M n := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨AI.actW g a, ?_⟩
  have := act_mem g ha
  rw [map_sub, ← io_act, map_mul, map_pow, map_natCast] at this
  exact this

/- English proof (translation)
Rewrite using `[← io_zl AI T]`. Conclude with `io_mul_mem_Lat AI _ hb`.
-/
theorem qB_mul_mem_Lat (T : LocTied l P AI) {M n : ℕ} (z : ℤ_[l]) {b : P.R.BdR}
    (hb : b ∈ Lat AI M n) : qB P (z : ℚ_[l]) * b ∈ Lat AI M n := by
  rw [← io_zl AI T]
  exact io_mul_mem_Lat AI _ hb

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h0 : ((l : ℚ_[l]) ^ k) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`. Establish `h1 : qB P ((l : ℚ_[l]) ^ k)⁻¹ * (l : P.R.BdR) ^ k = 1`.

Rewrite using `[← map_natCast (qB P), ← map_pow, ← map_mul, inv_mul_cancel₀ h0, map_one]`. Use `qB_mul_mem ((l : ℚ_[l]) ^ k)⁻¹ ha` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_pow, map_natCast, pow_add]`. Take the linear combination `(-(b - (l : P.R.BdR) ^ n * io AI a)) * h1`.

Introduce `hb`. Use `Lat_mul AI (io_mem_Lat AI M k 1) hb` as an intermediate fact. Simplify using `using this`.
-/
theorem pow_mul_mem_Lat_iff {M n k : ℕ} {b : P.R.BdR} :
    (l : P.R.BdR) ^ k * b ∈ Lat AI M (k + n) ↔ b ∈ Lat AI M n := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h0 : ((l : ℚ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have h1 : qB P ((l : ℚ_[l]) ^ k)⁻¹ * (l : P.R.BdR) ^ k = 1 := by
      rw [← map_natCast (qB P), ← map_pow, ← map_mul, inv_mul_cancel₀ h0, map_one]
    have := qB_mul_mem ((l : ℚ_[l]) ^ k)⁻¹ ha
    convert this using 1
    simp only [map_mul, map_pow, map_natCast, pow_add]
    linear_combination (-(b - (l : P.R.BdR) ^ n * io AI a)) * h1
  · intro hb
    have := Lat_mul AI (io_mem_Lat AI M k 1) hb
    simpa using this

variable {AI} {K : FinExt l}

/- English proof (translation)
Rewrite using `[io_apply, h, ← P.PD_ι K, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem Lifts.io_eq {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) : io AI w = oB P (c : Om l) := by
  rw [io_apply, h, ← P.PD_ι K, AlgHom.commutes]
  rfl

/- English proof (translation)
Unfold `Lifts at h ⊢`. Rewrite using `[AI.ιA_φ, h, ← P.PD_φ K, (P.PD K).φ_K₀]`.
-/
theorem Lifts.frob {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) :
    Lifts AI K (WittVector.frobenius w) (frK P K c) := by
  unfold Lifts at h ⊢
  rw [AI.ιA_φ, h, ← P.PD_φ K, (P.PD K).φ_K₀]

/- English proof (translation)
Apply `io_injective AI` to reduce the goal to its premises. Rewrite using `[io_act, h.io_eq, P.actQdR_Om]`. Conclude with `congrArg (oB P) (hg c)`.
-/
theorem Lifts.act {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) {g : GQ l}
    (hg : g ∈ (K0 K).fixingSubgroup) : AI.actW g w = w := by
  apply io_injective AI
  rw [io_act, h.io_eq, P.actQdR_Om]
  exact congrArg (oB P) (hg c)

/- English proof (translation)
Unfold `Lifts at h h' ⊢`. Rewrite using `[map_add, map_add, h, h']`.
-/
theorem Lifts.add {w w' : Ainf l} {c c' : ↥(K0 K)} (h : Lifts AI K w c) (h' : Lifts AI K w' c') :
    Lifts AI K (w + w') (c + c') := by
  unfold Lifts at h h' ⊢
  rw [map_add, map_add, h, h']

/- English proof (translation)
Unfold `Lifts at h h' ⊢`. Rewrite using `[map_sub, map_sub, h, h']`.
-/
theorem Lifts.sub {w w' : Ainf l} {c c' : ↥(K0 K)} (h : Lifts AI K w c) (h' : Lifts AI K w' c') :
    Lifts AI K (w - w') (c - c') := by
  unfold Lifts at h h' ⊢
  rw [map_sub, map_sub, h, h']

/- English proof (translation)
Unfold `Lifts at h h' ⊢`. Rewrite using `[map_mul, map_mul, h, h']`.
-/
theorem Lifts.mul {w w' : Ainf l} {c c' : ↥(K0 K)} (h : Lifts AI K w c) (h' : Lifts AI K w' c') :
    Lifts AI K (w * w') (c * c') := by
  unfold Lifts at h h' ⊢
  rw [map_mul, map_mul, h, h']

/- English proof (translation)
The claim follows from `AI.ιA_inj (h.trans h'.symm)`.
-/
theorem Lifts.unique {w w' : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (h' : Lifts AI K w' c) :
    w = w' := AI.ιA_inj (h.trans h'.symm)

/- English proof (translation)
The claim follows from `IntermediateField.fixingSubgroup_le le_sup_left`.
-/
theorem Gj_le_fix (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_le le_sup_left

/- English proof (translation)
The claim follows from `IntermediateField.fixingSubgroup_le le_sup_left`.
-/
theorem Hinf_le_fix : Hinf K ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_le le_sup_left

variable {s : ℕ} {g : GQ l} {U : ℤ_[l]}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun _ => 0, rfl, fun _ _ _ => map_zero _, fun k => by simp [Step]⟩`.
-/
theorem Solv.zero : Solv AI K s g U 0 :=
  ⟨fun _ => 0, fun _ => 0, rfl, fun _ _ _ => map_zero _, fun k => by simp [Step]⟩

/- English proof (translation)
Take `⟨p, r, rfl, h1, h2⟩` from `h`. Take `⟨p', r', rfl, h1', h2'⟩` from `h'`. Use `⟨fun k => p k + p' k, fun k => r k + r' k, rfl, fun k h hh => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, h1 k h hh, h1' k h hh]`. Establish `a` using `h2 k`.

Establish `a'` using `h2' k`. Unfold `Step at a a' ⊢`. Rewrite using `[map_add]`. Take the linear combination `a + a'`.
-/
theorem Solv.add {q q' : Ainf l} (h : Solv AI K s g U q) (h' : Solv AI K s g U q') :
    Solv AI K s g U (q + q') := by
  obtain ⟨p, r, rfl, h1, h2⟩ := h
  obtain ⟨p', r', rfl, h1', h2'⟩ := h'
  refine ⟨fun k => p k + p' k, fun k => r k + r' k, rfl, fun k h hh => ?_, fun k => ?_⟩
  · rw [map_add, h1 k h hh, h1' k h hh]
  · have a := h2 k
    have a' := h2' k
    unfold Step at a a' ⊢
    rw [map_add]
    linear_combination a + a'

/- English proof (translation)
Take `⟨p, r, rfl, h1, h2⟩` from `h`. Use `⟨fun k => w * p k, fun k => w * r k, rfl, fun k h hh => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h1 k h hh, hw h hh]`. Establish `a` using `h2 k`. Unfold `Step at a ⊢`.

Rewrite using `[map_mul, hg]`. Take the linear combination `w * a`.
-/
theorem Solv.mul {q w : Ainf l} (h : Solv AI K s g U q) (hg : AI.actW g w = w)
    (hw : ∀ h ∈ Hinf K, AI.actW h w = w) : Solv AI K s g U (w * q) := by
  obtain ⟨p, r, rfl, h1, h2⟩ := h
  refine ⟨fun k => w * p k, fun k => w * r k, rfl, fun k h hh => ?_, fun k => ?_⟩
  · rw [map_mul, h1 k h hh, hw h hh]
  · have a := h2 k
    unfold Step at a ⊢
    rw [map_mul, hg]
    linear_combination w * a

/- English proof (translation)
The claim follows from `Finset.sum_induction q _ (fun _ _ => Solv.add) Solv.zero h`.
-/
theorem Solv.sum {ι : Type} (T : Finset ι) (q : ι → Ainf l) (h : ∀ i ∈ T, Solv AI K s g U (q i)) :
    Solv AI K s g U (∑ i ∈ T, q i) :=
  Finset.sum_induction q _ (fun _ _ => Solv.add) Solv.zero h

end GlobalTheory.ExpImage
