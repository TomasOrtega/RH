import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := (IntAt.coe P (-1)).mul ha
    simpa using h

def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

variable {P}

/- English proof (translation)
The claim follows from `(intRing P).zero_mem`.
-/
theorem intAt_zero : IntAt P (0 : E) := (intRing P).zero_mem
/- English proof (translation)
The claim follows from `(intRing P).one_mem`.
-/
theorem intAt_one : IntAt P (1 : E) := (intRing P).one_mem
/- English proof (translation)
The claim follows from `(intRing P).neg_mem ha`.
-/
theorem intAt_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := (intRing P).neg_mem ha
/- English proof (translation)
The claim follows from `(intRing P).sub_mem ha hb`.
-/
theorem intAt_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := (intRing P).sub_mem ha hb
/- English proof (translation)
The claim follows from `(intRing P).pow_mem ha k`.
-/
theorem intAt_pow {a : E} (ha : IntAt P a) (k : ℕ) : IntAt P (a ^ k) := (intRing P).pow_mem ha k
/- English proof (translation)
The claim follows from `natCast_mem (intRing P) k`.
-/
theorem intAt_nat (k : ℕ) : IntAt P (k : E) := natCast_mem (intRing P) k
/- English proof (translation)
The claim follows from `(intRing P).sum_mem h`.
-/
theorem intAt_sum {ι : Type} (s : Finset ι) {f : ι → E} (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) :=
  (intRing P).sum_mem h

/- English proof (translation)
The claim follows from `map_one (redHom P)`.
-/
theorem reduction_one₂ : redP P (1 : E) = 1 := map_one (redHom P)
/- English proof (translation)
The claim follows from `map_zero (redHom P)`.
-/
theorem reduction_zero : redP P (0 : E) = 0 := map_zero (redHom P)

/- English proof (translation)
The claim follows from `map_sub (redHom P) ⟨a, ha⟩ ⟨b, hb⟩`.
-/
theorem reduction_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a - b) = redP P a - redP P b :=
  map_sub (redHom P) ⟨a, ha⟩ ⟨b, hb⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using reduction_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, reduction_add (h a (Finset.mem_insert_self _ _)) (intAt_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]`.
-/
theorem reduction_sum₂ {ι : Type} (s : Finset ι) {f : ι → E} (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using reduction_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, reduction_add (h a (Finset.mem_insert_self _ _))
      (intAt_sum s fun i hi => h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/- English proof (translation)
Set `B : Matrix ι ι (intRing P)` to `Matrix.of fun i j => ⟨A i j, h i j⟩`. Establish `h1 : A.det = (B.det : E)`. Use `(intRing P).subtype.map_det B` as an intermediate fact. Rewrite `this` using `[Subring.coe_subtype]`. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `⟨h1 ▸ B.det.2, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `(redHom P).map_det B`.
-/
theorem det_int {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι E} (h : ∀ i j, IntAt P (A i j)) :
    IntAt P A.det ∧ redP P A.det = (A.map (redP P)).det := by
  let B : Matrix ι ι (intRing P) := Matrix.of fun i j => ⟨A i j, h i j⟩
  have h1 : A.det = (B.det : E) := by
    have := (intRing P).subtype.map_det B
    rw [Subring.coe_subtype] at this
    rw [this]
    rfl
  refine ⟨h1 ▸ B.det.2, ?_⟩
  rw [h1]
  exact (redHom P).map_det B

/- English proof (translation)
The claim follows from `Ideal.absNorm_mem _`.
-/
theorem qOf_mem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _

/- English proof (translation)
Establish `: qOf P ≠ 0` using `fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `this` after adjusting the coercions.
-/
theorem qOf_ne_zero : ((qOf P : ℕ) : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

/- English proof (translation)
Use `reduction_coe P ((qOf P : ℕ) : 𝓞 E)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Rewrite using `[this]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 qOf_mem`.
-/
theorem reduction_absNorm_eq_zero : redP P ((qOf P : ℕ) : E) = 0 := by
  have := reduction_coe P ((qOf P : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 qOf_mem

/- English proof (translation)
Establish `e : a = (qOf P : E) * (a / (qOf P : E))` using `by field_simp [qOf_ne_zero (P := P)]`. Rewrite using `[e, reduction_mul (intAt_nat _) h, reduction_absNorm_eq_zero, zero_mul]`.
-/
theorem redP_eq_zero_of_div {a : E} (h : IntAt P (a / (qOf P : E))) : redP P a = 0 := by
  have e : a = (qOf P : E) * (a / (qOf P : E)) := by field_simp [qOf_ne_zero (P := P)]
  rw [e, reduction_mul (intAt_nat _) h, reduction_absNorm_eq_zero, zero_mul]

/- English proof (translation)
Take `⟨r, s, hs, h⟩` from `ha`. Establish `hr : r ∈ P.asIdeal`. Use `reduction_spec P hs h` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this.symm`.

Take `⟨I, hI⟩ : P.asIdeal ∣ Ideal.span {((qOf P : ℕ) : 𝓞 E)}` from `Ideal.dvd_span_singleton.2 qOf_mem`. Establish `hIP : ¬ I ≤ P.asIdeal`. Introduce `hle`. Apply `hq` to reduce the goal to its premises. Establish `: Ideal.span {((qOf P : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2`.

Rewrite using `[hI, sq]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self _)`. Take `⟨s', hs'I, hs'⟩` from `Set.not_subset.1 hIP`. Establish `hm : r * s' ∈ Ideal.span {((qOf P : ℕ) : 𝓞 E)}` using `hI ▸ Ideal.mul_mem_mul hr hs'I`.

Take `⟨r', hr'⟩` from `Ideal.mem_span_singleton'.1 hm`. Use `⟨r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap (𝓞 E) E) hr'`. Simplify using `only [map_mul, map_natCast] at e`. Establish `hq0` using `qOf_ne_zero (P := P)`.

Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm ((qOf P : ℕ) : E), e, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intAt_div_of_redP (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a : E} (ha : IntAt P a) (h0 : redP P a = 0) :
    IntAt P (a / (qOf P : E)) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hr : r ∈ P.asIdeal := by
    have := reduction_spec P hs h
    rw [h0, mul_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  obtain ⟨I, hI⟩ : P.asIdeal ∣ Ideal.span {((qOf P : ℕ) : 𝓞 E)} := Ideal.dvd_span_singleton.2 qOf_mem
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hle
    apply hq
    have : Ideal.span {((qOf P : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hI, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨s', hs'I, hs'⟩ := Set.not_subset.1 hIP
  have hm : r * s' ∈ Ideal.span {((qOf P : ℕ) : 𝓞 E)} := hI ▸ Ideal.mul_mem_mul hr hs'I
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  have e := congrArg (algebraMap (𝓞 E) E) hr'
  simp only [map_mul, map_natCast] at e
  have hq0 := qOf_ne_zero (P := P)
  rw [map_mul]
  field_simp
  rw [mul_comm ((qOf P : ℕ) : E), e, ← h]
  ring

/- English proof (translation)
Distinguish the cases in `ha : IntAt P a`. Rewrite using `[reduction_mul ha hu, h1, mul_one]`. Rewrite using `[reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral]`. Introduce `h`. Apply `ha` to reduce the goal to its premises.

Use `h.mul hu'` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ hu0, mul_one]`. Then use the resulting hypothesis.
-/
theorem reduction_mul_of_reduction_eq_one {u : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) (h1 : redP P u = 1) (a : E) :
    redP P (a * u) = redP P a := by
  by_cases ha : IntAt P a
  · rw [reduction_mul ha hu, h1, mul_one]
  · rw [reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral]
    intro h
    apply ha
    have := h.mul hu'
    rwa [mul_assoc, mul_inv_cancel₀ hu0, mul_one] at this

end Local

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
The claim follows from `mem_localization_standardLattice P x`.
-/
theorem mem_stdAt {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

/- English proof (translation)
The claim follows from `mem_stdAt.2 fun i => by by_cases h : i = j · subst h; simpa using intAt_one · simpa [h] using intAt_zero`.
-/
theorem single_mem_stdAt (j : Fin n) : (Pi.single j 1 : Sp E n) ∈ stdAt E n P := mem_stdAt.2 fun i => by
  by_cases h : i = j
  · subst h; simpa using intAt_one
  · simpa [h] using intAt_zero

/- English proof (translation)
Take `⟨r, s, hs, h⟩` from `ha`. Take `⟨s', hs', h'⟩` from `(mem_locP P N x).1 hx`. Use `(mem_locP P N _).2 ⟨s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩` and prove the remaining obligations. Establish `: (s * s') • a • x = r • s' • x`. Rewrite using `[← algebraMap_smul E (s * s'), ← algebraMap_smul E r, ← algebraMap_smul E s', smul_smul, smul_smul, map_mul, ← h]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `N.smul_mem r h'`.
-/
theorem smul_mem_locP {N : Submodule (𝓞 E) (Sp E n)} {a : E} (ha : IntAt P a) {x : Sp E n} (hx : x ∈ localization₂ P.asIdeal N) :
    a • x ∈ localization₂ P.asIdeal N := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨s', hs', h'⟩ := (mem_locP P N x).1 hx
  refine (mem_locP P N _).2 ⟨s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  have : (s * s') • a • x = r • s' • x := by
    rw [← algebraMap_smul E (s * s'), ← algebraMap_smul E r, ← algebraMap_smul E s', smul_smul, smul_smul, map_mul, ← h]
    congr 1
    ring
  rw [this]
  exact N.smul_mem r h'

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single x]`. Rewrite using `[map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: (Pi.single j (x j) : Sp E n) = x j • (Pi.single j 1 : Sp E n)` using `by rw [← Pi.single_smul, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, Pi.smul_apply, smul_eq_mul]`.
-/
theorem apply_eq_sum {m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (x : Sp E n) (i : Fin m) :
    f x i = ∑ j, x j * f (Pi.single j 1) i := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (x j) : Sp E n) = x j • (Pi.single j 1 : Sp E n) := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
The claim follows from `(k.2 x).2 hx`.
-/
theorem glint_mem (k : GLint E n P) {x : Sp E n} (hx : x ∈ stdAt E n P) : k.1 x ∈ stdAt E n P := (k.2 x).2 hx

/- English proof (translation)
The claim follows from `mem_stdAt.1 (glint_mem k (single_mem_stdAt j)) i`.
-/
theorem glint_entry (k : GLint E n P) (i j : Fin n) : IntAt P (k.1 (Pi.single j 1) i) :=
  mem_stdAt.1 (glint_mem k (single_mem_stdAt j)) i

def redMat (k : GLint E n P) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal) :=
  Matrix.of fun i j => redP P (k.1 (Pi.single j 1) i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show redP P ((k.1 : Sp E n →ₗ[E] Sp E n) x i) = ∑ j, redP P (k.1 (Pi.single j 1) i) * redP P (x j)`. Rewrite using `[apply_eq_sum]`. Apply the tactic sequence `refine (reduction_sum₂ _ fun j _ => (mem_stdAt.1 hx j).mul (glint_entry k i j)).trans (Finset.sum_congr rfl fun j _ => ?_)`. Rewrite using `[mul_comm (redP P _)]`.

Apply the tactic sequence `exact reduction_mul (mem_stdAt.1 hx j) (glint_entry k i j)`.
-/
theorem redV_apply (k : GLint E n P) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    redV P (k.1 x) = (redMat k).mulVec (redV P x) := by
  funext i
  show redP P ((k.1 : Sp E n →ₗ[E] Sp E n) x i) = ∑ j, redP P (k.1 (Pi.single j 1) i) * redP P (x j)
  rw [apply_eq_sum]
  refine (reduction_sum₂ _ fun j _ => (mem_stdAt.1 hx j).mul (glint_entry k i j)).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [mul_comm (redP P _)]
  exact reduction_mul (mem_stdAt.1 hx j) (glint_entry k i j)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify `reduction_one₂` using `[redV]`. Simplify `reduction_zero` using `[redV, h]`.
-/
theorem redV_single (j : Fin n) : redV P (Pi.single j 1 : Sp E n) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simpa [redV] using reduction_one₂
  · simpa [redV, h] using reduction_zero

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (h _ (single_mem_stdAt j)) i` as an intermediate fact. Rewrite `this` using `[redV_single, Matrix.mulVec_single_one]`. Conclude with `this`.
-/
theorem redMat_eq (k : GLint E n P) {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (h : ∀ x ∈ stdAt E n P, redV P (k.1 x) = A.mulVec (redV P x)) : redMat k = A := by
  ext i j
  have := congrFun (h _ (single_mem_stdAt j)) i
  rw [redV_single, Matrix.mulVec_single_one] at this
  exact this

variable (n P) in

def redGL : GLint E n P →* GL (Fin n) (𝓞 E ⧸ P.asIdeal) :=
  MonoidHom.toHomUnits
    { toFun := redMat
      map_one' := redMat_eq _ fun x _ => by rw [Matrix.one_mulVec]; rfl
      map_mul' := fun a b => redMat_eq _ fun x hx => by
        rw [← Matrix.mulVec_mulVec, ← redV_apply b hx, ← redV_apply a (glint_mem b hx)]
        rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem redGL_val (k : GLint E n P) : (redGL n P k : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) = redMat k := rfl

/- English proof (translation)
The claim follows from `redV_apply k hx`.
-/
theorem redV_redGL (k : GLint E n P) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    redV P (k.1 x) = (redGL n P k).1.mulVec (redV P x) := redV_apply k hx

/- English proof (translation)
The claim follows from `Units.ext (redMat_eq k h)`.
-/
theorem redGL_eq (k : GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (h : ∀ x ∈ stdAt E n P, redV P (k.1 x) = A.1.mulVec (redV P x)) : redGL n P k = A :=
  Units.ext (redMat_eq k h)

/- English proof (translation)
Establish `h1 : ((LinearEquiv.det k.1 : Eˣ) : E) = (LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n)).det`. Rewrite using `[LinearEquiv.coe_det, LinearMap.det_toMatrix']`. Rewrite using `[h1]`. Establish `h2 : ∀ i j, LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n) i j = k.1 (Pi.single j 1) i` using `fun i j => by`. Rewrite using `[LinearMap.toMatrix'_apply]`.

Both sides reduce to the same expression. Apply the tactic sequence `have h3 := det_int (P := P) (A := LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n)) fun i j => h2 i j ▸ glint_entry k i j`. Use `⟨h3.1, h3.2.trans ?_⟩` and prove the remaining obligations. Use `congr 1`.
-/
theorem det_glint (k : GLint E n P) :
    IntAt P ((LinearEquiv.det k.1 : Eˣ) : E) ∧ redP P ((LinearEquiv.det k.1 : Eˣ) : E) = (redMat k).det := by
  have h1 : ((LinearEquiv.det k.1 : Eˣ) : E) = (LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n)).det := by
    rw [LinearEquiv.coe_det, LinearMap.det_toMatrix']
  rw [h1]
  have h2 : ∀ i j, LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n) i j = k.1 (Pi.single j 1) i := fun i j => by
    rw [LinearMap.toMatrix'_apply]
    rfl
  have h3 := det_int (P := P) (A := LinearMap.toMatrix' (k.1 : Sp E n →ₗ[E] Sp E n)) fun i j => h2 i j ▸ glint_entry k i j
  refine ⟨h3.1, h3.2.trans ?_⟩
  congr 1

/- English proof (translation)
Use `reduction_mul_of_reduction_eq_one (Units.ne_zero _) (det_glint k).1 ?_ ?_ a` and prove the remaining obligations. Use `(det_glint k⁻¹).1` as an intermediate fact. Rewrite `this` using `[InvMemClass.coe_inv, map_inv, Units.val_inv_eq_inv_val]`. Then use the resulting hypothesis. Rewrite using `[(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one]`.
-/
theorem redP_mul_det (k : GLint E n P) (hk : redGL n P k = 1) (a : E) :
    redP P (a * ((LinearEquiv.det k.1 : Eˣ) : E)) = redP P a := by
  refine reduction_mul_of_reduction_eq_one (Units.ne_zero _) (det_glint k).1 ?_ ?_ a
  · have := (det_glint k⁻¹).1
    rwa [InvMemClass.coe_inv, map_inv, Units.val_inv_eq_inv_val] at this
  · rw [(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one]

variable (n P) in

def prinCong (c : ℕ) : Subgroup (GLint E n P) where
  carrier := {k | ∀ x ∈ stdAt E n P, ((qOf P : E) ^ c)⁻¹ • (k.1 x - x) ∈ stdAt E n P}
  one_mem' := fun x _ => by
    show ((qOf P : E) ^ c)⁻¹ • (x - x) ∈ _
    rw [sub_self, smul_zero]
    exact zero_mem _
  mul_mem' := fun {a b} ha hb x hx => by
    have e : (a * b).1 x - x = (a.1 (b.1 x) - b.1 x) + (b.1 x - x) := by
      show a.1 (b.1 x) - x = _
      abel
    rw [e, smul_add]
    exact add_mem (ha _ (glint_mem b hx)) (hb x hx)
  inv_mem' := fun {a} ha x hx => by
    have e : (a⁻¹).1 x - x = -(a.1 ((a⁻¹).1 x) - (a⁻¹).1 x) := by
      have : a.1 ((a⁻¹).1 x) = x := LinearEquiv.apply_symm_apply a.1 x
      rw [this]
      abel
    rw [e, smul_neg]
    exact neg_mem (ha _ (glint_mem a⁻¹ hx))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_prinCong {c : ℕ} {k : GLint E n P} :
    k ∈ prinCong n P c ↔ ∀ x ∈ stdAt E n P, ((qOf P : E) ^ c)⁻¹ • (k.1 x - x) ∈ stdAt E n P := Iff.rfl

instance (c : ℕ) : (prinCong n P c).Normal where
  conj_mem k hk g x hx := by
    have e : (g * k * g⁻¹).1 x - x = g.1 (k.1 ((g⁻¹).1 x) - (g⁻¹).1 x) := by
      have : g.1 ((g⁻¹).1 x) = x := LinearEquiv.apply_symm_apply g.1 x
      rw [map_sub, this]
      rfl
    rw [e, ← map_smul]
    exact glint_mem g (hk _ (glint_mem g⁻¹ hx))

/- English proof (translation)
Use `redGL_eq k fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Units.val_one, Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Establish `h1` using `mem_stdAt.1 (hk x hx) i`. Establish `h2 : redP P (k.1 x i - x i) = 0`.

Apply `redP_eq_zero_of_div` to reduce the goal to its premises. Establish `h3` using `(intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul h1`. Establish `hq` using `qOf_ne_zero (P := P)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Take `⟨c, rfl⟩ : ∃ c', c = c' + 1` from `⟨c - 1, by omega⟩`.

Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Nat.add_sub_cancel, pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[reduction_sub (mem_stdAt.1 (glint_mem k hx) i) (mem_stdAt.1 hx i), sub_eq_zero]`. Conclude with `h2`.
-/
theorem redGL_of_prinCong {c : ℕ} (hc : 0 < c) {k : GLint E n P} (hk : k ∈ prinCong n P c) : redGL n P k = 1 := by
  refine redGL_eq k fun x hx => ?_
  rw [Units.val_one, Matrix.one_mulVec]
  funext i
  have h1 := mem_stdAt.1 (hk x hx) i
  have h2 : redP P (k.1 x i - x i) = 0 := by
    apply redP_eq_zero_of_div
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul h1
    have hq := qOf_ne_zero (P := P)
    convert h3 using 1
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [reduction_sub (mem_stdAt.1 (glint_mem k hx) i) (mem_stdAt.1 hx i), sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Introduce `k hk x hx` and use `by have h1 := smul_mem_locP (intAt_pow (intAt_nat (P := P) (qOf P)) (c' - c)) (hk x hx) rw [smul_smul] at h1 have hq := qOf_ne_zero (P := P) obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h have e : ((qOf P : E) ^ (c + d - c) * ((qOf P : E) ^ (c + d))⁻¹) = ((qOf P : E) ^ c)⁻¹ := by r …`.
-/
theorem prinCong_anti {c c' : ℕ} (h : c ≤ c') : prinCong n P c' ≤ prinCong n P c := fun k hk x hx => by
  have h1 := smul_mem_locP (intAt_pow (intAt_nat (P := P) (qOf P)) (c' - c)) (hk x hx)
  rw [smul_smul] at h1
  have hq := qOf_ne_zero (P := P)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : ((qOf P : E) ^ (c + d - c) * ((qOf P : E) ^ (c + d))⁻¹) = ((qOf P : E) ^ c)⁻¹ := by
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rwa [e] at h1

end Red

section Sum

variable {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1)

def prH (E : Type) [Field E] {N n : ℕ} (hN : N = n + 1) : Sp E N →ₗ[E] Sp E n := LinearMap.funLeft E E (Br.iC hN)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prH_apply (x : Sp E N) (i : Fin n) : prH E hN x i = x (Br.iC hN i) := rfl

/- English proof (translation)
Distinguish the cases in `h : l.1 < n`. Conclude with `Or.inl ⟨⟨l.1, h⟩, rfl⟩`. Conclude with `Or.inr (Fin.ext (by have := l.2; show l.1 = n; omega))`.
-/
theorem idx_cases (l : Fin N) : (∃ i, l = Br.iC hN i) ∨ l = Br.iL hN := by
  by_cases h : l.1 < n
  · exact Or.inl ⟨⟨l.1, h⟩, rfl⟩
  · exact Or.inr (Fin.ext (by have := l.2; show l.1 = n; omega))

/- English proof (translation)
Use function extensionality and compare the values at `l`. Break down `idx_cases hN l with ⟨i, rfl⟩ | rfl` into its components or cases. Conclude with `congrFun h1 i`. Conclude with `h2`.
-/
theorem ext_prH {x y : Sp E N} (h1 : prH E hN x = prH E hN y) (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext l
  rcases idx_cases hN l with ⟨i, rfl⟩ | rfl
  · exact congrFun h1 i
  · exact h2

def sumL (g : Sp E n →ₗ[E] Sp E n) (t : E) : Sp E N →ₗ[E] Sp E N :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj (⟨l.1, h⟩ : Fin n) ∘ₗ g ∘ₗ prH E hN else t • LinearMap.proj l

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[prH_apply, sumL, LinearMap.pi_apply, dif_pos (show (Br.iC hN i).1 < n from i.2)]`. Both sides reduce to the same expression.
-/
theorem prH_sumL (g : Sp E n →ₗ[E] Sp E n) (t : E) (x : Sp E N) : prH E hN (sumL hN g t x) = g (prH E hN x) := by
  funext i
  rw [prH_apply, sumL, LinearMap.pi_apply, dif_pos (show (Br.iC hN i).1 < n from i.2)]
  rfl

/- English proof (translation)
Rewrite using `[sumL, LinearMap.pi_apply, dif_neg (show ¬ (Br.iL hN).1 < n from lt_irrefl n)]`. Both sides reduce to the same expression.
-/
theorem sumL_last (g : Sp E n →ₗ[E] Sp E n) (t : E) (x : Sp E N) : sumL hN g t x (Br.iL hN) = t * x (Br.iL hN) := by
  rw [sumL, LinearMap.pi_apply, dif_neg (show ¬ (Br.iL hN).1 < n from lt_irrefl n)]
  rfl

def sumE (g : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) : Sp E N ≃ₗ[E] Sp E N :=
  LinearEquiv.ofLinear (sumL hN (g : Sp E n →ₗ[E] Sp E n) t) (sumL hN (g.symm : Sp E n →ₗ[E] Sp E n) (t⁻¹ : Eˣ))
    (LinearMap.ext fun x => ext_prH hN (by simp [prH_sumL]) (by simp [sumL_last]))
    (LinearMap.ext fun x => ext_prH hN (by simp [prH_sumL]) (by simp [sumL_last]))

/- English proof (translation)
The claim follows from `prH_sumL hN _ _ x`.
-/
theorem prH_sumE (g : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) (x : Sp E N) : prH E hN (sumE hN g t x) = g (prH E hN x) :=
  prH_sumL hN _ _ x

/- English proof (translation)
The claim follows from `sumL_last hN _ _ x`.
-/
theorem sumE_last (g : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) (x : Sp E N) : sumE hN g t x (Br.iL hN) = t * x (Br.iL hN) :=
  sumL_last hN _ _ x

/- English proof (translation)
The claim follows from `prH_sumL hN _ _ x`.
-/
theorem prH_sumE_symm (g : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) (x : Sp E N) :
    prH E hN ((sumE hN g t).symm x) = g.symm (prH E hN x) := prH_sumL hN _ _ x

/- English proof (translation)
Rewrite using `[← Units.val_inv_eq_inv_val]`. Conclude with `sumL_last hN _ _ x`.
-/
theorem sumE_symm_last (g : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) (x : Sp E N) :
    (sumE hN g t).symm x (Br.iL hN) = (t : E)⁻¹ * x (Br.iL hN) := by
  rw [← Units.val_inv_eq_inv_val]
  exact sumL_last hN _ _ x

/- English proof (translation)
The claim follows from `LinearEquiv.ext fun x => ext_prH hN (by simp only [LinearEquiv.mul_apply, prH_sumE]) (by simp only [LinearEquiv.mul_apply, sumE_last, Units.val_mul, mul_assoc])`.
-/
theorem sumE_mul (g g' : Sp E n ≃ₗ[E] Sp E n) (t t' : Eˣ) : sumE hN (g * g') (t * t') = sumE hN g t * sumE hN g' t' :=
  LinearEquiv.ext fun x => ext_prH hN (by simp only [LinearEquiv.mul_apply, prH_sumE])
    (by simp only [LinearEquiv.mul_apply, sumE_last, Units.val_mul, mul_assoc])

/- English proof (translation)
The claim follows from `LinearEquiv.ext fun x => ext_prH hN (by rw [prH_sumE]; rfl) (by rw [sumE_last, Units.val_one, one_mul]; rfl)`.
-/
theorem sumE_one : sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) 1 = 1 :=
  LinearEquiv.ext fun x => ext_prH hN (by rw [prH_sumE]; rfl) (by rw [sumE_last, Units.val_one, one_mul]; rfl)

variable [NumberField E] [StarRing E]

/- English proof (translation)
Substitute `hN` using the available equality. Conclude with `LinearEquiv.ext fun x => ext_prH rfl ((initL_extE γ.1 x).trans (prH_sumE rfl γ.1 1 x).symm) ((extE_last γ.1 x).trans (by rw [sumE_last, Units.val_one, one_mul]; rfl))`.
-/
theorem extUH_val (γ : UF E n) : (extUH hN γ).1 = sumE hN γ.1 1 := by
  subst hN
  exact LinearEquiv.ext fun x => ext_prH rfl ((initL_extE γ.1 x).trans (prH_sumE rfl γ.1 1 x).symm)
    ((extE_last γ.1 x).trans (by rw [sumE_last, Units.val_one, one_mul]; rfl))

/- English proof (translation)
Substitute `hN` using the available equality. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[diagEmb_val]`. Use `show padM _ n (h w).1 = _`. Use extensionality with `i j`.

Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Simplify using `[padM, diagMat, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]`.
-/
theorem extGH_apply {SG : Finset (HeightOneSpectrum (𝓞 E))} (h : GLG E n SG) (w : SG) :
    extGH hN h w = diagEmb _ (by omega : n ≤ N) (h w) := by
  subst hN
  apply Units.ext
  rw [diagEmb_val]
  show padM _ n (h w).1 = _
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [padM, diagMat, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

variable {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Rewrite using `[mem_stdAt, mem_stdAt]`. Use `⟨fun h => ⟨fun i => h _, h _⟩, fun h l => ?_⟩` and prove the remaining obligations. Break down `idx_cases hN l with ⟨i, rfl⟩ | rfl` into its components or cases. Conclude with `h.1 i`. Conclude with `h.2`.
-/
theorem mem_stdAt_succ {x : Sp E N} : x ∈ stdAt E N P ↔ prH E hN x ∈ stdAt E n P ∧ IntAt P (x (Br.iL hN)) := by
  rw [mem_stdAt, mem_stdAt]
  refine ⟨fun h => ⟨fun i => h _, h _⟩, fun h l => ?_⟩
  rcases idx_cases hN l with ⟨i, rfl⟩ | rfl
  · exact h.1 i
  · exact h.2

variable (P) in

def extI : GLint E n P →* GLint E N P where
  toFun j := ⟨sumE hN j.1 1, fun x => by
    rw [mem_stdAt_succ hN, mem_stdAt_succ hN, prH_sumE, sumE_last, Units.val_one, one_mul, j.2]⟩
  map_one' := Subtype.ext (sumE_one hN)
  map_mul' a b := Subtype.ext (by
    have := sumE_mul hN a.1 b.1 1 1
    rwa [one_mul] at this)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extI_val (j : GLint E n P) : (extI hN P j).1 = sumE hN j.1 1 := rfl

/- English proof (translation)
Substitute `hN` using the available equality. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show ∑ l, diagMat n (n + 1) A i.castSucc l * v l = ∑ j, A i j * v j.castSucc`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[diagMat, Matrix.one_apply, Fin.castSucc_ne_last]`.

Use `show ∑ l, diagMat n (n + 1) A (Fin.last n) l * v l = v (Fin.last n)`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[diagMat, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]`.
-/
theorem diagMat_mulVec {κ : Type} [CommRing κ] (A : Matrix (Fin n) (Fin n) κ) (v : Fin N → κ) :
    (∀ i, (diagMat n N A).mulVec v (Br.iC hN i) = A.mulVec (fun j => v (Br.iC hN j)) i) ∧
      (diagMat n N A).mulVec v (Br.iL hN) = v (Br.iL hN) := by
  subst hN
  refine ⟨fun i => ?_, ?_⟩
  · show ∑ l, diagMat n (n + 1) A i.castSucc l * v l = ∑ j, A i j * v j.castSucc
    rw [Fin.sum_univ_castSucc]
    simp [diagMat, Matrix.one_apply, Fin.castSucc_ne_last]
  · show ∑ l, diagMat n (n + 1) A (Fin.last n) l * v l = v (Fin.last n)
    rw [Fin.sum_univ_castSucc]
    simp [diagMat, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

/- English proof (translation)
Use `redGL_eq _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[diagEmb_val]`. Use function extensionality and compare the values at `l`. Break down `idx_cases hN l with ⟨i, rfl⟩ | rfl` into its components or cases. Rewrite using `[(diagMat_mulVec hN _ _).1]`.

Establish `h1` using `congrFun (redV_redGL j ((mem_stdAt_succ hN).1 hx).1) i`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Conclude with `congrArg (redP P) (congrFun (prH_sumE hN j.1 1 x) i)`. Rewrite using `[(diagMat_mulVec hN _ _).2] show redP P (sumE hN j.1 1 x (Br.iL hN)) = _`. Rewrite using `[sumE_last, Units.val_one, one_mul]`.

Both sides reduce to the same expression.
-/
theorem redGL_extI (j : GLint E n P) : redGL N P (extI hN P j) = diagEmb _ (by omega : n ≤ N) (redGL n P j) := by
  refine redGL_eq _ fun x hx => ?_
  rw [diagEmb_val]
  funext l
  rcases idx_cases hN l with ⟨i, rfl⟩ | rfl
  · rw [(diagMat_mulVec hN _ _).1]
    have h1 := congrFun (redV_redGL j ((mem_stdAt_succ hN).1 hx).1) i
    refine Eq.trans ?_ h1
    exact congrArg (redP P) (congrFun (prH_sumE hN j.1 1 x) i)
  · rw [(diagMat_mulVec hN _ _).2]
    show redP P (sumE hN j.1 1 x (Br.iL hN)) = _
    rw [sumE_last, Units.val_one, one_mul]
    rfl

end Sum

section Lift

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def IsLiftFr (d : Deco E n ST SG) (w : SG) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  (∀ x, f x ∈ d.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.be w (f x) = redV w.1 x

/- English proof (translation)
Take `⟨r, s, hs, h⟩` from `id ha`. Establish `h1` using `hd.be_smul w s _ (smul_mem_locP ha hx)`. Establish `h2` using `hd.be_smul w r _ hx`. Establish `e : s • a • x = r • x`. Rewrite using `[← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, h]`.

Rewrite `h1` using `[e, h2, ← reduction_spec w.1 hs h, mul_smul]`. Use function extensionality and compare the values at `i`. Conclude with `(mul_left_cancel₀ (mk_ne_zero hs) (congrFun h1 i)).symm`.
-/
theorem be_smul_int {d : Deco E n ST SG} (hd : d.Ok) (w : SG) {a : E} (ha : IntAt w.1 a) {x : Sp E n} (hx : x ∈ d.at w.1) :
    d.be w (a • x) = redP w.1 a • d.be w x := by
  obtain ⟨r, s, hs, h⟩ := id ha
  have h1 := hd.be_smul w s _ (smul_mem_locP ha hx)
  have h2 := hd.be_smul w r _ hx
  have e : s • a • x = r • x := by
    rw [← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, h]
  rw [e, h2, ← reduction_spec w.1 hs h, mul_smul] at h1
  funext i
  exact (mul_left_cancel₀ (mk_ne_zero hs) (congrFun h1 i)).symm

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `hd.be_add w 0 (zero_mem _) 0 (zero_mem _)` as an intermediate fact. Rewrite `this` using `[add_zero, left_eq_add]`. Simplify using `using this`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hd.be_add w _ (h a (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]`.
-/
theorem be_sum {d : Deco E n ST SG} (hd : d.Ok) (w : SG) {ι : Type} (s : Finset ι) {f : ι → Sp E n}
    (h : ∀ i ∈ s, f i ∈ d.at w.1) : d.be w (∑ i ∈ s, f i) = ∑ i ∈ s, d.be w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hd.be_add w 0 (zero_mem _) 0 (zero_mem _)
    rw [add_zero, left_eq_add] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hd.be_add w _ (h a (Finset.mem_insert_self _ _)) _
      (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/- English proof (translation)
Use `choose v hv hbe using fun i : Fin n => hd.be_surj w (Pi.single i 1)`. Set `f : Sp E n →ₗ[E] Sp E n` to `Fintype.linearCombination E v`. Establish `hf : ∀ x, f x = ∑ i, x i • v i` using `fun x => Fintype.linearCombination_apply E v x`. Establish `hmem : ∀ x ∈ stdAt E n w.1, ∀ i, x i • v i ∈ d.at w.1` using `fun x hx i => smul_mem_locP (mem_stdAt.1 hx i) (le_locP _ _ (hv i))`. Establish `h1 : ∀ x ∈ stdAt E n w.1, f x ∈ d.at w.1` using `fun x hx => by`.

Rewrite using `[hf]`. Conclude with `Submodule.sum_mem _ fun i _ => hmem x hx i`. Establish `h2 : ∀ x ∈ stdAt E n w.1, d.be w (f x) = redV w.1 x` using `fun x hx => by`. Rewrite using `[hf, be_sum hd w _ fun i _ => hmem x hx i]`. Use `conv_rhs => rw [← Finset.univ_sum_single (redV w.1 x)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[be_smul_int hd w (mem_stdAt.1 hx i) (le_locP _ _ (hv i)), hbe, ← Pi.single_smul, smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Set `M : Submodule (𝓞 E) (Sp E n)` to `(stdLat E n).map (f.restrictScalars (𝓞 E))`. Establish `hMN : M ≤ d.N`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `hx'` from `(mem_stdLat x).1 hx`. Use `choose r hr using hx'`. Use `show f x ∈ _`. Rewrite using `[hf]`.

Conclude with `Submodule.sum_mem _ fun i _ => by rw [← hr, algebraMap_smul]; exact d.N.smul_mem _ (hv i)`. Establish `hle : d.N ≤ M ⊔ w.1.asIdeal • d.N` using `fun y hy => by choose r hr using fun i => Ideal.Quotient.mk_surjective (d.be w y i)`. Establish `hx : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n` using `(mem_stdLat _).2 fun i => ⟨r i, rfl⟩`. Establish `hm : f (fun i => algebraMap (𝓞 E) E (r i)) ∈ M` using `Submodule.mem_map_of_mem (f := f.restrictScalars (𝓞 E)) hx`. Use `Submodule.mem_sup.2 ⟨_, hm, y - f _, hd.be_ker w _ (sub_mem hy (hMN hm)) ?_, by abel⟩` and prove the remaining obligations.

Establish `e` using `hd.be_add w _ (le_locP _ _ (sub_mem hy (hMN hm))) _ (le_locP _ _ (hMN hm))`. Rewrite `e` using `[sub_add_cancel, h2 _ (le_locP _ _ hx)]`. Establish `e2 : redV w.1 (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) = d.be w y` using `funext fun i => (reduction_coe _ _).trans (hr i)`. Rewrite `e` using `[e2, right_eq_add]`. Conclude with `e`.

Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hd.lat.fg le_rfl hle`. Establish `hr0 : r ∉ w.1.asIdeal` using `fun h => one_notMem w.1 (by simpa using Ideal.sub_mem _ h hr1)`. Establish `h3 : ∀ y ∈ d.at w.1, ∃ x ∈ stdAt E n w.1, f x = y` using `fun y hy => by`. Take `⟨s, hs, h⟩` from `(mem_locP _ _ _).1 hy`. Take `⟨x, hx, e⟩` from `hr (Submodule.smul_mem_pointwise_smul _ r _ h)`.

Establish `hrs : r * s ∉ w.1.asIdeal` using `fun hm => (w.1.isPrime.mem_or_mem hm).elim hr0 hs`. Establish `h0 : algebraMap (𝓞 E) E (r * s) ≠ 0`. Rewrite using `[Ne, FaithfulSMul.algebraMap_eq_zero_iff]`. Introduce `h0`. Conclude with `hrs (h0 ▸ Ideal.zero_mem _)`.

Use `⟨(algebraMap (𝓞 E) E (r * s))⁻¹ • x, smul_mem_locP ?_ (le_locP _ _ hx), ?_⟩` and prove the remaining obligations. Use `(intAt_one (P := w.1)).div_of_notMem hrs` as an intermediate fact. Rewrite `this` using `[one_div]`. Then use the resulting hypothesis. Use `replace e : f x = r • s • y := e`. Rewrite using `[map_smul, e, smul_smul r s, ← algebraMap_smul E (r * s), smul_smul, inv_mul_cancel₀ h0, one_smul]`.

Establish `hsurj : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hd.lat.span_eq_top, Submodule.span_le]`. Introduce `y hy`. Take `⟨x, -, e⟩` from `h3 y (le_locP _ _ hy)`. Conclude with `⟨x, e⟩`.

Establish `hinj : Function.Injective f` using `LinearMap.injective_iff_surjective.2 hsurj`. Use `⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x => ⟨fun h => ?_, h1 x⟩, h2⟩` and prove the remaining obligations. Take `⟨x', hx', e⟩` from `h3 _ h`. Rewrite using `[← hinj e]` and apply the resulting hypothesis.
-/
theorem exists_liftFr {d : Deco E n ST SG} (hd : d.Ok) (w : SG) : ∃ f, IsLiftFr d w f := by
  classical
  choose v hv hbe using fun i : Fin n => hd.be_surj w (Pi.single i 1)
  let f : Sp E n →ₗ[E] Sp E n := Fintype.linearCombination E v
  have hf : ∀ x, f x = ∑ i, x i • v i := fun x => Fintype.linearCombination_apply E v x
  have hmem : ∀ x ∈ stdAt E n w.1, ∀ i, x i • v i ∈ d.at w.1 := fun x hx i =>
    smul_mem_locP (mem_stdAt.1 hx i) (le_locP _ _ (hv i))
  have h1 : ∀ x ∈ stdAt E n w.1, f x ∈ d.at w.1 := fun x hx => by
    rw [hf]; exact Submodule.sum_mem _ fun i _ => hmem x hx i
  have h2 : ∀ x ∈ stdAt E n w.1, d.be w (f x) = redV w.1 x := fun x hx => by
    rw [hf, be_sum hd w _ fun i _ => hmem x hx i]
    conv_rhs => rw [← Finset.univ_sum_single (redV w.1 x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [be_smul_int hd w (mem_stdAt.1 hx i) (le_locP _ _ (hv i)), hbe, ← Pi.single_smul, smul_eq_mul, mul_one]
    rfl
  let M : Submodule (𝓞 E) (Sp E n) := (stdLat E n).map (f.restrictScalars (𝓞 E))
  have hMN : M ≤ d.N := by
    rintro _ ⟨x, hx, rfl⟩
    obtain hx' := (mem_stdLat x).1 hx
    choose r hr using hx'
    show f x ∈ _
    rw [hf]
    exact Submodule.sum_mem _ fun i _ => by rw [← hr, algebraMap_smul]; exact d.N.smul_mem _ (hv i)
  have hle : d.N ≤ M ⊔ w.1.asIdeal • d.N := fun y hy => by
    choose r hr using fun i => Ideal.Quotient.mk_surjective (d.be w y i)
    have hx : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n := (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
    have hm : f (fun i => algebraMap (𝓞 E) E (r i)) ∈ M := Submodule.mem_map_of_mem (f := f.restrictScalars (𝓞 E)) hx
    refine Submodule.mem_sup.2 ⟨_, hm, y - f _, hd.be_ker w _ (sub_mem hy (hMN hm)) ?_, by abel⟩
    have e := hd.be_add w _ (le_locP _ _ (sub_mem hy (hMN hm))) _ (le_locP _ _ (hMN hm))
    rw [sub_add_cancel, h2 _ (le_locP _ _ hx)] at e
    have e2 : redV w.1 (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) = d.be w y := funext fun i => (reduction_coe _ _).trans (hr i)
    rw [e2, right_eq_add] at e
    exact e
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hd.lat.fg le_rfl hle
  have hr0 : r ∉ w.1.asIdeal := fun h => one_notMem w.1 (by simpa using Ideal.sub_mem _ h hr1)
  have h3 : ∀ y ∈ d.at w.1, ∃ x ∈ stdAt E n w.1, f x = y := fun y hy => by
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hy
    obtain ⟨x, hx, e⟩ := hr (Submodule.smul_mem_pointwise_smul _ r _ h)
    have hrs : r * s ∉ w.1.asIdeal := fun hm => (w.1.isPrime.mem_or_mem hm).elim hr0 hs
    have h0 : algebraMap (𝓞 E) E (r * s) ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      intro h0
      exact hrs (h0 ▸ Ideal.zero_mem _)
    refine ⟨(algebraMap (𝓞 E) E (r * s))⁻¹ • x, smul_mem_locP ?_ (le_locP _ _ hx), ?_⟩
    · have := (intAt_one (P := w.1)).div_of_notMem hrs
      rwa [one_div] at this
    · replace e : f x = r • s • y := e
      rw [map_smul, e, smul_smul r s, ← algebraMap_smul E (r * s), smul_smul, inv_mul_cancel₀ h0, one_smul]
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hd.lat.span_eq_top, Submodule.span_le]
    intro y hy
    obtain ⟨x, -, e⟩ := h3 y (le_locP _ _ hy)
    exact ⟨x, e⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.2 hsurj
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x => ⟨fun h => ?_, h1 x⟩, h2⟩
  obtain ⟨x', hx', e⟩ := h3 _ h
  rwa [← hinj e]

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (exists_liftFr hd w)`.
-/
theorem liftFr_spec {d : Deco E n ST SG} (hd : d.Ok) (w : SG) : IsLiftFr d w (d.liftFr w) :=
  Classical.epsilon_spec (exists_liftFr hd w)

def passFr {d : Deco E n ST SG} {w : SG} (γ : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsLiftFr d w f) (hf' : IsLiftFr (d.act γ h) w f') : GLint E n w.1 :=
  ⟨f'⁻¹ * γ * f, fun x => by
    rw [← hf'.1, ← hf.1]
    show f' (f'.symm (γ (f x))) ∈ localization₂ w.1.asIdeal (gmap γ d.N) ↔ _
    rw [LinearEquiv.apply_symm_apply, mem_localization_gmap, LinearEquiv.symm_apply_apply]⟩

/- English proof (translation)
Use `redGL_eq _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hf'.2 _ (glint_mem _ hx), ← hf.2 x hx]`. Use `show (h w).1.mulVec (d.be w (γ.symm (f' (f'.symm (γ (f x)))))) = _`. Rewrite using `[LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]`.
-/
theorem redGL_passFr {d : Deco E n ST SG} {w : SG} (γ : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsLiftFr d w f) (hf' : IsLiftFr (d.act γ h) w f') : redGL n w.1 (passFr γ h hf hf') = h w := by
  refine redGL_eq _ fun x hx => ?_
  rw [← hf'.2 _ (glint_mem _ hx), ← hf.2 x hx]
  show (h w).1.mulVec (d.be w (γ.symm (f' (f'.symm (γ (f x)))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Establish `hf'' : IsLiftFr (d.act 1 1) w f'` using `by rwa [Deco.act_one]`. Use `⟨passFr 1 1 hf hf'', redGL_passFr 1 1 hf hf'', ?_⟩` and prove the remaining obligations. Use `show f = f' * (f'⁻¹ * 1 * f)`. Use `group`.
-/
theorem exists_of_isLiftFr {d : Deco E n ST SG} {w : SG} {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsLiftFr d w f) (hf' : IsLiftFr d w f') : ∃ κ : GLint E n w.1, redGL n w.1 κ = 1 ∧ f = f' * κ.1 := by
  have hf'' : IsLiftFr (d.act 1 1) w f' := by rwa [Deco.act_one]
  refine ⟨passFr 1 1 hf hf'', redGL_passFr 1 1 hf hf'', ?_⟩
  show f = f' * (f'⁻¹ * 1 * f)
  group

variable {N : ℕ} (hN : N = n + 1)

/- English proof (translation)
Substitute `hN` using the available equality. Establish `e : (DecoSet.tilH (ST` using `ST) rfl pi d).1 = d.1.til pi := DecoSet.til_val d hT hG`. Rewrite using `[e]`. Establish `i1 : ∀ x, initL E n (sumE rfl f t x) = f (prH E rfl x)` using `prH_sumE rfl f t`. Establish `i2 : ∀ x, sumE rfl f t x (Fin.last n) = t * x (Fin.last n)` using `sumE_last rfl f t`.

Establish `h1 : ∀ x, sumE rfl f t x ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ x ∈ stdAt E (n + 1) w.1` using `fun x => by`. Rewrite using `[mem_localization_tilN, mem_stdAt_succ rfl, i1, i2]`. Use `and_congr (hf.1 _) ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `h.div_of_notMem (hG w)` as an intermediate fact. Rewrite `this` using `[show algebraMap (𝓞 E) E pi = t from ht.symm, mul_div_cancel_left₀ _ t.ne_zero]`. Then use the resulting hypothesis.

Rewrite using `[ht]`. Conclude with `(IntAt.coe _ pi).mul h`. Use `⟨h1, fun x hx => ?_⟩` and prove the remaining obligations. Use `show (if sumE rfl f t x ∈ localization₂ w.1.asIdeal (tilN d.1.N) then _ else _) = _`. Rewrite using `[if_pos ((h1 x).2 hx), i1, i2, hf.2 _ ((mem_stdAt_succ rfl).1 hx).1, show algebraMap (𝓞 E) E pi = t from ht.symm, mul_div_cancel_left₀ _ t.ne_zero]`.

Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.snoc_last]`. Both sides reduce to the same expression. Rewrite using `[Fin.snoc_castSucc]`.

Both sides reduce to the same expression.
-/
theorem isLiftFr_tilH (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) {f : Sp E n ≃ₗ[E] Sp E n} (hf : IsLiftFr d.1 w f) (t : Eˣ) (ht : (t : E) = (pi : E)) :
    IsLiftFr (DecoSet.tilH (ST := ST) hN pi d).1 w (sumE hN f t) := by
  classical
  subst hN
  have e : (DecoSet.tilH (ST := ST) rfl pi d).1 = d.1.til pi := DecoSet.til_val d hT hG
  rw [e]
  have i1 : ∀ x, initL E n (sumE rfl f t x) = f (prH E rfl x) := prH_sumE rfl f t
  have i2 : ∀ x, sumE rfl f t x (Fin.last n) = t * x (Fin.last n) := sumE_last rfl f t
  have h1 : ∀ x, sumE rfl f t x ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ x ∈ stdAt E (n + 1) w.1 := fun x => by
    rw [mem_localization_tilN, mem_stdAt_succ rfl, i1, i2]
    refine and_congr (hf.1 _) ⟨fun h => ?_, fun h => ?_⟩
    · have := h.div_of_notMem (hG w)
      rwa [show algebraMap (𝓞 E) E pi = t from ht.symm, mul_div_cancel_left₀ _ t.ne_zero] at this
    · rw [ht]
      exact (IntAt.coe _ pi).mul h
  refine ⟨h1, fun x hx => ?_⟩
  show (if sumE rfl f t x ∈ localization₂ w.1.asIdeal (tilN d.1.N) then _ else _) = _
  rw [if_pos ((h1 x).2 hx), i1, i2, hf.2 _ ((mem_stdAt_succ rfl).1 hx).1, show algebraMap (𝓞 E) E pi = t from ht.symm,
    mul_div_cancel_left₀ _ t.ne_zero]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_castSucc]; rfl

end Lift

end GlobalTheory.TopStep
