import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Iwasawa

variable {F : Type} [Field F] [NumberField F]

def IntAt (b : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  algebraMap F (A F) b v ∈ v.adicCompletionIntegers F

open Classical in

def idem (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : IntAt b v
    · simpa [h] using (v.adicCompletionIntegers F).one_mem
    · simpa [h] using (v.adicCompletionIntegers F).zero_mem⟩

open Classical in

def scale (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else (algebraMap F (A F) b v)⁻¹,
    Filter.Eventually.of_forall fun v => by
      by_cases h : IntAt b v
      · simpa [h] using (v.adicCompletionIntegers F).one_mem
      · simpa [h] using ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h⟩

open Classical in

def scaleInv (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else algebraMap F (A F) b v, by
    filter_upwards [(algebraMap F (A F) b).2] with v hv
    have h : IntAt b v := hv
    simpa [h] using (v.adicCompletionIntegers F).one_mem⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x * y) v = x v * y v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem add_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x + y) v = x v + y v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sub_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x - y) v = x v - y v := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem one_at (v : HeightOneSpectrum (𝓞 F)) : (1 : A F) v = 1 := rfl

/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem idem_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : idem b v = 1 :=
  if_pos h
/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem idem_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) : idem b v = 0 :=
  if_neg h
/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem scale_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scale b v = 1 :=
  if_pos h
/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem scale_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scale b v = (algebraMap F (A F) b v)⁻¹ :=
  if_neg h
/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem scaleInv_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scaleInv b v = 1 :=
  if_pos h
/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem scaleInv_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scaleInv b v = algebraMap F (A F) b v :=
  if_neg h

/- English proof (translation)
Introduce `h0` and use `h (by unfold IntAt; rw [h0]; exact (v.adicCompletionIntegers F).zero_mem)`.
-/
theorem ne_zero_of_not_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    algebraMap F (A F) b v ≠ 0 := fun h0 =>
  h (by unfold IntAt; rw [h0]; exact (v.adicCompletionIntegers F).zero_mem)

/- English proof (translation)
Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Rewrite using `[mul_at, one_at]`. Distinguish the cases in `h : IntAt b v`. Rewrite using `[scale_int h, scaleInv_int h, one_mul]`. Rewrite using `[scale_not h, scaleInv_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]`.
-/
theorem scale_mul_scaleInv (b : F) : scale b * scaleInv b = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [mul_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, scaleInv_int h, one_mul]
  · rw [scale_not h, scaleInv_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]

/- English proof (translation)
Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Rewrite using `[add_at, mul_at, mul_at, mul_at, sub_at, one_at]`. Distinguish the cases in `h : IntAt b v`. Rewrite using `[scale_int h, idem_int h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[scale_not h, idem_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scale_combo (b : F) :
    scale b * idem b + (1 - idem b) * (scale b * algebraMap F (A F) b) = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [add_at, mul_at, mul_at, mul_at, sub_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, idem_int h]; ring
  · rw [scale_not h, idem_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]; ring

/- English proof (translation)
Introduce `v` and use `by by_cases h : IntAt b v · rw [idem_int h]; exact (v.adicCompletionIntegers F).one_mem · rw [idem_not h]; exact (v.adicCompletionIntegers F).zero_mem`.
-/
theorem idem_mem (b : F) : idem b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [idem_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [idem_not h]; exact (v.adicCompletionIntegers F).zero_mem

/- English proof (translation)
Introduce `v` and use `by by_cases h : IntAt b v · rw [scale_int h]; exact (v.adicCompletionIntegers F).one_mem · rw [scale_not h] exact ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h`.
-/
theorem scale_mem (b : F) : scale b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [scale_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [scale_not h]
    exact ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h

/- English proof (translation)
Introduce `v` and use `(v.adicCompletionIntegers F).one_mem`.
-/
theorem Oh_one : (1 : A F) ∈ Oh F := fun v => (v.adicCompletionIntegers F).one_mem

/- English proof (translation)
Introduce `v` and use `(v.adicCompletionIntegers F).neg_mem _ (hx v)`.
-/
theorem Oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).neg_mem _ (hx v)

/- English proof (translation)
Introduce `v` and use `(v.adicCompletionIntegers F).sub_mem (hx v) (hy v)`.
-/
theorem Oh_sub {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).sub_mem (hx v) (hy v)

/- English proof (translation)
Introduce `v` and use `(v.adicCompletionIntegers F).mul_mem _ _ (hx v) (hy v)`.
-/
theorem Oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).mul_mem _ _ (hx v) (hy v)

/- English proof (translation)
Introduce `v` and use `by rw [mul_at] by_cases h : IntAt b v · rw [scale_int h, one_mul]; exact h · rw [scale_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)] exact (v.adicCompletionIntegers F).one_mem`.
-/
theorem scale_mul_mem (b : F) : scale b * algebraMap F (A F) b ∈ Oh F := fun v => by
  rw [mul_at]
  by_cases h : IntAt b v
  · rw [scale_int h, one_mul]; exact h
  · rw [scale_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]
    exact (v.adicCompletionIntegers F).one_mem

def scaleUnit (b : F) : (A F)ˣ :=
  ⟨scale b, scaleInv b, scale_mul_scaleInv b, by rw [mul_comm]; exact scale_mul_scaleInv b⟩

def kMat (b : F) : SL(2, A F) :=
  ⟨!![idem b - 1, idem b; -scale b, -(scale b * algebraMap F (A F) b)], by
    rw [Matrix.det_fin_two_of]
    linear_combination scale_combo b⟩

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, rfl⟩`. Use `⟨Oh_mul (scale_mem b) ho, ?_⟩` and prove the remaining obligations. Establish `: algebraMap F (A F) b * (scale b * o) = (scale b * algebraMap F (A F) b) * o` using `by ring`.

Use `show algebraMap F (A F) b * (scale b * o) ∈ Oh F`. Rewrite using `[this]`. Conclude with `Oh_mul (scale_mul_mem b) ho`. Introduce and unpack `⟨hx, hbx⟩`. Use `⟨scaleInv b * x, fun v => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_at]`. Distinguish the cases in `h : IntAt b v`. Rewrite using `[scaleInv_int h, one_mul]`. Conclude with `hx v`. Rewrite using `[scaleInv_not h]`.

Conclude with `hbx v`. Use `show scale b * (scaleInv b * x) = x`. Rewrite using `[← mul_assoc, scale_mul_scaleInv, one_mul]`.
-/
theorem image_scale (b : F) :
    (fun x => scale b * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨Oh_mul (scale_mem b) ho, ?_⟩
    have : algebraMap F (A F) b * (scale b * o) = (scale b * algebraMap F (A F) b) * o := by ring
    show algebraMap F (A F) b * (scale b * o) ∈ Oh F
    rw [this]
    exact Oh_mul (scale_mul_mem b) ho
  · rintro ⟨hx, hbx⟩
    refine ⟨scaleInv b * x, fun v => ?_, ?_⟩
    · rw [mul_at]
      by_cases h : IntAt b v
      · rw [scaleInv_int h, one_mul]; exact hx v
      · rw [scaleInv_not h]; exact hbx v
    · show scale b * (scaleInv b * x) = x
      rw [← mul_assoc, scale_mul_scaleInv, one_mul]

/- English proof (translation)
Establish `hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1` using `u.mul_inv`. Establish `hk : (k : Matrix (Fin 2) (Fin 2) R) = !![e - 1, e; -(u : R), -((u : R) * β)]`. Rewrite using `[Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) R), h00, h01, h10, h11]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(!![0, 1; -1, 0] * !![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) R) = !![1, (e - 1) * (u : R); 0, 1] * !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] * (k : Matrix (Fin 2) (Fin 2) R)`.

Rewrite using `[hk]`. Simplify using `only [Matrix.mul_fin_two]`. Establish `entries : ∀ a b c d a' b' c' d' : R, a = a' → b = b' → c = c' → d = d' → (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d']`. Introduce and unpack `_ _ _ _ _ _ _ _ rfl rfl rfl rfl`. Both sides reduce to the same expression.

Use `entries _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Take the linear combination `((e - 1) * (u : R)) * hu`. Take the linear combination `-h + ((e - 1) * (u : R) * β) * hu`. Take the linear combination `hu`. Take the linear combination `β * hu`.
-/
theorem w_n_eq {R : Type} [CommRing R] (β e : R) (u : Rˣ) (k : SL(2, R))
    (h00 : k 0 0 = e - 1) (h01 : k 0 1 = e) (h10 : k 1 0 = -(u : R))
    (h11 : k 1 1 = -((u : R) * β)) (h : (u : R) * e + (1 - e) * ((u : R) * β) = 1) :
    wMat * nMat β = nMat ((e - 1) * (u : R)) * mMat u * k := by
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hk : (k : Matrix (Fin 2) (Fin 2) R) = !![e - 1, e; -(u : R), -((u : R) * β)] := by
    rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) R), h00, h01, h10, h11]
  apply Subtype.ext
  change (!![0, 1; -1, 0] * !![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) R) =
    !![1, (e - 1) * (u : R); 0, 1] * !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] *
      (k : Matrix (Fin 2) (Fin 2) R)
  rw [hk]
  simp only [Matrix.mul_fin_two]
  have entries : ∀ a b c d a' b' c' d' : R, a = a' → b = b' → c = c' → d = d' →
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d'] := by
    rintro _ _ _ _ _ _ _ _ rfl rfl rfl rfl
    rfl
  refine entries _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination ((e - 1) * (u : R)) * hu
  · linear_combination -h + ((e - 1) * (u : R) * β) * hu
  · linear_combination hu
  · linear_combination β * hu

/- English proof (translation)
Introduce `F _ _ b`. Use `⟨(idem b - 1) * scale b, scaleUnit b, kMat b, ?_, ?_, image_scale b⟩` and prove the remaining obligations. Apply the tactic sequence `intro i j fin_cases i <;> fin_cases j`. Conclude with `Oh_sub (idem_mem b) Oh_one`. Conclude with `idem_mem b`.

Conclude with `Oh_neg (scale_mem b)`. Conclude with `Oh_neg (scale_mul_mem b)`. Conclude with `w_n_eq _ (idem b) (scaleUnit b) (kMat b) rfl rfl rfl rfl (scale_combo b)`.
-/
theorem iwasawa_w_n : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F,
    ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧
      wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧
      (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  intro F _ _ b
  refine ⟨(idem b - 1) * scale b, scaleUnit b, kMat b, ?_, ?_, image_scale b⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact Oh_sub (idem_mem b) Oh_one
    · exact idem_mem b
    · exact Oh_neg (scale_mem b)
    · exact Oh_neg (scale_mul_mem b)
  · exact w_n_eq _ (idem b) (scaleUnit b) (kMat b) rfl rfl rfl rfl (scale_combo b)

end GlobalTheory.CompanionTheory.SW.Iwasawa
