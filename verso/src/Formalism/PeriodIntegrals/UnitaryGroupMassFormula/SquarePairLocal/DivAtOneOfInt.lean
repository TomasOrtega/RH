import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Loc

variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]

/- English proof (translation)
Introduce `h` and use `hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)`.
-/
theorem one_nmem : (1 : 𝓞 E) ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

/- English proof (translation)
Introduce `h` and use `(hQ.mem_or_mem h).elim hs ht`.
-/
theorem mul_nmem {s t : 𝓞 E} (hs : s ∉ Q) (ht : t ∉ Q) : s * t ∉ Q :=
  fun h => (hQ.mem_or_mem h).elim hs ht

/- English proof (translation)
Unfold `IntAt`. Conclude with `⟨1, one_nmem, w, by simp⟩`.
-/
theorem intAt_coe (w : 𝓞 E) : IntAt Q (w : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, w, by simp⟩

/- English proof (translation)
Unfold `IntAt`. Conclude with `⟨1, one_nmem, 0, by simp⟩`.
-/
theorem intAt_zero : IntAt Q (0 : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, 0, by simp⟩

/- English proof (translation)
Unfold `IntAt`. Conclude with `⟨1, one_nmem, 1, by simp⟩`.
-/
theorem intAt_one : IntAt Q (1 : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, 1, by simp⟩

/- English proof (translation)
Unfold `IntAt at *`. Take `⟨s, hs, w, hw⟩` from `hx`. Take `⟨t, ht, v, hv⟩` from `hy`. Use `⟨s * t, mul_nmem hs ht, w * v, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `((t : E) * y) * hw + (w : E) * hv`.
-/
theorem intAt_mul {x y : E} (hx : IntAt Q x) (hy : IntAt Q y) : IntAt Q (x * y) := by
  unfold IntAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  obtain ⟨t, ht, v, hv⟩ := hy
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination ((t : E) * y) * hw + (w : E) * hv

/- English proof (translation)
Unfold `DivAt`. Conclude with `⟨1, one_nmem, 0, by simp⟩`.
-/
theorem divAt_zero {c : 𝓞 E} : DivAt Q c 0 := by
  unfold DivAt
  exact ⟨1, one_nmem, 0, by simp⟩

/- English proof (translation)
Unfold `DivAt at *`. Take `⟨s, hs, w, hw⟩` from `hx`. Take `⟨t, ht, v, hv⟩` from `hy`. Use `⟨s * t, mul_nmem hs ht, t * w + s * v, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `(t : E) * hw + (s : E) * hv`.
-/
theorem divAt_add {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x + y) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  obtain ⟨t, ht, v, hv⟩ := hy
  refine ⟨s * t, mul_nmem hs ht, t * w + s * v, ?_⟩
  push_cast
  linear_combination (t : E) * hw + (s : E) * hv

/- English proof (translation)
Unfold `DivAt at *`. Take `⟨s, hs, w, hw⟩` from `hx`. Use `⟨s, hs, -w, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `-hw`.
-/
theorem divAt_neg {c : 𝓞 E} {x : E} (hx : DivAt Q c x) : DivAt Q c (-x) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, -w, ?_⟩
  push_cast
  linear_combination -hw

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `divAt_add hx (divAt_neg hy)`.
-/
theorem divAt_sub {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x - y) := by
  rw [sub_eq_add_neg]
  exact divAt_add hx (divAt_neg hy)

/- English proof (translation)
Unfold `IntAt at ha`. Unfold `DivAt at *`. Take `⟨s, hs, w, hw⟩` from `ha`. Take `⟨t, ht, v, hv⟩` from `hx`. Use `⟨s * t, mul_nmem hs ht, w * v, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `((t : E) * x) * hw + (w : E) * hv`.
-/
theorem divAt_mul_left {c : 𝓞 E} {a x : E} (ha : IntAt Q a) (hx : DivAt Q c x) : DivAt Q c (a * x) := by
  unfold IntAt at ha
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := ha
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination ((t : E) * x) * hw + (w : E) * hv

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `divAt_mul_left ha hx`.
-/
theorem divAt_mul_right {c : 𝓞 E} {a x : E} (hx : DivAt Q c x) (ha : IntAt Q a) : DivAt Q c (x * a) := by
  rw [mul_comm]
  exact divAt_mul_left ha hx

/- English proof (translation)
The claim follows from `Finset.sum_induction f (DivAt Q c) (fun _ _ ha hb => divAt_add ha hb) divAt_zero h`.
-/
theorem divAt_sum {c : 𝓞 E} {ι : Type} (S : Finset ι) (f : ι → E) (h : ∀ i ∈ S, DivAt Q c (f i)) :
    DivAt Q c (∑ i ∈ S, f i) :=
  Finset.sum_induction f (DivAt Q c) (fun _ _ ha hb => divAt_add ha hb) divAt_zero h

/- English proof (translation)
Unfold `IntAt at hx`. Unfold `DivAt`. Take `⟨s, hs, w, hw⟩` from `hx`. Conclude with `⟨s, hs, w, by simp [hw]⟩`.
-/
theorem divAt_one_of_int {x : E} (hx : IntAt Q x) : DivAt Q 1 x := by
  unfold IntAt at hx
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simp [hw]⟩

/- English proof (translation)
Unfold `DivAt at hx`. Unfold `IntAt`. Take `⟨s, hs, w, hw⟩` from `hx`. Use `⟨s, hs, w, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem intAt_inv_mul {c : 𝓞 E} (hc : (c : E) ≠ 0) {x : E} (hx : DivAt Q c x) :
    IntAt Q ((c : E)⁻¹ * x) := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, w, ?_⟩
  calc (s : E) * ((c : E)⁻¹ * x) = (c : E)⁻¹ * ((s : E) * x) := by ring
    _ = (w : E) := by rw [hw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/- English proof (translation)
Unfold `DivAt`. Take `⟨s, hs, w, hw⟩` from `hK x hx`. Conclude with `⟨s, hs, w, by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw⟩`.
-/
theorem divAt_of_mem {c : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) {x : 𝓞 E} (hx : x ∈ Q ^ K) :
    DivAt Q c (x : E) := by
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hK x hx
  exact ⟨s, hs, w, by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw⟩

/- English proof (translation)
Unfold `DivAt at *`. Take `⟨s, hs, w, hw⟩` from `hK d hd`. Establish `hsd : (s : E) * (d : E) = (c : E) * (w : E)`. Conclude with `congrArg (fun z : 𝓞 E => (z : E)) hw` after adjusting the coercions. Take `⟨t, ht, v, hv⟩` from `hx`.

Use `⟨s * t, mul_nmem hs ht, w * v, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(s : E) * hv + (v : E) * hsd`.
-/
theorem divAt_trans {c d : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) (hd : d ∈ Q ^ K) {x : E}
    (hx : DivAt Q d x) : DivAt Q c x := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hK d hd
  have hsd : (s : E) * (d : E) = (c : E) * (w : E) := by
    exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination (s : E) * hv + (v : E) * hsd

end Loc

section Mat

variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}

/- English proof (translation)
Unfold `SmallAt`. Introduce `y hy`. Establish `hz` using `(hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩`. Establish `hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]`.

Establish `hdiv : ∀ i, DivAt Q c ((Gᴴ *ᵥ (M *ᵥ y)) i)`. Introduce `i`. Rewrite using `[hGM]`. Use `show DivAt Q c (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)`. Conclude with `divAt_sum Finset.univ _ (fun j _ => divAt_mul_right (hM i j) (hz j))`.

Take `⟨s, hs, hsv⟩` from `(hD ((c : E)⁻¹ • (M *ᵥ y))).mpr (fun i => by`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `intAt_inv_mul hc (hdiv i))`. Use `⟨s, hs, s • ((c : E)⁻¹ • (M *ᵥ y)), hsv, ?_⟩` and prove the remaining obligations. Establish `hcc : (c • (c : E)⁻¹ : E) = 1`.

Rewrite using `[Algebra.smul_def]`. Conclude with `mul_inv_cancel₀ hc`. Rewrite using `[smul_comm c s, ← smul_assoc c ((c : E)⁻¹) (M *ᵥ y), hcc, one_smul]`.
-/
theorem small_of {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {M : Matrix (Fin N) (Fin N) E}
    (hM : ∀ i j, DivAt Q c ((Gᴴ * M * G) i j)) : SmallAt Q c L M := by
  unfold SmallAt
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  have hdiv : ∀ i, DivAt Q c ((Gᴴ *ᵥ (M *ᵥ y)) i) := by
    intro i
    rw [hGM]
    show DivAt Q c (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
    exact divAt_sum Finset.univ _ (fun j _ => divAt_mul_right (hM i j) (hz j))
  obtain ⟨s, hs, hsv⟩ := (hD ((c : E)⁻¹ • (M *ᵥ y))).mpr (fun i => by
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact intAt_inv_mul hc (hdiv i))
  refine ⟨s, hs, s • ((c : E)⁻¹ • (M *ᵥ y)), hsv, ?_⟩
  have hcc : (c • (c : E)⁻¹ : E) = 1 := by
    rw [Algebra.smul_def]
    exact mul_inv_cancel₀ hc
  rw [smul_comm c s, ← smul_assoc c ((c : E)⁻¹) (M *ᵥ y), hcc, one_smul]

/- English proof (translation)
Unfold `DivAt at hx`. Unfold `IntAt`. Take `⟨s, hs, w, hw⟩` from `hx`. Conclude with `⟨s, hs, w, by simpa using hw⟩`.
-/
private theorem intAt_of_divAt_one {x : E} (hx : DivAt Q 1 x) : IntAt Q x := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simpa using hw⟩

/- English proof (translation)
Introduce `y hy`. Establish `hz` using `(hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩`. Apply `(hD (M *ᵥ y)).mpr` to reduce the goal to its premises. Introduce `i`. Establish `hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y)`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]`. Rewrite using `[hGM]`. Use `show IntAt Q (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)`. Conclude with `intAt_of_divAt_one (divAt_sum Finset.univ _ (fun j _ => divAt_mul_left (hM i j) (divAt_one_of_int (hz j))))`.
-/
theorem pres_of {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {M : Matrix (Fin N) (Fin N) E} (hM : ∀ i j, IntAt Q ((Gᴴ * M * G) i j)) :
    ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L := by
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  apply (hD (M *ᵥ y)).mpr
  intro i
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  rw [hGM]
  show IntAt Q (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
  exact intAt_of_divAt_one
    (divAt_sum Finset.univ _ (fun j _ => divAt_mul_left (hM i j) (divAt_one_of_int (hz j))))

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Use `choose! t ht using h`. Establish `hSL : ∀ g ∈ S, g ∈ L` using `fun g hg => hS ▸ Submodule.subset_span (Finset.mem_coe.mpr hg)`. Use `⟨∏ g ∈ S, t g, Finset.prod_induction t (· ∉ Q) (fun a b ha hb => mul_nmem ha hb) one_nmem (fun g hg => (ht g (hSL g hg)).1), ?_⟩` and prove the remaining obligations. Set `F : (Fin N → E) →ₗ[𝓞 E] (Fin N → E)` to `(∏ g ∈ S, t g) • (Matrix.mulVecLin M).restrictScalars (𝓞 E)`.

Establish `hle : Submodule.span (𝓞 E) (S : Set (Fin N → E)) ≤ L.comap F`. Rewrite using `[Submodule.span_le]`. Introduce `g hg`. Establish `hg' : g ∈ S` using `Finset.mem_coe.mp hg`. Use `show (∏ g ∈ S, t g) • (M *ᵥ g) ∈ L`.

Rewrite using `[← Finset.mul_prod_erase S t hg', mul_comm, mul_smul]`. Conclude with `L.smul_mem _ (ht g (hSL g hg')).2`. Introduce `y hy`. Rewrite `hy` using `[← hS]`. Conclude with `hle hy`.
-/
theorem clear {L : Submodule (𝓞 E) (Fin N → E)} (hL : L.FG) {M : Matrix (Fin N) (Fin N) E}
    (h : ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∀ y ∈ L, s • (M *ᵥ y) ∈ L := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose! t ht using h
  have hSL : ∀ g ∈ S, g ∈ L := fun g hg => hS ▸ Submodule.subset_span (Finset.mem_coe.mpr hg)
  refine ⟨∏ g ∈ S, t g, Finset.prod_induction t (· ∉ Q) (fun a b ha hb => mul_nmem ha hb) one_nmem
    (fun g hg => (ht g (hSL g hg)).1), ?_⟩
  let F : (Fin N → E) →ₗ[𝓞 E] (Fin N → E) :=
    (∏ g ∈ S, t g) • (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (S : Set (Fin N → E)) ≤ L.comap F := by
    rw [Submodule.span_le]
    intro g hg
    have hg' : g ∈ S := Finset.mem_coe.mp hg
    show (∏ g ∈ S, t g) • (M *ᵥ g) ∈ L
    rw [← Finset.mul_prod_erase S t hg', mul_comm, mul_smul]
    exact L.smul_mem _ (ht g (hSL g hg')).2
  intro y hy
  rw [← hS] at hy
  exact hle hy

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `small_of hGG hD hc` to reduce the goal to its premises. Introduce `i j`. Establish `hcs : Gᴴ * (e * e - e) * G = (Gᴴ * e * G) * (Gᴴ * e * G) - Gᴴ * e * G`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hGG, mul_one, mul_sub, sub_mul]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by simp only [mul_assoc]`. Rewrite using `[hcs, he]`. Establish `hm : ((t : E) • f) * ((t : E) • f) - (t : E) • f = ((t : E) * (t : E)) • (f * f - f) + ((t : E) * ((t : E) - 1)) • f`.

Rewrite using `[smul_mul_smul_comm, smul_sub, mul_sub, mul_one, sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hm]`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `divAt_add (divAt_mul_left (intAt_mul (intAt_coe t) (intAt_coe t)) (hf2 i j)) (divAt_mul_right (divAt_mul_left (intAt_coe t) ht) (hf i j))`.

Apply `small_of hGG hD hc` to reduce the goal to its premises. Introduce `i j`. Establish `hch : Gᴴ * (e + eᴴ - 1) * G = Gᴴ * e * G + (Gᴴ * e * G)ᴴ - 1`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_sub, mul_add, sub_mul, add_mul, mul_one, hG1]`. Simplify using `only [mul_assoc]`.

Rewrite using `[hch, he]`. Establish `hm : (t : E) • f + ((t : E) • f)ᴴ - 1 = star (t : E) • (f + fᴴ - 1) + ((t : E) - star (t : E)) • f + (star (t : E) - 1) • (1 : Matrix (Fin N) (Fin N) E)`. Rewrite using `[Matrix.conjTranspose_smul, smul_sub, smul_add, sub_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hm]`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h1 : IntAt Q ((1 : Matrix (Fin N) (Fin N) E) i j)`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `intAt_one`.

Conclude with `intAt_zero`. Establish `h2 : DivAt Q c ((t : E) - star (t : E))`. Rewrite using `[show (t : E) - star (t : E) = ((t : E) - 1) - (star (t : E) - 1) by ring]`. Conclude with `divAt_sub ht ht'`. Conclude with `divAt_add (divAt_add (divAt_mul_left ht'' (hf3 i j)) (divAt_mul_right h2 (hf i j))) (divAt_mul_right ht' h1)`.
-/
theorem good_gen {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hG1 : Gᴴ * G = 1) (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {f : Matrix (Fin N) (Fin N) E} (hf : ∀ i j, IntAt Q (f i j))
    (hf2 : ∀ i j, DivAt Q c ((f * f - f) i j)) (hf3 : ∀ i j, DivAt Q c ((f + fᴴ - 1) i j))
    {t : 𝓞 E} (ht : DivAt Q c ((t : E) - 1)) (ht' : DivAt Q c (star (t : E) - 1))
    (ht'' : IntAt Q (star (t : E)))
    {e : Matrix (Fin N) (Fin N) E} (he : Gᴴ * e * G = (t : E) • f) :
    SmallAt Q c L (e * e - e) ∧ SmallAt Q c L (e + eᴴ - 1) := by
  constructor
  · apply small_of hGG hD hc
    intro i j
    have hcs : Gᴴ * (e * e - e) * G = (Gᴴ * e * G) * (Gᴴ * e * G) - Gᴴ * e * G := by
      calc Gᴴ * (e * e - e) * G = Gᴴ * e * (G * Gᴴ) * e * G - Gᴴ * e * G := by
            rw [hGG, mul_one, mul_sub, sub_mul]
            simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    rw [hcs, he]
    have hm : ((t : E) • f) * ((t : E) • f) - (t : E) • f =
        ((t : E) * (t : E)) • (f * f - f) + ((t : E) * ((t : E) - 1)) • f := by
      rw [smul_mul_smul_comm, smul_sub, mul_sub, mul_one, sub_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact divAt_add (divAt_mul_left (intAt_mul (intAt_coe t) (intAt_coe t)) (hf2 i j))
      (divAt_mul_right (divAt_mul_left (intAt_coe t) ht) (hf i j))
  · apply small_of hGG hD hc
    intro i j
    have hch : Gᴴ * (e + eᴴ - 1) * G = Gᴴ * e * G + (Gᴴ * e * G)ᴴ - 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        mul_sub, mul_add, sub_mul, add_mul, mul_one, hG1]
      simp only [mul_assoc]
    rw [hch, he]
    have hm : (t : E) • f + ((t : E) • f)ᴴ - 1 = star (t : E) • (f + fᴴ - 1) +
        ((t : E) - star (t : E)) • f + (star (t : E) - 1) • (1 : Matrix (Fin N) (Fin N) E) := by
      rw [Matrix.conjTranspose_smul, smul_sub, smul_add, sub_smul, sub_smul, one_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : IntAt Q ((1 : Matrix (Fin N) (Fin N) E) i j) := by
      rw [Matrix.one_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    have h2 : DivAt Q c ((t : E) - star (t : E)) := by
      rw [show (t : E) - star (t : E) = ((t : E) - 1) - (star (t : E) - 1) by ring]
      exact divAt_sub ht ht'
    exact divAt_add (divAt_add (divAt_mul_left ht'' (hf3 i j)) (divAt_mul_right h2 (hf i j)))
      (divAt_mul_right ht' h1)

end Mat

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu, mul_one, mul_sub, sub_mul]`. Simplify using `only [mul_assoc]`.
-/
theorem conj_sq {N : ℕ} (u e : Matrix (Fin N) (Fin N) E) (hu : u * uᴴ = 1) :
    (uᴴ * e * u) * (uᴴ * e * u) - uᴴ * e * u = uᴴ * (e * e - e) * u := by
  calc (uᴴ * e * u) * (uᴴ * e * u) - uᴴ * e * u
      = uᴴ * e * (u * uᴴ) * e * u - uᴴ * e * u := by simp only [mul_assoc]
    _ = uᴴ * (e * e - e) * u := by
      rw [hu, mul_one, mul_sub, sub_mul]
      simp only [mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_sub, mul_add, sub_mul, add_mul, mul_one, hu]`. Simplify using `only [mul_assoc]`.
-/
theorem conj_herm {N : ℕ} (u e : Matrix (Fin N) (Fin N) E) (hu : uᴴ * u = 1) :
    uᴴ * e * u + (uᴴ * e * u)ᴴ - 1 = uᴴ * (e + eᴴ - 1) * u := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    mul_sub, mul_add, sub_mul, add_mul, mul_one, hu]
  simp only [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem star_coe (t : 𝓞 E) : star (t : E) = ((cj E t : 𝓞 E) : E) := by
  rfl

/- English proof (translation)
Unfold `InertAsm InertPlace`. Introduce `hLCP hME hD hLM hPL E _ _ _ hE N L' L'' hN hL' hL'' Q hQ hcj c hc`. Use `haveI : Q.IsPrime := hQ.isPrime`. Take `⟨M⟩` from `hME E hE Q hQ hcj`. Take `⟨G', hG'1, hG'2, hD'⟩` from `hD E hE N L' hL' Q hQ hcj`.

Take `⟨G'', hG''1, hG''2, hD''⟩` from `hD E hE N L'' hL'' Q hQ hcj`. Establish `hu1 : (G'ᴴ * G'')ᴴ * (G'ᴴ * G'') = 1`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc, ← mul_assoc G' G'ᴴ G'', hG'2, one_mul, hG''1]`. Establish `hu2 : (G'ᴴ * G'') * (G'ᴴ * G'')ᴴ = 1`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc, ← mul_assoc G'' G''ᴴ G', hG''2, one_mul, hG'1]`.

Unfold `PowLoc at hPL`. Take `⟨K, hK⟩` from `hPL E Q hQ c hc`. Take `⟨e₁, h1, h2, h3, h4, h5, h6⟩` from `hLM E Q hQ M hLCP N hN (G'ᴴ * G'') hu1 hu2 K`. Establish `hϖ : M.ϖ ^ K ∈ Q ^ K` using `Ideal.pow_mem_pow M.ϖ_Q K`. Establish `tr : ∀ x : E, DivAt Q (M.ϖ ^ K) x → DivAt Q c x` using `fun x hx => divAt_trans hK hϖ hx`.

Establish `hFG' : L'.FG`. Unfold `IsSDG at hL'`. Conclude with `hL'.1`. Establish `hFG'' : L''.FG`. Unfold `IsSDG at hL''`.

Conclude with `hL''.1`. Establish `hA' : G'ᴴ * (G' * e₁ * G'ᴴ) * G' = e₁`. Simplify using `only [mul_assoc, hG'1, mul_one]`. Rewrite using `[← mul_assoc, hG'1, one_mul]`. Establish `hA'' : G''ᴴ * (G' * e₁ * G'ᴴ) * G'' = (G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'')`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Simplify using `only [mul_assoc]`. Take `⟨s', hs', hs'L⟩` from `clear hFG' (pres_of hG'2 hD' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA']; exact h1 i j))`. Take `⟨s'', hs'', hs''L⟩` from `clear hFG'' (pres_of hG''2 hD'' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA'']; exact h2 i j))`. Take `⟨y, i, hi, hyi⟩` from `hQ.exists_inv (mul_nmem hs' hs'')`.

Take `⟨t, ht⟩ : ∃ t : 𝓞 E, t = s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k)` from `⟨_, rfl⟩`. Establish `ht1 : t - 1 = -(i ^ K)`. Establish `hg` using `geom_sum_mul i K`. Take the linear combination `ht + (∑ k ∈ Finset.range K, i ^ k) * hyi - hg`. Establish `htQ : t - 1 ∈ Q ^ K`.

Rewrite using `[ht1]`. Conclude with `neg_mem (Ideal.pow_mem_pow hi K)`. Establish `hci : cj E i ∈ Q`. Establish `hi' : i ∈ Ideal.comap (cj E) Q` using `by rw [hcj]; exact hi`. Conclude with `hi'`.

Establish `hct : cj E t - 1 ∈ Q ^ K`. Establish `hc1 : cj E t - 1 = -((cj E i) ^ K)`. Rewrite using `[← map_one (cj E), ← map_sub, ht1, map_neg, map_pow]`. Rewrite using `[hc1]`. Conclude with `neg_mem (Ideal.pow_mem_pow hci K)`.

Establish `htc : DivAt Q c ((t : E) - 1)`. Establish `h` using `divAt_of_mem hK htQ`. Move the coercions through the operations in `at h`. Conclude with `h`. Establish `htc' : DivAt Q c (star (t : E) - 1)`.

Rewrite using `[star_coe]`. Establish `h` using `divAt_of_mem hK hct`. Move the coercions through the operations in `at h`. Conclude with `h`. Establish `htc'' : IntAt Q (star (t : E))`.

Rewrite using `[star_coe]`. Conclude with `intAt_coe _`. Establish `hE' : G'ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G' = (t : E) • e₁`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, hA']`. Establish `hE'' : G''ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G'' = (t : E) • ((G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G''))`.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, hA'']`. Establish `hcE : (c : E) ≠ 0` using `by exact_mod_cast hc`. Take `⟨a1, a2⟩` from `good_gen hG'1 hG'2 hD' hcE h1 (fun i j => tr _ (h3 i j)) (fun i j => tr _ (h5 i j)) htc htc' htc'' hE'`. Take `⟨b1, b2⟩` from `good_gen hG''1 hG''2 hD'' hcE h2 (fun i j => by rw [conj_sq (G'ᴴ * G'') e₁ hu2]; exact tr _ (h4 i j)) (fun i j => by rw [conj_herm (G'ᴴ * G'') e₁ hu1]; exact tr _ (h6 i j)) htc htc' htc'' hE''`. Use `⟨(t : E) • (G' * e₁ * G'ᴴ), ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `Pres`. Introduce `z hz`. Establish `hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z)` using `by first`. Consider the case `exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z`. Consider the case `(ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])`.

Rewrite using `[hsm, show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _, ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) = (s'' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s' by ring, mul_smul]`. Conclude with `L'.smul_mem _ (hs'L z hz)`. Unfold `Pres`. Introduce `z hz`. Establish `hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z)` using `by first`.

Consider the case `exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z`. Consider the case `(ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])`. Rewrite using `[hsm, show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _, ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) = (s' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s'' by ring, mul_smul]`. Conclude with `L''.smul_mem _ (hs''L z hz)`. Unfold `Good`.

Conclude with `⟨a1, b1, a2, b2⟩`.
-/
theorem inertAsm : InertAsm := by
  unfold InertAsm InertPlace
  intro hLCP hME hD hLM hPL E _ _ _ hE N L' L'' hN hL' hL'' Q hQ hcj c hc
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨M⟩ := hME E hE Q hQ hcj
  obtain ⟨G', hG'1, hG'2, hD'⟩ := hD E hE N L' hL' Q hQ hcj
  obtain ⟨G'', hG''1, hG''2, hD''⟩ := hD E hE N L'' hL'' Q hQ hcj
  have hu1 : (G'ᴴ * G'')ᴴ * (G'ᴴ * G'') = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G' G'ᴴ G'', hG'2, one_mul, hG''1]
  have hu2 : (G'ᴴ * G'') * (G'ᴴ * G'')ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G'' G''ᴴ G', hG''2, one_mul, hG'1]
  unfold PowLoc at hPL
  obtain ⟨K, hK⟩ := hPL E Q hQ c hc
  obtain ⟨e₁, h1, h2, h3, h4, h5, h6⟩ := hLM E Q hQ M hLCP N hN (G'ᴴ * G'') hu1 hu2 K
  have hϖ : M.ϖ ^ K ∈ Q ^ K := Ideal.pow_mem_pow M.ϖ_Q K
  have tr : ∀ x : E, DivAt Q (M.ϖ ^ K) x → DivAt Q c x := fun x hx => divAt_trans hK hϖ hx
  have hFG' : L'.FG := by
    unfold IsSDG at hL'
    exact hL'.1
  have hFG'' : L''.FG := by
    unfold IsSDG at hL''
    exact hL''.1
  have hA' : G'ᴴ * (G' * e₁ * G'ᴴ) * G' = e₁ := by
    simp only [mul_assoc, hG'1, mul_one]
    rw [← mul_assoc, hG'1, one_mul]
  have hA'' : G''ᴴ * (G' * e₁ * G'ᴴ) * G'' = (G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'') := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [mul_assoc]
  obtain ⟨s', hs', hs'L⟩ := clear hFG'
    (pres_of hG'2 hD' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA']; exact h1 i j))
  obtain ⟨s'', hs'', hs''L⟩ := clear hFG''
    (pres_of hG''2 hD'' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA'']; exact h2 i j))
  obtain ⟨y, i, hi, hyi⟩ := hQ.exists_inv (mul_nmem hs' hs'')
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t = s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) := ⟨_, rfl⟩
  have ht1 : t - 1 = -(i ^ K) := by
    have hg := geom_sum_mul i K
    linear_combination ht + (∑ k ∈ Finset.range K, i ^ k) * hyi - hg
  have htQ : t - 1 ∈ Q ^ K := by
    rw [ht1]
    exact neg_mem (Ideal.pow_mem_pow hi K)
  have hci : cj E i ∈ Q := by
    have hi' : i ∈ Ideal.comap (cj E) Q := by rw [hcj]; exact hi
    exact hi'
  have hct : cj E t - 1 ∈ Q ^ K := by
    have hc1 : cj E t - 1 = -((cj E i) ^ K) := by
      rw [← map_one (cj E), ← map_sub, ht1, map_neg, map_pow]
    rw [hc1]
    exact neg_mem (Ideal.pow_mem_pow hci K)
  have htc : DivAt Q c ((t : E) - 1) := by
    have h := divAt_of_mem hK htQ
    push_cast at h
    exact h
  have htc' : DivAt Q c (star (t : E) - 1) := by
    rw [star_coe]
    have h := divAt_of_mem hK hct
    push_cast at h
    exact h
  have htc'' : IntAt Q (star (t : E)) := by
    rw [star_coe]
    exact intAt_coe _
  have hE' : G'ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G' = (t : E) • e₁ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA']
  have hE'' : G''ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G'' =
      (t : E) • ((G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'')) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA'']
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  obtain ⟨a1, a2⟩ := good_gen hG'1 hG'2 hD' hcE h1 (fun i j => tr _ (h3 i j)) (fun i j => tr _ (h5 i j))
    htc htc' htc'' hE'
  obtain ⟨b1, b2⟩ := good_gen hG''1 hG''2 hD'' hcE h2
    (fun i j => by rw [conj_sq (G'ᴴ * G'') e₁ hu2]; exact tr _ (h4 i j))
    (fun i j => by rw [conj_herm (G'ᴴ * G'') e₁ hu1]; exact tr _ (h6 i j))
    htc htc' htc'' hE''
  refine ⟨(t : E) • (G' * e₁ * G'ᴴ), ?_, ?_, ?_⟩
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s'' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s' by ring, mul_smul]
    exact L'.smul_mem _ (hs'L z hz)
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s'' by ring, mul_smul]
    exact L''.smul_mem _ (hs''L z hz)
  · unfold Good
    exact ⟨a1, b1, a2, b2⟩

end PI.SqPairLocal
