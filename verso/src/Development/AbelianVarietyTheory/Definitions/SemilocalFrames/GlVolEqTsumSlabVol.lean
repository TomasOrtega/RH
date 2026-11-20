import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaussDensDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def colM (x : Fin 3 → E) : Matrix (Fin 3) (Fin 1) E := Matrix.of fun a _ => x a

def lineFlag (E : Type) [Field E] [NumberField E] : Fin 2 → Submodule (𝓞 E) (Fin 3 → E) :=
  ![⊥, (intLat E 1).map ((Matrix.mulVecLin (colM (E := E) ![1, 1, 0])).restrictScalars (𝓞 E))]

/- English proof (translation)
Take `⟨s, hs⟩` from `hx`. Conclude with `⟨⟨star (s : E), s.2.map (starRingEnd E).toIntAlgHom⟩, by rw [← hs]; rfl⟩`.
-/
theorem star_mem_int {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) : star x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨s, hs⟩ := hx
  exact ⟨⟨star (s : E), s.2.map (starRingEnd E).toIntAlgHom⟩, by rw [← hs]; rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h (fun _ => 1) ((mem_intLat _).2 fun _ => one_mem _)` as an intermediate fact. Simplify `this` using `[dotProduct]`. Introduce `h t ht`.

Use `mul_mem (star_mem_int ((mem_intLat _).1 ht 0)) h` as an intermediate fact. Simplify `this` using `[dotProduct]`.
-/
theorem dual_intLat_one (u : Fin 1 → E) :
    (∀ t ∈ intLat E 1, star t ⬝ᵥ u ∈ (algebraMap (𝓞 E) E).range) ↔ u 0 ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro h
    have := h (fun _ => 1) ((mem_intLat _).2 fun _ => one_mem _)
    simpa [dotProduct] using this
  · intro h t ht
    have := mul_mem (star_mem_int ((mem_intLat _).1 ht 0)) h
    simpa [dotProduct] using this

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[signMat, Matrix.mul_diagonal, colM, Fin.sum_univ_three, sub_eq_add_neg]`.
-/
theorem colM_gram (x y : Fin 3 → E) : (colM x)ᴴ * signMat E ![true, false, true] * colM y =
    Matrix.of fun _ _ => star (x 0) * y 0 - star (x 1) * y 1 + star (x 2) * y 2 := by
  ext a b
  rw [Matrix.mul_apply]
  simp [signMat, Matrix.mul_diagonal, colM, Fin.sum_univ_three, sub_eq_add_neg]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[colM, Matrix.mulVec, dotProduct]`.
-/
theorem colM_mulVec (x : Fin 3 → E) (u : Fin 1 → E) : colM x *ᵥ u = fun a => x a * u 0 := by
  funext a; simp [colM, Matrix.mulVec, dotProduct]

/- English proof (translation)
Unfold `IsAdapted`. Rewrite using `[GlobalTheory.GaussMean.Test.lamX_one, GlobalTheory.GaussMean.Test.lamX_one]`. Use `⟨fun _ => rfl, rfl, fun _ => (⟨intLat_fg 1, intLat_span 1⟩ : Submodule.IsLattice E (intLat E 1)), fun i k => ⟨?_, ?_, fun h => absurd (Subsingleton.elim _ _) h⟩, fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : (colM (E` using `E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, 0] = 0 := by`. Rewrite using `[colM_gram]`.

Use extensionality with `a b`. Take `rfl` from `Subsingleton.elim a b`. Simplify using `[signMat]`. Conclude with `h`. Establish `h : (colM (E` using `E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 0 := by`.

Rewrite using `[colM_gram]`. Use extensionality with `a b`. Take `rfl` from `Subsingleton.elim a b`. Simplify using `[signMat]`. Conclude with `h`.

Establish `h : (colM (E` using `E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 1 := by`. Rewrite using `[colM_gram]`. Use extensionality with `a b`. Take `rfl` from `Subsingleton.elim a b`. Simplify using `[signMat]`.

Conclude with `h`. Establish `h : (colM (E` using `E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by`. Rewrite using `[colM_gram]`. Use extensionality with `a b`. Take `rfl` from `Subsingleton.elim a b`.

Simplify using `[signMat]`. Conclude with `h`. Establish `h : (colM (E` using `E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by`. Rewrite using `[colM_gram]`. Use extensionality with `a b`.

Take `rfl` from `Subsingleton.elim a b`. Simplify using `[signMat]`. Conclude with `h`. Establish `h : (colM (E` using `E) ![1, 1, -1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = (signMat E ![true]).map (RingEquiv.refl E) := by`. Rewrite using `[colM_gram]`.

Use extensionality with `a b`. Take `rfl` from `Subsingleton.elim a b`. Simplify using `[signMat]`. Conclude with `h`. Use `show ∀ z : Fin 3 → E, z ∈ intLat E 3 ↔ ∃ (u u' : Fin 1 → Fin 1 → E) (y : Fin 1 → E), (∀ i, u i ∈ intLat E 1) ∧ (∀ i, ∀ t ∈ intLat E 1, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 E) E).range) ∧ y ∈ intLat E 1 ∧ z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i + ∑ i, colM (E := E) ![0, -1, 1] *ᵥ u' i …`.

Introduce `z`. Simplify using `only [dual_intLat_one]`. Simplify using `only [mem_intLat, colM_mulVec, Fin.sum_univ_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨fun _ _ => z 1 + z 2, fun _ _ => z 0 - z 1, fun _ => z 0 - z 1 - z 2, fun _ _ => add_mem (h 1) (h 2), fun _ => sub_mem (h 0) (h 1), fun _ => sub_mem (sub_mem (h 0) (h 1)) (h 2), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `funext a; fin_cases a <;> simp <;> ring`. Introduce and unpack `⟨u, u', y, hu, hu', hy, rfl⟩ a fin_cases a`. Simplify using `using add_mem (hu 0 0) (hy 0)`. Simplify using `using add_mem (add_mem (hu 0 0) (neg_mem (hu' 0))) (hy 0)`.

Simplify using `using add_mem (hu' 0) (neg_mem (hy 0))`. Use `show ∀ (k : Fin 2) (z : Fin 3 → E), z ∈ lineFlag E k ↔ ∃ u : Fin 1 → Fin 1 → E, (∀ i, u i ∈ intLat E 1) ∧ (∀ i : Fin 1, ¬ i.castSucc < k → u i = 0) ∧ z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i`. Introduce `k z`. Use `fin_cases k`. Simplify using `only [lineFlag, Fin.sum_univ_one]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨0, fun _ => zero_mem _, fun _ _ => rfl, by simpa using h⟩`. Introduce and unpack `⟨u, -, h, rfl⟩`. Simplify using `[h 0 (by simp)]`.

Simplify using `only [lineFlag, Fin.sum_univ_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun _ => u, fun _ => hu, fun i hi => absurd (by fin_cases i; simp) hi, rfl⟩`. Introduce and unpack `⟨u, hu, -, rfl⟩`.

Conclude with `⟨u 0, hu 0, rfl⟩`.
-/
theorem isAdapted_rank_three (cm : Formalism.BasicNotions.CMData F E) :
    IsAdapted (ofSigns cm ![true, false, true]) (ofSigns cm ![true]) (RingEquiv.refl E) 1 (a := 1) (fun _ => 1)
      (lineFlag E) (fun _ => intLat E 1) 1 (fun _ => colM (E := E) ![1, 1, 0]) (fun _ => colM (E := E) ![0, -1, 1])
      (colM (E := E) ![1, 1, -1]) := by
  unfold IsAdapted
  rw [GlobalTheory.GaussMean.Test.lamX_one, GlobalTheory.GaussMean.Test.lamX_one]
  refine ⟨fun _ => rfl, rfl, fun _ => (⟨intLat_fg 1, intLat_span 1⟩ : Submodule.IsLattice E (intLat E 1)), fun i k => ⟨?_, ?_, fun h => absurd (Subsingleton.elim _ _) h⟩,
    fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, 0] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![0, -1, 1] = 1 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, 0])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![0, -1, 1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = 0 := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · have h : (colM (E := E) ![1, 1, -1])ᴴ * signMat E ![true, false, true] * colM (E := E) ![1, 1, -1] = (signMat E ![true]).map (RingEquiv.refl E) := by
      rw [colM_gram]; ext a b; obtain rfl := Subsingleton.elim a b; simp [signMat]
    exact h
  · show ∀ z : Fin 3 → E, z ∈ intLat E 3 ↔ ∃ (u u' : Fin 1 → Fin 1 → E) (y : Fin 1 → E), (∀ i, u i ∈ intLat E 1) ∧
      (∀ i, ∀ t ∈ intLat E 1, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 E) E).range) ∧ y ∈ intLat E 1 ∧
      z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i + ∑ i, colM (E := E) ![0, -1, 1] *ᵥ u' i + colM (E := E) ![1, 1, -1] *ᵥ y
    intro z
    simp only [dual_intLat_one]
    simp only [mem_intLat, colM_mulVec, Fin.sum_univ_one]
    constructor
    · intro h
      refine ⟨fun _ _ => z 1 + z 2, fun _ _ => z 0 - z 1, fun _ => z 0 - z 1 - z 2, fun _ _ => add_mem (h 1) (h 2),
        fun _ => sub_mem (h 0) (h 1), fun _ => sub_mem (sub_mem (h 0) (h 1)) (h 2), ?_⟩
      funext a; fin_cases a <;> simp <;> ring
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩ a
      fin_cases a
      · simpa using add_mem (hu 0 0) (hy 0)
      · simpa using add_mem (add_mem (hu 0 0) (neg_mem (hu' 0))) (hy 0)
      · simpa using add_mem (hu' 0) (neg_mem (hy 0))
  · show ∀ (k : Fin 2) (z : Fin 3 → E), z ∈ lineFlag E k ↔ ∃ u : Fin 1 → Fin 1 → E, (∀ i, u i ∈ intLat E 1) ∧
      (∀ i : Fin 1, ¬ i.castSucc < k → u i = 0) ∧ z = ∑ i, colM (E := E) ![1, 1, 0] *ᵥ u i
    intro k z
    fin_cases k
    · simp only [lineFlag, Fin.sum_univ_one]
      constructor
      · intro h
        exact ⟨0, fun _ => zero_mem _, fun _ _ => rfl, by simpa using h⟩
      · rintro ⟨u, -, h, rfl⟩
        simp [h 0 (by simp)]
    · simp only [lineFlag, Fin.sum_univ_one]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨fun _ => u, fun _ => hu, fun i hi => absurd (by fin_cases i; simp) hi, rfl⟩
      · rintro ⟨u, hu, -, rfl⟩
        exact ⟨u 0, hu 0, rfl⟩

/- English proof (translation)
Take `⟨I, -⟩` from `exists_signature 0 0`. Conclude with `⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, isAdapted_rank_three I.cm⟩`.
-/
theorem exists_isAdapted : ∃ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf)
    (S : Fin 2 → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ _ : Fin 1, Submodule (𝓞 I.E) (Fin 1 → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ _ : Fin 1, Matrix (Fin I.n) (Fin 1) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E),
    I.n = 3 ∧ I₀.n = 1 ∧ IsAdapted I I₀ e xf (a := 1) (fun _ => 1) S Λ x₀ T T' T₀ := by
  obtain ⟨I, -⟩ := exists_signature 0 0
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, isAdapted_rank_three I.cm⟩

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hL, hS⟩` from `h`. Use `⟨eq_bot_iff.2 fun z hz => ?_, fun k l hkl z hz => ?_, fun k z hz => ?_⟩` and prove the remaining obligations. Take `⟨u, -, h0, rfl⟩` from `(hS 0 z).1 hz`. Simplify using `[fun i => h0 i (by simp)]`. Take `⟨u, hu, h0, rfl⟩` from `(hS k z).1 hz`.

Conclude with `(hS l _).2 ⟨u, hu, fun i hi => h0 i fun h => hi (h.trans_le hkl), rfl⟩`. Take `⟨u, hu, -, rfl⟩` from `(hS k z).1 hz`. Use `(hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simp, zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, Matrix.mulVec_zero, Finset.sum_const_zero, map_zero, add_zero]`. Rewrite using `[show (fun _ : Fin I₀.n => (0 : I.E)) = 0 from rfl, Matrix.mulVec_zero, add_zero]`.
-/
theorem IsAdapted_flag {I I₀ : AutInst} {e : I₀.E ≃+* I.E} {xf : I.Gf} {a : ℕ} {j : Fin a → ℕ}
    {S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)} {Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)}
    {x₀ : I₀.Gf} {T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E} {T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E}
    (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) : S 0 = ⊥ ∧ Monotone S ∧ ∀ k, S k ≤ lamX I (1, xf) := by
  obtain ⟨-, -, -, -, -, -, hL, hS⟩ := h
  refine ⟨eq_bot_iff.2 fun z hz => ?_, fun k l hkl z hz => ?_, fun k z hz => ?_⟩
  · obtain ⟨u, -, h0, rfl⟩ := (hS 0 z).1 hz
    simp [fun i => h0 i (by simp)]
  · obtain ⟨u, hu, h0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => h0 i fun h => hi (h.trans_le hkl), rfl⟩
  · obtain ⟨u, hu, -, rfl⟩ := (hS k z).1 hz
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simp, zero_mem _, ?_⟩
    simp only [Pi.zero_apply, Matrix.mulVec_zero, Finset.sum_const_zero, map_zero, add_zero]
    rw [show (fun _ : Fin I₀.n => (0 : I.E)) = 0 from rfl, Matrix.mulVec_zero, add_zero]

/- English proof (translation)
Establish `hu : ∀ v, uMat ((1 : I.Ginf) v) = 1` using `fun v => rfl`. Establish `hL : (1 : I.Ginf) ∈ latGroup I xf`. Use `⟨1, ⟨1, one_mem _, fun v => ?_, ?_⟩, rfl, ?_⟩` and prove the remaining obligations. Use `(Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)` as an intermediate fact. Rewrite using `[show uMat ((1 : I.GA).1 v) = 1 from rfl]`.

Simplify using `[Matrix.nonsing_inv_mul _ this]`. Rewrite using `[show I.fmat (1 : I.GA).2 = 1 from rfl]`. Simplify using the standard rewrite rules. Simplify using `only [Prod.snd_one, mul_one, inv_mul_cancel]`. Conclude with `one_mem (Formalism.UG.stabGL I.Lf)`.

Use `⟨fun v i y hy => (by rw [hu]; simp [hy]), 1, ⟨hL, fun v k y hy => (by rw [hu]; simp [hy])⟩, 1, fun v => ⟨fun i y _ => (by rw [hu]; simp), fun y _ => (by rw [hu]; simp)⟩, by simp⟩` and prove the remaining obligations.
-/
theorem one_mem_leviGroup (I : AutInst) (xf : I.Gf) {a : ℕ}
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : (1 : I.Ginf) ∈ leviGroup I xf S := by
  have hu : ∀ v, uMat ((1 : I.Ginf) v) = 1 := fun v => rfl
  have hL : (1 : I.Ginf) ∈ latGroup I xf := by
    refine ⟨1, ⟨1, one_mem _, fun v => ?_, ?_⟩, rfl, ?_⟩
    · have := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl]
      simp [Matrix.nonsing_inv_mul _ this]
    · rw [show I.fmat (1 : I.GA).2 = 1 from rfl]
      simp
    · simp only [Prod.snd_one, mul_one, inv_mul_cancel]
      exact one_mem (Formalism.UG.stabGL I.Lf)
  refine ⟨fun v i y hy => (by rw [hu]; simp [hy]), 1, ⟨hL, fun v k y hy => (by rw [hu]; simp [hy])⟩, 1,
    fun v => ⟨fun i y _ => (by rw [hu]; simp), fun y _ => (by rw [hu]; simp)⟩, by simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glVol_eq_tsum_slabVol (E : Type) [Field E] [NumberField E] (j : ℕ) :
    glVol E j = ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
      slabVol E j (Quot.out c).1 := rfl

/- English proof (translation)
Use `⟨fun hy => ?_, fun h => Submodule.subset_span h⟩` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y h => exact h`. Consider the case `zero => exact fun x _ => ⟨0, by simp⟩`. Consider the case `add a b _ _ ha hb`.

Introduce `x hx`. Take `⟨p, hp⟩` from `ha x hx`. Take `⟨q, hq⟩` from `hb x hx`. Conclude with `⟨p + q, by simp [dotProduct_add, Finset.sum_add_distrib, hp, hq]⟩`. Consider the case `smul n a _ ha`.

Introduce `x hx`. Take `⟨p, hp⟩` from `ha x hx`. Use `⟨n * p, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hp, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, dotProduct_smul]`. Simplify using the standard rewrite rules.
-/
theorem mem_dualAt (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j)) (y : VecInf E j) :
    y ∈ dualAt E j L ↔ ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
  refine ⟨fun hy => ?_, fun h => Submodule.subset_span h⟩
  induction hy using Submodule.span_induction with
  | mem y h => exact h
  | zero => exact fun x _ => ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    obtain ⟨q, hq⟩ := hb x hx
    exact ⟨p + q, by simp [dotProduct_add, Finset.sum_add_distrib, hp, hq]⟩
  | smul n a _ ha =>
    intro x hx
    obtain ⟨p, hp⟩ := ha x hx
    refine ⟨n * p, ?_⟩
    push_cast
    rw [← hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pi.smul_apply, dotProduct_smul]
    simp

open MeasureTheory NumberField Matrix Finset in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in

/- English proof (translation)
Take `⟨γ', hγΛ, hγ'⟩` from `hγ`. Establish `hγw : ∀ w : InfinitePlace E, Matrix.of (γ w) = (γ' : Matrix (Fin j) (Fin j) E).map w.embedding` using `fun w => by`. Use extensionality with `a b`. Simplify using `[hγ' w a b]`. Establish `hinv : ∀ w : InfinitePlace E, (Matrix.of (γ w))⁻¹ = ((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).map w.embedding` using `fun w => by`.

Rewrite using `[hγw]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Simplify using the standard rewrite rules. Establish `key : ∀ (w : InfinitePlace E) (y : Fin j → E), (Matrix.of ((γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = (Matrix.of (g w))⁻¹ *ᵥ (fun a => w.embedding ((((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a))`.

Introduce `w y`. Rewrite using `[_root_.GlobalTheory.OrbitTerm.of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `(RingHom.map_mulVec w.embedding _ y a).symm`.

Unfold `_root_.GlobalTheory.FlagBase.latAt`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hγΛ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `hy`. Use function extensionality and compare the values at `w`.

Conclude with `(key w y).symm`. Introduce and unpack `⟨z, hz, rfl⟩`. Use `⟨(γ' : Matrix (Fin j) (Fin j) E) *ᵥ z, (hγΛ z).mpr hz, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Rewrite using `[key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) {γ : _root_.GlobalTheory.FlagMeas.MatInf E j}
    (hγ : γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ) (g : _root_.GlobalTheory.FlagMeas.MatInf E j) :
    _root_.GlobalTheory.FlagBase.latAt E j Λ (γ * g) = _root_.GlobalTheory.FlagBase.latAt E j Λ g := by
  obtain ⟨γ', hγΛ, hγ'⟩ := hγ
  have hγw : ∀ w : InfinitePlace E,
      Matrix.of (γ w) = (γ' : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    ext a b
    simp [hγ' w a b]
  have hinv : ∀ w : InfinitePlace E, (Matrix.of (γ w))⁻¹ =
      ((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    rw [hγw]
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  have key : ∀ (w : InfinitePlace E) (y : Fin j → E),
      (Matrix.of ((γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) =
        (Matrix.of (g w))⁻¹ *ᵥ
          (fun a => w.embedding ((((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a)) := by
    intro w y
    rw [_root_.GlobalTheory.OrbitTerm.of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    congr 1
    funext a
    exact (RingHom.map_mulVec w.embedding _ y a).symm
  unfold _root_.GlobalTheory.FlagBase.latAt
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y, ?_, ?_⟩
    · rw [← hγΛ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
      exact hy
    · funext w
      exact (key w y).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(γ' : Matrix (Fin j) (Fin j) E) *ᵥ z, (hγΛ z).mpr hz, ?_⟩
    funext w
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

end GlobalTheory.FlagBase.Test
