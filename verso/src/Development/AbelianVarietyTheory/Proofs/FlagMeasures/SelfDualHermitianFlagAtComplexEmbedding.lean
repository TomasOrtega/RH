import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpSetBaseChange
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MainTheorem

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem`. Consider the case `exact _root_.GlobalTheory.DenominatorTheorem.main_theorem`. Consider the case `(apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)`.
-/
theorem exists_smul_mem (G : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (G : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ G := by
  first
  | exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem
  | exact _root_.GlobalTheory.DenominatorTheorem.main_theorem
  | (apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)

/- English proof (translation)
Establish `hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0` using `by simpa using hc`. Establish `e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l)`. Use function extensionality and compare the values at `l`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)`.
-/
theorem mem_locFlag_of_smul (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) {c : 𝓞 E} (hc : c ≠ 0) {y : Fin n → E}
    (hy : c • y ∈ F b) : (P⁻¹ *ᵥ fun l => φ (y l)) ∈ locFlag φ P F b := by
  have hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc
  have e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l) := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [e, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨y, hy, rfl⟩ := hx`. Conclude with `h y hy`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul]`. Conclude with `W.smul_mem _ hx`.
-/
theorem mulVec_mem_of_span (φ : E →+* ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (S : Set (Fin n → E))
    (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ S, (Q *ᵥ fun l => φ (y l)) ∈ W) {u : Fin n → ℂ}
    (hu : u ∈ Submodule.span ℂ ((fun w : Fin n → E => fun i => φ (w i)) '' S)) : Q *ᵥ u ∈ W := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem _ hx

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `e : (P⁻¹)ᴴ * Pᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]`.
-/
theorem form_frame {P K M : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * K * P = M)
    (u v : Fin n → ℂ) : star (P⁻¹ *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ (K *ᵥ (P *ᵥ v)) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]

omit [NumberField E] in
/- English proof (translation)
Simplify using `[dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]`.
-/
theorem form_emb [StarRing E] (φ : E →+* ℂ) (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    star (fun l => φ (x l)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) = φ (star x ⬝ᵥ (J *ᵥ y)) := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]

/- English proof (translation)
Introduce `E _ _ _ n m J φ P ε F hφ hP hJ hF hsp`. Take `⟨hmono, h0, hm, hd⟩` from `hF`. Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z` using `fun z => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]`.

Establish `hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z` using `fun z => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `htop : locFlag φ P F m = ⊤`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Rewrite using `[← hinv z]`.

Use `mulVec_mem_of_span φ _ _ _ ?_ (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))` and prove the remaining obligations. Introduce `y _`. Take `⟨c, hc, hy⟩` from `exists_smul_mem _ hsp y`. Conclude with `mem_locFlag_of_smul φ P F m hc hy`. Use `⟨⟨?_, ?_, ?_, ?_⟩, htop⟩` and prove the remaining obligations.

Introduce `a b hab`. Conclude with `Submodule.span_mono (Set.image_mono (hmono hab))`. Unfold `locFlag`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Rewrite `hy` using `[h0]`. Establish `: y = 0` using `by simpa using hy`. Substitute `this` using the available equality. Establish `e : (fun l => φ ((0 : Fin n → E) l)) = 0` using `by funext l; simp`. Simplify using `only [e, Matrix.mulVec_zero]`.

Introduce `b hb`. Unfold `locFlag`. Rewrite using `[hm b hb]`. Introduce `b hb z`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Use `⟨by rw [htop]; trivial, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]`. Consider the case `mem z hz`. Take `⟨y, hy, rfl⟩` from `hz`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]`. Consider the case `mem a ha`. Take `⟨v, hv, rfl⟩` from `ha`. Rewrite using `[form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]`.

Introduce and unpack `⟨-, hz⟩`. Rewrite using `[← hinv z]`. Set `f : (Fin n → E) → Module.Dual E (Fin n → E)` to `fun x => { toFun := fun y => star x ⬝ᵥ (J *ᵥ y) map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add] map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }`. Establish `hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y)` using `fun _ _ => rfl`. Use `mulVec_mem_of_span φ _ _ _ ?_ (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)` and prove the remaining obligations.

Introduce `y hy`. Take `⟨c, hc, hcy⟩` from `exists_smul_mem _ hsp y`. Use `mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)` and prove the remaining obligations. Establish `h1 : star x ⬝ᵥ (J *ᵥ y) = 0` using `hy (f x) ⟨x, hx, rfl⟩`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h1` using `hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)`. Rewrite `h1` using `[form_frame hP hJ]`. Rewrite using `[← h1]`. Generalize the expression as in `P *ᵥ z = u`.

Simplify using `only [hf, Matrix.mulVec_single_one]`. Simplify using `only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum, Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem locDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  intro E _ _ _ n m J φ P ε F hφ hP hJ hF hsp
  classical
  obtain ⟨hmono, h0, hm, hd⟩ := hF
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have htop : locFlag φ P F m = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [← hinv z]
    refine mulVec_mem_of_span φ _ _ _ ?_
      (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))
    intro y _
    obtain ⟨c, hc, hy⟩ := exists_smul_mem _ hsp y
    exact mem_locFlag_of_smul φ P F m hc hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, htop⟩
  · intro a b hab
    exact Submodule.span_mono (Set.image_mono (hmono hab))
  · unfold locFlag
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have : y = 0 := by simpa using hy
    subst this
    have e : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    simp only [e, Matrix.mulVec_zero]
  · intro b hb
    unfold locFlag
    rw [hm b hb]
  · intro b hb z
    constructor
    · intro hz
      refine ⟨by rw [htop]; trivial, fun x hx => ?_⟩
      induction hz using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        induction hx using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]
        | mem a ha =>
          obtain ⟨v, hv, rfl⟩ := ha
          rw [form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]
    · rintro ⟨-, hz⟩
      rw [← hinv z]
      let f : (Fin n → E) → Module.Dual E (Fin n → E) := fun x =>
        { toFun := fun y => star x ⬝ᵥ (J *ᵥ y)
          map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
      have hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y) := fun _ _ => rfl
      refine mulVec_mem_of_span φ _ _ _ ?_
        (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)
      · intro y hy
        obtain ⟨c, hc, hcy⟩ := exists_smul_mem _ hsp y
        refine mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)
        have h1 : star x ⬝ᵥ (J *ᵥ y) = 0 := hy (f x) ⟨x, hx, rfl⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)
        rw [form_frame hP hJ] at h1
        rw [← h1]
        generalize P *ᵥ z = u
        simp only [hf, Matrix.mulVec_single_one]
        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum,
          Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]
        rw [Finset.sum_comm]
        rfl

end GlobalTheory.LocDual
