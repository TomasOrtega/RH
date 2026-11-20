import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Lat
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

omit [NumberField E] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v, hv, Matrix.det_transpose (Matrix.of v)⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v, hv, (Matrix.det_transpose v).symm⟩`.
-/
theorem mem_detSet (M : Submodule (𝓞 E) (Fin n → E)) (d : E) :
    d ∈ detSet M ↔ ∃ v : Matrix (Fin n) (Fin n) E, (∀ i, v i ∈ M) ∧ d = v.det := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, Matrix.det_transpose (Matrix.of v)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (Matrix.det_transpose v).symm⟩

def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)

omit [NumberField E] in
/- English proof (translation)
The claim follows from `Submodule.subset_span ((mem_detSet M _).2 ⟨v, hv, rfl⟩)`.
-/
theorem det_mem {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M) :
    v.det ∈ detSpan M := Submodule.subset_span ((mem_detSet M _).2 ⟨v, hv, rfl⟩)

omit [NumberField E] in
/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.updateRow_self]` and apply the resulting hypothesis. Rewrite using `[Matrix.updateRow_ne h]`. Conclude with `hv i`.
-/
theorem row_update_mem {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M)
    (j : Fin n) (m : Fin n → E) (hm : m ∈ M) (i : Fin n) : v.updateRow j m i ∈ M := by
  by_cases h : i = j
  · subst h; rwa [Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne h]; exact hv i

omit [NumberField E] in
/- English proof (translation)
Establish `dec : ∀ x ∈ M' ⊔ Submodule.span (𝓞 E) {m}, ∃ v ∈ M', ∃ t : 𝓞 E, x = v + t • m`. Introduce `x hx`. Take `⟨v, hv, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Conclude with `⟨v, hv, t, rfl⟩`.

Establish `key : ∀ s : Finset (Fin n), ∀ w : Matrix (Fin n) (Fin n) E, (∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) → (∀ i, i ∉ s → w i ∈ M') → a • w.det ∈ detSpan M'`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro w _ h; exact Submodule.smul_mem _ _ (det_mem w fun i => h i (by simp))`. Consider the case `insert j s hj ih`.

Introduce `w hw h`. Use `choose v hv t ht using fun i => dec _ (hw i)`. Establish `e1 : w.det = (w.updateRow j (v j)).det + (t j : E) * (w.updateRow j m).det` using `by conv_lhs => rw [← Matrix.updateRow_eq_self w j, ht j]`. Rewrite using `[Matrix.det_updateRow_add, ← Matrix.det_updateRow_smul]`. Both sides reduce to the same expression.

Establish `e2 : (w.updateRow j m).det = ((Matrix.of v).updateRow j m).det`. Apply `Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = j then 0 else (t i : E)) j (by simp)` to reduce the goal to its premises. Introduce `i k`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `only [Matrix.updateRow_ne hi, hi, if_false, Matrix.updateRow_self, Matrix.of_apply]`. Rewrite using `[ht i]`. Both sides reduce to the same expression. Rewrite using `[e1, smul_add]`.

Use `Submodule.add_mem _ (ih _ (row_update_mem w hw j _ (Submodule.mem_sup_left (hv j))) ?_) ?_` and prove the remaining obligations. Introduce `i hi`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.updateRow_self]`.

Conclude with `hv i`. Rewrite using `[Matrix.updateRow_ne hij]; exact h i (by simp [hij, hi])`. Establish `e3 : a • ((t j : E) * (w.updateRow j m).det) = ((Matrix.of v).updateRow j (t j • a • m)).det`. Rewrite using `[e2]`. Express the relevant statement in the definitionally equal form `(a : E) * _ = ((Matrix.of v).updateRow j ((t j : E) • (a : E) • m)).det`.

Rewrite using `[Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `det_mem _ (row_update_mem _ hv j _ (M'.smul_mem _ ha))`. Conclude with `key Finset.univ w hw (fun i hi => absurd (Finset.mem_univ i) hi)`.
-/
theorem smul_det_mem (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) (a : 𝓞 E) (ha : a • m ∈ M')
    (w : Matrix (Fin n) (Fin n) E) (hw : ∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) :
    a • w.det ∈ detSpan M' := by
  classical
  have dec : ∀ x ∈ M' ⊔ Submodule.span (𝓞 E) {m}, ∃ v ∈ M', ∃ t : 𝓞 E, x = v + t • m := by
    intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨v, hv, t, rfl⟩
  have key : ∀ s : Finset (Fin n), ∀ w : Matrix (Fin n) (Fin n) E,
      (∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) → (∀ i, i ∉ s → w i ∈ M') → a • w.det ∈ detSpan M' := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ h; exact Submodule.smul_mem _ _ (det_mem w fun i => h i (by simp))
    | insert j s hj ih =>
      intro w hw h
      choose v hv t ht using fun i => dec _ (hw i)
      have e1 : w.det = (w.updateRow j (v j)).det + (t j : E) * (w.updateRow j m).det := by
        conv_lhs => rw [← Matrix.updateRow_eq_self w j, ht j]
        rw [Matrix.det_updateRow_add, ← Matrix.det_updateRow_smul]
        rfl
      have e2 : (w.updateRow j m).det = ((Matrix.of v).updateRow j m).det := by
        apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = j then 0 else (t i : E)) j (by simp)
        intro i k
        by_cases hi : i = j
        · subst hi; simp
        · simp only [Matrix.updateRow_ne hi, hi, if_false, Matrix.updateRow_self, Matrix.of_apply]
          rw [ht i]; rfl
      rw [e1, smul_add]
      refine Submodule.add_mem _ (ih _ (row_update_mem w hw j _ (Submodule.mem_sup_left (hv j))) ?_) ?_
      · intro i hi
        by_cases hij : i = j
        · subst hij; rw [Matrix.updateRow_self]; exact hv i
        · rw [Matrix.updateRow_ne hij]; exact h i (by simp [hij, hi])
      · have e3 : a • ((t j : E) * (w.updateRow j m).det) =
            ((Matrix.of v).updateRow j (t j • a • m)).det := by
          rw [e2]
          change (a : E) * _ = ((Matrix.of v).updateRow j ((t j : E) • (a : E) • m)).det
          rw [Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]; ring
        rw [e3]
        exact det_mem _ (row_update_mem _ hv j _ (M'.smul_mem _ ha))
  exact key Finset.univ w hw (fun i hi => absurd (Finset.mem_univ i) hi)

omit [NumberField E] in
/- English proof (translation)
Establish `h` using `Matrix.mulVec_cramer v.transpose m`. Rewrite `h` using `[Matrix.det_transpose]`. Rewrite using `[← h]`. Use extensionality with `k`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.cramer_transpose_apply, Finset.sum_apply, mul_comm]`.
-/
theorem cramer_rows (v : Matrix (Fin n) (Fin n) E) (m : Fin n → E) :
    v.det • m = ∑ i, (v.updateRow i m).det • v i := by
  have h := Matrix.mulVec_cramer v.transpose m
  rw [Matrix.det_transpose] at h
  rw [← h]
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.cramer_transpose_apply, Finset.sum_apply, mul_comm]

omit [NumberField E] in
/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `⟨v, fun i => h (hv i), rfl⟩`.
-/
theorem detSpan_mono {M' M : Submodule (𝓞 E) (Fin n → E)} (h : M' ≤ M) : detSpan M' ≤ detSpan M := by
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, fun i => h (hv i), rfl⟩

def Bdd (M : Submodule (𝓞 E) (Fin n → E)) : Prop := ∃ k : 𝓞 E, k ≠ 0 ∧ ∀ v ∈ M, k • v ∈ stdLat E n

omit [NumberField E] in
/- English proof (translation)
Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]`.
-/
theorem mem_std (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

omit [NumberField E] in
/- English proof (translation)
Take `⟨k, hk, h⟩` from `h`. Apply `FractionalIdeal.isFractional_span_iff.2` to reduce the goal to its premises. Use `⟨k ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hk), ?_⟩` and prove the remaining obligations. Introduce `d hd`. Take `⟨v, hv, rfl⟩` from `(mem_detSet M d).1 hd`.

Use `choose b hb using fun i => (mem_std _).1 (h _ (hv i))`. Use `⟨(Matrix.of b).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Establish `: (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = (k : E) • v`. Use extensionality with `i j`.

Conclude with `hb i j`. Rewrite using `[this, Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]`.
-/
theorem frac_of_bdd {M : Submodule (𝓞 E) (Fin n → E)} (h : Bdd M) :
    IsFractional (nonZeroDivisors (𝓞 E)) (detSpan M) := by
  obtain ⟨k, hk, h⟩ := h
  apply FractionalIdeal.isFractional_span_iff.2
  refine ⟨k ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hk), ?_⟩
  intro d hd
  obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
  choose b hb using fun i => (mem_std _).1 (h _ (hv i))
  refine ⟨(Matrix.of b).det, ?_⟩
  rw [RingHom.map_det]
  have : (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = (k : E) • v := by
    ext i j
    exact hb i j
  rw [this, Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]

/- English proof (translation)
Use `set M := M' ⊔ Submodule.span (𝓞 E) {m} with hM`. Establish `hle : M' ≤ M` using `le_sup_left`. Establish `hm : m ∈ M` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)`. Apply `le_antisymm` to reduce the goal to its premises. Distinguish the cases in `h0 : detSpan M = ⊥`.

Conclude with `(detSpan_mono hle).trans (h0.le.trans bot_le)`. Set `I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E` to `⟨detSpan M, frac_of_bdd hb⟩`. Establish `hI : I ≠ 0` using `fun h => h0 (by`. Use `congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E)) h` as an intermediate fact. Simplify using `only [FractionalIdeal.coe_zero] at this`.

Conclude with `this)`. Establish `h1 : detSpan M * ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = 1`. Use `congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E)) (mul_inv_cancel₀ hI)` as an intermediate fact. Simplify using `only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at this`. Conclude with `this`.

Generalize the expression as in `((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = J at h1`. Establish `hint : ∀ x ∈ detSpan M, ∀ y ∈ J, ∃ b : 𝓞 E, (b : E) = x * y`. Introduce `x hx y hy`. Use `Submodule.mul_mem_mul hx hy` as an intermediate fact. Rewrite `this` using `[h1]`.

Conclude with `Submodule.mem_one.1 this`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce `d hd`. Take `⟨v, hv, rfl⟩` from `(mem_detSet M' d).1 hd`. Establish `h1m : (1 : E) ∈ detSpan M * J` using `by rw [h1]; exact Submodule.mem_one.2 ⟨1, map_one _⟩`.

Establish `: ∀ z ∈ detSpan M * J, v.det * z ∈ (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) • detSpan M`. Introduce `z hz`. Use `Submodule.mul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `x hx y hy`. Take `⟨b, hb⟩` from `hint _ (det_mem v fun i => hle (hv i)) y hy`.

Establish `e : v.det * (x * y) = b • x`. Express the relevant statement in the definitionally equal form `_ = (b : E) * x`. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Submodule.smul_mem_smul ?_ hx` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `b • m ∈ M'`. Establish `e2 : b • m = y • (v.det • m)`. Express the relevant statement in the definitionally equal form `(b : E) • m = _`. Rewrite using `[hb, smul_smul, mul_comm]`.

Rewrite using `[e2, cramer_rows, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨b', hb'⟩` from `hint _ (det_mem _ (row_update_mem v (fun i => hle (hv i)) i m hm)) y hy`. Rewrite using `[smul_smul, mul_comm, ← hb']`. Conclude with `M'.smul_mem b' (hv i)`.

Introduce `x y hx hy`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Simplify using `using this 1 h1m`. Apply `Submodule.smul_le.2` to reduce the goal to its premises.

Introduce `a ha x hx`. Establish `: detSpan M ≤ (detSpan M').comap (LinearMap.lsmul (𝓞 E) E a)`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce `d hd`. Take `⟨v, hv, rfl⟩` from `(mem_detSet M d).1 hd`.

Conclude with `smul_det_mem M' m a ha v hv`. Conclude with `this hx`.
-/
theorem detSpan_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E)
    (hb : Bdd (M' ⊔ Submodule.span (𝓞 E) {m})) :
    detSpan M' = (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) •
      detSpan (M' ⊔ Submodule.span (𝓞 E) {m}) := by
  set M := M' ⊔ Submodule.span (𝓞 E) {m} with hM
  have hle : M' ≤ M := le_sup_left
  have hm : m ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)
  apply le_antisymm
  · by_cases h0 : detSpan M = ⊥
    · exact (detSpan_mono hle).trans (h0.le.trans bot_le)
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨detSpan M, frac_of_bdd hb⟩
    have hI : I ≠ 0 := fun h => h0 (by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E)) h
      simp only [FractionalIdeal.coe_zero] at this
      exact this)
    have h1 : detSpan M * ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = 1 := by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E))
        (mul_inv_cancel₀ hI)
      simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at this
      exact this
    generalize ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = J at h1
    have hint : ∀ x ∈ detSpan M, ∀ y ∈ J, ∃ b : 𝓞 E, (b : E) = x * y := by
      intro x hx y hy
      have := Submodule.mul_mem_mul hx hy
      rw [h1] at this
      exact Submodule.mem_one.1 this
    apply Submodule.span_le.2
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (mem_detSet M' d).1 hd
    have h1m : (1 : E) ∈ detSpan M * J := by rw [h1]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have : ∀ z ∈ detSpan M * J, v.det * z ∈
        (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) • detSpan M := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro x hx y hy
        obtain ⟨b, hb⟩ := hint _ (det_mem v fun i => hle (hv i)) y hy
        have e : v.det * (x * y) = b • x := by
          change _ = (b : E) * x
          rw [hb]; ring
        rw [e]
        refine Submodule.smul_mem_smul ?_ hx
        change b • m ∈ M'
        have e2 : b • m = y • (v.det • m) := by
          change (b : E) • m = _
          rw [hb, smul_smul, mul_comm]
        rw [e2, cramer_rows, Finset.smul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨b', hb'⟩ := hint _ (det_mem _ (row_update_mem v (fun i => hle (hv i)) i m hm)) y hy
        rw [smul_smul, mul_comm, ← hb']
        exact M'.smul_mem b' (hv i)
      · intro x y hx hy
        rw [mul_add]; exact Submodule.add_mem _ hx hy
    simpa using this 1 h1m
  · apply Submodule.smul_le.2
    intro a ha x hx
    have : detSpan M ≤ (detSpan M').comap (LinearMap.lsmul (𝓞 E) E a) := by
      apply Submodule.span_le.2
      intro d hd
      obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
      exact smul_det_mem M' m a ha v hv
    exact this hx

/- English proof (translation)
Rewrite using `[Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, LinearMap.span_singleton_eq_range, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `AddSubgroup.index_comap M'.toAddSubgroup (LinearMap.toSpanSingleton (𝓞 E) _ m).toAddMonoidHom`.
-/
theorem index_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) :
    Ideal.absNorm (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
      M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 E) {m}).toAddSubgroup := by
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, LinearMap.span_singleton_eq_range,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.index_comap M'.toAddSubgroup (LinearMap.toSpanSingleton (𝓞 E) _ m).toAddMonoidHom

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧ Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _; exact ⟨⊤, by simp, by simp, by simp⟩`. Consider the case `insert m s _ ih`.

Introduce `hs`. Take `⟨𝔞, h0, h1, h2⟩` from `ih fun x hx => hs x (Finset.mem_insert_of_mem hx)`. Use `set N := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN`. Establish `hm : m ∈ M` using `hs m (Finset.mem_insert_self _ _)`. Establish `e : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) = N ⊔ Submodule.span (𝓞 E) {m}`.

Rewrite using `[Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]`. Establish `hNM : N ⊔ Submodule.span (𝓞 E) {m} ≤ M`. Rewrite using `[← e]`. Conclude with `sup_le hle (Submodule.span_le.2 fun x hx => hs x hx)`. Establish `hb' : Bdd (N ⊔ Submodule.span (𝓞 E) {m})`.

Take `⟨k, hk, h⟩` from `hb`. Conclude with `⟨k, hk, fun v hv => h v (hNM hv)⟩`. Rewrite using `[e]`. Use `⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `mul_ne_zero h0 ?_` and prove the remaining obligations.

Take `⟨a, ha, ham⟩` from `ht m hm`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : M' ≤ N) ham, ha⟩`. Rewrite using `[h1, Submodule.mul_smul, ← detSpan_cyclic N m hb']`. Rewrite using `[map_mul, h2, index_cyclic]`. Conclude with `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left) (Submodule.toAddSubgroup_mono le_sup_left)`.

Establish `hfg : M.FG`. Take `⟨k, hk, h⟩` from `hb`. Establish `hs : (stdLat E n).FG` using `Submodule.fg_pi fun _ => by`. Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`.

Apply `Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k) (fun x y hxy => smul_right_injective _ hk hxy)` to reduce the goal to its premises. Conclude with `hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)`. Take `⟨s, rfl⟩` from `hfg`. Use `key s fun x hx => Submodule.subset_span hx` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 hle]`. Then use the resulting hypothesis.
-/
theorem exists_index_ideal (M' M : Submodule (𝓞 E) (Fin n → E)) (hle : M' ≤ M) (hb : Bdd M)
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan M ∧
      Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex
          (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have e : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNM : N ⊔ Submodule.span (𝓞 E) {m} ≤ M := by
        rw [← e]
        exact sup_le hle (Submodule.span_le.2 fun x hx => hs x hx)
      have hb' : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) := by
        obtain ⟨k, hk, h⟩ := hb
        exact ⟨k, hk, fun v hv => h v (hNM hv)⟩
      rw [e]
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : M' ≤ N) ham, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb']
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hb
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 hle] at this

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v`. Conclude with `⟨d, nonZeroDivisors.ne_zero d.2, (mem_std _).2 fun j => hd j⟩`.
-/
theorem exists_smul_std (v : Fin n → E) : ∃ a : 𝓞 E, a ≠ 0 ∧ a • v ∈ stdLat E n := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v
  exact ⟨d, nonZeroDivisors.ne_zero d.2, (mem_std _).2 fun j => hd j⟩

/- English proof (translation)
Establish `hfull : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Set `u : Fin n → E` to `fun j => IsCMField.complexConj E (f (Pi.single j 1))`. Establish `hu : ∀ w, ∑ j, IsCMField.complexConj E (u j) * w j = f w`.

Introduce `w`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f w]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [u, IsCMField.complexConj_apply_apply, smul_eq_mul, mul_comm]`. Use `congr 2`.

Use extensionality with `k`. Simplify using `[Pi.single_apply, eq_comm]`. Establish `hk : ∀ w ∈ Λ.La, f w = 0` using `fun w hw => hf (Submodule.subset_span hw)`. Establish `huL : u ∈ Λ.La` using `(h u).2 fun w hw => by rw [hu, hk w hw]; exact zero_mem _`. Establish `h0` using `hu u`.

Rewrite `h0` using `[hk u huL]`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h1` using `congrArg φ h0`. Simplify using `only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero, ← Complex.normSq_eq_conj_mul_self] at h1`. Establish `h2 : ∑ j, Complex.normSq (φ (u j)) = 0` using `by exact_mod_cast h1`.

Establish `h3 : ∀ j, u j = 0` using `fun j => by`. Use `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)` as an intermediate fact. Simplify using `using this`. Apply `hf0` to reduce the goal to its premises. Use extensionality with `w`.

Simplify using `[← hu, h3]`. Establish `hmul : ∀ x : Fin n → E, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ.La`. Introduce `x`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (Λ.La : Set (Fin n → E)) x (by rw [hfull]; trivial)`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨t, nonZeroDivisors.ne_zero t.2, ht⟩`. Use `choose a ha0 ha using fun j : Fin n => hmul (Pi.single j 1)`. Establish `hA : ∀ j, (∏ i, a i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La`. Introduce `j`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul]`.

Conclude with `Λ.La.smul_mem _ (ha j)`. Use `⟨IsCMField.ringOfIntegersComplexConj E (∏ i, a i), ?_, fun v hv => (mem_std _).2 fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => ha0 i`. Take `⟨b, hb⟩` from `(h _).1 (hA j) v hv`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]`. Express the relevant statement in the definitionally equal form `_ = ((IsCMField.ringOfIntegersComplexConj E (∏ i, a i) : 𝓞 E) : E) * v j`. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj]`. Simplify `hb` using `[Algebra.smul_def]`.
-/
theorem bdd_of_unimod [IsCMField E] (Λ : GenLat E n) (h : Λ.Unimod) : Bdd Λ.La := by
  classical
  have hfull : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let u : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
    have hu : ∀ w, ∑ j, IsCMField.complexConj E (u j) * w j = f w := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [u, IsCMField.complexConj_apply_apply, smul_eq_mul, mul_comm]
      congr 2
      ext k; simp [Pi.single_apply, eq_comm]
    have hk : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
    have huL : u ∈ Λ.La := (h u).2 fun w hw => by rw [hu, hk w hw]; exact zero_mem _
    have h0 := hu u
    rw [hk u huL] at h0
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg φ h0
    simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
      ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ∑ j, Complex.normSq (φ (u j)) = 0 := by exact_mod_cast h1
    have h3 : ∀ j, u j = 0 := fun j => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)
      simpa using this
    apply hf0
    ext w
    simp [← hu, h3]
  have hmul : ∀ x : Fin n → E, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ.La := by
    intro x
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E
      (Λ.La : Set (Fin n → E)) x (by rw [hfull]; trivial)
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  choose a ha0 ha using fun j : Fin n => hmul (Pi.single j 1)
  have hA : ∀ j, (∏ i, a i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := by
    intro j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul]
    exact Λ.La.smul_mem _ (ha j)
  refine ⟨IsCMField.ringOfIntegersComplexConj E (∏ i, a i), ?_, fun v hv => (mem_std _).2 fun j => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => ha0 i
  · obtain ⟨b, hb⟩ := (h _).1 (hA j) v hv
    refine ⟨b, ?_⟩
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at hb
    change _ = ((IsCMField.ringOfIntegersComplexConj E (∏ i, a i) : 𝓞 E) : E) * v j
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    simpa [Algebra.smul_def] using hb

end Lat

section Push
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `φ ((b : E) * x) = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem map_smul_int (b : 𝓞 E) (x : E) : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
  change φ ((b : E) * x) = _
  rw [map_mul]; rfl

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul b x _ hx => rw [map_smul_int]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem span_image_span (S : Set E) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 E) S : Set E)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [map_smul_int]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha y hy`.

Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `Submodule.mul_mem_mul (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨y, hy, rfl⟩)`. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Rewrite using `[Submodule.span_mul_span]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨a, ha, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨a • y, Submodule.smul_mem_smul ha hy, by rw [Algebra.smul_def, map_mul]; rfl⟩`.
-/
theorem span_image_smul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) :
    Submodule.span (𝓞 F) (φ '' ((𝔞 • N : Submodule (𝓞 E) E) : Set E)) =
      Submodule.span (𝓞 F) ((φ.comp (algebraMap (𝓞 E) E)) '' (𝔞 : Set (𝓞 E))) *
        Submodule.span (𝓞 F) (φ '' (N : Set E)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      rw [Algebra.smul_def, map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨y, hy, rfl⟩)
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, Submodule.smul_mem_smul ha hy, by rw [Algebra.smul_def, map_mul]; rfl⟩

end Push

/- English proof (translation)
Introduce `E _ _ _ H Dw l c n bad hK Λ hU _`. Take `⟨𝔞, h0, h1, h2⟩` from `exists_index_ideal Λ.Ln Λ.La inf_le_left (bdd_of_unimod Λ hU) (fun m hm => by`. Take `⟨a, ha, h⟩` from `exists_smul_std m`. Conclude with `⟨a, ha, Λ.La.smul_mem a hm, h⟩)`. Take `⟨β, hβ0, hβ1, hβ2⟩` from `hK 𝔞 h0`.

Use `⟨β, hβ0, ?_, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : ∀ τ, idealAt c Λ.Ln τ = Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c Λ.La τ`. Introduce `τ`. Unfold `idealAt`. Rewrite using `[← span_image_span (embF c τ) (detSet Λ.Ln), ← span_image_span (embF c τ) (detSet Λ.La)]`.

Use `span_image_smul (embF c τ) 𝔞 (detSpan Λ.La)` as an intermediate fact. Rewrite `this` using `[← h1]`. Conclude with `this`. Unfold `BetaIs`. Simplify using `only [e, mul_pow, Finset.prod_mul_distrib, hβ1]`.

Rewrite using `[hβ2, h2]`. Both sides reduce to the same expression.
-/
theorem betaExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (n bad : ℕ), Formalism.L2.Pj.BetaExists (Dw := Dw) c n bad := by
  intro E _ _ _ H Dw l c n bad hK Λ hU _
  obtain ⟨𝔞, h0, h1, h2⟩ := exists_index_ideal Λ.Ln Λ.La inf_le_left (bdd_of_unimod Λ hU) (fun m hm => by
    obtain ⟨a, ha, h⟩ := exists_smul_std m
    exact ⟨a, ha, Λ.La.smul_mem a hm, h⟩)
  obtain ⟨β, hβ0, hβ1, hβ2⟩ := hK 𝔞 h0
  refine ⟨β, hβ0, ?_, fun σ => ?_⟩
  · have e : ∀ τ, idealAt c Λ.Ln τ =
        Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c Λ.La τ := by
      intro τ
      unfold idealAt
      rw [← span_image_span (embF c τ) (detSet Λ.Ln), ← span_image_span (embF c τ) (detSet Λ.La)]
      have := span_image_smul (embF c τ) 𝔞 (detSpan Λ.La)
      rw [← h1] at this
      exact this
    unfold BetaIs
    simp only [e, mul_pow, Finset.prod_mul_distrib, hβ1]
  · rw [hβ2, h2]; rfl

end GlobalTheory.BetaEx
