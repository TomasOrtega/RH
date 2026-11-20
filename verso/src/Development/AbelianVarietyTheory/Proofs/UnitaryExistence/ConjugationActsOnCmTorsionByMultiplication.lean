import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Acts

/- English proof (translation)
Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `f0 : f (0, 0) = 0` using `by simp [hf]`. Establish `f1 : f (1, 0) = 1` using `by simp [hf]`. Establish `h0 : R 0 0`. Take `⟨z', h⟩` from `tot 0`.

Take `⟨a, ha⟩` from `(iff _ _ _ _ (add _ _ _ _ h h) h).1 ⟨(0, 0), by simp [f0]⟩`. Conclude with `rsp _ _ _ h ⟨a, by rw [← ha]; ring⟩`. Establish `neg : ∀ z z', R z z' → R (-z) (-z')`. Introduce `z z' h`. Take `⟨y, hy⟩` from `tot (-z)`.

Take `⟨a, ha⟩` from `(iff _ _ _ _ (add _ _ _ _ h hy) h0).1 ⟨(0, 0), by simp [f0]⟩`. Conclude with `rsp _ _ _ hy ⟨a, by rw [← ha]; ring⟩`. Establish `int : ∀ (m : ℤ) z z', R z z' → R (m * z) (m * z')`. Introduce `m z z' h`. Proceed by induction on `m using Int.induction_on with`.

Consider the case `zero => simpa using h0`. Consider the case `succ k ih`. Use `add _ _ _ _ ih h` as an intermediate fact. Apply the tactic sequence `convert this using 1 <;> push_cast <;> ring`. Consider the case `pred k ih`.

Use `add _ _ _ _ ih (neg _ _ h)` as an intermediate fact. Apply the tactic sequence `convert this using 1 <;> push_cast <;> ring`. Establish `mul : ∀ a z z', R z z' → R (f a * z) (f a * z')`. Introduce `a z z' h`. Use `add _ _ _ _ (int a.1 _ _ h) (int a.2 _ _ (om _ _ h))` as an intermediate fact.

Apply the tactic sequence `convert this using 1 <;> rw [hf] <;> ring`. Prove the components needed by the constructor for the conclusion. Take `⟨z', h⟩` from `tot (1 / n)`. Take `⟨s, hs⟩` from `(iff _ _ _ _ (int n _ _ h) h0).1 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩`. Use `⟨s, fun a => ?_⟩` and prove the remaining obligations.

Use `mul a _ _ h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hs]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `s hs`. Take `⟨z, h⟩` from `sur (1 / n)`. Take `⟨s', hs'⟩` from `(iff _ _ _ _ (int n _ _ h) h0).2 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩`.

Take `⟨a, ha⟩` from `(iff _ _ _ _ (hs s') h).1 ⟨(0, 0), by rw [f0, ← hs']; push_cast; field_simp; ring⟩`. Use `⟨s', a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem corr (ω : ℂ) (f : ℤ × ℤ → ℂ) (hf : ∀ s, f s = s.1 + s.2 * ω) (R : ℂ → ℂ → Prop)
    (tot : ∀ z, ∃ z', R z z') (sur : ∀ z', ∃ z, R z z')
    (add : ∀ z z' y y', R z z' → R y y' → R (z + y) (z' + y'))
    (om : ∀ z z', R z z' → R (ω * z) (ω * z'))
    (iff : ∀ z z' y y', R z z' → R y y' → ((∃ a, z - y = f a) ↔ ∃ a, z' - y' = f a))
    (rsp : ∀ z z' y', R z z' → (∃ a, z' - y' = f a) → R z y') (n : ℕ) (hn : 0 < n) :
    (∃ s, ∀ a, R (f a / n) (f s * f a / n)) ∧
      ∀ s, (∀ a, R (f a / n) (f s * f a / n)) → ∃ s' a, f s' * f s = 1 + n * f a := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have f0 : f (0, 0) = 0 := by simp [hf]
  have f1 : f (1, 0) = 1 := by simp [hf]
  have h0 : R 0 0 := by
    obtain ⟨z', h⟩ := tot 0
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h h) h).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ h ⟨a, by rw [← ha]; ring⟩
  have neg : ∀ z z', R z z' → R (-z) (-z') := by
    intro z z' h
    obtain ⟨y, hy⟩ := tot (-z)
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h hy) h0).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ hy ⟨a, by rw [← ha]; ring⟩
  have int : ∀ (m : ℤ) z z', R z z' → R (m * z) (m * z') := by
    intro m z z' h
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ k ih =>
      have := add _ _ _ _ ih h
      convert this using 1 <;> push_cast <;> ring
    | pred k ih =>
      have := add _ _ _ _ ih (neg _ _ h)
      convert this using 1 <;> push_cast <;> ring
  have mul : ∀ a z z', R z z' → R (f a * z) (f a * z') := by
    intro a z z' h
    have := add _ _ _ _ (int a.1 _ _ h) (int a.2 _ _ (om _ _ h))
    convert this using 1 <;> rw [hf] <;> ring
  constructor
  · obtain ⟨z', h⟩ := tot (1 / n)
    obtain ⟨s, hs⟩ := (iff _ _ _ _ (int n _ _ h) h0).1 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    refine ⟨s, fun a => ?_⟩
    have := mul a _ _ h
    convert this using 1
    · ring
    · rw [← hs]; push_cast; field_simp; ring
  · intro s hs
    obtain ⟨z, h⟩ := sur (1 / n)
    obtain ⟨s', hs'⟩ := (iff _ _ _ _ (int n _ _ h) h0).2 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (hs s') h).1 ⟨(0, 0), by rw [f0, ← hs']; push_cast; field_simp; ring⟩
    refine ⟨s', a, ?_⟩
    rw [← ha]; field_simp; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem spMap_symm (τ : ℂ ≃+* ℂ) : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x; simp

/- English proof (translation)
The claim follows from `Over.w (C.u.ex fun _ => C.c * z)`.
-/
theorem pt_over (C : Curve H) (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * z)

/- English proof (translation)
Establish `e : ∀ a b, C.pt (a + b) = (C.u.ex (fun _ => C.c * a) * C.u.ex (fun _ => C.c * b)).left`. Introduce `a b`. Rewrite using `[← C.u.ex_add, Curve.pt]`. Use `congr 2`. Use function extensionality and compare the values at `_`.

Simplify using `[mul_add]`. Set `U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ 𝟙_ (Over (Sp ℂ))` to `Over.homMk f (by simp)`. Use `h.2 _ (C.u.ex fun _ => C.c * z') (C.u.ex fun _ => C.c * y') (U ≫ C.u.ex fun _ => C.c * z) (U ≫ C.u.ex fun _ => C.c * y) hz.symm hy.symm` as an intermediate fact. Rewrite `this` using `[← MonObj.comp_mul]`. Rewrite using `[e, e]`.

Conclude with `this.symm`.
-/
theorem pt_add (C : Curve H) {f : Sp ℂ ⟶ Sp ℂ} {io : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A f io) {z z' y y' : ℂ} (hz : C.pt z' ≫ io = f ≫ C.pt z)
    (hy : C.pt y' ≫ io = f ≫ C.pt y) : C.pt (z' + y') ≫ io = f ≫ C.pt (z + y) := by
  have e : ∀ a b, C.pt (a + b) = (C.u.ex (fun _ => C.c * a) * C.u.ex (fun _ => C.c * b)).left := by
    intro a b
    rw [← C.u.ex_add, Curve.pt]
    congr 2
    funext _; simp [mul_add]
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk f (by simp)
  have := h.2 _ (C.u.ex fun _ => C.c * z') (C.u.ex fun _ => C.c * y') (U ≫ C.u.ex fun _ => C.c * z)
    (U ≫ C.u.ex fun _ => C.c * y) hz.symm hy.symm
  rw [← MonObj.comp_mul] at this
  rw [e, e]
  exact this.symm

/- English proof (translation)
Introduce `E _ _ _ H C τ hτ io h n hn`. Take `⟨W, -, hW, hker, hon, hcomm⟩` from `GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C`. Establish `hc` using `hcomm τ hτ io h`. Establish `key` using `corr (wC H (0, 1)) (wC H) (fun s => by simp [wC]) (fun z z' => C.pt z' ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z) (fun z => by`. Establish `w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z) ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ)`.

Rewrite using `[Category.assoc, pt_over]`. Simplify using the standard rewrite rules. Take `⟨z', hz⟩` from `hon (h.1.lift _ _ w) (h.1.lift_snd _ _ w)`. Conclude with `⟨z', by rw [hz, h.1.lift_fst]⟩)`. Use the proof step `(fun z' => by`.

Take `⟨z, hz⟩` from `hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z' ≫ io) (by`. Rewrite using `[Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z'), pt_over, Category.id_comp, spMap_symm])`. Use `⟨z, ?_⟩` and prove the remaining obligations. Use `spMap_symm τ.symm` as an intermediate fact. Rewrite `this` using `[RingEquiv.symm_symm]`.

Rewrite using `[hz, ← Category.assoc, this, Category.id_comp])`. Use the proof step `(fun z z' y y' hz hy => pt_add C h hz hy)`. Use the proof step `(fun z z' hz => by`. Rewrite using `[← hW, ← hW, Category.assoc, hc, ← Category.assoc, hz, Category.assoc])`. Use the proof step `(fun z z' y y' hz hy => by`.

Rewrite using `[← hker, ← hker]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hz, hy, e]`.

Rewrite using `[pt_over, pt_over]`. Introduce `e`. Establish `e' : spMap (τ : ℂ →+* ℂ) ≫ C.pt z = spMap (τ : ℂ →+* ℂ) ≫ C.pt y` using `by rw [← hz, ← hy, e]`. Use `congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) e'` as an intermediate fact. Simplify `this)` using `only [← Category.assoc, spMap_symm, Category.id_comp]`.

Use the proof step `(fun z z' y' hz e => by rw [← (hker _ _).2 e]; exact hz) n hn`. Use `⟨key.1.imp fun s hs => ⟨h, hs⟩, fun s hs => ⟨key.2 s hs.2, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `m ⟨k, rfl⟩`. Use `⟨h, fun a => ?_⟩` and prove the remaining obligations. Establish `hk : (k : ℂ) ≠ 0`.

Introduce and unpack `hk`. Establish `: k = 0` using `by exact_mod_cast hk`. Simplify using `[this] at hn`. Establish `e : wC H (k * a.1, k * a.2) = k * wC H a` using `by simp [wC]; ring`. Use `hs.2 (k * a.1, k * a.2)` as an intermediate fact.

Rewrite `this` using `[e]`. Establish `hm : (m : ℂ) ≠ 0`. Introduce and unpack `hk`. Establish `: m = 0` using `by exact_mod_cast hk`. Simplify using `[this] at hn`.

Establish `e1 : wC H s * (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H s * wC H a / m` using `by push_cast; field_simp`. Establish `e2 : (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H a / m` using `by push_cast; field_simp`. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  intro E _ _ _ H C τ hτ io h n hn
  obtain ⟨W, -, hW, hker, hon, hcomm⟩ := GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C
  have hc := hcomm τ hτ io h
  have key := corr (wC H (0, 1)) (wC H) (fun s => by simp [wC])
    (fun z z' => C.pt z' ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z)
    (fun z => by
      have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z) ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
        rw [Category.assoc, pt_over]; simp
      obtain ⟨z', hz⟩ := hon (h.1.lift _ _ w) (h.1.lift_snd _ _ w)
      exact ⟨z', by rw [hz, h.1.lift_fst]⟩)
    (fun z' => by
      obtain ⟨z, hz⟩ := hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z' ≫ io) (by
        rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z'), pt_over, Category.id_comp,
          spMap_symm])
      refine ⟨z, ?_⟩
      have := spMap_symm τ.symm
      rw [RingEquiv.symm_symm] at this
      rw [hz, ← Category.assoc, this, Category.id_comp])
    (fun z z' y y' hz hy => pt_add C h hz hy)
    (fun z z' hz => by
      rw [← hW, ← hW, Category.assoc, hc, ← Category.assoc, hz, Category.assoc])
    (fun z z' y y' hz hy => by
      rw [← hker, ← hker]
      constructor
      · intro e
        apply h.1.hom_ext
        · rw [hz, hy, e]
        · rw [pt_over, pt_over]
      · intro e
        have e' : spMap (τ : ℂ →+* ℂ) ≫ C.pt z = spMap (τ : ℂ →+* ℂ) ≫ C.pt y := by rw [← hz, ← hy, e]
        have := congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) e'
        simpa only [← Category.assoc, spMap_symm, Category.id_comp] using this)
    (fun z z' y' hz e => by rw [← (hker _ _).2 e]; exact hz) n hn
  refine ⟨key.1.imp fun s hs => ⟨h, hs⟩, fun s hs => ⟨key.2 s hs.2, ?_⟩⟩
  rintro m ⟨k, rfl⟩
  refine ⟨h, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := by
    rintro hk
    have : k = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by simp [wC]; ring
  have := hs.2 (k * a.1, k * a.2)
  rw [e] at this
  have hm : (m : ℂ) ≠ 0 := by
    rintro hk
    have : m = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e1 : wC H s * (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H s * wC H a / m := by push_cast; field_simp
  have e2 : (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H a / m := by push_cast; field_simp
  rwa [e1, e2] at this

end GlobalTheory.CompRat.Acts
