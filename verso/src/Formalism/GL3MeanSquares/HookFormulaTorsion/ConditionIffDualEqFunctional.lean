import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hP`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Conclude with `⟨⟨fun a b => Subtype.ext (((h a).1 a.2).1.trans ((h b).1 b.2).1.symm)⟩, ⟨⟨a0, (h a0).2 ⟨rfl, hP⟩⟩⟩⟩`. Introduce `hP`.

Establish `: IsEmpty {a // C a}` using `⟨fun a => hP ((h a).1 a.2).2⟩`. Conclude with `Nat.card_of_isEmpty`.
-/
private lemma nat_card_subtype_single {α : Type*} (C : α → Prop) (a0 : α) (P : Prop)
    (h : ∀ a, C a ↔ (a = a0 ∧ P)) :
    (P → Nat.card {a // C a} = 1) ∧ (¬ P → Nat.card {a // C a} = 0) := by
  constructor
  · intro hP
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (((h a).1 a.2).1.trans ((h b).1 b.2).1.symm)⟩,
      ⟨⟨a0, (h a0).2 ⟨rfl, hP⟩⟩⟩⟩
  · intro hP
    have : IsEmpty {a // C a} := ⟨fun a => hP ((h a).1 a.2).2⟩
    exact Nat.card_of_isEmpty

/- English proof (translation)
Establish `hq : (q : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Establish `h1 : (a : ℚ) - (w.val : ℚ) = q * m`. Rewrite using `[hm]`.

Clear the denominators using the available nonvanishing facts. Establish `h2 : a - (w.val : ℤ) = q * m` using `by exact_mod_cast h1`. Establish `h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = ((q * m : ℤ) : ZMod q)` using `by rw [h2]`. Move the coercions through the operations in `at h3`. Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id_eq, ZMod.natCast_self, zero_mul] at h3`.

Conclude with `(sub_eq_zero.1 h3).symm`. Introduce `hw`. Establish `h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = 0`. Use `push_cast`. Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id_eq]`.

Rewrite using `[hw, sub_self]`. Take `⟨m, hm⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 h3`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h1 : (a : ℚ) - (w.val : ℚ) = q * m` using `by exact_mod_cast hm`. Rewrite using `[← sub_div, h1]`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma fraction_integer_iff_congruent (q : ℕ) [Fact q.Prime] (a : ℤ) (w : ZMod q) :
    ((a : ℚ) / q - ((w.val : ℕ) : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ)) ↔ w = (a : ZMod q) := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  constructor
  · rintro ⟨m, hm⟩
    have h1 : (a : ℚ) - (w.val : ℚ) = q * m := by
      rw [hm]; field_simp
    have h2 : a - (w.val : ℤ) = q * m := by exact_mod_cast h1
    have h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = ((q * m : ℤ) : ZMod q) := by rw [h2]
    push_cast at h3
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, ZMod.natCast_self, zero_mul] at h3
    exact (sub_eq_zero.1 h3).symm
  · intro hw
    have h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = 0 := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [hw, sub_self]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 h3
    refine ⟨m, ?_⟩
    have h1 : (a : ℚ) - (w.val : ℚ) = q * m := by exact_mod_cast hm
    rw [← sub_div, h1]; field_simp

/- English proof (translation)
Introduce `q _ n n' fW x0 x _ e1 intMat rhs UKcond KUcond`. Establish `hq : (q : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero`. Distinguish the cases in `hI : intMat`. Use `swap`. Establish `h1 : IsEmpty {xW // UKcond xW}` using `⟨fun a => hI a.2.2.1⟩`.

Establish `h2 : IsEmpty {f // KUcond f}` using `⟨fun a => hI a.2.2.1⟩`. Use `⟨by rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty], fun h => absurd h.1 hI, fun _ => Nat.card_of_isEmpty⟩` and prove the remaining obligations. Establish `hI'` using `hI`. Use `choose X hX using hI'`. Use `set y : Fin n' → ℤ := fun i => ∑ j, X i j * x0 j with hydef`.

Establish `hmv : ∀ (v : Fin n → ℚ) (i : Fin n'), x.mulVec v i = ∑ j, (X i j : ℚ) * v j`. Introduce `v i`. Simplify using `only [Matrix.mulVec, dotProduct, hX]`. Establish `hy : ∀ i, x.mulVec (fun j => (x0 j : ℚ)) i = (y i : ℚ)`. Introduce `i`.

Rewrite using `[hmv, hydef]`. Use `push_cast`. Both sides reduce to the same expression. Establish `he1 : ∀ i, x.mulVec e1 i = (y i : ℚ) / q`. Introduce `i`.

Rewrite using `[hmv, hydef]`. Use `push_cast`. Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl (fun j _ => by simp only [e1]; ring)`. Use `set Z : ℤ := ∑ i, fW i * y i with hZdef`.

Establish `hrhs : rhs ↔ (Z : ZMod q) = 1`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, z, hz, hz1⟩`. Establish `: (Z : ℚ) = z`. Rewrite using `[← hz, hZdef]`.

Use `push_cast`. Conclude with `Finset.sum_congr rfl (fun i _ => by rw [hy])`. Establish `hZz : Z = z` using `by exact_mod_cast this`. Rewrite using `[hZz]`. Conclude with `hz1`.

Introduce `h`. Use `⟨hI, Z, ?_, h⟩` and prove the remaining obligations. Rewrite using `[hZdef]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl (fun i _ => by rw [hy])`.

Establish `hKU : ∀ f, KUcond f ↔ (f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) ∧ (Z : ZMod q) = 1)`. Establish `key : ∑ j, ((∑ i, fW i * X i j : ℤ) : ZMod q) * (x0 j : ZMod q) = (Z : ZMod q)`. Rewrite using `[hZdef, hydef]`. Use `push_cast`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _, h3⟩`.

Establish `hf : f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q))`. Use function extensionality and compare the values at `j`. Take `⟨z, hz, hzf⟩` from `h3 j`. Establish `: ((∑ i, fW i * X i j : ℤ) : ℚ) = z`. Rewrite using `[← hz]`.

Use `push_cast`. Conclude with `Finset.sum_congr rfl (fun i _ => by rw [hX])`. Establish `h' : (∑ i, fW i * X i j : ℤ) = z` using `by exact_mod_cast this`. Rewrite using `[h', hzf]`. Use `⟨hf, ?_⟩` and prove the remaining obligations.

Rewrite using `[← key, ← h1, hf]`. Introduce and unpack `⟨hf, hP⟩`. Use `⟨?_, hI, fun j => ⟨∑ i, fW i * X i j, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hf, key, hP]`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl (fun i _ => by rw [hX])`. Rewrite using `[hf]`. Establish `hUK : ∀ xW, UKcond xW ↔ (xW = (fun i => (y i : ZMod q)) ∧ (Z : ZMod q) = 1)`. Establish `key : ∑ i, (fW i : ZMod q) * (y i : ZMod q) = (Z : ZMod q)`. Rewrite using `[hZdef]`.

Use `push_cast`. Both sides reduce to the same expression. Introduce `xW`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _, h3, _⟩`.

Establish `hw : xW = (fun i => (y i : ZMod q))`. Use function extensionality and compare the values at `i`. Use `h3 i` as an intermediate fact. Rewrite `this` using `[he1]`. Conclude with `(fraction_integer_iff_congruent q (y i) (xW i)).1 this`.

Use `⟨hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← key, ← h1, hw]`. Introduce and unpack `⟨hw, hP⟩`. Establish `h3 : ∀ i, (y i : ℚ) / q - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ)` using `fun i => (fraction_integer_iff_congruent q (y i) (xW i)).2 (by rw [hw])`. Use `⟨?_, hI, fun i => by rw [he1]; exact h3 i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw, key, hP]`. Introduce `l c choose m hm using h3`. Use `⟨fun i => (∑ j, X i j * l j) + c * m i, c, fun i => ?_⟩` and prove the remaining obligations. Establish `hsplit : x.mulVec (fun j => (l j : ℚ) + c * e1 j) i = (∑ j, (X i j : ℚ) * l j) + c * x.mulVec e1 i`. Rewrite using `[hmv, hmv, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Rewrite using `[hsplit, he1]`. Use `push_cast`. Rewrite using `[hm i]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨a1, a0⟩` from `nat_card_subtype_single UKcond _ _ hUK`. Take `⟨b1, b0⟩` from `nat_card_subtype_single KUcond _ _ hKU`. Use `⟨?_, fun h => b1 (hrhs.1 h), fun h => b0 (fun hP => h (hrhs.2 hP))⟩` and prove the remaining obligations. Distinguish the cases in `hP : (Z : ZMod q) = 1`. Rewrite using `[a1 hP, b1 hP]`.

Rewrite using `[a0 hP, b0 hP]`.
-/
theorem kernel_description : IndicatorKernelSum := by
  intro q _ n n' fW x0 x _ e1 intMat rhs UKcond KUcond
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  by_cases hI : intMat
  swap
  · have h1 : IsEmpty {xW // UKcond xW} := ⟨fun a => hI a.2.2.1⟩
    have h2 : IsEmpty {f // KUcond f} := ⟨fun a => hI a.2.2.1⟩
    refine ⟨by rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty], fun h => absurd h.1 hI,
      fun _ => Nat.card_of_isEmpty⟩
  have hI' := hI
  choose X hX using hI'
  set y : Fin n' → ℤ := fun i => ∑ j, X i j * x0 j with hydef
  have hmv : ∀ (v : Fin n → ℚ) (i : Fin n'), x.mulVec v i = ∑ j, (X i j : ℚ) * v j := by
    intro v i
    simp only [Matrix.mulVec, dotProduct, hX]
  have hy : ∀ i, x.mulVec (fun j => (x0 j : ℚ)) i = (y i : ℚ) := by
    intro i
    rw [hmv, hydef]; push_cast; rfl
  have he1 : ∀ i, x.mulVec e1 i = (y i : ℚ) / q := by
    intro i
    rw [hmv, hydef]; push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by simp only [e1]; ring)
  set Z : ℤ := ∑ i, fW i * y i with hZdef
  have hrhs : rhs ↔ (Z : ZMod q) = 1 := by
    constructor
    · rintro ⟨_, z, hz, hz1⟩
      have : (Z : ℚ) = z := by
        rw [← hz, hZdef]; push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hy])
      have hZz : Z = z := by exact_mod_cast this
      rw [hZz]; exact hz1
    · intro h
      refine ⟨hI, Z, ?_, h⟩
      rw [hZdef]; push_cast
      exact Finset.sum_congr rfl (fun i _ => by rw [hy])
  have hKU : ∀ f, KUcond f ↔
      (f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) ∧ (Z : ZMod q) = 1) := by
    have key : ∑ j, ((∑ i, fW i * X i j : ℤ) : ZMod q) * (x0 j : ZMod q) = (Z : ZMod q) := by
      rw [hZdef, hydef]; push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    intro f
    constructor
    · rintro ⟨h1, _, h3⟩
      have hf : f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) := by
        funext j
        obtain ⟨z, hz, hzf⟩ := h3 j
        have : ((∑ i, fW i * X i j : ℤ) : ℚ) = z := by
          rw [← hz]; push_cast
          exact Finset.sum_congr rfl (fun i _ => by rw [hX])
        have h' : (∑ i, fW i * X i j : ℤ) = z := by exact_mod_cast this
        rw [h', hzf]
      refine ⟨hf, ?_⟩
      rw [← key, ← h1, hf]
    · rintro ⟨hf, hP⟩
      refine ⟨?_, hI, fun j => ⟨∑ i, fW i * X i j, ?_, ?_⟩⟩
      · rw [hf, key, hP]
      · push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hX])
      · rw [hf]
  have hUK : ∀ xW, UKcond xW ↔
      (xW = (fun i => (y i : ZMod q)) ∧ (Z : ZMod q) = 1) := by
    have key : ∑ i, (fW i : ZMod q) * (y i : ZMod q) = (Z : ZMod q) := by
      rw [hZdef]; push_cast; rfl
    intro xW
    constructor
    · rintro ⟨h1, _, h3, _⟩
      have hw : xW = (fun i => (y i : ZMod q)) := by
        funext i
        have := h3 i
        rw [he1] at this
        exact (fraction_integer_iff_congruent q (y i) (xW i)).1 this
      refine ⟨hw, ?_⟩
      rw [← key, ← h1, hw]
    · rintro ⟨hw, hP⟩
      have h3 : ∀ i, (y i : ℚ) / q - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ) :=
        fun i => (fraction_integer_iff_congruent q (y i) (xW i)).2 (by rw [hw])
      refine ⟨?_, hI, fun i => by rw [he1]; exact h3 i, ?_⟩
      · rw [hw, key, hP]
      · intro l c
        choose m hm using h3
        refine ⟨fun i => (∑ j, X i j * l j) + c * m i, c, fun i => ?_⟩
        have hsplit : x.mulVec (fun j => (l j : ℚ) + c * e1 j) i =
            (∑ j, (X i j : ℚ) * l j) + c * x.mulVec e1 i := by
          rw [hmv, hmv, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit, he1]
        push_cast
        rw [hm i]
        ring
  obtain ⟨a1, a0⟩ := nat_card_subtype_single UKcond _ _ hUK
  obtain ⟨b1, b0⟩ := nat_card_subtype_single KUcond _ _ hKU
  refine ⟨?_, fun h => b1 (hrhs.1 h), fun h => b0 (fun hP => h (hrhs.2 hP))⟩
  by_cases hP : (Z : ZMod q) = 1
  · rw [a1 hP, b1 hP]
  · rw [a0 hP, b0 hP]

section Count

variable {F : Type} [Field F]

private noncomputable def dotProductDual (m : ℕ) : (Fin m → F) →ₗ[F] Module.Dual F (Fin m → F) :=
  LinearMap.mk₂ F (fun a b => a ⬝ᵥ b) (fun a b c => add_dotProduct a b c)
    (fun c a b => smul_dotProduct c a b) (fun a b c => dotProduct_add a b c)
    (fun c a b => dotProduct_smul c a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma dot_product_dual_apply (m : ℕ) (a b : Fin m → F) : dotProductDual m a b = a ⬝ᵥ b := rfl

/- English proof (translation)
Introduce `φ`. Use `⟨fun i => φ (Pi.single i 1), ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[dot_product_dual_apply]`.
-/
private lemma dot_product_dual_surjective (m : ℕ) : Function.Surjective (dotProductDual (F := F) m) := by
  intro φ
  refine ⟨fun i => φ (Pi.single i 1), ?_⟩
  ext i
  simp [dot_product_dual_apply]

private noncomputable def functionalWithScalar {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (c : F) :
    ((Fin n → F) × F) →ₗ[F] F :=
  fL.coprod (c • LinearMap.id)

/- English proof (translation)
Simplify using `[functionalWithScalar]`.
-/
private lemma functional_with_scalar_apply {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (c : F) (v : Fin n → F) (s : F) :
    functionalWithScalar fL c (v, s) = fL v + c * s := by
  simp [functionalWithScalar]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Establish `hl' : fL l = 0` using `hl`. Simplify using `[LinearMap.mem_ker, functional_with_scalar_apply, hl']`.

Rewrite using `[Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, functional_with_scalar_apply]`. Simplify using `[he]`. Introduce and unpack `⟨v, s⟩ h`. Rewrite `h` using `[LinearMap.mem_ker, functional_with_scalar_apply]`. Establish `h1 : ((v, s) : (Fin n → F) × F) = LinearMap.inl F (Fin n → F) F (v + (c * s) • e) + s • ((-c) • e, (1 : F))`.

Use `ext`. Simplify using `[smul_smul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Use `Submodule.add_mem_sup (Submodule.mem_map_of_mem ?_) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))` and prove the remaining obligations. Simplify using `[LinearMap.mem_ker, he, h]`.
-/
private lemma level_set_eq_ker_functional {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (he : fL e = 1) (c : F) :
    Uc fL e c = LinearMap.ker (functionalWithScalar fL c) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      have hl' : fL l = 0 := hl
      simp [LinearMap.mem_ker, functional_with_scalar_apply, hl']
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, functional_with_scalar_apply]
      simp [he]
  · rintro ⟨v, s⟩ h
    rw [LinearMap.mem_ker, functional_with_scalar_apply] at h
    have h1 : ((v, s) : (Fin n → F) × F) =
        LinearMap.inl F (Fin n → F) F (v + (c * s) • e) + s • ((-c) • e, (1 : F)) := by
      ext
      · simp [smul_smul]; ring
      · simp
    rw [h1]
    refine Submodule.add_mem_sup (Submodule.mem_map_of_mem ?_)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    simp [LinearMap.mem_ker, he, h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨v, s⟩`. Establish `hd : ((v, s) : (Fin n → F) × F) = (v - fL v • e, 0) + fL v • (e, (0 : F)) + s • ((0 : Fin n → F), (1 : F))`.

Apply the tactic sequence `ext <;> simp`. Establish `hk : v - fL v • e ∈ LinearMap.ker fL` using `by simp [LinearMap.mem_ker, he]`. Use `h1 _ hk` as an intermediate fact. Rewrite using `[functional_with_scalar_apply]`. Simplify using `only [LinearMap.comp_apply, LinearMap.dualMap_apply, dot_product_dual_apply]`.

Rewrite using `[hd, map_add, map_add, map_smul, map_smul, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, this, h2, h3]`. Simplify using `[mul_comm]`. Introduce `h`. Establish `h' : ∀ v s, fW ⬝ᵥ x' (v, s) = fL v + c * s`. Introduce `v s`.

Rewrite using `[← functional_with_scalar_apply, ← h]`. Both sides reduce to the same expression. Use `⟨fun l hl => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hl' : fL l = 0` using `hl`. Rewrite using `[h', hl']`.

Simplify using the standard rewrite rules. Rewrite using `[h', he]`. Simplify using the standard rewrite rules. Rewrite using `[h']`. Simplify using the standard rewrite rules.
-/
private lemma condition_iff_dual_eq_functional {n m : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (he : fL e = 1)
    (x' : ((Fin n → F) × F) →ₗ[F] (Fin m → F)) (c : F) (fW : Fin m → F) :
    ((∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧ fW ⬝ᵥ x' (e, 0) = 1 ∧ fW ⬝ᵥ x' (0, 1) = c) ↔
      (x'.dualMap ∘ₗ dotProductDual m) fW = functionalWithScalar fL c := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    apply LinearMap.ext
    rintro ⟨v, s⟩
    have hd : ((v, s) : (Fin n → F) × F) =
        (v - fL v • e, 0) + fL v • (e, (0 : F)) + s • ((0 : Fin n → F), (1 : F)) := by
      ext <;> simp
    have hk : v - fL v • e ∈ LinearMap.ker fL := by simp [LinearMap.mem_ker, he]
    have := h1 _ hk
    rw [functional_with_scalar_apply]
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, dot_product_dual_apply]
    rw [hd, map_add, map_add, map_smul, map_smul, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, this, h2, h3]
    simp [mul_comm]
  · intro h
    have h' : ∀ v s, fW ⬝ᵥ x' (v, s) = fL v + c * s := by
      intro v s
      rw [← functional_with_scalar_apply, ← h]
      rfl
    refine ⟨fun l hl => ?_, ?_, ?_⟩
    · have hl' : fL l = 0 := hl
      rw [h', hl']; simp
    · rw [h', he]; simp
    · rw [h']; simp

variable [Fintype F]

/- English proof (translation)
Take `⟨v0, rfl⟩` from `hw`. Rewrite using `[← Nat.card_eq_fintype_card, ← Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker T)]`. Use `Nat.card_congr { toFun := fun v => ⟨v.1 - v0, by simp [LinearMap.mem_ker, v.2]⟩ invFun := fun u => ⟨u.1 + v0, by` and prove the remaining obligations. Establish `: T u.1 = 0` using `u.2`. Simplify using `[this]⟩`.

Use `left_inv := fun v => by simp`. Use `right_inv := fun u => by simp }`.
-/
private lemma card_fibre_linear_map {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Module.Finite F V] (T : V →ₗ[F] W) (w : W) (hw : w ∈ LinearMap.range T) :
    Nat.card {v : V // T v = w} = Fintype.card F ^ Module.finrank F (LinearMap.ker T) := by
  obtain ⟨v0, rfl⟩ := hw
  rw [← Nat.card_eq_fintype_card, ← Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker T)]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1 - v0, by simp [LinearMap.mem_ker, v.2]⟩
      invFun := fun u => ⟨u.1 + v0, by
        have : T u.1 = 0 := u.2
        simp [this]⟩
      left_inv := fun v => by simp
      right_inv := fun u => by simp }

/- English proof (translation)
Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (x'.dualMap ∘ₗ dotProductDual (F := F) (n + g))`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker x'`. Rewrite `h1` using `[LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)), LinearMap.finrank_range_dualMap_eq_finrank_range]`. Simplify using `only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
private lemma finrank_ker_dual_composition {n g : ℕ} (hg : 1 ≤ g)
    (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) :
    Module.finrank F (LinearMap.ker (x'.dualMap ∘ₗ dotProductDual (n + g))) =
      g - 1 + Module.finrank F (LinearMap.ker x') := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (x'.dualMap ∘ₗ dotProductDual (F := F) (n + g))
  have h2 := LinearMap.finrank_range_add_finrank_ker x'
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)),
    LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
  simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at h1 h2
  omega

/- English proof (translation)
Introduce `F _ _ n g hg fL e he x' c`. Establish `hq : (1 : ℤ) ≤ (Fintype.card F : ℤ)` using `by exact_mod_cast Fintype.card_pos`. Use `set T := x'.dualMap ∘ₗ dotProductDual (F := F) (n + g) with hT`. Establish `hcount : fjCount fL e x' c = Nat.card {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c}`. Unfold `fjCount`.

Conclude with `Nat.card_congr (Equiv.subtypeEquivRight (fun fW => condition_iff_dual_eq_functional fL e he x' c fW))`. Establish `hrange : LinearMap.range T = (LinearMap.ker x').dualAnnihilator`. Rewrite using `[hT, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)), LinearMap.range_dualMap_eq_dualAnnihilator_ker]`. Rewrite using `[hcount, level_set_eq_ker_functional fL e he c]`. Distinguish the cases in `hle : LinearMap.ker x' ≤ LinearMap.ker (functionalWithScalar fL c)`.

Establish `hmem : functionalWithScalar fL c ∈ LinearMap.range T`. Rewrite using `[hrange, Submodule.mem_dualAnnihilator]`. Conclude with `fun w hw => hle hw`. Rewrite using `[card_fibre_linear_map T _ hmem, finrank_ker_dual_composition hg, inf_eq_right.2 hle]`. Take `⟨g', rfl⟩ : ∃ g', g = g' + 1` from `⟨g - 1, by omega⟩`.

Rewrite using `[Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hemp : IsEmpty {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c}`. Use `⟨fun ⟨fW, h⟩ => hle ?_⟩` and prove the remaining obligations.

Establish `: functionalWithScalar fL c ∈ LinearMap.range T` using `⟨fW, h⟩`. Rewrite `this` using `[hrange, Submodule.mem_dualAnnihilator]`. Conclude with `fun w hw => this w hw`. Rewrite using `[Nat.card_of_isEmpty]`. Use `set R := (functionalWithScalar fL c).domRestrict (LinearMap.ker x') with hR`.

Establish `hRne : R ≠ 0`. Introduce `h0`. Apply `hle` to reduce the goal to its premises. Introduce `w hw`. Use `LinearMap.congr_fun h0 ⟨w, hw⟩` as an intermediate fact.

Simplify `this` using `[hR]`. Establish `hsurj : LinearMap.range R = ⊤` using `LinearMap.range_eq_top.2 (LinearMap.surjective hRne)`. Establish `h3` using `LinearMap.finrank_range_add_finrank_ker R`. Rewrite `h3` using `[hsurj, finrank_top, Module.finrank_self]`. Establish `h4 : Module.finrank F (LinearMap.ker R) = Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' : Submodule F ((Fin n → F) × F))`.

Rewrite using `[hR, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]`. Establish `h5 : g + Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' : Submodule F ((Fin n → F) × F)) = g - 1 + Module.finrank F (LinearMap.ker x')`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h5]`. Simplify using the standard rewrite rules.
-/
theorem point_count_formula : KernelDimensionCount := by
  intro F _ _ n g hg fL e he x' c
  have hq : (1 : ℤ) ≤ (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  set T := x'.dualMap ∘ₗ dotProductDual (F := F) (n + g) with hT
  have hcount : fjCount fL e x' c = Nat.card {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c} := by
    unfold fjCount
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun fW => condition_iff_dual_eq_functional fL e he x' c fW))
  have hrange : LinearMap.range T = (LinearMap.ker x').dualAnnihilator := by
    rw [hT, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)),
      LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [hcount, level_set_eq_ker_functional fL e he c]
  by_cases hle : LinearMap.ker x' ≤ LinearMap.ker (functionalWithScalar fL c)
  · have hmem : functionalWithScalar fL c ∈ LinearMap.range T := by
      rw [hrange, Submodule.mem_dualAnnihilator]
      exact fun w hw => hle hw
    rw [card_fibre_linear_map T _ hmem, finrank_ker_dual_composition hg, inf_eq_right.2 hle]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  · have hemp : IsEmpty {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c} := by
      refine ⟨fun ⟨fW, h⟩ => hle ?_⟩
      have : functionalWithScalar fL c ∈ LinearMap.range T := ⟨fW, h⟩
      rw [hrange, Submodule.mem_dualAnnihilator] at this
      exact fun w hw => this w hw
    rw [Nat.card_of_isEmpty]
    set R := (functionalWithScalar fL c).domRestrict (LinearMap.ker x') with hR
    have hRne : R ≠ 0 := by
      intro h0
      apply hle
      intro w hw
      have := LinearMap.congr_fun h0 ⟨w, hw⟩
      simpa [hR] using this
    have hsurj : LinearMap.range R = ⊤ := LinearMap.range_eq_top.2 (LinearMap.surjective hRne)
    have h3 := LinearMap.finrank_range_add_finrank_ker R
    rw [hsurj, finrank_top, Module.finrank_self] at h3
    have h4 : Module.finrank F (LinearMap.ker R) =
        Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F)) := by
      rw [hR, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
        Submodule.map_comap_subtype, inf_comm]
    have h5 : g + Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F)) = g - 1 + Module.finrank F (LinearMap.ker x') := by
      omega
    rw [h5]
    simp

end Count

section FJ

variable {F : Type} [Field F] [Fintype F]

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Take `⟨a, ha⟩` from `AddChar.ne_one_iff.1 hψ`. Take `⟨y, hy⟩` from `LinearMap.surjective h a`.

Use `eq_zero_of_mul_eq_self_left ha ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => ?_)` and prove the remaining obligations. Simplify using `[hy, AddChar.map_add_eq_mul]`.
-/
private lemma sum_char_linear_functional {M : Type} [AddCommGroup M] [Module F M] [Fintype M]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (L : M →ₗ[F] F) [Decidable (L = 0)] :
    ∑ x, ψ (L x) = if L = 0 then (Fintype.card M : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp
  · obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ
    obtain ⟨y, hy⟩ := LinearMap.surjective h a
    refine eq_zero_of_mul_eq_self_left ha ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => ?_)
    simp [hy, AddChar.map_add_eq_mul]

end FJ

/- English proof (translation)
Introduce `F _ _ _ n g hg fL e he x' ψ hψ`. Use `set q : ℂ := (Fintype.card F : ℂ) with hqdef`. Establish `hq0 : q ≠ 0`. Rewrite using `[hqdef]`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions.

Set `A : (Fin (n + g) → F) → Prop` to `fun fW => (∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧ fW ⬝ᵥ x' (e, 0) = 1`. Set `Lf : (Fin (n + g) → F) → ((Fin n → F) →ₗ[F] F)` to `fun fW => fL - (dotProductDual (n + g) fW) ∘ₗ x' ∘ₗ LinearMap.inl F (Fin n → F) F`. Establish `hLf : ∀ fW e', Lf fW e' = fL e' - fW ⬝ᵥ x' (e', 0)` using `fun fW e' => rfl`. Establish `hA : ∀ fW, Lf fW = 0 ↔ A fW`. Introduce `fW`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : ∀ e', fW ⬝ᵥ x' (e', 0) = fL e'` using `fun e' => by`. Use `LinearMap.congr_fun h e'` as an intermediate fact. Rewrite `this` using `[hLf]`.

Conclude with `(sub_eq_zero.1 this).symm`. Conclude with `⟨fun l hl => by rw [h']; exact hl, by rw [h', he]⟩`. Introduce and unpack `⟨h1, h2⟩`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Establish `hk : v - fL v • e ∈ LinearMap.ker fL` using `by simp [LinearMap.mem_ker, he]`. Establish `h3` using `h1 _ hk`. Establish `hd : ((v, 0) : (Fin n → F) × F) = (v - fL v • e, 0) + fL v • (e, (0 : F))`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[hLf, hd, map_add, map_smul, dotProduct_add, dotProduct_smul, h3, h2]`.

Simplify using the standard rewrite rules. Establish `hL : ∑ c : F, ψ c * (fjCount fL e x' c : ℂ) = ∑ fW : Fin (n + g) → F, if A fW then ψ (fW ⬝ᵥ x' (0, 1)) else 0`. Establish `hc : ∀ c : F, (fjCount fL e x' c : ℂ) = ∑ fW : Fin (n + g) → F, if A fW ∧ fW ⬝ᵥ x' (0, 1) = c then (1 : ℂ) else 0`. Introduce `c`. Unfold `fjCount`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]`. Use `congr 2`. Use extensionality with `fW`. Simplify using `[A, and_assoc]`. Simplify using `only [hc, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun fW _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : A fW`. Simplify using `[h]`. Simplify using `[h]`.

Establish `hind : ∀ y : Fin (n + g) → F, ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ y) = if y = 0 then q ^ (n + g) else 0`. Introduce `y`. Use `sum_char_linear_functional ψ hψ ((dotProductDual (F := F) (n + g)).flip y)` as an intermediate fact. Establish `h0 : (dotProductDual (F` using `F) (n + g)).flip y = 0 ↔ y = 0 := by`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use function extensionality and compare the values at `i`. Use `LinearMap.congr_fun h (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[dot_product_dual_apply]`. Introduce and unpack `rfl`.

Simplify using the standard rewrite rules. Simplify using `only [LinearMap.flip_apply, dot_product_dual_apply, h0] at this`. Rewrite using `[this]`. Simplify using `[hqdef]`. Establish `hinner : ∀ fW : Fin (n + g) → F, ∑ e' : Fin n → F, ψ (Lf fW e') = if A fW then q ^ n else 0`.

Introduce `fW`. Rewrite using `[sum_char_linear_functional ψ hψ (Lf fW)]`. Simplify using `[hA, hqdef]`. Apply `mul_left_cancel₀ (pow_ne_zero n hq0)` to reduce the goal to its premises. Rewrite using `[hL]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun fW _ => ?_)` and prove the remaining obligations. Rewrite using `[hinner]`. Distinguish the cases in `h : A fW`.

Simplify using `[h, mul_comm]`. Simplify using `[h]`. Use `_ = ∑ e' : Fin n → F, ψ (fL e') * ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ x' (-e', 1)) := by`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun e' _ => Finset.sum_congr rfl (fun fW _ => ?_))` and prove the remaining obligations. Establish `hd : ((-e', 1) : (Fin n → F) × F) = (0, 1) - (e', 0)`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[hLf, hd, LinearMap.map_sub x', dotProduct_sub, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = q ^ n * (q ^ g * ∑ e' : Fin n → F, ψ (fL e') * (if x' (-e', 1) = 0 then 1 else 0)) := by`. Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun e' _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hind]`.

Distinguish the cases in `h : x' (-e', 1) = 0`. Simplify using `[h, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`.
-/
theorem fourier_jacobi_count : CharacterSumCancellation := by
  classical
  intro F _ _ _ n g hg fL e he x' ψ hψ
  set q : ℂ := (Fintype.card F : ℂ) with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef]; exact_mod_cast Fintype.card_ne_zero

  let A : (Fin (n + g) → F) → Prop := fun fW =>
    (∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧ fW ⬝ᵥ x' (e, 0) = 1

  let Lf : (Fin (n + g) → F) → ((Fin n → F) →ₗ[F] F) := fun fW =>
    fL - (dotProductDual (n + g) fW) ∘ₗ x' ∘ₗ LinearMap.inl F (Fin n → F) F
  have hLf : ∀ fW e', Lf fW e' = fL e' - fW ⬝ᵥ x' (e', 0) := fun fW e' => rfl
  have hA : ∀ fW, Lf fW = 0 ↔ A fW := by
    intro fW
    constructor
    · intro h
      have h' : ∀ e', fW ⬝ᵥ x' (e', 0) = fL e' := fun e' => by
        have := LinearMap.congr_fun h e'
        rw [hLf] at this
        exact (sub_eq_zero.1 this).symm
      exact ⟨fun l hl => by rw [h']; exact hl, by rw [h', he]⟩
    · rintro ⟨h1, h2⟩
      apply LinearMap.ext
      intro v
      have hk : v - fL v • e ∈ LinearMap.ker fL := by simp [LinearMap.mem_ker, he]
      have h3 := h1 _ hk
      have hd : ((v, 0) : (Fin n → F) × F) = (v - fL v • e, 0) + fL v • (e, (0 : F)) := by
        ext <;> simp
      rw [hLf, hd, map_add, map_smul, dotProduct_add, dotProduct_smul, h3, h2]
      simp
  have hL : ∑ c : F, ψ c * (fjCount fL e x' c : ℂ) =
      ∑ fW : Fin (n + g) → F, if A fW then ψ (fW ⬝ᵥ x' (0, 1)) else 0 := by
    have hc : ∀ c : F, (fjCount fL e x' c : ℂ) =
        ∑ fW : Fin (n + g) → F, if A fW ∧ fW ⬝ᵥ x' (0, 1) = c then (1 : ℂ) else 0 := by
      intro c
      unfold fjCount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
      congr 2
      ext fW
      simp [A, and_assoc]
    simp only [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun fW _ => ?_)
    by_cases h : A fW
    · simp [h]
    · simp [h]
  have hind : ∀ y : Fin (n + g) → F,
      ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ y) = if y = 0 then q ^ (n + g) else 0 := by
    intro y
    have := sum_char_linear_functional ψ hψ ((dotProductDual (F := F) (n + g)).flip y)
    have h0 : (dotProductDual (F := F) (n + g)).flip y = 0 ↔ y = 0 := by
      constructor
      · intro h
        funext i
        have := LinearMap.congr_fun h (Pi.single i 1)
        simpa [dot_product_dual_apply] using this
      · rintro rfl; simp
    simp only [LinearMap.flip_apply, dot_product_dual_apply, h0] at this
    rw [this]
    simp [hqdef]
  have hinner : ∀ fW : Fin (n + g) → F,
      ∑ e' : Fin n → F, ψ (Lf fW e') = if A fW then q ^ n else 0 := by
    intro fW
    rw [sum_char_linear_functional ψ hψ (Lf fW)]
    simp [hA, hqdef]
  apply mul_left_cancel₀ (pow_ne_zero n hq0)
  rw [hL]
  calc q ^ n * ∑ fW : Fin (n + g) → F, (if A fW then ψ (fW ⬝ᵥ x' (0, 1)) else 0)
      = ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ x' (0, 1)) * ∑ e' : Fin n → F, ψ (Lf fW e') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun fW _ => ?_)
        rw [hinner]
        by_cases h : A fW
        · simp [h, mul_comm]
        · simp [h]
    _ = ∑ e' : Fin n → F, ψ (fL e') * ∑ fW : Fin (n + g) → F, ψ (fW ⬝ᵥ x' (-e', 1)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e' _ => Finset.sum_congr rfl (fun fW _ => ?_))
        have hd : ((-e', 1) : (Fin n → F) × F) = (0, 1) - (e', 0) := by
          ext <;> simp
        rw [hLf, hd, LinearMap.map_sub x', dotProduct_sub, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = q ^ n * (q ^ g * ∑ e' : Fin n → F, ψ (fL e') * (if x' (-e', 1) = 0 then 1 else 0)) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e' _ => ?_)
        rw [← Finset.mul_sum, hind]
        by_cases h : x' (-e', 1) = 0
        · simp [h, pow_add]; ring
        · simp [h]

section Onto

open Formalism.LogVandermondeBounds.product_first_zeroth_parts

section FFOnto

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

/- English proof (translation)
Simplify using `only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
private lemma pair_smul_left_hook_formula_torsion (a : k) (f x : Fin r → k) : pair (a • f) x = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`.
-/
private lemma pair_smul_right' (a : k) (f x : Fin r → k) : pair f (a • x) = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/- English proof (translation)
Simplify using `only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
private lemma pair_add_left' (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [pair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
private lemma pairing_sub_right (f x y : Fin r → k) : pair f (x - y) = pair f x - pair f y := by
  simp only [pair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[pair]`.
-/
private lemma pair_zero_right' (f : Fin r → k) : pair f (0 : Fin r → k) = 0 := by
  simp [pair]

/- English proof (translation)
Simplify using `[pair, Pi.single_apply]`.
-/
private lemma pairing_single_left (x : Fin r → k) (i : Fin r) (a : k) :
    pair (Pi.single i a) x = a * x i := by
  simp [pair, Pi.single_apply]

private def unitSmulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma unit_smul_equiv_apply (c : kˣ) (f : Fin r → k) :
    unitSmulEquiv c f = (c : k) • f := rfl

/- English proof (translation)
Use `eq_zero_of_mul_eq_self_left hb ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => (h x).symm)`.
-/
private lemma sum_eq_zero_of_twisted_shift {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) (y : G)
    (b : ℂ) (hb : b ≠ 1) (h : ∀ x, F (y + x) = b * F x) : ∑ x, F x = 0 := by
  refine eq_zero_of_mul_eq_self_left hb ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => (h x).symm)

/- English proof (translation)
Use `split_ifs with hh`. Substitute `hh` using the available equality. Simplify using `[pair_zero_right']`. Take `⟨i, hi'⟩` from `Function.ne_iff.1 hh`. Establish `hi : h i ≠ 0` using `hi'`.

Take `⟨x0, hx0⟩` from `AddChar.ne_one_iff.1 hψ`. Use `sum_eq_zero_of_twisted_shift (fun f => ψ (pair f h)) (Pi.single i (x0 * (h i)⁻¹)) (ψ x0) hx0 (fun f => ?_)` and prove the remaining obligations. Rewrite using `[pair_add_left', pairing_single_left, mul_assoc, inv_mul_cancel₀ hi, mul_one, AddChar.map_add_eq_mul]`.
-/
private lemma sum_char_pairing_orthogonality (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h : Fin r → k) :
    ∑ f, ψ (pair f h) = if h = 0 then (Fintype.card k : ℂ) ^ r else 0 := by
  split_ifs with hh
  · subst hh
    simp [pair_zero_right']
  obtain ⟨i, hi'⟩ := Function.ne_iff.1 hh
  have hi : h i ≠ 0 := hi'
  obtain ⟨x0, hx0⟩ := AddChar.ne_one_iff.1 hψ
  refine sum_eq_zero_of_twisted_shift (fun f => ψ (pair f h)) (Pi.single i (x0 * (h i)⁻¹)) (ψ x0) hx0
    (fun f => ?_)
  rw [pair_add_left', pairing_single_left, mul_assoc, inv_mul_cancel₀ hi, mul_one,
    AddChar.map_add_eq_mul]

end FFOnto

/- English proof (translation)
Introduce `k _ _ _ r ψ hψ ψv hv`. Use `set v0 : (Fin r → k) → ℂ := fun x => if x = 0 then 0 else ψv x with hv0`. Establish `hq : (Fintype.card k : ℂ) ^ r ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)`. Establish `hnm0 : ∀ y, ∑ c : kˣ, v0 (((c⁻¹ : kˣ) : k) • y) = 0`. Introduce `y`.

Distinguish the cases in `hy : y = 0`. Simplify using `[hy, hv0]`. Use `hv y hy` as an intermediate fact. Simplify using `only [nmV, diaV] at this`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Simplify using `[hv0, hy]`. Set `φ : (Fin r → k) → ℂ` to `fun f => ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ x, ψ (-pair f x) * v0 x`. Establish `hnm : ∀ f, nmP φ f = 0`. Introduce `f`.

Simplify using `only [nmP, diaP, φ]`. Rewrite using `[← Finset.mul_sum]`. Establish `key : ∑ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x = 0`. Establish `step : ∀ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x = ∑ y, ψ (-pair f y) * v0 (((c⁻¹ : kˣ) : k) • y)`. Introduce `c`.

Use `Fintype.sum_equiv (unitSmulEquiv c) _ _ (fun x => ?_)` and prove the remaining obligations. Simplify using `only [unit_smul_equiv_apply, pair_smul_left_hook_formula_torsion, pair_smul_right', smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]`. Use `Finset.sum_eq_zero (fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hnm0, mul_zero]`.

Rewrite using `[key, mul_zero]`. Establish `hφ0 : φ 0 = 0`. Use `hnm 0` as an intermediate fact. Simplify using `only [nmP, diaP, smul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)`.

Use `⟨φ, fun f _ => hnm f, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : opFF ψ φ x = ∑ f, ψ (pair f x) * φ f`. Simplify using `only [opFF, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun f _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hf : f = 0`.

Simplify using `[hf, hφ0]`. Simplify using `[hf]`. Establish `h2 : ∑ f, ψ (pair f x) * φ f = ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ y, v0 y * ∑ f, ψ (pair f (x - y))`. Simplify using `only [φ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun f _ => ?_))` and prove the remaining obligations. Rewrite using `[pairing_sub_right, sub_eq_add_neg, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Simplify using `only [sum_char_pairing_orthogonality ψ hψ, sub_eq_zero, mul_ite, mul_zero]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [hv0, hx, Finset.mem_univ, if_true, if_false]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fourier_transform_kernel_surjective : Formalism.HermitianLattices.LocalLatticeBases.FourierTransformKernelSurjective := by
  intro k _ _ _ r ψ hψ ψv hv
  set v0 : (Fin r → k) → ℂ := fun x => if x = 0 then 0 else ψv x with hv0
  have hq : (Fintype.card k : ℂ) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hnm0 : ∀ y, ∑ c : kˣ, v0 (((c⁻¹ : kˣ) : k) • y) = 0 := by
    intro y
    by_cases hy : y = 0
    · simp [hy, hv0]
    · have := hv y hy
      simp only [nmV, diaV] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [hv0, hy]
  let φ : (Fin r → k) → ℂ :=
    fun f => ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ x, ψ (-pair f x) * v0 x
  have hnm : ∀ f, nmP φ f = 0 := by
    intro f
    simp only [nmP, diaP, φ]
    rw [← Finset.mul_sum]
    have key : ∑ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x = 0 := by
      have step : ∀ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x =
          ∑ y, ψ (-pair f y) * v0 (((c⁻¹ : kˣ) : k) • y) := by
        intro c
        refine Fintype.sum_equiv (unitSmulEquiv c) _ _ (fun x => ?_)
        simp only [unit_smul_equiv_apply, pair_smul_left_hook_formula_torsion, pair_smul_right', smul_smul,
          Units.inv_mul, one_smul]
      rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [← Finset.mul_sum, hnm0, mul_zero]
    rw [key, mul_zero]
  have hφ0 : φ 0 = 0 := by
    have := hnm 0
    simp only [nmP, diaP, smul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine ⟨φ, fun f _ => hnm f, fun x hx => ?_⟩
  have h1 : opFF ψ φ x = ∑ f, ψ (pair f x) * φ f := by
    simp only [opFF, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases hf : f = 0
    · simp [hf, hφ0]
    · simp [hf]
  have h2 : ∑ f, ψ (pair f x) * φ f =
      ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ y, v0 y * ∑ f, ψ (pair f (x - y)) := by
    simp only [φ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun f _ => ?_))
    rw [pairing_sub_right, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [h1, h2]
  simp only [sum_char_pairing_orthogonality ψ hψ, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [hv0, hx, Finset.mem_univ, if_true, if_false]
  field_simp

end Onto

end Formalism.HermitianLattices.LocalLatticeBases
