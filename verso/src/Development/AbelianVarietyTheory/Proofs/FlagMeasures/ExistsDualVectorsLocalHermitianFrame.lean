import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]`.
-/
private lemma h_add_right (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

/- English proof (translation)
Rewrite using `[H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]`.
-/
private lemma h_smul_right (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

/- English proof (translation)
Use `H.h_smul_left (-1) x y` as an intermediate fact. Simplify using `using this`.
-/
private lemma h_neg_left (H : HermSp M V) (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]`.
-/
private lemma h_sub_left (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]`.
-/
private lemma h_sub_right (H : HermSp M V) (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]

/- English proof (translation)
Set `φ : V →+ E` to `AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)`. Conclude with `map_sum φ v s`.
-/
private lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)
  exact map_sum φ v s

/- English proof (translation)
Set `φ : V →+ E` to `AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)`. Conclude with `map_sum φ v s`.
-/
private lemma h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  let φ : V →+ E := AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)
  exact map_sum φ v s

end GlobalTheory.LocDual

open GlobalTheory.LocDual in

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy`. Take `⟨y, hy⟩` from `hy`. Use `haveI := hM.char0`. Use `set z := f (Fin.last r) with hz`. Use `set e : Fin r → V := fun i => f i.castSucc with he`.

Establish `hez : ∀ k, H.h (e k) z = 0` using `fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))`. Establish `hze : ∀ k, H.h z (e k) = 0` using `fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))`. Establish `hee : ∀ k l, H.h (e k) (e l) = 0` using `fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))`. Set `y' : Fin r → V` to `fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z`. Establish `hy'z : ∀ j, H.h (y' j) z = 0`.

Introduce `j`. Simplify using `only [y', H.h_add_left, H.h_smul_left, hzz]`. Rewrite using `[show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]`. Rewrite using `[inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]`. Establish `hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0`.

Introduce `k j`. Simplify using `only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]`. Conclude with `hy k j`. Set `half : E` to `algebraMap F E (1 / 2)`. Establish `hhalf : M.L.cj half = half` using `M.L.cj.commutes _`.

Establish `hhalf2 : half + half = 1`. Simplify using `only [half, ← map_add, add_halves, map_one]`. Set `b : Fin r → Fin r → E` to `fun j k => half * H.h (y' j) (y' k)`. Set `es : Fin r → V` to `fun j => y' j - ∑ k, b j k • e k`. Establish `hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v`.

Introduce `i v`. Simplify using `only [es, h_sub_left, h_sum_left, H.h_smul_left]`. Establish `hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k)`. Introduce `v j`. Simplify using `only [es, h_sub_right, h_sum_right, h_smul_right]`.

Establish `hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0`. Introduce `i k`. Rewrite using `[H.h_herm, hey' k i]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[hesR]`. Simplify using `only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [b, map_mul, hhalf]`. Rewrite using `[← H.h_herm (y' j) (y' i)]`.

Take the linear combination `(-H.h (y' i) (y' j)) * hhalf2`. Introduce `i j show H.h (e i) (es j) = _`. Rewrite using `[hesR]`. Simplify using `only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]`. Introduce `i show H.h (es i) z = 0`.

Rewrite using `[hesL]`. Simplify using `only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]`.
-/
theorem GlobalTheory.LocDual.frameD_exists : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (f : Fin (r + 1) → V) (T : F), T ≠ 0 → (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) → H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T) → (∃ y : Fin r → V, ∀ i j : Fin r, H.h (f i.castSucc) (y j) = if i = j then 1 else 0) → ∃ Fr : FrameD H r, Fr.f = f ∧ Fr.T = T := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy
  obtain ⟨y, hy⟩ := hy
  haveI := hM.char0
  set z := f (Fin.last r) with hz
  set e : Fin r → V := fun i => f i.castSucc with he
  have hez : ∀ k, H.h (e k) z = 0 := fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  have hze : ∀ k, H.h z (e k) = 0 := fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))
  have hee : ∀ k l, H.h (e k) (e l) = 0 := fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  let y' : Fin r → V := fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z
  have hy'z : ∀ j, H.h (y' j) z = 0 := by
    intro j
    simp only [y', H.h_add_left, H.h_smul_left, hzz]
    rw [show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T
        = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]
    rw [inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]
  have hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0 := by
    intro k j
    simp only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]
    exact hy k j
  let half : E := algebraMap F E (1 / 2)
  have hhalf : M.L.cj half = half := M.L.cj.commutes _
  have hhalf2 : half + half = 1 := by
    simp only [half, ← map_add, add_halves, map_one]
  let b : Fin r → Fin r → E := fun j k => half * H.h (y' j) (y' k)
  let es : Fin r → V := fun j => y' j - ∑ k, b j k • e k
  have hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v := by
    intro i v
    simp only [es, h_sub_left, h_sum_left, H.h_smul_left]
  have hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k) := by
    intro v j
    simp only [es, h_sub_right, h_sum_right, h_smul_right]
  have hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0 := by
    intro i k
    rw [H.h_herm, hey' k i]
    split_ifs <;> simp
  refine ⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j
    rw [hesR]
    simp only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [b, map_mul, hhalf]
    rw [← H.h_herm (y' j) (y' i)]
    linear_combination (-H.h (y' i) (y' j)) * hhalf2
  · intro i j
    show H.h (e i) (es j) = _
    rw [hesR]
    simp only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro i
    show H.h (es i) z = 0
    rw [hesL]
    simp only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]
