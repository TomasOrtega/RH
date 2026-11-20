import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.UnipFrame

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

section Form

variable (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma hL_apply (x y : V) : hL H y x = H.h x y := rfl

/- English proof (translation)
The claim follows from `map_sub (hL H y) x x'`.
-/
lemma h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := map_sub (hL H y) x x'

/- English proof (translation)
The claim follows from `map_sum (hL H y) g s`.
-/
lemma h_sum_left {ι : Type} (s : Finset ι) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, g i) y = ∑ i ∈ s, H.h (g i) y := map_sum (hL H y) g s

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma cj_ite (p : Prop) [Decidable p] : M.L.cj (if p then (1 : E) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

end Form

section Frame

variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

/- English proof (translation)
The claim follows from `Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)`.
-/
lemma e_e (a b : Fin r) : H.h (Fr.f a.castSucc) (Fr.f b.castSucc) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)

/- English proof (translation)
Rewrite using `[H.h_herm (Fr.f b.castSucc) (Fr.es a), Fr.h_es b a, cj_ite]`.
-/
lemma es_e (a b : Fin r) : H.h (Fr.es a) (Fr.f b.castSucc) = if b = a then 1 else 0 := by
  rw [H.h_herm (Fr.f b.castSucc) (Fr.es a), Fr.h_es b a, cj_ite]

def InW (v : V) : Prop := ∀ a, H.h v (Fr.f a.castSucc) = 0 ∧ H.h v (Fr.es a) = 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma prF_eq (v : V) : Fr.prF v =
    v - ∑ a, H.h v (Fr.es a) • Fr.f a.castSucc - ∑ a, H.h v (Fr.f a.castSucc) • Fr.es a := rfl

/- English proof (translation)
Rewrite using `[prF_eq]`. Normalize the expressions using the abelian group laws.
-/
lemma decomp (v : V) : v = (∑ a, H.h v (Fr.es a) • Fr.f a.castSucc) + Fr.prF v +
    ∑ a, H.h v (Fr.f a.castSucc) • Fr.es a := by
  rw [prF_eq]; abel

/- English proof (translation)
Introduce `b`. Prove the components needed by the constructor for the conclusion. Rewrite using `[prF_eq, h_sub_left, h_sub_left, h_sum_left, h_sum_left]`. Simplify using `[H.h_smul_left, e_e, es_e]`. Rewrite using `[prF_eq, h_sub_left, h_sub_left, h_sum_left, h_sum_left]`.

Simplify using `[H.h_smul_left, Fr.h_es, Fr.h_ss]`.
-/
lemma prF_inW (v : V) : InW Fr (Fr.prF v) := by
  intro b
  constructor
  · rw [prF_eq, h_sub_left, h_sub_left, h_sum_left, h_sum_left]
    simp [H.h_smul_left, e_e, es_e]
  · rw [prF_eq, h_sub_left, h_sub_left, h_sum_left, h_sum_left]
    simp [H.h_smul_left, Fr.h_es, Fr.h_ss]

/- English proof (translation)
Rewrite using `[prF_eq]`. Simplify using `[Fr.h_es, e_e]`.
-/
lemma prF_e (b : Fin r) : Fr.prF (Fr.f b.castSucc) = 0 := by
  rw [prF_eq]; simp [Fr.h_es, e_e]

/- English proof (translation)
Rewrite using `[prF_eq]`. Simplify using `[Fr.h_ss, es_e]`.
-/
lemma prF_es (b : Fin r) : Fr.prF (Fr.es b) = 0 := by
  rw [prF_eq]; simp [Fr.h_ss, es_e]

/- English proof (translation)
Rewrite using `[prF_eq]`. Simplify using `[fun a => (hw a).1, fun a => (hw a).2]`.
-/
lemma prF_of_inW {w : V} (hw : InW Fr w) : Fr.prF w = w := by
  rw [prF_eq]; simp [fun a => (hw a).1, fun a => (hw a).2]

/- English proof (translation)
Rewrite using `[decomp Fr u]`. Simplify using `only [map_add, map_sum, map_smul, he, hs, hw _ (prF_inW Fr u)]`.
-/
lemma ext_decomp (f g : V →ₗ[E] E) (he : ∀ a : Fin r, f (Fr.f a.castSucc) = g (Fr.f a.castSucc))
    (hs : ∀ a, f (Fr.es a) = g (Fr.es a)) (hw : ∀ w, InW Fr w → f w = g w) (u : V) : f u = g u := by
  rw [decomp Fr u]
  simp only [map_add, map_sum, map_smul, he, hs, hw _ (prF_inW Fr u)]

end Frame

section Elem

variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) (y : Fin r → V)

def prL : V →ₗ[E] V :=
  LinearMap.id - ∑ a, (hL H (Fr.es a)).smulRight (Fr.f a.castSucc) -
    ∑ a, (hL H (Fr.f a.castSucc)).smulRight (Fr.es a)

/- English proof (translation)
Simplify using `[prL, prF_eq]`.
-/
lemma prL_apply (v : V) : prL Fr v = Fr.prF v := by
  simp [prL, prF_eq]

def Nl : V →ₗ[E] V :=
  ∑ a, (hL H (Fr.f a.castSucc)).smulRight (y a - Fr.es a) -
    ∑ j, ((hL H (y j)).comp (prL Fr)).smulRight (Fr.f j.castSucc)

/- English proof (translation)
Simplify using `[Nl, prL_apply]`.
-/
lemma Nl_apply (v : V) : Nl Fr y v = ∑ a, H.h v (Fr.f a.castSucc) • (y a - Fr.es a) -
    ∑ j, H.h (Fr.prF v) (y j) • Fr.f j.castSucc := by
  simp [Nl, prL_apply]

variable (hy1 : ∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0)
  (hy2 : ∀ a b, H.h (y a) (y b) = 0)

include hy1 in
/- English proof (translation)
Rewrite using `[hy1]`. Simplify using `[Fin.castSucc_inj]`.
-/
lemma ye (a b : Fin r) : H.h (y a) (Fr.f b.castSucc) = if b = a then 1 else 0 := by
  rw [hy1]; simp [Fin.castSucc_inj]

include hy1 in
/- English proof (translation)
Rewrite using `[H.h_herm (y a) (Fr.f b.castSucc), ye Fr y hy1, cj_ite]`.
-/
lemma ey (a b : Fin r) : H.h (Fr.f b.castSucc) (y a) = if b = a then 1 else 0 := by
  rw [H.h_herm (y a) (Fr.f b.castSucc), ye Fr y hy1, cj_ite]

include hy1 in
/- English proof (translation)
Rewrite using `[hy1, if_neg (Fin.castSucc_lt_last a).ne']`.
-/
lemma yz (a : Fin r) : H.h (y a) (Fr.f (Fin.last r)) = 0 := by
  rw [hy1, if_neg (Fin.castSucc_lt_last a).ne']

/- English proof (translation)
Rewrite using `[Nl_apply, prF_e]`. Simplify using `[e_e, HermSp.h_zero_left]`.
-/
lemma Nl_e (b : Fin r) : Nl Fr y (Fr.f b.castSucc) = 0 := by
  rw [Nl_apply, prF_e]; simp [e_e, HermSp.h_zero_left]

/- English proof (translation)
Rewrite using `[Nl_apply, prF_es]`. Simplify using `[es_e, HermSp.h_zero_left]`.
-/
lemma Nl_es (b : Fin r) : Nl Fr y (Fr.es b) = y b - Fr.es b := by
  rw [Nl_apply, prF_es]; simp [es_e, HermSp.h_zero_left]

/- English proof (translation)
Rewrite using `[Nl_apply]`. Simplify using `[hv]`.
-/
lemma Nl_perp {v : V} (hv : ∀ b : Fin r, H.h v (Fr.f b.castSucc) = 0) :
    Nl Fr y v = -∑ j, H.h (Fr.prF v) (y j) • Fr.f j.castSucc := by
  rw [Nl_apply]; simp [hv]

include hy1 in
/- English proof (translation)
Rewrite using `[Nl_apply, h_sub_left, h_sum_left, h_sum_left]`. Simplify using `[H.h_smul_left, h_sub_left, ye Fr y hy1, es_e, e_e]`.
-/
lemma Nl_orth (v : V) (b : Fin r) : H.h (Nl Fr y v) (Fr.f b.castSucc) = 0 := by
  rw [Nl_apply, h_sub_left, h_sum_left, h_sum_left]
  simp [H.h_smul_left, h_sub_left, ye Fr y hy1, es_e, e_e]

include hy1 in
/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Module.End.mul_apply, LinearMap.zero_apply]`. Establish `h` using `Nl_perp Fr y (v := Nl Fr y v) (Nl_orth Fr y hy1 v)`. Rewrite using `[h, map_neg, map_sum]`. Simplify using `[Nl_e]`.
-/
lemma Nl_cube : Nl Fr y * Nl Fr y * Nl Fr y = 0 := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.zero_apply]
  have h := Nl_perp Fr y (v := Nl Fr y v) (Nl_orth Fr y hy1 v)
  rw [h, map_neg, map_sum]
  simp [Nl_e]

include hy1 in
/- English proof (translation)
Establish `: (1 + Nl Fr y) * (1 - Nl Fr y + Nl Fr y * Nl Fr y) = 1 + Nl Fr y * Nl Fr y * Nl Fr y` using `by noncomm_ring`. Rewrite using `[this, Nl_cube Fr y hy1, add_zero]`.
-/
lemma inv_left : (1 + Nl Fr y) * (1 - Nl Fr y + Nl Fr y * Nl Fr y) = 1 := by
  have : (1 + Nl Fr y) * (1 - Nl Fr y + Nl Fr y * Nl Fr y) = 1 + Nl Fr y * Nl Fr y * Nl Fr y := by
    noncomm_ring
  rw [this, Nl_cube Fr y hy1, add_zero]

include hy1 in
/- English proof (translation)
Establish `: (1 - Nl Fr y + Nl Fr y * Nl Fr y) * (1 + Nl Fr y) = 1 + Nl Fr y * Nl Fr y * Nl Fr y` using `by noncomm_ring`. Rewrite using `[this, Nl_cube Fr y hy1, add_zero]`.
-/
lemma inv_right : (1 - Nl Fr y + Nl Fr y * Nl Fr y) * (1 + Nl Fr y) = 1 := by
  have : (1 - Nl Fr y + Nl Fr y * Nl Fr y) * (1 + Nl Fr y) = 1 + Nl Fr y * Nl Fr y * Nl Fr y := by
    noncomm_ring
  rw [this, Nl_cube Fr y hy1, add_zero]

def nE : V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (1 + Nl Fr y) (1 - Nl Fr y + Nl Fr y * Nl Fr y) (inv_left Fr y hy1) (inv_right Fr y hy1)

/- English proof (translation)
Simplify using `[nE]`.
-/
lemma nE_apply (v : V) : nE Fr y hy1 v = v + Nl Fr y v := by
  simp [nE]

end Elem

section Unit

variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) (y : Fin r → V)
  (hy1 : ∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0)
  (hy2 : ∀ a b, H.h (y a) (y b) = 0)

include hy1

/- English proof (translation)
Rewrite using `[nE_apply, Nl_e, add_zero]`.
-/
lemma n_e (b : Fin r) : nE Fr y hy1 (Fr.f b.castSucc) = Fr.f b.castSucc := by
  rw [nE_apply, Nl_e, add_zero]

/- English proof (translation)
Rewrite using `[nE_apply, Nl_es]`. Normalize the expressions using the abelian group laws.
-/
lemma n_es (b : Fin r) : nE Fr y hy1 (Fr.es b) = y b := by
  rw [nE_apply, Nl_es]; abel

/- English proof (translation)
Rewrite using `[nE_apply, Nl_perp Fr y (fun b => (hw b).1), prF_of_inW Fr hw, sub_eq_add_neg]`.
-/
lemma unipotentFrameEquiv_orthogonal_complement {w : V} (hw : InW Fr w) :
    nE Fr y hy1 w = w - ∑ j, H.h w (y j) • Fr.f j.castSucc := by
  rw [nE_apply, Nl_perp Fr y (fun b => (hw b).1), prF_of_inW Fr hw, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[H.h_herm (nE Fr y hy1 u), h, ← H.h_herm]`.
-/
lemma preserves_form_symm {u v : V} (h : H.h (nE Fr y hy1 u) (nE Fr y hy1 v) = H.h u v) :
    H.h (nE Fr y hy1 v) (nE Fr y hy1 u) = H.h v u := by
  rw [H.h_herm (nE Fr y hy1 u), h, ← H.h_herm]

/- English proof (translation)
Rewrite using `[n_e, n_e]`.
-/
lemma preserves_form_e_e (a b : Fin r) :
    H.h (nE Fr y hy1 (Fr.f a.castSucc)) (nE Fr y hy1 (Fr.f b.castSucc)) =
      H.h (Fr.f a.castSucc) (Fr.f b.castSucc) := by
  rw [n_e, n_e]

/- English proof (translation)
Rewrite using `[n_es, n_e, ye Fr y hy1, es_e]`.
-/
lemma preserves_form_dual_e (a b : Fin r) :
    H.h (nE Fr y hy1 (Fr.es a)) (nE Fr y hy1 (Fr.f b.castSucc)) = H.h (Fr.es a) (Fr.f b.castSucc) := by
  rw [n_es, n_e, ye Fr y hy1, es_e]

/- English proof (translation)
Rewrite using `[unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, n_e, h_sub_left, h_sum_left]`. Simplify using `[H.h_smul_left, e_e]`.
-/
lemma P_W_e {w : V} (hw : InW Fr w) (b : Fin r) :
    H.h (nE Fr y hy1 w) (nE Fr y hy1 (Fr.f b.castSucc)) = H.h w (Fr.f b.castSucc) := by
  rw [unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, n_e, h_sub_left, h_sum_left]
  simp [H.h_smul_left, e_e]

include hy2 in
/- English proof (translation)
Rewrite using `[n_es, n_es, hy2, Fr.h_ss]`.
-/
lemma preserves_form_dual_dual (a b : Fin r) :
    H.h (nE Fr y hy1 (Fr.es a)) (nE Fr y hy1 (Fr.es b)) = H.h (Fr.es a) (Fr.es b) := by
  rw [n_es, n_es, hy2, Fr.h_ss]

/- English proof (translation)
Rewrite using `[unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, n_es, h_sub_left, h_sum_left, (hw b).2]`. Simplify using `[H.h_smul_left, ey Fr y hy1]`.
-/
lemma P_W_es {w : V} (hw : InW Fr w) (b : Fin r) :
    H.h (nE Fr y hy1 w) (nE Fr y hy1 (Fr.es b)) = H.h w (Fr.es b) := by
  rw [unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, n_es, h_sub_left, h_sum_left, (hw b).2]
  simp [H.h_smul_left, ey Fr y hy1]

/- English proof (translation)
Establish `h1 : ∀ j : Fin r, H.h (Fr.f j.castSucc) (nE Fr y hy1 w') = 0`. Introduce `j`. Rewrite using `[H.h_herm (nE Fr y hy1 w') (Fr.f j.castSucc), ← n_e Fr y hy1 j, P_W_e Fr y hy1 hw' j, (hw' j).1, map_zero]`. Establish `h2 : H.h w (nE Fr y hy1 w') = H.h w w'`. Establish `h0 : ∀ k : Fin r, H.h (Fr.f k.castSucc) w = 0` using `fun k => by`.

Rewrite using `[H.h_herm w, (hw k).1, map_zero]`. Rewrite using `[H.h_herm (nE Fr y hy1 w') w, unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw', h_sub_left, h_sum_left]`. Simplify using `only [H.h_smul_left, h0, mul_zero, Finset.sum_const_zero, sub_zero]`. Rewrite using `[← H.h_herm]`. Rewrite using `[unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, h_sub_left, h_sum_left]`.

Simplify using `only [H.h_smul_left, h1, mul_zero, Finset.sum_const_zero, sub_zero, h2]`.
-/
lemma unitaryFrameDual_preserves_herm_on_frameSpan {w w' : V} (hw : InW Fr w) (hw' : InW Fr w') :
    H.h (nE Fr y hy1 w) (nE Fr y hy1 w') = H.h w w' := by
  have h1 : ∀ j : Fin r, H.h (Fr.f j.castSucc) (nE Fr y hy1 w') = 0 := by
    intro j
    rw [H.h_herm (nE Fr y hy1 w') (Fr.f j.castSucc), ← n_e Fr y hy1 j, P_W_e Fr y hy1 hw' j,
      (hw' j).1, map_zero]
  have h2 : H.h w (nE Fr y hy1 w') = H.h w w' := by
    have h0 : ∀ k : Fin r, H.h (Fr.f k.castSucc) w = 0 := fun k => by
      rw [H.h_herm w, (hw k).1, map_zero]
    rw [H.h_herm (nE Fr y hy1 w') w, unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw', h_sub_left, h_sum_left]
    simp only [H.h_smul_left, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [← H.h_herm]
  rw [unipotentFrameEquiv_orthogonal_complement Fr y hy1 hw, h_sub_left, h_sum_left]
  simp only [H.h_smul_left, h1, mul_zero, Finset.sum_const_zero, sub_zero, h2]

include hy2 in
/- English proof (translation)
Use `ext_decomp Fr ((hL H (nE Fr y hy1 x)).comp (nE Fr y hy1).toLinearMap) (hL H x) (by intro a; simpa using he a) (by intro a; simpa using hs a) (by intro w hw; simpa using hx w hw) u` as an intermediate fact. Simplify using `using this`.
-/
lemma preserves_form_left (x : V) (hx : ∀ u, InW Fr u → H.h (nE Fr y hy1 u) (nE Fr y hy1 x) = H.h u x)
    (he : ∀ a : Fin r, H.h (nE Fr y hy1 (Fr.f a.castSucc)) (nE Fr y hy1 x) = H.h (Fr.f a.castSucc) x)
    (hs : ∀ a, H.h (nE Fr y hy1 (Fr.es a)) (nE Fr y hy1 x) = H.h (Fr.es a) x) (u : V) :
    H.h (nE Fr y hy1 u) (nE Fr y hy1 x) = H.h u x := by
  have := ext_decomp Fr ((hL H (nE Fr y hy1 x)).comp (nE Fr y hy1).toLinearMap) (hL H x)
    (by intro a; simpa using he a) (by intro a; simpa using hs a) (by intro w hw; simpa using hx w hw) u
  simpa using this

include hy2 in
/- English proof (translation)
Establish `Be : ∀ (b : Fin r) u, H.h (nE Fr y hy1 u) (nE Fr y hy1 (Fr.f b.castSucc)) = H.h u (Fr.f b.castSucc)` using `fun b => preserves_form_left Fr y hy1 hy2 _ (fun u hu => P_W_e Fr y hy1 hu b) (fun a => preserves_form_e_e Fr y hy1 a b) (fun a => preserves_form_dual_e Fr y hy1 a b)`. Establish `Bs : ∀ b u, H.h (nE Fr y hy1 u) (nE Fr y hy1 (Fr.es b)) = H.h u (Fr.es b)` using `fun b => preserves_form_left Fr y hy1 hy2 _ (fun u hu => P_W_es Fr y hy1 hu b) (fun a => preserves_form_symm Fr y hy1 (preserves_form_dual_e Fr y hy1 b a)) (fun a => preserves_form_dual_dual Fr y hy1 hy2 a b)`. Establish `Bw : ∀ w, InW Fr w → ∀ u, H.h (nE Fr y hy1 u) (nE Fr y hy1 w) = H.h u w` using `fun w hw => preserves_form_left Fr y hy1 hy2 _ (fun u hu => unitaryFrameDual_preserves_herm_on_frameSpan Fr y hy1 hu hw) (fun a => preserves_form_symm Fr y hy1 (P_W_e Fr y hy1 hw a)) (fun a => preserves_form_symm Fr y hy1 (P_W_es Fr y hy1 hw a))`. Introduce `u v`. Conclude with `preserves_form_left Fr y hy1 hy2 v (fun w hw => preserves_form_symm Fr y hy1 (Bw w hw v)) (fun a => preserves_form_symm Fr y hy1 (Be a v)) (fun a => preserves_form_symm Fr y hy1 (Bs a v)) u`.
-/
lemma unitary : IsUnitary H (nE Fr y hy1) := by

  have Be : ∀ (b : Fin r) u, H.h (nE Fr y hy1 u) (nE Fr y hy1 (Fr.f b.castSucc)) = H.h u (Fr.f b.castSucc) :=
    fun b => preserves_form_left Fr y hy1 hy2 _ (fun u hu => P_W_e Fr y hy1 hu b) (fun a => preserves_form_e_e Fr y hy1 a b)
      (fun a => preserves_form_dual_e Fr y hy1 a b)
  have Bs : ∀ b u, H.h (nE Fr y hy1 u) (nE Fr y hy1 (Fr.es b)) = H.h u (Fr.es b) :=
    fun b => preserves_form_left Fr y hy1 hy2 _ (fun u hu => P_W_es Fr y hy1 hu b)
      (fun a => preserves_form_symm Fr y hy1 (preserves_form_dual_e Fr y hy1 b a)) (fun a => preserves_form_dual_dual Fr y hy1 hy2 a b)
  have Bw : ∀ w, InW Fr w → ∀ u, H.h (nE Fr y hy1 u) (nE Fr y hy1 w) = H.h u w :=
    fun w hw => preserves_form_left Fr y hy1 hy2 _ (fun u hu => unitaryFrameDual_preserves_herm_on_frameSpan Fr y hy1 hu hw)
      (fun a => preserves_form_symm Fr y hy1 (P_W_e Fr y hy1 hw a)) (fun a => preserves_form_symm Fr y hy1 (P_W_es Fr y hy1 hw a))
  intro u v
  exact preserves_form_left Fr y hy1 hy2 v (fun w hw => preserves_form_symm Fr y hy1 (Bw w hw v))
    (fun a => preserves_form_symm Fr y hy1 (Be a v)) (fun a => preserves_form_symm Fr y hy1 (Bs a v)) u

end Unit

/- English proof (translation)
Introduce `hy1 hy2`. Use `⟨nE Fr y hy1, unitary Fr y hy1 hy2, ?_, n_es Fr y hy1, ?_⟩` and prove the remaining obligations. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Establish `hz : InW Fr (Fr.f (Fin.last r))`. Introduce `a`. Use `⟨Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne), ?_⟩` and prove the remaining obligations. Rewrite using `[H.h_herm (Fr.es a), Fr.h_sz, map_zero]`. Rewrite using `[unipotentFrameEquiv_orthogonal_complement Fr y hy1 hz]`.

Establish `: ∀ j, H.h (Fr.f (Fin.last r)) (y j) = 0` using `fun j => by`. Rewrite using `[H.h_herm (y j), yz Fr y hy1, map_zero]`. Simplify using `[this]`. Consider the case `cast b => exact n_e Fr y hy1 b`. Introduce `v hv`.

Establish `hv' : ∀ b : Fin r, H.h v (Fr.f b.castSucc) = 0` using `fun b => hv _ (Submodule.subset_span ⟨b, rfl⟩)`. Rewrite using `[nE_apply, add_sub_cancel_left, Nl_perp Fr y hv']`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem exists_unitary_frame_dual {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type}
    [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (y : Fin r → V) :
    (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → (∀ a b, H.h (y a) (y b) = 0) →
    ∃ n : V ≃ₗ[E] V, IsUnitary H n ∧ (∀ b, n (Fr.f b) = Fr.f b) ∧ (∀ a, n (Fr.es a) = y a) ∧
      ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f := by
  intro hy1 hy2
  refine ⟨nE Fr y hy1, unitary Fr y hy1 hy2, ?_, n_es Fr y hy1, ?_⟩
  · intro b
    induction b using Fin.lastCases with
    | last =>
      have hz : InW Fr (Fr.f (Fin.last r)) := by
        intro a
        refine ⟨Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne), ?_⟩
        rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
      rw [unipotentFrameEquiv_orthogonal_complement Fr y hy1 hz]
      have : ∀ j, H.h (Fr.f (Fin.last r)) (y j) = 0 := fun j => by
        rw [H.h_herm (y j), yz Fr y hy1, map_zero]
      simp [this]
    | cast b => exact n_e Fr y hy1 b
  · intro v hv
    have hv' : ∀ b : Fin r, H.h v (Fr.f b.castSucc) = 0 := fun b =>
      hv _ (Submodule.subset_span ⟨b, rfl⟩)
    rw [nE_apply, add_sub_cancel_left, Nl_perp Fr y hv']
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨j, rfl⟩

end GlobalTheory.UnipFrame
