import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

def nodeOf (x : C.Letter) : ℝ := if x.1 then x.2 else x.2 - 1

def Sep (x y : C.Letter) : Prop := ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |x.2 - y.2 + δ|

def pushU {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) : Finset (List C.Letter) :=
  univ.image fun j : Fin K → Fin (d + 1) => mk (List.ofFn fun b => grid b (j b))

def pushTh {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (a : List C.Letter) : ℝ :=
  ∑ j : Fin K → Fin (d + 1), if mk (List.ofFn fun b => grid b (j b)) = a then F7.thGrid grid j else 0

/- English proof (translation)
Introduce `δ h1 h2`. Establish `h'` using `h (-δ) (by omega) (by omega)`. Rewrite using `[show y.2 - x.2 + (δ : ℝ) = -(x.2 - y.2 + ((-δ : ℤ) : ℝ)) by push_cast; ring, abs_neg]`. Conclude with `h'`.
-/
theorem sep_symm {x y : C.Letter} (h : Sep x y) : Sep y x := by
  intro δ h1 h2
  have h' := h (-δ) (by omega) (by omega)
  rw [show y.2 - x.2 + (δ : ℝ) = -(x.2 - y.2 + ((-δ : ℤ) : ℝ)) by push_cast; ring, abs_neg]
  exact h'

/- English proof (translation)
Introduce `δ h1 h2`. Establish `hδ1 : (-2 : ℝ) ≤ δ` using `by exact_mod_cast h1`. Establish `hδ2 : (δ : ℝ) ≤ 2` using `by exact_mod_cast h2`. Break down `lt_abs.mp h with h | h` into its components or cases. Conclude with `lt_abs.mpr (Or.inl (by linarith))`.

Conclude with `lt_abs.mpr (Or.inr (by linarith))`.
-/
theorem sep_of_four {x y : C.Letter} (h : 4 < |x.2 - y.2|) : Sep x y := by
  intro δ h1 h2
  have hδ1 : (-2 : ℝ) ≤ δ := by exact_mod_cast h1
  have hδ2 : (δ : ℝ) ≤ 2 := by exact_mod_cast h2
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))

/- English proof (translation)
Rewrite using `[List.pairwise_iff_getElem]`. Prove the components needed by the constructor for the conclusion. Introduce `h j j' hj hj' hne`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. Conclude with `h j j' hj hj' hlt`.

Conclude with `sep_symm (h j' j hj' hj hlt)`. Introduce `h j j' hj hj' hlt`. Conclude with `h j j' hj hj' (ne_of_lt hlt)`.
-/
theorem pairwise_iff_idx (L : List C.Letter) :
    L.Pairwise Sep ↔ ∀ (j j' : ℕ) (hj : j < L.length) (hj' : j' < L.length), j ≠ j' → Sep (L[j]'hj) (L[j']'hj') := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h j j' hj hj' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h j j' hj hj' hlt
    · exact sep_symm (h j' j hj' hj hlt)
  · intro h j j' hj hj' hlt
    exact h j j' hj hj' (ne_of_lt hlt)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def AdmList (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (L : List C.Letter) : Prop :=
  (∀ j (hj : j < L.length), nodeOf (L[j]'hj) ∈ S.grid v (L.length - j) ∪ S.grid1 v) ∧ L.Pairwise Sep

/- English proof (translation)
Take `⟨⟨h1, h2⟩, -⟩` from `w.2`. Conclude with `⟨fun j hj => h1 v j hj, (pairwise_iff_idx _).2 fun j j' hj hj' hne δ hδ1 hδ2 => h2 v j j' hj hj' hne δ hδ1 hδ2⟩`.
-/
theorem admissible_list_of_word (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) : AdmList S v (w.1 v) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := w.2
  exact ⟨fun j hj => h1 v j hj, (pairwise_iff_idx _).2 fun j j' hj hj' hne δ hδ1 hδ2 => h2 v j j' hj hj' hne δ hδ1 hδ2⟩

/- English proof (translation)
Establish `h : 20 ≤ S.Ntop`. Unfold `C.HidaSetting.Ntop C.Kst`. Use linear arithmetic over natural numbers and integers. Conclude with `h` after adjusting the coercions.
-/
theorem ntop_ge (S : C.HidaSetting E Wp Wq) : (20 : ℝ) ≤ S.Ntop := by
  have h : 20 ≤ S.Ntop := by
    unfold C.HidaSetting.Ntop C.Kst
    omega
  exact_mod_cast h

/- English proof (translation)
Take `⟨hL1, hL2⟩` from `hL`. Take `⟨⟨h1, h2⟩, hc⟩` from `w.2`. Use `⟨⟨Function.update w.1 v L, ⟨⟨fun u => ?_, fun u => ?_⟩, ?_⟩⟩, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Generalize the expression as in `hM : Function.update w.1 u L u = M`. Establish `hML : M = L` using `by rw [← hM]; simp`. Substitute `hML` using the available equality. Conclude with `hL1`. Generalize the expression as in `hM : Function.update w.1 v L u = M`.

Establish `hML : M = w.1 u` using `by rw [← hM]; simp [hu]`. Substitute `hML` using the available equality. Conclude with `h1 u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Generalize the expression as in `hM : Function.update w.1 u L u = M`. Establish `hML : M = L` using `by rw [← hM]; simp`. Substitute `hML` using the available equality. Conclude with `fun j j' hj hj' hne δ hδ1 hδ2 => (pairwise_iff_idx M).1 hL2 j j' hj hj' hne δ hδ1 hδ2`. Generalize the expression as in `hM : Function.update w.1 v L u = M`.

Establish `hML : M = w.1 u` using `by rw [← hM]; simp [hu]`. Substitute `hML` using the available equality. Conclude with `h2 u`. Unfold `C.Word.cnt`. Use `Finset.sup_le fun u _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Simplify using `using hlen`. Establish `hM : Function.update w.1 v L u = w.1 u` using `by simp [hu]`. Rewrite using `[hM]`.

Conclude with `(Finset.le_sup (f := fun u => (w.1 u).length) (Finset.mem_univ u)).trans hc`.
-/
theorem admissible_at_of_admissible_list (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) (L : List C.Letter)
    (hL : AdmList S v L) (hlen : L.length ≤ S.Ntop) : D.AdmAt S v L := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨⟨h1, h2⟩, hc⟩ := w.2
  refine ⟨⟨Function.update w.1 v L, ⟨⟨fun u => ?_, fun u => ?_⟩, ?_⟩⟩, by simp⟩
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact hL1
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h1 u
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact fun j j' hj hj' hne δ hδ1 hδ2 => (pairwise_iff_idx M).1 hL2 j j' hj hj' hne δ hδ1 hδ2
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h2 u
  · unfold C.Word.cnt
    refine Finset.sup_le fun u _ => ?_
    by_cases hu : u = v
    · subst hu
      simpa using hlen
    · have hM : Function.update w.1 v L u = w.1 u := by simp [hu]
      rw [hM]
      exact (Finset.le_sup (f := fun u => (w.1 u).length) (Finset.mem_univ u)).trans hc

/- English proof (translation)
Use `⟨fun j hj => ?_, List.pairwise_append.2 ⟨hpp, ha.2, hpa⟩⟩` and prove the remaining obligations. Distinguish the cases in `hjp : j < pre.length`. Rewrite using `[List.getElem_append_left hjp, List.length_append]`. Conclude with `hpre j hjp`. Establish `hj2 : j - pre.length < a.length`.

Rewrite `hj` using `[List.length_append]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[List.getElem_append_right (by omega), List.length_append, show pre.length + a.length - j = a.length - (j - pre.length) by omega]`. Conclude with `ha.1 (j - pre.length) hj2`.
-/
theorem admissible_list_prepend (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (pre a : List C.Letter) (ha : AdmList S v a)
    (hpre : ∀ j (hj : j < pre.length), nodeOf (pre[j]'hj) ∈ S.grid v (pre.length + a.length - j) ∪ S.grid1 v)
    (hpp : pre.Pairwise Sep) (hpa : ∀ x ∈ pre, ∀ y ∈ a, Sep x y) : AdmList S v (pre ++ a) := by
  refine ⟨fun j hj => ?_, List.pairwise_append.2 ⟨hpp, ha.2, hpa⟩⟩
  by_cases hjp : j < pre.length
  · rw [List.getElem_append_left hjp, List.length_append]
    exact hpre j hjp
  · have hj2 : j - pre.length < a.length := by
      rw [List.length_append] at hj
      omega
    rw [List.getElem_append_right (by omega), List.length_append,
      show pre.length + a.length - j = a.length - (j - pre.length) by omega]
    exact ha.1 (j - pre.length) hj2

/- English proof (translation)
Take `⟨hlen, hgr, -⟩` from `hG v`. Establish `hN : (20 : ℝ) ≤ S.Ntop` using `ntop_ge S`. Take `⟨-, -, hyl, hyu⟩` from `hgr b y hy`. Take `⟨-, -, hyl', hyu'⟩` from `hgr b' y' hy'`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at he he'`.

Apply the tactic sequence `have he0 : 0 ≤ e ∧ e ≤ 1 := by rcases he with rfl | rfl <;> norm_num`. Apply the tactic sequence `have he0' : 0 ≤ e' ∧ e' ≤ 1 := by rcases he' with rfl | rfl <;> norm_num`. Unfold `C.gridL at hyl hyu hyl' hyu'`. Establish `hNpos : (0 : ℝ) < 6 * S.Ntop` using `by positivity`. Establish `hΔ : (S.Ntop : ℝ) ^ 2 + 1 ≤ (S.cutHi v - S.cutLo v) / (6 * S.Ntop)`.

Rewrite using `[le_div_iff₀ hNpos]`. Use the polynomial consequences of the given equalities and inequalities. Use `set Δ := (S.cutHi v - S.cutLo v) / (6 * S.Ntop) with hΔdef`. Establish `hΔ0 : 0 ≤ Δ` using `by nlinarith`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases.

Establish `hbb : (b : ℝ) + 1 ≤ b'` using `by exact_mod_cast hlt`. Establish `key : 2 * (b : ℝ) * Δ + 2 * Δ ≤ 2 * (b' : ℝ) * Δ` using `by nlinarith`. Conclude with `le_abs.2 (Or.inr (by linarith))`. Establish `hbb : (b' : ℝ) + 1 ≤ b` using `by exact_mod_cast hlt`. Establish `key : 2 * (b' : ℝ) * Δ + 2 * Δ ≤ 2 * (b : ℝ) * Δ` using `by nlinarith`.

Conclude with `le_abs.2 (Or.inl (by linarith))`.
-/
theorem sep_grid (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) {b b' : ℕ} {y y' : ℝ}
    (hy : y ∈ S.grid v b) (hy' : y' ∈ S.grid v b') (hne : b ≠ b') {e e' : ℝ}
    (he : e ∈ ({0, 1} : Finset ℝ)) (he' : e' ∈ ({0, 1} : Finset ℝ)) :
    (S.Ntop : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')| := by
  obtain ⟨hlen, hgr, -⟩ := hG v
  have hN : (20 : ℝ) ≤ S.Ntop := ntop_ge S
  obtain ⟨-, -, hyl, hyu⟩ := hgr b y hy
  obtain ⟨-, -, hyl', hyu'⟩ := hgr b' y' hy'
  simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
  have he0 : 0 ≤ e ∧ e ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have he0' : 0 ≤ e' ∧ e' ≤ 1 := by rcases he' with rfl | rfl <;> norm_num
  unfold C.gridL at hyl hyu hyl' hyu'
  have hNpos : (0 : ℝ) < 6 * S.Ntop := by positivity
  have hΔ : (S.Ntop : ℝ) ^ 2 + 1 ≤ (S.cutHi v - S.cutLo v) / (6 * S.Ntop) := by
    rw [le_div_iff₀ hNpos]
    nlinarith
  set Δ := (S.cutHi v - S.cutLo v) / (6 * S.Ntop) with hΔdef
  have hΔ0 : 0 ≤ Δ := by nlinarith
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hbb : (b : ℝ) + 1 ≤ b' := by exact_mod_cast hlt
    have key : 2 * (b : ℝ) * Δ + 2 * Δ ≤ 2 * (b' : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inr (by linarith))
  · have hbb : (b' : ℝ) + 1 ≤ b := by exact_mod_cast hlt
    have key : 2 * (b' : ℝ) * Δ + 2 * Δ ≤ 2 * (b : ℝ) * Δ := by nlinarith
    exact le_abs.2 (Or.inl (by linarith))

/- English proof (translation)
Apply the tactic sequence `rcases x with ⟨_ | _, p⟩ <;> simp [nodeOf]`.
-/
theorem pt_split (x : C.Letter) : x.2 = nodeOf x + (if x.1 then 0 else 1) ∧
    (if x.1 then (0 : ℝ) else 1) ∈ ({0, 1} : Finset ℝ) := by
  rcases x with ⟨_ | _, p⟩ <;> simp [nodeOf]

/- English proof (translation)
Take `⟨j, hj, rfl⟩` from `List.getElem_of_mem hz`. Break down `Finset.mem_union.1 (ha.1 j hj) with h | h` into its components or cases. Conclude with `Or.inl ⟨a.length - j, Nat.sub_le _ _, h⟩`. Conclude with `Or.inr h`.
-/
theorem nodeOf_mem_grid_or_grid1 (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (ha : AdmList S v a) (z : C.Letter)
    (hz : z ∈ a) : (∃ n, n ≤ a.length ∧ nodeOf z ∈ S.grid v n) ∨ nodeOf z ∈ S.grid1 v := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  rcases Finset.mem_union.1 (ha.1 j hj) with h | h
  · exact Or.inl ⟨a.length - j, Nat.sub_le _ _, h⟩
  · exact Or.inr h

/- English proof (translation)
Establish `h` using `ntop_ge S`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem four_lt_sq (S : C.HidaSetting E Wp Wq) : (4 : ℝ) < (S.Ntop : ℝ) ^ 2 / 8 ∧ (4 : ℝ) < (S.Ntop : ℝ) ^ 2 + 1 := by
  have h := ntop_ge S
  constructor <;> nlinarith

/- English proof (translation)
Establish `hz'` using `(pt_split z).1`. Establish `he'` using `(pt_split z).2`. Break down `nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode` into its components or cases. Establish `h` using `sep_grid S hG v hy hnode (by omega) he he'`. Rewrite using `[hz']`.

Combine the linear relations using `[(four_lt_sq S).2]`. Establish `h` using `(hG v).2.2.2.2.1 (nodeOf z) hnode B y hy _ he' e he`. Rewrite using `[hz', abs_sub_comm]`. Combine the linear relations using `[(four_lt_sq S).2]`.
-/
theorem grid_point_far_from_letters (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {B : ℕ} {y : ℝ} (hy : y ∈ S.grid v B) (hB : a.length < B) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by
  have hz' := (pt_split z).1
  have he' := (pt_split z).2
  rcases nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode
  · have h := sep_grid S hG v hy hnode (by omega) he he'
    rw [hz']
    linarith [(four_lt_sq S).2]
  · have h := (hG v).2.2.2.2.1 (nodeOf z) hnode B y hy _ he' e he
    rw [hz', abs_sub_comm]
    linarith [(four_lt_sq S).2]

/- English proof (translation)
Establish `hz'` using `(pt_split z).1`. Establish `he'` using `(pt_split z).2`. Break down `nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode` into its components or cases. Establish `h` using `(hG v).2.2.2.2.1 y hy n (nodeOf z) hnode e he _ he'`. Rewrite using `[hz']`.

Combine the linear relations using `[(four_lt_sq S).2]`. Establish `hne : y ≠ nodeOf z` using `fun h => hyn (by rw [h]; exact List.mem_map.2 ⟨z, hz, rfl⟩)`. Establish `h` using `(hG v).2.2.2.1 y hy (nodeOf z) hnode hne e he _ he'`. Rewrite using `[hz']`. Combine the linear relations using `[(four_lt_sq S).1]`.
-/
theorem grid1_point_far_from_letters (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {y : ℝ} (hy : y ∈ S.grid1 v) (hyn : y ∉ a.map nodeOf) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by
  have hz' := (pt_split z).1
  have he' := (pt_split z).2
  rcases nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode
  · have h := (hG v).2.2.2.2.1 y hy n (nodeOf z) hnode e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).2]
  · have hne : y ≠ nodeOf z := fun h => hyn (by rw [h]; exact List.mem_map.2 ⟨z, hz, rfl⟩)
    have h := (hG v).2.2.2.1 y hy (nodeOf z) hnode hne e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).1]

/- English proof (translation)
Take `⟨w, hw⟩` from `haA`. Establish `ha : AdmList S v a` using `by rw [← hw]; exact admissible_list_of_word S w v`. Establish `hcut : ∀ y, ((∃ n, y ∈ S.grid v n) ∨ y ∈ S.grid1 v) → ∀ e ∈ ({0, 1} : Finset ℝ), I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) (y + e)`. Introduce `y hy e he`. Take `⟨h1, h2, -⟩` from `(hG v).2.2.2.2.2 y hy`.

Take `⟨h1a, h1b⟩` from `h1`. Take `⟨h2a, h2b⟩` from `h2`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at he`. Apply `hC v` to reduce the goal to its premises. Rewrite using `[Set.mem_Icc]`.

Unfold `C.HidaSetting.cutLo C.HidaSetting.cutHi`. Apply the tactic sequence `rcases he with rfl | rfl <;> constructor <;> linarith`. Establish `hLcut : ∀ L, AdmList S v L → KB.CutWord (D.parOf S v) (S.l + 1) L`. Introduce `L hL`. Use `(cutWord_iff _ _ L).2 ⟨fun x hx => ?_, hL.2.imp fun h => ?_⟩` and prove the remaining obligations.

Take `⟨j, hj, rfl⟩` from `List.getElem_of_mem hx`. Rewrite using `[(pt_split _).1]`. Use `hcut _ ?_ _ (pt_split _).2` and prove the remaining obligations. Break down `Finset.mem_union.1 (hL.1 j hj) with h | h` into its components or cases. Conclude with `Or.inl ⟨_, h⟩`.

Conclude with `Or.inr h`. Establish `h0` using `h 0 (by norm_num) (by norm_num)`. Simplify using `using h0`. Establish `hP : AdmList S v (KB.plusW ys a)`. Rewrite using `[plusW_eq]`.

Use `admissible_list_prepend S v _ a ha ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Establish `hj' : j < ys.length` using `by simpa using hj`. Simplify `H3 j hj'` using `[nodeOf]`. Rewrite using `[List.pairwise_map]`.

Conclude with `H1.imp fun h => sep_of_four h`. Introduce `x hx z hz`. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hx`. Conclude with `sep_of_four (by simpa using (H2 y hy z hz).1)`. Establish `hM : AdmList S v (KB.minusW ys a)`.

Rewrite using `[minusW_eq]`. Use `admissible_list_prepend S v _ a ha ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Establish `hj' : j < ys.length` using `by simpa using hj`. Simplify `H3 j hj'` using `[nodeOf]`.

Rewrite using `[List.pairwise_map]`. Conclude with `H1.imp fun h => sep_of_four (by simpa using h)`. Introduce `x hx z hz`. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hx`. Conclude with `sep_of_four (by simpa using (H2 y hy z hz).2)`.

Establish `hlenP : (KB.plusW ys a).length ≤ S.Ntop` using `by rw [plusW_eq]; simpa using hlen`. Establish `hlenM : (KB.minusW ys a).length ≤ S.Ntop` using `by rw [minusW_eq]; simpa using hlen`. Conclude with `⟨admissible_at_of_admissible_list S w v _ hP hlenP, admissible_at_of_admissible_list S w v _ hM hlenM, hLcut _ hP, hLcut _ hM⟩`.
-/
theorem extend (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (v : Fin S.f) (a : List C.Letter)
    (haA : D.AdmAt S v a) (ys : List ℝ) (H1 : ys.Pairwise fun y y' => 4 < |y - y'|)
    (H2 : ∀ y ∈ ys, ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2|)
    (H3 : ∀ i (hi : i < ys.length), ys[i] ∈ S.grid v (ys.length + a.length - i) ∪ S.grid1 v)
    (hlen : ys.length + a.length ≤ S.Ntop) :
    D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) := by
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := by rw [← hw]; exact admissible_list_of_word S w v
  have hcut : ∀ y, ((∃ n, y ∈ S.grid v n) ∨ y ∈ S.grid1 v) → ∀ e ∈ ({0, 1} : Finset ℝ),
      I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) (y + e) := by
    intro y hy e he
    obtain ⟨h1, h2, -⟩ := (hG v).2.2.2.2.2 y hy
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    apply hC v
    rw [Set.mem_Icc]
    unfold C.HidaSetting.cutLo C.HidaSetting.cutHi
    rcases he with rfl | rfl <;> constructor <;> linarith
  have hLcut : ∀ L, AdmList S v L → KB.CutWord (D.parOf S v) (S.l + 1) L := by
    intro L hL
    refine (cutWord_iff _ _ L).2 ⟨fun x hx => ?_, hL.2.imp fun h => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [(pt_split _).1]
      refine hcut _ ?_ _ (pt_split _).2
      rcases Finset.mem_union.1 (hL.1 j hj) with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    · have h0 := h 0 (by norm_num) (by norm_num)
      simpa using h0
  have hP : AdmList S v (KB.plusW ys a) := by
    rw [plusW_eq]
    refine admissible_list_prepend S v _ a ha ?_ ?_ ?_
    · intro j hj
      have hj' : j < ys.length := by simpa using hj
      simpa [nodeOf] using H3 j hj'
    · rw [List.pairwise_map]
      exact H1.imp fun h => sep_of_four h
    · intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact sep_of_four (by simpa using (H2 y hy z hz).1)
  have hM : AdmList S v (KB.minusW ys a) := by
    rw [minusW_eq]
    refine admissible_list_prepend S v _ a ha ?_ ?_ ?_
    · intro j hj
      have hj' : j < ys.length := by simpa using hj
      simpa [nodeOf] using H3 j hj'
    · rw [List.pairwise_map]
      exact H1.imp fun h => sep_of_four (by simpa using h)
    · intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact sep_of_four (by simpa using (H2 y hy z hz).2)
  have hlenP : (KB.plusW ys a).length ≤ S.Ntop := by rw [plusW_eq]; simpa using hlen
  have hlenM : (KB.minusW ys a).length ≤ S.Ntop := by rw [minusW_eq]; simpa using hlen
  exact ⟨admissible_at_of_admissible_list S w v _ hP hlenP, admissible_at_of_admissible_list S w v _ hM hlenM, hLcut _ hP, hLcut _ hM⟩

end

section new

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Unfold `F7.lagCo`. Conclude with `Finset.prod_ne_zero_iff.2 fun i hi => inv_ne_zero (sub_ne_zero.2 fun h => Finset.ne_of_mem_erase hi (hy h).symm)`.
-/
theorem lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  exact Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero (sub_ne_zero.2 fun h => Finset.ne_of_mem_erase hi (hy h).symm)

/- English proof (translation)
Unfold `F7.thGrid`. Conclude with `Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)`.
-/
theorem thGrid_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) :
    0 ≤ F7.thGrid grid j := by
  unfold F7.thGrid
  exact Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)

/- English proof (translation)
Unfold `F7.thGrid`. Establish `h` using `Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin (d + 1)))) (fun a i => |F7.lagCo (grid a) i| / ∑ i, |F7.lagCo (grid a) i|)`. Rewrite `h` using `[Fintype.piFinset_univ]`. Rewrite using `[← h]`. Use `Finset.prod_eq_one fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_div, div_self]`. Establish `h0 : 0 < |F7.lagCo (grid b) 0|` using `abs_pos.2 (lagCo_ne_zero _ (hinj b) 0)`. Conclude with `(Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨0, Finset.mem_univ _, h0⟩).ne'`.
-/
theorem thGrid_sum {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    ∑ j, F7.thGrid grid j = 1 := by
  unfold F7.thGrid
  have h := Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin (d + 1))))
    (fun a i => |F7.lagCo (grid a) i| / ∑ i, |F7.lagCo (grid a) i|)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← Finset.sum_div, div_self]
  have h0 : 0 < |F7.lagCo (grid b) 0| := abs_pos.2 (lagCo_ne_zero _ (hinj b) 0)
  exact (Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨0, Finset.mem_univ _, h0⟩).ne'

/- English proof (translation)
Use `⟨⟨fun a => ?_, fun a ha => ?_, ?_⟩, fun a ha => ?_⟩` and prove the remaining obligations. Unfold `pushTh`. Conclude with `Finset.sum_nonneg fun j _ => by split_ifs exacts [thGrid_nonneg grid j, le_refl 0]`. Unfold `pushTh`. Use `Finset.sum_eq_zero fun j _ => if_neg fun h => ha ?_` and prove the remaining obligations.

Rewrite using `[← h]`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ j)`. Unfold `pushTh`. Rewrite using `[Finset.sum_comm, ← thGrid_sum grid hinj]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_ite_eq, if_pos (by unfold pushU; exact Finset.mem_image_of_mem _ (Finset.mem_univ j))]`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `hmk j`.
-/
theorem locProb_push (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (n' : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (mk : List ℝ → List C.Letter)
    (hmk : ∀ j : Fin K → Fin (d + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (j b))) ∧
      (mk (List.ofFn fun b => grid b (j b))).length ≤ n') :
    KB.LocProb S v n' (pushU grid mk) (pushTh grid mk) := by
  classical
  refine ⟨⟨fun a => ?_, fun a ha => ?_, ?_⟩, fun a ha => ?_⟩
  · unfold pushTh
    exact Finset.sum_nonneg fun j _ => by
      split_ifs
      exacts [thGrid_nonneg grid j, le_refl 0]
  · unfold pushTh
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ha ?_
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · unfold pushTh
    rw [Finset.sum_comm, ← thGrid_sum grid hinj]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq, if_pos (by unfold pushU; exact Finset.mem_image_of_mem _ (Finset.mem_univ j))]
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact hmk j

end new

end

def NewLetters : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K n : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop → n ≤ 2 * S.G.r →
    KB.CutWord (D.parOf S v) (S.l + 1) a ∧
    ∃ grid : Fin K → Fin (n + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ j, |F7.lagCo (grid b) j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n) ∧
      (∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ))) ∧
      (∀ j : Fin K → Fin (n + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'|) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.plusW ys a) (pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.minusW ys a) (pushTh grid fun ys => KB.minusW ys a)

def NewLetters1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop →
    ∃ ys : List ℝ, ys.length = K ∧ ys.Nodup ∧ (∀ y ∈ ys, y ∈ S.grid1 v) ∧
      D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) ∧
      ys.Pairwise fun y y' => 4 < |y - y'|

/- English proof (translation)
Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K n haA hlen hn`. Take `⟨w, hw⟩` from `haA`. Establish `ha : AdmList S v a` using `hw ▸ admissible_list_of_word S w v`. Use `⟨hw ▸ cutWord_of_adm S hG hC w v, ?_⟩` and prove the remaining obligations. Establish `hex : ∀ b : Fin K, ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧ (∀ j, y j ∈ S.grid v (a.length + K - (b : ℕ))) ∧ ∑ j, |F7.lagCo y j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n` using `fun b => (hR v).2 _ (by omega) (by omega) n hn`.

Use `choose grid hinj hmem hbd using hex`. Establish `h4` using `four_lt_sq S`. Establish `key : ∀ j : Fin K → Fin (n + 1), D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧ D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.m …`. Introduce `j`. Establish `H1 : (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'|`.

Rewrite using `[List.pairwise_ofFn]`. Introduce `i i' hii'`. Establish `hlt : (i : ℕ) < i'` using `hii'`. Establish `hi` using `i.isLt`. Establish `hi'` using `i'.isLt`.

Use `sep_grid S hG v (hmem i (j i)) (hmem i' (j i')) (by omega) (e := 0) (e' := 0) (by simp) (by simp)` as an intermediate fact. Simplify using `only [add_zero] at this`. Combine the linear relations using `[h4.2]`. Establish `H2 : ∀ y ∈ List.ofFn (fun b => grid b (j b)), ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2|`. Introduce `y hy z hz`.

Take `⟨i, hi, rfl⟩` from `List.getElem_of_mem hy`. Establish `hiK : i < K` using `by simpa using hi`. Rewrite using `[List.getElem_ofFn]`. Establish `hB : a.length < a.length + K - ((⟨i, hiK⟩ : Fin K) : ℕ)` using `by show a.length < a.length + K - i; omega`. Conclude with `⟨grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp), grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp)⟩`.

Establish `H3 : ∀ i (hi : i < (List.ofFn fun b => grid b (j b)).length), (List.ofFn fun b => grid b (j b))[i] ∈ S.grid v ((List.ofFn fun b => grid b (j b)).length + a.length - i) ∪ S.grid1 v`. Introduce `i hi`. Rewrite using `[List.getElem_ofFn]`. Use `Finset.mem_union_left _ ?_` and prove the remaining obligations. Use `hmem ⟨i, by simpa using hi⟩ (j ⟨i, by simpa using hi⟩)` as an intermediate fact.

Simplify `this` using `[Nat.add_comm]`. Take `⟨e1, e2, e3, e4⟩` from `extend S hG hC v a ⟨w, hw⟩ _ H1 H2 H3 (by simp; omega)`. Conclude with `⟨e1, e2, e3, e4, H1⟩`. Use `⟨grid, hinj, hbd, hmem, key, ?_, ?_⟩` and prove the remaining obligations. Conclude with `locProb_push S v _ grid hinj _ fun j => ⟨(key j).1, by rw [plusW_eq]; simp; omega⟩`.

Conclude with `locProb_push S v _ grid hinj _ fun j => ⟨(key j).2.1, by rw [minusW_eq]; simp; omega⟩`.
-/
theorem newLetters : NewLetters := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K n haA hlen hn
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := hw ▸ admissible_list_of_word S w v
  refine ⟨hw ▸ cutWord_of_adm S hG hC w v, ?_⟩
  have hex : ∀ b : Fin K, ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧
      (∀ j, y j ∈ S.grid v (a.length + K - (b : ℕ))) ∧
      ∑ j, |F7.lagCo y j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n :=
    fun b => (hR v).2 _ (by omega) (by omega) n hn
  choose grid hinj hmem hbd using hex
  have h4 := four_lt_sq S
  have key : ∀ j : Fin K → Fin (n + 1),
      D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
      D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
      (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'| := by
    intro j
    have H1 : (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'| := by
      rw [List.pairwise_ofFn]
      intro i i' hii'
      have hlt : (i : ℕ) < i' := hii'
      have hi := i.isLt
      have hi' := i'.isLt
      have := sep_grid S hG v (hmem i (j i)) (hmem i' (j i')) (by omega) (e := 0) (e' := 0) (by simp) (by simp)
      simp only [add_zero] at this
      linarith [h4.2]
    have H2 : ∀ y ∈ List.ofFn (fun b => grid b (j b)), ∀ z ∈ a, 4 < |(y + 0) - z.2| ∧ 4 < |(y + 1) - z.2| := by
      intro y hy z hz
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hiK : i < K := by simpa using hi
      rw [List.getElem_ofFn]
      have hB : a.length < a.length + K - ((⟨i, hiK⟩ : Fin K) : ℕ) := by show a.length < a.length + K - i; omega
      exact ⟨grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp),
        grid_point_far_from_letters S hG v a ha (hmem ⟨i, hiK⟩ (j ⟨i, hiK⟩)) hB z hz (by simp)⟩
    have H3 : ∀ i (hi : i < (List.ofFn fun b => grid b (j b)).length),
        (List.ofFn fun b => grid b (j b))[i] ∈
          S.grid v ((List.ofFn fun b => grid b (j b)).length + a.length - i) ∪ S.grid1 v := by
      intro i hi
      rw [List.getElem_ofFn]
      refine Finset.mem_union_left _ ?_
      have := hmem ⟨i, by simpa using hi⟩ (j ⟨i, by simpa using hi⟩)
      simpa [Nat.add_comm] using this
    obtain ⟨e1, e2, e3, e4⟩ := extend S hG hC v a ⟨w, hw⟩ _ H1 H2 H3 (by simp; omega)
    exact ⟨e1, e2, e3, e4, H1⟩
  refine ⟨grid, hinj, hbd, hmem, key, ?_, ?_⟩
  · exact locProb_push S v _ grid hinj _ fun j => ⟨(key j).1, by rw [plusW_eq]; simp; omega⟩
  · exact locProb_push S v _ grid hinj _ fun j => ⟨(key j).2.1, by rw [minusW_eq]; simp; omega⟩

/- English proof (translation)
Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K haA hlen`. Take `⟨w, hw⟩` from `haA`. Establish `ha : AdmList S v a` using `by rw [← hw]; exact admissible_list_of_word S w v`. Establish `hT1 : K ≤ (S.grid1 v \ (a.map nodeOf).toFinset).card`. Establish `h1` using `Finset.le_card_sdiff ((a.map nodeOf).toFinset) (S.grid1 v)`.

Establish `h2` using `List.toFinset_card_le (a.map nodeOf)`. Establish `h3` using `(hR v).1`. Rewrite `h2` using `[List.length_map]`. Use linear arithmetic over natural numbers and integers. Take `⟨U, hUT, hUc⟩` from `Finset.exists_subset_card_eq hT1`.

Establish `hmem : ∀ y ∈ U.toList, y ∈ S.grid1 v ∧ y ∉ a.map nodeOf`. Introduce `y hy`. Establish `h` using `hUT (Finset.mem_toList.1 hy)`. Rewrite `h` using `[Finset.mem_sdiff, List.mem_toFinset]`. Conclude with `h`.

Establish `hpw : U.toList.Pairwise fun y y' => 4 < |y - y'|`. Use `U.nodup_toList.pairwise_of_forall_ne fun y hy y' hy' hne => ?_` and prove the remaining obligations. Establish `h` using `(hG v).2.2.2.1 y (hmem y hy).1 y' (hmem y' hy').1 hne 0 (by simp) 0 (by simp)`. Simplify using `only [add_zero] at h`. Combine the linear relations using `[(four_lt_sq S).1]`.

Establish `hlen2 : U.toList.length + a.length ≤ S.Ntop`. Rewrite using `[Finset.length_toList, hUc]`. Use linear arithmetic over natural numbers and integers. Take `⟨h1, h2, h3, h4⟩` from `extend S hG hC v a ⟨w, hw⟩ U.toList hpw (fun y hy z hz => ⟨grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp), grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp)⟩) (fun i hi => Finset.mem_union_right _ (hmem _ (Lis …`. Conclude with `⟨U.toList, by rw [Finset.length_toList, hUc], U.nodup_toList, fun y hy => (hmem y hy).1, h1, h2, h3, h4, hpw⟩`.
-/
theorem newLetters1 : NewLetters1 := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S hG hR hC v a K haA hlen
  classical
  obtain ⟨w, hw⟩ := haA
  have ha : AdmList S v a := by rw [← hw]; exact admissible_list_of_word S w v
  have hT1 : K ≤ (S.grid1 v \ (a.map nodeOf).toFinset).card := by
    have h1 := Finset.le_card_sdiff ((a.map nodeOf).toFinset) (S.grid1 v)
    have h2 := List.toFinset_card_le (a.map nodeOf)
    have h3 := (hR v).1
    rw [List.length_map] at h2
    omega
  obtain ⟨U, hUT, hUc⟩ := Finset.exists_subset_card_eq hT1
  have hmem : ∀ y ∈ U.toList, y ∈ S.grid1 v ∧ y ∉ a.map nodeOf := by
    intro y hy
    have h := hUT (Finset.mem_toList.1 hy)
    rw [Finset.mem_sdiff, List.mem_toFinset] at h
    exact h
  have hpw : U.toList.Pairwise fun y y' => 4 < |y - y'| := by
    refine U.nodup_toList.pairwise_of_forall_ne fun y hy y' hy' hne => ?_
    have h := (hG v).2.2.2.1 y (hmem y hy).1 y' (hmem y' hy').1 hne 0 (by simp) 0 (by simp)
    simp only [add_zero] at h
    linarith [(four_lt_sq S).1]
  have hlen2 : U.toList.length + a.length ≤ S.Ntop := by
    rw [Finset.length_toList, hUc]
    omega
  obtain ⟨h1, h2, h3, h4⟩ := extend S hG hC v a ⟨w, hw⟩ U.toList hpw
    (fun y hy z hz => ⟨grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp),
      grid1_point_far_from_letters S hG v a ha (hmem y hy).1 (hmem y hy).2 z hz (by simp)⟩)
    (fun i hi => Finset.mem_union_right _ (hmem _ (List.getElem_mem hi)).1) hlen2
  exact ⟨U.toList, by rw [Finset.length_toList, hUc], U.nodup_toList, fun y hy => (hmem y hy).1, h1, h2, h3, h4,
    hpw⟩

end Formalism.FourierDecayAlt.P.PBD

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBD.newLetters`.
-/
theorem Formalism.FourierDecayAlt.P.new_letters_admissible : Formalism.FourierDecayAlt.P.PBD.NewLetters := Formalism.FourierDecayAlt.P.PBD.newLetters
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBD.newLetters1`.
-/
theorem Formalism.FourierDecayAlt.P.new_letters_admissible_level_one : Formalism.FourierDecayAlt.P.PBD.NewLetters1 := Formalism.FourierDecayAlt.P.PBD.newLetters1
