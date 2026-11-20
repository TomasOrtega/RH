import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.Twist (app_resM)

/- English proof (translation)
The claim follows from `Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ (fun j hj => hg j (by by_contra h exact hj ⟨⟨j, by omega⟩, rfl⟩)) fun _ => rfl`.
-/
theorem sum_castLE_eq {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, l ≤ (j : ℕ) → g j = 0) :
    ∑ k : Fin l, g (Fin.castLE hl k) = ∑ j, g j :=
  Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _
    (fun j hj => hg j (by
      by_contra h
      exact hj ⟨⟨j, by omega⟩, rfl⟩)) fun _ => rfl

/- English proof (translation)
Establish `hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U`. Use `(hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by` as an intermediate fact. Rewrite using `[Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Simplify using `at hj`.

Use linear arithmetic over natural numbers and integers. Simplify `this` using `[Pi.single_apply, Finset.sum_ite_eq']`. Set `e : Fin l → Γ(P.toMod, U)` to `fun k => P.mkSec _ (hmem k)`. Establish `hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) : P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) = ∑ k, b k • resM F h (c (Fin.castLE hl k))`. Rewrite using `[Fintype.linearCombination_apply, ← appLinear_apply, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, appLinear_apply, app_resM]`. Both sides reduce to the same expression. Set `ext (V : X.Opens) (b : Fin l → Γ(X, V)) : Fin N → Γ(X, V)` to `fun j => if hj : (j : ℕ) < l then b ⟨j, hj⟩ else 0`. Establish `hext0 (V : X.Opens) (b : Fin l → Γ(X, V)) (j : Fin N) (hj : l ≤ (j : ℕ)) : ext V b j = 0` using `dif_neg (by omega)`.

Establish `hextk (V : X.Opens) (b : Fin l → Γ(X, V)) (k : Fin l) : ext V b (Fin.castLE hl k) = b k` using `dif_pos k.2`. Establish `hsum (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)) (ha : ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) : ∑ k : Fin l, a (Fin.castLE hl k) • resM F h (c (Fin.castLE hl k)) = ∑ j, a j • resM F h (c j)` using `sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [ha j hj, zero_smul]`. Use `⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg (P.incl.app V) hbb`. Rewrite `h1` using `[hincl, hincl]`.

Establish `h2 : Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b) = Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b')`. Rewrite using `[Fintype.linearCombination_apply, Fintype.linearCombination_apply, ← hsum V h _ (hext0 V b), ← hsum V h _ (hext0 V b')]`. Simplify `h1` using `only [hextk]`. Use function extensionality and compare the values at `k`. Rewrite using `[← hextk V b k, ← hextk V b' k, (hc V h).1 h2]`.

Take `⟨a, ha⟩` from `(hc V h).2 (P.incl.app V s)`. Rewrite `ha` using `[Fintype.linearCombination_apply]`. Establish `hz` using `(hP V h a).1 (ha ▸ P.incl_app_mem s)`. Use `⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩` and prove the remaining obligations. Rewrite using `[hincl, hsum V h a hz, ha]`.
-/
theorem exists_isFrame_sub_of_vanishing {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ}
    (P : VB.Sub F) (c : Fin N → Γ(F, U)) (hc : VB.IsFrame c) (l : ℕ) (hl : l ≤ N)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
    ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e := by
  classical

  have hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      simp at hj
      omega
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  let e : Fin l → Γ(P.toMod, U) := fun k => P.mkSec _ (hmem k)

  have hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) :
      P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) =
        ∑ k, b k • resM F h (c (Fin.castLE hl k)) := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    rfl

  let ext (V : X.Opens) (b : Fin l → Γ(X, V)) : Fin N → Γ(X, V) :=
    fun j => if hj : (j : ℕ) < l then b ⟨j, hj⟩ else 0
  have hext0 (V : X.Opens) (b : Fin l → Γ(X, V)) (j : Fin N) (hj : l ≤ (j : ℕ)) : ext V b j = 0 :=
    dif_neg (by omega)
  have hextk (V : X.Opens) (b : Fin l → Γ(X, V)) (k : Fin l) : ext V b (Fin.castLE hl k) = b k :=
    dif_pos k.2
  have hsum (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V))
      (ha : ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
      ∑ k : Fin l, a (Fin.castLE hl k) • resM F h (c (Fin.castLE hl k)) =
        ∑ j, a j • resM F h (c j) :=
    sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [ha j hj, zero_smul]
  refine ⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩⟩
  · have h1 := congrArg (P.incl.app V) hbb
    rw [hincl, hincl] at h1
    have h2 : Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b) =
        Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b') := by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply,
        ← hsum V h _ (hext0 V b), ← hsum V h _ (hext0 V b')]
      simpa only [hextk] using h1
    funext k
    rw [← hextk V b k, ← hextk V b' k, (hc V h).1 h2]
  · obtain ⟨a, ha⟩ := (hc V h).2 (P.incl.app V s)
    rw [Fintype.linearCombination_apply] at ha
    have hz := (hP V h a).1 (ha ▸ P.incl_app_mem s)
    refine ⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩
    rw [hincl, hsum V h a hz, ha]

end GlobalTheory.VB
