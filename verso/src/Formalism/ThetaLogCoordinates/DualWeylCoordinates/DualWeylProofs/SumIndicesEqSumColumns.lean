import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LWedge

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_E (lo : ℤ) (N : ℕ) (F : ℤ → Finset (Fin n)) : Fin N → Finset (Fin n) := fun j => F (lo + 1 + (j : ℕ))

/- English proof (translation)
Use `symm`. Use `Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j _`. Use `j.2` as an intermediate fact. Simplify using `only [mem_Ioc]`.

Use linear arithmetic over natural numbers and integers. Introduce `i _ j _ h`. Use `ext`. Use linear arithmetic over natural numbers and integers. Introduce `c hc`.

Simplify using `only [mem_Ioc] at hc`. Conclude with `⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩`. Introduce `j _`. Both sides reduce to the same expression.
-/
lemma ql_prod_Ioc {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by
  symm
  refine Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_
  · intro j _; have := j.2; simp only [mem_Ioc]; omega
  · intro i _ j _ h; ext; omega
  · intro c hc
    simp only [mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩
  · intro j _; rfl

def ql_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : lo < c ∧ c ≤ lo + N then f ⟨(c - lo - 1).toNat, by omega⟩ else if c ≤ lo then univ else ∅

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `j.2` as an intermediate fact. Simplify using `only [ql_E, ql_fill]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Use `congr 1`.

Use `ext`. Use `show (lo + 1 + (j : ℕ) - lo - 1).toNat = j`. Use linear arithmetic over natural numbers and integers.
-/
lemma ql_E_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by
  funext j
  have := j.2
  simp only [ql_E, ql_fill]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  show (lo + 1 + (j : ℕ) - lo - 1).toNat = j
  omega

/- English proof (translation)
Use `Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `L hL`. Conclude with `hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩`.
-/
lemma ql_sum_L {M : Type*} [AddCommMonoid M] {b : ℕ} (φ : Finset (Fin n) → M) (hφ : ∀ L, L.card ≠ b → φ L = 0) :
    ∑ L : LamIdx n b, φ L.1 = ∑ L, φ L := by
  refine Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro L hL
  exact hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩

variable [NeZero n]

/- English proof (translation)
Unfold `ql_fill`. Use `split_ifs with h h'`. Rewrite using `[hf]`. Use `congr 1 show lo + 1 + ((c - lo - 1).toNat : ℤ) = c`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[qs_colH_low hmu (h'.trans h1)]`. Simplify using the standard rewrite rules. Rewrite using `[qs_colH_high hmu (by omega)]; simp`.
-/
lemma ql_fill_card {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by
  unfold ql_fill
  split_ifs with h h'
  · rw [hf]; congr 1
    show lo + 1 + ((c - lo - 1).toNat : ℤ) = c
    omega
  · rw [qs_colH_low hmu (h'.trans h1)]; simp
  · rw [qs_colH_high hmu (by omega)]; simp

/- English proof (translation)
The claim follows from `qs_ext_card hmu I _`.
-/
lemma ql_E_card {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := qs_ext_card hmu I _

/- English proof (translation)
Use `Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `I I' h`. Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← qs_ext_mem, ← qs_ext_mem]`.

Establish `hc` using `c.2`. Simplify using `only [TCols, mem_Ioc] at hc`. Use `congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩` as an intermediate fact. Establish `e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1` using `by omega`. Simplify using `only [ql_E, e] at this`.

Conclude with `this`. Introduce `f hf`. Apply `hφ` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by`. Simplify using `only [qs_ext_res hmu, ql_E_fill]⟩`.
-/
lemma sum_indices_eq_sum_columns {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by
  refine Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)
  · intro I I' h
    funext c
    apply Subtype.ext
    rw [← qs_ext_mem, ← qs_ext_mem]
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have := congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩
    have e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1 := by omega
    simp only [ql_E, e] at this
    exact this
  · intro f hf
    apply hφ
    by_contra hc
    push Not at hc
    exact hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by
      simp only [qs_ext_res hmu, ql_E_fill]⟩

/- English proof (translation)
Rewrite using `[qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]`. Both sides reduce to the same expression.
-/
lemma ql_TMat {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by
  rw [qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]; rfl

/- English proof (translation)
Rewrite using `[qs_ext_can hmu, ← qb_lt_colH_iff hmu]`. Simplify using `[qs_ini]`.
-/
lemma ql_mem_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by
  rw [qs_ext_can hmu, ← qb_lt_colH_iff hmu]; simp [qs_ini]

end Formalism.InvariantFactorPaths.ColumnFamilies
