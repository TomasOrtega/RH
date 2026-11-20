import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison
open GlobalTheory.CatH (face toLast)

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CatPrism

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

def cyl {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) : Fin 2 × C' ⥤ C := Functor.uncurry.obj (ComposableArrows.mk₁ α)

/- English proof (translation)
Simplify using `[cyl]`. Conclude with `(Category.id_comp _).symm`.
-/
theorem cyl_top {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {T T' : C'} (φ : T ⟶ T') :
    G₂.map φ = (cyl α).map ((𝟙 (Fin.last 1), φ) : (Fin.last 1, T) ⟶ (Fin.last 1, T')) := by
  simp [cyl]
  exact (Category.id_comp _).symm

/- English proof (translation)
Simplify using `[cyl]`. Conclude with `(Category.id_comp _).symm`.
-/
theorem cyl_bot {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {T T' : C'} (φ : T ⟶ T') :
    G₁.map φ = (cyl α).map ((𝟙 (0 : Fin 2), φ) : ((0 : Fin 2), T) ⟶ ((0 : Fin 2), T')) := by
  simp [cyl]
  exact (Category.id_comp _).symm

/- English proof (translation)
Simplify using `[cyl]`.
-/
theorem cyl_step {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (T : C') :
    α.app T = (cyl α).map ((homOfLE (Fin.zero_le _), 𝟙 T) : ((0 : Fin 2), T) ⟶ (Fin.last 1, T)) := by
  simp [cyl]

variable {n p : ℕ}

/- English proof (translation)
Rewrite using `[F.map_comp]`. Both sides reduce to the same expression.
-/
theorem map_map {X Y Z : C} (F : C ⥤ ModuleCat.{w} R) (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : F.obj X) :
    (F.map ψ).hom ((F.map φ).hom x) = (F.map (φ ≫ ψ)).hom x := by
  rw [F.map_comp]; rfl

def chain {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) (s : ComposableArrows C' n) : ComposableArrows C p :=
  (ha.functor.prod' (ht.functor ⋙ s)) ⋙ cyl α

def up (s : ComposableArrows C' n) (b : Fin 2) (c : Fin (n + 1)) :
    (b, s.obj c) ⟶ (Fin.last 1, s.obj (Fin.last n)) :=
  (homOfLE (Fin.le_last b), s.map (homOfLE (Fin.le_last c)))

variable (m₂ : CH.Mor F F' σ) {G₁ : C' ⥤ C} (α : G₁ ⟶ m₂.G)

def val (s : ComposableArrows C' n) (f : CH.Cn F p) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) : F'.obj (s.obj (Fin.last n)) :=
  m₂.τ _ ((F.map ((cyl α).map (up s (a (Fin.last p)) (t (Fin.last p))))).hom (f (chain α ha ht s)))

/- English proof (translation)
Substitute `h h'` using the available equality. Both sides reduce to the same expression.
-/
theorem val_congr (s : ComposableArrows C' n) (f : CH.Cn F p) {a a' : Fin (p + 1) → Fin 2} {t t' : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) (ha' : Monotone a') (ht' : Monotone t') (h : a = a') (h' : t = t') :
    val m₂ α s f ha ht = val m₂ α s f ha' ht' := by
  subst h h'; rfl

/- English proof (translation)
Establish `e : (cyl α).map (up (face j s) (a (Fin.last p)) (t (Fin.last p))) ≫ m₂.G.map (toLast j s) = (cyl α).map (up s (a (Fin.last p)) (j.succAbove (t (Fin.last p))))`. Rewrite using `[cyl_top α, ← Functor.map_comp]`. Use `congr 1`. Use `Prod.ext (Subsingleton.elim _ _) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s.map _ ≫ s.map _ = s.map _`.

Rewrite using `[← s.map_comp]`. Both sides reduce to the same expression. Unfold `val`. Rewrite using `[← m₂.nat]`. Conclude with `congrArg (m₂.τ _) ((map_map F _ _ _).trans (congrArg (fun q => (F.map q).hom (f (chain α ha ht (face j s)))) e))`.
-/
theorem val_face (s : ComposableArrows C' (n + 1)) (f : CH.Cn F p) (j : Fin (n + 2)) {a : Fin (p + 1) → Fin 2}
    {t : Fin (p + 1) → Fin (n + 1)} (ha : Monotone a) (ht : Monotone t) :
    (F'.map (toLast j s)).hom (val m₂ α (face j s) f ha ht) =
      val m₂ α s f ha ((Fin.strictMono_succAbove j).monotone.comp ht) := by
  have e : (cyl α).map (up (face j s) (a (Fin.last p)) (t (Fin.last p))) ≫ m₂.G.map (toLast j s) =
      (cyl α).map (up s (a (Fin.last p)) (j.succAbove (t (Fin.last p)))) := by
    rw [cyl_top α, ← Functor.map_comp]
    congr 1
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change s.map _ ≫ s.map _ = s.map _
    rw [← s.map_comp]; rfl
  unfold val
  rw [← m₂.nat]
  exact congrArg (m₂.τ _) ((map_map F _ _ _).trans
    (congrArg (fun q => (F.map q).hom (f (chain α ha ht (face j s)))) e))

/- English proof (translation)
Establish `e : ∀ k : Fin (p + 2), toLast k (chain α ha ht s) ≫ (cyl α).map (up s (a (Fin.last (p + 1))) (t (Fin.last (p + 1)))) = (cyl α).map (up s (a (k.succAbove (Fin.last p))) (t (k.succAbove (Fin.last p))))`. Introduce `k`. Express the relevant statement in the definitionally equal form `(cyl α).map _ ≫ _ = _`. Rewrite using `[← Functor.map_comp]`. Use `congr 1`.

Use `Prod.ext (Subsingleton.elim _ _) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s.map _ ≫ s.map _ = s.map _`. Rewrite using `[← s.map_comp]`. Both sides reduce to the same expression. Unfold `val`.

Express the relevant statement in the definitionally equal form `m₂.τ _ ((F.map _).hom (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (F.map (toLast k (chain α ha ht s))).hom (f (face k (chain α ha ht s))))) = _`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul]`. Conclude with `congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • m₂.τ _ y) ((map_map F _ _ _).trans (congrArg (fun q => (F.map q).hom (f (face k (chain α ha ht s)))) (e k)))`.
-/
theorem val_d (s : ComposableArrows C' n) (f : CH.Cn F p) {a : Fin (p + 2) → Fin 2} {t : Fin (p + 2) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) :
    val m₂ α s (CH.d F p f) ha ht = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      val m₂ α s f (ha.comp (Fin.strictMono_succAbove k).monotone) (ht.comp (Fin.strictMono_succAbove k).monotone) := by
  have e : ∀ k : Fin (p + 2), toLast k (chain α ha ht s) ≫ (cyl α).map (up s (a (Fin.last (p + 1))) (t (Fin.last (p + 1)))) =
      (cyl α).map (up s (a (k.succAbove (Fin.last p))) (t (k.succAbove (Fin.last p)))) := by
    intro k
    change (cyl α).map _ ≫ _ = _
    rw [← Functor.map_comp]
    congr 1
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change s.map _ ≫ s.map _ = s.map _
    rw [← s.map_comp]; rfl
  unfold val
  change m₂.τ _ ((F.map _).hom (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (F.map (toLast k (chain α ha ht s))).hom (f (face k (chain α ha ht s))))) = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul]
  exact congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • m₂.τ _ y) ((map_map F _ _ _).trans
    (congrArg (fun q => (F.map q).hom (f (face k (chain α ha ht s)))) (e k)))

section Combinatorics

/- English proof (translation)
Unfold `Fin.succAbove`. Simplify using `only [Fin.lt_def, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem succAbove_val {m : ℕ} (p : Fin (m + 1)) (q : Fin m) :
    (p.succAbove q : ℕ) = if (q : ℕ) < p then (q : ℕ) else q + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

/- English proof (translation)
Unfold `Fin.predAbove`. Simplify using `only [Fin.lt_def, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem predAbove_val {m : ℕ} (p : Fin m) (q : Fin (m + 1)) :
    (p.predAbove q : ℕ) = if (p : ℕ) < q then (q : ℕ) - 1 else q := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

/- English proof (translation)
Establish `h' : (-1 : ℤ) ^ (a + b + c + e) = -1` using `h.neg_one_pow`. Rewrite `h'` using `[pow_add, pow_add, pow_add]`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ a with ha | ha <;> rcases neg_one_pow_eq_or ℤ b with hb | hb <;>`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ c with hc | hc <;> rcases neg_one_pow_eq_or ℤ e with he | he <;>`. Simplify the hypotheses and the goal together.
-/
theorem sign_of_odd (a b c e : ℕ) (h : Odd (a + b + c + e)) :
    (-1 : ℤ) ^ a * (-1) ^ b = -((-1) ^ c * (-1) ^ e) := by
  have h' : (-1 : ℤ) ^ (a + b + c + e) = -1 := h.neg_one_pow
  rw [pow_add, pow_add, pow_add] at h'
  rcases neg_one_pow_eq_or ℤ a with ha | ha <;> rcases neg_one_pow_eq_or ℤ b with hb | hb <;>
    rcases neg_one_pow_eq_or ℤ c with hc | hc <;> rcases neg_one_pow_eq_or ℤ e with he | he <;>
    simp_all

def skip {m : ℕ} (i : Fin (m + 1)) (l : Fin m) : Fin (m + 2) := i.castSucc.succAbove (i.succAbove l)

/- English proof (translation)
Unfold `skip`. Simplify using `only [succAbove_val, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem skip_val {m : ℕ} (i : Fin (m + 1)) (l : Fin m) :
    (skip i l : ℕ) = if (l : ℕ) < i then (l : ℕ) else l + 2 := by
  unfold skip
  simp only [succAbove_val, Fin.val_castSucc]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi : ∀ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • X i k = (X i i.castSucc - X i i.succ) + ∑ l : Fin m, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i (skip i l)`. Introduce `i`. Rewrite using `[Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i, Fin.succAbove_castSucc_self]`. Establish `e1 : (-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (i : ℕ) = 1`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Simplify using `only [smul_add, Finset.smul_sum, smul_smul, Fin.val_castSucc, Fin.val_succ, pow_succ, e1]`. Establish `e2 : (-1 : ℤ) ^ (i : ℕ) * ((-1 : ℤ) ^ (i : ℕ) * (-1)) = -1`. Rewrite using `[← mul_assoc, e1]`. Simplify using the standard rewrite rules.

Rewrite using `[e2, one_smul, neg_smul, one_smul, sub_eq_add_neg, add_assoc]`. Both sides reduce to the same expression. Simplify using `only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[Fin.sum_univ_succ (fun i : Fin (m + 1) => X i i.castSucc), Fin.sum_univ_castSucc (fun i : Fin (m + 1) => X i i.succ)]`.

Simplify using `only [h1]`. Simplify using `only [Fin.castSucc_zero, Fin.succ_last]`. Normalize the expressions using the abelian group laws.
-/
theorem prism_tele {A : Type*} [AddCommGroup A] (m : ℕ) (X : Fin (m + 1) → Fin (m + 2) → A)
    (h1 : ∀ i : Fin m, X i.succ i.succ.castSucc = X i.castSucc i.castSucc.succ) :
    ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • X i k =
      X 0 0 - X (Fin.last m) (Fin.last (m + 1)) +
        ∑ i : Fin (m + 1), ∑ l : Fin m, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i (skip i l) := by
  have hi : ∀ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • X i k =
      (X i i.castSucc - X i i.succ) +
        ∑ l : Fin m, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i (skip i l) := by
    intro i
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i, Fin.succAbove_castSucc_self]
    have e1 : (-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; simp
    simp only [smul_add, Finset.smul_sum, smul_smul, Fin.val_castSucc, Fin.val_succ, pow_succ, e1]
    have e2 : (-1 : ℤ) ^ (i : ℕ) * ((-1 : ℤ) ^ (i : ℕ) * (-1)) = -1 := by
      rw [← mul_assoc, e1]; simp
    rw [e2, one_smul, neg_smul, one_smul, sub_eq_add_neg, add_assoc]
    rfl
  simp only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  rw [Fin.sum_univ_succ (fun i : Fin (m + 1) => X i i.castSucc), Fin.sum_univ_castSucc (fun i : Fin (m + 1) => X i i.succ)]
  simp only [h1]
  simp only [Fin.castSucc_zero, Fin.succ_last]
  abel

/- English proof (translation)
Establish `hinv : Function.Involutive (fun p : Fin (n + 2) × Fin (n + 1) => (p.1.succAbove p.2, p.2.predAbove p.1))`. Introduce and unpack `⟨i, l⟩`. Simplify using `only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]`. Rewrite using `[← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Equiv.sum_comp hinv.toPerm (fun p : Fin (n + 2) × Fin (n + 1) => (-1 : ℤ) ^ (p.1 : ℕ) • (-1 : ℤ) ^ (p.2 : ℕ) • Y p.1 p.2), ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero ?_` and prove the remaining obligations.

Introduce and unpack `⟨i, l⟩ _`. Simplify using `only [Function.Involutive.coe_toPerm, smul_smul]`. Rewrite using `[h, sign_of_odd (i : ℕ) (skip i l : ℕ) (i.succAbove l : ℕ) (l.predAbove i : ℕ), neg_smul, neg_add_cancel]`. Rewrite using `[Nat.odd_iff, skip_val, succAbove_val, predAbove_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem prism_cancel {A : Type*} [AddCommGroup A] (n : ℕ) (X : Fin (n + 2) → Fin (n + 1) → A)
    (Y : Fin (n + 2) → Fin (n + 1) → A) (h : ∀ i l, X i l = Y (i.succAbove l) (l.predAbove i)) :
    ∑ i : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i l +
      ∑ j : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • (-1 : ℤ) ^ (l : ℕ) • Y j l = 0 := by
  have hinv : Function.Involutive (fun p : Fin (n + 2) × Fin (n + 1) => (p.1.succAbove p.2, p.2.predAbove p.1)) := by
    rintro ⟨i, l⟩
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Equiv.sum_comp hinv.toPerm (fun p : Fin (n + 2) × Fin (n + 1) => (-1 : ℤ) ^ (p.1 : ℕ) • (-1 : ℤ) ^ (p.2 : ℕ) • Y p.1 p.2),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero ?_
  rintro ⟨i, l⟩ _
  simp only [Function.Involutive.coe_toPerm, smul_smul]
  rw [h, sign_of_odd (i : ℕ) (skip i l : ℕ) (i.succAbove l : ℕ) (l.predAbove i : ℕ), neg_smul, neg_add_cancel]
  rw [Nat.odd_iff, skip_val, succAbove_val, predAbove_val]
  split_ifs <;> omega

end Combinatorics

section Prism

def pa {m : ℕ} (i : Fin (m + 1)) (t : Fin (m + 2)) : Fin 2 := if (i : ℕ) < t then Fin.last 1 else 0

/- English proof (translation)
Introduce `x y h`. Establish `h' : (x : ℕ) ≤ y` using `h`. Unfold `pa`. Use `split_ifs with h1 h2`. Conclude with `le_rfl`.

Use linear arithmetic over natural numbers and integers. Conclude with `Fin.zero_le _`. Conclude with `le_rfl`.
-/
theorem pa_mono {m : ℕ} (i : Fin (m + 1)) : Monotone (pa i) := by
  intro x y h
  have h' : (x : ℕ) ≤ y := h
  unfold pa
  split_ifs with h1 h2
  · exact le_rfl
  · omega
  · exact Fin.zero_le _
  · exact le_rfl

/- English proof (translation)
The claim follows from `Fin.predAbove_right_monotone i`.
-/
theorem pt_mono {m : ℕ} (i : Fin (m + 1)) : Monotone i.predAbove := Fin.predAbove_right_monotone i

/- English proof (translation)
The claim follows from `(Fin.strictMono_succAbove k).monotone`.
-/
theorem sa_mono {m : ℕ} (k : Fin (m + 1)) : Monotone k.succAbove := (Fin.strictMono_succAbove k).monotone

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, pa, succAbove_val, Fin.val_succ, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem pa_diag {m : ℕ} (i : Fin m) : pa i.succ ∘ i.succ.castSucc.succAbove = pa i.castSucc ∘ i.castSucc.succ.succAbove := by
  funext x
  simp only [Function.comp, pa, succAbove_val, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Function.comp, predAbove_val, succAbove_val, Fin.val_succ, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pt_diag {m : ℕ} (i : Fin m) : i.succ.predAbove ∘ i.succ.castSucc.succAbove = i.castSucc.predAbove ∘ i.castSucc.succ.succAbove := by
  funext x
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, pa, succAbove_val, Fin.val_zero]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem pa_first {m : ℕ} : pa (0 : Fin (m + 1)) ∘ (0 : Fin (m + 2)).succAbove = fun _ => Fin.last 1 := by
  funext x
  simp only [Function.comp, pa, succAbove_val, Fin.val_zero]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Function.comp, predAbove_val, succAbove_val, Fin.val_zero, id]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pt_first {m : ℕ} : (0 : Fin (m + 1)).predAbove ∘ (0 : Fin (m + 2)).succAbove = id := by
  funext x
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_zero, id]
  split_ifs <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `x.2` as an intermediate fact. Simplify using `only [Function.comp, pa, succAbove_val, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem prism_last_comp_succAbove_zero {m : ℕ} : pa (Fin.last m) ∘ (Fin.last (m + 1)).succAbove = fun _ => 0 := by
  funext x
  have := x.2
  simp only [Function.comp, pa, succAbove_val, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `x.2` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Function.comp, predAbove_val, succAbove_val, Fin.val_last, id]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem predAbove_last_comp_succAbove_id {m : ℕ} : (Fin.last m).predAbove ∘ (Fin.last (m + 1)).succAbove = id := by
  funext x
  have := x.2
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_last, id]
  split_ifs <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, pa, succAbove_val, predAbove_val, skip_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem pa_skip {m : ℕ} (i : Fin (m + 2)) (l : Fin (m + 1)) : pa i ∘ (skip i l).succAbove = pa (l.predAbove i) := by
  funext x
  simp only [Function.comp, pa, succAbove_val, predAbove_val, skip_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Function.comp, succAbove_val, predAbove_val, skip_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pt_skip {m : ℕ} (i : Fin (m + 2)) (l : Fin (m + 1)) :
    i.predAbove ∘ (skip i l).succAbove = (i.succAbove l).succAbove ∘ (l.predAbove i).predAbove := by
  funext x
  apply Fin.ext
  simp only [Function.comp, succAbove_val, predAbove_val, skip_val]
  split_ifs <;> omega

end Prism

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `only [eqToHom_refl, Category.id_comp] at hφ`. Rewrite using `[hφ]`.
-/
theorem cochain_congr (f : CH.Cn F p) {c c' : ComposableArrows C p} (h : c = c') {X : C}
    (φ : c.obj (Fin.last p) ⟶ X) (φ' : c'.obj (Fin.last p) ⟶ X) (hφ : φ = eqToHom (by rw [h]) ≫ φ') :
    (F.map φ).hom (f c) = (F.map φ').hom (f c') := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hφ
  rw [hφ]

/- English proof (translation)
Use `CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_` and prove the remaining obligations. Simplify using `only [eqToHom_refl, Category.id_comp, Category.comp_id]`. Use `Eq.trans ?_ (cyl_top α (s.map g)).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cyl α).map (X := (Fin.last 1, s.obj x)) (Y := (Fin.last 1, s.obj y)) (_, s.map _) = _`. Use `congr 1`.
-/
theorem chain_top {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (s : ComposableArrows C' n) :
    chain α (monotone_const : Monotone fun _ : Fin (n + 1) => Fin.last 1) monotone_id s = s ⋙ G₂ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Eq.trans ?_ (cyl_top α (s.map g)).symm
  change (cyl α).map (X := (Fin.last 1, s.obj x)) (Y := (Fin.last 1, s.obj y)) (_, s.map _) = _
  congr 1

/- English proof (translation)
Use `CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_` and prove the remaining obligations. Simplify using `only [eqToHom_refl, Category.id_comp, Category.comp_id]`. Use `Eq.trans ?_ (cyl_bot α (s.map g)).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cyl α).map (X := ((0 : Fin 2), s.obj x)) (Y := ((0 : Fin 2), s.obj y)) (_, s.map _) = _`. Use `congr 1`.
-/
theorem chain_bot {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (s : ComposableArrows C' n) :
    chain α (monotone_const : Monotone fun _ : Fin (n + 1) => (0 : Fin 2)) monotone_id s = s ⋙ G₁ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Eq.trans ?_ (cyl_bot α (s.map g)).symm
  change (cyl α).map (X := ((0 : Fin 2), s.obj x)) (Y := ((0 : Fin 2), s.obj y)) (_, s.map _) = _
  congr 1

/- English proof (translation)
The claim follows from `Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))`.
-/
theorem up_top (s : ComposableArrows C' n) : up s (Fin.last 1) (Fin.last n) = 𝟙 _ :=
  Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))

/- English proof (translation)
The claim follows from `Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))`.
-/
theorem up_bot (s : ComposableArrows C' n) :
    up s 0 (Fin.last n) = (homOfLE (Fin.zero_le _), 𝟙 (s.obj (Fin.last n))) :=
  Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))

/- English proof (translation)
Use `congrArg (m₂.τ _) ((cochain_congr f (chain_top α s) _ (𝟙 _) ?_).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (Category.comp_id _).symm` and prove the remaining obligations. Use `Eq.trans ?_ (eqToHom_refl _ rfl).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cyl α).map (up s (Fin.last 1) (Fin.last n)) = 𝟙 _`. Rewrite using `[up_top, (cyl α).map_id]`.

Rewrite using `[F.map_id]`. Both sides reduce to the same expression.
-/
theorem val_top (s : ComposableArrows C' n) (f : CH.Cn F n) :
    val m₂ α s f (monotone_const : Monotone fun _ : Fin (n + 1) => Fin.last 1) monotone_id = m₂.pullC n f s := by
  refine congrArg (m₂.τ _) ((cochain_congr f (chain_top α s) _ (𝟙 _) ?_).trans ?_)
  · refine Eq.trans ?_ (Category.comp_id _).symm
    refine Eq.trans ?_ (eqToHom_refl _ rfl).symm
    change (cyl α).map (up s (Fin.last 1) (Fin.last n)) = 𝟙 _
    rw [up_top, (cyl α).map_id]
  · rw [F.map_id]; rfl

/- English proof (translation)
Use `Eq.trans (congrArg (m₂.τ _) (cochain_congr f (chain_bot α s) _ (α.app _) ?_)) (hτ _ _)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (· ≫ α.app _) (eqToHom_refl _ rfl)).symm` and prove the remaining obligations. Use `Eq.trans ?_ (Category.id_comp _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cyl α).map (up s 0 (Fin.last n)) = _`. Rewrite using `[up_bot, cyl_step α]`.

Both sides reduce to the same expression.
-/
theorem val_bot (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (s : ComposableArrows C' n) (f : CH.Cn F n) :
    val m₂ α s f (monotone_const : Monotone fun _ : Fin (n + 1) => (0 : Fin 2)) monotone_id = m₁.pullC n f s := by
  refine Eq.trans (congrArg (m₂.τ _) (cochain_congr f (chain_bot α s) _ (α.app _) ?_)) (hτ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ α.app _) (eqToHom_refl _ rfl)).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  change (cyl α).map (up s 0 (Fin.last n)) = _
  rw [up_bot, cyl_step α]
  rfl

def htpy (n : ℕ) (f : CH.Cn F (n + 1)) : CH.Cn F' n := fun s =>
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • val m₂ α s f (pa_mono i) (pt_mono i)

/- English proof (translation)
The claim follows from `(congrArg (m₂.τ _) (map_zero _)).trans (map_zero _)`.
-/
theorem val_zero (s : ComposableArrows C' n) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) : val m₂ α s (0 : CH.Cn F p) ha ht = 0 :=
  (congrArg (m₂.τ _) (map_zero _)).trans (map_zero _)

/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [val_zero, smul_zero]`.
-/
theorem htpy_zero (n : ℕ) : htpy m₂ α n (0 : CH.Cn F (n + 1)) = 0 := by
  funext s
  exact Finset.sum_eq_zero fun i _ => by rw [val_zero, smul_zero]

def xv (s : ComposableArrows C' n) (f : CH.Cn F n) (i : Fin (n + 1)) (k : Fin (n + 2)) : F'.obj (s.obj (Fin.last n)) :=
  val m₂ α s f ((pa_mono i).comp (sa_mono k)) ((pt_mono i).comp (sa_mono k))

/- English proof (translation)
Establish `h0 : htpy m₂ α n (CH.d F n f) s = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • xv m₂ α s f i k` using `Finset.sum_congr rfl fun i _ => congrArg _ (val_d m₂ α s f _ _)`. Rewrite using `[h0, prism_tele n (xv m₂ α s f) fun i => val_congr m₂ α s f _ _ _ _ (pa_diag i) (pt_diag i)]`. Use `congr 2`. Conclude with `(val_congr m₂ α s f _ _ monotone_const monotone_id pa_first pt_first).trans (val_top m₂ α s f)`. Conclude with `(val_congr m₂ α s f _ _ monotone_const monotone_id prism_last_comp_succAbove_zero predAbove_last_comp_succAbove_id).trans (val_bot m₂ m₁ α hτ s f)`.
-/
theorem hd_eq (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (s : ComposableArrows C' n) (f : CH.Cn F n) :
    htpy m₂ α n (CH.d F n f) s = m₂.pullC n f s - m₁.pullC n f s +
      ∑ i : Fin (n + 1), ∑ l : Fin n, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • xv m₂ α s f i (skip i l) := by
  have h0 : htpy m₂ α n (CH.d F n f) s = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • xv m₂ α s f i k :=
    Finset.sum_congr rfl fun i _ => congrArg _ (val_d m₂ α s f _ _)
  rw [h0, prism_tele n (xv m₂ α s f) fun i => val_congr m₂ α s f _ _ _ _ (pa_diag i) (pt_diag i)]
  congr 2
  · exact (val_congr m₂ α s f _ _ monotone_const monotone_id pa_first pt_first).trans (val_top m₂ α s f)
  · exact (val_congr m₂ α s f _ _ monotone_const monotone_id prism_last_comp_succAbove_zero predAbove_last_comp_succAbove_id).trans (val_bot m₂ m₁ α hτ s f)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • (F'.map (toLast j s)).hom (∑ l : Fin (n + 1), (-1 : ℤ) ^ (l : ℕ) • val m₂ α (face j s) f (pa_mono l) (pt_mono l)) = _`. Simplify using `only [map_sum, map_zsmul, val_face, Finset.smul_sum]`.
-/
theorem dh_eq (s : ComposableArrows C' (n + 1)) (f : CH.Cn F (n + 1)) :
    CH.d F' n (htpy m₂ α n f) s = ∑ j : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • (-1 : ℤ) ^ (l : ℕ) •
      val m₂ α s f (pa_mono l) ((sa_mono j).comp (pt_mono l)) := by
  change ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • (F'.map (toLast j s)).hom
    (∑ l : Fin (n + 1), (-1 : ℤ) ^ (l : ℕ) • val m₂ α (face j s) f (pa_mono l) (pt_mono l)) = _
  simp only [map_sum, map_zsmul, val_face, Finset.smul_sum]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `htpy m₂ α (n + 1) (CH.d F (n + 1) f) s + CH.d F' n (htpy m₂ α n f) s = m₂.pullC (n + 1) f s - m₁.pullC (n + 1) f s`. Rewrite using `[hd_eq m₂ m₁ α hτ, dh_eq]`. Conclude with `(add_assoc _ _ _).trans ((congrArg _ (prism_cancel n (fun i l => xv m₂ α s f i (skip i l)) (fun j l => val m₂ α s f (pa_mono l) ((sa_mono j).comp (pt_mono l))) (fun i l => val_congr m₂ α s f _ _ _ _ (pa_skip i l) (pt_skip i l)))).trans (add_zero _))`.
-/
theorem htpy_spec (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (f : CH.Cn F (n + 1)) :
    htpy m₂ α (n + 1) (CH.d F (n + 1) f) + CH.d F' n (htpy m₂ α n f) = m₂.pullC (n + 1) f - m₁.pullC (n + 1) f := by
  funext s
  change htpy m₂ α (n + 1) (CH.d F (n + 1) f) s + CH.d F' n (htpy m₂ α n f) s = m₂.pullC (n + 1) f s - m₁.pullC (n + 1) f s
  rw [hd_eq m₂ m₁ α hτ, dh_eq]
  exact (add_assoc _ _ _).trans ((congrArg _ (prism_cancel n (fun i l => xv m₂ α s f i (skip i l))
    (fun j l => val m₂ α s f (pa_mono l) ((sa_mono j).comp (pt_mono l)))
    (fun i l => val_congr m₂ α s f _ _ _ _ (pa_skip i l) (pt_skip i l)))).trans (add_zero _))

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[hd_eq m₂ m₁ α hτ]`. Simplify using the standard rewrite rules.
-/
theorem htpy_spec_zero (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (f : CH.Cn F 0) : htpy m₂ α 0 (CH.d F 0 f) = m₂.pullC 0 f - m₁.pullC 0 f := by
  funext s
  rw [hd_eq m₂ m₁ α hτ]
  simp

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (m₁.hom.mapZ j z) = Submodule.Quotient.mk (m₂.hom.mapZ j z)`. Rewrite using `[Submodule.Quotient.eq]`. Express the relevant statement in the definitionally equal form `m₁.pullC j z.1 - m₂.pullC j z.1 ∈ (CH.cx F').B j`.

Establish `hz : CH.d F j z.1 = 0` using `z.2`. Consider the cases of `j with`. Consider the case `zero`. Establish `h` using `htpy_spec_zero m₂ m₁ α hτ z.1`. Rewrite `h` using `[hz, htpy_zero]`.

Establish `h' : m₁.pullC 0 z.1 - m₂.pullC 0 z.1 = 0`. Rewrite using `[← neg_sub, ← h, neg_zero]`. Rewrite using `[h']`. Conclude with `Submodule.zero_mem _`. Consider the case `succ n`.

Establish `h` using `htpy_spec m₂ m₁ α hτ z.1`. Rewrite `h` using `[hz, htpy_zero, zero_add]`. Use `⟨-htpy m₂ α n z.1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CH.d F' n (-htpy m₂ α n z.1) = _`. Rewrite using `[map_neg, h, neg_sub]`.
-/
theorem pull_eq_of_natTrans (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) (j : ℕ) :
    m₁.pull j = m₂.pull j := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (m₁.hom.mapZ j z) = Submodule.Quotient.mk (m₂.hom.mapZ j z)
  rw [Submodule.Quotient.eq]
  change m₁.pullC j z.1 - m₂.pullC j z.1 ∈ (CH.cx F').B j
  have hz : CH.d F j z.1 = 0 := z.2
  cases j with
  | zero =>
    have h := htpy_spec_zero m₂ m₁ α hτ z.1
    rw [hz, htpy_zero] at h
    have h' : m₁.pullC 0 z.1 - m₂.pullC 0 z.1 = 0 := by
      rw [← neg_sub, ← h, neg_zero]
    rw [h']
    exact Submodule.zero_mem _
  | succ n =>
    have h := htpy_spec m₂ m₁ α hτ z.1
    rw [hz, htpy_zero, zero_add] at h
    refine ⟨-htpy m₂ α n z.1, ?_⟩
    change CH.d F' n (-htpy m₂ α n z.1) = _
    rw [map_neg, h, neg_sub]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ m₁ m₂ α h j` and use `pull_eq_of_natTrans m₂ m₁ α h j`.
-/
theorem pull_eq_target : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j :=
  fun _ _ _ _ _ _ _ _ m₁ m₂ α h j => pull_eq_of_natTrans m₂ m₁ α h j

end GlobalTheory.CompanionTheory.CatPrism

end
