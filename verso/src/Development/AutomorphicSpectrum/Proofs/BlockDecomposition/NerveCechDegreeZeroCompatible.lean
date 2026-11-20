import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero

variable {R : Type} [CommRing R]

section Chains

variable {C : Type} [Category.{0} C]

abbrev pt (a : C) : Fin (0 + 1) ⥤ C := (Functor.const _).obj a

/- English proof (translation)
Establish `hX : ∀ X : Fin (0 + 1), X = 0` using `fun X => Fin.ext (by have := X.isLt; simp only [Fin.val_zero]; omega)`. Establish `hobj : ∀ X, c.obj X = (pt (c.obj 0)).obj X` using `fun X => congrArg c.obj (hX X)`. Use `⟨c.obj 0, CategoryTheory.Functor.ext hobj (fun X Y f => ?_)⟩` and prove the remaining obligations. Take `rfl` from `hX X`. Take `rfl` from `hX Y`.

Take `rfl : f = 𝟙 _` from `Subsingleton.elim _ _`. Simplify using the standard rewrite rules.
-/
theorem exists_pt (c : Fin (0 + 1) ⥤ C) : ∃ a, c = pt a := by
  have hX : ∀ X : Fin (0 + 1), X = 0 := fun X => Fin.ext (by have := X.isLt; simp only [Fin.val_zero]; omega)
  have hobj : ∀ X, c.obj X = (pt (c.obj 0)).obj X := fun X => congrArg c.obj (hX X)
  refine ⟨c.obj 0, CategoryTheory.Functor.ext hobj (fun X Y f => ?_)⟩
  obtain rfl := hX X
  obtain rfl := hX Y
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  simp

/- English proof (translation)
Take `⟨a, rfl⟩` from `exists_pt c`. Both sides reduce to the same expression.
-/
theorem eval_chain (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1) ⥤ C) :
    x c = x (pt (c.obj (Fin.last 0))) := by
  obtain ⟨a, rfl⟩ := exists_pt c
  rfl

/- English proof (translation)
Rewrite using `[pullNC_apply]`. Use `show (G.map (c.map (homOfLE (le_refl (Fin.last (0 + 1)))))).hom (x ((Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom.monotone.functor ⋙ c)) = _`. Rewrite using `[show homOfLE (le_refl (Fin.last (0 + 1))) = 𝟙 (Fin.last (0 + 1) : Fin (0 + 1 + 1)) from Subsingleton.elim _ _, c.map_id, G.map_id]`. Conclude with `eval_chain G x _`.
-/
theorem pull_last (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c = x (pt (c.obj (Fin.last (0 + 1)))) := by
  rw [pullNC_apply]
  show (G.map (c.map (homOfLE (le_refl (Fin.last (0 + 1)))))).hom
    (x ((Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom.monotone.functor ⋙ c)) = _
  rw [show homOfLE (le_refl (Fin.last (0 + 1))) = 𝟙 (Fin.last (0 + 1) : Fin (0 + 1 + 1)) from
    Subsingleton.elim _ _, c.map_id, G.map_id]
  exact eval_chain G x _

/- English proof (translation)
Rewrite using `[pullNC_apply]`. Conclude with `congrArg (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (eval_chain G x _)`.
-/
theorem pull_first (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c =
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  rw [pullNC_apply]
  exact congrArg (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (eval_chain G x _)

/- English proof (translation)
Establish `hsum : dNC G 0 x c = pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c - pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c`. Simplify using `only [dNC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]`. Use `show ∑ i : Fin 2, (-1 : R) ^ (i : ℕ) • (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) x c = _`. Rewrite using `[Fin.sum_univ_two]`. Apply the tactic sequence `simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, sub_eq_add_neg] <;> rfl`.

Apply the tactic sequence `rw [hsum, pull_last, pull_first] <;> rfl`.
-/
theorem dNC_zero_apply (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    dNC G 0 x c = (show G.obj (c.obj (Fin.last (0 + 1))) from x (pt (c.obj (Fin.last (0 + 1))))) -
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  have hsum : dNC G 0 x c = pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c -
      pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c := by
    simp only [dNC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
    show ∑ i : Fin 2, (-1 : R) ^ (i : ℕ) • (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) x c = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, sub_eq_add_neg] <;> rfl
  rw [hsum, pull_last, pull_first] <;> rfl

end Chains

section Semilattice

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P) (G : Pᵒᵖ ⥤ ModuleCat.{0} R)

def epsLin : NC G 0 →ₗ[R] Cube.Term (cubeOf e G) 1 where
  toFun x s hs := x (pt (op (s.1.inf' hs.down e)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev val (x : NC G 0) (a : P) : G.obj (op a) := x (pt (op a))

def Compat (x : NC G 0) : Prop :=
  ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx a b h`. Establish `h1` using `congrFun hx (ComposableArrows.mk₁ (homOfLE h).op)`. Establish `hm : (ComposableArrows.mk₁ (homOfLE h).op).map (homOfLE (Fin.le_last (0 : Fin (0 + 1 + 1)))) = (homOfLE h).op` using `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Rewrite `h1` using `[dNC_zero_apply, Pi.zero_apply, sub_eq_zero, hm]`.

Conclude with `h1`. Introduce `hc`. Use function extensionality and compare the values at `c`. Rewrite using `[dNC_zero_apply, Pi.zero_apply, sub_eq_zero]`. Establish `h : (c.obj (Fin.last (0 + 1))).unop ≤ (c.obj 0).unop` using `leOfHom (c.map (homOfLE (Fin.le_last 0))).unop`.

Establish `hm : c.map (homOfLE (Fin.le_last 0)) = (homOfLE h).op` using `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Rewrite using `[hm]`. Conclude with `hc h`.
-/
theorem dNC_zero_iff (x : NC G 0) : dNC G 0 x = 0 ↔ Compat G x := by
  constructor
  · intro hx a b h
    have h1 := congrFun hx (ComposableArrows.mk₁ (homOfLE h).op)
    have hm : (ComposableArrows.mk₁ (homOfLE h).op).map (homOfLE (Fin.le_last (0 : Fin (0 + 1 + 1)))) =
        (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero, hm] at h1
    exact h1
  · intro hc
    funext c
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero]
    have h : (c.obj (Fin.last (0 + 1))).unop ≤ (c.obj 0).unop := leOfHom (c.map (homOfLE (Fin.le_last 0))).unop
    have hm : c.map (homOfLE (Fin.le_last 0)) = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hm]
    exact hc h

/- English proof (translation)
Introduce `x y hxy`. Use function extensionality and compare the values at `c`. Rewrite using `[eval_chain G x c, eval_chain G y c]`. Take `⟨k, hk⟩` from `he (c.obj (Fin.last 0)).unop`. Establish `h1 : x (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) = y (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e)))` using `congrFun (congrFun hxy ⟨{k}, Finset.card_singleton k⟩) ⟨Finset.singleton_nonempty k⟩`.

Rewrite `h1` using `[Finset.inf'_singleton, hk]`. Conclude with `h1`.
-/
theorem epsLin_injective (he : Function.Surjective e) : Function.Injective (epsLin e G) := by
  intro x y hxy
  funext c
  rw [eval_chain G x c, eval_chain G y c]
  obtain ⟨k, hk⟩ := he (c.obj (Fin.last 0)).unop
  have h1 : x (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) =
      y (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) :=
    congrFun (congrFun hxy ⟨{k}, Finset.card_singleton k⟩) ⟨Finset.singleton_nonempty k⟩
  rw [Finset.inf'_singleton, hk] at h1
  exact h1

/- English proof (translation)
Substitute `h` using the available equality. Apply the tactic sequence `rw [eqToHom_refl, G.map_id] <;> rfl`.
-/
private theorem map_eqToHom_singleton_eq (z : Cube.Term (cubeOf e G) 1) {k' k : κ} (h : k' = k)
    (pr : op (({k'} : Finset κ).inf' (Finset.singleton_nonempty k') e) =
      op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e)) :
    (G.map (eqToHom pr)).hom (z ⟨{k'}, Finset.card_singleton k'⟩ ⟨Finset.singleton_nonempty k'⟩) =
      z ⟨{k}, Finset.card_singleton k⟩ ⟨Finset.singleton_nonempty k⟩ := by
  subst h
  rw [eqToHom_refl, G.map_id] <;> rfl

/- English proof (translation)
Introduce `z`. Use `choose f hf using he'`. Establish `hop : ∀ p : P, op (({f p} : Finset κ).inf' (Finset.singleton_nonempty (f p)) e) = op p`. Introduce `p`. Rewrite using `[Finset.inf'_singleton, hf]`.

Use `⟨fun c => (G.map (eqToHom (hop (c.obj (Fin.last 0)).unop))).hom (z ⟨{f (c.obj (Fin.last 0)).unop}, Finset.card_singleton _⟩ ⟨Finset.singleton_nonempty _⟩), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s hs`. Take `⟨s, hs1⟩` from `s`. Take `⟨k, rfl⟩` from `Finset.card_eq_one.mp hs1`. Establish `hk : f (({k} : Finset κ).inf' hs.down e) = k`.

Apply `he` to reduce the goal to its premises. Rewrite using `[hf, Finset.inf'_singleton]`. Conclude with `map_eqToHom_singleton_eq e G z hk _`.
-/
theorem epsLin_surjective (he : Function.Injective e) (he' : Function.Surjective e) :
    Function.Surjective (epsLin e G) := by
  intro z
  choose f hf using he'
  have hop : ∀ p : P, op (({f p} : Finset κ).inf' (Finset.singleton_nonempty (f p)) e) = op p := by
    intro p
    rw [Finset.inf'_singleton, hf]
  refine ⟨fun c => (G.map (eqToHom (hop (c.obj (Fin.last 0)).unop))).hom
      (z ⟨{f (c.obj (Fin.last 0)).unop}, Finset.card_singleton _⟩ ⟨Finset.singleton_nonempty _⟩), ?_⟩
  funext s hs
  obtain ⟨s, hs1⟩ := s
  obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hs1
  have hk : f (({k} : Finset κ).inf' hs.down e) = k := by
    apply he
    rw [hf, Finset.inf'_singleton]
  exact map_eqToHom_singleton_eq e G z hk _

/- English proof (translation)
Use `erw [GlobalTheory.Cube.d_one_apply_pair (cubeOf e G) (epsLin e G x) hij, Pi.sub_apply]`. Conclude with `congrArg₂ (· - ·) (cubeRes_apply e G (by simp : ({j} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{j}, Finset.card_singleton j⟩) (Finset.singleton_nonempty j) ⟨hp⟩) (cubeRes_apply e G (by simp : ({i} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{i}, Finset.card_singleton i⟩) (Finset.singleton_no …`.
-/
theorem d_pair (x : NC G 0) {κ : Type} [LinearOrder κ] (e : κ → P) {i j : κ} (hij : i < j)
    (hp : ({i, j} : Finset κ).Nonempty)
    (h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e)
    (h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ =
      (G.map (homOfLE h1).op).hom (val G x _) - (G.map (homOfLE h2).op).hom (val G x _) := by
  erw [GlobalTheory.Cube.d_one_apply_pair (cubeOf e G) (epsLin e G x) hij, Pi.sub_apply]
  exact congrArg₂ (· - ·)
    (cubeRes_apply e G (by simp : ({j} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{j}, Finset.card_singleton j⟩)
      (Finset.singleton_nonempty j) ⟨hp⟩)
    (cubeRes_apply e G (by simp : ({i} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{i}, Finset.card_singleton i⟩)
      (Finset.singleton_nonempty i) ⟨hp⟩)

/- English proof (translation)
Substitute `ha hb hm` using the available equality. Establish `e2 : homOfLE h2 = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite `E` using `[e2, op_id, G.map_id]`. Conclude with `E.symm`.
-/
theorem step (x : NC G 0) {a a' b b' m : P} (ha : a' = a) (hb : b' = b) (hm : m = b) (h : b ≤ a)
    (h1 : m ≤ a') (h2 : m ≤ b')
    (E : (G.map (homOfLE h1).op).hom (val G x a') = (G.map (homOfLE h2).op).hom (val G x b')) :
    val G x b = (G.map (homOfLE h).op).hom (val G x a) := by
  subst ha hb hm
  have e2 : homOfLE h2 = 𝟙 _ := Subsingleton.elim _ _
  rw [e2, op_id, G.map_id] at E
  exact E.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hd a b h`. Take `⟨i, rfl⟩` from `he a`. Take `⟨j, rfl⟩` from `he b`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Establish `hp : ({i, j} : Finset κ).Nonempty` using `Finset.insert_nonempty _ _`. Establish `h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e` using `Finset.inf'_mono e (by simp) _`. Establish `h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e` using `Finset.inf'_mono e (by simp) _`. Establish `E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0`. Apply the tactic sequence `rw [hd] <;> rfl`.

Rewrite `E0` using `[d_pair G x e hij hp h1 h2, sub_eq_zero]`. Conclude with `step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_right.mpr h]) h h2 h1 E0.symm`. Establish `e2 : homOfLE h = 𝟙 _` using `Subsingleton.elim _ _`. Apply the tactic sequence `rw [e2, op_id, G.map_id] <;> rfl`. Establish `hp : ({j, i} : Finset κ).Nonempty` using `Finset.insert_nonempty _ _`.

Establish `h1 : ({j, i} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e` using `Finset.inf'_mono e (by simp) _`. Establish `h2 : ({j, i} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e` using `Finset.inf'_mono e (by simp) _`. Establish `E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{j, i}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0`. Apply the tactic sequence `rw [hd] <;> rfl`. Rewrite `E0` using `[d_pair G x e hij hp h1 h2, sub_eq_zero]`.

Conclude with `step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_left.mpr h]) h h1 h2 E0`. Introduce `hc`. Establish `hc' : ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a)` using `hc`. Use function extensionality and compare the values at `t ht`. Take `⟨t, htc⟩` from `t`.

Take `⟨i, j, hne, hs⟩` from `Finset.card_eq_two.mp htc`. Break down `lt_or_gt_of_ne hne with hij | hij` into its components or cases. Substitute `hs` using the available equality. Establish `h1 : ({i, j} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e` using `Finset.inf'_mono e (by simp) _`. Establish `h2 : ({i, j} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e` using `Finset.inf'_mono e (by simp) _`.

Apply the tactic sequence `rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl`. Rewrite `hs` using `[Finset.pair_comm]`. Substitute `hs` using the available equality. Establish `h1 : ({j, i} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e` using `Finset.inf'_mono e (by simp) _`. Establish `h2 : ({j, i} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e` using `Finset.inf'_mono e (by simp) _`.

Apply the tactic sequence `rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl`.
-/
theorem d_eps_zero_iff {κ : Type} [LinearOrder κ] (e : κ → P) (he : Function.Surjective e) (x : NC G 0) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) = 0 ↔ Compat G x := by
  constructor
  · intro hd a b h
    obtain ⟨i, rfl⟩ := he a
    obtain ⟨j, rfl⟩ := he b
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hp : ({i, j} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_right.mpr h]) h h2 h1 E0.symm
    · have e2 : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
      rw [e2, op_id, G.map_id] <;> rfl
    · have hp : ({j, i} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({j, i} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{j, i}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_left.mpr h]) h h1 h2 E0
  · intro hc
    have hc' : ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a) := hc
    funext t ht
    obtain ⟨t, htc⟩ := t
    obtain ⟨i, j, hne, hs⟩ := Finset.card_eq_two.mp htc
    rcases lt_or_gt_of_ne hne with hij | hij
    · subst hs
      have h1 : ({i, j} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl
    · rw [Finset.pair_comm] at hs
      subst hs
      have h1 : ({j, i} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl

end Semilattice

/- English proof (translation)
Introduce `hbij`. Use `⟨fun G => (LinearEquiv.ofBijective (epsLin e G) ⟨epsLin_injective e G hbij.2, epsLin_surjective e G hbij.1 hbij.2⟩).toModuleIso, ?_, ?_⟩` and prove the remaining obligations. Introduce `G G' φ`. Use extensionality with `x`. Both sides reduce to the same expression.

Introduce `G x`. Establish `hd1 : (nerveCx.obj G).d 0 1 = ModuleCat.ofHom (dNC G 0)` using `nerveCx_d G 0`. Establish `hc1 : ((cechOf e).obj G).d 0 1 = ModuleCat.ofHom ((cubeOf e G).d 1)` using `GlobalTheory.cechComplex_d (cubeOf e G) 0`. Rewrite using `[hd1, hc1]`. Conclude with `(dNC_zero_iff G x).trans (d_eps_zero_iff G e hbij.2 x).symm`.
-/
theorem degZero {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P) :
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  intro hbij
  refine ⟨fun G => (LinearEquiv.ofBijective (epsLin e G)
      ⟨epsLin_injective e G hbij.2, epsLin_surjective e G hbij.1 hbij.2⟩).toModuleIso, ?_, ?_⟩
  · intro G G' φ
    ext x
    rfl
  · intro G x
    have hd1 : (nerveCx.obj G).d 0 1 = ModuleCat.ofHom (dNC G 0) := nerveCx_d G 0
    have hc1 : ((cechOf e).obj G).d 0 1 = ModuleCat.ofHom ((cubeOf e G).d 1) := GlobalTheory.cechComplex_d (cubeOf e G) 0
    rw [hd1, hc1]
    exact (dNC_zero_iff G x).trans (d_eps_zero_iff G e hbij.2 x).symm

end GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero
