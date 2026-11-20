import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_af_type

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩ y`. Establish `hy : g y ∈ RC` using `hg y (Set.mem_univ y)`. Use `Submodule.mem_span_singleton.2 ⟨⟨g y, hy⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g y * (p : C) = (p : C) * g y`.

Expand and normalize the polynomial expressions, which then agree. Introduce `h choose a ha using fun y => Submodule.mem_span_singleton.1 (h y)`. Use `⟨fun y => (a y : C), fun y _ => (a y).2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Rewrite using `[← ha y]`.

Express the relevant statement in the definitionally equal form `(p : C) * (a y : C) = (a y : C) * (p : C)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_mul_std (RC : Subalgebra o C) (p : ℕ) {X : Type} (f : X → C) :
    f ∈ mulLat (p : C) (stdLat RC X) ↔ ∀ y, f y ∈ pInt (C := C) RC p := by
  constructor
  · rintro ⟨g, hg, rfl⟩ y
    have hy : g y ∈ RC := hg y (Set.mem_univ y)
    refine Submodule.mem_span_singleton.2 ⟨⟨g y, hy⟩, ?_⟩
    change g y * (p : C) = (p : C) * g y
    ring
  · intro h
    choose a ha using fun y => Submodule.mem_span_singleton.1 (h y)
    refine ⟨fun y => (a y : C), fun y _ => (a y).2, ?_⟩
    funext y
    rw [← ha y]
    change (p : C) * (a y : C) = (a y : C) * (p : C)
    ring

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 h`. Express the relevant statement in the definitionally equal form `(a : C) * (p : C) ∈ RC`. Conclude with `RC.mul_mem a.2 (natCast_mem RC p)`.
-/
theorem pInt_mem (RC : Subalgebra o C) (p : ℕ) {c : C} (h : c ∈ pInt (C := C) RC p) : c ∈ RC := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
  change (a : C) * (p : C) ∈ RC
  exact RC.mul_mem a.2 (natCast_mem RC p)

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Use `Submodule.mem_span_singleton.2 ⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : C) * (p : C) = _`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem coe_mem_pInt (RC : Subalgebra o C) (p : ℕ) {c : RC} (h : c ∈ Ideal.span {(p : RC)}) :
    (c : C) ∈ pInt (C := C) RC p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  change (a : C) * (p : C) = _
  push_cast
  rfl

/- English proof (translation)
Establish `hl : ∀ y : Fin n → F, linMap n χ u y = ∑ k, u k * χ (y k)`. Introduce `y`. Simplify using `[linMap, Fintype.linearCombination_apply, Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `linMap n χ u ∈ D.M ⊔ mulLat (p : C) (stdLat RC _) ↔ _`. Rewrite using `[AddSubgroup.mem_sup]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, f, hf, h⟩`. Use `⟨g, hg, fun y => ?_⟩` and prove the remaining obligations. Use `(mem_mul_std RC p f).1 hf y` as an intermediate fact. Rewrite using `[← hl, ← h]`.

Simplify using `using this`. Introduce and unpack `⟨g, hg, h⟩`. Use `⟨g, hg, linMap n χ u - g, (mem_mul_std RC p _).2 fun y => ?_, by abel⟩` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, hl]`. Conclude with `h y`.
-/
theorem mem_af (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
    (D : LieLatticeData C F n Sg r s) (χ : F → C) (u : Fin n → C) :
    u ∈ D.af RC p χ ↔ ∃ g ∈ D.M, ∀ y : Fin n → F,
      (∑ k, u k * χ (y k)) - g y ∈ pInt (C := C) RC p := by
  have hl : ∀ y : Fin n → F, linMap n χ u y = ∑ k, u k * χ (y k) := by
    intro y
    simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply]
  change linMap n χ u ∈ D.M ⊔ mulLat (p : C) (stdLat RC _) ↔ _
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, f, hf, h⟩
    refine ⟨g, hg, fun y => ?_⟩
    have := (mem_mul_std RC p f).1 hf y
    rw [← hl, ← h]
    simpa using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, linMap n χ u - g, (mem_mul_std RC p _).2 fun y => ?_, by abel⟩
    rw [Pi.sub_apply, hl]
    exact h y

/- English proof (translation)
Simplify using `only [dotDual, AddSubgroup.mem_iInf]`. Both sides reduce to the same expression.
-/
theorem mem_dotDual (RC : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (u : Fin m → C) :
    u ∈ dotDual RC L ↔ ∀ l ∈ L, l ⬝ᵥ u ∈ RC := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

/- English proof (translation)
Establish `h1 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) ∈ Ideal.span {(p : RC)}` using `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k)`. Establish `h2 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) = (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Rewrite `h1` using `[h2]`.

Establish `h3` using `coe_mem_pInt RC p h1`. Establish `h4 : (((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k : RC) : C) = algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C)`. Express the relevant statement in the definitionally equal form `algebraMap RC C ((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k) = _`. Rewrite using `[map_sub, map_sum (algebraMap RC C) (fun k => l k * b k)]`. Simplify using `only [map_mul]`.

Both sides reduce to the same expression. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis.
-/
theorem congr_lin (RC : Subalgebra o C) (p : ℕ) {I : Type} [Fintype I] {n : ℕ}
    (Pm : Matrix (Fin n) I RC) (a : I → RC) (b : Fin n → RC)
    (h : ∀ k, (∑ j, Pm k j * a j) - b k ∈ Ideal.span {(p : RC)}) (l : Fin n → RC) :
    algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C)
      ∈ pInt (C := C) RC p := by
  have h1 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) ∈ Ideal.span {(p : RC)} :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k)
  have h2 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k)
      = (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k := by
    simp only [mul_sub, Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [h2] at h1
  have h3 := coe_mem_pInt RC p h1
  have h4 : (((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k : RC) : C)
      = algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C) := by
    change algebraMap RC C ((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k) = _
    rw [map_sub, map_sum (algebraMap RC C) (fun k => l k * b k)]
    simp only [map_mul]
    rfl
  rwa [h4] at h3

/- English proof (translation)
Establish `h : ∀ k, ((Matrix.vecMul l J k : RC) : C) = ∑ j, (l j : C) * algebraMap RC C (J j k)`. Introduce `k`. Express the relevant statement in the definitionally equal form `algebraMap RC C (∑ j, l j * J j k) = _`. Rewrite using `[map_sum]`. Simplify using `only [map_mul]`.

Both sides reduce to the same expression. Simplify using `only [h, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem dot_eq (RC : Subalgebra o C) {I : Type} [Fintype I] {n : ℕ}
    (J : Matrix I (Fin n) RC) (l : I → RC) (u : Fin n → C) :
    (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j)
      = (fun k => ((Matrix.vecMul l J k : RC) : C)) ⬝ᵥ u := by
  have h : ∀ k, ((Matrix.vecMul l J k : RC) : C) = ∑ j, (l j : C) * algebraMap RC C (J j k) := by
    intro k
    change algebraMap RC C (∑ j, l j * J j k) = _
    rw [map_sum]
    simp only [map_mul]
    rfl
  simp only [h, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

end PositivityTheory.Xgn.A_pt_af_type

open PositivityTheory.Xgn.A_pt_af_type in
/- English proof (translation)
Introduce `o C _ _ _ RC p _ I _ _ MM hint F _ _ n Sg r s D χ h0 h1 i π hπ hst hM Pm J hPJ hc hAF`. Establish `hMM : ∀ g, g ∈ D.M ↔ ∃ h ∈ MM, (fun y => h (i y)) = g`. Introduce `g`. Rewrite using `[← hM]`. Conclude with `Submodule.mem_map`.

Establish `P1 : ∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM`. Introduce `l`. Rewrite using `[mem_af]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, h⟩`.

Take `⟨h', hh', rfl⟩` from `(hMM g).1 hg`. Use `⟨_, hst h' hh', fun x => ?_⟩` and prove the remaining obligations. Establish `e1` using `congr_lin RC p Pm (fun j => ((x j).val : RC)) (fun k => χ (π x k)) (fun k => hc k x) l`. Establish `e2` using `h (π x)`. Establish `e3` using `Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)`.

Use `e3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨g, hg, h⟩`. Use `⟨_, (hMM _).2 ⟨g, hg, rfl⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `e1` using `congr_lin RC p Pm (fun j => ((i y j).val : RC)) (fun k => χ (π (i y) k)) (fun k => hc k (i y)) l`.

Rewrite `e1` using `[hπ]`. Establish `e2` using `h (i y)`. Establish `e3` using `Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)`. Use `e3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hco : ∀ u ∈ D.af RC p (fun a => (χ a : C)), ∀ k, u k ∈ RC`. Introduce `u hu k`. Take `⟨g, hg, h⟩` from `(mem_af RC p D _ u).1 hu`. Take `⟨h', hh', rfl⟩` from `(hMM g).1 hg`. Establish `e1` using `pInt_mem RC p (h (Pi.single k 1))`.

Establish `e2 : ∑ j, u j * ((χ ((Pi.single k 1 : Fin n → F) j) : RC) : C) = u k`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[h1]`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj, h0]`.

Simplify using the standard rewrite rules. Rewrite `e1` using `[e2]`. Establish `e3 : h' (i (Pi.single k 1)) ∈ RC`. Use `hint hh'` as an intermediate fact. Take `⟨a, ha⟩` from `this (i (Pi.single k 1))`.

Rewrite using `[← ha]`. Conclude with `a.2`. Simplify using `using RC.add_mem e1 e3`. Use `⟨P1, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[LieLatticeData.hh, mem_dotDual]`.

Prove the components needed by the constructor for the conclusion. Introduce `h l hl`. Rewrite using `[dot_eq]`. Use `h _ ((P1 _).2 ?_)` and prove the remaining obligations. Rewrite using `[Matrix.vecMul_vecMul]`.

Conclude with `hAF l hl`. Introduce `h l hl`. Set `l' : Fin n → RC` to `fun k => ⟨l k, hco l hl k⟩`. Establish `e` using `h _ ((P1 l').1 hl)`. Rewrite `e` using `[dot_eq, Matrix.vecMul_vecMul, hPJ, Matrix.vecMul_one]`.

Conclude with `e`.
-/
theorem PositivityTheory.Xgn.t_pt_af_type : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC := by
  intro o C _ _ _ RC p _ I _ _ MM hint F _ _ n Sg r s D χ h0 h1 i π hπ hst hM Pm J hPJ hc hAF
  have hMM : ∀ g, g ∈ D.M ↔ ∃ h ∈ MM, (fun y => h (i y)) = g := by
    intro g
    rw [← hM]
    exact Submodule.mem_map
  have P1 : ∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔
      Matrix.vecMul l Pm ∈ afLat p MM := by
    intro l
    rw [mem_af]
    constructor
    · rintro ⟨g, hg, h⟩
      obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
      refine ⟨_, hst h' hh', fun x => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((x j).val : RC)) (fun k => χ (π x k))
        (fun k => hc k x) l
      have e2 := h (π x)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
    · rintro ⟨g, hg, h⟩
      refine ⟨_, (hMM _).2 ⟨g, hg, rfl⟩, fun y => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((i y j).val : RC)) (fun k => χ (π (i y) k))
        (fun k => hc k (i y)) l
      rw [hπ] at e1
      have e2 := h (i y)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
  have hco : ∀ u ∈ D.af RC p (fun a => (χ a : C)), ∀ k, u k ∈ RC := by
    intro u hu k
    obtain ⟨g, hg, h⟩ := (mem_af RC p D _ u).1 hu
    obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
    have e1 := pInt_mem RC p (h (Pi.single k 1))
    have e2 : ∑ j, u j * ((χ ((Pi.single k 1 : Fin n → F) j) : RC) : C) = u k := by
      rw [Finset.sum_eq_single k]
      · simp [h1]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj, h0]
      · simp
    rw [e2] at e1
    have e3 : h' (i (Pi.single k 1)) ∈ RC := by
      have := hint hh'
      obtain ⟨a, ha⟩ := this (i (Pi.single k 1))
      rw [← ha]
      exact a.2
    simpa using RC.add_mem e1 e3
  refine ⟨P1, fun u => ?_⟩
  rw [LieLatticeData.hh, mem_dotDual]
  constructor
  · intro h l hl
    rw [dot_eq]
    refine h _ ((P1 _).2 ?_)
    rw [Matrix.vecMul_vecMul]
    exact hAF l hl
  · intro h l hl
    let l' : Fin n → RC := fun k => ⟨l k, hco l hl k⟩
    have e := h _ ((P1 l').1 hl)
    rw [dot_eq, Matrix.vecMul_vecMul, hPJ, Matrix.vecMul_one] at e
    exact e
