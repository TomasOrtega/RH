import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationGenerator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdFamL

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealHCLv

open PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)

variable {n : ℕ}

abbrev FA (n : ℕ) : Type := FreeAlgebra ℂ (Bool × Fin n × Fin n)

abbrev lt (s : Bool) (a b : Fin n) : FA n := FreeAlgebra.ι ℂ (s, a, b)

inductive Rl : FA n → FA n → Prop
  | gl (s : Bool) (a b c d : Fin n) : Rl (lt s a b * lt s c d - lt s c d * lt s a b)
      ((if b = c then lt s a d else 0) - (if d = a then lt s c b else 0))
  | cm (a b c d : Fin n) : Rl (lt true a b * lt false c d) (lt false c d * lt true a b)

abbrev UE (n : ℕ) : Type := RingQuot (Rl (n := n))

def uL (s : Bool) (a b : Fin n) : UE n := RingQuot.mkAlgHom ℂ Rl (lt s a b)

/- English proof (translation)
Establish `h` using `RingQuot.mkAlgHom_rel ℂ (Rl.gl s a b c d)`. Simplify using `only [map_sub, map_mul, apply_ite (RingQuot.mkAlgHom ℂ (Rl (n := n))), map_zero] at h`. Conclude with `h`.
-/
theorem uL_gl (s : Bool) (a b c d : Fin n) : uL s a b * uL s c d - uL s c d * uL s a b =
    (if b = c then uL s a d else 0) - (if d = a then uL s c b else 0) := by
  have h := RingQuot.mkAlgHom_rel ℂ (Rl.gl s a b c d)
  simp only [map_sub, map_mul, apply_ite (RingQuot.mkAlgHom ℂ (Rl (n := n))), map_zero] at h
  exact h

/- English proof (translation)
Establish `h` using `RingQuot.mkAlgHom_rel ℂ (Rl.cm a b c d)`. Simplify using `only [map_mul] at h`. Conclude with `h`.
-/
theorem uL_cm (a b c d : Fin n) : uL true a b * uL false c d = uL false c d * uL true a b := by
  have h := RingQuot.mkAlgHom_rel ℂ (Rl.cm a b c d)
  simp only [map_mul] at h
  exact h

def EU (s : Bool) : Fin n → Fin n → Module.End ℂ (UE n) := fun a b => Algebra.lmul ℂ (UE n) (uL s a b)

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `congrArg (Algebra.lmul ℂ (UE n)) (uL_gl s a b c d)`. Simplify using `only [map_sub, map_mul, apply_ite (Algebra.lmul ℂ (UE n)), map_zero] at h`. Conclude with `h`.
-/
theorem EU_gl (s : Bool) : GlRel (EU (n := n) s) := by
  intro a b c d
  have h := congrArg (Algebra.lmul ℂ (UE n)) (uL_gl s a b c d)
  simp only [map_sub, map_mul, apply_ite (Algebra.lmul ℂ (UE n)), map_zero] at h
  exact h

/- English proof (translation)
Use `⟨EU_gl true, EU_gl false, fun a b c d => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Algebra.lmul ℂ (UE n)) (uL_cm a b c d)`. Simplify using `only [map_mul] at h`. Conclude with `h`.
-/
theorem EU_pair : IsPairA (EU (n := n) true) (EU false) := by
  refine ⟨EU_gl true, EU_gl false, fun a b c d => ?_⟩
  have h := congrArg (Algebra.lmul ℂ (UE n)) (uL_cm a b c d)
  simp only [map_mul] at h
  exact h

section Lift

variable {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Simplify using `[GlobalTheory.CompanionTheory.PairMult.ev2]`.
-/
theorem evalPair_letter_true (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2 (lt true a b) = E1 a b := by
  simp [GlobalTheory.CompanionTheory.PairMult.ev2]

/- English proof (translation)
Simplify using `[GlobalTheory.CompanionTheory.PairMult.ev2]`.
-/
theorem evalPair_letter_false (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2 (lt false a b) = E2 a b := by
  simp [GlobalTheory.CompanionTheory.PairMult.ev2]

def rho (h : IsPairA E1 E2) : UE n →ₐ[ℂ] Module.End ℂ V :=
  RingQuot.liftAlgHom ℂ ⟨GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2, by
    intro x y hxy
    cases hxy with
    | gl s a b c d =>
      cases s
      · simp only [map_sub, map_mul, apply_ite (GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2), map_zero, evalPair_letter_false]
        exact h.2.1 a b c d
      · simp only [map_sub, map_mul, apply_ite (GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2), map_zero, evalPair_letter_true]
        exact h.1 a b c d
    | cm a b c d =>
      simp only [map_mul, evalPair_letter_true, evalPair_letter_false]
      exact h.2.2 a b c d⟩

/- English proof (translation)
Simplify using `[rho, uL, evalPair_letter_true, RingQuot.liftAlgHom_mkAlgHom_apply]`.
-/
theorem rho_true (h : IsPairA E1 E2) (a b : Fin n) : rho h (uL true a b) = E1 a b := by
  simp [rho, uL, evalPair_letter_true, RingQuot.liftAlgHom_mkAlgHom_apply]

/- English proof (translation)
Simplify using `[rho, uL, evalPair_letter_false, RingQuot.liftAlgHom_mkAlgHom_apply]`.
-/
theorem rho_false (h : IsPairA E1 E2) (a b : Fin n) : rho h (uL false a b) = E2 a b := by
  simp [rho, uL, evalPair_letter_false, RingQuot.liftAlgHom_mkAlgHom_apply]

def piV (h : IsPairA E1 E2) (x : V) : UE n →ₗ[ℂ] V where
  toFun t := rho h t x
  map_add' s t := by simp
  map_smul' c t := by simp

/- English proof (translation)
Simplify using `[piV]`.
-/
theorem piV_one (h : IsPairA E1 E2) (x : V) : piV h x 1 = x := by simp [piV]

/- English proof (translation)
Simplify using `[piV, EU, rho_true]`.
-/
theorem piV_true (h : IsPairA E1 E2) (x : V) (a b : Fin n) (t : UE n) :
    piV h x (EU true a b t) = E1 a b (piV h x t) := by
  simp [piV, EU, rho_true]

/- English proof (translation)
Simplify using `[piV, EU, rho_false]`.
-/
theorem piV_false (h : IsPairA E1 E2) (x : V) (a b : Fin n) (t : UE n) :
    piV h x (EU false a b t) = E2 a b (piV h x t) := by
  simp [piV, EU, rho_false]

end Lift

section RU

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def RU (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ a b v, lev a < lev b ∧ (y = E1 a b v ∨ y = E2 a b v)}

/- English proof (translation)
Simplify using `only [RU, or_comm]`.
-/
theorem RU_comm (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : RU lev E1 E2 = RU lev E2 E1 := by
  simp only [RU, or_comm]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, b, v, h, Or.inl rfl⟩`.
-/
theorem left_mem (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {a b : Fin n} (h : lev a < lev b) (v : V) :
    E1 a b v ∈ RU lev E1 E2 :=
  Submodule.subset_span ⟨a, b, v, h, Or.inl rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, b, v, h, Or.inr rfl⟩`.
-/
theorem right_mem (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {a b : Fin n} (h : lev a < lev b) (v : V) :
    E2 a b v ∈ RU lev E1 E2 :=
  Submodule.subset_span ⟨a, b, v, h, Or.inr rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨a, b, v, hab, rfl | rfl⟩`. Establish `h` using `congrArg (fun T : Module.End ℂ V => T v) (hG p q a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Establish `h' : G p q (G a b v) = G a b (G p q v) + (((if q = a then G p b else 0) - (if b = p then G a q else 0) : Module.End ℂ V) v)`.

Rewrite using `[LinearMap.sub_apply, ← h]`. Normalize the expressions using the abelian group laws. Use `show G p q (G a b v) ∈ RU lev G H`. Rewrite using `[h']`. Use `add_mem (left_mem lev G H hab _) ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.sub_apply]`. Use `sub_mem ?_ ?_` and prove the remaining obligations. Use `split_ifs with e`. Substitute `e; exact left_mem lev G H (by omega) _` using the available equality. Simplify using the standard rewrite rules.

Use `split_ifs with e`. Substitute `e; exact left_mem lev G H (by omega) _` using the available equality. Simplify using the standard rewrite rules. Establish `h` using `congrArg (fun T : Module.End ℂ V => T v) (hc p q a b)`. Simplify using `only [Module.End.mul_apply] at h`.

Use `show G p q (H a b v) ∈ RU lev G H`. Rewrite using `[h]`. Conclude with `right_mem lev G H hab _`.
-/
theorem RU_stab (lev : Fin n → ℕ) {G H : Fin n → Fin n → Module.End ℂ V} (hG : GlRel G)
    (hc : ∀ a b c d, G a b * H c d = H c d * G a b) {p q : Fin n} (hpq : lev p = lev q) :
    RU lev G H ≤ (RU lev G H).comap (G p q) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, b, v, hab, rfl | rfl⟩
  · have h := congrArg (fun T : Module.End ℂ V => T v) (hG p q a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have h' : G p q (G a b v) = G a b (G p q v) +
        (((if q = a then G p b else 0) - (if b = p then G a q else 0) : Module.End ℂ V) v) := by
      rw [LinearMap.sub_apply, ← h]; abel
    show G p q (G a b v) ∈ RU lev G H
    rw [h']
    refine add_mem (left_mem lev G H hab _) ?_
    rw [LinearMap.sub_apply]
    refine sub_mem ?_ ?_
    · split_ifs with e
      · subst e; exact left_mem lev G H (by omega) _
      · simp
    · split_ifs with e
      · subst e; exact left_mem lev G H (by omega) _
      · simp
  · have h := congrArg (fun T : Module.End ℂ V => T v) (hc p q a b)
    simp only [Module.End.mul_apply] at h
    show G p q (H a b v) ∈ RU lev G H
    rw [h]
    exact right_mem lev G H hab _

end RU

section Quot

variable (lev : Fin n → ℕ)

abbrev WQ : Type := UE n ⧸ RU lev (EU (n := n) true) (EU false)

/- English proof (translation)
Consider the cases of `s`. Rewrite using `[RU_comm]`. Conclude with `RU_stab lev (EU_gl false) (fun a b c d => (EU_pair.2.2 c d a b).symm) hpq`. Conclude with `RU_stab lev (EU_gl true) EU_pair.2.2 hpq`.
-/
theorem EU_stab (s : Bool) {p q : Fin n} (hpq : lev p = lev q) :
    RU lev (EU (n := n) true) (EU false) ≤ (RU lev (EU (n := n) true) (EU false)).comap (EU s p q) := by
  cases s
  · rw [RU_comm]
    exact RU_stab lev (EU_gl false) (fun a b c d => (EU_pair.2.2 c d a b).symm) hpq
  · exact RU_stab lev (EU_gl true) EU_pair.2.2 hpq

def XW (s : Bool) (p q : Fin n) : Module.End ℂ (WQ (n := n) lev) :=
  if h : lev p = lev q then Submodule.mapQ _ _ (EU s p q) (EU_stab lev s h) else 0

/- English proof (translation)
Simplify using `[XW, h]`.
-/
theorem XW_mk (s : Bool) {p q : Fin n} (h : lev p = lev q) (t : UE n) :
    XW lev s p q (Submodule.Quotient.mk t) = Submodule.Quotient.mk (EU s p q t) := by
  simp [XW, h]

/- English proof (translation)
Establish `key : ∀ (s : Bool) (p q r v : Fin n), lev p = lev q → lev r = lev v → XW lev s p q * XW lev s r v - XW lev s r v * XW lev s p q = (if q = r then XW lev s p v else 0) - (if v = p then XW lev s r q else 0)`. Introduce `s p q r v h1 h2`. Use `Submodule.linearMap_qext _ (LinearMap.ext fun t => ?_)` and prove the remaining obligations. Establish `h` using `congrArg (fun T : Module.End ℂ (UE n) => T t) (EU_gl s p q r v)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`.

Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply]`. Rewrite using `[XW_mk lev s h2, XW_mk lev s h1, XW_mk lev s h1, XW_mk lev s h2, ← Submodule.Quotient.mk_sub, h, Submodule.Quotient.mk_sub]`. Use `congr 1`. Use `split_ifs with e`. Substitute `e` using the available equality.

Rewrite using `[XW_mk lev s (h1.trans h2)]`. Simplify using the standard rewrite rules. Use `split_ifs with e`. Substitute `e` using the available equality. Rewrite using `[XW_mk lev s (h2.trans h1)]`.

Simplify using the standard rewrite rules. Use `⟨key true, key false, fun p q r v h1 h2 => ?_⟩` and prove the remaining obligations. Use `Submodule.linearMap_qext _ (LinearMap.ext fun t => ?_)` and prove the remaining obligations. Establish `h` using `congrArg (fun T : Module.End ℂ (UE n) => T t) (EU_pair.2.2 p q r v)`. Simplify using `only [Module.End.mul_apply] at h`.

Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply]`. Rewrite using `[XW_mk lev _ h2, XW_mk lev _ h1, XW_mk lev _ h1, XW_mk lev _ h2, h]`.
-/
theorem XW_lrel : GlobalTheory.CompanionTheory.PairMult.LRel lev (XW (n := n) lev true) (XW lev false) := by
  have key : ∀ (s : Bool) (p q r v : Fin n), lev p = lev q → lev r = lev v →
      XW lev s p q * XW lev s r v - XW lev s r v * XW lev s p q =
        (if q = r then XW lev s p v else 0) - (if v = p then XW lev s r q else 0) := by
    intro s p q r v h1 h2
    refine Submodule.linearMap_qext _ (LinearMap.ext fun t => ?_)
    have h := congrArg (fun T : Module.End ℂ (UE n) => T t) (EU_gl s p q r v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply]
    rw [XW_mk lev s h2, XW_mk lev s h1, XW_mk lev s h1, XW_mk lev s h2, ← Submodule.Quotient.mk_sub, h,
      Submodule.Quotient.mk_sub]
    congr 1
    · split_ifs with e
      · subst e; rw [XW_mk lev s (h1.trans h2)]
      · simp
    · split_ifs with e
      · subst e; rw [XW_mk lev s (h2.trans h1)]
      · simp
  refine ⟨key true, key false, fun p q r v h1 h2 => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun t => ?_)
  have h := congrArg (fun T : Module.End ℂ (UE n) => T t) (EU_pair.2.2 p q r v)
  simp only [Module.End.mul_apply] at h
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply]
  rw [XW_mk lev _ h2, XW_mk lev _ h1, XW_mk lev _ h1, XW_mk lev _ h2, h]

end Quot

/- English proof (translation)
Proceed by induction on `b using FreeAlgebra.induction generalizing v with`. Consider the case `grade0 r => simp [Module.algebraMap_end_apply]`. Consider the case `grade1 x`. Take `⟨s, p, q⟩` from `x`. Simplify using `only [GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]`.

Distinguish the cases in `h : lev p = lev q`. Apply the tactic sequence `cases s <;> simp [h, h1, h2]`. Simplify using `[h]`. Consider the case `mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`.
-/
theorem evB_inter {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (lev : Fin n → ℕ)
    (X1 X2 : Fin n → Fin n → Module.End ℂ V) (Y1 Y2 : Fin n → Fin n → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h1 : ∀ p q, lev p = lev q → ∀ v, f (X1 p q v) = Y1 p q (f v))
    (h2 : ∀ p q, lev p = lev q → ∀ v, f (X2 p q v) = Y2 p q (f v)) (b : FA n) (v : V) :
    f (GlobalTheory.CompanionTheory.PairMult.evB lev X1 X2 b v) = GlobalTheory.CompanionTheory.PairMult.evB lev Y1 Y2 b (f v) := by
  induction b using FreeAlgebra.induction generalizing v with
  | grade0 r => simp [Module.algebraMap_end_apply]
  | grade1 x =>
    obtain ⟨s, p, q⟩ := x
    simp only [GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]
    by_cases h : lev p = lev q
    · cases s <;> simp [h, h1, h2]
    · simp [h]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

section Letters

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def toE : FA n →ₐ[ℂ] FA n :=
  FreeAlgebra.lift ℂ fun g => if g.1 then lt true g.2.1 g.2.2 - lt false g.2.1 g.2.2
    else lt true g.2.1 g.2.2 + lt false g.2.1 g.2.2

def toK : FA n →ₐ[ℂ] FA n :=
  FreeAlgebra.lift ℂ fun g => if g.1 then (1 / 2 : ℂ) • (lt false g.2.1 g.2.2 + lt true g.2.1 g.2.2)
    else (1 / 2 : ℂ) • (lt false g.2.1 g.2.2 - lt true g.2.1 g.2.2)

/- English proof (translation)
Establish `h : (GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2).comp toE = evKP E1 E2`. Use `FreeAlgebra.hom_ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨s, p, q⟩` from `g`. Apply the tactic sequence `cases s <;> simp [toE, evKP, kA, pA, evalPair_letter_true, evalPair_letter_false]`. Conclude with `DFunLike.congr_fun h a`.
-/
theorem evalPair_toE_eq_evalKPair (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a : FA n) :
    GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2 (toE a) = evKP E1 E2 a := by
  have h : (GlobalTheory.CompanionTheory.PairMult.ev2 E1 E2).comp toE = evKP E1 E2 := by
    refine FreeAlgebra.hom_ext (funext fun g => ?_)
    obtain ⟨s, p, q⟩ := g
    cases s <;> simp [toE, evKP, kA, pA, evalPair_letter_true, evalPair_letter_false]
  exact DFunLike.congr_fun h a

/- English proof (translation)
Establish `h : (evLv lev E1 E2).comp toK = GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2`. Use `FreeAlgebra.hom_ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨s, p, q⟩` from `g`. Distinguish the cases in `e : lev p = lev q`. Consider the cases of `s`.

Simplify using `only [Function.comp, AlgHom.comp_apply, toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]`. Simplify using `only [e, if_true, Bool.false_eq_true, if_false, map_smul, map_sub, FreeAlgebra.lift_ι_apply, kA, pA]`. Use `module`. Simplify using `only [Function.comp, AlgHom.comp_apply, toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]`. Simplify using `only [e, if_true, Bool.false_eq_true, if_false, map_smul, map_add, FreeAlgebra.lift_ι_apply, kA, pA]`.

Use `module`. Apply the tactic sequence `cases s <;> simp [toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, e]`. Conclude with `DFunLike.congr_fun h b`.
-/
theorem evLv_toK (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (b : FA n) :
    evLv lev E1 E2 (toK b) = GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b := by
  have h : (evLv lev E1 E2).comp toK = GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 := by
    refine FreeAlgebra.hom_ext (funext fun g => ?_)
    obtain ⟨s, p, q⟩ := g
    by_cases e : lev p = lev q
    · cases s
      · simp only [Function.comp, AlgHom.comp_apply, toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]
        simp only [e, if_true, Bool.false_eq_true, if_false, map_smul, map_sub, FreeAlgebra.lift_ι_apply, kA, pA]
        module
      · simp only [Function.comp, AlgHom.comp_apply, toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, FreeAlgebra.lift_ι_apply]
        simp only [e, if_true, Bool.false_eq_true, if_false, map_smul, map_add, FreeAlgebra.lift_ι_apply, kA, pA]
        module
    · cases s <;> simp [toK, evLv, GlobalTheory.CompanionTheory.PairMult.evB, e]
  exact DFunLike.congr_fun h b

def Lm (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : (Lt n → V) →ₗ[ℂ] V :=
  ∑ l : Lt n, if inUU lev l then (xL E1 E2 l) ∘ₗ LinearMap.proj l else 0

/- English proof (translation)
Simplify using `only [Lm, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Lm_apply (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (w : Lt n → V) :
    Lm lev E1 E2 w = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0 := by
  simp only [Lm, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use `⟨Pi.single l v, ?_⟩` and prove the remaining obligations. Rewrite using `[Lm_apply, Finset.sum_eq_single l]`. Simplify using `[h]`. Introduce `m _ hm`. Simplify using `[hm]`.

Simplify using the standard rewrite rules.
-/
theorem xL_mem_range (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {l : Lt n} (h : inUU lev l) (v : V) :
    xL E1 E2 l v ∈ LinearMap.range (Lm lev E1 E2) := by
  refine ⟨Pi.single l v, ?_⟩
  rw [Lm_apply, Finset.sum_eq_single l]
  · simp [h]
  · intro m _ hm
    simp [hm]
  · simp

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨a, b, v, hab, rfl | rfl⟩`. Establish `hlt : a < b` using `hm.reflect_lt hab`. Establish `hK` using `xL_mem_range lev E1 E2 (l := (false, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)`. Establish `hP` using `xL_mem_range lev E1 E2 (l := (true, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)`.

Use `add_mem hK hP` as an intermediate fact. Simplify using `only [xL, kA, pA, Bool.false_eq_true, if_false, if_true, map_smul, LinearMap.add_apply, LinearMap.sub_apply] at this`. Establish `e : E1 a b v = (1 / 2 : ℂ) • (E1 a b v + E2 a b v) + (1 / 2 : ℂ) • (E1 a b v - E2 a b v)` using `by module`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `this`.

Establish `hlt : a < b` using `hm.reflect_lt hab`. Establish `hK` using `xL_mem_range lev E1 E2 (l := (false, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)`. Establish `hP` using `xL_mem_range lev E1 E2 (l := (true, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)`. Use `sub_mem hK hP` as an intermediate fact. Simplify using `only [xL, kA, pA, Bool.false_eq_true, if_false, if_true, map_smul, LinearMap.add_apply, LinearMap.sub_apply] at this`.

Establish `e : E2 a b v = (1 / 2 : ℂ) • (E1 a b v + E2 a b v) - (1 / 2 : ℂ) • (E1 a b v - E2 a b v)` using `by module`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `this`.
-/
theorem RU_le_range {lev : Fin n → ℕ} (hm : Monotone lev) (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    RU lev E1 E2 ≤ LinearMap.range (Lm lev E1 E2) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, b, v, hab, rfl | rfl⟩
  · have hlt : a < b := hm.reflect_lt hab
    have hK := xL_mem_range lev E1 E2 (l := (false, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)
    have hP := xL_mem_range lev E1 E2 (l := (true, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)
    have := add_mem hK hP
    simp only [xL, kA, pA, Bool.false_eq_true, if_false, if_true, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply] at this
    have e : E1 a b v = (1 / 2 : ℂ) • (E1 a b v + E2 a b v) + (1 / 2 : ℂ) • (E1 a b v - E2 a b v) := by module
    rw [SetLike.mem_coe, e]
    exact this
  · have hlt : a < b := hm.reflect_lt hab
    have hK := xL_mem_range lev E1 E2 (l := (false, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)
    have hP := xL_mem_range lev E1 E2 (l := (true, ⟨(a, b), hlt⟩)) hab ((1 / 2 : ℂ) • v)
    have := sub_mem hK hP
    simp only [xL, kA, pA, Bool.false_eq_true, if_false, if_true, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply] at this
    have e : E2 a b v = (1 / 2 : ℂ) • (E1 a b v + E2 a b v) - (1 / 2 : ℂ) • (E1 a b v - E2 a b v) := by module
    rw [SetLike.mem_coe, e]
    exact this

/- English proof (translation)
Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Take `⟨s, i⟩` from `l`. Consider the cases of `s`. Simplify using `only [GlobalTheory.CompanionTheory.PairMult.Tl, GlobalTheory.CompanionTheory.PairMult.Ts, Bool.false_eq_true, if_false, LinearMap.sub_apply]`.

Conclude with `sub_mem (left_mem lev E1 E2 h _) (right_mem lev E1 E2 h _)`. Simplify using `only [GlobalTheory.CompanionTheory.PairMult.Tl, GlobalTheory.CompanionTheory.PairMult.Ts, if_true, LinearMap.add_apply]`. Conclude with `add_mem (left_mem lev E1 E2 h _) (right_mem lev E1 E2 h _)`. Conclude with `zero_mem _`.
-/
theorem sum_Tl_mem (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (w : GlobalTheory.CompanionTheory.PairMult.Lt n → V) :
    (∑ l : GlobalTheory.CompanionTheory.PairMult.Lt n, if GlobalTheory.CompanionTheory.PairMult.inUL lev l then GlobalTheory.CompanionTheory.PairMult.Tl E1 E2 l (w l) else 0) ∈
      RU lev E1 E2 := by
  refine sum_mem fun l _ => ?_
  split_ifs with h
  · obtain ⟨s, i⟩ := l
    cases s
    · simp only [GlobalTheory.CompanionTheory.PairMult.Tl, GlobalTheory.CompanionTheory.PairMult.Ts, Bool.false_eq_true, if_false, LinearMap.sub_apply]
      exact sub_mem (left_mem lev E1 E2 h _) (right_mem lev E1 E2 h _)
    · simp only [GlobalTheory.CompanionTheory.PairMult.Tl, GlobalTheory.CompanionTheory.PairMult.Ts, if_true, LinearMap.add_apply]
      exact add_mem (left_mem lev E1 E2 h _) (right_mem lev E1 E2 h _)
  · exact zero_mem _

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨a, b, v, hab, rfl | rfl⟩`. Use `show piV h x (EU true a b v) ∈ RU lev E1 E2`. Rewrite using `[piV_true]`. Conclude with `left_mem lev E1 E2 hab _`.

Use `show piV h x (EU false a b v) ∈ RU lev E1 E2`. Rewrite using `[piV_false]`. Conclude with `right_mem lev E1 E2 hab _`.
-/
theorem RU_map {E1 E2 : Fin n → Fin n → Module.End ℂ V} (lev : Fin n → ℕ) (h : IsPairA E1 E2) (x : V) :
    RU lev (EU (n := n) true) (EU false) ≤ (RU lev E1 E2).comap (piV h x) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, b, v, hab, rfl | rfl⟩
  · show piV h x (EU true a b v) ∈ RU lev E1 E2
    rw [piV_true]; exact left_mem lev E1 E2 hab _
  · show piV h x (EU false a b v) ∈ RU lev E1 E2
    rw [piV_false]; exact right_mem lev E1 E2 hab _

end Letters

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, h.2.2⟩`.
-/
theorem isPairA_of_pairRel {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (h : GlobalTheory.CompanionTheory.PairMult.PairRel E1 E2) : IsPairA E1 E2 := ⟨h.1, h.2.1, h.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, h.2.2⟩`.
-/
theorem pairRel_of_isPairA {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (h : IsPairA E1 E2) : GlobalTheory.CompanionTheory.PairMult.PairRel E1 E2 := ⟨h.1, h.2.1, h.2.2⟩

/- English proof (translation)
Introduce `n lev hm a ha`. Establish `hInv : GlobalTheory.CompanionTheory.PairMult.Inv2 (toE a)`. Introduce `V _ _ E1 E2 hE c d`. Rewrite using `[evalPair_toE_eq_evalKPair]`. Conclude with `ha V E1 E2 (isPairA_of_pairRel hE) c d`.

Take `⟨b0, hb0⟩` from `GlobalTheory.CompanionTheory.PairMult.HCD.hcDec2 n lev (toE a) hm hInv`. Establish `hmem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → ∀ x : V, evKP E1 E2 a x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b0 x ∈ RU lev E1 E2`. Introduce `V _ _ E1 E2 hE x`. Take `⟨w, hw⟩` from `hb0 V E1 E2 (pairRel_of_isPairA hE) x`. Rewrite `hw` using `[evalPair_toE_eq_evalKPair]`.

Rewrite using `[hw]`. Conclude with `sum_Tl_mem lev E1 E2 w`. Establish `hmk : ∀ (b : FA n) (t : UE n), GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b (Submodule.Quotient.mk t) = Submodule.Quotient.mk (GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b t)`. Introduce `b t`. Conclude with `(evB_inter lev (EU true) (EU false) (XW lev true) (XW lev false) (Submodule.mkQ _) (fun p q h v => (XW_mk lev true h v).symm) (fun p q h v => (XW_mk lev false h v).symm) b t).symm`.

Establish `hb0mk : ∀ t : UE n, GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 (Submodule.Quotient.mk t) = Submodule.Quotient.mk (evKP (EU true) (EU false) a t)`. Introduce `t`. Rewrite using `[hmk]`. Conclude with `((Submodule.Quotient.eq _).2 (hmem _ _ _ EU_pair t)).symm`. Establish `hcomm : ∀ p q, lev p = lev q → ∀ s : WQ (n` using `n) lev, (XW lev true p q + XW lev false p q) (GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 s) = GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 ((XW lev true p q + XW lev false p q) s) := by`.

Introduce `p q h s`. Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ s`. Establish `hc` using `congrArg (fun T : Module.End ℂ (UE n) => T t) (ha (UE n) (EU true) (EU false) EU_pair p q).eq`. Simplify using `only [Module.End.mul_apply, kA, LinearMap.add_apply] at hc`. Simplify using `only [LinearMap.add_apply]`.

Rewrite using `[XW_mk lev true h, XW_mk lev false h, ← Submodule.Quotient.mk_add, hb0mk, hb0mk, XW_mk lev true h, XW_mk lev false h, ← Submodule.Quotient.mk_add, hc]`. Take `⟨b', hinv, hact⟩` from `GlobalTheory.CompanionTheory.PairMult.invL n lev (WQ (n := n) lev) (XW lev true) (XW lev false) ⊤ b0 (XW_lrel lev) (fun _ _ _ _ _ => Submodule.mem_top) (fun p q h s _ => hcomm p q h s)`. Use `⟨toK b', ?_, ?_⟩` and prove the remaining obligations. Introduce `H _ _ F1 F2 hF c d hcd`. Rewrite using `[evLv_toK]`.

Use `hinv H F1 F2 ?_ c d hcd` and prove the remaining obligations. Conclude with `⟨fun p q r v h1 h2 => (hF p q r v h1 h2).1, fun p q r v h1 h2 => (hF p q r v h1 h2).2.1, fun p q r v h1 h2 => (hF p q r v h1 h2).2.2⟩`. Introduce `V _ _ E1 E2 hE x`. Rewrite using `[evLv_toK]`. Establish `h1 : GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b' 1 - GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b0 1 ∈ RU lev (EU (n` using `n) true) (EU false) := by`.

Use `hact (Submodule.Quotient.mk 1) Submodule.mem_top` as an intermediate fact. Rewrite `this` using `[hmk, hmk]`. Conclude with `(Submodule.Quotient.eq _).1 this`. Establish `h2` using `RU_map lev hE x h1`. Establish `hpi : ∀ b : FA n, piV hE x (GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b 1) = GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b x`.

Introduce `b`. Rewrite using `[evB_inter lev (EU true) (EU false) E1 E2 (piV hE x) (fun p q _ v => piV_true hE x p q v) (fun p q _ v => piV_false hE x p q v) b 1, piV_one]`. Establish `h3 : GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b' x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b0 x ∈ RU lev E1 E2`. Use `h2` as an intermediate fact. Simplify using `only [Submodule.mem_comap, map_sub, hpi] at this`.

Conclude with `this`. Establish `h4 : evKP E1 E2 a x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b' x ∈ RU lev E1 E2`. Use `sub_mem (hmem V E1 E2 hE x) h3` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Take `⟨w, hw⟩` from `RU_le_range hm E1 E2 h4`. Conclude with `⟨w, by rw [← hw, Lm_apply]⟩`.
-/
theorem hcdecLv : HCdecLv := by
  intro n lev hm a ha

  have hInv : GlobalTheory.CompanionTheory.PairMult.Inv2 (toE a) := by
    intro V _ _ E1 E2 hE c d
    rw [evalPair_toE_eq_evalKPair]
    exact ha V E1 E2 (isPairA_of_pairRel hE) c d
  obtain ⟨b0, hb0⟩ := GlobalTheory.CompanionTheory.PairMult.HCD.hcDec2 n lev (toE a) hm hInv
  have hmem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ x : V, evKP E1 E2 a x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b0 x ∈ RU lev E1 E2 := by
    intro V _ _ E1 E2 hE x
    obtain ⟨w, hw⟩ := hb0 V E1 E2 (pairRel_of_isPairA hE) x
    rw [evalPair_toE_eq_evalKPair] at hw
    rw [hw]
    exact sum_Tl_mem lev E1 E2 w

  have hmk : ∀ (b : FA n) (t : UE n),
      GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b (Submodule.Quotient.mk t) =
        Submodule.Quotient.mk (GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b t) := by
    intro b t
    exact (evB_inter lev (EU true) (EU false) (XW lev true) (XW lev false) (Submodule.mkQ _)
      (fun p q h v => (XW_mk lev true h v).symm) (fun p q h v => (XW_mk lev false h v).symm) b t).symm
  have hb0mk : ∀ t : UE n, GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (evKP (EU true) (EU false) a t) := by
    intro t
    rw [hmk]
    exact ((Submodule.Quotient.eq _).2 (hmem _ _ _ EU_pair t)).symm
  have hcomm : ∀ p q, lev p = lev q → ∀ s : WQ (n := n) lev,
      (XW lev true p q + XW lev false p q) (GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 s) =
        GlobalTheory.CompanionTheory.PairMult.evB lev (XW lev true) (XW lev false) b0 ((XW lev true p q + XW lev false p q) s) := by
    intro p q h s
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ s
    have hc := congrArg (fun T : Module.End ℂ (UE n) => T t) (ha (UE n) (EU true) (EU false) EU_pair p q).eq
    simp only [Module.End.mul_apply, kA, LinearMap.add_apply] at hc
    simp only [LinearMap.add_apply]
    rw [XW_mk lev true h, XW_mk lev false h, ← Submodule.Quotient.mk_add, hb0mk, hb0mk, XW_mk lev true h,
      XW_mk lev false h, ← Submodule.Quotient.mk_add, hc]
  obtain ⟨b', hinv, hact⟩ := GlobalTheory.CompanionTheory.PairMult.invL n lev (WQ (n := n) lev) (XW lev true) (XW lev false) ⊤ b0 (XW_lrel lev)
    (fun _ _ _ _ _ => Submodule.mem_top) (fun p q h s _ => hcomm p q h s)
  refine ⟨toK b', ?_, ?_⟩
  · intro H _ _ F1 F2 hF c d hcd
    rw [evLv_toK]
    refine hinv H F1 F2 ?_ c d hcd
    exact ⟨fun p q r v h1 h2 => (hF p q r v h1 h2).1, fun p q r v h1 h2 => (hF p q r v h1 h2).2.1,
      fun p q r v h1 h2 => (hF p q r v h1 h2).2.2⟩
  · intro V _ _ E1 E2 hE x
    rw [evLv_toK]

    have h1 : GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b' 1 -
        GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b0 1 ∈ RU lev (EU (n := n) true) (EU false) := by
      have := hact (Submodule.Quotient.mk 1) Submodule.mem_top
      rw [hmk, hmk] at this
      exact (Submodule.Quotient.eq _).1 this
    have h2 := RU_map lev hE x h1
    have hpi : ∀ b : FA n, piV hE x (GlobalTheory.CompanionTheory.PairMult.evB lev (EU true) (EU false) b 1) =
        GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b x := by
      intro b
      rw [evB_inter lev (EU true) (EU false) E1 E2 (piV hE x) (fun p q _ v => piV_true hE x p q v)
        (fun p q _ v => piV_false hE x p q v) b 1, piV_one]
    have h3 : GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b' x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b0 x ∈ RU lev E1 E2 := by
      have := h2
      simp only [Submodule.mem_comap, map_sub, hpi] at this
      exact this
    have h4 : evKP E1 E2 a x - GlobalTheory.CompanionTheory.PairMult.evB lev E1 E2 b' x ∈ RU lev E1 E2 := by
      have := sub_mem (hmem V E1 E2 hE x) h3
      convert this using 1
      abel
    obtain ⟨w, hw⟩ := RU_le_range hm E1 E2 h4
    exact ⟨w, by rw [← hw, Lm_apply]⟩

end GlobalTheory.CompanionTheory.RealHCLv
