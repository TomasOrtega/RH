import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlbHZeroRight

open ValuativeRel Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open Formalism.MainNotions.S

def act {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] (P : Matrix ι ι R)
    (v : ι → N) : ι → N :=
  fun a => ∑ i, P i a • v i

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [act, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem act_act {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι]
    (P Q : Matrix ι ι R) (v : ι → N) : act Q (act P v) = act (P * Q) v := by
  funext a
  simp only [act, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[act, Matrix.one_apply]`.
-/
theorem act_one {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (v : ι → N) : act (1 : Matrix ι ι R) v = v := by
  funext a
  simp [act, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[act, map_sum, map_smul]`.
-/
theorem act_map {R N N' ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N']
    [Module R N'] [Fintype ι] (f : N →ₗ[R] N') (P : Matrix ι ι R) (v : ι → N) :
    (fun a => f (act P v a)) = act P (fun a => f (v a)) := by
  funext a
  simp [act, map_sum, map_smul]

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

def cls (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} (G : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ) :=
  Set.range fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dens_eq_cls (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    (G : Matrix ι ι E) :
    H.dens ϖ Λ G = (Nat.card (cls H ϖ Λ G) : ℝ) /
      (Nat.card 𝓀[F] : ℝ) ^ ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) := rfl

end

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
The claim follows from `Submodule.smul_mem (Submodule.span M.L.O {ϖE}) (⟨x, hx⟩ : M.L.O) hy`.
-/
theorem mul_mem_span {ϖE x y : E} (hx : x ∈ M.L.O) (hy : y ∈ Submodule.span M.L.O {ϖE}) :
    x * y ∈ Submodule.span M.L.O {ϖE} := Submodule.smul_mem (Submodule.span M.L.O {ϖE}) (⟨x, hx⟩ : M.L.O) hy

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hv`. Establish `back : act B (act P v) = v` using `by rw [act_act, hPB, act_one]`. Establish `memO : ∀ (Q : Matrix ι ι M.L.O) (w : ι → V) a, act Q w a ∈ Submodule.span M.L.O (Set.range w)` using `fun Q w a => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨fun a => Λ.sum_mem fun i _ => Λ.smul_mem _ (h1 i), ?_, ?_⟩` and prove the remaining obligations. Rewrite `h2`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Establish `E1 : ∀ g : ι → E, ∑ j, (∑ a, g a * (P j a : E)) • v j = ∑ a, g a • act P v a`. Introduce `g`. Simplify using `only [act, Finset.sum_smul, Finset.smul_sum, Subring.smul_def, smul_smul]`. Conclude with `Finset.sum_comm`.

Establish `key : ∀ j, ∑ a, g a * (P j a : E) = 0` using `h2 _ ((E1 g).trans hg)`. Establish `hB'P' : B.map M.L.O.subtype * P.map M.L.O.subtype = 1`. Rewrite using `[← Matrix.map_mul, hBP, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hPg : Matrix.mulVec (P.map M.L.O.subtype) g = 0`. Use function extensionality and compare the values at `j`.

Use `show ∑ a, (P j a : E) * g a = 0`. Conclude with `(Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (key j)`. Establish `hg0 : g = 0`. Rewrite using `[← Matrix.one_mulVec g, ← hB'P', ← Matrix.mulVec_mulVec, hPg, Matrix.mulVec_zero]`. Introduce `i`.

Rewrite using `[hg0]`. Both sides reduce to the same expression. Introduce `x hxΛ hxspan`. Establish `hE : Submodule.span E (Set.range (act P v)) ≤ Submodule.span E (Set.range v)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (P i a : E) (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h'` using `h3 x hxΛ (hE hxspan)`. Establish `hO : Submodule.span M.L.O (Set.range v) ≤ Submodule.span M.L.O (Set.range (act P v))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Establish `e : v a = act B (act P v) a` using `by rw [back]`. Rewrite using `[e]`. Conclude with `memO B (act P v) a`. Conclude with `hO h'`.
-/
theorem prim_act (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P B : Matrix ι ι M.L.O) (hPB : P * B = 1) (hBP : B * P = 1) {v : ι → V} (hv : H.Prim Λ v) :
    H.Prim Λ (act P v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have back : act B (act P v) = v := by rw [act_act, hPB, act_one]
  have memO : ∀ (Q : Matrix ι ι M.L.O) (w : ι → V) a, act Q w a ∈ Submodule.span M.L.O (Set.range w) :=
    fun Q w a => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun a => Λ.sum_mem fun i _ => Λ.smul_mem _ (h1 i), ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have E1 : ∀ g : ι → E, ∑ j, (∑ a, g a * (P j a : E)) • v j = ∑ a, g a • act P v a := by
      intro g
      simp only [act, Finset.sum_smul, Finset.smul_sum, Subring.smul_def, smul_smul]
      exact Finset.sum_comm
    have key : ∀ j, ∑ a, g a * (P j a : E) = 0 := h2 _ ((E1 g).trans hg)
    have hB'P' : B.map M.L.O.subtype * P.map M.L.O.subtype = 1 := by
      rw [← Matrix.map_mul, hBP, Matrix.map_one _ (map_zero _) (map_one _)]
    have hPg : Matrix.mulVec (P.map M.L.O.subtype) g = 0 := by
      funext j
      show ∑ a, (P j a : E) * g a = 0
      exact (Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (key j)
    have hg0 : g = 0 := by
      rw [← Matrix.one_mulVec g, ← hB'P', ← Matrix.mulVec_mulVec, hPg, Matrix.mulVec_zero]
    intro i
    rw [hg0]
    rfl
  · intro x hxΛ hxspan
    have hE : Submodule.span E (Set.range (act P v)) ≤ Submodule.span E (Set.range v) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (P i a : E) (Submodule.subset_span ⟨i, rfl⟩)
    have h' := h3 x hxΛ (hE hxspan)
    have hO : Submodule.span M.L.O (Set.range v) ≤ Submodule.span M.L.O (Set.range (act P v)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have e : v a = act B (act P v) a := by rw [back]
      rw [e]
      exact memO B (act P v) a
    exact hO h'

/- English proof (translation)
Establish `hR : ∀ x y y', H.h x (y + y') = H.h x y + H.h x y'`. Introduce `x y y'`. Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]`. Establish `hS : ∀ (c : E) x y, H.h x (c • y) = M.L.cj c * H.h x y`. Introduce `c x y`.

Rewrite using `[H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]`. Establish `hsumL : ∀ (f : ι → V) y, H.h (∑ i, f i) y = ∑ i, H.h (f i) y` using `fun f y => map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f Finset.univ`. Establish `hsumR : ∀ x (f : ι → V), H.h x (∑ i, f i) = ∑ i, H.h x (f i)` using `fun x f => map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => hR x y y')) f Finset.univ`. Establish `e1 : H.h (act P v b) (act P v a) = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * H.h (v j) (v i)`. Rewrite using `[show act P v b = ∑ j, (P j b : E) • v j from rfl, show act P v a = ∑ i, (P i a : E) • v i from rfl, hsumL]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[H.h_smul_left, hsumR, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hS]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) a b = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * G i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Subring.coe_subtype]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub]`.

Conclude with `mul_mem_span (M.L.O.mul_mem (P j b).2 (PI.UnitaryGroupMassFormula.CntFormula.fl_cj_mem M.L (P i a).2)) (hv i j)`.
-/
theorem gram_act (H : Loc.HermSp M V) (ϖE : E) {ι : Type} [Fintype ι]
    (P : Matrix ι ι M.L.O) (G : Matrix ι ι E) {v : ι → V}
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ Submodule.span M.L.O {ϖE}) (a b : ι) :
    H.h (act P v b) (act P v a) -
        (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) a b
      ∈ Submodule.span M.L.O {ϖE} := by
  have hR : ∀ x y y', H.h x (y + y') = H.h x y + H.h x y' := by
    intro x y y'
    rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]
  have hS : ∀ (c : E) x y, H.h x (c • y) = M.L.cj c * H.h x y := by
    intro c x y
    rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  have hsumL : ∀ (f : ι → V) y, H.h (∑ i, f i) y = ∑ i, H.h (f i) y := fun f y =>
    map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f Finset.univ
  have hsumR : ∀ x (f : ι → V), H.h x (∑ i, f i) = ∑ i, H.h x (f i) := fun x f =>
    map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => hR x y y')) f Finset.univ
  have e1 : H.h (act P v b) (act P v a) = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * H.h (v j) (v i) := by
    rw [show act P v b = ∑ j, (P j b : E) • v j from rfl, show act P v a = ∑ i, (P i a : E) • v i from rfl, hsumL]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.h_smul_left, hsumR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS]
    ring
  have e2 : (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) a b
      = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * G i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Subring.coe_subtype]
    ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  exact mul_mem_span (M.L.O.mul_mem (P j b).2 (PI.UnitaryGroupMassFormula.CntFormula.fl_cj_mem M.L (P i a).2)) (hv i j)

/- English proof (translation)
Introduce and unpack `_ ⟨_, ⟨⟨w, hw1, hw2⟩, rfl⟩, rfl⟩`. Use `⟨⟨act P w, prim_act H Λ P B hPB hBP hw1, gram_act H _ P G hw2⟩, ?_⟩` and prove the remaining obligations. Conclude with `act_map (Submodule.mkQ _) P w`.
-/
theorem cls_act (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (P B : Matrix ι ι M.L.O) (hPB : P * B = 1) (hBP : B * P = 1) (G : Matrix ι ι E) :
    act P '' cls H ϖ Λ G ⊆
      cls H ϖ Λ (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) := by
  rintro _ ⟨_, ⟨⟨w, hw1, hw2⟩, rfl⟩, rfl⟩
  refine ⟨⟨act P w, prim_act H Λ P B hPB hBP hw1, gram_act H _ P G hw2⟩, ?_⟩
  exact act_map (Submodule.mkQ _) P w

/- English proof (translation)
Take `⟨y, hy, hAy⟩` from `hdet`. Use `set P : Matrix ι ι M.L.O := Matrix.of fun i j => ⟨A i j, hA i j⟩ with hPdef`. Establish `hPA : P.map M.L.O.subtype = A`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hdetA : ((P.det : M.L.O) : E) = A.det`. Rewrite using `[← hPA]`. Conclude with `RingHom.map_det M.L.O.subtype P`. Establish `hdetP : P.det * ⟨y, hy⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subring.coe_mul, hdetA]`. Conclude with `hAy`. Use `set B : Matrix ι ι M.L.O := (⟨y, hy⟩ : M.L.O) • P.adjugate with hBdef`. Establish `hPB : P * B = 1`. Rewrite using `[hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdetP, one_smul]`.

Establish `hBP : B * P = 1`. Rewrite using `[hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdetP, one_smul]`. Establish `hmc : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj` using `fun X Y => Matrix.map_mul (f := (M.L.cj : E →+* E))`. Establish `hAB : A * B.map M.L.O.subtype = 1`. Rewrite using `[← hPA, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hG : ((B.map M.L.O.subtype).map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) * B.map M.L.O.subtype = G`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hmc, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = G := by`.

Rewrite using `[hAB, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `h1 : act B '' cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ⊆ cls H ϖ Λ G`. Use `cls_act H ϖ Λ B P hBP hPB ((A.map M.L.cj).transpose * G * A)` as an intermediate fact. Rewrite `this` using `[hG]`. Then use the resulting hypothesis. Establish `h2 : act P '' cls H ϖ Λ G ⊆ cls H ϖ Λ ((A.map M.L.cj).transpose * G * A)`.

Use `cls_act H ϖ Λ P B hPB hBP G` as an intermediate fact. Rewrite `this` using `[hPA]`. Then use the resulting hypothesis. Set `e : cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ≃ cls H ϖ Λ G` to `{ toFun := fun x => ⟨act B x.1, h1 ⟨x.1, x.2, rfl⟩⟩ invFun := fun x => ⟨act P x.1, h2 ⟨x.1, x.2, rfl⟩⟩ left_inv := fun x => Subtype.ext (by show act P (act B x.1) = x.1`. Rewrite using `[act_act, hBP, act_one])`. Use `right_inv := fun x => Subtype.ext (by show act B (act P x.1) = x.1`.

Rewrite using `[act_act, hPB, act_one]) }`. Rewrite using `[dens_eq_cls, dens_eq_cls, Nat.card_congr e]`.
-/
theorem cong_dens (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O)
    (hdet : ∃ y ∈ M.L.O, A.det * y = 1) (G : Matrix ι ι E) :
    H.dens ϖ Λ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ Λ G := by
  obtain ⟨y, hy, hAy⟩ := hdet
  set P : Matrix ι ι M.L.O := Matrix.of fun i j => ⟨A i j, hA i j⟩ with hPdef
  have hPA : P.map M.L.O.subtype = A := by
    ext i j
    rfl
  have hdetA : ((P.det : M.L.O) : E) = A.det := by
    rw [← hPA]
    exact RingHom.map_det M.L.O.subtype P
  have hdetP : P.det * ⟨y, hy⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdetA]
    exact hAy
  set B : Matrix ι ι M.L.O := (⟨y, hy⟩ : M.L.O) • P.adjugate with hBdef
  have hPB : P * B = 1 := by
    rw [hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdetP, one_smul]
  have hBP : B * P = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdetP, one_smul]
  have hmc : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj := fun X Y =>
    Matrix.map_mul (f := (M.L.cj : E →+* E))
  have hAB : A * B.map M.L.O.subtype = 1 := by
    rw [← hPA, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : ((B.map M.L.O.subtype).map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) *
      B.map M.L.O.subtype = G := by
    calc _ = ((A * B.map M.L.O.subtype).map M.L.cj).transpose * G * (A * B.map M.L.O.subtype) := by
            rw [hmc, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
      _ = G := by
            rw [hAB, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
              Matrix.mul_one]
  have h1 : act B '' cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ⊆ cls H ϖ Λ G := by
    have := cls_act H ϖ Λ B P hBP hPB ((A.map M.L.cj).transpose * G * A)
    rwa [hG] at this
  have h2 : act P '' cls H ϖ Λ G ⊆ cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) := by
    have := cls_act H ϖ Λ P B hPB hBP G
    rwa [hPA] at this
  let e : cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ≃ cls H ϖ Λ G :=
    { toFun := fun x => ⟨act B x.1, h1 ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨act P x.1, h2 ⟨x.1, x.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (by
        show act P (act B x.1) = x.1
        rw [act_act, hBP, act_one])
      right_inv := fun x => Subtype.ext (by
        show act B (act P x.1) = x.1
        rw [act_act, hPB, act_one]) }
  rw [dens_eq_cls, dens_eq_cls, Nat.card_congr e]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ M V _ _ H Λ ϖ ι _ _ A a hA hdet`. Conclude with `cong_dens H ϖ Λ A hA hdet _`.
-/
theorem congruence_density : CongStep := by
  intro F E _ _ _ _ _ _ _ M V _ _ H Λ ϖ ι _ _ A a hA hdet
  exact cong_dens H ϖ Λ A hA hdet _

end PI.UnitaryGroupMassFormula.LocDensCorank
