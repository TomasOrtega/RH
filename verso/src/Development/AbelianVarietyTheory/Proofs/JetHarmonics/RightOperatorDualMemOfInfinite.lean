import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.RhvPoly

inductive IsPol {V : Type} [AddCommGroup V] [Module ℂ V] : (ℂ → V) → Prop
  | const (a : V) : IsPol fun _ => a
  | add {f g : ℂ → V} : IsPol f → IsPol g → IsPol fun y => f y + g y
  | xsmul {f : ℂ → V} : IsPol f → IsPol fun y => y • f y

section module

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Proceed by induction on `hf with`. Consider the case `const a => exact IsPol.const _`. Consider the case `add _ _ h1 h2 => simpa only [map_add] using h1.add h2`. Consider the case `xsmul _ h => simpa only [map_smul] using h.xsmul`.
-/
theorem IsPol.map {f : ℂ → V} (hf : IsPol f) (φ : V →ₗ[ℂ] W) : IsPol fun y => φ (f y) := by
  induction hf with
  | const a => exact IsPol.const _
  | add _ _ h1 h2 => simpa only [map_add] using h1.add h2
  | xsmul _ h => simpa only [map_smul] using h.xsmul

end module

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Proceed by induction on `hf with`. Consider the case `const a => exact hg.map (LinearMap.mulLeft ℂ a)`. Consider the case `add _ _ h1 h2 => simpa only [add_mul] using h1.add h2`. Consider the case `xsmul _ h => simpa only [smul_mul_assoc] using h.xsmul`.
-/
theorem IsPol.mul {f g : ℂ → A} (hf : IsPol f) (hg : IsPol g) : IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact hg.map (LinearMap.mulLeft ℂ a)
  | add _ _ h1 h2 => simpa only [add_mul] using h1.add h2
  | xsmul _ h => simpa only [smul_mul_assoc] using h.xsmul

end alg

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
private lemma isPol_finset_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → V}
    (hf : ∀ i ∈ s, _root_.GlobalTheory.RhvPoly.IsPol (f i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v`. Consider the case `succ n ih`. Simplify using `only [pow_succ', mul_smul]`. Conclude with `ih.xsmul`.
-/
private lemma isPol_pow_smul (n : ℕ) (v : V) : _root_.GlobalTheory.RhvPoly.IsPol fun y : ℂ => y ^ n • v := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    exact ih.xsmul

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Simplify using `only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]`. Use `isPol_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Use `isPol_pow_smul i (p.coeff i • v) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Conclude with `smul_comm _ _ _`.
-/
private lemma isPol_eval_smul (p : Polynomial ℂ) (v : V) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => p.eval y • v := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]
  refine isPol_finset_sum _ fun i _ => ?_
  convert isPol_pow_smul i (p.coeff i • v) using 1
  funext y
  exact smul_comm _ _ _

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
/- English proof (translation)
Establish `h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ)`. Introduce `y`. Use extensionality with `ρ'`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Simplify using `only [h, map_sum, map_smul]`.

Conclude with `isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _`.
-/
private lemma isPol_linearMap_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℂ) →ₗ[ℂ] A)
    (p : ι → Polynomial ℂ) : _root_.GlobalTheory.RhvPoly.IsPol fun y => g (fun ρ => (p ρ).eval y) := by
  have h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ) := by
    intro y
    ext ρ'
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [h, map_sum, map_smul]
  exact isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Proceed by induction on `hf with`. Consider the case `const a => exact .const _`. Consider the case `add _ _ ihf ihg => simpa only [map_add] using ihf.add ihg`. Consider the case `xsmul _ ih => simpa only [map_smul] using ih.xsmul`.
-/
private lemma isPol_linearMap_comp (g : V →ₗ[ℂ] W) {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => g (f y) := by
  induction hf with
  | const a => exact .const _
  | add _ _ ihf ihg => simpa only [map_add] using ihf.add ihg
  | xsmul _ ih => simpa only [map_smul] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
/- English proof (translation)
Proceed by induction on `hf with`. Consider the case `const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg`. Consider the case `add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg`. Consider the case `xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul`.
-/
private lemma isPol_mul {f g : ℂ → A} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (hg : _root_.GlobalTheory.RhvPoly.IsPol g) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg
  | add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg
  | xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
/- English proof (translation)
Simplify `isPol_eval_smul p (1 : A)` using `[Algebra.algebraMap_eq_smul_one]`.
-/
private lemma isPol_algebraMap_eval (p : Polynomial ℂ) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => algebraMap ℂ A (p.eval y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPol_eval_smul p (1 : A)

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)`. Consider the case `cons a l ih => simpa using isPol_mul (hF a) ih`.
-/
private lemma isPol_list_prod {ι : Type} (l : List ι) {F : ι → ℂ → A}
    (hF : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol (F i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => (l.map fun i => F i y).prod := by
  induction l with
  | nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)
  | cons a l ih => simpa using isPol_mul (hF a) ih

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
/- English proof (translation)
Establish `hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i`. Introduce `i`. Establish `: (fun y => L.Tvl y i) = fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0]`. Use function extensionality and compare the values at `y`. Unfold `_root_.Formalism.FourierDecayAlt.R.LevelData.Tvl`.

Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]`. Rewrite using `[this]`. Conclude with `(_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)`. Establish `h : (fun y => L.Tvprod y) = fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod`.

Use function extensionality and compare the values at `y`. Unfold `_root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod`. Simplify using `[List.ofFn_eq_map, List.map_reverse]`. Rewrite using `[h]`. Conclude with `isPol_list_prod _ hT`.
-/
private lemma isPol_Tvprod' {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvprod y := by
  have hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i := by
    intro i
    have : (fun y => L.Tvl y i) =
        fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0] := by
      funext y
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvl
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    rw [this]
    exact (_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)
  have h : (fun y => L.Tvprod y) =
      fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod := by
    funext y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod
    simp [List.ofFn_eq_map, List.map_reverse]
  rw [h]
  exact isPol_list_prod _ hT

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Proceed by induction on `hf with`. Consider the case `const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩`. Consider the case `add _ _ ihf ihg`. Take `⟨p, hp⟩` from `ihf`. Take `⟨q, hq⟩` from `ihg`.

Conclude with `⟨p + q, fun y => by simp [hp, hq]⟩`. Consider the case `xsmul _ ih`. Take `⟨p, hp⟩` from `ih`. Conclude with `⟨Polynomial.X * p, fun y => by simp [hp]⟩`.
-/
private lemma exists_polynomial_eq_functional_of_isPol {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (φ : V →ₗ[ℂ] ℂ) :
    ∃ p : Polynomial ℂ, ∀ y, φ (f y) = p.eval y := by
  induction hf with
  | const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, fun y => by simp [hp, hq]⟩
  | xsmul _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨Polynomial.X * p, fun y => by simp [hp]⟩

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
/- English proof (translation)
Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `φ`. Take `⟨p, hp⟩` from `exists_polynomial_eq_functional_of_isPol hf φ`. Establish `: p = 0` using `Polynomial.eq_zero_of_infinite_isRoot p (hS.mono fun x hx => by simp [← hp, h0 x hx])`. Simplify using `[hp, this]`.
-/
private lemma isPol_eq_zero_of_infinite_zeros {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) {S : Set ℂ}
    (hS : S.Infinite) (h0 : ∀ y ∈ S, f y = 0) (y : ℂ) : f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨p, hp⟩ := exists_polynomial_eq_functional_of_isPol hf φ
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    (hS.mono fun x hx => by simp [← hp, h0 x hx])
  simp [hp, this]

open MeasureTheory in

/- English proof (translation)
Introduce `P A _ _ _ d K S hS hmem y`. Establish `hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y`. Use `isPol_linearMap_eval d.κ.toLinearMap (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))` as an intermediate fact. Use `this using 2 with y` and compare the differences between its conclusion and the goal. Unfold `_root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC`.

Simplify using `[Polynomial.eval_prod]`. Establish `hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y`. Unfold `_root_.Formalism.FourierDecayAlt.Q.NFData.S12`. Use `isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)` and prove the remaining obligations. Use `isPol_linearMap_eval d.κ.toLinearMap (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))` as an intermediate fact.

Use `this using 2 with y` and compare the differences between its conclusion and the goal. Unfold `_root_.Formalism.FourierDecayAlt.M.xEx`. Simplify using `[Polynomial.eval_prod]`. Establish `hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y`. Use `(_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi))) (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))` as an intermediate fact.

Use `this using 2 with y` and compare the differences between its conclusion and the goal. Unfold `_root_.Formalism.FourierDecayAlt.R.LevelData.m0`. Simplify using `[sub_eq_add_neg]`. Establish `hTv` using `isPol_Tvprod' d.L`. Apply the tactic sequence `have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j := fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv`.

Establish `hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y`. Establish `h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y => d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 + d.L.GG * d.x y * d.L.Tvprod y 1 0)`. Use function extensionality and compare the values at `y`. Unfold `_root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Apply the tactic sequence `refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12) (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))`. Establish `hq` using `isPol_linearMap_comp K.mkQ hpol`. Use `isPol_eq_zero_of_infinite_zeros hq hS (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y` as an intermediate fact. Conclude with `(Submodule.Quotient.mk_eq_zero K).1 this`.
-/
theorem _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A]
    (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite →
    (∀ y ∈ S, _root_.GlobalTheory.HatNF.rhv d y ∈ K) → ∀ y : ℂ, _root_.GlobalTheory.HatNF.rhv d y ∈ K := by
  intro P A _ _ _ d K S hS hmem y
  classical
  have hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y := by
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC
    simp [Polynomial.eval_prod]
  have hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y := by
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.S12
    refine isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.M.xEx
    simp [Polynomial.eval_prod]
  have hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y := by
    have := (_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add
      (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi)))
        (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.m0
    simp [sub_eq_add_neg]
  have hTv := isPol_Tvprod' d.L
  have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j :=
    fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv
  have hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y := by
    have h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y =>
        d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 +
          d.L.GG * d.x y * d.L.Tvprod y 1 0) := by
      funext y
      unfold _root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr
      simp
    rw [h]
    refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12)
      (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))
  have hq := isPol_linearMap_comp K.mkQ hpol
  have := isPol_eq_zero_of_infinite_zeros hq hS
    (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y
  exact (Submodule.Quotient.mk_eq_zero K).1 this

end GlobalTheory.RhvPoly
