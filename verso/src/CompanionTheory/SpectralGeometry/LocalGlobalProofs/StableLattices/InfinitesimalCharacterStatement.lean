import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def PolyFn (F : ℂ → A) : Prop := ∃ p : Polynomial A, ∀ u, F u = p.eval (algebraMap ℂ A u)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Polynomial.C c, fun u => by simp⟩`.
-/
theorem PolyFn.const (c : A) : PolyFn (fun _ : ℂ => c) := ⟨Polynomial.C c, fun u => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Polynomial.X, fun u => by simp⟩`.
-/
theorem PolyFn.alg : PolyFn (fun u : ℂ => algebraMap ℂ A u) := ⟨Polynomial.X, fun u => by simp⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Conclude with `⟨p + q, fun u => by simp [hp, hq]⟩`.
-/
theorem PolyFn.add {F G : ℂ → A} (hF : PolyFn F) (hG : PolyFn G) : PolyFn (fun u => F u + G u) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun u => by simp [hp, hq]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Conclude with `⟨p - q, fun u => by simp [hp, hq]⟩`.
-/
theorem PolyFn.sub {F G : ℂ → A} (hF : PolyFn F) (hG : PolyFn G) : PolyFn (fun u => F u - G u) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun u => by simp [hp, hq]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Use `⟨p * q, fun u => ?_⟩` and prove the remaining obligations. Use `show F u * G u = _`. Rewrite using `[hp, hq]`.

Simplify using `only [Polynomial.eval]`. Rewrite using `[Polynomial.eval₂_mul_noncomm]`. Introduce `k`. Conclude with `(Algebra.commutes u _).symm`.
-/
theorem PolyFn.mul {F G : ℂ → A} (hF : PolyFn F) (hG : PolyFn G) : PolyFn (fun u => F u * G u) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  refine ⟨p * q, fun u => ?_⟩
  show F u * G u = _
  rw [hp, hq]
  simp only [Polynomial.eval]
  rw [Polynomial.eval₂_mul_noncomm]
  intro k
  exact (Algebra.commutes u _).symm

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using PolyFn.const (1 : A)`. Consider the case `succ k ih => simpa only [pow_succ] using ih.mul hF`.
-/
theorem PolyFn.pow {F : ℂ → A} (hF : PolyFn F) (k : ℕ) : PolyFn (fun u => F u ^ k) := by
  induction k with
  | zero => simpa using PolyFn.const (1 : A)
  | succ k ih => simpa only [pow_succ] using ih.mul hF

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using PolyFn.const (0 : A)`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `(h i).add ih`.
-/
theorem PolyFn.sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → A} (h : ∀ i, PolyFn (F i)) :
    PolyFn (fun u => ∑ i ∈ s, F i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyFn.const (0 : A)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using PolyFn.const (1 : A)`. Consider the case `succ m ih`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Conclude with `(h 0).mul (ih _ fun k => h k.succ)`.
-/
theorem PolyFn.list {m : ℕ} (F : Fin m → ℂ → A) (h : ∀ k, PolyFn (F k)) :
    PolyFn (fun u => (List.ofFn fun k => F k u).prod) := by
  induction m with
  | zero => simpa using PolyFn.const (1 : A)
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih _ fun k => h k.succ)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using PolyFn.const (1 : A)`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.prod_insert hi, map_mul]`. Conclude with `(h i).mul ih`.
-/
theorem PolyFn.algProd {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i, PolyFn (fun u => algebraMap ℂ A (f i u))) :
    PolyFn (fun u => algebraMap ℂ A (∏ i ∈ s, f i u)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyFn.const (1 : A)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, map_mul]
    exact (h i).mul ih

/- English proof (translation)
Unfold `Tm`. Distinguish the cases in `h : a = b`. Simplify using `only [h, if_true, map_sub]`. Conclude with `(PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)`. Simplify using `only [h, if_false]`.

Conclude with `(PolyFn.const _).add (PolyFn.const _)`.
-/
theorem polyFn_tm {n : ℕ} (E : Fin n → Fin n → A) (c : ℂ) (a b : Fin n) :
    PolyFn (fun u : ℂ => Tm E (u - c) a b) := by
  unfold Tm
  by_cases h : a = b
  · simp only [h, if_true, map_sub]
    exact (PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)
  · simp only [h, if_false]
    exact (PolyFn.const _).add (PolyFn.const _)

/- English proof (translation)
Unfold `qdet qminor`. Use `PolyFn.sum _ fun σ => (PolyFn.const _).mul ?_` and prove the remaining obligations. Conclude with `PolyFn.list (fun (k : Fin n) (u : ℂ) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)) fun k => polyFn_tm E _ _ _`.
-/
theorem polyFn_qdet {n : ℕ} (E : Fin n → Fin n → A) : PolyFn (fun u : ℂ => qdet E u) := by
  unfold qdet qminor
  refine PolyFn.sum _ fun σ => (PolyFn.const _).mul ?_
  exact PolyFn.list (fun (k : Fin n) (u : ℂ) => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
    fun k => polyFn_tm E _ _ _

/- English proof (translation)
Unfold `qdet qminor`. Use `Commute.sum_right _ _ _ fun σ _ => ?_` and prove the remaining obligations. Use `(Int.cast_commute _ O).symm.mul_right (Commute.list_prod_right _ _ fun T hT => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩` from `(List.mem_ofFn' _ _).1 hT`. Unfold `Tm`.

Use `Commute.add_right ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(Algebra.commutes _ _).symm`. Conclude with `Commute.zero_right _`.
-/
theorem commute_qdet {n : ℕ} {E : Fin n → Fin n → A} (O : A) (h : ∀ a b, Commute O (E a b)) (u : ℂ) :
    Commute O (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine (Int.cast_commute _ O).symm.mul_right (Commute.list_prod_right _ _ fun T hT => ?_)
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact (Algebra.commutes _ _).symm
  · exact Commute.zero_right _

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_` and prove the remaining obligations. Establish `key : ∀ p : Polynomial (Module.End ℂ V), ∃ q : Polynomial ℂ, ∀ u, φ ((p.eval (algebraMap ℂ _ u)) v) = q.eval u`.

Introduce `p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨a, ha⟩` from `hp`. Take `⟨b, hb⟩` from `hq`.

Conclude with `⟨a + b, fun u => by simp [ha, hb]⟩`. Consider the case `monomial k T`. Use `⟨Polynomial.monomial k (φ (T v)), fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_monomial, ← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨q, hq⟩` from `key p`. Establish `hq0 : q = 0`. Use `Polynomial.eq_zero_of_infinite_isRoot q (((Set.finite_singleton u₀).infinite_compl).mono fun u hu => ?_)` and prove the remaining obligations. Establish `e` using `hq u`. Rewrite `e` using `[← hp, h u hu]`.

Simplify `e.symm` using `[Polynomial.IsRoot.def]`. Rewrite using `[hp, hq, hq0]`. Simplify using the standard rewrite rules.
-/
theorem PolyFn.vanish {V : Type*} [AddCommGroup V] [Module ℂ V] {F : ℂ → Module.End ℂ V}
    (hF : PolyFn F) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → F u = 0) : F u₀ = 0 := by
  obtain ⟨p, hp⟩ := hF
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have key : ∀ p : Polynomial (Module.End ℂ V), ∃ q : Polynomial ℂ,
      ∀ u, φ ((p.eval (algebraMap ℂ _ u)) v) = q.eval u := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, fun u => by simp [ha, hb]⟩
    | monomial k T =>
      refine ⟨Polynomial.monomial k (φ (T v)), fun u => ?_⟩
      simp only [Polynomial.eval_monomial, ← map_pow, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, smul_eq_mul]
      ring
  obtain ⟨q, hq⟩ := key p
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q
      (((Set.finite_singleton u₀).infinite_compl).mono fun u hu => ?_)
    have e := hq u
    rw [← hp, h u hu] at e
    simpa [Polynomial.IsRoot.def] using e.symm
  rw [hp, hq, hq0]
  simp

/- English proof (translation)
Establish `cA : ∀ (s : ℂ) (T : A), Commute (algebraMap ℂ A s) T` using `fun s T => Algebra.commutes s T`. Take `⟨N, hNdef⟩ : ∃ N, N = c - algebraMap ℂ A (r * w)` from `⟨_, rfl⟩`. Establish `hc : c = N + algebraMap ℂ A (r * w)` using `by rw [hNdef]; abel`. Rewrite `hN` using `[← hNdef]`. Establish `hNν : Commute N ν` using `by rw [hNdef]; exact hcν.sub_left (cA _ _)`.

Take `⟨G, hG⟩ : ∃ G, G = algebraMap ℂ A (w + 1) + ν` from `⟨_, rfl⟩`. Take `⟨g, hg⟩ : ∃ g, g = algebraMap ℂ A w + ν` from `⟨_, rfl⟩`. Take `⟨x, hx⟩ : ∃ x, x = D - algebraMap ℂ A (r * (w + 1))` from `⟨_, rfl⟩`. Take `⟨H, hH⟩ : ∃ H, H = algebraMap ℂ A r * ν` from `⟨_, rfl⟩`. Establish `hxg : x * g = N * G - H`.

Establish `e : x * g = D * g - algebraMap ℂ A (r * (w + 1)) * g` using `by rw [hx, sub_mul]`. Rewrite using `[e, hg, hid, hc, hG, hH]`. Simplify using `only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]`. Use `module`. Establish `hNG : Commute N G` using `by rw [hG]; exact (cA _ _).symm.add_right hNν`.

Establish `hνH : Commute ν H` using `by rw [hH]; exact (cA _ _).symm.mul_right (Commute.refl ν)`. Establish `h1 : (N * G) ^ k = 0` using `by rw [hNG.mul_pow, hN, zero_mul]`. Establish `h2 : (-H) ^ M = 0`. Establish `: H ^ M = 0` using `by rw [hH, (cA _ _).mul_pow, hν, mul_zero]`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ M with e | e <;> simp [neg_pow H, this]`.

Establish `hNH : Commute N H` using `by rw [hH]; exact (cA _ _).symm.mul_right hNν`. Establish `hGH : Commute G H`. Rewrite using `[hG]`. Conclude with `(cA _ _).add_left hνH`. Establish `hcomm : Commute (N * G) (-H)` using `(hNH.mul_left hGH).neg_right`.

Establish `h3 : (x * g) ^ (k + M) = 0`. Rewrite using `[hxg, sub_eq_add_neg]`. Conclude with `hcomm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h1 h2 (by omega)`. Establish `hxc : Commute x g`. Rewrite using `[hx, hg]`.

Conclude with `((cA _ _).symm.sub_left (cA _ _)).add_right (hDν.sub_left (cA _ _))`. Establish `hgu : IsUnit g`. Rewrite using `[hg]`. Conclude with `IsNilpotent.isUnit_add_left_of_commute ⟨M, hν⟩ ((IsUnit.mk0 w hw).map (algebraMap ℂ A)) (cA _ _).symm`. Establish `h4 : x ^ (k + M) * g ^ (k + M) = 0` using `by rw [← hxc.mul_pow, h3]`.

Rewrite using `[← hx]`. Conclude with `(hgu.pow _).mul_left_eq_zero.1 h4`.
-/
theorem core {D c ν : A} {k M : ℕ} {w r : ℂ} (hw : w ≠ 0) (hν : ν ^ M = 0)
    (hN : (c - algebraMap ℂ A (r * w)) ^ k = 0) (hcν : Commute c ν) (hDν : Commute D ν)
    (hid : D * (algebraMap ℂ A w + ν) = c * (algebraMap ℂ A (w + 1) + ν)) :
    (D - algebraMap ℂ A (r * (w + 1))) ^ (k + M) = 0 := by
  have cA : ∀ (s : ℂ) (T : A), Commute (algebraMap ℂ A s) T := fun s T => Algebra.commutes s T
  obtain ⟨N, hNdef⟩ : ∃ N, N = c - algebraMap ℂ A (r * w) := ⟨_, rfl⟩
  have hc : c = N + algebraMap ℂ A (r * w) := by rw [hNdef]; abel
  rw [← hNdef] at hN
  have hNν : Commute N ν := by rw [hNdef]; exact hcν.sub_left (cA _ _)
  obtain ⟨G, hG⟩ : ∃ G, G = algebraMap ℂ A (w + 1) + ν := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = algebraMap ℂ A w + ν := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = D - algebraMap ℂ A (r * (w + 1)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = algebraMap ℂ A r * ν := ⟨_, rfl⟩
  have hxg : x * g = N * G - H := by
    have e : x * g = D * g - algebraMap ℂ A (r * (w + 1)) * g := by rw [hx, sub_mul]
    rw [e, hg, hid, hc, hG, hH]
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_smul]
    module
  have hNG : Commute N G := by rw [hG]; exact (cA _ _).symm.add_right hNν
  have hνH : Commute ν H := by rw [hH]; exact (cA _ _).symm.mul_right (Commute.refl ν)
  have h1 : (N * G) ^ k = 0 := by rw [hNG.mul_pow, hN, zero_mul]
  have h2 : (-H) ^ M = 0 := by
    have : H ^ M = 0 := by rw [hH, (cA _ _).mul_pow, hν, mul_zero]
    rcases neg_one_pow_eq_or ℤ M with e | e <;> simp [neg_pow H, this]
  have hNH : Commute N H := by rw [hH]; exact (cA _ _).symm.mul_right hNν
  have hGH : Commute G H := by
    rw [hG]
    exact (cA _ _).add_left hνH
  have hcomm : Commute (N * G) (-H) := (hNH.mul_left hGH).neg_right
  have h3 : (x * g) ^ (k + M) = 0 := by
    rw [hxg, sub_eq_add_neg]
    exact hcomm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h1 h2 (by omega)
  have hxc : Commute x g := by
    rw [hx, hg]
    exact ((cA _ _).symm.sub_left (cA _ _)).add_right (hDν.sub_left (cA _ _))
  have hgu : IsUnit g := by
    rw [hg]
    exact IsNilpotent.isUnit_add_left_of_commute ⟨M, hν⟩ ((IsUnit.mk0 w hw).map (algebraMap ℂ A))
      (cA _ _).symm
  have h4 : x ^ (k + M) * g ^ (k + M) = 0 := by rw [← hxc.mul_pow, h3]
  rw [← hx]
  exact (hgu.pow _).mul_left_eq_zero.1 h4

end Poly

section Restrict

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}

def Rs (G : Module.End ℂ S) (F : Module.End ℂ V) : Prop := ∀ x : S, ((G x : S) : V) = F x

/- English proof (translation)
The claim follows from `LinearMap.ext fun x => Subtype.ext ((h x).trans (h' x).symm)`.
-/
theorem Rs.ext {G G' : Module.End ℂ S} {F : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F) : G = G' :=
  LinearMap.ext fun x => Subtype.ext ((h x).trans (h' x).symm)

/- English proof (translation)
Introduce `x` and use `by simp only [Module.End.mul_apply] rw [h, h']`.
-/
theorem Rs.mul {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G * G') (F * F') := fun x => by
  simp only [Module.End.mul_apply]
  rw [h, h']

/- English proof (translation)
Introduce `x` and use `by simp only [LinearMap.add_apply, Submodule.coe_add] rw [h, h']`.
-/
theorem Rs.add {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G + G') (F + F') := fun x => by
  simp only [LinearMap.add_apply, Submodule.coe_add]
  rw [h, h']

/- English proof (translation)
Introduce `x` and use `by simp only [LinearMap.sub_apply, Submodule.coe_sub] rw [h, h']`.
-/
theorem Rs.sub {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F') :
    Rs (G - G') (F - F') := fun x => by
  simp only [LinearMap.sub_apply, Submodule.coe_sub]
  rw [h, h']

/- English proof (translation)
Introduce `x` and use `by simp [Module.algebraMap_end_apply]`.
-/
theorem Rs.alg (c : ℂ) : Rs (algebraMap ℂ (Module.End ℂ S) c) (algebraMap ℂ (Module.End ℂ V) c) :=
  fun x => by simp [Module.algebraMap_end_apply]

/- English proof (translation)
Introduce `x` and use `by simp`.
-/
theorem Rs.zero : Rs (0 : Module.End ℂ S) (0 : Module.End ℂ V) := fun x => by simp

/- English proof (translation)
Introduce `x` and use `by simp`.
-/
theorem Rs.one : Rs (1 : Module.End ℂ S) (1 : Module.End ℂ V) := fun x => by simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using Rs.one`. Consider the case `succ k ih => simpa only [pow_succ] using ih.mul h`.
-/
theorem Rs.pow {G : Module.End ℂ S} {F : Module.End ℂ V} (h : Rs G F) (k : ℕ) : Rs (G ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using Rs.one
  | succ k ih => simpa only [pow_succ] using ih.mul h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Rs.zero`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `(h i).add ih`.
-/
theorem Rs.sum {ι : Type*} (s : Finset ι) {G : ι → Module.End ℂ S} {F : ι → Module.End ℂ V}
    (h : ∀ i, Rs (G i) (F i)) : Rs (∑ i ∈ s, G i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rs.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℂ (Module.End ℂ S)), ← map_intCast (algebraMap ℂ (Module.End ℂ V))]`. Conclude with `Rs.alg _`.
-/
theorem Rs.intCast (z : ℤ) : Rs ((z : Module.End ℂ S)) ((z : Module.End ℂ V)) := by
  rw [← map_intCast (algebraMap ℂ (Module.End ℂ S)), ← map_intCast (algebraMap ℂ (Module.End ℂ V))]
  exact Rs.alg _

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using Rs.one`. Consider the case `succ m ih`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Conclude with `(h 0).mul (ih fun k => h k.succ)`.
-/
theorem Rs.list {m : ℕ} {G : Fin m → Module.End ℂ S} {F : Fin m → Module.End ℂ V}
    (h : ∀ k, Rs (G k) (F k)) : Rs (List.ofFn G).prod (List.ofFn F).prod := by
  induction m with
  | zero => simpa using Rs.one
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih fun k => h k.succ)

/- English proof (translation)
Unfold `Tm`. Use `Rs.add ?_ (h a b)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Rs.alg u`. Conclude with `Rs.zero`.
-/
theorem Rs.tm {n : ℕ} {G : Fin n → Fin n → Module.End ℂ S} {F : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b, Rs (G a b) (F a b)) (u : ℂ) (a b : Fin n) : Rs (Tm G u a b) (Tm F u a b) := by
  unfold Tm
  refine Rs.add ?_ (h a b)
  split_ifs
  · exact Rs.alg u
  · exact Rs.zero

/- English proof (translation)
Unfold `Formalism.REAL.qdet qminor`. Conclude with `Rs.sum _ fun σ => (Rs.intCast _).mul (Rs.list fun k => Rs.tm h _ _ _)`.
-/
theorem Rs.qdet {n : ℕ} {G : Fin n → Fin n → Module.End ℂ S} {F : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b, Rs (G a b) (F a b)) (u : ℂ) : Rs (qdet G u) (qdet F u) := by
  unfold Formalism.REAL.qdet qminor
  exact Rs.sum _ fun σ => (Rs.intCast _).mul (Rs.list fun k => Rs.tm h _ _ _)

/- English proof (translation)
Establish `e` using `h'.mul h`. Rewrite `e` using `[← hc.eq]`. Conclude with `(h.mul h').ext e`.
-/
theorem Rs.commute {G G' : Module.End ℂ S} {F F' : Module.End ℂ V} (h : Rs G F) (h' : Rs G' F')
    (hc : Commute F F') : Commute G G' := by
  have e := h'.mul h
  rw [← hc.eq] at e
  exact (h.mul h').ext e

end Restrict

section Nil

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce `g _ h`. Simplify using `using h`. Consider the case `cons T l ih`.

Introduce `g hg h`. Take `⟨b, rfl⟩` from `hl T (by simp)`. Establish `ih'` using `ih fun T hT => hl T (by simp [hT])`. Establish `hcf : ∀ c : ℂ, Commute f (f - c • (1 : Module.End ℂ V))` using `fun c => (Commute.refl f).sub_right ((Commute.one_right f).smul_right c)`. Establish `hP : Commute f l.prod` using `Commute.list_prod_right _ _ fun T hT => by`.

Take `⟨c, rfl⟩` from `hl T (by simp [hT])`. Conclude with `hcf c`. Establish `hPg : l.prod g ∈ f.maxGenEigenspace a` using `Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg`. Establish `hh : (f - b • (1 : Module.End ℂ V)) (l.prod g) = 0` using `by simpa using h`. Distinguish the cases in `hb : b = a`.

Substitute `hb` using the available equality. Establish `hcomm : Commute l.prod (f - b • (1 : Module.End ℂ V))` using `hP.symm.sub_right ((Commute.one_right _).smul_right b)`. Establish `e : l.prod ((f - b • (1 : Module.End ℂ V)) g) = 0`. Use `congrArg (fun T : Module.End ℂ V => T g) hcomm.eq` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Rewrite using `[this, hh]`. Establish `hg' : (f - b • (1 : Module.End ℂ V)) g ∈ f.maxGenEigenspace b` using `Module.End.mapsTo_maxGenEigenspace_of_comm (hcf b) _ hg`. Use `ih' _ hg' e` as an intermediate fact. Rewrite using `[List.length_cons, pow_succ, Module.End.mul_apply]`. Conclude with `this`.

Establish `h0 : l.prod g = 0`. Establish `hmem : l.prod g ∈ f.maxGenEigenspace b`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Conclude with `⟨1, by simpa using hh⟩`. Conclude with `Submodule.disjoint_def.1 (Module.End.disjoint_genEigenspace f hb ⊤ ⊤) _ hmem hPg`.

Use `ih' g hg h0` as an intermediate fact. Rewrite using `[List.length_cons, pow_succ', Module.End.mul_apply, this, map_zero]`.
-/
theorem nil_list {f : Module.End ℂ V} {a : ℂ} (l : List (Module.End ℂ V))
    (hl : ∀ T ∈ l, ∃ b : ℂ, T = f - b • (1 : Module.End ℂ V)) :
    ∀ g ∈ f.maxGenEigenspace a, l.prod g = 0 → ((f - a • (1 : Module.End ℂ V)) ^ l.length) g = 0 := by
  induction l with
  | nil =>
    intro g _ h
    simpa using h
  | cons T l ih =>
    intro g hg h
    obtain ⟨b, rfl⟩ := hl T (by simp)
    have ih' := ih fun T hT => hl T (by simp [hT])
    have hcf : ∀ c : ℂ, Commute f (f - c • (1 : Module.End ℂ V)) := fun c =>
      (Commute.refl f).sub_right ((Commute.one_right f).smul_right c)
    have hP : Commute f l.prod := Commute.list_prod_right _ _ fun T hT => by
      obtain ⟨c, rfl⟩ := hl T (by simp [hT])
      exact hcf c
    have hPg : l.prod g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg
    have hh : (f - b • (1 : Module.End ℂ V)) (l.prod g) = 0 := by simpa using h
    by_cases hb : b = a
    · subst hb
      have hcomm : Commute l.prod (f - b • (1 : Module.End ℂ V)) :=
        hP.symm.sub_right ((Commute.one_right _).smul_right b)
      have e : l.prod ((f - b • (1 : Module.End ℂ V)) g) = 0 := by
        have := congrArg (fun T : Module.End ℂ V => T g) hcomm.eq
        simp only [Module.End.mul_apply] at this
        rw [this, hh]
      have hg' : (f - b • (1 : Module.End ℂ V)) g ∈ f.maxGenEigenspace b :=
        Module.End.mapsTo_maxGenEigenspace_of_comm (hcf b) _ hg
      have := ih' _ hg' e
      rw [List.length_cons, pow_succ, Module.End.mul_apply]
      exact this
    · have h0 : l.prod g = 0 := by
        have hmem : l.prod g ∈ f.maxGenEigenspace b := by
          rw [Module.End.mem_maxGenEigenspace]
          exact ⟨1, by simpa using hh⟩
        exact Submodule.disjoint_def.1 (Module.End.disjoint_genEigenspace f hb ⊤ ⊤) _ hmem hPg
      have := ih' g hg h0
      rw [List.length_cons, pow_succ', Module.End.mul_apply, this, map_zero]

/- English proof (translation)
Establish `hP : Commute f l.prod` using `Commute.list_prod_right _ _ fun T hT => by`. Take `⟨c, rfl⟩` from `hl T hT`. Conclude with `(Commute.refl f).sub_right ((Commute.one_right f).smul_right c)`. Establish `hcf : Commute f (f - a • (1 : Module.End ℂ V))` using `(Commute.refl f).sub_right ((Commute.one_right f).smul_right a)`. Establish `hPQ : Commute l.prod (f - a • (1 : Module.End ℂ V))` using `hP.symm.sub_right ((Commute.one_right _).smul_right a)`.

Proceed by induction on `K with`. Consider the case `zero`. Introduce `g _ h`. Simplify using `using h`. Consider the case `succ K ih`.

Introduce `g hg h`. Establish `hPg : l.prod g ∈ f.maxGenEigenspace a` using `Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg`. Establish `e1 : (l.prod ^ K) (l.prod g) = 0`. Rewrite `h` using `[pow_succ, Module.End.mul_apply]`. Conclude with `h`.

Establish `e2` using `ih _ hPg e1`. Establish `e3 : l.prod (((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g) = 0`. Use `congrArg (fun T : Module.End ℂ V => T g) (hPQ.pow_right (l.length * K)).eq` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, e2]`.

Establish `hg' : ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g ∈ f.maxGenEigenspace a` using `Module.End.mapsTo_maxGenEigenspace_of_comm (hcf.pow_right _) _ hg`. Establish `e4` using `nil_list l hl _ hg' e3`. Rewrite using `[Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]`. Conclude with `e4`.
-/
theorem nil_pow {f : Module.End ℂ V} {a : ℂ} (l : List (Module.End ℂ V))
    (hl : ∀ T ∈ l, ∃ b : ℂ, T = f - b • (1 : Module.End ℂ V)) (K : ℕ) :
    ∀ g ∈ f.maxGenEigenspace a, (l.prod ^ K) g = 0 →
      ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g = 0 := by
  have hP : Commute f l.prod := Commute.list_prod_right _ _ fun T hT => by
    obtain ⟨c, rfl⟩ := hl T hT
    exact (Commute.refl f).sub_right ((Commute.one_right f).smul_right c)
  have hcf : Commute f (f - a • (1 : Module.End ℂ V)) :=
    (Commute.refl f).sub_right ((Commute.one_right f).smul_right a)
  have hPQ : Commute l.prod (f - a • (1 : Module.End ℂ V)) :=
    hP.symm.sub_right ((Commute.one_right _).smul_right a)
  induction K with
  | zero =>
    intro g _ h
    simpa using h
  | succ K ih =>
    intro g hg h
    have hPg : l.prod g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg
    have e1 : (l.prod ^ K) (l.prod g) = 0 := by
      rw [pow_succ, Module.End.mul_apply] at h
      exact h
    have e2 := ih _ hPg e1
    have e3 : l.prod (((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g) = 0 := by
      have := congrArg (fun T : Module.End ℂ V => T g) (hPQ.pow_right (l.length * K)).eq
      simp only [Module.End.mul_apply] at this
      rw [this, e2]
    have hg' : ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm (hcf.pow_right _) _ hg
    have e4 := nil_list l hl _ hg' e3
    rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
    exact e4

end Nil

section Main

open Formalism.QuantumDeterminants (capP)

variable {n : ℕ}

/- English proof (translation)
Unfold `capP`. Rewrite using `[Finset.prod_erase_mul _ _ (mem_univ s)]`.
-/
theorem capelliPoly_eq_mul_prod_erase (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP χ Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s) := by
  unfold capP
  rw [Finset.prod_erase_mul _ _ (mem_univ s)]

/- English proof (translation)
Rewrite using `[capelliPoly_eq_mul_prod_erase _ s]`. Use `congr 1`. Use `Finset.prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Simplify using `[Pi.single_eq_of_ne (Finset.ne_of_mem_erase ht)]`. Simplify using `[add_assoc]`.
-/
theorem capelliPoly_add_single (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP (χ + Pi.single s 1) Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s + 1) := by
  rw [capelliPoly_eq_mul_prod_erase _ s]
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase ht)]
  · simp [add_assoc]

/- English proof (translation)
Proceed by induction on `k generalizing f with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Simplify using `[Module.algebraMap_end_apply]`.
-/
theorem compLeft_pow_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {I : Type*} (T : Module.End ℂ V)
    (c : ℂ) (k : ℕ) (f : I → V) (i : I) :
    ((T.compLeft I - algebraMap ℂ (Module.End ℂ (I → V)) c) ^ k) f i =
      ((T - algebraMap ℂ (Module.End ℂ V) c) ^ k) (f i) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    simp [Module.algebraMap_end_apply]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun b => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, om_apply, LinearMap.compLeft_apply, Function.comp, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (Formalism.REAL.qDetCentral _ n X.E X.gl u a b) (f a)`.
-/
theorem commute_C_om (X : GMod n) (u : ℂ) : Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  refine LinearMap.ext fun f => funext fun b => ?_
  simp only [Module.End.mul_apply, om_apply, LinearMap.compLeft_apply, Function.comp, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact LinearMap.congr_fun (Formalism.REAL.qDetCentral _ n X.E X.gl u a b) (f a)

/- English proof (translation)
The claim follows from `(commute_qdet (om X) (fun a b => (commute_om X a b).symm) u).symm`.
-/
theorem commute_T_om (X : GMod n) (u : ℂ) : Commute (qdet (tensE X) u) (om X) :=
  (commute_qdet (om X) (fun a b => (commute_om X a b).symm) u).symm

/- English proof (translation)
Introduce `n X χ s hχ`. Take `⟨K0, hK0⟩` from `hC n X χ hχ`. Take `⟨k, hk⟩` from `hχ`. Take `⟨z, hz⟩ : ∃ z, z = χ s` from `⟨_, rfl⟩`. Rewrite using `[← hz]`.

Take `⟨a, ha⟩ : ∃ a, a = z - cn n` from `⟨_, rfl⟩`. Establish `hstab : ∀ O : Module.End ℂ (Fin n → X.V), Commute O (om X) → ∀ x ∈ stepSub X z, O x ∈ stepSub X z` using `fun O h _ hx => Module.End.mapsTo_maxGenEigenspace_of_comm h.symm _ hx`. Establish `hSa : stepSub X z = (om X).maxGenEigenspace a` using `by rw [ha]; rfl`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, ∀ g ∈ stepSub X z, ((om X - a • (1 : Module.End ℂ (Fin n → X.V))) ^ M) g = 0 := by`. Use `⟨_, fun g hg => nil_pow (f := om X) (a := a) (List.ofFn fun t : Fin n => om X - (χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))) (fun T hT' => ?_) K0 g (hSa ▸ hg) ?_⟩` and prove the remaining obligations.

Take `⟨t, rfl⟩` from `(List.mem_ofFn' _ _).1 hT'`. Conclude with `⟨_, rfl⟩`. Rewrite using `[hK0]`. Simplify using the standard rewrite rules. Establish `hcomν : Commute (om X - a • (1 : Module.End ℂ (Fin n → X.V))) (om X)` using `(Commute.refl _).sub_left ((Commute.one_left _).smul_left a)`.

Set `ν : Module.End ℂ (stepSub X z)` to `(om X - a • (1 : Module.End ℂ (Fin n → X.V))).restrict (hstab _ hcomν)`. Set `c : ℂ → Module.End ℂ (stepSub X z)` to `fun u => ((qdet X.E u).compLeft (Fin n)).restrict (hstab _ (commute_C_om X u))`. Set `D : ℂ → Module.End ℂ (stepSub X z)` to `fun u => qdet (step X z).E u`. Establish `hRν : Rs ν (om X - a • (1 : Module.End ℂ (Fin n → X.V)))` using `fun _ => rfl`. Establish `hRc : ∀ u, Rs (c u) ((qdet X.E u).compLeft (Fin n))` using `fun _ _ => rfl`.

Establish `hRD : ∀ u, Rs (D u) (qdet (tensE X) u)` using `fun u => Rs.qdet (fun _ _ _ => rfl) u`. Establish `hν : ν ^ M = 0` using `(hRν.pow M).ext fun x => by`. Simplify using `using (hM x x.2).symm`. Establish `hcν : ∀ u, Commute (c u) ν` using `fun u => (hRc u).commute hRν ((commute_C_om X u).sub_right ((Commute.one_right _).smul_right a))`. Establish `hDν : ∀ u, Commute (D u) ν` using `fun u => (hRD u).commute hRν ((commute_T_om X u).sub_right ((Commute.one_right _).smul_right a))`.

Establish `hadd : ∀ u : ℂ, Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a) + ν) (u • (1 : Module.End ℂ (Fin n → X.V)) + om X)`. Introduce `u`. Establish `h` using `(Rs.alg (S := stepSub X z) (u + a)).add hRν`. Establish `e : algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (u + a) + (om X - a • (1 : Module.End ℂ (Fin n → X.V))) = u • (1 : Module.End ℂ (Fin n → X.V)) + om X`. Rewrite using `[Algebra.algebraMap_eq_smul_one, add_smul]`.

Normalize the expressions using the abelian group laws. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hid : ∀ u, D u * (algebraMap ℂ _ (u + a) + ν) = c u * (algebraMap ℂ _ (u + a + 1) + ν)`. Introduce `u`. Establish `e2 : Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a + 1) + ν) ((u + 1) • (1 : Module.End ℂ (Fin n → X.V)) + om X)`.

Use `hadd (u + 1)` as an intermediate fact. Rewrite `this` using `[show u + 1 + a = u + a + 1 by ring]`. Then use the resulting hypothesis. Use `((hRD u).mul (hadd u)).ext ?_` and prove the remaining obligations. Rewrite using `[hT n X u]`. Conclude with `(hRc u).mul e2`.

Take `⟨R, hRdef⟩ : ∃ R : ℂ → ℂ, R = fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t)` from `⟨_, rfl⟩`. Establish `hN : ∀ u, (c u - algebraMap ℂ _ (R u * (u + a))) ^ k = 0`. Introduce `u`. Establish `hp : capP χ (u - cn n) = R u * (u + a)`. Rewrite using `[capelliPoly_eq_mul_prod_erase _ s, hRdef, ha, hz]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hk (u - cn n)`. Establish `e : u - cn n + ((n : ℂ) - 1) / 2 = u` using `by simp [cn]`. Rewrite `h0` using `[e, hp, ← Algebra.algebraMap_eq_smul_one]`.

Use `(((hRc u).sub (Rs.alg (R u * (u + a)))).pow k).ext fun x => ?_` and prove the remaining obligations. Establish `hz0 : (((qdet X.E u).compLeft (Fin n) - algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (R u * (u + a))) ^ k) (x : Fin n → X.V) = 0`. Use function extensionality and compare the values at `i`. Rewrite using `[compLeft_pow_apply, h0]`. Simplify using the standard rewrite rules.

Rewrite using `[hz0]`. Simplify using the standard rewrite rules. Establish `hcore : ∀ u, u + a ≠ 0 → (D u - algebraMap ℂ _ (R u * (u + a + 1))) ^ (k + M) = 0` using `fun u hu => core hu hν (hN u) (hcν u) (hDν u) (hid u)`. Unfold `HasChar`. Use `⟨k + M, fun Y => ?_⟩` and prove the remaining obligations.

Take `⟨F, hFdef⟩ : ∃ F : ℂ → Module.End ℂ (stepSub X z), F = fun u => (D u - algebraMap ℂ _ (capP (χ + Pi.single s 1) (u - cn n))) ^ (k + M)` from `⟨_, rfl⟩`. Establish `hPF : PolyFn F`. Rewrite using `[hFdef]`. Use `PolyFn.pow (PolyFn.sub (polyFn_qdet _) ?_) _` and prove the remaining obligations. Unfold `capP`.

Use `PolyFn.algProd _ fun t => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_sub]`. Conclude with `(PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)`. Establish `hF : ∀ u, u ≠ -a → F u = 0`. Introduce `u hu`.

Establish `hp : capP (χ + Pi.single s 1) (u - cn n) = R u * (u + a + 1)`. Rewrite using `[capelliPoly_add_single, hRdef, ha, hz]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hFdef]`.

Simplify using `only`. Rewrite using `[hp]`. Conclude with `hcore u fun h => hu (eq_neg_of_add_eq_zero_left h)`. Establish `hF0 : ∀ u, F u = 0` using `fun u => by`. Distinguish the cases in `h : u = -a`.

Rewrite using `[h]`. Conclude with `hPF.vanish _ hF`. Conclude with `hF u h`. Establish `h` using `hF0 (Y + cn n)`. Rewrite `h` using `[hFdef]`.

Simplify using `only [add_sub_cancel_right] at h`. Rewrite `h` using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `h`.
-/
theorem stepChar_of (hT : QdetTens) (hC : CayleyHam) : StepChar := by
  intro n X χ s hχ
  obtain ⟨K0, hK0⟩ := hC n X χ hχ
  obtain ⟨k, hk⟩ := hχ
  obtain ⟨z, hz⟩ : ∃ z, z = χ s := ⟨_, rfl⟩
  rw [← hz]
  obtain ⟨a, ha⟩ : ∃ a, a = z - cn n := ⟨_, rfl⟩
  have hstab : ∀ O : Module.End ℂ (Fin n → X.V), Commute O (om X) →
      ∀ x ∈ stepSub X z, O x ∈ stepSub X z := fun O h _ hx =>
    Module.End.mapsTo_maxGenEigenspace_of_comm h.symm _ hx
  have hSa : stepSub X z = (om X).maxGenEigenspace a := by rw [ha]; rfl

  obtain ⟨M, hM⟩ : ∃ M, ∀ g ∈ stepSub X z, ((om X - a • (1 : Module.End ℂ (Fin n → X.V))) ^ M) g = 0 := by
    refine ⟨_, fun g hg => nil_pow (f := om X) (a := a)
      (List.ofFn fun t : Fin n => om X - (χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V)))
      (fun T hT' => ?_) K0 g (hSa ▸ hg) ?_⟩
    · obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 hT'
      exact ⟨_, rfl⟩
    · rw [hK0]; simp
  have hcomν : Commute (om X - a • (1 : Module.End ℂ (Fin n → X.V))) (om X) :=
    (Commute.refl _).sub_left ((Commute.one_left _).smul_left a)
  let ν : Module.End ℂ (stepSub X z) :=
    (om X - a • (1 : Module.End ℂ (Fin n → X.V))).restrict (hstab _ hcomν)
  let c : ℂ → Module.End ℂ (stepSub X z) := fun u =>
    ((qdet X.E u).compLeft (Fin n)).restrict (hstab _ (commute_C_om X u))
  let D : ℂ → Module.End ℂ (stepSub X z) := fun u => qdet (step X z).E u
  have hRν : Rs ν (om X - a • (1 : Module.End ℂ (Fin n → X.V))) := fun _ => rfl
  have hRc : ∀ u, Rs (c u) ((qdet X.E u).compLeft (Fin n)) := fun _ _ => rfl
  have hRD : ∀ u, Rs (D u) (qdet (tensE X) u) := fun u => Rs.qdet (fun _ _ _ => rfl) u
  have hν : ν ^ M = 0 := (hRν.pow M).ext fun x => by
    simpa using (hM x x.2).symm
  have hcν : ∀ u, Commute (c u) ν := fun u =>
    (hRc u).commute hRν ((commute_C_om X u).sub_right ((Commute.one_right _).smul_right a))
  have hDν : ∀ u, Commute (D u) ν := fun u =>
    (hRD u).commute hRν ((commute_T_om X u).sub_right ((Commute.one_right _).smul_right a))
  have hadd : ∀ u : ℂ, Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a) + ν)
      (u • (1 : Module.End ℂ (Fin n → X.V)) + om X) := by
    intro u
    have h := (Rs.alg (S := stepSub X z) (u + a)).add hRν
    have e : algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (u + a) +
        (om X - a • (1 : Module.End ℂ (Fin n → X.V))) =
        u • (1 : Module.End ℂ (Fin n → X.V)) + om X := by
      rw [Algebra.algebraMap_eq_smul_one, add_smul]
      abel
    rwa [e] at h
  have hid : ∀ u, D u * (algebraMap ℂ _ (u + a) + ν) = c u * (algebraMap ℂ _ (u + a + 1) + ν) := by
    intro u
    have e2 : Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a + 1) + ν)
        ((u + 1) • (1 : Module.End ℂ (Fin n → X.V)) + om X) := by
      have := hadd (u + 1)
      rwa [show u + 1 + a = u + a + 1 by ring] at this
    refine ((hRD u).mul (hadd u)).ext ?_
    rw [hT n X u]
    exact (hRc u).mul e2
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ → ℂ, R = fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) := ⟨_, rfl⟩
  have hN : ∀ u, (c u - algebraMap ℂ _ (R u * (u + a))) ^ k = 0 := by
    intro u
    have hp : capP χ (u - cn n) = R u * (u + a) := by
      rw [capelliPoly_eq_mul_prod_erase _ s, hRdef, ha, hz]
      congr 1
      ring
    have h0 := hk (u - cn n)
    have e : u - cn n + ((n : ℂ) - 1) / 2 = u := by simp [cn]
    rw [e, hp, ← Algebra.algebraMap_eq_smul_one] at h0
    refine (((hRc u).sub (Rs.alg (R u * (u + a)))).pow k).ext fun x => ?_
    have hz0 : (((qdet X.E u).compLeft (Fin n) -
        algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (R u * (u + a))) ^ k) (x : Fin n → X.V) = 0 := by
      funext i
      rw [compLeft_pow_apply, h0]
      simp
    rw [hz0]
    simp
  have hcore : ∀ u, u + a ≠ 0 → (D u - algebraMap ℂ _ (R u * (u + a + 1))) ^ (k + M) = 0 :=
    fun u hu => core hu hν (hN u) (hcν u) (hDν u) (hid u)
  unfold HasChar
  refine ⟨k + M, fun Y => ?_⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → Module.End ℂ (stepSub X z), F = fun u =>
      (D u - algebraMap ℂ _ (capP (χ + Pi.single s 1) (u - cn n))) ^ (k + M) := ⟨_, rfl⟩
  have hPF : PolyFn F := by
    rw [hFdef]
    refine PolyFn.pow (PolyFn.sub (polyFn_qdet _) ?_) _
    unfold capP
    refine PolyFn.algProd _ fun t => ?_
    simp only [map_add, map_sub]
    exact (PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)
  have hF : ∀ u, u ≠ -a → F u = 0 := by
    intro u hu
    have hp : capP (χ + Pi.single s 1) (u - cn n) = R u * (u + a + 1) := by
      rw [capelliPoly_add_single, hRdef, ha, hz]
      congr 1
      ring
    rw [hFdef]
    simp only
    rw [hp]
    exact hcore u fun h => hu (eq_neg_of_add_eq_zero_left h)
  have hF0 : ∀ u, F u = 0 := fun u => by
    by_cases h : u = -a
    · rw [h]
      exact hPF.vanish _ hF
    · exact hF u h
  have h := hF0 (Y + cn n)
  rw [hFdef] at h
  simp only [add_sub_cancel_right] at h
  rw [Algebra.algebraMap_eq_smul_one] at h
  exact h

end Main

/- English proof (translation)
The claim follows from `stepChar_of GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.CayleyHamiltonHk`.
-/
theorem stepChar : CompanionTheory.RgExh.StepChar := stepChar_of GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.CayleyHamiltonHk

end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
