import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermFiniteProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermCentredIntegralEquation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PrimitiveLinearForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace PrimeGermPrimitivePresentation

variable {σ : Type} [Fintype σ]

def anFun (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg

def toGerm (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩

/- English proof (translation)
Introduce and unpack `⟨φ, f, hf, rfl⟩`. Conclude with `⟨⟨f, hf⟩, rfl⟩`.
-/
theorem toGerm_surjective (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

def rep {w : σ → ℂ} (φ : holGerms w) : anFun w := Classical.choose (toGerm_surjective w φ)

/- English proof (translation)
The claim follows from `Classical.choose_spec (toGerm_surjective w φ)`.
-/
theorem toGerm_rep {w : σ → ℂ} (φ : holGerms w) : toGerm w (rep φ) = φ :=
  Classical.choose_spec (toGerm_surjective w φ)

def compA {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) : anFun (A w) →+* anFun w where
  toFun u := ⟨fun z => u.1 (A z), (show AnalyticAt ℂ u.1 (A w) from u.2).comp (A.analyticAt w)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h' : ((u.1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = (v.1 : Germ (𝓝 (A w)) ℂ)` using `congrArg Subtype.val h`. Conclude with `Germ.coe_eq.2 ((A.continuous.tendsto w).eventually (Germ.coe_eq.1 h'))`.
-/
theorem toGerm_compA_congr {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u v : anFun (A w))
    (h : toGerm (A w) u = toGerm (A w) v) : toGerm w (compA A w u) = toGerm w (compA A w v) := by
  apply Subtype.ext
  have h' : ((u.1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = (v.1 : Germ (𝓝 (A w)) ℂ) := congrArg Subtype.val h
  exact Germ.coe_eq.2 ((A.continuous.tendsto w).eventually (Germ.coe_eq.1 h'))

def pull {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) : holGerms (A w) →+* holGerms w where
  toFun φ := toGerm w (compA A w (rep φ))
  map_one' := by
    show toGerm w (compA A w (rep 1)) = 1
    rw [toGerm_compA_congr A w (rep 1) 1 (by rw [toGerm_rep, map_one]), map_one, map_one]
  map_mul' φ ψ := by
    show toGerm w (compA A w (rep (φ * ψ))) = toGerm w (compA A w (rep φ)) * toGerm w (compA A w (rep ψ))
    rw [← map_mul, ← map_mul]
    exact toGerm_compA_congr A w _ _ (by rw [map_mul, toGerm_rep, toGerm_rep, toGerm_rep])
  map_zero' := by
    show toGerm w (compA A w (rep 0)) = 0
    rw [toGerm_compA_congr A w (rep 0) 0 (by rw [toGerm_rep, map_zero]), map_zero, map_zero]
  map_add' φ ψ := by
    show toGerm w (compA A w (rep (φ + ψ))) = toGerm w (compA A w (rep φ)) + toGerm w (compA A w (rep ψ))
    rw [← map_add, ← map_add]
    exact toGerm_compA_congr A w _ _ (by rw [map_add, toGerm_rep, toGerm_rep, toGerm_rep])

/- English proof (translation)
The claim follows from `toGerm_compA_congr A w _ _ (toGerm_rep _)`.
-/
theorem pull_toGerm {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    pull A w (toGerm (A w) u) = toGerm w (compA A w u) :=
  toGerm_compA_congr A w _ _ (toGerm_rep _)

def mkA {w : σ → ℂ} (f : (σ → ℂ) → ℂ) (hf : AnalyticAt ℂ f w) : anFun w := ⟨f, hf⟩

/- English proof (translation)
Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ hφ`. Take `⟨i, hi⟩` from `hφ`. Use `⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩` and prove the remaining obligations. Rewrite using `[hi]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Consider the case `zero`. Use `⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩` and prove the remaining obligations.

Rewrite using `[show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by`. Use function extensionality and compare the values at `z`. Use the proof step `simp]`. Both sides reduce to the same expression. Consider the case `add x y _ _ hx hy`.

Take `⟨h₁, hh₁, e₁⟩` from `hx`. Take `⟨h₂, hh₂, e₂⟩` from `hy`. Use `⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩` and prove the remaining obligations. Use `show (x : Germ (𝓝 w) ℂ) + y = _`. Rewrite using `[e₁, e₂, ← Germ.coe_add]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `[add_mul, Finset.sum_add_distrib]`. Consider the case `smul a x _ hx`. Take `⟨h, hh, e⟩` from `hx`.

Take `⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a` from `a.2`. Use `⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩` and prove the remaining obligations. Use `show (a : Germ (𝓝 w) ℂ) * x = _`. Rewrite using `[e, ← efa, ← Germ.coe_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Simplify using `[Finset.mul_sum, mul_assoc]`.
-/
theorem exists_of_mem_holGermIdeal {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu`. Take `⟨h, hh, e⟩` from `exists_of_mem_holGermIdeal p hu`. Conclude with `⟨h, hh, Germ.coe_eq.1 e⟩`. Introduce and unpack `⟨h, hh, hev⟩`.

Establish `hsum : toGerm w u = ∑ i, toGerm w (mkA (h i) (hh i)) * toGerm w (mkA (p i) (hp i))`. Simplify using `only [← map_mul, ← map_sum]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((u.1 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (((∑ i, mkA (h i) (hh i) * mkA (p i) (hp i) : anFun w) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)`. Use `Germ.coe_eq.2 (hev.mono fun z hz => ?_)` and prove the remaining obligations.

Simplify using `[hz, Finset.sum_apply, mkA]`. Rewrite using `[hsum]`. Use `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)` and prove the remaining obligations.
-/
theorem toGerm_mem_iff {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    (u : anFun w) : toGerm w u ∈ holGermIdeal w p ↔ IsGermCombination w p u.1 := by
  constructor
  · intro hu
    obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
    exact ⟨h, hh, Germ.coe_eq.1 e⟩
  · rintro ⟨h, hh, hev⟩
    have hsum : toGerm w u = ∑ i, toGerm w (mkA (h i) (hh i)) * toGerm w (mkA (p i) (hp i)) := by
      simp only [← map_mul, ← map_sum]
      apply Subtype.ext
      change ((u.1 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
        (((∑ i, mkA (h i) (hh i) * mkA (p i) (hp i) : anFun w) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      refine Germ.coe_eq.2 (hev.mono fun z hz => ?_)
      simp [hz, Finset.sum_apply, mkA]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `σ _ w k p hp hPr`. Take `⟨d, A, hinj, hint, hgen⟩` from `hFP σ w k p hp hPr`. Take `⟨hdom, hic⟩` from `hIC d (A w)`. Use `set P := holGermIdeal w p with hPdef`. Establish `: P.IsPrime` using `hPr`.

Set `R` to `↥(holGerms (A w))`. Set `B` to `↥(holGerms w) ⧸ P`. Establish `: IsDomain R` using `hdom`. Establish `: IsIntegrallyClosed R` using `hic`. Set `_ : Algebra R B` to `((Ideal.Quotient.mk P).comp (pull A w)).toAlgebra`.

Set `cl : anFun w →+* B` to `(Ideal.Quotient.mk P).comp (toGerm w)`. Establish `hcl0 : ∀ u : anFun w, cl u = 0 ↔ IsGermCombination w p u.1` using `fun u => by show Ideal.Quotient.mk P (toGerm w u) = 0 ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `toGerm_mem_iff hp u`. Establish `hcompA : ∀ v : anFun (A w), cl (compA A w v) = algebraMap R B (toGerm (A w) v)` using `fun v => by show Ideal.Quotient.mk P (toGerm w (compA A w v)) = Ideal.Quotient.mk P (pull A w (toGerm (A w) v))`.

Rewrite using `[pull_toGerm]`. Establish `hcomp : ∀ r : R, cl (compA A w (rep r)) = algebraMap R B r` using `fun r => by`. Rewrite using `[hcompA, toGerm_rep]`. Establish `hRB : Function.Injective (algebraMap R B)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `r hr`. Rewrite `hr` using `[← hcomp, hcl0]`. Establish `hev` using `hinj (rep r).1 (rep r).2 hr`. Rewrite using `[← toGerm_rep r]`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(((rep r).1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ)`. Conclude with `Germ.coe_eq.2 hev`. Set `cst : ℂ →+* anFun (A w)` to `{ toFun := fun c => mkA (fun _ => c) analyticAt_const map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Set `ι : ℂ →+* R` to `(toGerm (A w)).comp cst`. Set `e` to `Fintype.equivFin σ`.

Set `crd : σ → anFun w` to `fun i => mkA (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)`. Set `x : Fin (Fintype.card σ) → B` to `fun j => cl (crd (e.symm j))`. Establish `hx : Algebra.adjoin R (Set.range x) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `b -`.

Take `⟨ψ, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨u, rfl⟩` from `toGerm_surjective w ψ`. Take `⟨s, a, ha, hc⟩` from `hgen u.1 u.2`. Set `a' : (σ → ℕ) → anFun (A w)` to `fun m => if hm : m ∈ s then mkA (a m) (ha m hm) else 0`. Establish `hU : ((u - ∑ m ∈ s, compA A w (a' m) * ∏ i, crd i ^ m i : anFun w) : (σ → ℂ) → ℂ) = fun z => u.1 z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i`.

Use function extensionality and compare the values at `z`. Simplify using `only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Simplify using `[a', hm, compA, mkA, crd]`.

Establish `h0` using `(hcl0 _).2 (by rw [hU]; exact hc)`. Rewrite `h0` using `[map_sub, sub_eq_zero, map_sum]`. Use `show cl u ∈ _`. Rewrite using `[h0]`. Use `Subalgebra.sum_mem _ fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hcompA, map_prod]`. Use `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_pow]`. Establish `hmem : cl (crd i) ∈ Set.range x` using `⟨e i, by simp [x]⟩`. Conclude with `Subalgebra.pow_mem _ (Algebra.subset_adjoin hmem) _`.

Establish `hxint : ∀ i : σ, IsIntegral R (cl (crd i))`. Introduce `i`. Take `⟨n', b, hb, hc⟩` from `hint i`. Use `⟨X ^ n' + ∑ j : Fin n', C (toGerm (A w) (mkA (b j) (hb j))) * X ^ (j : ℕ), monic_X_pow_add (degree_sum_fin_lt _), ?_⟩` and prove the remaining obligations. Establish `hV : ((crd i ^ n' + ∑ j : Fin n', compA A w (mkA (b j) (hb j)) * crd i ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) = fun z => z i ^ n' + ∑ j, b j (A z) * z i ^ (j : ℕ)`.

Use function extensionality and compare the values at `z`. Simplify using `[compA, mkA, crd, Finset.sum_apply]`. Establish `h0` using `(hcl0 _).2 (by rw [hV]; exact hc)`. Rewrite `h0` using `[map_add, map_pow, map_sum]`. Simplify using `only [map_mul, map_pow, hcompA] at h0`.

Rewrite using `[eval₂_add, eval₂_X_pow, eval₂_finsetSum]`. Simplify `h0` using `[eval₂_mul, eval₂_C, eval₂_X_pow]`. Establish `: Module.Finite R B`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.top_toSubmodule, ← hx]`.

Conclude with `fg_adjoin_of_finite (Set.finite_range x) (by rintro _ ⟨j, rfl⟩; exact hxint _)`. Take `⟨c, m, D, Q, hmon, -, hdiv, hD0, ⟨a, b, hab⟩, hQ⟩` from `GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm.exists_primitive_data hRB ι x hx`. Set `ℓ : (σ → ℂ) →L[ℂ] ℂ` to `∑ j : Fin (Fintype.card σ), c j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)`. Set `lA : anFun w` to `mkA ℓ (ℓ.analyticAt w)`. Use `set ℓB : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓB`.

Establish `hlA : cl lA = ℓB`. Establish `: lA = ∑ j : Fin (Fintype.card σ), compA A w (cst (c j)) * crd (e.symm j)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Simplify using `[lA, mkA, ℓ, compA, cst, crd, Finset.sum_apply]`.

Rewrite using `[this, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hcompA]`. Both sides reduce to the same expression. Establish `haev : ∀ (q : R[X]) (K : ℕ), q.natDegree < K → aeval ℓB q = cl (∑ j : Fin K, compA A w (rep (q.coeff j)) * lA ^ (j : ℕ))`.

Introduce `q K hq`. Rewrite using `[aeval_eq_sum_range' hq, ← Fin.sum_univ_eq_sum_range (fun i => q.coeff i • ℓB ^ i) K, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hlA, hcomp, Algebra.smul_def]`. Use `set N := m.natDegree with hN`.

Establish `hm0 : aeval ℓB m = 0` using `(hdiv m).2 dvd_rfl`. Establish `hm1 : m ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hm0`. Set `cf : Fin N → (Fin d → ℂ) → ℂ` to `fun j => (rep (m.coeff j)).1`.

Set `δ : (Fin d → ℂ) → ℂ` to `(rep D).1`. Use `⟨d, A, ℓ, N, cf, δ, ⟨fun j => (rep (m.coeff j)).2, (rep D).2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hU : ((lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) = fun z => ℓ z ^ N + ∑ j, cf j (A z) * ℓ z ^ (j : ℕ)`. Use function extensionality and compare the values at `z`. Simplify using `[lA, mkA, compA, cf, Finset.sum_apply]`.

Establish `hcm : cl (lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ)) = aeval ℓB m` using `by conv_rhs => rw [hmon.as_sum]`. Rewrite using `[map_add, map_pow, hlA, map_sum, map_add, map_pow, aeval_X, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => aeval ℓB (C (m.coeff i) * X ^ i)) N]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hlA, hcomp, map_mul, aeval_C, map_pow, aeval_X]`.

Establish `h` using `(hcl0 _).1 (hcm.trans hm0)`. Rewrite `h` using `[hU]`. Conclude with `h`. Introduce `a' ha' hc' j`. Set `q : R[X]` to `∑ i : Fin N, C (toGerm (A w) (mkA (a' i) (ha' i))) * X ^ (i : ℕ)`.

Establish `hq : aeval ℓB q = 0`. Establish `hU : ((∑ i : Fin N, compA A w (mkA (a' i) (ha' i)) * lA ^ (i : ℕ) : anFun w) : (σ → ℂ) → ℂ) = fun z => ∑ i, a' i (A z) * ℓ z ^ (i : ℕ)`. Use function extensionality and compare the values at `z`. Simplify using `[lA, mkA, compA, Finset.sum_apply]`. Establish `h` using `(hcl0 _).2 (by rw [hU]; exact hc')`.

Rewrite using `[← h, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, hlA, hcompA]`. Establish `hq0 : q = 0`. Use `eq_zero_of_dvd_of_degree_lt ((hdiv q).1 hq) ?_` and prove the remaining obligations.

Rewrite using `[degree_eq_natDegree hmon.ne_zero]`. Conclude with `degree_sum_fin_lt _`. Establish `hcoef : q.coeff j = toGerm (A w) (mkA (a' j) (ha' j))`. Simplify using `only [q, finsetSum_coeff, coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (Fin.ext h.symm))) (by simp)]`.

Simplify using the standard rewrite rules. Rewrite `hcoef` using `[hq0, coeff_zero]`. Establish `h'` using `congrArg Subtype.val hcoef.symm`. Express the relevant statement in the definitionally equal form `((a' j : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ) at h'`. Conclude with `Germ.coe_eq.1 h'`.

Set `G : ((Fin d → ℂ) → ℂ) →+* Germ (𝓝 (A w)) ℂ` to `Germ.coeRingHom _`. Set `ιR : R →+* Germ (𝓝 (A w)) ℂ` to `(holGerms (A w)).subtype`. Set `lift : R[X] → ((Fin d → ℂ) → ℂ)[X]` to `fun q => ∑ i ∈ Finset.range (q.natDegree + 1), C (rep (q.coeff i)).1 * X ^ i`. Establish `hGrep : ∀ r : R, G (rep r).1 = ιR r` using `fun r => congrArg Subtype.val (toGerm_rep r)`. Establish `hlc : ∀ (q : R[X]) (i : ℕ), G ((lift q).coeff i) = ιR (q.coeff i)`.

Introduce `q i`. Simplify using `only [lift, finsetSum_coeff, coeff_C_mul_X_pow]`. Distinguish the cases in `hi : i < q.natDegree + 1`. Rewrite using `[Finset.sum_eq_single i (fun j _ hji => if_neg (Ne.symm hji)) (fun h => absurd (Finset.mem_range.2 hi) h), if_pos rfl, hGrep]`. Rewrite using `[Finset.sum_eq_zero (fun j hj => if_neg (fun h => by subst h; exact hi (Finset.mem_range.1 hj))), map_zero, coeff_eq_zero_of_natDegree_lt (by omega), map_zero]`.

Establish `hlift : ∀ q : R[X], (lift q).map G = q.map ιR` using `fun q => by`. Use extensionality with `i`. Rewrite using `[coeff_map, coeff_map, hlc]`. Set `Fm : ((Fin d → ℂ) → ℂ)[X]` to `X ^ N + ∑ j : Fin N, C (cf j) * X ^ (j : ℕ)`. Establish `hFm : Fm.map G = m.map ιR` using `by conv_rhs => rw [hmon.as_sum]`.

Simplify using `only [Fm, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum, Polynomial.map_mul, map_C, cf, hGrep]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => C (ιR (m.coeff i)) * X ^ i) N]`. Set `E : ((Fin d → ℂ) → ℂ)[X]` to `lift a * Fm + lift b * derivative Fm - C δ`. Establish `hE : E.map G = 0`. Establish `h1 : E.map G = (a * m + b * derivative m - C D).map ιR`.

Simplify using `only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, ← derivative_map, hlift, hFm, map_C, δ, hGrep]`. Rewrite using `[h1, hab, sub_self, Polynomial.map_zero]`. Establish `hev : ∀ᶠ y in 𝓝 (A w), ∀ i ∈ E.support, E.coeff i y = 0`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `i _`.

Establish `h` using `congrArg (fun q => q.coeff i) hE`. Simplify using `only [coeff_map, coeff_zero] at h`. Conclude with `Germ.coe_eq.1 h`. Use `filter_upwards [hev] with y hy hδy`. Set `ev : ((Fin d → ℂ) → ℂ) →+* ℂ` to `Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y`.

Establish `hE0 : E.map ev = 0`. Use extensionality with `i`. Rewrite using `[coeff_map, coeff_zero]`. Distinguish the cases in `hi : E.coeff i = 0`. Rewrite using `[hi, map_zero]`.

Conclude with `hy i (mem_support_iff.2 hi)`. Establish `hFy : Fm.map ev = monicOfCoeffs fun j => cf j y`. Simplify using `[Fm, monicOfCoeffs, Polynomial.map_sum, ev]`. Rewrite using `[separable_def, ← hFy]`. Simplify using `only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map, sub_eq_zero] at hE0`.

Use `⟨C (δ y)⁻¹ * (lift a).map ev, C (δ y)⁻¹ * (lift b).map ev, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_assoc, ← mul_add, hE0, ← C_mul, show ev δ = δ y from rfl, inv_mul_cancel₀ hδy, C_1]`. Introduce `g hg`. Establish `hall : ∀ z ∈ Algebra.adjoin R (Set.range x), ∃ M : ℕ, algebraMap R B D ^ M * z ∈ Algebra.adjoin R {ℓB}`. Introduce `z hz`.

Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Take `⟨j, rfl⟩` from `hz`. Conclude with `⟨1, by rw [pow_one, hQ j]; exact aeval_mem_adjoin_singleton R ℓB⟩`. Consider the case `algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩`.

Consider the case `add u v _ _ hu hv`. Take `⟨M₁, h₁⟩` from `hu`. Take `⟨M₂, h₂⟩` from `hv`. Use `⟨M₁ + M₂, ?_⟩` and prove the remaining obligations. Establish `: algebraMap R B D ^ (M₁ + M₂) * (u + v) = algebraMap R B D ^ M₂ * (algebraMap R B D ^ M₁ * u) + algebraMap R B D ^ M₁ * (algebraMap R B D ^ M₂ * v)` using `by ring`.

Rewrite using `[this]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₁) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₂)`. Consider the case `mul u v _ _ hu hv`. Take `⟨M₁, h₁⟩` from `hu`. Take `⟨M₂, h₂⟩` from `hv`.

Use `⟨M₁ + M₂, ?_⟩` and prove the remaining obligations. Rewrite using `[show algebraMap R B D ^ (M₁ + M₂) * (u * v) = (algebraMap R B D ^ M₁ * u) * (algebraMap R B D ^ M₂ * v) by ring]`. Conclude with `Subalgebra.mul_mem _ h₁ h₂`. Take `⟨M, hM⟩` from `hall (cl (mkA g hg)) (by rw [hx]; exact Algebra.mem_top)`. Rewrite `hM` using `[Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨Q', hQ'⟩` from `hM`. Establish `hr : aeval ℓB (Q' %ₘ m) = algebraMap R B D ^ M * cl (mkA g hg)`. Rewrite using `[aeval_modByMonic_eq_self_of_root hm0]`. Conclude with `hQ'`. Establish `hrdeg : (Q' %ₘ m).natDegree < N` using `natDegree_modByMonic_lt Q' hmon hm1`.

Use `⟨M, fun j => (rep ((Q' %ₘ m).coeff j)).1, fun j => (rep ((Q' %ₘ m).coeff j)).2, ?_⟩` and prove the remaining obligations. Establish `hU : ((compA A w (rep D) ^ M * mkA g hg - ∑ j : Fin N, compA A w (rep ((Q' %ₘ m).coeff j)) * lA ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) = fun z => δ (A z) ^ M * g z - ∑ j : Fin N, (rep ((Q' %ₘ m).coeff j)).1 (A z) * ℓ z ^ (j : ℕ)`. Use function extensionality and compare the values at `z`. Simplify using `[lA, mkA, compA, δ, Finset.sum_apply]`. Rewrite using `[← hU, ← hcl0, map_sub, ← haev _ N hrdeg, hr, map_mul, map_pow, hcomp, sub_self]`.

Introduce `g hg`. Conclude with `hCE σ w k p d A hp hint hgen g hg`. Introduce `hδ`. Establish `h0 : cl (compA A w (rep D)) = 0` using `(hcl0 _).2 hδ`. Rewrite `h0` using `[hcomp]`.

Conclude with `hD0 (hRB (h0.trans (map_zero _).symm))`.
-/
theorem proof (hFP : PrimeGermFiniteProjection.Statement) (hIC : HolGermsIntegrallyClosed.Statement)
    (hCE : CentredIntegralEquation.Statement) : PrimeGermPrimitivePresentation.Statement := by
  classical
  intro σ _ w k p hp hPr
  obtain ⟨d, A, hinj, hint, hgen⟩ := hFP σ w k p hp hPr
  obtain ⟨hdom, hic⟩ := hIC d (A w)
  set P := holGermIdeal w p with hPdef
  have : P.IsPrime := hPr
  let R := ↥(holGerms (A w))
  let B := ↥(holGerms w) ⧸ P
  have : IsDomain R := hdom
  have : IsIntegrallyClosed R := hic
  let _ : Algebra R B := ((Ideal.Quotient.mk P).comp (pull A w)).toAlgebra

  let cl : anFun w →+* B := (Ideal.Quotient.mk P).comp (toGerm w)
  have hcl0 : ∀ u : anFun w, cl u = 0 ↔ IsGermCombination w p u.1 := fun u => by
    show Ideal.Quotient.mk P (toGerm w u) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact toGerm_mem_iff hp u
  have hcompA : ∀ v : anFun (A w), cl (compA A w v) = algebraMap R B (toGerm (A w) v) := fun v => by
    show Ideal.Quotient.mk P (toGerm w (compA A w v)) = Ideal.Quotient.mk P (pull A w (toGerm (A w) v))
    rw [pull_toGerm]
  have hcomp : ∀ r : R, cl (compA A w (rep r)) = algebraMap R B r := fun r => by
    rw [hcompA, toGerm_rep]

  have hRB : Function.Injective (algebraMap R B) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    rw [← hcomp, hcl0] at hr
    have hev := hinj (rep r).1 (rep r).2 hr
    rw [← toGerm_rep r]
    apply Subtype.ext
    change (((rep r).1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ)
    exact Germ.coe_eq.2 hev

  let cst : ℂ →+* anFun (A w) :=
    { toFun := fun c => mkA (fun _ => c) analyticAt_const
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ι : ℂ →+* R := (toGerm (A w)).comp cst
  let e := Fintype.equivFin σ
  let crd : σ → anFun w := fun i =>
    mkA (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  let x : Fin (Fintype.card σ) → B := fun j => cl (crd (e.symm j))

  have hx : Algebra.adjoin R (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    rintro b -
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨u, rfl⟩ := toGerm_surjective w ψ
    obtain ⟨s, a, ha, hc⟩ := hgen u.1 u.2
    let a' : (σ → ℕ) → anFun (A w) := fun m => if hm : m ∈ s then mkA (a m) (ha m hm) else 0
    have hU : ((u - ∑ m ∈ s, compA A w (a' m) * ∏ i, crd i ^ m i : anFun w) : (σ → ℂ) → ℂ) =
        fun z => u.1 z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i := by
      funext z
      simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply,
        Finset.prod_apply, Pi.pow_apply]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      simp [a', hm, compA, mkA, crd]
    have h0 := (hcl0 _).2 (by rw [hU]; exact hc)
    rw [map_sub, sub_eq_zero, map_sum] at h0
    show cl u ∈ _
    rw [h0]
    refine Subalgebra.sum_mem _ fun m _ => ?_
    rw [map_mul, hcompA, map_prod]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)
    rw [map_pow]
    have hmem : cl (crd i) ∈ Set.range x := ⟨e i, by simp [x]⟩
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin hmem) _

  have hxint : ∀ i : σ, IsIntegral R (cl (crd i)) := by
    intro i
    obtain ⟨n', b, hb, hc⟩ := hint i
    refine ⟨X ^ n' + ∑ j : Fin n', C (toGerm (A w) (mkA (b j) (hb j))) * X ^ (j : ℕ),
      monic_X_pow_add (degree_sum_fin_lt _), ?_⟩
    have hV : ((crd i ^ n' + ∑ j : Fin n', compA A w (mkA (b j) (hb j)) * crd i ^ (j : ℕ) : anFun w) :
        (σ → ℂ) → ℂ) = fun z => z i ^ n' + ∑ j, b j (A z) * z i ^ (j : ℕ) := by
      funext z
      simp [compA, mkA, crd, Finset.sum_apply]
    have h0 := (hcl0 _).2 (by rw [hV]; exact hc)
    rw [map_add, map_pow, map_sum] at h0
    simp only [map_mul, map_pow, hcompA] at h0
    rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
    simpa [eval₂_mul, eval₂_C, eval₂_X_pow] using h0
  have : Module.Finite R B := by
    refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, ← hx]
    exact fg_adjoin_of_finite (Set.finite_range x) (by rintro _ ⟨j, rfl⟩; exact hxint _)

  obtain ⟨c, m, D, Q, hmon, -, hdiv, hD0, ⟨a, b, hab⟩, hQ⟩ :=
    GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm.exists_primitive_data hRB ι x hx
  let ℓ : (σ → ℂ) →L[ℂ] ℂ :=
    ∑ j : Fin (Fintype.card σ), c j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)
  let lA : anFun w := mkA ℓ (ℓ.analyticAt w)
  set ℓB : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓB
  have hlA : cl lA = ℓB := by
    have : lA = ∑ j : Fin (Fintype.card σ), compA A w (cst (c j)) * crd (e.symm j) := by
      apply Subtype.ext
      funext z
      simp [lA, mkA, ℓ, compA, cst, crd, Finset.sum_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcompA]
    rfl
  have haev : ∀ (q : R[X]) (K : ℕ), q.natDegree < K →
      aeval ℓB q = cl (∑ j : Fin K, compA A w (rep (q.coeff j)) * lA ^ (j : ℕ)) := by
    intro q K hq
    rw [aeval_eq_sum_range' hq, ← Fin.sum_univ_eq_sum_range (fun i => q.coeff i • ℓB ^ i) K, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hlA, hcomp, Algebra.smul_def]
  set N := m.natDegree with hN
  have hm0 : aeval ℓB m = 0 := (hdiv m).2 dvd_rfl
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hm0
  let cf : Fin N → (Fin d → ℂ) → ℂ := fun j => (rep (m.coeff j)).1
  let δ : (Fin d → ℂ) → ℂ := (rep D).1
  refine ⟨d, A, ℓ, N, cf, δ, ⟨fun j => (rep (m.coeff j)).2, (rep D).2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    have hU : ((lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ) : anFun w) :
        (σ → ℂ) → ℂ) = fun z => ℓ z ^ N + ∑ j, cf j (A z) * ℓ z ^ (j : ℕ) := by
      funext z
      simp [lA, mkA, compA, cf, Finset.sum_apply]
    have hcm : cl (lA ^ N + ∑ j : Fin N, compA A w (rep (m.coeff j)) * lA ^ (j : ℕ)) = aeval ℓB m := by
      conv_rhs => rw [hmon.as_sum]
      rw [map_add, map_pow, hlA, map_sum, map_add, map_pow, aeval_X, map_sum,
        ← Fin.sum_univ_eq_sum_range (fun i => aeval ℓB (C (m.coeff i) * X ^ i)) N]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, hlA, hcomp, map_mul, aeval_C, map_pow, aeval_X]
    have h := (hcl0 _).1 (hcm.trans hm0)
    rw [hU] at h
    exact h
  ·
    intro a' ha' hc' j
    let q : R[X] := ∑ i : Fin N, C (toGerm (A w) (mkA (a' i) (ha' i))) * X ^ (i : ℕ)
    have hq : aeval ℓB q = 0 := by
      have hU : ((∑ i : Fin N, compA A w (mkA (a' i) (ha' i)) * lA ^ (i : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
          fun z => ∑ i, a' i (A z) * ℓ z ^ (i : ℕ) := by
        funext z
        simp [lA, mkA, compA, Finset.sum_apply]
      have h := (hcl0 _).2 (by rw [hU]; exact hc')
      rw [← h, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, hlA, hcompA]
    have hq0 : q = 0 := by
      refine eq_zero_of_dvd_of_degree_lt ((hdiv q).1 hq) ?_
      rw [degree_eq_natDegree hmon.ne_zero]
      exact degree_sum_fin_lt _
    have hcoef : q.coeff j = toGerm (A w) (mkA (a' j) (ha' j)) := by
      simp only [q, finsetSum_coeff, coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (Fin.ext h.symm))) (by simp)]
      simp
    rw [hq0, coeff_zero] at hcoef
    have h' := congrArg Subtype.val hcoef.symm
    change ((a' j : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = ((0 : (Fin d → ℂ) → ℂ) : Germ _ ℂ) at h'
    exact Germ.coe_eq.1 h'
  ·
    let G : ((Fin d → ℂ) → ℂ) →+* Germ (𝓝 (A w)) ℂ := Germ.coeRingHom _
    let ιR : R →+* Germ (𝓝 (A w)) ℂ := (holGerms (A w)).subtype
    let lift : R[X] → ((Fin d → ℂ) → ℂ)[X] := fun q =>
      ∑ i ∈ Finset.range (q.natDegree + 1), C (rep (q.coeff i)).1 * X ^ i
    have hGrep : ∀ r : R, G (rep r).1 = ιR r := fun r => congrArg Subtype.val (toGerm_rep r)
    have hlc : ∀ (q : R[X]) (i : ℕ), G ((lift q).coeff i) = ιR (q.coeff i) := by
      intro q i
      simp only [lift, finsetSum_coeff, coeff_C_mul_X_pow]
      by_cases hi : i < q.natDegree + 1
      · rw [Finset.sum_eq_single i (fun j _ hji => if_neg (Ne.symm hji))
          (fun h => absurd (Finset.mem_range.2 hi) h), if_pos rfl, hGrep]
      · rw [Finset.sum_eq_zero (fun j hj => if_neg (fun h => by subst h; exact hi (Finset.mem_range.1 hj))),
          map_zero, coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    have hlift : ∀ q : R[X], (lift q).map G = q.map ιR := fun q => by
      ext i
      rw [coeff_map, coeff_map, hlc]
    let Fm : ((Fin d → ℂ) → ℂ)[X] := X ^ N + ∑ j : Fin N, C (cf j) * X ^ (j : ℕ)
    have hFm : Fm.map G = m.map ιR := by
      conv_rhs => rw [hmon.as_sum]
      simp only [Fm, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum, Polynomial.map_mul,
        map_C, cf, hGrep]
      rw [← Fin.sum_univ_eq_sum_range (fun i => C (ιR (m.coeff i)) * X ^ i) N]
    let E : ((Fin d → ℂ) → ℂ)[X] := lift a * Fm + lift b * derivative Fm - C δ
    have hE : E.map G = 0 := by
      have h1 : E.map G = (a * m + b * derivative m - C D).map ιR := by
        simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, ← derivative_map, hlift, hFm,
          map_C, δ, hGrep]
      rw [h1, hab, sub_self, Polynomial.map_zero]
    have hev : ∀ᶠ y in 𝓝 (A w), ∀ i ∈ E.support, E.coeff i y = 0 := by
      rw [Filter.eventually_all_finset]
      intro i _
      have h := congrArg (fun q => q.coeff i) hE
      simp only [coeff_map, coeff_zero] at h
      exact Germ.coe_eq.1 h
    filter_upwards [hev] with y hy hδy
    let ev : ((Fin d → ℂ) → ℂ) →+* ℂ := Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y
    have hE0 : E.map ev = 0 := by
      ext i
      rw [coeff_map, coeff_zero]
      by_cases hi : E.coeff i = 0
      · rw [hi, map_zero]
      · exact hy i (mem_support_iff.2 hi)
    have hFy : Fm.map ev = monicOfCoeffs fun j => cf j y := by
      simp [Fm, monicOfCoeffs, Polynomial.map_sum, ev]
    rw [separable_def, ← hFy]
    simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map,
      sub_eq_zero] at hE0
    refine ⟨C (δ y)⁻¹ * (lift a).map ev, C (δ y)⁻¹ * (lift b).map ev, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_add, hE0, ← C_mul, show ev δ = δ y from rfl, inv_mul_cancel₀ hδy, C_1]
  ·
    intro g hg
    have hall : ∀ z ∈ Algebra.adjoin R (Set.range x),
        ∃ M : ℕ, algebraMap R B D ^ M * z ∈ Algebra.adjoin R {ℓB} := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        exact ⟨1, by rw [pow_one, hQ j]; exact aeval_mem_adjoin_singleton R ℓB⟩
      | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
      | add u v _ _ hu hv =>
        obtain ⟨M₁, h₁⟩ := hu
        obtain ⟨M₂, h₂⟩ := hv
        refine ⟨M₁ + M₂, ?_⟩
        have : algebraMap R B D ^ (M₁ + M₂) * (u + v) = algebraMap R B D ^ M₂ * (algebraMap R B D ^ M₁ * u) +
            algebraMap R B D ^ M₁ * (algebraMap R B D ^ M₂ * v) := by ring
        rw [this]
        exact Subalgebra.add_mem _
          (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₁)
          (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ D) _) h₂)
      | mul u v _ _ hu hv =>
        obtain ⟨M₁, h₁⟩ := hu
        obtain ⟨M₂, h₂⟩ := hv
        refine ⟨M₁ + M₂, ?_⟩
        rw [show algebraMap R B D ^ (M₁ + M₂) * (u * v) =
          (algebraMap R B D ^ M₁ * u) * (algebraMap R B D ^ M₂ * v) by ring]
        exact Subalgebra.mul_mem _ h₁ h₂
    obtain ⟨M, hM⟩ := hall (cl (mkA g hg)) (by rw [hx]; exact Algebra.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hM
    obtain ⟨Q', hQ'⟩ := hM
    have hr : aeval ℓB (Q' %ₘ m) = algebraMap R B D ^ M * cl (mkA g hg) := by
      rw [aeval_modByMonic_eq_self_of_root hm0]
      exact hQ'
    have hrdeg : (Q' %ₘ m).natDegree < N := natDegree_modByMonic_lt Q' hmon hm1
    refine ⟨M, fun j => (rep ((Q' %ₘ m).coeff j)).1, fun j => (rep ((Q' %ₘ m).coeff j)).2, ?_⟩
    have hU : ((compA A w (rep D) ^ M * mkA g hg -
        ∑ j : Fin N, compA A w (rep ((Q' %ₘ m).coeff j)) * lA ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
        fun z => δ (A z) ^ M * g z - ∑ j : Fin N, (rep ((Q' %ₘ m).coeff j)).1 (A z) * ℓ z ^ (j : ℕ) := by
      funext z
      simp [lA, mkA, compA, δ, Finset.sum_apply]
    rw [← hU, ← hcl0, map_sub, ← haev _ N hrdeg, hr, map_mul, map_pow, hcomp, sub_self]
  ·
    intro g hg
    exact hCE σ w k p d A hp hint hgen g hg
  ·
    intro hδ
    have h0 : cl (compA A w (rep D)) = 0 := (hcl0 _).2 hδ
    rw [hcomp] at h0
    exact hD0 (hRB (h0.trans (map_zero _).symm))

end PrimeGermPrimitivePresentation

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
