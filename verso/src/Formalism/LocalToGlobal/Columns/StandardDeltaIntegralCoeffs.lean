import Mathlib
import Formalism.LocalToGlobal.Columns.SummandSlopeOfThreeLemmas
import Formalism.LocalToGlobal.Columns.MaxSlopeOrthogonalNegLog

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section Mon

variable {ι : Type} [Fintype ι] {n : ℕ}

def MonOK (lam : ι → DomWeight n) (m : (ι × Fin n × Fin n) →₀ ℕ) : Prop :=
  ∀ τ s, ∑ a, m (τ, a, s) = (lam τ).natW s

def MonI (lam : ι → DomWeight n) : Type := {m : (ι × Fin n × Fin n) →₀ ℕ // MonOK lam m}

/- English proof (translation)
Set `M : (ι × Fin n × Fin n) →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun v => (lam v.1).natW v.2.2`. Use `(Set.finite_Icc (0 : (ι × Fin n × Fin n) →₀ ℕ) M).subset ?_` and prove the remaining obligations. Introduce `m hm`. Use `⟨zero_le, fun v => ?_⟩` and prove the remaining obligations. Take `⟨τ, a, s⟩` from `v`.

Use `show m (τ, a, s) ≤ (lam τ).natW s`. Rewrite using `[← hm τ s]`. Conclude with `Finset.single_le_sum (f := fun a => m (τ, a, s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.
-/
theorem monOK_finite (lam : ι → DomWeight n) : {m | MonOK lam m}.Finite := by
  classical
  let M : (ι × Fin n × Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun v => (lam v.1).natW v.2.2
  refine (Set.finite_Icc (0 : (ι × Fin n × Fin n) →₀ ℕ) M).subset ?_
  intro m hm
  refine ⟨zero_le, fun v => ?_⟩
  obtain ⟨τ, a, s⟩ := v
  show m (τ, a, s) ≤ (lam τ).natW s
  rw [← hm τ s]
  exact Finset.single_le_sum (f := fun a => m (τ, a, s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

instance (lam : ι → DomWeight n) : Finite (MonI lam) := (monOK_finite lam).to_subtype

instance (lam : ι → DomWeight n) : Fintype (MonI lam) := Fintype.ofFinite _

instance (lam : ι → DomWeight n) : DecidableEq (MonI lam) := Classical.decEq _

/- English proof (translation)
Establish `e : u.sum (fun i c => c • Formalism.GradedWeylDivisibility.colW r n i) = ∑ i, u i • Formalism.GradedWeylDivisibility.colW r n i` using `Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ _)`. Rewrite using `[← h, Finsupp.weight_apply, e, Finset.sum_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW, Pi.single_apply]`.
-/
theorem column_sum_eq_weight {r : ℕ} (ν : Fin n → ℕ) (u : (Fin r × Fin n) →₀ ℕ) (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) u = ν) (s : Fin n) :
    ∑ a, u (a, s) = ν s := by
  classical
  have e : u.sum (fun i c => c • Formalism.GradedWeylDivisibility.colW r n i) = ∑ i, u i • Formalism.GradedWeylDivisibility.colW r n i :=
    Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ _)
  rw [← h, Finsupp.weight_apply, e, Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

open Classical in
/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `m hm τ s`. Rewrite `hm` using `[Finset.prod_empty, coeff_one]`. Establish `: m = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hm (if_neg fun h' => h h'.symm)`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Consider the case `insert t T ht ih`.

Introduce `m hm τ s`. Rewrite `hm` using `[Finset.prod_insert ht]`. Establish `hm'` using `support_mul _ _ (mem_support_iff.2 hm)`. Take `⟨m1, h1, m2, h2, rfl⟩` from `Finset.mem_add.1 hm'`. Establish `i2` using `ih m2 (mem_support_iff.1 h2) τ s`.

Take `⟨u, hu, hu0⟩` from `coeff_rename_ne_zero _ _ _ (mem_support_iff.1 h1)`. Establish `hinj : Function.Injective (fun v : Fin n × Fin n => (t, v))` using `fun a b h => (Prod.mk.inj h).2`. Establish `hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) u = (lam t).natW`. Use `(hf t).1` as an intermediate fact. Conclude with `this hu0`.

Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, i2]`. Distinguish the cases in `hτ : τ = t`. Substitute `hτ` using the available equality. Establish `: ∀ a, m1 (τ, a, s) = u (a, s)` using `fun a => by`. Rewrite using `[← hu]`.

Conclude with `Finsupp.mapDomain_apply hinj u (a, s)`. Simplify using `only [this, column_sum_eq_weight _ u hw s, if_neg ht, Finset.mem_insert, true_or, if_true, add_zero]`. Establish `: ∀ a, m1 (τ, a, s) = 0` using `fun a => by`. Rewrite using `[← hu]`. Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨v, hv⟩`. Conclude with `hτ (Prod.mk.inj hv).1.symm`. Simplify using `only [this, Finset.sum_const_zero, zero_add, Finset.mem_insert, hτ, false_or]`.
-/
theorem product_support_weights (K : Type) [Field K] (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) (T : Finset ι) :
    ∀ m, coeff m (∏ τ ∈ T, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ≠ 0 → ∀ τ s, ∑ a, m (τ, a, s) = if τ ∈ T then (lam τ).natW s else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro m hm τ s
    rw [Finset.prod_empty, coeff_one] at hm
    have : m = 0 := by
      by_contra h
      exact hm (if_neg fun h' => h h'.symm)
    subst this
    simp
  | insert t T ht ih =>
    intro m hm τ s
    rw [Finset.prod_insert ht] at hm
    have hm' := support_mul _ _ (mem_support_iff.2 hm)
    obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.1 hm'
    have i2 := ih m2 (mem_support_iff.1 h2) τ s
    obtain ⟨u, hu, hu0⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 h1)
    have hinj : Function.Injective (fun v : Fin n × Fin n => (t, v)) := fun a b h => (Prod.mk.inj h).2
    have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) u = (lam t).natW := by
      have := (hf t).1
      exact this hu0
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, i2]
    by_cases hτ : τ = t
    · subst hτ
      have : ∀ a, m1 (τ, a, s) = u (a, s) := fun a => by
        rw [← hu]; exact Finsupp.mapDomain_apply hinj u (a, s)
      simp only [this, column_sum_eq_weight _ u hw s, if_neg ht, Finset.mem_insert, true_or, if_true, add_zero]
    · have : ∀ a, m1 (τ, a, s) = 0 := fun a => by
        rw [← hu]
        refine Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨v, hv⟩
        exact hτ (Prod.mk.inj hv).1.symm
      simp only [this, Finset.sum_const_zero, zero_add, Finset.mem_insert, hτ, false_or]

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Introduce `m hm τ s`.

Use `product_support_weights K lam f hf Finset.univ m hm τ s` as an intermediate fact. Simplify using `using this`. Consider the case `zero => intro m hm`. Conclude with `absurd (coeff_zero m) hm`. Consider the case `add x y _ _ hx hy`.

Introduce `m hm`. Rewrite `hm` using `[coeff_add]`. Distinguish the cases in `h : coeff m x = 0`. Conclude with `hy m (by rw [h, zero_add] at hm; exact hm)`. Conclude with `hx m h`.

Consider the case `smul c x _ hx`. Introduce `m hm`. Rewrite `hm` using `[coeff_smul]`. Conclude with `hx m (fun h => hm (by rw [h, smul_zero]))`.
-/
theorem coefficient_space_support (K : Type) [Field K] (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    ∀ m, coeff m F ≠ 0 → MonOK lam m := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    intro m hm τ s
    have := product_support_weights K lam f hf Finset.univ m hm τ s
    simpa using this
  | zero => intro m hm; exact absurd (coeff_zero m) hm
  | add x y _ _ hx hy =>
    intro m hm
    rw [coeff_add] at hm
    by_cases h : coeff m x = 0
    · exact hy m (by rw [h, zero_add] at hm; exact hm)
    · exact hx m h
  | smul c x _ hx =>
    intro m hm
    rw [coeff_smul] at hm
    exact hx m (fun h => hm (by rw [h, smul_zero]))

variable {K : Type} [Field K]

def cfMap (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam →ₗ[K] (MonI lam → K) where
  toFun x := fun m => coeff m.1 (trAct g x.1)
  map_add' x y := by funext m; simp
  map_smul' c x := by funext m; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cfMap_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (x : VV K lam) (m : MonI lam) :
    cfMap lam g x m = coeff m.1 (trAct g x.1) := rfl

/- English proof (translation)
The claim follows from `(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).2 (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ)) (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF`.
-/
theorem transpose_action_mem (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K lam) : trAct g F ∈ VV K lam :=
  (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).2
    (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ))
    (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, ← trAct_mul, mul_inv_cancel, trAct_one]`. Both sides reduce to the same expression.
-/
theorem transpose_action_inv_right (g : ι → GL (Fin n) K) (F : Pol K ι n) : trAct g (trAct g⁻¹ F) = F := by
  rw [← AlgHom.comp_apply, ← trAct_mul, mul_inv_cancel, trAct_one]
  rfl

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, ← trAct_mul, inv_mul_cancel, trAct_one]`. Both sides reduce to the same expression.
-/
theorem transpose_action_inv_left (g : ι → GL (Fin n) K) (F : Pol K ι n) : trAct g⁻¹ (trAct g F) = F := by
  rw [← AlgHom.comp_apply, ← trAct_mul, inv_mul_cancel, trAct_one]
  rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h0 : trAct g x.1 = 0`. Use extensionality with `m`. Rewrite using `[coeff_zero]`.

Assume the negation of the conclusion as `h`. Establish `hm` using `coefficient_space_support K lam (transpose_action_mem lam g x.2) m h`. Conclude with `h (congrFun hx ⟨m, hm⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `transpose_action_inv_left g x.1` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`.
-/
theorem cfMap_injective (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : Function.Injective (cfMap lam g) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : trAct g x.1 = 0 := by
    ext m
    rw [coeff_zero]
    by_contra h
    have hm := coefficient_space_support K lam (transpose_action_mem lam g x.2) m h
    exact h (congrFun hx ⟨m, hm⟩)
  apply Subtype.ext
  have := transpose_action_inv_left g x.1
  rw [h0, map_zero] at this
  exact this.symm

end Mon

section Int

variable {K : Type} [Field K] [NumberField K]

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {x | x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)}
  mul_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 hy
    refine ⟨s * t, mul_mem hs ht, Submodule.mem_one.2 ⟨a * b, ?_⟩⟩
    rw [map_mul, ha, hb, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  one_mem' := ⟨1, one_mem _, by rw [one_smul]; exact Submodule.one_le.1 le_rfl⟩
  add_mem' := fun {x y} hx hy => (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).add_mem hx hy
  zero_mem' := (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).zero_mem
  neg_mem' := fun {x} hx => (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).neg_mem hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) : x ∈ locRing w ↔ x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := Iff.rfl

/- English proof (translation)
Use `⟨∑ m ∈ P.support, monomial m ⟨coeff m P, h m⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [map_monomial, Subring.coe_subtype]`. Conclude with `P.support_sum_monomial_coeff`.
-/
theorem mem_range_of_coeff_mem {σ : Type} (R0 : Subring K) {P : MvPolynomial σ K} (h : ∀ m, coeff m P ∈ R0) :
    P ∈ (map (σ := σ) R0.subtype).range := by
  refine ⟨∑ m ∈ P.support, monomial m ⟨coeff m P, h m⟩, ?_⟩
  rw [map_sum]
  simp only [map_monomial, Subring.coe_subtype]
  exact P.support_sum_monomial_coeff

/- English proof (translation)
Take `⟨Q, rfl⟩` from `hP`. Rewrite using `[coeff_map]`. Conclude with `(coeff m Q).2`.
-/
theorem coeff_mem_of_mem_range {σ : Type} (R0 : Subring K) {P : MvPolynomial σ K} (hP : P ∈ (map (σ := σ) R0.subtype).range) (m : σ →₀ ℕ) :
    coeff m P ∈ R0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [coeff_map]
  exact (coeff m Q).2

/- English proof (translation)
Take `⟨Q, rfl⟩` from `hP`. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[map_C, algHom_C]`. Conclude with `⟨C a, by simp⟩`.

Consider the case `add p q hp hq`. Rewrite using `[map_add (map R0.subtype), map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul (map R0.subtype), map_X, map_mul, blockAct_X]`.

Conclude with `mul_mem hp (sum_mem fun b _ => mul_mem ⟨C ⟨_, hU v.1 v.2.1 b⟩, by simp⟩ ⟨X (v.1, b, v.2.2), by simp⟩)`.
-/
theorem block_action_integral (R0 : Subring K) {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ R0)
    {P : MvPolynomial (ι × Fin n × Fin n) K} (hP : P ∈ (map (σ := ι × Fin n × Fin n) R0.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (map (σ := ι × Fin n × Fin n) R0.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact ⟨C a, by simp⟩
  | add p q hp hq =>
    rw [map_add (map R0.subtype), map_add]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (map R0.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem ⟨C ⟨_, hU v.1 v.2.1 b⟩, by simp⟩ ⟨X (v.1, b, v.2.2), by simp⟩)

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `delStd Formalism.GradedWeylDivisibility.tensorLat at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `choose f0 _ hf0 using fun s => Submodule.mem_map.1 (hf s)`.

Establish `e : (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (f s)) = map (algebraMap (𝓞 K) K) (∏ s, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) s (f0 s))`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← hf0 s]`. Simplify using `only [Formalism.GradedWeylDivisibility.blockEmb, toK, AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]`.

Both sides reduce to the same expression. Rewrite using `[e, coeff_map]`. Conclude with `Submodule.mem_one.2 ⟨_, rfl⟩`. Consider the case `zero => rw [coeff_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [coeff_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [coeff_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem standard_delta_integral_coeffs (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ delStd K lam) (m : (ι × Fin n × Fin n) →₀ ℕ) :
    coeff m F ∈ (1 : Submodule (𝓞 K) K) := by
  unfold delStd Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    choose f0 _ hf0 using fun s => Submodule.mem_map.1 (hf s)
    have e : (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (f s)) = map (algebraMap (𝓞 K) K) (∏ s, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) s (f0 s)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← hf0 s]
      simp only [Formalism.GradedWeylDivisibility.blockEmb, toK, AlgHom.toLinearMap_apply, mapAlgHom_apply, map_rename]
      rfl
    rw [e, coeff_map]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  | zero => rw [coeff_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coeff_add]; exact add_mem hx hy
  | smul c x _ hx => rw [coeff_smul]; exact Submodule.smul_mem _ c hx

def twId (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) K :=
  ⨅ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (_ : ∀ τ, IsBasisAt w (M τ) (B τ)),
    (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).comap ((LinearMap.mulLeft K (detTwK lam B⁻¹)).restrictScalars (𝓞 K))

/- English proof (translation)
Simplify using `only [twId, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]`.
-/
theorem mem_twId (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (a : K) :
    a ∈ twId lam M ↔ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      detTwK lam B⁻¹ * a ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  simp only [twId, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]

/- English proof (translation)
Introduce `x hx` and use `⟨1, one_mem _, by rwa [one_smul]⟩`.
-/
theorem le_localisation {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) :
    L ≤ localization₂ w.asIdeal L := fun x hx => ⟨1, one_mem _, by rwa [one_smul]⟩

/- English proof (translation)
Rewrite using `[mem_twId]`. Introduce `w B hB`. Establish `hx' : actP lam B⁻¹ x.1 ∈ localization₂ w.asIdeal (delStd K lam)`. Establish `h` using `hx`. Simplify using `only [delK, delP, transLat, Submodule.mem_comap, Submodule.mem_iInf] at h`.

Conclude with `h w B hB`. Establish `hF0 : actP lam B⁻¹ x.1 ∈ (map (σ` using `ι × Fin n × Fin n) (locRing w).subtype).range := by`. Use `mem_range_of_coeff_mem _ fun m' => ?_` and prove the remaining obligations. Take `⟨s, hs, hsF⟩` from `hx'`. Rewrite using `[mem_locRing]`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_smul]`. Conclude with `standard_delta_integral_coeffs lam hsF m'`. Establish `hU : ∀ τ a b, (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ a b ∈ locRing w`. Introduce `τ a b`.

Establish `hcol : (fun c => (B τ : Matrix (Fin n) (Fin n) K) c a) ∈ localization₂ w.asIdeal (M τ)`. Rewrite using `[hB τ]`. Conclude with `le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)`. Take `⟨s, hs, hsx⟩` from `hcol`. Rewrite using `[mem_locRing]`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `hg τ _ hsx b` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul]`. Establish `e : (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ a b = ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ fun c => (B τ : Matrix (Fin n) (Fin n) K) c a) b`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[e]`. Conclude with `this`. Establish `hkey` using `coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1`. Establish `e : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) (actP lam B⁻¹ x.1) = detTwK lam B⁻¹ • trAct g x.1` using `by show trAct (g * B) (actP lam B⁻¹ x.1) = _`. Rewrite using `[trAct_mul]`.

Simplify using `only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]`. Rewrite `hkey` using `[e, coeff_smul, smul_eq_mul, mem_locRing]`. Conclude with `hkey`.
-/
theorem coefficient_map_mem_twisted (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K)
    (hg : ∀ τ, ∀ x ∈ M τ, ∀ a, ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K))
    (x : VV K lam) (hx : x ∈ delK lam M) (m : MonI lam) : cfMap lam g x m ∈ twId lam M := by
  rw [mem_twId]
  intro w B hB
  have hx' : actP lam B⁻¹ x.1 ∈ localization₂ w.asIdeal (delStd K lam) := by
    have h := hx
    simp only [delK, delP, transLat, Submodule.mem_comap, Submodule.mem_iInf] at h
    exact h w B hB
  have hF0 : actP lam B⁻¹ x.1 ∈ (map (σ := ι × Fin n × Fin n) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    obtain ⟨s, hs, hsF⟩ := hx'
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    rw [← coeff_smul]
    exact standard_delta_integral_coeffs lam hsF m'
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ a b ∈ locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin n) (Fin n) K) c a) ∈ localization₂ w.asIdeal (M τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := hg τ _ hsx b
    rw [Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ a b =
        ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ fun c => (B τ : Matrix (Fin n) (Fin n) K) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (((g * B) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) (actP lam B⁻¹ x.1) =
      detTwK lam B⁻¹ • trAct g x.1 := by
    show trAct (g * B) (actP lam B⁻¹ x.1) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int

end Formalism.L2.Col
