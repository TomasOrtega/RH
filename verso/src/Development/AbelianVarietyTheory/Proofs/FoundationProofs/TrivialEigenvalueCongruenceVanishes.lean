import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZeroStatement

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.LamZero

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp [slP]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]`.
-/
theorem map_slP {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (Q : MvPolynomial (Fin 2) R) : MvPolynomial.map f (slP m Q) = slP m (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

/- English proof (translation)
Simplify using `[MvPolynomial.smul_eq_C_mul]`.
-/
theorem map_coef_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (c • Q) = f c • MvPolynomial.map f Q := by
  simp [MvPolynomial.smul_eq_C_mul]

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

/- English proof (translation)
Use extensionality with `m`. Establish `h1` using `congrArg (MvPolynomial.coeff m) h`. Simplify using `only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero, smul_eq_mul] at h1`. Use `Fintype.linearIndependent_iff.1 hv (fun a => MvPolynomial.coeff m (Q a)) (by` as an intermediate fact. Simplify `h1)` using `[Algebra.smul_def, mul_comm]`.

Simplify using `using this a`.
-/
theorem eq_zero_of_sum {k : ℕ} {v : Fin k → E} (hv : LinearIndependent ℤ_[l] v)
    (Q : Fin k → MvPolynomial (Fin 2) ℤ_[l])
    (h : ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) = 0) (a : Fin k) : Q a = 0 := by
  ext m
  have h1 := congrArg (MvPolynomial.coeff m) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
    smul_eq_mul] at h1
  have := Fintype.linearIndependent_iff.1 hv (fun a => MvPolynomial.coeff m (Q a)) (by
    simpa [Algebra.smul_def, mul_comm] using h1)
  simpa using this a

/- English proof (translation)
Set `L` to `Submodule.span ℤ_[l] (S : Set E)`. Use `haveI : Module.Finite ℤ_[l] L := Module.Finite.span_finset _ _`. Use `haveI : NoZeroSMulDivisors ℤ_[l] E := ⟨fun {c x} h => by`. Rewrite `h` using `[Algebra.smul_def]`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `Or.inl (hinj (by simpa using h))`. Conclude with `Or.inr h⟩`. Use `haveI : Module.Free ℤ_[l] L := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.finBasis ℤ_[l] L`. Use `⟨_, fun a => (b a : E), fun x => if h : x ∈ L then b.repr ⟨x, h⟩ else 0, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `b.linearIndependent.map' L.subtype (by simp)`. Introduce `x hx`. Establish `hxL : x ∈ L` using `Submodule.subset_span hx`. Establish `h2 : ((∑ i, (b.repr ⟨x, hxL⟩) i • b i : L) : E) = x` using `congrArg Subtype.val (b.sum_repr _)`. Rewrite `h2` using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul] at h2`. Simplify using `only [dif_pos hxL]`. Conclude with `h2.symm`.
-/
theorem exists_basis (hinj : Function.Injective (algebraMap ℤ_[l] E)) (S : Finset E) :
    ∃ (k : ℕ) (v : Fin k → E) (r : E → Fin k → ℤ_[l]), LinearIndependent ℤ_[l] v ∧
      ∀ x ∈ S, x = ∑ a, r x a • v a := by
  classical
  let L := Submodule.span ℤ_[l] (S : Set E)
  haveI : Module.Finite ℤ_[l] L := Module.Finite.span_finset _ _
  haveI : NoZeroSMulDivisors ℤ_[l] E := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h⟩
  haveI : Module.Free ℤ_[l] L := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] L
  refine ⟨_, fun a => (b a : E), fun x => if h : x ∈ L then b.repr ⟨x, h⟩ else 0, ?_, ?_⟩
  · exact b.linearIndependent.map' L.subtype (by simp)
  · intro x hx
    have hxL : x ∈ L := Submodule.subset_span hx
    have h2 : ((∑ i, (b.repr ⟨x, hxL⟩) i • b i : L) : E) = x := congrArg Subtype.val (b.sum_repr _)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    simp only [dif_pos hxL]
    exact h2.symm

/- English proof (translation)
Use `⟨fun a => ∑ m ∈ P.support, MvPolynomial.monomial m (r (P.coeff m) a), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Simplify using `only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial, smul_eq_mul, map_sum]`. Distinguish the cases in `hn : n ∈ P.support`. Simplify using `only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_pos hn]`.

Use `(hr n hn).trans ?_` and prove the remaining obligations. Simplify using `[Algebra.smul_def, mul_comm]`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hn]`. Simplify using `only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_neg hn, mul_zero, Finset.sum_const_zero]`.
-/
theorem poly_decomp {k : ℕ} (v : Fin k → E) (r : E → Fin k → ℤ_[l]) (P : MvPolynomial (Fin 2) E)
    (hr : ∀ m ∈ P.support, P.coeff m = ∑ a, r (P.coeff m) a • v a) :
    ∃ Q : Fin k → MvPolynomial (Fin 2) ℤ_[l], P = ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) := by
  classical
  refine ⟨fun a => ∑ m ∈ P.support, MvPolynomial.monomial m (r (P.coeff m) a), ?_⟩
  ext n
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial,
    smul_eq_mul, map_sum]
  by_cases hn : n ∈ P.support
  · simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_pos hn]
    refine (hr n hn).trans ?_
    simp [Algebra.smul_def, mul_comm]
  · rw [MvPolynomial.notMem_support_iff.1 hn]
    simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_neg hn, mul_zero,
      Finset.sum_const_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

/- English proof (translation)
Simplify using `only [map_sum, map_coef_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hf i, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[Algebra.smul_def]`. Conclude with `mul_comm _ _`.
-/
theorem sum_reorg {n k : ℕ} (f : Fin n → E) (v : Fin k → E) (c : Fin n → Fin k → ℤ_[l])
    (hf : ∀ i, f i = ∑ a, c i a • v a) (F : Fin n → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (∑ i, c i a • F i) =
      ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i) := by
  simp only [map_sum, map_coef_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Algebra.smul_def]
  exact mul_comm _ _

/- English proof (translation)
Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, RingHom.map_sub, map_slP, smul_sub]`.
-/
theorem sum_slP {k : ℕ} (v : Fin k → E) (m : Matrix (Fin 2) (Fin 2) ℤ) (A B : Fin k → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (slP m (A a) - B a) =
      slP m (∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (A a)) -
        ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (B a) := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, RingHom.map_sub, map_slP, smul_sub]

/- English proof (translation)
Establish `: ∀ i, f i ⊗ₜ[ℤ_[l]] b i = ∑ a, v a ⊗ₜ[ℤ_[l]] (c i a • b i)`. Introduce `i`. Rewrite using `[hf i, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul]`.

Simplify using `only [this]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← TensorProduct.tmul_sum, hb a, TensorProduct.tmul_zero]`.
-/
theorem tmul_sum_zero {M : Type} [AddCommGroup M] [Module ℤ_[l] M] {n k : ℕ} (f : Fin n → E) (v : Fin k → E)
    (c : Fin n → Fin k → ℤ_[l]) (hf : ∀ i, f i = ∑ a, c i a • v a) (b : Fin n → M)
    (hb : ∀ a, ∑ i, c i a • b i = 0) : ∑ i, f i ⊗ₜ[ℤ_[l]] b i = 0 := by
  have : ∀ i, f i ⊗ₜ[ℤ_[l]] b i = ∑ a, v a ⊗ₜ[ℤ_[l]] (c i a • b i) := by
    intro i
    rw [hf i, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← TensorProduct.tmul_sum, hb a, TensorProduct.tmul_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Take `⟨hadd, hzero, hsmul, -, -⟩` from `GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l`. Establish `: ∀ s : Finset (Fin n), Rel X l (∑ j ∈ s, c j • b j) (∑ j ∈ s, c j • F j)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hzero`.

Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj]`. Conclude with `hadd _ _ _ _ (hsmul _ _ _ (hR j)) ih`. Conclude with `this Finset.univ`.
-/
theorem rel_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n : ℕ} (b : Fin n → X.Fn l)
    (F : Fin n → ℂ → MvPolynomial (Fin 2) ℤ_[l]) (hR : ∀ j, Rel X l (b j) (F j)) (c : Fin n → ℤ_[l]) :
    Rel X l (∑ j, c j • b j) (∑ j, c j • F j) := by
  obtain ⟨hadd, hzero, hsmul, -, -⟩ := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have : ∀ s : Finset (Fin n), Rel X l (∑ j ∈ s, c j • b j) (∑ j ∈ s, c j • F j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd _ _ _ _ (hsmul _ _ _ (hR j)) ih
  exact this Finset.univ

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3

open LamZero in

/- English proof (translation)
Introduce `Ω _ _ ε X l _ E _ _ hinj w Γ M₀ hM₀ hΓ p hp hT`. Take `⟨n, f, g, hfg⟩` from `Submodule.mem_span_set'.1 hp`. Use `choose b F hRel hg using fun i => (g i).2`. Take `⟨ψ, P, hψ, hP⟩` from `hT`. Take `⟨k, v, r, hv, hr⟩` from `exists_basis hinj (Finset.univ.image f ∪ P.support.image (fun m => P.coeff m))`.

Establish `hf : ∀ i, f i = ∑ a, r (f i) a • v a` using `fun i => hr _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Take `⟨Q, hQ⟩` from `poly_decomp v r P (fun m hm => hr _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)))`. Set `c : Fin n → Fin k → ℤ_[l]` to `fun i a => r (f i) a`. Set `G : Fin k → ℂ → MvPolynomial (Fin 2) ℤ_[l]` to `fun a z => ∑ i, c i a • F i z`. Establish `hp1 : p.1 = ∑ i, f i ⊗ₜ[ℤ_[l]] b i`.

Rewrite using `[← hfg]`. Simplify using `[Prod.fst_sum, hg, TensorProduct.smul_tmul']`. Establish `hp2 : ∀ z, p.2 z = ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i z)`. Introduce `z`. Rewrite using `[← hfg]`.

Simplify using `[Prod.snd_sum, Finset.sum_apply, hg]`. Establish `hkey : ∀ z, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a z) = p.2 z` using `fun z => (sum_reorg f v c hf (fun i => F i z)).trans (hp2 z).symm`. Establish `e1 : ∀ y, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a y - Q a) = p.2 y - P`. Introduce `y`. Simplify using `only [RingHom.map_sub, smul_sub, Finset.sum_sub_distrib, hkey, ← hQ]`.

Establish `hGT : ∀ a, (fun z => G a z) ∈ Triv ℤ_[l] w Γ`. Introduce `a`. Use `⟨fun z => G a z - Q a, Q a, fun γ hγ z hz => ?_, fun z _ => by ring⟩` and prove the remaining obligations. Establish `hγz : mob (ofSL γ) z ∈ Hs` using `GlobalTheory.KZ.MobLaws.mob_mem _ hz`. Establish `h0` using `eq_zero_of_sum hv (fun a => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (G a (mob (ofSL γ) z) - Q a) - (G a z - Q a)) (by`.

Rewrite using `[sum_slP, e1, e1, hP _ hγz, hP _ hz, add_sub_cancel_right, add_sub_cancel_right, hψ γ hγ z hz, sub_self]) a`. Conclude with `sub_eq_zero.1 h0`. Establish `hb : ∀ a, ∑ i, c i a • b i = 0`. Introduce `a`. Establish `hR` using `rel_sum X l b F hRel (fun i => c i a)`.

Establish `hG : (∑ i, c i a • F i) = fun z => G a z`. Use function extensionality and compare the values at `z`. Simplify using `[G, Finset.sum_apply]`. Rewrite `hR` using `[hG]`. Conclude with `GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero Ω ε X l w Γ M₀ hM₀ hΓ _ _ hR (hGT a)`.

Rewrite using `[hp1]`. Conclude with `tmul_sum_zero f v c hf b hb`.
-/
theorem lam_fst_eq_zero_of_triv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  intro Ω _ _ ε X l _ E _ _ hinj w Γ M₀ hM₀ hΓ p hp hT
  classical
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hp
  choose b F hRel hg using fun i => (g i).2
  obtain ⟨ψ, P, hψ, hP⟩ := hT
  obtain ⟨k, v, r, hv, hr⟩ := exists_basis hinj (Finset.univ.image f ∪ P.support.image (fun m => P.coeff m))
  have hf : ∀ i, f i = ∑ a, r (f i) a • v a := fun i =>
    hr _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  obtain ⟨Q, hQ⟩ := poly_decomp v r P (fun m hm =>
    hr _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)))
  let c : Fin n → Fin k → ℤ_[l] := fun i a => r (f i) a
  let G : Fin k → ℂ → MvPolynomial (Fin 2) ℤ_[l] := fun a z => ∑ i, c i a • F i z
  have hp1 : p.1 = ∑ i, f i ⊗ₜ[ℤ_[l]] b i := by
    rw [← hfg]
    simp [Prod.fst_sum, hg, TensorProduct.smul_tmul']
  have hp2 : ∀ z, p.2 z = ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i z) := by
    intro z
    rw [← hfg]
    simp [Prod.snd_sum, Finset.sum_apply, hg]
  have hkey : ∀ z, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a z) = p.2 z := fun z =>
    (sum_reorg f v c hf (fun i => F i z)).trans (hp2 z).symm
  have e1 : ∀ y, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a y - Q a) = p.2 y - P := by
    intro y
    simp only [RingHom.map_sub, smul_sub, Finset.sum_sub_distrib, hkey, ← hQ]
  have hGT : ∀ a, (fun z => G a z) ∈ Triv ℤ_[l] w Γ := by
    intro a
    refine ⟨fun z => G a z - Q a, Q a, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have hγz : mob (ofSL γ) z ∈ Hs := GlobalTheory.KZ.MobLaws.mob_mem _ hz
    have h0 := eq_zero_of_sum hv (fun a => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (G a (mob (ofSL γ) z) - Q a) -
      (G a z - Q a)) (by
        rw [sum_slP, e1, e1, hP _ hγz, hP _ hz, add_sub_cancel_right, add_sub_cancel_right, hψ γ hγ z hz, sub_self]) a
    exact sub_eq_zero.1 h0
  have hb : ∀ a, ∑ i, c i a • b i = 0 := by
    intro a
    have hR := rel_sum X l b F hRel (fun i => c i a)
    have hG : (∑ i, c i a • F i) = fun z => G a z := by
      funext z; simp [G, Finset.sum_apply]
    rw [hG] at hR
    exact GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero Ω ε X l w Γ M₀ hM₀ hΓ _ _ hR (hGT a)
  rw [hp1]
  exact tmul_sum_zero f v c hf b hb

end GlobalTheory.KZ.H3
