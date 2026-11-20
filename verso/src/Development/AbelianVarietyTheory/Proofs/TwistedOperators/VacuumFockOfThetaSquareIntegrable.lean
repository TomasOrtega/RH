import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix Complex
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open GlobalTheory.Ker (ipO)
open scoped Classical ComplexConjugate

namespace GlobalTheory.VacuumFockLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hsub : (k + Finsupp.single v 1).support ⊆ insert v k.support`. Introduce `i hi`. Rewrite `hi` using `[Finsupp.mem_support_iff]`. Distinguish the cases in `h : i = v`. Conclude with `h ▸ Finset.mem_insert_self _ _`.

Use `Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr ?_)` and prove the remaining obligations. Simplify `hi` using `[Finsupp.single_apply, Ne.symm h]`. Establish `h1 : multiFact k = ∏ i ∈ insert v k.support, (k i).factorial` using `Finsupp.prod_of_support_subset _ (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)`. Establish `h2 : multiFact (k + Finsupp.single v 1) = ∏ i ∈ insert v k.support, ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial` using `Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => Nat.factorial_zero)`. Rewrite using `[h1, h2, ← Finset.mul_prod_erase _ (fun i => ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial) (Finset.mem_insert_self v k.support), ← Finset.mul_prod_erase _ (fun i => (k i).factorial) (Finset.mem_insert_self v k.support), ← mul_assoc]`.

Use `congr 1`. Simplify using `[Nat.factorial_succ]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : i ≠ v` using `Finset.ne_of_mem_erase hi`. Simplify using `[Finsupp.single_apply, Ne.symm hne]`.
-/
theorem multiFact_add_single {ι : Type} (k : ι →₀ ℕ) (v : ι) :
    multiFact (k + Finsupp.single v 1) = (k v + 1) * multiFact k := by
  classical
  have hsub : (k + Finsupp.single v 1).support ⊆ insert v k.support := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = v
    · exact h ▸ Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr ?_)
      simpa [Finsupp.single_apply, Ne.symm h] using hi
  have h1 : multiFact k = ∏ i ∈ insert v k.support, (k i).factorial :=
    Finsupp.prod_of_support_subset _ (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)
  have h2 : multiFact (k + Finsupp.single v 1) =
      ∏ i ∈ insert v k.support, ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial :=
    Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => Nat.factorial_zero)
  rw [h1, h2, ← Finset.mul_prod_erase _ (fun i => ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial)
      (Finset.mem_insert_self v k.support),
    ← Finset.mul_prod_erase _ (fun i => (k i).factorial) (Finset.mem_insert_self v k.support), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ v := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, Ne.symm hne]

/- English proof (translation)
Use `Finsupp.induction k h0 fun a b g _ _ ih => ?_` and prove the remaining obligations. Establish `key : ∀ n : ℕ, p (Finsupp.single a n + g)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using ih`.

Consider the case `succ n ihn`. Establish `e : Finsupp.single a (n + 1) + g = (Finsupp.single a n + g) + Finsupp.single a 1`. Rewrite using `[add_right_comm, ← Finsupp.single_add]`. Rewrite using `[e]`. Conclude with `h1 _ _ ihn`.

Conclude with `key b`.
-/
theorem multiIndex_induction {ι : Type} {p : (ι →₀ ℕ) → Prop} (h0 : p 0)
    (h1 : ∀ k v, p k → p (k + Finsupp.single v 1)) (k : ι →₀ ℕ) : p k := by
  refine Finsupp.induction k h0 fun a b g _ _ ih => ?_
  have key : ∀ n : ℕ, p (Finsupp.single a n + g) := by
    intro n
    induction n with
    | zero => simpa using ih
    | succ n ihn =>
      have e : Finsupp.single a (n + 1) + g = (Finsupp.single a n + g) + Finsupp.single a 1 := by
        rw [add_right_comm, ← Finsupp.single_add]
      rw [e]
      exact h1 _ _ ihn
  exact key b

/- English proof (translation)
Proceed by induction on `p generalizing y with`. Consider the case `nil => rfl`. Consider the case `cons x _ ih => simp only [List.foldr_cons, ih]`. Consider the case `swap x z l => simp only [List.foldr_cons]`. Conclude with `hF _ _ _`.

Consider the case `trans _ _ ih1 ih2 => exact (ih1 y).trans (ih2 y)`.
-/
private theorem foldr_eq_of_perm_of_comm {ι Y : Type} (F : ι → Y → Y) (hF : ∀ i j y, F i (F j y) = F j (F i y))
    {l₁ l₂ : List ι} (p : l₁.Perm l₂) (y : Y) : l₁.foldr F y = l₂.foldr F y := by
  induction p generalizing y with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x z l => simp only [List.foldr_cons]; exact hF _ _ _
  | trans _ _ ih1 ih2 => exact (ih1 y).trans (ih2 y)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons i l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih, hA]`.
-/
private theorem foldr_coe_eq_coe_foldr {ι X : Type} (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g) (g : M) (l : List ι) :
    l.foldr (fun i h => A i h) (g : X → ℂ) = ((l.foldr (fun i h => a i h) g : M) : X → ℂ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih, hA]

/- English proof (translation)
Establish `e : MvPolynomial.monomial u c = c • MvPolynomial.basisMonomials ι ℂ u`. Simplify using `only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul]`. Unfold `pureTensorL`. Rewrite using `[Module.Basis.constr_basis]`.
-/
private theorem pureTensorL_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (u : ι →₀ ℕ)
    (c : ℂ) : pureTensorL A f (MvPolynomial.monomial u c) = c • opPow A u f := by
  have e : MvPolynomial.monomial u c = c • MvPolynomial.basisMonomials ι ℂ u := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]

/- English proof (translation)
Take `⟨P, hPdef⟩ : ∃ P : (ι →₀ ℕ) → M, ∀ k, P k = (Finsupp.toMultiset k).toList.foldr (fun i h => a i h) f` from `⟨_, fun _ => rfl⟩`. Establish `hP : ∀ k, opPow A k (f : X → ℂ) = (P k : X → ℂ)`. Introduce `k`. Unfold `opPow`. Rewrite using `[hPdef]`.

Conclude with `foldr_coe_eq_coe_foldr M A a hA f _`. Establish `hP0 : P 0 = f`. Rewrite using `[hPdef]`. Simplify using the standard rewrite rules. Establish `hPs : ∀ k v, P (k + Finsupp.single v 1) = a v (P k)`.

Introduce `k v`. Rewrite using `[hPdef, hPdef]`. Establish `hp : ((Finsupp.toMultiset (k + Finsupp.single v 1)).toList).Perm (v :: (Finsupp.toMultiset k).toList)`. Rewrite using `[← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add, Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]`. Rewrite using `[foldr_eq_of_perm_of_comm (fun i h => a i h) (fun i j y => haa i j y) hp]`.

Both sides reduce to the same expression. Establish `hb0 : ∀ k v, k v = 0 → b v (P k) = 0`. Introduce `k`. Use `multiIndex_induction (p := fun k => ∀ v, k v = 0 → b v (P k) = 0) ?_ ?_ k` and prove the remaining obligations. Introduce `v _`.

Rewrite using `[hP0]`. Conclude with `hf v`. Introduce `k w ih v hv`. Establish `hvw : v ≠ w`. Introduce `h`.

Substitute `h` using the available equality. Simplify using `at hv`. Establish `hkv : k v = 0` using `by simpa [Finsupp.single_apply, Ne.symm hvw] using hv`. Rewrite using `[hPs, hba, ih v hkv, map_zero, if_neg hvw, zero_smul, add_zero]`. Establish `hb1 : ∀ k v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k`.

Introduce `k`. Use `multiIndex_induction (p := fun k => ∀ v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k) ?_ ?_ k` and prove the remaining obligations. Introduce `v`. Rewrite using `[hPs 0 v, hba, hP0, hf, map_zero, zero_add, if_pos rfl, one_smul]`. Simplify using the standard rewrite rules.

Introduce `k w ih v`. Rewrite using `[add_right_comm, hPs (k + Finsupp.single v 1) w, hba, ih v, map_smul, ← hPs k w]`. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Rewrite using `[if_pos rfl, ← add_smul, Finsupp.add_apply, Finsupp.single_eq_same]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hvw, zero_smul, add_zero]`. Establish `e : (k + Finsupp.single w 1 : ι →₀ ℕ) v = k v` using `by simp [Finsupp.single_apply, Ne.symm hvw]`.

Rewrite using `[e]`. Establish `hmono : ∀ u c, pureTensorL A (f : X → ℂ) (MvPolynomial.monomial u c) = c • (P u : X → ℂ)`. Introduce `u c`. Rewrite using `[pureTensorL_monomial, hP]`. Establish `hmem : ∀ Q, pureTensorL A (f : X → ℂ) Q ∈ M`.

Introduce `Q`. Proceed by induction on `Q using MvPolynomial.induction_on'`. Name the introduced variables `u c`. Rewrite using `[hmono]`. Conclude with `M.smul_mem c (P u).2`.

Name the introduced variables `p q hp hq`. Rewrite using `[map_add]`. Conclude with `M.add_mem hp hq`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Introduce `ip hadd hsmul hzero hadj1 hadj2 β Q`.

Establish `hip0 : ∀ z, ip 0 z = 0`. Introduce `z`. Establish `h` using `hsmul 0 0 z`. Rewrite `h` using `[zero_smul, zero_mul]`. Then use the resulting hypothesis. Establish `hG : ∀ β α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0`.

Introduce `β`. Use `multiIndex_induction (p := fun β => ∀ α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ β` and prove the remaining obligations. Introduce `α`. Use `multiIndex_induction (p := fun α => ip (P α : X → ℂ) (P 0) = if α = 0 then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ α` and prove the remaining obligations. Simplify using `[hP0, multiFact]`.

Introduce `α v _`. Rewrite using `[hPs, hadj1, hP0, hf]`. Establish `hne : α + Finsupp.single v 1 ≠ 0`. Introduce `h`. Use `congrArg (fun g : ι →₀ ℕ => g v) h` as an intermediate fact.

Simplify using `at this`. Rewrite using `[if_neg hne]`. Simplify using `using hzero _`. Introduce `β v ih α`. Rewrite using `[hPs, hadj2]`.

Distinguish the cases in `hα : α v = 0`. Rewrite using `[hb0 α v hα]`. Establish `hne : α ≠ β + Finsupp.single v 1`. Introduce `h`. Rewrite `hα` using `[h]`.

Simplify using `at hα`. Rewrite using `[if_neg hne]`. Simplify using `using hip0 _`. Choose the witnesses or unpack the hypotheses as in `⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single v 1 := by`. Use `⟨α - Finsupp.single v 1, ?_⟩` and prove the remaining obligations.

Use extensionality with `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Rewrite using `[hb1, Submodule.coe_smul, hsmul, ih α', multiFact_add_single]`. Distinguish the cases in `he : α' = β`. Substitute `he` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : α' + Finsupp.single v 1 ≠ β + Finsupp.single v 1` using `fun h => he (add_right_cancel h)`. Rewrite using `[if_neg he, if_neg hne, mul_zero]`. Rewrite using `[hmono β 1, one_smul]`.

Proceed by induction on `Q using MvPolynomial.induction_on'`. Name the introduced variables `u c`. Rewrite using `[hmono, hsmul, hG, MvPolynomial.coeff_monomial]`. Distinguish the cases in `h : u = β`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Name the introduced variables `p q hp hq`. Rewrite using `[map_add, MvPolynomial.coeff_add, add_mul, ← hp, ← hq]`. Conclude with `hadd ⟨_, hmem p⟩ ⟨_, hmem q⟩ (P β)`.
-/
theorem fock_of_ccr {ι X : Type} (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a b : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g)
    (haa : ∀ i j g, a i (a j g) = a j (a i g))
    (hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g)
    (f : M) (hf : ∀ i, b i f = 0) :
    (∀ Q, pureTensorL A (f : X → ℂ) Q ∈ M) ∧
    ∀ ip : (X → ℂ) → (X → ℂ) → ℂ, (∀ x y z : M, ip (x + y) z = ip x z + ip y z) →
      (∀ (c : ℂ) x z, ip (c • x) z = c * ip x z) → (∀ x, ip x 0 = 0) →
      (∀ i (x y : M), ip (a i x) y = ip x (b i y)) → (∀ i (x y : M), ip x (a i y) = ip (b i x) y) →
      ∀ (β : ι →₀ ℕ) Q, ip (pureTensorL A (f : X → ℂ) Q) (pureTensorL A (f : X → ℂ) (MvPolynomial.monomial β 1)) =
        Q.coeff β * ((multiFact β : ℂ) * ip f f) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : (ι →₀ ℕ) → M,
      ∀ k, P k = (Finsupp.toMultiset k).toList.foldr (fun i h => a i h) f := ⟨_, fun _ => rfl⟩
  have hP : ∀ k, opPow A k (f : X → ℂ) = (P k : X → ℂ) := by
    intro k
    unfold opPow
    rw [hPdef]
    exact foldr_coe_eq_coe_foldr M A a hA f _
  have hP0 : P 0 = f := by
    rw [hPdef]
    simp
  have hPs : ∀ k v, P (k + Finsupp.single v 1) = a v (P k) := by
    intro k v
    rw [hPdef, hPdef]
    have hp : ((Finsupp.toMultiset (k + Finsupp.single v 1)).toList).Perm (v :: (Finsupp.toMultiset k).toList) := by
      rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add,
        Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
    rw [foldr_eq_of_perm_of_comm (fun i h => a i h) (fun i j y => haa i j y) hp]
    rfl
  have hb0 : ∀ k v, k v = 0 → b v (P k) = 0 := by
    intro k
    refine multiIndex_induction (p := fun k => ∀ v, k v = 0 → b v (P k) = 0) ?_ ?_ k
    · intro v _
      rw [hP0]
      exact hf v
    · intro k w ih v hv
      have hvw : v ≠ w := by
        intro h
        subst h
        simp at hv
      have hkv : k v = 0 := by simpa [Finsupp.single_apply, Ne.symm hvw] using hv
      rw [hPs, hba, ih v hkv, map_zero, if_neg hvw, zero_smul, add_zero]
  have hb1 : ∀ k v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k := by
    intro k
    refine multiIndex_induction
      (p := fun k => ∀ v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k) ?_ ?_ k
    · intro v
      rw [hPs 0 v, hba, hP0, hf, map_zero, zero_add, if_pos rfl, one_smul]
      simp
    · intro k w ih v
      rw [add_right_comm, hPs (k + Finsupp.single v 1) w, hba, ih v, map_smul, ← hPs k w]
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos rfl, ← add_smul, Finsupp.add_apply, Finsupp.single_eq_same]
        congr 1
        push_cast
        ring
      · rw [if_neg hvw, zero_smul, add_zero]
        have e : (k + Finsupp.single w 1 : ι →₀ ℕ) v = k v := by simp [Finsupp.single_apply, Ne.symm hvw]
        rw [e]
  have hmono : ∀ u c, pureTensorL A (f : X → ℂ) (MvPolynomial.monomial u c) = c • (P u : X → ℂ) := by
    intro u c
    rw [pureTensorL_monomial, hP]
  have hmem : ∀ Q, pureTensorL A (f : X → ℂ) Q ∈ M := by
    intro Q
    induction Q using MvPolynomial.induction_on'
    · rename_i u c
      rw [hmono]
      exact M.smul_mem c (P u).2
    · rename_i p q hp hq
      rw [map_add]
      exact M.add_mem hp hq
  refine ⟨hmem, ?_⟩
  intro ip hadd hsmul hzero hadj1 hadj2 β Q
  have hip0 : ∀ z, ip 0 z = 0 := by
    intro z
    have h := hsmul 0 0 z
    rwa [zero_smul, zero_mul] at h
  have hG : ∀ β α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0 := by
    intro β
    refine multiIndex_induction
      (p := fun β => ∀ α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ β
    · intro α
      refine multiIndex_induction
        (p := fun α => ip (P α : X → ℂ) (P 0) = if α = 0 then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ α
      · simp [hP0, multiFact]
      · intro α v _
        rw [hPs, hadj1, hP0, hf]
        have hne : α + Finsupp.single v 1 ≠ 0 := by
          intro h
          have := congrArg (fun g : ι →₀ ℕ => g v) h
          simp at this
        rw [if_neg hne]
        simpa using hzero _
    · intro β v ih α
      rw [hPs, hadj2]
      by_cases hα : α v = 0
      · rw [hb0 α v hα]
        have hne : α ≠ β + Finsupp.single v 1 := by
          intro h
          rw [h] at hα
          simp at hα
        rw [if_neg hne]
        simpa using hip0 _
      · obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single v 1 := by
          refine ⟨α - Finsupp.single v 1, ?_⟩
          ext w
          by_cases hw : w = v
          · subst hw
            simp
            omega
          · simp [Finsupp.single_apply, Ne.symm hw]
        rw [hb1, Submodule.coe_smul, hsmul, ih α', multiFact_add_single]
        by_cases he : α' = β
        · subst he
          rw [if_pos rfl, if_pos rfl]
          push_cast
          ring
        · have hne : α' + Finsupp.single v 1 ≠ β + Finsupp.single v 1 := fun h => he (add_right_cancel h)
          rw [if_neg he, if_neg hne, mul_zero]
  rw [hmono β 1, one_smul]
  induction Q using MvPolynomial.induction_on'
  · rename_i u c
    rw [hmono, hsmul, hG, MvPolynomial.coeff_monomial]
    by_cases h : u = β
    · subst h
      simp
    · simp [h]
  · rename_i p q hp hq
    rw [map_add, MvPolynomial.coeff_add, add_mul, ← hp, ← hq]
    exact hadd ⟨_, hmem p⟩ ⟨_, hmem q⟩ (P β)

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def sgnAt (M : DSModel V S) (τ : D.what₂.Tau) (a : Fin V.rank) : ℝ := if M.ε τ a then 1 else -1

/- English proof (translation)
Unfold `sgnAt`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
theorem sgnAt_cases (M : DSModel V S) (τ : D.what₂.Tau) (a : Fin V.rank) : sgnAt M τ a = 1 ∨ sgnAt M τ a = -1 := by
  unfold sgnAt
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Unfold `Formalism.REAL.Jm sgnAt`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jm_eq (M : DSModel V S) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = diagonal fun a => (sgnAt M τ a : ℂ) := by
  unfold Formalism.REAL.Jm sgnAt
  congr 1
  funext a
  split_ifs <;> simp

/- English proof (translation)
Unfold `onb`. Conclude with `Matrix.isUnit_nonsing_inv_det_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))`.
-/
theorem onb_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (onb M τ).det := by
  unfold onb
  exact Matrix.isUnit_nonsing_inv_det_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

/- English proof (translation)
Establish `hu : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)`. Unfold `cart onb`. Rewrite using `[← Jm_eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.
-/
theorem cart_mul_onb (M : DSModel V S) (τ : D.what₂.Tau) :
    cart M τ * onb M τ = onb M τ * diagonal fun a => (sgnAt M τ a : ℂ) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold cart onb
  rw [← Jm_eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

/- English proof (translation)
Establish `hu : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)`. Unfold `onb`. Rewrite using `[← M.fr_gram τ, ← Jm_eq]`. Establish `e : ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹)`. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, Matrix.mul_nonsing_inv _ hu]`. Simplify using the standard rewrite rules.
-/
theorem onb_gram (M : DSModel V S) (τ : D.what₂.Tau) :
    (onb M τ)ᴴ * gramAt D V τ * onb M τ = diagonal fun a => (sgnAt M τ a : ℂ) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold onb
  rw [← M.fr_gram τ, ← Jm_eq]
  have e : ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_nonsing_inv _ hu]
  simp

def uMap (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2

def uSgn (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) : ℝ := sgnAt M' l.1 l.2.1 * sgnAt M l.1 l.2.2

/- English proof (translation)
Unfold `uSgn`. Apply the tactic sequence `rcases sgnAt_cases M' l.1 l.2.1 with h | h <;> rcases sgnAt_cases M l.1 l.2.2 with h' | h' <;>`. Evaluate the numerical expressions using `[h, h']`.
-/
theorem uSgn_cases (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) :
    uSgn M M' l = 1 ∨ uSgn M M' l = -1 := by
  unfold uSgn
  rcases sgnAt_cases M' l.1 l.2.1 with h | h <;> rcases sgnAt_cases M l.1 l.2.2 with h' | h' <;>
    norm_num [h, h']

/- English proof (translation)
Unfold `uMap uSgn`. Rewrite using `[GlobalTheory.FockVecInj.cplxO_unitMap (onb_det M l.1) (cart_mul_onb M l.1) (cart_mul_onb M' l.1)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cplxO_uMap (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) :
    cplxO (cart M l.1) (cart M' l.1) (uMap M M' l) = (I * uSgn M M' l) • uMap M M' l := by
  unfold uMap uSgn
  rw [GlobalTheory.FockVecInj.cplxO_unitMap (onb_det M l.1) (cart_mul_onb M l.1) (cart_mul_onb M' l.1)]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨τ, i, j⟩` from `k`. Take `⟨τ', i', j'⟩` from `l`. Unfold `commScalar`. Distinguish the cases in `hτ : τ = τ'`. Substitute `hτ` using the available equality.

Establish `hε : ∀ (N : Type) [Fintype N] (g : N → ℝ), (∀ a, g a = 1 ∨ g a = -1) → ∀ a, (g a : ℂ) * (g a : ℂ) = 1`. Introduce `N _ g hg a`. Apply the tactic sequence `rcases hg a with h | h <;> simp [h]`. Establish `ht` using `GlobalTheory.FockVecInj.trace_unitMap (hε _ _ (sgnAt_cases M τ)) (onb_gram M τ) (onb_gram M' τ) i j i' j'`. Unfold `symplAt hermAt uMap uSgn`.

Simplify using `only [if_true, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]`. Rewrite using `[ht]`. Distinguish the cases in `hij : i = i' ∧ j = j'`. Take `⟨rfl, rfl⟩` from `hij`. Simplify using `only [and_self, if_true]`.

Use `push_cast`. Simplify using `only [Complex.star_def]`. Put the polynomial expressions in normal form. Establish `hne : (τ, i, j) ≠ (τ, i', j')`. Introduce `he`.

Simplify using `only [Prod.mk.injEq, true_and] at he`. Conclude with `hij he`. Simplify using `[hij, hne]`. Establish `hne : (τ, i, j) ≠ (τ', i', j')`. Introduce `he`.

Simplify using `only [Prod.mk.injEq] at he`. Conclude with `hτ he.1`. Simplify using `[hτ, hne]`.
-/
theorem commScalar_uMap (M : DSModel V S) (M' : DSModel W S') (c c' : ℂ) (k l : FVar D W.rank V.rank) :
    commScalar V W k.1 l.1 (c • uMap M M' k) (c' • uMap M M' l) =
      if k = l then -(2 * Real.pi * I) * ((2 * (tauE D k.1 D.host.xi0 * (c * conj c' * uSgn M M' k)).re : ℝ) : ℂ)
      else 0 := by
  classical
  obtain ⟨τ, i, j⟩ := k
  obtain ⟨τ', i', j'⟩ := l
  unfold commScalar
  by_cases hτ : τ = τ'
  · subst hτ
    have hε : ∀ (N : Type) [Fintype N] (g : N → ℝ), (∀ a, g a = 1 ∨ g a = -1) → ∀ a, (g a : ℂ) * (g a : ℂ) = 1 := by
      intro N _ g hg a
      rcases hg a with h | h <;> simp [h]
    have ht := GlobalTheory.FockVecInj.trace_unitMap (hε _ _ (sgnAt_cases M τ)) (onb_gram M τ) (onb_gram M' τ) i j i' j'
    unfold symplAt hermAt uMap uSgn
    simp only [if_true, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [ht]
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, if_true]
      push_cast
      simp only [Complex.star_def]
      ring_nf
    · have hne : (τ, i, j) ≠ (τ, i', j') := by
        intro he
        simp only [Prod.mk.injEq, true_and] at he
        exact hij he
      simp [hij, hne]
  · have hne : (τ, i, j) ≠ (τ', i', j') := by
      intro he
      simp only [Prod.mk.injEq] at he
      exact hτ he.1
    simp [hτ, hne]

/- English proof (translation)
Establish `hre : (tauE D τ D.host.xi0).re = 0` using `GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ`. Establish `him : 0 < (tauE D τ D.host.xi0).im` using `Formalism.L2.Theta.xi_zero_im_pos D τ`. Establish `hz : tauE D τ D.host.xi0 = ((tauE D τ D.host.xi0).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Establish `hn : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im`.

Rewrite using `[hz]`. Simplify using `[abs_of_pos him]`. Establish `h2 : fockScale D τ * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im`. Unfold `fockScale`. Rewrite using `[hn]`.

Establish `h0 : 0 ≤ 2 * Real.pi * (tauE D τ D.host.xi0).im` using `by positivity`. Establish `hs` using `Real.mul_self_sqrt h0`. Take the linear combination `4 * hs`. Conclude with `h2` after adjusting the coercions.
-/
theorem fockScale_sq (τ : D.what₂.Tau) :
    (fockScale D τ : ℂ) * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
  have hre : (tauE D τ D.host.xi0).re = 0 := GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ
  have him : 0 < (tauE D τ D.host.xi0).im := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hz : tauE D τ D.host.xi0 = ((tauE D τ D.host.xi0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im := by
    rw [hz]
    simp [abs_of_pos him]
  have h2 : fockScale D τ * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
    unfold fockScale
    rw [hn]
    have h0 : 0 ≤ 2 * Real.pi * (tauE D τ D.host.xi0).im := by positivity
    have hs := Real.mul_self_sqrt h0
    linear_combination 4 * hs
  exact_mod_cast h2

/- English proof (translation)
Introduce `h`. Establish `h2` using `fockScale_sq (D := D) τ`. Rewrite `h2` using `[h, zero_mul]`. Establish `him : 0 < (tauE D τ D.host.xi0).im` using `Formalism.L2.Theta.xi_zero_im_pos D τ`. Establish `hp : (0 : ℝ) < 8 * Real.pi * (tauE D τ D.host.xi0).im` using `by positivity`.

Establish `h3 : (8 * Real.pi * (tauE D τ D.host.xi0).im : ℝ) = 0` using `by exact_mod_cast h2.symm`. Conclude with `hp.ne' h3`.
-/
theorem fockScale_ne (τ : D.what₂.Tau) : (fockScale D τ : ℂ) ≠ 0 := by
  intro h
  have h2 := fockScale_sq (D := D) τ
  rw [h, zero_mul] at h2
  have him : 0 < (tauE D τ D.host.xi0).im := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hp : (0 : ℝ) < 8 * Real.pi * (tauE D τ D.host.xi0).im := by positivity
  have h3 : (8 * Real.pi * (tauE D τ D.host.xi0).im : ℝ) = 0 := by exact_mod_cast h2.symm
  exact hp.ne' h3

variable (V W) in

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) : Submodule ℂ (WO V W → ℂ) where
  carrier := {g | IsThetaFunO ψ V W g}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

/- English proof (translation)
Establish `hdR_th : ∀ τ z (g : thetaSub V W ψ), IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g)` using `fun τ z g => (hsk τ z).2.1 _ g.2`. Take `⟨Dop, hDop⟩ : ∃ Dop : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ → Module.End ℂ (thetaSub V W ψ), ∀ p g, (Dop p g : WO V W → ℂ) = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ p.1 p.2 g` from `⟨fun p => { toFun := fun g => ⟨_, hdR_th p.1 p.2 g⟩ map_add' := fun g g' => Subtype.ext (GlobalTheory.Size.dRho_add hψ hθ p.1 p.2 g.2 g'.2) map_smul' := fun c g => Subtype.ext (GlobalTheory.Size.dRho_smul p.1 p.2 c g) }, fun _ _ => rfl⟩`. Establish `hDc : ∀ p q g, Dop p (Dop q g) = Dop q (Dop p g) + commScalar V W p.1 q.1 p.2 q.2 • g`. Introduce `p q g`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h` using `(hco p.1 q.1 p.2 q.2).2 g g.2`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul, hDop]`. Rewrite using `[← h]`. Normalize the expressions using the abelian group laws. Take `⟨a, ha⟩ : ∃ a : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, a k = ((fockScale D k.1 : ℂ)⁻¹) • (Dop (k.1, (1 : ℂ) • uMap M M' k) - I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k))` from `⟨_, fun _ => rfl⟩`.

Take `⟨b, hb⟩ : ∃ b : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, b k = (-((fockScale D k.1 : ℂ)⁻¹)) • (Dop (k.1, (1 : ℂ) • uMap M M' k) + I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k))` from `⟨_, fun _ => rfl⟩`. Establish `hA : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k g = (a k g : WO V W → ℂ)`. Introduce `k g`. Rewrite using `[ha]`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, hDop, one_smul]`.

Rewrite using `[← cplxO_uMap]`. Both sides reduce to the same expression. Establish `hB : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k g = (b k g : WO V W → ℂ)`. Introduce `k g`. Rewrite using `[hb]`.

Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hDop, one_smul]`. Rewrite using `[← cplxO_uMap]`. Both sides reduce to the same expression. Establish `hfb : ∀ k, b k ⟨f, hf.theta⟩ = 0`. Introduce `k`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hB]`. Establish `h` using `hf.vac k.1 (uMap M M' k)`. Unfold `annih at h`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k f = 0`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp annih`. Rewrite using `[show unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2 = uMap M M' k from rfl, h, smul_zero]`. Establish `S1 : ∀ i j : FVar D W.rank V.rank, (fockScale D i.1 : ℂ)⁻¹ * (fockScale D j.1 : ℂ)⁻¹ * (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) - commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) - I * (commScala …`. Introduce `i j`. Simplify using `only [commScalar_uMap]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by`. Use `⟨(tauE D i.1 D.host.xi0).im, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]`.

Simplify using `only [if_true, hy]`. Apply the tactic sequence `rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> simp`. Simplify using `[hij]`. Establish `S2 : ∀ i j : FVar D W.rank V.rank, -(fockScale D i.1 : ℂ)⁻¹ * ((fockScale D j.1 : ℂ)⁻¹ * (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) + commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) + I * (commSca …`. Introduce `i j`.

Simplify using `only [commScalar_uMap]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by`. Use `⟨(tauE D i.1 D.host.xi0).im, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]`. Establish `hF` using `fockScale_sq (D := D) i.1`. Establish `hF0` using `fockScale_ne (D := D) i.1`. Rewrite `hF` using `[hy]`. Simplify using `only [if_true, hy]`.

Apply the tactic sequence `rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> clear * - hF hF0 <;> simp at hF ⊢ <;> field_simp <;>`. Take the linear combination `(-1 : ℂ) * hF + (-8 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_sq`. Simplify using `[hij]`. Establish `haa : ∀ i j g, a i (a j g) = a j (a i g)`. Introduce `i j g`.

Establish `h1` using `(GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i) (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j) ((fockScale D i.1 : ℂ)⁻¹) ((fockScale D j.1 …`. Simplify using `only [S1 i j, zero_smul, add_zero] at h1`. Rewrite using `[ha i, ha j]`. Conclude with `h1`. Establish `hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g`.

Introduce `i j g`. Establish `h2` using `(GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i) (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j) 1 ((fockScale D j.1 : ℂ)⁻¹) g).2`. Rewrite using `[hb i, ha j]`. Simplify using `only [LinearMap.smul_apply] at h2 ⊢`. Rewrite using `[h2, map_smul, ← S2 i j]`.

Use `module`. Establish `hmain` using `fock_of_ccr (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b hA haa (fun i j g => by convert hba i j g) ⟨f, hf.theta⟩ hfb`. Establish `hpt : ∀ P, ptOf ψ θ M M' f P = pureTensorL (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) f P` using `fun _ => rfl`. Use `⟨fun P => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpt]`.

Conclude with `hmain.1 P`. Introduce `l l' g hg`. Rewrite using `[hA l' ⟨g, hg⟩, hA l, hA l ⟨g, hg⟩, hA l', haa]`. Introduce `l l' g hg`. Rewrite using `[hA l' ⟨g, hg⟩, hB l, hB l ⟨g, hg⟩, hA l', hba, Submodule.coe_add, add_sub_cancel_left, Submodule.coe_smul]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `μ 𝓕 hμ h𝓕 α β`. Establish `hadd : ∀ x y z : thetaSub V W ψ, ipO μ 𝓕 ((x : WO V W → ℂ) + y) z = ipO μ 𝓕 x z + ipO μ 𝓕 y z` using `fun x y z => GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 x.2 y.2 z.2`. Establish `hsm : ∀ (c : ℂ) (x z : WO V W → ℂ), ipO μ 𝓕 (c • x) z = c * ipO μ 𝓕 x z` using `fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z`. Establish `hz : ∀ x : WO V W → ℂ, ipO μ 𝓕 x 0 = 0`.

Introduce `x`. Establish `h` using `GlobalTheory.Size.ipO_smul_right μ 𝓕 0 x 0`. Rewrite `h` using `[zero_smul, map_zero, zero_mul]`. Then use the resulting hypothesis. Establish `hskw : ∀ p (x y : thetaSub V W ψ), ipO μ 𝓕 (Dop p x : WO V W → ℂ) y = -ipO μ 𝓕 x (Dop p y)`. Introduce `p x y`.

Rewrite using `[hDop, hDop]`. Conclude with `(hsk p.1 p.2).2.2 μ 𝓕 hμ h𝓕 x y x.2 y.2`. Establish `hsplit : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ), ipO μ 𝓕 ((c • Dop p x + c' • Dop q x : thetaSub V W ψ) : WO V W → ℂ) y = c * ipO μ 𝓕 x (Dop p y) * (-1) + c' * ipO μ 𝓕 x (Dop q y) * (-1)`. Introduce `c c' p q x y`. Rewrite using `[Submodule.coe_add, hadd, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, hskw, hskw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsplit' : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ), ipO μ 𝓕 (x : WO V W → ℂ) ((c • Dop p y + c' • Dop q y : thetaSub V W ψ) : WO V W → ℂ) = conj c * ipO μ 𝓕 x (Dop p y) + conj c' * ipO μ 𝓕 x (Dop q y)`. Introduce `c c' p q x y`. Rewrite using `[Submodule.coe_add, GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 x.2 (c • Dop p y).2 (c' • Dop q y).2, Submodule.coe_smul, Submodule.coe_smul, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right]`. Establish `hcr : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), a k x = ((fockScale D k.1 : ℂ)⁻¹) • Dop (k.1, (1 : ℂ) • uMap M M' k) x + (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x`.

Introduce `k x`. Rewrite using `[ha]`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply]`. Use `module`. Establish `han : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), b k x = (-((fockScale D k.1 : ℂ)⁻¹)) • Dop (k.1, (1 : ℂ) • uMap M M' k) x + (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x`.

Introduce `k x`. Rewrite using `[hb]`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply]`. Use `module`. Establish `hcj : ∀ k : FVar D W.rank V.rank, conj ((fockScale D k.1 : ℂ)⁻¹) = (fockScale D k.1 : ℂ)⁻¹`.

Introduce `k`. Rewrite using `[map_inv₀, Complex.conj_ofReal]`. Establish `hadj1 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (a k x : WO V W → ℂ) y = ipO μ 𝓕 x (b k y)`. Introduce `k x y`. Rewrite using `[hcr, han, hsplit, hsplit']`.

Simplify using `only [map_neg, map_mul, hcj, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `hadj2 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (x : WO V W → ℂ) (a k y) = ipO μ 𝓕 (b k x) y`. Introduce `k x y`. Rewrite using `[hcr, han, hsplit, hsplit']`.

Simplify using `only [map_neg, map_mul, hcj, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpt, hpt, hmain.2 (ipO μ 𝓕) hadd hsm hz hadj1 hadj2 β (MvPolynomial.monomial α 1), MvPolynomial.coeff_monomial]`. Distinguish the cases in `h : α = β`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hinj` using `GlobalTheory.FockVecInj.injective_of_canonicalCommutation (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b (fun _ => (1 : ℂ)) hA haa (fun i j g => by convert hba i j g) (fun _ => one_ne_zero) ⟨f, hf.theta⟩ hfb (fun h => hf …`. Introduce `P Q hPQ`. Conclude with `hinj hPQ`.
-/
theorem fockLaws {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hsk : DerSkew ψ θ V W) (hco : DerComm ψ θ V W) (M : DSModel V S) (M' : DSModel W S') {f : WO V W → ℂ}
    (hf : IsVacVec ψ θ M M' f) : FockLaws ψ θ M M' f := by
  classical
  have hdR_th : ∀ τ z (g : thetaSub V W ψ), IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) :=
    fun τ z g => (hsk τ z).2.1 _ g.2
  obtain ⟨Dop, hDop⟩ : ∃ Dop : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ → Module.End ℂ (thetaSub V W ψ),
      ∀ p g, (Dop p g : WO V W → ℂ) = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ p.1 p.2 g :=
    ⟨fun p =>
      { toFun := fun g => ⟨_, hdR_th p.1 p.2 g⟩
        map_add' := fun g g' => Subtype.ext (GlobalTheory.Size.dRho_add hψ hθ p.1 p.2 g.2 g'.2)
        map_smul' := fun c g => Subtype.ext (GlobalTheory.Size.dRho_smul p.1 p.2 c g) }, fun _ _ => rfl⟩
  have hDc : ∀ p q g, Dop p (Dop q g) = Dop q (Dop p g) + commScalar V W p.1 q.1 p.2 q.2 • g := by
    intro p q g
    apply Subtype.ext
    have h := (hco p.1 q.1 p.2 q.2).2 g g.2
    simp only [Submodule.coe_add, Submodule.coe_smul, hDop]
    rw [← h]
    abel
  obtain ⟨a, ha⟩ : ∃ a : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, a k =
      ((fockScale D k.1 : ℂ)⁻¹) • (Dop (k.1, (1 : ℂ) • uMap M M' k) -
        I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k)) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, b k =
      (-((fockScale D k.1 : ℂ)⁻¹)) • (Dop (k.1, (1 : ℂ) • uMap M M' k) +
        I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k)) := ⟨_, fun _ => rfl⟩
  have hA : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k g = (a k g : WO V W → ℂ) := by
    intro k g
    rw [ha]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, hDop, one_smul]
    rw [← cplxO_uMap]
    rfl
  have hB : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k g = (b k g : WO V W → ℂ) := by
    intro k g
    rw [hb]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hDop, one_smul]
    rw [← cplxO_uMap]
    rfl
  have hfb : ∀ k, b k ⟨f, hf.theta⟩ = 0 := by
    intro k
    apply Subtype.ext
    rw [← hB]
    have h := hf.vac k.1 (uMap M M' k)
    unfold annih at h
    show GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k f = 0
    unfold GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp annih
    rw [show unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2 = uMap M M' k from rfl, h, smul_zero]
  have S1 : ∀ i j : FVar D W.rank V.rank, (fockScale D i.1 : ℂ)⁻¹ * (fockScale D j.1 : ℂ)⁻¹ *
      (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) -
        commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) -
        I * (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) +
          commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((1 : ℂ) • uMap M M' j))) = 0 := by
    intro i j
    simp only [commScalar_uMap]
    by_cases hij : i = j
    · subst hij
      obtain ⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by
        refine ⟨(tauE D i.1 D.host.xi0).im, ?_⟩
        apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]
      simp only [if_true, hy]
      rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> simp
    · simp [hij]
  have S2 : ∀ i j : FVar D W.rank V.rank, -(fockScale D i.1 : ℂ)⁻¹ * ((fockScale D j.1 : ℂ)⁻¹ *
      (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) +
        commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) +
        I * (commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((1 : ℂ) • uMap M M' j) -
          commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j)))) =
      if i = j then 1 else 0 := by
    intro i j
    simp only [commScalar_uMap]
    by_cases hij : i = j
    · subst hij
      obtain ⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by
        refine ⟨(tauE D i.1 D.host.xi0).im, ?_⟩
        apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]
      have hF := fockScale_sq (D := D) i.1
      have hF0 := fockScale_ne (D := D) i.1
      rw [hy] at hF
      simp only [if_true, hy]
      rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> clear * - hF hF0 <;> simp at hF ⊢ <;> field_simp <;>
        linear_combination (-1 : ℂ) * hF + (-8 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_sq
    · simp [hij]
  have haa : ∀ i j g, a i (a j g) = a j (a i g) := by
    intro i j g
    have h1 := (GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc
      (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i)
      (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j)
      ((fockScale D i.1 : ℂ)⁻¹) ((fockScale D j.1 : ℂ)⁻¹) g).1
    simp only [S1 i j, zero_smul, add_zero] at h1
    rw [ha i, ha j]
    exact h1
  have hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g := by
    intro i j g
    have h2 := (GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc
      (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i)
      (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j)
      1 ((fockScale D j.1 : ℂ)⁻¹) g).2
    rw [hb i, ha j]
    simp only [LinearMap.smul_apply] at h2 ⊢
    rw [h2, map_smul, ← S2 i j]
    module
  have hmain := fock_of_ccr (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b hA haa
    (fun i j g => by convert hba i j g)
    ⟨f, hf.theta⟩ hfb
  have hpt : ∀ P, ptOf ψ θ M M' f P = pureTensorL (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) f P := fun _ => rfl
  refine ⟨fun P => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpt]
    exact hmain.1 P
  · intro l l' g hg
    rw [hA l' ⟨g, hg⟩, hA l, hA l ⟨g, hg⟩, hA l', haa]
  · intro l l' g hg
    rw [hA l' ⟨g, hg⟩, hB l, hB l ⟨g, hg⟩, hA l', hba, Submodule.coe_add, add_sub_cancel_left, Submodule.coe_smul]
    split_ifs <;> simp
  · intro μ 𝓕 hμ h𝓕 α β
    have hadd : ∀ x y z : thetaSub V W ψ, ipO μ 𝓕 ((x : WO V W → ℂ) + y) z = ipO μ 𝓕 x z + ipO μ 𝓕 y z :=
      fun x y z => GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 x.2 y.2 z.2
    have hsm : ∀ (c : ℂ) (x z : WO V W → ℂ), ipO μ 𝓕 (c • x) z = c * ipO μ 𝓕 x z :=
      fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z
    have hz : ∀ x : WO V W → ℂ, ipO μ 𝓕 x 0 = 0 := by
      intro x
      have h := GlobalTheory.Size.ipO_smul_right μ 𝓕 0 x 0
      rwa [zero_smul, map_zero, zero_mul] at h
    have hskw : ∀ p (x y : thetaSub V W ψ), ipO μ 𝓕 (Dop p x : WO V W → ℂ) y = -ipO μ 𝓕 x (Dop p y) := by
      intro p x y
      rw [hDop, hDop]
      exact (hsk p.1 p.2).2.2 μ 𝓕 hμ h𝓕 x y x.2 y.2
    have hsplit : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ),
        ipO μ 𝓕 ((c • Dop p x + c' • Dop q x : thetaSub V W ψ) : WO V W → ℂ) y =
          c * ipO μ 𝓕 x (Dop p y) * (-1) + c' * ipO μ 𝓕 x (Dop q y) * (-1) := by
      intro c c' p q x y
      rw [Submodule.coe_add, hadd, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, hskw, hskw]
      ring
    have hsplit' : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ),
        ipO μ 𝓕 (x : WO V W → ℂ) ((c • Dop p y + c' • Dop q y : thetaSub V W ψ) : WO V W → ℂ) =
          conj c * ipO μ 𝓕 x (Dop p y) + conj c' * ipO μ 𝓕 x (Dop q y) := by
      intro c c' p q x y
      rw [Submodule.coe_add, GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 x.2 (c • Dop p y).2 (c' • Dop q y).2,
        Submodule.coe_smul, Submodule.coe_smul, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right]
    have hcr : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), a k x = ((fockScale D k.1 : ℂ)⁻¹) • Dop (k.1, (1 : ℂ) • uMap M M' k) x +
        (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x := by
      intro k x
      rw [ha]
      simp only [LinearMap.smul_apply, LinearMap.sub_apply]
      module
    have han : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), b k x = (-((fockScale D k.1 : ℂ)⁻¹)) • Dop (k.1, (1 : ℂ) • uMap M M' k) x +
        (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x := by
      intro k x
      rw [hb]
      simp only [LinearMap.smul_apply, LinearMap.add_apply]
      module
    have hcj : ∀ k : FVar D W.rank V.rank, conj ((fockScale D k.1 : ℂ)⁻¹) = (fockScale D k.1 : ℂ)⁻¹ := by
      intro k
      rw [map_inv₀, Complex.conj_ofReal]
    have hadj1 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (a k x : WO V W → ℂ) y = ipO μ 𝓕 x (b k y) := by
      intro k x y
      rw [hcr, han, hsplit, hsplit']
      simp only [map_neg, map_mul, hcj, Complex.conj_I]
      ring
    have hadj2 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (x : WO V W → ℂ) (a k y) = ipO μ 𝓕 (b k x) y := by
      intro k x y
      rw [hcr, han, hsplit, hsplit']
      simp only [map_neg, map_mul, hcj, Complex.conj_I]
      ring
    rw [hpt, hpt, hmain.2 (ipO μ 𝓕) hadd hsm hz hadj1 hadj2 β (MvPolynomial.monomial α 1),
      MvPolynomial.coeff_monomial]
    by_cases h : α = β
    · subst h
      simp
    · simp [h]
  · have hinj := GlobalTheory.FockVecInj.injective_of_canonicalCommutation (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b
      (fun _ => (1 : ℂ)) hA haa (fun i j g => by convert hba i j g) (fun _ => one_ne_zero) ⟨f, hf.theta⟩ hfb
      (fun h => hf.ne (congrArg Subtype.val h))
    intro P Q hPQ
    exact hinj hPQ

/- English proof (translation)
Introduce `V W S S' M M' ψ θ hψ hθ f hf`. Take `⟨-, hV⟩` from `h V W`. Take `⟨-, -, hD⟩` from `hV ψ hψ`. Conclude with `fockLaws hψ hθ (hD θ hθ).1 (hD θ hθ).2.1 M M' hf`.
-/
theorem vacuumFock_of_thetaSquareIntegrable (D : D7) (h : ThetaSquareIntegrable D) : VacuumFock D := by
  intro V W S S' M M' ψ θ hψ hθ f hf
  obtain ⟨-, hV⟩ := h V W
  obtain ⟨-, -, hD⟩ := hV ψ hψ
  exact fockLaws hψ hθ (hD θ hθ).1 (hD θ hθ).2.1 M M' hf

end GlobalTheory.VacuumFockLaws

end
