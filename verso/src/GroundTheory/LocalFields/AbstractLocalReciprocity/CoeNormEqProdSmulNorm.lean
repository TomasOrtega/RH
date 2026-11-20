import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.NormFormula
import GroundTheory.LocalFields.AbstractLocalReciprocity.Reciprocity

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

/- English proof (translation)
Use `set Q := K ⊓ d.ker with hQ`. Establish `hQK : Q ≤ K` using `inf_le_left`. Set `incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K` to `Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by`. Rewrite `h`, the goal using `[QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]`. Establish `hq : ((q⁻¹ * q' : Q) : G) ∈ Q` using `(q⁻¹ * q').2`.

Simplify using `using (hJ _ hq).2 h`. Set `φK : K` to `⟨φ, hφK⟩`. Set `F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K` to `fun p => (φK ^ (p.1 : ℕ)) • incl p.2`. Establish `hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) = ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K)` using `fun _ _ => rfl`. Establish `hdeg : ∀ (m : ℤ) (q : G), q ∈ Q → Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂)`.

Introduce `m q hq`. Rewrite using `[map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hF : Function.Bijective F`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ν, x⟩ ⟨μ, y⟩ hxy`. Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H q`. Proceed by induction on `y using QuotientGroup.induction_on with`.

Consider the case `H q'`. Rewrite `hxy` using `[hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy`. Establish `hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) = (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q')`. Rewrite using `[zpow_sub, zpow_natCast, zpow_natCast]`.

Use `group`. Establish `hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) = ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂)`. Rewrite using `[map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]`. Conclude with `hdeg _ _ q'.2`. Establish `hmem` using `hdS _ hxy`.

Rewrite `hmem` using `[hx, hdq]`. Establish `hdvd` using `(intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem`. Move the coercions through the operations in `at hdvd`. Establish `hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν` using `(mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd`. Establish `hνμ : ν = μ`.

Establish `hμ` using `μ.2`. Establish `hν` using `ν.2`. Establish `h0 : ((μ : ℤ) - ν) = 0` using `Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)`. Conclude with `Fin.ext (by omega)`. Substitute `hνμ` using the available equality.

Establish `hqq : (q : G)⁻¹ * q' ∈ S` using `by simpa [mul_assoc] using hxy`. Establish `hqQ : (q : G)⁻¹ * q' ∈ Q` using `Q.mul_mem (Q.inv_mem q.2) q'.2`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using (hJ _ hqQ).1 hqq`.

Introduce `y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H k`. Take `⟨w, hw⟩` from `mem_multiples.1 (hdK k k.2)`. Use `set N : ℕ+ := ⟨n, hn⟩ with hNdef`.

Use `set ν : ℕ := (proj N w).val with hνdef`. Establish `hνn : ν < n` using `ZMod.val_lt _`. Establish `hw' : w - (ν : ℤ̂) ∈ multiples n`. Use `(proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by` as an intermediate fact. Rewrite using `[map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])`.

Simplify `this` using `[hNdef]`. Take `⟨z, hz⟩` from `mem_multiples.1 hw'`. Establish `hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f)`. Rewrite using `[map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]`. Use `mem_multiples.2 ⟨z, ?_⟩` and prove the remaining obligations.

Establish `: w = (ν : ℤ̂) + n • z` using `by rw [← hz]; ring`. Rewrite using `[this]`. Simplify using `only [nsmul_eq_mul, zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨s, hs, hds⟩` from `hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk`. Use `set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef`. Establish `hqQ : q ∈ Q`. Use `⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩` and prove the remaining obligations. Use `show d q = 1`.

Rewrite using `[hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]`. Use `⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩` and prove the remaining obligations. Rewrite using `[hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]`. Establish `: ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s`.

Rewrite using `[zpow_neg, zpow_natCast]`. Use `group`. Rewrite using `[this]`. Conclude with `hs`. Rewrite using `[coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]`.

Set `_` to `Fintype.ofFinite (Q ⧸ J.subgroupOf Q)`. Rewrite using `[finprod_eq_prod_of_fintype, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations.

Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H q`. Rewrite using `[Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]`. Both sides reduce to the same expression.
-/
theorem coe_norm_eq_prod_smul_norm (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl

namespace ClassFieldData

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in

instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance

omit [TotallyDisconnectedSpace G] in

/- English proof (translation)
Take `⟨y, hy⟩` from `(D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩`. Use `mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, toAdd_pow]`.
-/
theorem toAdd_deg_mem_multiples (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

/- English proof (translation)
Establish `hmap` using `map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s.mem) s.deg_eq (L := (L : Subgroup G))`. Use `coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) (fun x hx => s.field_le hLK hx) ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _` and prove the remaining obligations. Introduce `x hx`. Establish `: D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[hmap]`.

Conclude with `this`. Introduce `k _ hk`. Establish `: D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K))` using `hk`. Rewrite `this` using `[← hmap]`. Take `⟨x, hx, hxk⟩` from `this`.

Conclude with `⟨x, hx, hxk⟩`. Introduce `q hq`. Prove the components needed by the constructor for the conclusion. Introduce `hqS`. Establish `: q ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker` using `⟨hqS, hq.2⟩`.

Rewrite `this` using `[s.field_inf_ker hLK]`. Conclude with `this`. Introduce `hqJ`. Conclude with `le_frobeniusClosure hqJ`.
-/
theorem coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by
  have hmap := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s.mem)
    s.deg_eq (L := (L : Subgroup G))
  refine coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    (fun x hx => s.field_le hLK hx) ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap] at this
    exact this
  · intro k _ hk
    have : D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K)) := hk
    rw [← hmap] at this
    obtain ⟨x, hx, hxk⟩ := this
    exact ⟨x, hx, hxk⟩
  · intro q hq
    constructor
    · intro hqS
      have : q ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker := ⟨hqS, hq.2⟩
      rw [s.field_inf_ker hLK] at this
      exact this
    · intro hqJ
      exact le_frobeniusClosure hqJ

end ClassFieldData

end GroundTheory.LocalField.Abstract
