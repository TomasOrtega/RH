import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Triangular

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

open Classical in

noncomputable def hcProjLin : U n →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  pbw.constr ℂ fun m => if IsDiagExp m then monomial (diagExp m) 1 else 0

/- English proof (translation)
Rewrite using `[hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_pos h]`.
-/
theorem hcProjLin_canon_of_isDiagExp {m : Fin n × Fin n →₀ ℕ} (h : IsDiagExp m) :
    hcProjLin (canon m) = monomial (diagExp m) 1 := by
  rw [hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_pos h]

/- English proof (translation)
Rewrite using `[hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_neg h]`.
-/
theorem hcProjLin_canon_of_not {m : Fin n × Fin n →₀ ℕ} (h : ¬ IsDiagExp m) :
    hcProjLin (canon m) = 0 := by
  rw [hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_neg h]

/- English proof (translation)
Establish `hz : ∀ a, ¬ IsDiag a → m a = 0` using `fun a ha => by`. Assume the negation of the conclusion as `h'`. Conclude with `ha (h a h')`. Rewrite using `[canon_eq_triangular, blockW_eq_nil (l := lowL n) (fun a ha => hz a (not_lower_of_diag.mt (not_not.2 (mem_lowL.1 ha)) |> fun h' => fun hd => h' hd)), blockW_eq_nil (l := upL n) (fun a ha => hz a fun hd => not_upper_of_diag hd (mem_upL.1 ha))]`. Simplify using the standard rewrite rules.
-/
theorem canon_of_isDiagExp {m : Fin n × Fin n →₀ ℕ} (h : IsDiagExp m) :
    canon m = hcEmb (monomial (diagExp m) 1) := by
  have hz : ∀ a, ¬ IsDiag a → m a = 0 := fun a ha => by
    by_contra h'; exact ha (h a h')
  rw [canon_eq_triangular, blockW_eq_nil (l := lowL n) (fun a ha => hz a
      (not_lower_of_diag.mt (not_not.2 (mem_lowL.1 ha)) |> fun h' => fun hd => h' hd)),
    blockW_eq_nil (l := upL n) (fun a ha => hz a fun hd => not_upper_of_diag hd (mem_upL.1 ha))]
  simp

noncomputable def diagEmbExp (μ : Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.mapDomain (fun i => (i, i)) μ

/- English proof (translation)
Introduce `_ _ h` and use `congrArg Prod.fst h`.
-/
theorem diagEmbExp_injective : Function.Injective (fun i : Fin n => (i, i)) :=
  fun _ _ h => congrArg Prod.fst h

/- English proof (translation)
Introduce `a ha`. Assume the negation of the conclusion as `hd`. Apply `ha` to reduce the goal to its premises. Rewrite using `[diagEmbExp, Finsupp.mapDomain_of_notMem_range]`. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `hd rfl`.
-/
theorem isDiagExp_diagEmbExp (μ : Fin n →₀ ℕ) : IsDiagExp (diagEmbExp μ) := by
  intro a ha
  by_contra hd
  apply ha
  rw [diagEmbExp, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨i, rfl⟩
  exact hd rfl

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[diagExp_apply, diagEmbExp, Finsupp.mapDomain_apply diagEmbExp_injective]`.
-/
theorem diagExp_diagEmbExp (μ : Fin n →₀ ℕ) : diagExp (diagEmbExp μ) = μ := by
  ext i
  rw [diagExp_apply, diagEmbExp, Finsupp.mapDomain_apply diagEmbExp_injective]

/- English proof (translation)
Rewrite using `[canon_of_isDiagExp (isDiagExp_diagEmbExp μ), diagExp_diagEmbExp]`.
-/
theorem hcEmb_monomial_one (μ : Fin n →₀ ℕ) : hcEmb (monomial μ 1) = canon (diagEmbExp μ) := by
  rw [canon_of_isDiagExp (isDiagExp_diagEmbExp μ), diagExp_diagEmbExp]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial μ c`. Rewrite using `[show monomial μ c = c • monomial μ (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, hcEmb_monomial_one, hcProjLin_canon_of_isDiagExp (isDiagExp_diagEmbExp μ), diagExp_diagEmbExp]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.
-/
theorem hcProjLin_hcEmb (p : MvPolynomial (Fin n) ℂ) : hcProjLin (hcEmb p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [show monomial μ c = c • monomial μ (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, map_smul, hcEmb_monomial_one, hcProjLin_canon_of_isDiagExp (isDiagExp_diagEmbExp μ),
      diagExp_diagEmbExp]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective hcProjLin_hcEmb`.
-/
theorem hcEmb_injective : Function.Injective (hcEmb (n := n)) :=
  Function.LeftInverse.injective hcProjLin_hcEmb

/- English proof (translation)
Establish `hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x}` using `nPlusU_le_spanUpper hx`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`.

Conclude with `hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hm)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [map_smul, hx, smul_zero]`.
-/
theorem hcProjLin_eq_zero_of_mem_nPlusU {x : U n} (hx : x ∈ nPlusU n) : hcProjLin x = 0 := by
  have hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x} :=
    nPlusU_le_spanUpper hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/- English proof (translation)
Establish `hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasLower m ∧ canon m = x}` using `nMinusU_le_spanLower hx`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`.

Conclude with `hcProjLin_canon_of_not (not_isDiagExp_of_hasLower hm)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [map_smul, hx, smul_zero]`.
-/
theorem hcProjLin_eq_zero_of_mem_nMinusU {x : U n} (hx : x ∈ nMinusU n) : hcProjLin x = 0 := by
  have hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasLower m ∧ canon m = x} :=
    nMinusU_le_spanLower hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact hcProjLin_canon_of_not (not_isDiagExp_of_hasLower hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add, hcProjLin_eq_zero_of_mem_nMinusU hy, hcProjLin_eq_zero_of_mem_nPlusU hz, add_zero]`.
-/
theorem hcProjLin_eq_zero_of_mem_sup {x : U n} (hx : x ∈ nMinusU n ⊔ nPlusU n) :
    hcProjLin x = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hcProjLin_eq_zero_of_mem_nMinusU hy, hcProjLin_eq_zero_of_mem_nPlusU hz, add_zero]

/- English proof (translation)
Set `φ : U n →ₗ[ℂ] U n` to `LinearMap.id - hcEmb.toLinearMap ∘ₗ hcProjLin`. Establish `hφ : ∀ u, φ u = u - hcEmb (hcProjLin u)` using `fun _ => rfl`. It suffices to establish `⊤ ≤ (nMinusU n ⊔ nPlusU n).comap φ by`. Use `this (Submodule.mem_top (x := u))` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, hφ]`. Then use the resulting hypothesis.

Rewrite using `[← span_canon_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, hφ]`. Break down `isDiagExp_or m with h | h | h` into its components or cases. Rewrite using `[hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]`.

Conclude with `Submodule.zero_mem _`. Rewrite using `[hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]`. Conclude with `Submodule.mem_sup_right (canon_mem_nPlusU h)`. Rewrite using `[hcProjLin_canon_of_not (not_isDiagExp_of_hasLower h), map_zero, sub_zero]`. Conclude with `Submodule.mem_sup_left (canon_mem_nMinusU h)`.
-/
theorem sub_hcEmb_mem (u : U n) : u - hcEmb (hcProjLin u) ∈ nMinusU n ⊔ nPlusU n := by
  let φ : U n →ₗ[ℂ] U n := LinearMap.id - hcEmb.toLinearMap ∘ₗ hcProjLin
  have hφ : ∀ u, φ u = u - hcEmb (hcProjLin u) := fun _ => rfl
  suffices ⊤ ≤ (nMinusU n ⊔ nPlusU n).comap φ by
    have := this (Submodule.mem_top (x := u))
    rwa [Submodule.mem_comap, hφ] at this
  rw [← span_canon_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hφ]
  rcases isDiagExp_or m with h | h | h
  · rw [hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]
    exact Submodule.zero_mem _
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]
    exact Submodule.mem_sup_right (canon_mem_nPlusU h)
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasLower h), map_zero, sub_zero]
    exact Submodule.mem_sup_left (canon_mem_nMinusU h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `sub_hcEmb_mem u`. Introduce `h`. Use `hcProjLin_eq_zero_of_mem_sup h` as an intermediate fact.

Rewrite `this` using `[map_sub, hcProjLin_hcEmb, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem hcProjLin_eq_iff (u : U n) (p : MvPolynomial (Fin n) ℂ) :
    hcProjLin u = p ↔ u - hcEmb p ∈ nMinusU n ⊔ nPlusU n := by
  constructor
  · rintro rfl; exact sub_hcEmb_mem u
  · intro h
    have := hcProjLin_eq_zero_of_mem_sup h
    rwa [map_sub, hcProjLin_hcEmb, sub_eq_zero] at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `x ⟨p, rfl⟩ hx`. Use `hcProjLin_eq_zero_of_mem_sup hx` as an intermediate fact. Rewrite `this` using `[AlgHom.toLinearMap_apply, hcProjLin_hcEmb]`.

Simplify using `[this]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `u _`. Rewrite using `[← sub_add_cancel u (hcEmb (hcProjLin u)), add_comm]`. Conclude with `Submodule.add_mem_sup ⟨_, rfl⟩ (sub_hcEmb_mem u)`.
-/
theorem isCompl_range_hcEmb :
    IsCompl (LinearMap.range (hcEmb (n := n)).toLinearMap) (nMinusU n ⊔ nPlusU n) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨p, rfl⟩ hx
    have := hcProjLin_eq_zero_of_mem_sup hx
    rw [AlgHom.toLinearMap_apply, hcProjLin_hcEmb] at this
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    intro u _
    rw [← sub_add_cancel u (hcEmb (hcProjLin u)), add_comm]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ (sub_hcEmb_mem u)

/- English proof (translation)
Simplify using `only [rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem sum_mul_rootAt (a : Fin n × Fin n) :
    ∑ k : Fin n, (k : ℤ) * rootAt a k = (a.1 : ℤ) - a.2 := by
  simp only [rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Simplify using `only [wt, Finsupp.sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_mul_rootAt, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem sum_mul_wt (m : Fin n × Fin n →₀ ℕ) :
    ∑ k : Fin n, (k : ℤ) * wt m k = m.sum fun a c => (c : ℤ) * ((a.1 : ℤ) - a.2) := by
  simp only [wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_mul_rootAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Establish `h0 : ∑ k : Fin n, (k : ℤ) * wt m k = 0` using `by simp [hw]`. Rewrite `h0` using `[sum_mul_wt, Finsupp.sum]`. Take `⟨a, ha, hma⟩` from `hl`. Establish `hnonneg : ∀ b ∈ m.support, 0 ≤ (m b : ℤ) * ((b.1 : ℤ) - b.2)`.

Introduce `b hb`. Use `mul_nonneg (by positivity) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hneg`. Apply `hu` to reduce the goal to its premises. Use `⟨b, ?_, Finsupp.mem_support_iff.1 hb⟩` and prove the remaining obligations.

Simplify using `only [IsUpper]`. Establish `: (b.1 : ℤ) < b.2` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hpos : 0 < (m a : ℤ) * ((a.1 : ℤ) - a.2)`. Use `mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hma) ?_` and prove the remaining obligations.

Simplify using `only [IsLower] at ha`. Establish `: (a.2 : ℤ) < a.1` using `by exact_mod_cast ha`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Finset.sum_pos' hnonneg ⟨a, Finsupp.mem_support_iff.2 hma, hpos⟩` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hasUpper_of_wt_eq_zero {m : Fin n × Fin n →₀ ℕ} (hw : ∀ k, wt m k = 0) (hl : HasLower m) :
    HasUpper m := by
  by_contra hu
  have h0 : ∑ k : Fin n, (k : ℤ) * wt m k = 0 := by simp [hw]
  rw [sum_mul_wt, Finsupp.sum] at h0
  obtain ⟨a, ha, hma⟩ := hl
  have hnonneg : ∀ b ∈ m.support, 0 ≤ (m b : ℤ) * ((b.1 : ℤ) - b.2) := by
    intro b hb
    refine mul_nonneg (by positivity) ?_
    by_contra hneg
    apply hu
    refine ⟨b, ?_, Finsupp.mem_support_iff.1 hb⟩
    simp only [IsUpper]
    have : (b.1 : ℤ) < b.2 := by linarith
    exact_mod_cast this
  have hpos : 0 < (m a : ℤ) * ((a.1 : ℤ) - a.2) := by
    refine mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hma) ?_
    simp only [IsLower] at ha
    have : (a.2 : ℤ) < a.1 := by exact_mod_cast ha
    linarith
  have := Finset.sum_pos' hnonneg ⟨a, Finsupp.mem_support_iff.2 hma, hpos⟩
  linarith

/- English proof (translation)
Use `set s := (pbw.repr z).support`. Use `set c := fun m => pbw.repr z m`. Establish `hzs : z = ∑ m ∈ s, c m • canon m` using `(sum_repr_canon z).symm`. Establish `hwt : ∀ m ∈ s, ∀ k, wt m k = 0`. Introduce `m hm k`.

Establish `h0 : ∑ m ∈ s, (c m * (wt m k : ℂ)) • canon m = 0`. Use `sub_eq_zero.2 (hz k)` as an intermediate fact. Rewrite `this` using `[hzs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul]`. Use `linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm` as an intermediate fact. Establish `hc : c m ≠ 0` using `Finsupp.mem_support_iff.1 hm`. Conclude with `(mul_eq_zero.1 this).resolve_left hc` after adjusting the coercions. Rewrite using `[hzs, map_sum, map_sum, ← Finset.sum_sub_distrib]`.

Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, ← smul_sub]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Break down `isDiagExp_or m with h | h | h` into its components or cases. Rewrite using `[hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]`.

Conclude with `Submodule.zero_mem _`. Rewrite using `[hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]`. Conclude with `canon_mem_nPlusU h`. Establish `hu` using `hasUpper_of_wt_eq_zero (hwt m hm) h`. Rewrite using `[hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hu), map_zero, sub_zero]`.

Conclude with `canon_mem_nPlusU hu`.
-/
theorem sub_hcEmb_mem_nPlusU {z : U n} (hz : ∀ k, e (k, k) * z = z * e (k, k)) :
    z - hcEmb (hcProjLin z) ∈ nPlusU n := by
  set s := (pbw.repr z).support
  set c := fun m => pbw.repr z m
  have hzs : z = ∑ m ∈ s, c m • canon m := (sum_repr_canon z).symm
  have hwt : ∀ m ∈ s, ∀ k, wt m k = 0 := by
    intro m hm k
    have h0 : ∑ m ∈ s, (c m * (wt m k : ℂ)) • canon m = 0 := by
      have := sub_eq_zero.2 (hz k)
      rw [hzs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at this
      rw [← this]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul]
    have := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
    have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
    exact_mod_cast (mul_eq_zero.1 this).resolve_left hc
  rw [hzs, map_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [map_smul, map_smul, ← smul_sub]
  refine Submodule.smul_mem _ _ ?_
  rcases isDiagExp_or m with h | h | h
  · rw [hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]
    exact Submodule.zero_mem _
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]
    exact canon_mem_nPlusU h
  · have hu := hasUpper_of_wt_eq_zero (hwt m hm) h
    rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hu), map_zero, sub_zero]
    exact canon_mem_nPlusU hu

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, a, ha, rfl⟩` from `hx`. Establish `h` using `e_diag_mul_sub k a`. Establish `: u * e a * e (k, k) = (u * e (k, k)) * e a - (rootAt a k : ℂ) • (u * e a)`.

Rewrite using `[mul_assoc, mul_assoc, ← mul_smul_comm, ← mul_sub, ← h]`. Use `noncomm_ring`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.subset_span ⟨_, a, ha, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, a, ha, rfl⟩))`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem mul_e_diag_mem_nPlusU {x : U n} (hx : x ∈ nPlusU n) (k : Fin n) :
    x * e (k, k) ∈ nPlusU n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, a, ha, rfl⟩ := hx
    have h := e_diag_mul_sub k a
    have : u * e a * e (k, k) = (u * e (k, k)) * e a - (rootAt a k : ℂ) • (u * e a) := by
      rw [mul_assoc, mul_assoc, ← mul_smul_comm, ← mul_sub, ← h]; noncomm_ring
    rw [this]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, a, ha, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, a, ha, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Set `S : Subalgebra ℂ (U n)` to `{ carrier := {y | ∀ x ∈ nPlusU n, x * y ∈ nPlusU n} mul_mem' := fun {a b} ha hb x hx => by rw [← mul_assoc]; exact hb _ (ha x hx) add_mem' := fun {a b} ha hb x hx => by rw [mul_add]; exact Submodule.add_mem _ (ha x hx) (hb x hx) algebraMap_mem' := fun r x hx => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]`. Conclude with `Submodule.smul_mem _ r hx }`. Establish `: cartanSub n ≤ S`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩ x hx`. Conclude with `mul_e_diag_mem_nPlusU hx k`. Conclude with `this hy x hx`.
-/
theorem mul_mem_nPlusU_of_mem_cartanSub {x y : U n} (hx : x ∈ nPlusU n) (hy : y ∈ cartanSub n) :
    x * y ∈ nPlusU n := by
  let S : Subalgebra ℂ (U n) :=
    { carrier := {y | ∀ x ∈ nPlusU n, x * y ∈ nPlusU n}
      mul_mem' := fun {a b} ha hb x hx => by rw [← mul_assoc]; exact hb _ (ha x hx)
      add_mem' := fun {a b} ha hb x hx => by rw [mul_add]; exact Submodule.add_mem _ (ha x hx) (hb x hx)
      algebraMap_mem' := fun r x hx => by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]; exact Submodule.smul_mem _ r hx }
  have : cartanSub n ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩ x hx
    exact mul_e_diag_mem_nPlusU hx k
  exact this hy x hx

abbrev centralizerT (n : ℕ) : Subalgebra ℂ (U n) := Subalgebra.centralizer ℂ (cartanSet n)

/- English proof (translation)
The claim follows from `(Subalgebra.mem_centralizer_iff ℂ).1 hz _ ⟨k, rfl⟩`.
-/
theorem commute_e_diag_of_mem {z : U n} (hz : z ∈ centralizerT n) (k : Fin n) :
    e (k, k) * z = z * e (k, k) :=
  (Subalgebra.mem_centralizer_iff ℂ).1 hz _ ⟨k, rfl⟩

/- English proof (translation)
Rewrite using `[← canon_zero, hcProjLin_canon_of_isDiagExp (fun a h => absurd rfl h)]`. Establish `: diagExp (0 : Fin n × Fin n →₀ ℕ) = 0` using `by ext; simp`. Rewrite using `[this, ← C_1, monomial_zero']`.
-/
theorem hcProjLin_one : hcProjLin (1 : U n) = 1 := by
  rw [← canon_zero, hcProjLin_canon_of_isDiagExp (fun a h => absurd rfl h)]
  have : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [this, ← C_1, monomial_zero']

/- English proof (translation)
Use `set p := hcProjLin z`. Use `set p' := hcProjLin z'`. Establish `hx` using `sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz)`. Establish `hx'` using `sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz')`. Use `set x := z - hcEmb p`.

Use `set x' := z' - hcEmb p'`. Establish `hzz : z * z' = hcEmb (p * p') + (hcEmb p * x' + x * hcEmb p' + x * x')`. Rewrite using `[map_mul]`. Simplify using `only [x, x']`. Use `noncomm_ring`.

Rewrite using `[hzz, map_add, hcProjLin_hcEmb]`. Establish `: hcEmb p * x' + x * hcEmb p' + x * x' ∈ nPlusU n` using `Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_nPlusU _ hx') (mul_mem_nPlusU_of_mem_cartanSub hx (hcEmb_mem_cartanSub p'))) (mul_mem_nPlusU _ hx')`. Rewrite using `[hcProjLin_eq_zero_of_mem_nPlusU this, add_zero]`.
-/
theorem hcProjLin_mul {z z' : U n} (hz : z ∈ centralizerT n) (hz' : z' ∈ centralizerT n) :
    hcProjLin (z * z') = hcProjLin z * hcProjLin z' := by
  set p := hcProjLin z
  set p' := hcProjLin z'
  have hx := sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz)
  have hx' := sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz')
  set x := z - hcEmb p
  set x' := z' - hcEmb p'
  have hzz : z * z' = hcEmb (p * p') + (hcEmb p * x' + x * hcEmb p' + x * x') := by
    rw [map_mul]; simp only [x, x']; noncomm_ring
  rw [hzz, map_add, hcProjLin_hcEmb]
  have : hcEmb p * x' + x * hcEmb p' + x * x' ∈ nPlusU n :=
    Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_nPlusU _ hx')
      (mul_mem_nPlusU_of_mem_cartanSub hx (hcEmb_mem_cartanSub p'))) (mul_mem_nPlusU _ hx')
  rw [hcProjLin_eq_zero_of_mem_nPlusU this, add_zero]

noncomputable def hcProj0 : centralizerT n →ₐ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun z := hcProjLin (z : U n)
  map_one' := hcProjLin_one
  map_mul' z z' := hcProjLin_mul z.2 z'.2
  map_zero' := by simp
  map_add' z z' := by simp
  commutes' r := by
    show hcProjLin (algebraMap ℂ (U n) r) = algebraMap ℂ _ r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hcProjLin_one, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem hcProj0_apply (z : centralizerT n) : hcProj0 z = hcProjLin (z : U n) := rfl

/- English proof (translation)
Establish `hN : ∀ x ∈ nPlusU n, φ x v = 0`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, a, ha, rfl⟩` from `hx`.

Rewrite using `[map_mul, Module.End.mul_apply, hup a ha, map_zero]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]`. Establish `hC : ∀ p, φ (hcEmb p) v = eval lam p • v`.

Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [AlgHom.commutes, Module.algebraMap_end_apply]`. Consider the case `add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq, map_add, add_smul]`. Consider the case `mul_X p i hp`.

Rewrite using `[map_mul, map_mul, Module.End.mul_apply, hcEmb_X, hH, map_smul, hp, smul_smul, eval_mul, eval_X, mul_comm]`. Use `sub_hcEmb_mem_nPlusU hz` as an intermediate fact. Establish `h` using `hN _ this`. Rewrite `h` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Rewrite using `[h, hC]`.
-/
theorem rep_apply_of_highestWeight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    {z : U n} (hz : ∀ k, e (k, k) * z = z * e (k, k)) :
    φ z v = eval lam (hcProjLin z) • v := by
  have hN : ∀ x ∈ nPlusU n, φ x v = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      rw [map_mul, Module.End.mul_apply, hup a ha, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hC : ∀ p, φ (hcEmb p) v = eval lam p • v := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [AlgHom.commutes, Module.algebraMap_end_apply]
    | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq, map_add, add_smul]
    | mul_X p i hp =>
      rw [map_mul, map_mul, Module.End.mul_apply, hcEmb_X, hH, map_smul, hp, smul_smul,
        eval_mul, eval_X, mul_comm]
  have := sub_hcEmb_mem_nPlusU hz
  have h := hN _ this
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
  rw [h, hC]

noncomputable def rhoVec (n : ℕ) : Fin n → ℂ := fun i => ((n : ℂ) - 1) / 2 - (i : ℂ)

noncomputable def translate (c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval fun i => X i + C (c i)

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [translate]`. Consider the case `add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, eval_mul, eval_mul, hp]`.

Simplify using `[translate]`.
-/
theorem eval_translate (c lam : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    eval lam (translate c p) = eval (lam + c) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [translate]
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval_mul, eval_mul, hp]
    simp [translate]

noncomputable def harishChandraHom : Subalgebra.center ℂ (U n) →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  (translate (-rhoVec n)).comp
    (hcProj0.comp (Subalgebra.inclusion (Subalgebra.center_le_centralizer ℂ (cartanSet n))))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem harishChandraHom_apply (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z = translate (-rhoVec n) (hcProjLin (z : U n)) := rfl

/- English proof (translation)
Rewrite using `[harishChandraHom_apply, eval_translate, sub_eq_add_neg]`.
-/
theorem eval_harishChandraHom (z : Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) :
    eval lam (harishChandraHom z) = eval (lam - rhoVec n) (hcProjLin (z : U n)) := by
  rw [harishChandraHom_apply, eval_translate, sub_eq_add_neg]

/- English proof (translation)
The claim follows from `Subalgebra.center_le_centralizer ℂ (cartanSet n) hz`.
-/
theorem mem_centralizerT_of_mem_center {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    z ∈ centralizerT n :=
  Subalgebra.center_le_centralizer ℂ (cartanSet n) hz

end GroundTheory.Automorphic.HarishChandra
