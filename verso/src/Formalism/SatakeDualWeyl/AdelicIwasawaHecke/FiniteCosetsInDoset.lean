import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

abbrev conjInter (K : Subgroup G) (s : G) : Subgroup K :=
  (K.map (MulAut.conj s).toMonoidHom).subgroupOf K

/- English proof (translation)
Use `haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩`. Conclude with `Subgroup.finite_quotient_of_finiteIndex`.
-/
theorem finite_quot_conjInter {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by
  haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩
  exact Subgroup.finite_quotient_of_finiteIndex

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (conjInter K s) k`. Establish `hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s` using `(h⁻¹).2`. Rewrite `hmem` using `[Subgroup.mem_subgroupOf, Subgroup.mem_map]`. Take `⟨m, hmK, hm⟩` from `hmem`. Use `⟨⟨m, hmK⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hh]`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm`. Establish `hm' : s * m = ((h : K) : G)⁻¹ * s`. Rewrite using `[← hm]`. Use `group`.

Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[mul_assoc _ s, hm']`. Use `group`.
-/
theorem mul_eq_out_mul (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (conjInter K s) k
  have hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s := (h⁻¹).2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hmem
  obtain ⟨m, hmK, hm⟩ := hmem
  refine ⟨⟨m, hmK⟩, ?_⟩
  rw [hh]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm
  have hm' : s * m = ((h : K) : G)⁻¹ * s := by
    rw [← hm]; group
  simp only [Subgroup.coe_mul]
  rw [mul_assoc _ s, hm']
  group

/- English proof (translation)
Use `haveI := finite_quot_conjInter hK s`. Use `(Set.finite_range (fun y : K ⧸ conjInter K s => ((((y.out : K) : G) * s : G) : G ⧸ K))).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨a, b, hx⟩`. Take `⟨k', hk'⟩` from `mul_eq_out_mul K s a`. Use `⟨QuotientGroup.mk a, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Establish `hxx : (QuotientGroup.mk x.out : G ⧸ K) = x` using `Quotient.out_eq x`. Rewrite using `[← hxx, hx, hk', QuotientGroup.eq]`. Establish `e : ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s)⁻¹ * ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s * k' * b) = k' * b` using `by group`. Rewrite using `[e]`.

Conclude with `K.mul_mem k'.2 b.2`.
-/
theorem finite_cosets_in_doset {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * s * b}.Finite := by
  haveI := finite_quot_conjInter hK s
  refine (Set.finite_range
    (fun y : K ⧸ conjInter K s => ((((y.out : K) : G) * s : G) : G ⧸ K))).subset ?_
  rintro x ⟨a, b, hx⟩
  obtain ⟨k', hk'⟩ := mul_eq_out_mul K s a
  refine ⟨QuotientGroup.mk a, ?_⟩
  dsimp only
  have hxx : (QuotientGroup.mk x.out : G ⧸ K) = x := Quotient.out_eq x
  rw [← hxx, hx, hk', QuotientGroup.eq]
  have e : ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s)⁻¹ *
      ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s * k' * b) = k' * b := by
    group
  rw [e]
  exact K.mul_mem k'.2 b.2

/- English proof (translation)
Take `⟨S, hS⟩` from `hf`. Use `(S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨s, hs, a, b, h⟩` from `hS _ hx`. Conclude with `Set.mem_biUnion hs ⟨a, b, h⟩`.
-/
theorem finite_support_cosets {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, h⟩ := hS _ hx
  exact Set.mem_biUnion hs ⟨a, b, h⟩

end Formalism.UG.P
