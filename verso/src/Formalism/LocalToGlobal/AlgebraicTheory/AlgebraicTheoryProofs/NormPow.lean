import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsReps IsSemiChar imgLat Th alphaQ qOf opU
  relIdx inter fixedBy stdH stdLat blk4 pow4 slice tens4 kernel4 sumU IsIsom F0 StdData prodFn)
open Formalism.L2.Th1.GD (LocNorm)

namespace RepresentativeBijection

section Reps

variable {V : Type} [AddCommGroup V]

/- English proof (translation)
Establish `h2` using `hS.2.1`. Establish `h3` using `hS.2.2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩ hxy`. Simplify using `only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hxy`.

Establish `h'` using `Λ₁.neg_mem hxy`. Rewrite `h'` using `[neg_add, neg_neg, ← sub_eq_add_neg]`. Conclude with `Subtype.ext (h2 x hx y hy h')`. Introduce `q`. Take `⟨⟨z, hz⟩, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Take `⟨x, hx, hzx⟩` from `h3 z hz`. Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Rewrite using `[neg_add_eq_sub]` and apply the resulting hypothesis.
-/
private theorem bijective_mk_of_isReps {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    Function.Bijective (fun x : {x // x ∈ S} =>
      (QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : Λ₂) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)) := by
  have h2 := hS.2.1
  have h3 := hS.2.2
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg] at hxy
    have h' := Λ₁.neg_mem hxy
    rw [neg_add, neg_neg, ← sub_eq_add_neg] at h'
    exact Subtype.ext (h2 x hx y hy h')
  · intro q
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, hx, hzx⟩ := h3 z hz
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    rwa [neg_add_eq_sub]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIdx_eq_card {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    relIdx Λ₁ Λ₂ = S.card := by
  classical
  calc relIdx Λ₁ Λ₂ = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := rfl
    _ = Nat.card {x // x ∈ S} := (Nat.card_congr (Equiv.ofBijective _ (bijective_mk_of_isReps hS))).symm
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/- English proof (translation)
Simplify using `only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`.

Conclude with `⟨g.symm y, h, by simp⟩`.
-/
theorem mem_imgLat' [Module ℂ V] (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (y : V) :
    y ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ g.symm y ∈ Λ := by
  simp only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

end Reps

/- English proof (translation)
Establish `hfin : Finite (B ⧸ A.addSubgroupOf B)` using `Nat.finite_of_card_ne_zero hAB`. Use `Fintype.ofFinite (B ⧸ A.addSubgroupOf B)` as an intermediate fact. Use `choose r hr using (QuotientAddGroup.mk_surjective : Function.Surjective (QuotientAddGroup.mk : B → B ⧸ A.addSubgroupOf B))`. Use `⟨Finset.univ.image fun q => ((r q : B) : V), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(r q).2`. Introduce `x hx y hy hxy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hy`.

Establish `hqq : q = q'`. Rewrite using `[← hr q, ← hr q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Establish `h'` using `A.neg_mem hxy`. Rewrite `h'` using `[neg_sub, sub_eq_neg_add]`. Then use the resulting hypothesis. Rewrite using `[hqq]`.

Introduce `y hy`. Use `⟨(r (QuotientAddGroup.mk ⟨y, hy⟩) : V), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h'` using `hr (QuotientAddGroup.mk ⟨y, hy⟩)`. Rewrite `h'` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Rewrite `h'` using `[neg_add_eq_sub]`. Then use the resulting hypothesis.
-/
private theorem exists_isReps_of_relIdx_ne_zero {V : Type} [AddCommGroup V] {A B : AddSubgroup V}
    (hAB : relIdx A B ≠ 0) : ∃ S : Finset V, IsReps A B S := by
  classical
  have hfin : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hAB
  have := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
  choose r hr using (QuotientAddGroup.mk_surjective :
    Function.Surjective (QuotientAddGroup.mk : B → B ⧸ A.addSubgroupOf B))
  refine ⟨Finset.univ.image fun q => ((r q : B) : V), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r q).2
  · intro x hx y hy hxy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
    have hqq : q = q' := by
      rw [← hr q, ← hr q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg]
      have h' := A.neg_mem hxy
      rwa [neg_sub, sub_eq_neg_add] at h'
    rw [hqq]
  · intro y hy
    refine ⟨(r (QuotientAddGroup.mk ⟨y, hy⟩) : V), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    have h' := hr (QuotientAddGroup.mk ⟨y, hy⟩)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg] at h'
    rwa [neg_add_eq_sub] at h'

/- English proof (translation)
Establish `hF' : ∀ y ∈ A, ∀ w, α y * opU H y F w = F w` using `hF`. Establish `h1` using `hα.1`. Establish `hxa` using `hα.2 x hx a haB`. Establish `hax` using `hα.2 a haB x hx`. Rewrite `hax` using `[add_comm a x]`.

Apply the tactic sequence `have hx0 : α x ≠ 0 := by rcases h1 x hx with h | h <;> rw [h] <;> norm_num`. Apply the tactic sequence `have ha0 : α a ≠ 0 := by rcases h1 a haB with h | h <;> rw [h] <;> norm_num`. Establish `hE : altE H a x = -altE H x a`. Simplify using `only [altE]`. Rewrite using `[hH x a, Complex.conj_im]`.

Establish `h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ))`. Establish `h3 : α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) = α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ))`. Rewrite using `[← hxa, hax]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ (mul_ne_zero hx0 ha0) h3`.

Establish `hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) = 1` using `by conv_lhs => arg 2; rw [h4]`. Rewrite using `[← Complex.exp_add, hE, Complex.ofReal_neg]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hFa` using `hF' a ha (z + x)`.

Simplify using `only [opU] at hFa ⊢`. Establish `hPQ : ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2) + (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2) = (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) + (Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)`. Establish `hc : H x a - conj (H x a) = 2 * Complex.I * (((H x a).im : ℝ) : ℂ)`. Rewrite using `[Complex.sub_conj]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, LinearMap.add_apply, altE]`. Rewrite using `[hH x a]`. Take the linear combination `((Real.pi : ℂ) / 2) * hc`. Establish `hinv : Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2) * Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2) = 1`.

Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `key : Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2) * Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2) = Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, hPQ]`.

Rewrite using `[← add_assoc]`. Use `set E1 := Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2)`. Use `set E2 := Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)`. Use `set EQ := Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)`. Use `set eR := Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)`.

Use `set eE := Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))`. Take the linear combination `(F (z + x + a) * EQ) * hxa + (α x * eR) * hFa + (-(α x * α a * F (z + x + a) * eE * EQ)) * hinv + (α x * α a * F (z + x + a) * eE * E1) * key + (α x * α a * F (z + x + a) * eR * E1) * hexp`.
-/
private theorem mul_opU_add_eq_of_mem_fixedBy {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
    {A B : AddSubgroup V} {α : V → ℂ} {F : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H B α)
    (hF : F ∈ fixedBy H α A) {x a : V} (hx : x ∈ B) (ha : a ∈ A) (haB : a ∈ B) (z : V) :
    α (x + a) * opU H (x + a) F z = α x * opU H x F z := by
  have hF' : ∀ y ∈ A, ∀ w, α y * opU H y F w = F w := hF
  have h1 := hα.1
  have hxa := hα.2 x hx a haB
  have hax := hα.2 a haB x hx
  rw [add_comm a x] at hax
  have hx0 : α x ≠ 0 := by rcases h1 x hx with h | h <;> rw [h] <;> norm_num
  have ha0 : α a ≠ 0 := by rcases h1 a haB with h | h <;> rw [h] <;> norm_num
  have hE : altE H a x = -altE H x a := by
    simp only [altE]
    rw [hH x a, Complex.conj_im]
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ)) := by
    have h3 : α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
        = α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ)) := by
      rw [← hxa, hax]; ring
    exact mul_left_cancel₀ (mul_ne_zero hx0 ha0) h3
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
      * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) = 1 := by
    conv_lhs => arg 2; rw [h4]
    rw [← Complex.exp_add, hE, Complex.ofReal_neg]
    convert Complex.exp_zero using 2
    ring
  have hFa := hF' a ha (z + x)
  simp only [opU] at hFa ⊢
  have hPQ : ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
      + (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
      = (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
        + (Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ) := by
    have hc : H x a - conj (H x a) = 2 * Complex.I * (((H x a).im : ℝ) : ℂ) := by
      rw [Complex.sub_conj]; push_cast; ring
    simp only [map_add, LinearMap.add_apply, altE]
    rw [hH x a]
    linear_combination ((Real.pi : ℂ) / 2) * hc
  have hinv : Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2)
      * Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  have key : Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
      * Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
      = Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
        * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hPQ]
  rw [← add_assoc]
  set E1 := Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2)
  set E2 := Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
  set EQ := Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
  set eR := Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
  set eE := Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
  linear_combination (F (z + x + a) * EQ) * hxa + (α x * eR) * hFa
    + (-(α x * α a * F (z + x + a) * eE * EQ)) * hinv + (α x * α a * F (z + x + a) * eE * E1) * key
    + (α x * α a * F (z + x + a) * eR * E1) * hexp

/- English proof (translation)
Rewrite using `[← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_of_isReps hS)), finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort S]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `set q := (Equiv.ofBijective _ (bijective_mk_of_isReps hS)) x with hqdef`. Establish `hq : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : B)` using `QuotientAddGroup.out_eq' q`. Rewrite `hq` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]`.

Establish `hoB : ((Quotient.out q : B) : V) ∈ B` using `(Quotient.out q).2`. Establish `haB : -((Quotient.out q : B) : V) + x.1 ∈ B` using `B.add_mem (B.neg_mem hoB) (hS.1 x.1 x.2)`. Establish `hxo : (x.1 : V) = ((Quotient.out q : B) : V) + (-((Quotient.out q : B) : V) + x.1)` using `by abel`. Rewrite using `[hxo]`. Conclude with `(mul_opU_add_eq_of_mem_fixedBy hH hα hF hoB hq haB z).symm`.
-/
private theorem finsum_quotient_eq_sum_reps {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
    {A B : AddSubgroup V} {α : V → ℂ} {F : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H B α)
    (hF : F ∈ fixedBy H α A) {S : Finset V} (hS : IsReps A B S) (z : V) :
    (∑ᶠ c : B ⧸ A.addSubgroupOf B, α ((Quotient.out c : B) : V) * opU H ((Quotient.out c : B) : V) F z)
      = ∑ x ∈ S, α x * opU H x F z := by
  classical
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_of_isReps hS)), finsum_eq_sum_of_fintype,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun x _ => ?_
  set q := (Equiv.ofBijective _ (bijective_mk_of_isReps hS)) x with hqdef
  have hq : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B)
      = QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : B) := QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at hq
  have hoB : ((Quotient.out q : B) : V) ∈ B := (Quotient.out q).2
  have haB : -((Quotient.out q : B) : V) + x.1 ∈ B := B.add_mem (B.neg_mem hoB) (hS.1 x.1 x.2)
  have hxo : (x.1 : V) = ((Quotient.out q : B) : V) + (-((Quotient.out q : B) : V) + x.1) := by abel
  rw [hxo]
  exact (mul_opU_add_eq_of_mem_fixedBy hH hα hF hoB hq haB z).symm

/- English proof (translation)
Simplify using `only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]`.
-/
private theorem stdH_apply_algebraic (L : PeriodPair) (N : Type) [Fintype N] [DecidableEq N] (u v : N → ℂ) :
    stdH L N u v = ∑ m, u m * ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * conj (v m) := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules.
-/
private theorem sum_ite_eq_snd {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (b : β)
    (f : α × β → ℂ) : ∑ w : α × β, (if b = w.2 then f w else 0) = ∑ k, f (k, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules.
-/
private theorem sum_ite_eq_fst {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (a : α)
    (f : α × β → ℂ) : ∑ w : α × β, (if a = w.1 then f w else 0) = ∑ k, f (a, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

/- English proof (translation)
Simplify using `only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_fst]`. Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
private theorem matH_blk4 {N : Type} [Fintype N] (g : Matrix N N ℂ) (u v : Fin 4 × N → ℂ) :
    matH (blk4 g) u v = ∑ a, matH g (slice a u) (slice a v) := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_fst]
  rw [Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Establish `h : Real.sqrt ((r ^ k : ℕ) : ℝ) = Real.sqrt r ^ k` using `by conv_lhs => rw [Nat.cast_pow, ← Real.sq_sqrt (Nat.cast_nonneg r)]`. Rewrite using `[← pow_mul, mul_comm 2 k, pow_mul, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]`. Rewrite using `[h, Complex.ofReal_pow, inv_pow]`.
-/
theorem sqrt_pow_inv (r k : ℕ) :
    ((Real.sqrt ((r ^ k : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ = (((Real.sqrt r : ℝ) : ℂ)⁻¹) ^ k := by
  have h : Real.sqrt ((r ^ k : ℕ) : ℝ) = Real.sqrt r ^ k := by
    conv_lhs => rw [Nat.cast_pow, ← Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [← pow_mul, mul_comm 2 k, pow_mul, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
  rw [h, Complex.ofReal_pow, inv_pow]

section Slices

variable {M M' I : Type} [Fintype M] [Fintype M'] [Fintype I] (e : M' ≃ M × I)

def sl (i : I) (w : M' → ℂ) : M → ℂ := fun m => w (e.symm (m, i))

def asm (f : I → M → ℂ) : M' → ℂ := fun m' => f (e m').2 (e m').1

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[sl, asm]`.
-/
theorem sl_asm (f : I → M → ℂ) (i : I) : sl e i (asm e f) = f i := by
  funext m
  simp [sl, asm]

/- English proof (translation)
Use function extensionality and compare the values at `m'`. Simplify using `[sl, asm]`.
-/
theorem asm_sl (w : M' → ℂ) : asm e (fun i => sl e i w) = w := by
  funext m'
  simp [sl, asm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sl_add (i : I) (x y : M' → ℂ) : sl e i (x + y) = sl e i x + sl e i y := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sl_sub (i : I) (x y : M' → ℂ) : sl e i (x - y) = sl e i x - sl e i y := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sl_smul (i : I) (c : ℂ) (x : M' → ℂ) : sl e i (c • x) = c • sl e i x := rfl

/- English proof (translation)
Introduce `f g h`. Use function extensionality and compare the values at `i`. Use `congrArg (sl e i) h` as an intermediate fact. Rewrite `this` using `[sl_asm, sl_asm]`. Then use the resulting hypothesis.
-/
theorem asm_injective : Function.Injective (asm e) := by
  intro f g h
  funext i
  have := congrArg (sl e i) h
  rwa [sl_asm, sl_asm] at this

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp e.symm G, Fintype.sum_prod_type, Finset.sum_comm]`.
-/
theorem sum_e (G : M' → ℂ) : ∑ m', G m' = ∑ i, ∑ m, G (e.symm (m, i)) := by
  rw [← Equiv.sum_comp e.symm G, Fintype.sum_prod_type, Finset.sum_comm]

/- English proof (translation)
Rewrite using `[← Equiv.prod_comp e.symm G, Fintype.prod_prod_type, Finset.prod_comm]`.
-/
theorem prod_e (G : M' → ℂ) : ∏ m', G m' = ∏ i, ∏ m, G (e.symm (m, i)) := by
  rw [← Equiv.prod_comp e.symm G, Fintype.prod_prod_type, Finset.prod_comm]

def prodSub (A : AddSubgroup (M → ℂ)) : AddSubgroup (M' → ℂ) where
  carrier := {w | ∀ i, sl e i w ∈ A}
  zero_mem' := fun _ => A.zero_mem
  add_mem' := fun hx hy i => A.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => A.neg_mem (hx i)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_prodSub (A : AddSubgroup (M → ℂ)) (w : M' → ℂ) : w ∈ prodSub e A ↔ ∀ i, sl e i w ∈ A := Iff.rfl

variable [DecidableEq I]

/- English proof (translation)
Establish `h1` using `hS.1`. Establish `h2` using `hS.2.1`. Establish `h3` using `hS.2.2`. Use `⟨(Fintype.piFinset fun _ : I => S).image (asm e), ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite `hf` using `[Fintype.mem_piFinset]`. Use `(mem_prodSub e B _).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[sl_asm]`. Conclude with `h1 _ (hf i)`.

Introduce `x hx y hy hxy`. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨g, hg, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite `hf`, `hg` using `[Fintype.mem_piFinset]`. Establish `hfg : f = g`.

Use function extensionality and compare the values at `i`. Use `(mem_prodSub e A _).1 hxy i` as an intermediate fact. Rewrite `this` using `[sl_sub, sl_asm, sl_asm]`. Conclude with `h2 _ (hf i) _ (hg i) this`. Rewrite using `[hfg]`.

Introduce `y hy`. Establish `: ∀ i, ∃ x ∈ S, sl e i y - x ∈ A` using `fun i => h3 _ ((mem_prodSub e B y).1 hy i)`. Use `choose f hfS hfA using this`. Use `⟨asm e f, Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 hfS, rfl⟩, ?_⟩` and prove the remaining obligations. Use `(mem_prodSub e A _).2 fun i => ?_` and prove the remaining obligations.

Rewrite using `[sl_sub, sl_asm]`. Conclude with `hfA i`. Rewrite using `[Finset.card_image_of_injective _ (asm_injective e), Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]`. Introduce `G`. Rewrite using `[Finset.sum_image fun x _ y _ h => asm_injective e h]`.
-/
theorem reps_prod {A B : AddSubgroup (M → ℂ)} {S : Finset (M → ℂ)} (hS : IsReps A B S) :
    ∃ S' : Finset (M' → ℂ), IsReps (prodSub e A) (prodSub e B) S' ∧ S'.card = S.card ^ Fintype.card I ∧
      ∀ G : (M' → ℂ) → ℂ, ∑ x ∈ S', G x = ∑ f ∈ Fintype.piFinset (fun _ : I => S), G (asm e f) := by
  classical
  have h1 := hS.1
  have h2 := hS.2.1
  have h3 := hS.2.2
  refine ⟨(Fintype.piFinset fun _ : I => S).image (asm e), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    rw [Fintype.mem_piFinset] at hf
    refine (mem_prodSub e B _).2 fun i => ?_
    rw [sl_asm]
    exact h1 _ (hf i)
  · intro x hx y hy hxy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hy
    rw [Fintype.mem_piFinset] at hf hg
    have hfg : f = g := by
      funext i
      have := (mem_prodSub e A _).1 hxy i
      rw [sl_sub, sl_asm, sl_asm] at this
      exact h2 _ (hf i) _ (hg i) this
    rw [hfg]
  · intro y hy
    have : ∀ i, ∃ x ∈ S, sl e i y - x ∈ A := fun i => h3 _ ((mem_prodSub e B y).1 hy i)
    choose f hfS hfA using this
    refine ⟨asm e f, Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 hfS, rfl⟩, ?_⟩
    refine (mem_prodSub e A _).2 fun i => ?_
    rw [sl_sub, sl_asm]
    exact hfA i
  · rw [Finset.card_image_of_injective _ (asm_injective e), Fintype.card_piFinset,
      Finset.prod_const, Finset.card_univ]
  · intro G
    rw [Finset.sum_image fun x _ y _ h => asm_injective e h]

/- English proof (translation)
Take `⟨S, hS⟩` from `exists_isReps_of_relIdx_ne_zero hAB`. Take `⟨S', hS', hcard, -⟩` from `reps_prod e hS`. Rewrite using `[relIdx_eq_card hS', relIdx_eq_card hS, hcard]`.
-/
theorem relIdx_prod {A B : AddSubgroup (M → ℂ)} (hAB : relIdx A B ≠ 0) :
    relIdx (prodSub e A) (prodSub e B) = relIdx A B ^ Fintype.card I := by
  obtain ⟨S, hS⟩ := exists_isReps_of_relIdx_ne_zero hAB
  obtain ⟨S', hS', hcard, -⟩ := reps_prod e hS
  rw [relIdx_eq_card hS', relIdx_eq_card hS, hcard]

variable (H : Sesq (M → ℂ)) (H' : Sesq (M' → ℂ)) (hHd : ∀ x y, H' x y = ∑ i, H (sl e i x) (sl e i y))
include hHd

/- English proof (translation)
Introduce `x y`. Rewrite using `[hHd, hHd, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hH _ _`.
-/
theorem herm_prod (hH : IsHerm H) : IsHerm H' := by
  intro x y
  rw [hHd, hHd, map_sum]
  exact Finset.sum_congr rfl fun i _ => hH _ _

/- English proof (translation)
Simplify using `only [altE, hHd, Complex.im_sum]`.
-/
theorem altE_prod (x y : M' → ℂ) : altE H' x y = ∑ i, altE H (sl e i x) (sl e i y) := by
  simp only [altE, hHd, Complex.im_sum]

/- English proof (translation)
Simplify using `only [alphaQ, qOf, hHd, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum]`.
-/
theorem alphaQ_prod (c : ℝ) (x : M' → ℂ) : alphaQ c H' x = ∏ i, alphaQ c H (sl e i x) := by
  simp only [alphaQ, qOf, hHd, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum]

/- English proof (translation)
Simplify using `only [opU, hHd, sl_add, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]`.
-/
theorem opU_prod (x : M' → ℂ) (F : (M → ℂ) → ℂ) (z : M' → ℂ) :
    opU H' x (fun w => ∏ i, F (sl e i w)) z = ∏ i, opU H (sl e i x) F (sl e i z) := by
  simp only [opU, hHd, sl_add, Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hα`. Use `⟨fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[mem_prodSub]`. Use `Finset.prod_induction _ (fun z => z = 1 ∨ z = -1) ?_ (Or.inl rfl) fun i _ => h1 _ (hx i)` and prove the remaining obligations. Apply the tactic sequence `rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num`.

Rewrite `hx`, `hy` using `[mem_prodSub]`. Simplify using `only [sl_add]`. Rewrite using `[Finset.prod_congr rfl fun i _ => h2 _ (hx i) _ (hy i), Finset.prod_mul_distrib, Finset.prod_mul_distrib, altE_prod (hHd := hHd), Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]`.
-/
theorem semiChar_prod {B : AddSubgroup (M → ℂ)} {α : (M → ℂ) → ℂ} (hα : IsSemiChar H B α) :
    IsSemiChar H' (prodSub e B) (fun x => ∏ i, α (sl e i x)) := by
  obtain ⟨h1, h2⟩ := hα
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [mem_prodSub] at hx
    refine Finset.prod_induction _ (fun z => z = 1 ∨ z = -1) ?_ (Or.inl rfl) fun i _ => h1 _ (hx i)
    rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · rw [mem_prodSub] at hx hy
    simp only [sl_add]
    rw [Finset.prod_congr rfl fun i _ => h2 _ (hx i) _ (hy i), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, altE_prod (hHd := hHd), Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]

/- English proof (translation)
Establish `hF' : ∀ x ∈ A, ∀ z, α x * opU H x F z = F z` using `hF`. Use `show ∀ x ∈ prodSub e A, ∀ z, (∏ i, α (sl e i x)) * opU H' x (fun w => ∏ i, F (sl e i w)) z = ∏ i, F (sl e i z)`. Introduce `x hx z`. Rewrite `hx` using `[mem_prodSub]`. Rewrite using `[opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun i _ => hF' _ (hx i) _`.
-/
theorem fixed_prod {A : AddSubgroup (M → ℂ)} {α : (M → ℂ) → ℂ} {F : (M → ℂ) → ℂ} (hF : F ∈ fixedBy H α A) :
    (fun w => ∏ i, F (sl e i w)) ∈ fixedBy H' (fun x => ∏ i, α (sl e i x)) (prodSub e A) := by
  have hF' : ∀ x ∈ A, ∀ z, α x * opU H x F z = F z := hF
  show ∀ x ∈ prodSub e A, ∀ z, (∏ i, α (sl e i x)) * opU H' x (fun w => ∏ i, F (sl e i w)) z
    = ∏ i, F (sl e i z)
  intro x hx z
  rw [mem_prodSub] at hx
  rw [opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => hF' _ (hx i) _

/- English proof (translation)
Take `⟨S, hS⟩` from `exists_isReps_of_relIdx_ne_zero hAB`. Take `⟨S', hS', hcard, hsum⟩` from `reps_prod e hS`. Establish `hR : ∀ i, inter H α A B F (sl e i z) = ((Real.sqrt (relIdx A B) : ℝ) : ℂ)⁻¹ * ∑ x ∈ S, α x * opU H x F (sl e i z)` using `fun i => by`. Simplify using `only [inter]`. Rewrite using `[finsum_quotient_eq_sum_reps hH hα hF hS]`.

Rewrite using `[Finset.prod_congr rfl fun i _ => hR i, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Simplify using `only [inter]`. Rewrite using `[finsum_quotient_eq_sum_reps (herm_prod e H H' hHd hH) (semiChar_prod e H H' hHd hα) (fixed_prod e H H' hHd hF) hS' z, hsum, relIdx_prod e hAB, sqrt_pow_inv]`. Use `congr 1`. Rewrite using `[Finset.prod_univ_sum]`.

Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]`. Simplify using `only [sl_asm]`.
-/
theorem inter_prod (hH : IsHerm H) (A B : AddSubgroup (M → ℂ)) (α : (M → ℂ) → ℂ) (hα : IsSemiChar H B α)
    (F : (M → ℂ) → ℂ) (hF : F ∈ fixedBy H α A) (hAB : relIdx A B ≠ 0) (z : M' → ℂ) :
    inter H' (fun x => ∏ i, α (sl e i x)) (prodSub e A) (prodSub e B) (fun w => ∏ i, F (sl e i w)) z
      = ∏ i, inter H α A B F (sl e i z) := by
  classical
  obtain ⟨S, hS⟩ := exists_isReps_of_relIdx_ne_zero hAB
  obtain ⟨S', hS', hcard, hsum⟩ := reps_prod e hS
  have hR : ∀ i, inter H α A B F (sl e i z)
      = ((Real.sqrt (relIdx A B) : ℝ) : ℂ)⁻¹ * ∑ x ∈ S, α x * opU H x F (sl e i z) := fun i => by
    simp only [inter]
    rw [finsum_quotient_eq_sum_reps hH hα hF hS]
  rw [Finset.prod_congr rfl fun i _ => hR i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  simp only [inter]
  rw [finsum_quotient_eq_sum_reps (herm_prod e H H' hHd hH) (semiChar_prod e H H' hHd hα)
    (fixed_prod e H H' hHd hF) hS' z, hsum, relIdx_prod e hAB, sqrt_pow_inv]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]
  simp only [sl_asm]

end Slices

section Std

variable {M M' I : Type} [Fintype M] [Fintype M'] [Fintype I] [DecidableEq M] [DecidableEq M'] (e : M' ≃ M × I)

/- English proof (translation)
Simplify using `only [stdH_apply_algebraic]`. Rewrite using `[sum_e e]`. Both sides reduce to the same expression.
-/
theorem stdH_prod (L : PeriodPair) (x y : M' → ℂ) :
    stdH L M' x y = ∑ i, stdH L M (sl e i x) (sl e i y) := by
  simp only [stdH_apply_algebraic]
  rw [sum_e e]
  rfl

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[mem_prodSub]`. Simplify using `only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, sl]`. Prove the components needed by the constructor for the conclusion. Introduce `h i m`.

Conclude with `h _`. Introduce `h m'`. Use `h (e m').2 (e m').1` as an intermediate fact. Simplify using `using this`.
-/
theorem stdLat_prod (L : PeriodPair) : stdLat L M' = prodSub e (stdLat L M) := by
  ext w
  rw [mem_prodSub]
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, sl]
  constructor
  · intro h i m
    exact h _
  · intro h m'
    have := h (e m').2 (e m').1
    simpa using this

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [F0, prodFn]`. Conclude with `prod_e e _`.
-/
theorem gaussianVacuum_prod_blocks (L : PeriodPair) (ω₀ : ℂ) : F0 L ω₀ M' = fun w => ∏ i, F0 L ω₀ M (sl e i w) := by
  funext w
  simp only [F0, prodFn]
  exact prod_e e _

end Std

section Pow

variable {n : Type} [Fintype n] [DecidableEq n] {I : Type} [Fintype I] [DecidableEq I]

def eP (n I : Type) : Fin 4 × (n × I) ≃ (Fin 4 × n) × I := (Equiv.prodAssoc (Fin 4) n I).symm

def powEquiv {M M' : Type} [Fintype M] [Fintype M'] (e : M' ≃ M × I) (g : (M → ℂ) ≃ₗ[ℂ] (M → ℂ)) : (M' → ℂ) ≃ₗ[ℂ] (M' → ℂ) where
  toFun z := asm e fun i => g (sl e i z)
  invFun z := asm e fun i => g.symm (sl e i z)
  map_add' x y := by
    funext m'
    show g (sl e (e m').2 (x + y)) (e m').1 = g (sl e (e m').2 x) (e m').1 + g (sl e (e m').2 y) (e m').1
    rw [sl_add, map_add]; rfl
  map_smul' c x := by
    funext m'
    show g (sl e (e m').2 (c • x)) (e m').1 = c * g (sl e (e m').2 x) (e m').1
    rw [sl_smul, map_smul]; rfl
  left_inv z := by
    show asm e (fun i => g.symm (sl e i (asm e fun i => g (sl e i z)))) = z
    simp only [sl_asm, LinearEquiv.symm_apply_apply, asm_sl]
  right_inv z := by
    show asm e (fun i => g (sl e i (asm e fun i => g.symm (sl e i z)))) = z
    simp only [sl_asm, LinearEquiv.apply_symm_apply, asm_sl]

/- English proof (translation)
Use `show sl e i (asm e fun i => g (sl e i z)) = g (sl e i z)`. Rewrite using `[sl_asm]`.
-/
theorem sl_powEquiv {M M' : Type} [Fintype M] [Fintype M'] (e : M' ≃ M × I) (g : (M → ℂ) ≃ₗ[ℂ] (M → ℂ)) (i : I) (z : M' → ℂ) :
    sl e i (powEquiv e g z) = g (sl e i z) := by
  show sl e i (asm e fun i => g (sl e i z)) = g (sl e i z)
  rw [sl_asm]

/- English proof (translation)
Simplify using `only [matH, LinearMap.mk₂'ₛₗ_apply, hPow, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_snd]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_comm]`.
-/
theorem matH_hPow (h : Matrix n n ℂ) (u v : n × I → ℂ) :
    matH (hPow I h) u v = ∑ i, matH h (fun k => u (k, i)) (fun k => v (k, i)) := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, hPow, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_snd]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/- English proof (translation)
Rewrite using `[matH_blk4]`. Simplify using `only [matH_hPow]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[matH_blk4]`.

Both sides reduce to the same expression.
-/
theorem hermitian_block_power_sum (h : Matrix n n ℂ) (x y : Fin 4 × (n × I) → ℂ) :
    matH (blk4 (hPow I h)) x y = ∑ i, matH (blk4 h) (sl (eP n I) i x) (sl (eP n I) i y) := by
  rw [matH_blk4]
  simp only [matH_hPow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matH_blk4]
  rfl

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_imgLat', mem_prodSub]`. Simplify using `only [mem_imgLat']`. Prove the components needed by the constructor for the conclusion. Introduce `h i show ∀ a, _`.

Introduce `a`. Conclude with `h a i`. Introduce `h a show ∀ i, _`. Introduce `i`. Conclude with `h i a`.
-/
theorem img_prod (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (Λ : AddSubgroup (n → ℂ)) :
    imgLat ((powEquiv (eP n I) g : (Fin 4 × (n × I) → ℂ) ≃ₗ[ℂ] (Fin 4 × (n × I) → ℂ)) :
        (Fin 4 × (n × I) → ℂ) →ₗ[ℂ] (Fin 4 × (n × I) → ℂ)) (pow4 (latPow I Λ)) =
      prodSub (eP n I) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
  ext y
  rw [mem_imgLat', mem_prodSub]
  simp only [mem_imgLat']
  constructor
  · intro h i
    show ∀ a, _
    intro a
    exact h a i
  · intro h a
    show ∀ i, _
    intro i
    exact h i a

end Pow

end RepresentativeBijection

open RepresentativeBijection

/- English proof (translation)
Introduce `a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hL`. Take `⟨g₁, ε, h1, h2, h3, h4, h5⟩` from `hL`. Use `⟨g₁, c ^ 4 * ε, h1, h2, h3, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Use function extensionality and compare the values at `z`. Establish `hz` using `congrFun h5 z`. Simplify using `only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hz ⊢`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_norm_scaling : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hL
  obtain ⟨g₁, ε, h1, h2, h3, h4, h5⟩ := hL
  refine ⟨g₁, c ^ 4 * ε, h1, h2, h3, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 ^ 4 * 1 := by gcongr
      _ = 1 := by norm_num
  · funext z
    have hz := congrFun h5 z
    simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hz ⊢
    rw [hz]
    ring

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hΛ hΛθ θ hθ p _ ι hN I _ _`. Take `⟨g₁, ε, hiso, hp, hidx, hε, hT⟩` from `hN`. Establish `hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0`. Introduce `h0`. Rewrite `hp` using `[h0]`.

Conclude with `hp (dvd_zero p)`. Establish `hSD` using `Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hOK.1 hOK.2.1 hOK.2.2.1 n h Λ g₁ hiso hΛ hΛθ hidx1 hidx`. Establish `hH : IsHerm (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))` using `(Formalism.L2.Th1.H.stdHBasic (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)).2.1`. Establish `hF` using `(Formalism.L2.Th1.H.product_theta_mem' (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hSD.per hSD.half _ hSD.betaStd).1.2`. Establish `hHd` using `stdH_prod (eP n I) (cmL a₀ b₀ dK ha hdK lam hlam)`.

Use `⟨powEquiv (eP n I) g₁, ε ^ Fintype.card I, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[hHd, hermitian_block_power_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[sl_powEquiv, sl_powEquiv]`. Conclude with `hiso _ _`. Rewrite using `[stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx1]`. Introduce `hd`. Conclude with `hp ((Fact.out : p.Prime).dvd_of_dvd_pow hd)`.

Rewrite using `[stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx]`. Conclude with `pow_ne_zero _ hidx`. Rewrite using `[map_pow, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hε`. Use function extensionality and compare the values at `z`.

Establish `hL : tens4 (fnPow I θ) z = ∏ i, tens4 θ (sl (eP n I) i z)`. Simplify using `only [tens4, fnPow]`. Rewrite using `[Finset.prod_comm]`. Both sides reduce to the same expression. Rewrite using `[hL, Pi.smul_apply, smul_eq_mul]`.

Simplify using `only [hT, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Use `congr 1`. Simplify using `only [kernel4]`. Establish `hα : alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × (n × I))) = fun x => ∏ i, alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (sl (eP n I) i x)`. Use function extensionality and compare the values at `fun x => alphaQ_prod (eP n I) _ _ hHd _ x`.

Rewrite using `[stdLat_prod (eP n I), img_prod, hα, gaussianVacuum_prod_blocks (eP n I), inter_prod (eP n I) _ _ hHd hH _ _ _ hSD.betaSemi _ hF hidx1]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sl_powEquiv]`.
-/
theorem local_norm_power : LocNormPow := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hΛ hΛθ θ hθ p _ ι hN I _ _
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, hT⟩ := hN
  have hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := by
    intro h0; rw [h0] at hp; exact hp (dvd_zero p)
  have hSD := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hOK.1 hOK.2.1 hOK.2.2.1 n h Λ g₁ hiso hΛ hΛθ
    hidx1 hidx
  have hH : IsHerm (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) :=
    (Formalism.L2.Th1.H.stdHBasic (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)).2.1
  have hF := (Formalism.L2.Th1.H.product_theta_mem' (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hSD.per hSD.half _
    hSD.betaStd).1.2
  have hHd := stdH_prod (eP n I) (cmL a₀ b₀ dK ha hdK lam hlam)
  refine ⟨powEquiv (eP n I) g₁, ε ^ Fintype.card I, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearEquiv.coe_coe]
    rw [hHd, hermitian_block_power_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sl_powEquiv, sl_powEquiv]
    exact hiso _ _
  · rw [stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx1]
    intro hd
    exact hp ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
  · rw [stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx]
    exact pow_ne_zero _ hidx
  · rw [map_pow, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hε
  · funext z
    have hL : tens4 (fnPow I θ) z = ∏ i, tens4 θ (sl (eP n I) i z) := by
      simp only [tens4, fnPow]
      rw [Finset.prod_comm]
      rfl
    rw [hL, Pi.smul_apply, smul_eq_mul]
    simp only [hT, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    simp only [kernel4]
    have hα : alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × (n × I))) =
        fun x => ∏ i, alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (sl (eP n I) i x) :=
      funext fun x => alphaQ_prod (eP n I) _ _ hHd _ x
    rw [stdLat_prod (eP n I), img_prod, hα, gaussianVacuum_prod_blocks (eP n I),
      inter_prod (eP n I) _ _ hHd hH _ _ _ hSD.betaSemi _ hF hidx1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sl_powEquiv]

end Formalism.L2.AlgTh
