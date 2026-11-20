import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.HeisenbergUnitaryHolds

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

section Reps
variable {G : Type*} [AddCommGroup G]

/- English proof (translation)
Establish `: (M.addSubgroupOf N).FiniteIndex` using `⟨h⟩`. Establish `: Finite (N ⧸ M.addSubgroupOf N)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Use `letI := Fintype.ofFinite (N ⧸ M.addSubgroupOf N)`. Set `f : (N ⧸ M.addSubgroupOf N) → G` to `fun q => ((Quotient.out q : N) : G)`. Establish `hf : Function.Injective f`.

Introduce `q q' hq`. Establish `: (Quotient.out q : N) = Quotient.out q'` using `Subtype.ext hq`. Simplify using `using congrArg (fun x : N => (x : N ⧸ M.addSubgroupOf N)) this`. Use `⟨Finset.univ.image f, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(Quotient.out q : N).2`. Introduce `x hx y hy hxy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hy`.

Establish `: q = q'`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']`. Rewrite using `[QuotientAddGroup.eq]`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Establish `: -(f q) + f q' ∈ M`.

Use `M.neg_mem hxy` as an intermediate fact. Simplify `this` using `[neg_sub, sub_eq_neg_add]`. Simplify `this` using `[f]`. Rewrite using `[this]`. Introduce `y hy`.

Use `⟨f (QuotientAddGroup.mk (⟨y, hy⟩ : N)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Establish `h1` using `QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨y, hy⟩ : N) : N ⧸ M.addSubgroupOf N)`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [f, AddSubgroup.coe_add, AddSubgroup.coe_neg]`.

Normalize the expressions using the abelian group laws. Rewrite using `[Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression.
-/
theorem repsG_exist (M N : AddSubgroup G) (h : M.relIndex N ≠ 0) :
    ∃ S : Finset G, IsRepsG M N S ∧ S.card = M.relIndex N := by
  classical
  have : (M.addSubgroupOf N).FiniteIndex := ⟨h⟩
  have : Finite (N ⧸ M.addSubgroupOf N) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (N ⧸ M.addSubgroupOf N)
  let f : (N ⧸ M.addSubgroupOf N) → G := fun q => ((Quotient.out q : N) : G)
  have hf : Function.Injective f := by
    intro q q' hq
    have : (Quotient.out q : N) = Quotient.out q' := Subtype.ext hq
    simpa using congrArg (fun x : N => (x : N ⧸ M.addSubgroupOf N)) this
  refine ⟨Finset.univ.image f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q : N).2
  · intro x hx y hy hxy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
    have : q = q' := by
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
      rw [QuotientAddGroup.eq]
      rw [AddSubgroup.mem_addSubgroupOf]
      have : -(f q) + f q' ∈ M := by
        have := M.neg_mem hxy
        simpa [neg_sub, sub_eq_neg_add] using this
      simpa [f] using this
    rw [this]
  · intro y hy
    refine ⟨f (QuotientAddGroup.mk (⟨y, hy⟩ : N)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨y, hy⟩ : N) : N ⧸ M.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    convert h1 using 1
    simp only [f, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl

end Reps

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Unfold `cU`. Rewrite using `[Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Use `⟨-n, ?_⟩` and prove the remaining obligations.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0` using `by simp [hpi, Complex.I_ne_zero]`. Establish `: ((altE H (a : V) (b : V) : ℝ) : ℂ) = ((-n : ℤ) : ℂ)`. Apply `mul_right_cancel₀ h2` to reduce the goal to its premises. Use `push_cast`.

Take the linear combination `-hn`. Conclude with `this` after adjusting the coercions. Introduce and unpack `⟨m, hm⟩`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cU_eq_one_iff (H : Sesq V) (A B : AddSubgroup V) (b : B) (a : A) :
    cU H A B b a = 1 ↔ ∃ m : ℤ, altE H (a : V) (b : V) = m := by
  unfold cU
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have : ((altE H (a : V) (b : V) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_right_cancel₀ h2
      push_cast
      linear_combination -hn
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rw [hm]; push_cast; ring

end

section Moves
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Rewrite using `[← AddSubgroup.inf_addSubgroupOf_right Y Z, AddSubgroup.relIndex_addSubgroupOf inf_le_right, ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right (X ⊓ Z)]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic.
-/
theorem relIndex_addSubgroupOf_inf (X Y Z : AddSubgroup V) :
    (X.addSubgroupOf Z).relIndex (Y.addSubgroupOf Z) = (X ⊓ Z).relIndex (Y ⊓ Z) := by
  rw [← AddSubgroup.inf_addSubgroupOf_right Y Z, AddSubgroup.relIndex_addSubgroupOf inf_le_right,
    ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right (X ⊓ Z)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  tauto

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => h.1 b a, fun a a' b => h.2.2 b a a', fun a b b' => h.2.1 b b' a⟩`.
-/
theorem bichar_swap {k : Type*} [Field k] {A B : Type*} [AddCommGroup A] [AddCommGroup B] {c : B → A → k}
    (h : IsBichar c) : IsBichar (fun a b => c b a) :=
  ⟨fun a b => h.1 b a, fun a a' b => h.2.2 b a a', fun a b b' => h.2.1 b b' a⟩

/- English proof (translation)
Establish `hsa : 0 < Real.sqrt a` using `Real.sqrt_pos.2 ha`. Establish `hsb : 0 < Real.sqrt b` using `Real.sqrt_pos.2 hb`. Establish `hbb : Real.sqrt b * Real.sqrt b = b` using `Real.mul_self_sqrt hb.le`. Rewrite using `[Real.sqrt_div ha.le, Real.sqrt_mul ha.le]`. Clear the denominators using the available nonvanishing facts.

Use polynomial arithmetic with `[hbb]`.
-/
theorem sqrt_div_mul_eq_sqrt_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt (a * b))⁻¹ * b = (Real.sqrt (a / b))⁻¹ := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
  field_simp
  nlinarith [hbb]

/- English proof (translation)
Introduce `V _ _ H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin θ hθ Xi hXi`. Take `⟨hbc, hheis⟩` from `heisenberg_unitary_holds V H α A B hH hA hB`. Establish `int0 : ∀ x ∈ Λ₀, ∀ y ∈ Λ₀, ∃ m : ℤ, altE H x y = m` using `fun x hx y hy => (semiCharBasic V H hH Λ₀ α g0.1).2.2 hx y hy`. Establish `int1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, ∃ m : ℤ, altE H x y = m` using `fun x hx y hy => (semiCharBasic V H hH Λ₁ α g1.1).2.2 hx y hy`. Establish `o1 : ∀ b : B, b ∈ Λ₀.addSubgroupOf B ↔ ∀ a ∈ Λ₀.addSubgroupOf A, cU H A B b a = 1`.

Introduce `b`. Simplify using `only [AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce `hb a ha`. Conclude with `(cU_eq_one_iff H A B b a).2 (int0 _ ha _ hb)`.

Introduce `h`. Conclude with `g0.2.2.2.2 b b.2 fun a ha haΛ => (cU_eq_one_iff H A B b ⟨a, ha⟩).1 (h ⟨a, ha⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using haΛ))`. Establish `o2 : ∀ b ∈ Λ₁.addSubgroupOf B, ∀ a ∈ Λ₁.addSubgroupOf A, cU H A B b a = 1`. Introduce `b hb a ha`. Rewrite `hb`, `ha` using `[AddSubgroup.mem_addSubgroupOf]`.

Conclude with `(cU_eq_one_iff H A B b a).2 (int1 _ ha _ hb)`. Establish `o3 : ∀ a : A, (∀ b ∈ Λ₁.addSubgroupOf B, cU H A B b a = 1) → a ∈ Λ₁.addSubgroupOf A`. Introduce `a h`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Conclude with `g1.2.2.2.1 a a.2 fun b hb hbΛ => (cU_eq_one_iff H A B ⟨b, hb⟩ a).1 (h ⟨b, hb⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hbΛ))`.

Establish `hfinB : (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B) ≠ 0`. Rewrite using `[relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ B)]`. Establish `e : Λ₀ ⊓ B ⊓ (Λ₁ ⊓ B) = Λ₀ ⊓ (Λ₁ ⊓ B)`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`.

The claim follows by propositional logic. Rewrite using `[e, AddSubgroup.inf_relIndex_right]`. Introduce `h0`. Conclude with `hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)`. Establish `hfinA : (Λ₀.addSubgroupOf A).relIndex (Λ₁.addSubgroupOf A) ≠ 0`.

Rewrite using `[relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ A)]`. Establish `e : Λ₀ ⊓ A ⊓ (Λ₁ ⊓ A) = Λ₀ ⊓ (Λ₁ ⊓ A)`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic.

Rewrite using `[e, AddSubgroup.inf_relIndex_right]`. Introduce `h0`. Conclude with `hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)`. Establish `hdual : (Λ₁.addSubgroupOf A).relIndex (Λ₀.addSubgroupOf A) = (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B)`. Use `hID ℂ B A (fun a b => cU H A B b a) (bichar_swap hbc) (Λ₁.addSubgroupOf B) (Λ₀.addSubgroupOf B) (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf A) ?_ ?_ ?_ hfinB` and prove the remaining obligations.

Introduce `a`. Conclude with `⟨fun ha b hb => o2 b hb a ha, fun h => o3 a h⟩`. Introduce `a ha b hb`. Conclude with `(o1 b).1 hb a ha`. Introduce `b hb h`.

Conclude with `(o1 b).2 h`. Take `⟨SA, hSA, hSAc⟩` from `repsG_exist _ _ hfinA`. Take `⟨SB, hSB, hSBc⟩` from `repsG_exist _ _ hfinB`. Establish `hSBne : (SB.card : ℂ) ≠ 0` using `by rw [hSBc]; exact_mod_cast hfinB`. Take `⟨h, hsum⟩` from `hMv ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis (Λ₀.addSubgroupOf A) (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf B) (Λ₁.addSubgroupOf B) θ Xi hXi o1 o2 (fun a _ h => o3 a h) SA SB hSA hSB hSBne`.

Use `⟨h, ?_, ?_⟩` and prove the remaining obligations. Unfold `volA`. Establish `h1 : 0 < (Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A)`. Rewrite using `[← relIndex_addSubgroupOf_inf]`. Conclude with `Nat.pos_of_ne_zero hfinA`.

Establish `h2 : 0 < (Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A)`. Rewrite using `[← relIndex_addSubgroupOf_inf, hdual]`. Conclude with `Nat.pos_of_ne_zero hfinB`. Check the signs of the components of the expression. Set `f : A × B → V` to `fun p => (p.1 : V) + (p.2 : V)`.

Establish `key : ∀ p ∈ SA ×ˢ SB, ∀ q ∈ SA ×ˢ SB, f p - f q ∈ Λ₀ → p = q`. Introduce `p hp q hq hpq`. Rewrite `hp`, `hq` using `[Finset.mem_product]`. Establish `e : f p - f q = ((p.1 : V) - q.1) + ((p.2 : V) - q.2)` using `by simp only [f]; abel`. Rewrite `hpq` using `[e]`.

Establish `ha : ((p.1 : V) - q.1) ∈ Λ₀` using `g0.2.2.1 _ (A.sub_mem p.1.2 q.1.2) _ (B.sub_mem p.2.2 q.2.2) hpq`. Establish `e1 : p.1 = q.1` using `hSA.2.1 _ hp.1 _ hq.1 (by simpa [AddSubgroup.mem_addSubgroupOf] using ha)`. Establish `hb : ((p.2 : V) - q.2) ∈ Λ₀`. Use `Λ₀.sub_mem hpq ha` as an intermediate fact. Simplify using `using this`.

Establish `e2 : p.2 = q.2` using `hSB.2.1 _ hp.2 _ hq.2 (by simpa [AddSubgroup.mem_addSubgroupOf] using hb)`. Conclude with `Prod.ext e1 e2`. Establish `hinj : Set.InjOn f (SA ×ˢ SB : Finset (A × B))`. Introduce `p hp q hq hpq`. Conclude with `key p hp q hq (by rw [hpq, sub_self]; exact Λ₀.zero_mem)`.

Set `S : Finset V` to `(SA ×ˢ SB).image f`. Establish `hS : IsReps Λ₀ Λ₁ S`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hx`.

Rewrite `hp` using `[Finset.mem_product]`. Establish `h1` using `hSA.1 _ hp.1`. Establish `h2` using `hSB.1 _ hp.2`. Rewrite `h1`, `h2` using `[AddSubgroup.mem_addSubgroupOf]`. Conclude with `Λ₁.add_mem h1 h2`.

Introduce `x hx y hy hxy`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[key p hp q hq hxy]`. Introduce `y hy`.

Take `⟨y1, hy1, y2, hy2, rfl⟩` from `AddSubgroup.mem_sup.1 (g1.2.1 hy)`. Take `⟨a, ha, ha'⟩` from `hSA.2.2 ⟨y1, hy1.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy1.1)`. Take `⟨b, hb, hb'⟩` from `hSB.2.2 ⟨y2, hy2.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy2.1)`. Use `⟨f (a, b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha, hb⟩), ?_⟩` and prove the remaining obligations. Rewrite `ha'`, `hb'` using `[AddSubgroup.mem_addSubgroupOf]`.

Establish `e : y1 + y2 - f (a, b) = (y1 - a) + (y2 - b)` using `by simp only [f]; abel`. Rewrite using `[e]`. Conclude with `Λ₀.add_mem (by simpa using ha') (by simpa using hb')`. Establish `hcard : S.card = SA.card * SB.card`. Rewrite using `[Finset.card_image_of_injOn hinj, Finset.card_product]`.

Establish `hn : relIdx Λ₀ Λ₁ = SA.card * SB.card`. Rewrite using `[← hcard]`. Conclude with `((repsExist V Λ₀ Λ₁ hfin).2 S hS).symm`. Use function extensionality and compare the values at `z`. Rewrite using `[interReps V H hH Λ₀ Λ₁ α g1.1 θ hθ S hS z]`.

Establish `hsumU : sumU H α S θ z = (SB.card : ℂ) * Xi ⟨_, h⟩ z`. Use `congrFun hsum z` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[← this]`. Unfold `sumU`.

Rewrite using `[Finset.sum_image hinj, Finset.sum_product]`. Use `Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `h1` using `hSA.1 _ ha`. Establish `h2` using `hSB.1 _ hb`. Rewrite `h1`, `h2` using `[AddSubgroup.mem_addSubgroupOf]`.

Simplify using `only [wA, wB, wU, LinearMap.coe_mk, AddHom.coe_mk, f]`. Conclude with `(semiHom V H hH Λ₁ α g1.1 _ h1 _ h2 θ z).symm`. Rewrite using `[hsumU, hn]`. Establish `hA' : ((Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A) : ℝ) = SA.card`. Rewrite using `[hSAc, relIndex_addSubgroupOf_inf]`.

Establish `hB' : ((Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A) : ℝ) = SB.card`. Rewrite using `[hSBc, ← hdual, relIndex_addSubgroupOf_inf]`. Establish `hpa : (0 : ℝ) < SA.card` using `by rw [hSAc]; exact_mod_cast Nat.pos_of_ne_zero hfinA`. Establish `hpb : (0 : ℝ) < SB.card` using `by rw [hSBc]; exact_mod_cast Nat.pos_of_ne_zero hfinB`. Establish `hv : volA A Λ₀ Λ₁ = (SA.card : ℝ) / SB.card` using `by unfold volA; rw [hA', hB']`.

Rewrite using `[hv, ← sqrt_div_mul_eq_sqrt_mul _ _ hpa hpb]`. Simplify using `only [Pi.smul_apply, Complex.real_smul, Nat.cast_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem MovesU_of (hMv : Moves) (hID : IndexDual) : MovesU := by
  intro V _ _ H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin θ hθ Xi hXi
  classical
  obtain ⟨hbc, hheis⟩ := heisenberg_unitary_holds V H α A B hH hA hB
  have int0 : ∀ x ∈ Λ₀, ∀ y ∈ Λ₀, ∃ m : ℤ, altE H x y = m :=
    fun x hx y hy => (semiCharBasic V H hH Λ₀ α g0.1).2.2 hx y hy
  have int1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, ∃ m : ℤ, altE H x y = m :=
    fun x hx y hy => (semiCharBasic V H hH Λ₁ α g1.1).2.2 hx y hy
  have o1 : ∀ b : B, b ∈ Λ₀.addSubgroupOf B ↔ ∀ a ∈ Λ₀.addSubgroupOf A, cU H A B b a = 1 := by
    intro b
    simp only [AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hb a ha
      exact (cU_eq_one_iff H A B b a).2 (int0 _ ha _ hb)
    · intro h
      exact g0.2.2.2.2 b b.2 fun a ha haΛ =>
        (cU_eq_one_iff H A B b ⟨a, ha⟩).1 (h ⟨a, ha⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using haΛ))
  have o2 : ∀ b ∈ Λ₁.addSubgroupOf B, ∀ a ∈ Λ₁.addSubgroupOf A, cU H A B b a = 1 := by
    intro b hb a ha
    rw [AddSubgroup.mem_addSubgroupOf] at hb ha
    exact (cU_eq_one_iff H A B b a).2 (int1 _ ha _ hb)
  have o3 : ∀ a : A, (∀ b ∈ Λ₁.addSubgroupOf B, cU H A B b a = 1) → a ∈ Λ₁.addSubgroupOf A := by
    intro a h
    rw [AddSubgroup.mem_addSubgroupOf]
    exact g1.2.2.2.1 a a.2 fun b hb hbΛ =>
      (cU_eq_one_iff H A B ⟨b, hb⟩ a).1 (h ⟨b, hb⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hbΛ))
  have hfinB : (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B) ≠ 0 := by
    rw [relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ B)]
    have e : Λ₀ ⊓ B ⊓ (Λ₁ ⊓ B) = Λ₀ ⊓ (Λ₁ ⊓ B) := by
      ext x; simp only [AddSubgroup.mem_inf]; tauto
    rw [e, AddSubgroup.inf_relIndex_right]
    intro h0
    exact hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  have hfinA : (Λ₀.addSubgroupOf A).relIndex (Λ₁.addSubgroupOf A) ≠ 0 := by
    rw [relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ A)]
    have e : Λ₀ ⊓ A ⊓ (Λ₁ ⊓ A) = Λ₀ ⊓ (Λ₁ ⊓ A) := by
      ext x; simp only [AddSubgroup.mem_inf]; tauto
    rw [e, AddSubgroup.inf_relIndex_right]
    intro h0
    exact hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)

  have hdual : (Λ₁.addSubgroupOf A).relIndex (Λ₀.addSubgroupOf A) =
      (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B) := by
    refine hID ℂ B A (fun a b => cU H A B b a) (bichar_swap hbc) (Λ₁.addSubgroupOf B) (Λ₀.addSubgroupOf B)
      (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf A) ?_ ?_ ?_ hfinB
    · intro a
      exact ⟨fun ha b hb => o2 b hb a ha, fun h => o3 a h⟩
    · intro a ha b hb
      exact (o1 b).1 hb a ha
    · intro b hb h
      exact (o1 b).2 h
  obtain ⟨SA, hSA, hSAc⟩ := repsG_exist _ _ hfinA
  obtain ⟨SB, hSB, hSBc⟩ := repsG_exist _ _ hfinB
  have hSBne : (SB.card : ℂ) ≠ 0 := by rw [hSBc]; exact_mod_cast hfinB
  obtain ⟨h, hsum⟩ := hMv ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf B) (Λ₁.addSubgroupOf B) θ Xi hXi
    o1 o2 (fun a _ h => o3 a h) SA SB hSA hSB hSBne
  refine ⟨h, ?_, ?_⟩
  · unfold volA
    have h1 : 0 < (Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A) := by
      rw [← relIndex_addSubgroupOf_inf]; exact Nat.pos_of_ne_zero hfinA
    have h2 : 0 < (Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A) := by
      rw [← relIndex_addSubgroupOf_inf, hdual]; exact Nat.pos_of_ne_zero hfinB
    positivity

  let f : A × B → V := fun p => (p.1 : V) + (p.2 : V)
  have key : ∀ p ∈ SA ×ˢ SB, ∀ q ∈ SA ×ˢ SB, f p - f q ∈ Λ₀ → p = q := by
    intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : f p - f q = ((p.1 : V) - q.1) + ((p.2 : V) - q.2) := by simp only [f]; abel
    rw [e] at hpq
    have ha : ((p.1 : V) - q.1) ∈ Λ₀ :=
      g0.2.2.1 _ (A.sub_mem p.1.2 q.1.2) _ (B.sub_mem p.2.2 q.2.2) hpq
    have e1 : p.1 = q.1 := hSA.2.1 _ hp.1 _ hq.1 (by simpa [AddSubgroup.mem_addSubgroupOf] using ha)
    have hb : ((p.2 : V) - q.2) ∈ Λ₀ := by
      have := Λ₀.sub_mem hpq ha
      simpa using this
    have e2 : p.2 = q.2 := hSB.2.1 _ hp.2 _ hq.2 (by simpa [AddSubgroup.mem_addSubgroupOf] using hb)
    exact Prod.ext e1 e2
  have hinj : Set.InjOn f (SA ×ˢ SB : Finset (A × B)) := by
    intro p hp q hq hpq
    exact key p hp q hq (by rw [hpq, sub_self]; exact Λ₀.zero_mem)
  let S : Finset V := (SA ×ˢ SB).image f
  have hS : IsReps Λ₀ Λ₁ S := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product] at hp
      have h1 := hSA.1 _ hp.1
      have h2 := hSB.1 _ hp.2
      rw [AddSubgroup.mem_addSubgroupOf] at h1 h2
      exact Λ₁.add_mem h1 h2
    · intro x hx y hy hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [key p hp q hq hxy]
    · intro y hy
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := AddSubgroup.mem_sup.1 (g1.2.1 hy)
      obtain ⟨a, ha, ha'⟩ := hSA.2.2 ⟨y1, hy1.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy1.1)
      obtain ⟨b, hb, hb'⟩ := hSB.2.2 ⟨y2, hy2.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy2.1)
      refine ⟨f (a, b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha, hb⟩), ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf] at ha' hb'
      have e : y1 + y2 - f (a, b) = (y1 - a) + (y2 - b) := by simp only [f]; abel
      rw [e]
      exact Λ₀.add_mem (by simpa using ha') (by simpa using hb')
  have hcard : S.card = SA.card * SB.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  have hn : relIdx Λ₀ Λ₁ = SA.card * SB.card := by
    rw [← hcard]; exact ((repsExist V Λ₀ Λ₁ hfin).2 S hS).symm
  funext z
  rw [interReps V H hH Λ₀ Λ₁ α g1.1 θ hθ S hS z]
  have hsumU : sumU H α S θ z = (SB.card : ℂ) * Xi ⟨_, h⟩ z := by
    have := congrFun hsum z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    unfold sumU
    rw [Finset.sum_image hinj, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have h1 := hSA.1 _ ha
    have h2 := hSB.1 _ hb
    rw [AddSubgroup.mem_addSubgroupOf] at h1 h2
    simp only [wA, wB, wU, LinearMap.coe_mk, AddHom.coe_mk, f]
    exact (semiHom V H hH Λ₁ α g1.1 _ h1 _ h2 θ z).symm
  rw [hsumU, hn]
  have hA' : ((Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A) : ℝ) = SA.card := by
    rw [hSAc, relIndex_addSubgroupOf_inf]
  have hB' : ((Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A) : ℝ) = SB.card := by
    rw [hSBc, ← hdual, relIndex_addSubgroupOf_inf]
  have hpa : (0 : ℝ) < SA.card := by rw [hSAc]; exact_mod_cast Nat.pos_of_ne_zero hfinA
  have hpb : (0 : ℝ) < SB.card := by rw [hSBc]; exact_mod_cast Nat.pos_of_ne_zero hfinB
  have hv : volA A Λ₀ Λ₁ = (SA.card : ℝ) / SB.card := by unfold volA; rw [hA', hB']
  rw [hv, ← sqrt_div_mul_eq_sqrt_mul _ _ hpa hpb]
  simp only [Pi.smul_apply, Complex.real_smul, Nat.cast_mul]
  push_cast
  ring

end Moves

end Formalism.L2.PairingIndexBounds.Mv
