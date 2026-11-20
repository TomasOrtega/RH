import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyHamilton
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterApplyIdempotentNatLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterEqZeroOfIsNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIdeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemisimpleRepOfIsSemisimpleRingRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTraceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTraceStatement
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

/- English proof (translation)
Use `GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)` and prove the remaining obligations. Take `⟨p, hp, -, hT⟩` from `cayleyHamilton k R d T h x`. Conclude with `⟨p, hp, hnd _ hT⟩`. Use `hnd x fun y => ?_` and prove the remaining obligations. Rewrite using `[show T (x * y) = T (y * x) from h.comm x y]`.

Conclude with `GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)`. Establish `hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a` using `fun i => by`. Take `⟨⟨a, -, ha⟩, h0⟩` from `GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)`. Use `⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩` and prove the remaining obligations. Rewrite using `[ha, h', Nat.cast_zero]`.

Use `choose a ha1 ha using hv`. Take `⟨⟨s, hs, hsT⟩, -⟩` from `GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum`. Establish `h1 : ((∑ i, a i : ℕ) : k) = s`. Rewrite using `[← hsT, map_sum]`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl fun i _ => (ha i).symm`. Establish `h2 : ∑ i, a i = s` using `by exact_mod_cast h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

/- English proof (translation)
The claim follows from `TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x`.
-/
theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

/- English proof (translation)
Use `⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, fun a => ?_⟩` and prove the remaining obligations. Establish `: (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]`.

Conclude with `Submodule.liftQ_apply _ _ _`.
-/
theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

/- English proof (translation)
Take `⟨T', hT'g, hT'⟩` from `exists_linear_extension Γ k d T hT`. Establish `hc : ∀ x y, T' (x * y) = T' (y * x)` using `hT'.comm`. Set `I` to `traceKer T' hc`. Set `f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient` to `RingCon.mkₐ k I.ringCon`. Establish `hf : Function.Surjective f` using `fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩`.

Establish `hk : ∀ x, f x = 0 ↔ x ∈ I` using `fun x => by`. Rewrite using `[TwoSidedIdeal.mem_iff, ← RingCon.eq]`. Both sides reduce to the same expression. Take `⟨S, hS⟩` from `exists_descend f.toLinearMap hf T' fun a ha => by`. Simplify using `using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1`.

Establish `hS1 : ∀ a, S (f a) = T' a` using `hS`. Establish `hS' : IsPsChar d (fun x => S x)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show S 1 = d`. Rewrite using `[← map_one f, hS1]`.

Conclude with `hT'.one`. Introduce `x y`. Take `⟨a, rfl⟩` from `hf x`. Take `⟨b, rfl⟩` from `hf y`. Use `show S (f a * f b) = S (f b * f a)`.

Rewrite using `[← map_mul, ← map_mul, hS1, hS1]`. Conclude with `hc a b`. Introduce `x choose a ha using fun i => hf (x i)`. Establish `hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i)` using `funext fun i => (ha i).symm`. Rewrite using `[hx, alt_comp_monoidHom]`.

Establish `he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g`. Use function extensionality and compare the values at `fun g => hS1 g`. Rewrite using `[he]`. Conclude with `hT'.alt_eq_zero a`. Establish `hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0`.

Introduce `x hx`. Take `⟨a, rfl⟩` from `hf x`. Use `(hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)` and prove the remaining obligations. Rewrite using `[← hS1, map_mul]`. Conclude with `hx (f b)`.

Take `⟨hfin, hss⟩` from `finite_semisimple k _ d S hS' hnd`. Take `⟨N, n, hn, ⟨e⟩⟩` from `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient`. Set `τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k` to `S ∘ₗ e.symm.toLinearMap`. Establish `hτ : ∀ x, τ x = S (e.symm x)` using `fun x => rfl`. Take `⟨c, hcτ⟩` from `GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by`.

Rewrite using `[hτ, hτ, map_mul e.symm, map_mul e.symm]`. Conclude with `hS'.comm _ _`. Establish `hcn : ∀ i, ∃ m : ℕ, c i = m`. Introduce `i`. Use `haveI := hn i`.

Set `E : Π j, Matrix (Fin (n j)) (Fin (n j)) k` to `Pi.single i (Matrix.single 0 0 1)`. Establish `hE : IsIdempotentElem E`. Unfold `IsIdempotentElem`. Use `ext1 j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[E, Matrix.single_mul_single_same]`. Simplify using `[E, hj]`. Establish `hτE : τ E = c i`. Rewrite using `[hcτ, Finset.sum_eq_single i]`.

Simplify using `[E, Matrix.trace_single_eq_same]`. Introduce `j _ hj`. Simplify using `[E, hj]`. Simplify using the standard rewrite rules. Take `⟨⟨m, -, hm⟩, -⟩` from `GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)`.

Conclude with `⟨m, hτE.symm.trans hm⟩`. Use `choose m hm using hcn`. Establish `hsum : ∑ i, m i * n i = d`. Establish `h1 : τ 1 = d` using `by rw [hτ, map_one]; exact hS'.one`. Rewrite `h1` using `[hcτ]`.

Simplify using `only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1`. Conclude with `h1` after adjusting the coercions. Take `⟨ρ₀, hρ₀⟩` from `GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum`. Set `g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k` to `ρ₀.comp e.toAlgHom`. Set `ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k` to `g.comp f`.

Establish `htr : ∀ a, (ρ a).trace = T' a` using `fun a => by show (ρ₀ (e (f a))).trace = _`. Rewrite using `[hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]`. Simplify using `[hm]`. Establish `hrange : IsSemisimpleRing ρ.range`. Establish `: ρ.range = g.range`.

Rewrite using `[AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]`. Rewrite using `[this]`. Conclude with `RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _)`. Use `⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange, fun x => ?_⟩` and prove the remaining obligations. Use `show (ρ (MonoidAlgebra.of k Γ x)).trace = T x`.

Rewrite using `[htr, hT'g]`.
-/
theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
