import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} = ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c}`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, c, hc, rfl⟩`.

Establish `hMz : (0 : ℤ) < M` using `by exact_mod_cast hM`. Establish `h0 : 0 ≤ z % (M : ℤ)` using `Int.emod_nonneg z hMz.ne'`. Establish `h1 : z % (M : ℤ) < M` using `Int.emod_lt_of_pos z hMz`. Establish `hdiv` using `congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)`. Simplify using `only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv`.

Use `⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩` and prove the remaining obligations. Establish `hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h0]`. Simplify using `only [hr]`. Take the linear combination `-hdiv`.

Introduce and unpack `⟨r, c, hc, hx⟩`. Use `⟨((r : ℕ) : ℤ), c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_natCast]`. Take the linear combination `hx`. Rewrite using `[key]`.

Conclude with `isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)`.
-/
theorem isClosed_int_add_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (M : ℕ) (hM : 0 < M) (hcl : IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c}) :
    IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} := by
  have key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} =
      ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨z, c, hc, rfl⟩
      have hMz : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg z hMz.ne'
      have h1 : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMz
      have hdiv := congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv
      refine ⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩
      have hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      simp only [hr]
      linear_combination -hdiv
    · rintro ⟨r, c, hc, hx⟩
      refine ⟨((r : ℕ) : ℤ), c, hc, ?_⟩
      rw [Int.cast_natCast]
      linear_combination hx
  rw [key]
  exact isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)

/- English proof (translation)
Establish `hSc : ∀ M : ℕ, 0 < M → IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c}` using `fun M hM => isClosed_int_add_mul O M hM (hcl M hM)`. Establish `hL : Continuous fun r : β → A => a - ∑ i, r i * w i` using `continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)`. Set `t : ℕ → Set (β → A)` to `fun m => (⋂ i, (fun r : β → A => r i) ⁻¹' {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩ (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}`. Establish `htc : ∀ m, IsClosed (t m)` using `fun m => (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter ((hcl (m + 1) m.succ_pos).preimage hL)`. Establish `hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A))` using `isCompact_univ_pi fun _ => hO`.

Establish `hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty`. Introduce `u`. Establish `hNpos : 0 < ∏ m ∈ u, (m + 1)` using `Finset.prod_pos fun m _ => m.succ_pos`. Take `⟨z, c, hc, hac⟩` from `ha _ hNpos`. Use `⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_iInter]`. Introduce `m hm`. Take `⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1)` from `Finset.dvd_prod_of_mem _ hm`. Rewrite `hac` using `[hk]`. Simplify using `only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]`.

Use `⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at hac ⊢`. Take the linear combination `hac`. Take `⟨r, -, hr⟩` from `hs.inter_iInter_nonempty t htc hne`. Simplify using `only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr`.

Establish `hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1` using `fun M hM => ⟨M - 1, by omega⟩`. Use `⟨r, fun i M hM => ?_, ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `hpred M hM`. Conclude with `(hr m).1 i`. Establish `h0 : a - ∑ i, r i * w i = 0` using `hz _ fun M hM => by`.

Take `⟨m, rfl⟩` from `hpred M hM`. Conclude with `(hr m).2`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem exists_sum_of_approx {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (hO : IsCompact (O : Set A))
    (hcl : ∀ M : ℕ, 0 < M → IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c})
    (hz : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c ∈ O, a = (M : A) * c) → a = 0)
    {β : Type} [Fintype β] (w : β → A) (a : A)
    (ha : ∀ M : ℕ, 0 < M → ∃ (z : β → ℤ) (c : A), c ∈ O ∧ a = ∑ i, (z i : A) * w i + (M : A) * c) :
    ∃ r : β → A, (∀ i, ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r i = (z : A) + (M : A) * c) ∧
      a = ∑ i, r i * w i := by
  classical
  have hSc : ∀ M : ℕ, 0 < M →
      IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} :=
    fun M hM => isClosed_int_add_mul O M hM (hcl M hM)
  have hL : Continuous fun r : β → A => a - ∑ i, r i * w i :=
    continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  let t : ℕ → Set (β → A) := fun m =>
    (⋂ i, (fun r : β → A => r i) ⁻¹'
      {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩
    (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter
      ((hcl (m + 1) m.succ_pos).preimage hL)
  have hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A)) := isCompact_univ_pi fun _ => hO
  have hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty := by
    intro u
    have hNpos : 0 < ∏ m ∈ u, (m + 1) := Finset.prod_pos fun m _ => m.succ_pos
    obtain ⟨z, c, hc, hac⟩ := ha _ hNpos
    refine ⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩
    simp only [Set.mem_iInter]
    intro m hm
    obtain ⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1) := Finset.dvd_prod_of_mem _ hm
    rw [hk] at hac
    simp only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩
    push_cast at hac ⊢
    linear_combination hac
  obtain ⟨r, -, hr⟩ := hs.inter_iInter_nonempty t htc hne
  simp only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr
  have hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1 := fun M hM => ⟨M - 1, by omega⟩
  refine ⟨r, fun i M hM => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hpred M hM
    exact (hr m).1 i
  · have h0 : a - ∑ i, r i * w i = 0 := hz _ fun M hM => by
      obtain ⟨m, rfl⟩ := hpred M hM
      exact (hr m).2
    exact sub_eq_zero.mp h0

private def intAdeles (F : Type) [Field F] [NumberField F] :
    Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' ha v := neg_mem (ha v)

/- English proof (translation)
Introduce `F _ _ β _ ω a ha`. Take `⟨hcomp, hclM, hzero, -, -, -⟩` from `GlobalTheory.T.integralFiniteAdele_compact_closed_multiples F`. Establish `hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F)`. Introduce `x`. Use `conv_lhs => rw [← ω.sum_repr x]`.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]`. Use `exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_` and prove the remaining obligations. Introduce `M hM`. Take `⟨x, c, hc, hac⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha`. Use `⟨fun i => ω.repr x i, c, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[hac, hexp, nsmul_eq_mul]`.
-/
theorem exists_sum_integralBasis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ r : β → FiniteAdeleRing (𝓞 F) F, (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) ∧ a = ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) := by
  intro F _ _ β _ ω a ha
  obtain ⟨hcomp, hclM, hzero, -, -, -⟩ := GlobalTheory.T.integralFiniteAdele_compact_closed_multiples F
  have hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) =
      ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F) := by
    intro x
    conv_lhs => rw [← ω.sum_repr x]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_
  intro M hM
  obtain ⟨x, c, hc, hac⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha
  refine ⟨fun i => ω.repr x i, c, hc, ?_⟩
  rw [hac, hexp, nsmul_eq_mul]

end GlobalTheory.ClassFin
