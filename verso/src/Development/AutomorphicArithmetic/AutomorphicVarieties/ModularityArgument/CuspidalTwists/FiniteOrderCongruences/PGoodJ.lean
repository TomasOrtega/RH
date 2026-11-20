import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace GoodJ

/- English proof (translation)
Introduce `k` and use `hκ k fun φ => by have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) refine absurd ?_ h rw [ComplexEmbedding.isReal_iff] ext x simp`.
-/
theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

/- English proof (translation)
Establish `e` using `((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq`. Rewrite `e` using `[CG.twist_mk]`. Rewrite using `[e]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [(InfType.expo_of_infType K κ).1 m (isAlg_of_pos hκ) τ]`.

Apply the tactic sequence `try ring`.
-/
theorem infChar_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (P : CuspSub K n)
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) (τ : K →+* ℂ) :
    (CG.mk (P.twist κ)).infChar τ = ((CG.mk P).infChar τ).map (· + ((m τ : ℤ) : ℂ)) := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [(InfType.expo_of_infType K κ).1 m (isAlg_of_pos hκ) τ]
  try ring

end GoodJ

/- English proof (translation)
Introduce `K _ _ _ hK π hreg m hm`. Set `S : Finset ℂ` to `Finset.univ.biUnion fun τ : K →+* ℂ => (((CG.mk π).infChar τ).toFinset ×ˢ ((CG.mk π).infChar (ComplexEmbedding.conjugate τ)).toFinset).image fun p => p.1 - p.2`. Establish `h2 : ∀ τ : K →+* ℂ, ((CG.mk π).infChar τ).toFinset.card ≤ 2` using `fun τ => (Multiset.toFinset_card_le _).trans (CG.card_infChar _ τ).le`. Establish `hS : S.card ≤ 8`. Use `(Finset.card_biUnion_le_card_mul _ _ 4 fun τ _ => ?_).trans ?_` and prove the remaining obligations.

Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_product]`. Establish `a1` using `h2 τ`. Establish `a2` using `h2 (ComplexEmbedding.conjugate τ)`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[Finset.card_univ, NumberField.Embeddings.card K ℂ, hK]`. Establish `hinj : Function.Injective fun j : ℕ => ((2 * m * j : ℕ) : ℂ)`. Introduce `a b h`. Establish `h' : 2 * m * a = 2 * m * b` using `Nat.cast_injective h`. Conclude with `Nat.eq_of_mul_eq_mul_left (by omega) h'`.

Establish `hcard : S.card < ((Finset.Icc 1 9).image fun j : ℕ => ((2 * m * j : ℕ) : ℂ)).card`. Rewrite using `[Finset.card_image_of_injective _ hinj, Nat.card_Icc]`. Use linear arithmetic over natural numbers and integers. Take `⟨_, hz, hzS⟩` from `Finset.exists_mem_notMem_of_card_lt_card hcard`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.1 hz`.

Rewrite `hj` using `[Finset.mem_Icc]`. Use `⟨j, hj.1, hj.2, fun Y a e hY ha ha' => ?_⟩` and prove the remaining obligations. Establish `eM` using `GoodJ.infChar_twist π hY e`. Establish `eM'` using `GoodJ.infChar_twist π hY (ComplexEmbedding.conjugate e)`. Rewrite `eM` using `[ha]`.

Rewrite `eM'` using `[ha']`. Use `⟨(CG.mk (π.twist Y)).infChar e, (CG.mk (π.twist Y)).infChar (ComplexEmbedding.conjugate e), ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) e, ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) (ComplexEmbedding.conjugate e), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `CG.card_infChar (CG.mk (π.twist Y)) e`. Rewrite `h1` using `[h0]`.

Simplify using `at h1`. Rewrite using `[Multiset.nodup_add, eM, eM']`. Use `⟨(hreg e).1.map (add_left_injective _), (hreg _).1.map (add_left_injective _), Multiset.disjoint_left.2 fun {z} hz hz' => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨x', hx', hxx⟩` from `Multiset.mem_map.1 hz'`.

Use `hzS (Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, Finset.mem_image.2 ⟨(x, x'), Finset.mem_product.2 ⟨Multiset.mem_toFinset.2 hx, Multiset.mem_toFinset.2 hx'⟩, ?_⟩⟩)` and prove the remaining obligations. Move the coercions through the operations in `at hxx ⊢`. Take the linear combination `-hxx`. Introduce `z hz`. Break down `Multiset.mem_add.1 hz with hz | hz` into its components or cases.

Rewrite `hz` using `[eM]`. Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨k, rfl⟩` from `(hreg e).2 x hx`. Conclude with `⟨k - ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩`. Rewrite `hz` using `[eM']`.

Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨k, rfl⟩` from `(hreg _).2 x hx`. Conclude with `⟨k + ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩`.
-/
theorem goodJ : GoodJ := by
  intro K _ _ _ hK π hreg m hm
  classical
  let S : Finset ℂ := Finset.univ.biUnion fun τ : K →+* ℂ =>
    (((CG.mk π).infChar τ).toFinset ×ˢ ((CG.mk π).infChar (ComplexEmbedding.conjugate τ)).toFinset).image
      fun p => p.1 - p.2
  have h2 : ∀ τ : K →+* ℂ, ((CG.mk π).infChar τ).toFinset.card ≤ 2 := fun τ =>
    (Multiset.toFinset_card_le _).trans (CG.card_infChar _ τ).le
  have hS : S.card ≤ 8 := by
    refine (Finset.card_biUnion_le_card_mul _ _ 4 fun τ _ => ?_).trans ?_
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      have a1 := h2 τ
      have a2 := h2 (ComplexEmbedding.conjugate τ)
      nlinarith
    · rw [Finset.card_univ, NumberField.Embeddings.card K ℂ, hK]
  have hinj : Function.Injective fun j : ℕ => ((2 * m * j : ℕ) : ℂ) := by
    intro a b h
    have h' : 2 * m * a = 2 * m * b := Nat.cast_injective h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h'
  have hcard : S.card < ((Finset.Icc 1 9).image fun j : ℕ => ((2 * m * j : ℕ) : ℂ)).card := by
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  obtain ⟨_, hz, hzS⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
  rw [Finset.mem_Icc] at hj
  refine ⟨j, hj.1, hj.2, fun Y a e hY ha ha' => ?_⟩
  have eM := GoodJ.infChar_twist π hY e
  have eM' := GoodJ.infChar_twist π hY (ComplexEmbedding.conjugate e)
  rw [ha] at eM
  rw [ha'] at eM'
  refine ⟨(CG.mk (π.twist Y)).infChar e, (CG.mk (π.twist Y)).infChar (ComplexEmbedding.conjugate e),
    ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) e,
    ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) (ComplexEmbedding.conjugate e), ?_, ?_, ?_⟩
  · intro h0
    have h1 := CG.card_infChar (CG.mk (π.twist Y)) e
    rw [h0] at h1
    simp at h1
  · rw [Multiset.nodup_add, eM, eM']
    refine ⟨(hreg e).1.map (add_left_injective _), (hreg _).1.map (add_left_injective _),
      Multiset.disjoint_left.2 fun {z} hz hz' => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨x', hx', hxx⟩ := Multiset.mem_map.1 hz'
    refine hzS (Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, Finset.mem_image.2
      ⟨(x, x'), Finset.mem_product.2 ⟨Multiset.mem_toFinset.2 hx, Multiset.mem_toFinset.2 hx'⟩, ?_⟩⟩)
    push_cast at hxx ⊢
    linear_combination -hxx
  · intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · rw [eM] at hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      obtain ⟨k, rfl⟩ := (hreg e).2 x hx
      exact ⟨k - ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩
    · rw [eM'] at hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      obtain ⟨k, rfl⟩ := (hreg _).2 x hx
      exact ⟨k + ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩

end UpperTheory.V.Cu2

end
