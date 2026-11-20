import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.FrobKerDim

/- English proof (translation)
Introduce `q K H _ _ _ _ hq`. Use `set J := frobKerIdeal q K H with hJ`. Use `set ε := Bialgebra.counitAlgHom K H with hε`. Use `set mk := Ideal.Quotient.mkₐ K J with hmk`. Establish `hJI : ∀ a ∈ J, ε a = 0` using `fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha`.

Use `set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ`. Establish `hεQmk : ∀ a, εQ (mk a) = ε a` using `fun a => rfl`. Establish `hmks : Function.Surjective mk` using `Ideal.Quotient.mkₐ_surjective K J`. Use `haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks`. Use `haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance`.

Establish `hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z`. Introduce `z hz`. Take `⟨a, rfl⟩` from `hmks z`. Use `⟨a, ?_, rfl⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[RingHom.mem_ker]`.

Rewrite using `[← hεQmk]`. Conclude with `hz`. Establish `hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0`. Introduce `z hz`. Take `⟨a, ha, rfl⟩` from `hkerQ z hz`.

Rewrite using `[← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)`. Establish `hnil : IsNilpotent (RingHom.ker εQ)`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `f hf`.

Conclude with `⟨q, hpowQ f hf⟩`. Use `haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)`. Use `set d := Module.finrank K (AugCot ε) with hd`. Set `b` to `Module.finBasis K (AugCot ε)`. Use `choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)`.

Establish `hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i`. Introduce `l`. Simplify using `[map_sum, hx]`. Establish `hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε`. Introduce `l`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (x i).2`. Establish `hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2`. Introduce `a ha`.

Use `⟨b.repr (AugCot.d ε a), ?_⟩` and prove the remaining obligations. Establish `h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0`. Rewrite using `[map_sub, hsum, b.sum_repr, sub_self]`. Rewrite `h1` using `[AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero]`. Then use the resulting hypothesis. Set `y : Fin d → H ⧸ J` to `fun i => mk (x i)`.

Establish `hy : ∀ i, y i ∈ RingHom.ker εQ` using `fun i => by`. Rewrite using `[RingHom.mem_ker, hεQmk]`. Conclude with `(x i).2`. Establish `hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `a ha`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Conclude with `ha`. Establish `hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2`. Introduce `z hz`.

Take `⟨a, ha, rfl⟩` from `hkerQ z hz`. Take `⟨l, hl⟩` from `hspanH a ha`. Use `⟨l, ?_⟩` and prove the remaining obligations. Establish `h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2)` using `Ideal.mem_map_of_mem _ hl`. Rewrite `h1` using `[Ideal.map_pow]`.

Establish `h2` using `Ideal.pow_right_mono hmapI 2 h1`. Simplify `h2` using `[y, map_sub, map_sum, map_smul]`. Establish `hsurj` using `GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan`. Establish `hyq : ∀ i, y i ^ q = 0` using `fun i => hpowQ _ (hy i)`. Set `mon : (Fin d → Fin q) → H ⧸ J` to `fun e => ∏ i, y i ^ (e i : ℕ)`.

Establish `htop : Submodule.span K (Set.range mon) = ⊤`. Establish `hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon)`. Introduce `P`. Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a`.

Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), ← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Distinguish the cases in `h : ∀ i, u i < q`. Conclude with `Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩`. Use `push_neg at h`.

Take `⟨i, hi⟩` from `h`. Establish `h0 : y i ^ u i = 0` using `pow_eq_zero_of_le hi (hyq i)`. Rewrite using `[Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]`. Conclude with `Submodule.zero_mem _`. Consider the case `add P Q hP hQ => rw [map_add]`.

Conclude with `Submodule.add_mem _ hP hQ`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `hsurj z`. Conclude with `hall P`. Establish `h1` using `finrank_range_le_card (R := K) (b := mon)`.

Rewrite `h1` using `[Set.finrank, htop, finrank_top]`. Simplify `h1` using `[Fintype.card_fun, Fintype.card_fin]`.
-/
theorem finrank_quot_frobKerIdeal_le : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H]
    [Module.Finite K H], 0 < q →
    Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  intro q K H _ _ _ _ hq
  classical
  set J := frobKerIdeal q K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨q, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1
    simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ q = 0 := fun i => hpowQ _ (hy i)

  let mon : (Fin d → Fin q) → H ⧸ J := fun e => ∏ i, y i ^ (e i : ℕ)
  have htop : Submodule.span K (Set.range mon) = ⊤ := by
    have hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon) := by
      intro P
      induction P using MvPolynomial.induction_on' with
      | monomial u a =>
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
          ← Algebra.smul_def]
        refine Submodule.smul_mem _ _ ?_
        by_cases h : ∀ i, u i < q
        · exact Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩
        · push_neg at h
          obtain ⟨i, hi⟩ := h
          have h0 : y i ^ u i = 0 := pow_eq_zero_of_le hi (hyq i)
          rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]
          exact Submodule.zero_mem _
      | add P Q hP hQ => rw [map_add]; exact Submodule.add_mem _ hP hQ
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨P, rfl⟩ := hsurj z
    exact hall P
  have h1 := finrank_range_le_card (R := K) (b := mon)
  rw [Set.finrank, htop, finrank_top] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end GlobalTheory.FrobKerDim
