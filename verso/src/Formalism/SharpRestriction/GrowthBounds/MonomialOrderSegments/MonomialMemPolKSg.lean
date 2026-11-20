import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutionXFirstEmbedding

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

/- English proof (translation)
Rewrite using `[mem_PolK_iff]`. Introduce `β hβ`. Rewrite using `[Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ)]`. Conclude with `h`.
-/
theorem monomial_mem_PolK_sg {K : Type} [Field K] {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ)
    (c : K) (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro β hβ
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ)]
  exact h

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def outSeg (i : D.ML) : Prop := ¬ ∃ k, D.e0 j k = i

instance : DecidablePred (D.outSeg j) := Classical.decPred _
instance : DecidablePred (D.SegL j) := Classical.decPred _

def pullE (ζ : D.EM) : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ :=
  Finsupp.comapDomain (Prod.map (D.e0 j) id) ζ
    (((D.index_embedding_injective j).prodMap (Function.injective_id (α := Fin D.r))).injOn)

/- English proof (translation)
Conclude with `Finsupp.comapDomain_apply _ _ _ _`.
-/
theorem pullE_apply (ζ : D.EM) (k : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.pullE j ζ (k, a) = ζ (D.e0 j k, a) := by
  exact Finsupp.comapDomain_apply _ _ _ _

/- English proof (translation)
Unfold `ldeg`. Simplify using `only [pullE_apply]`.
-/
theorem ldeg_pullE (ζ : D.EM) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = ldeg ζ (D.e0 j k) := by
  unfold ldeg
  simp only [pullE_apply]

/- English proof (translation)
Use extensionality with `⟨i, a⟩`. Distinguish the cases in `hi : ∃ k, D.e0 j k = i`. Take `⟨k, rfl⟩` from `hi`. Establish `hinj : Function.Injective (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r))` using `(D.index_embedding_injective j).prodMap Function.injective_id`. Establish `hout : ¬ D.outSeg j (D.e0 j k)` using `fun h => h ⟨k, rfl⟩`.

Conclude with `(Finsupp.mapDomain_apply hinj (D.pullE j ζ) (k, a)).trans ((D.pullE_apply j ζ k a).trans ((eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)).symm)`. Establish `hout : D.outSeg j i` using `hi`. Rewrite using `[Finsupp.mapDomain_notin_range]`. Conclude with `((eIn_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos hout)).symm`. Introduce and unpack `⟨⟨k, b⟩, hkb⟩`.

Conclude with `hi ⟨k, (Prod.mk.inj hkb).1⟩`.
-/
theorem mapDomain_pullE (ζ : D.EM) :
    Finsupp.mapDomain (Prod.map (D.e0 j) id) (D.pullE j ζ) = eIn (D.outSeg j) ζ := by
  ext ⟨i, a⟩
  by_cases hi : ∃ k, D.e0 j k = i
  · obtain ⟨k, rfl⟩ := hi
    have hinj : Function.Injective (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r)) :=
      (D.index_embedding_injective j).prodMap Function.injective_id
    have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
    exact (Finsupp.mapDomain_apply hinj (D.pullE j ζ) (k, a)).trans
      ((D.pullE_apply j ζ k a).trans ((eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)).symm)
  · have hout : D.outSeg j i := hi
    rw [Finsupp.mapDomain_notin_range]
    · exact ((eIn_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos hout)).symm
    · rintro ⟨⟨k, b⟩, hkb⟩
      exact hi ⟨k, (Prod.mk.inj hkb).1⟩

/- English proof (translation)
Use extensionality with `⟨k, a⟩`. Rewrite using `[pullE_apply, pullE_apply]`. Conclude with `h k a`.
-/
theorem pullE_congr (ζ ζ' : D.EM) (h : ∀ k a, ζ (D.e0 j k, a) = ζ' (D.e0 j k, a)) :
    D.pullE j ζ = D.pullE j ζ' := by
  ext ⟨k, a⟩
  rw [pullE_apply, pullE_apply]
  exact h k a

/- English proof (translation)
Apply `D.pullE_congr j` to reduce the goal to its premises. Introduce `k a`. Establish `hout : ¬ D.outSeg j (D.e0 j k)` using `fun h => h ⟨k, rfl⟩`. Conclude with `(eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)`.
-/
theorem pullE_eIn (ζ : D.EM) : D.pullE j (eIn (D.outSeg j) ζ) = D.pullE j ζ := by
  apply D.pullE_congr j
  intro k a
  have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
  exact (eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)

/- English proof (translation)
Rewrite using `[ldeg_pullE]`. Consider the cases of `k using Fin.addCases with`. Consider the case `left a`. Establish `hseg : D.seg (D.eB j a) = j` using `(Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2`. Rewrite using `[first_embedding_castAdd, h.1 _ hseg]`.

Simplify using `only [eA, dO, Fin.addCases_left, Sum.elim_inl]`. Consider the case `right m`. Rewrite using `[first_embedding_natAdd, h.2.1]`. Simplify using `only [eA, dO, Fin.addCases_right, Sum.elim_inr]`.
-/
theorem pullE_deg (ζ : D.EM) (h : D.PreE j ζ) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = D.dO (D.eA j k) := by
  rw [ldeg_pullE]
  cases k using Fin.addCases with
  | left a =>
    have hseg : D.seg (D.eB j a) = j := (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2
    rw [first_embedding_castAdd, h.1 _ hseg]
    simp only [eA, dO, Fin.addCases_left, Sum.elim_inl]
  | right m =>
    rw [first_embedding_natAdd, h.2.1]
    simp only [eA, dO, Fin.addCases_right, Sum.elim_inr]

variable {ι : Type} [Fintype ι]

def TT (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun lam => ∑ b, cc lam b • PP b

def Th (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (eOut (D.outSeg j) ζ) 1 * D.TT j cc PP (monomial (D.pullE j ζ) 1)

variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

/- English proof (translation)
Simplify using `only [TT, lsup_monomial, one_smul]`.
-/
theorem TT_monomial (lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) :
    D.TT j cc PP (monomial lam 1) = ∑ b, cc lam b • PP b := by
  simp only [TT, lsup_monomial, one_smul]

/- English proof (translation)
Simplify using `only [Th, lsup_monomial, one_smul, TT_monomial]`.
-/
theorem Th_monomial (ζ : D.EM) :
    D.Th j cc PP (monomial ζ 1) =
      monomial (eOut (D.outSeg j) ζ) 1 * ∑ b, cc (D.pullE j ζ) b • PP b := by
  simp only [Th, lsup_monomial, one_smul, TT_monomial]

/- English proof (translation)
Establish `hQsupp : ∀ lam ∈ Q.support, ∀ k, ldeg lam k = D.dO (D.eA j k)`. Introduce `lam hlam k`. Conclude with `(mem_PolK_iff _ Q).mp hQ lam hlam k`. Use `set c : ι → K := fun b => ∑ lam ∈ Q.support, Q.coeff lam * cc lam b with hc`. Establish `hT : D.TT j cc PP Q = ∑ b, c b • PP b`.

Simplify using `only [TT, lsup_apply, Finset.smul_sum, smul_smul, hc, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `hQ' : Q = ∑ b, c b • Ψ b`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun lam _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Use `_ = ∑ lam ∈ Q.support, Q.coeff lam • ∑ b, cc lam b • Ψ b := by`. Use `Finset.sum_congr rfl fun lam hlam => ?_` and prove the remaining obligations. Rewrite using `[hcc lam (hQsupp lam hlam)]`. Use `_ = ∑ b, c b • Ψ b := by`.

Simplify using `only [Finset.smul_sum, smul_smul, hc, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `hca : ∀ b, c b = a b`. Establish `h0 : ∑ b, (c b - a b) • Ψ b = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[← hQ', ← ha, sub_self]`. Introduce `b`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 b)`. Rewrite using `[hT]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [hca b]`.
-/
theorem TT_expand (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (Q : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hQ : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k))) (a : ι → K) (ha : Q = ∑ b, a b • Ψ b) :
    D.TT j cc PP Q = ∑ b, a b • PP b := by
  classical
  have hQsupp : ∀ lam ∈ Q.support, ∀ k, ldeg lam k = D.dO (D.eA j k) := by
    intro lam hlam k
    exact (mem_PolK_iff _ Q).mp hQ lam hlam k
  set c : ι → K := fun b => ∑ lam ∈ Q.support, Q.coeff lam * cc lam b with hc
  have hT : D.TT j cc PP Q = ∑ b, c b • PP b := by
    simp only [TT, lsup_apply, Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
    exact Finset.sum_comm
  have hQ' : Q = ∑ b, c b • Ψ b := by
    calc Q = ∑ lam ∈ Q.support, Q.coeff lam • monomial lam (1 : K) := by
            conv_lhs => rw [Q.as_sum]
            refine Finset.sum_congr rfl fun lam _ => ?_
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      _ = ∑ lam ∈ Q.support, Q.coeff lam • ∑ b, cc lam b • Ψ b := by
            refine Finset.sum_congr rfl fun lam hlam => ?_
            rw [hcc lam (hQsupp lam hlam)]
      _ = ∑ b, c b • Ψ b := by
            simp only [Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
            exact Finset.sum_comm
  have hca : ∀ b, c b = a b := by
    have h0 : ∑ b, (c b - a b) • Ψ b = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hQ', ← ha, sub_self]
    intro b
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 b)
  rw [hT]
  exact Finset.sum_congr rfl fun b _ => by rw [hca b]

/- English proof (translation)
Rewrite using `[Th_monomial]`. Apply `integral_mul' (integral_monomial' _ (by simp))` to reduce the goal to its premises. Apply `integral_sum'` to reduce the goal to its premises. Introduce `b _`. Conclude with `integral_smul' (hccint _ (D.pullE_deg j ζ hζ) b) (hPP b)`.
-/
theorem Th_integral {v : AddValuation K (WithTop ℚ)}
    (hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b))
    (hPP : ∀ b, Integral v (PP b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    Integral v (D.Th j cc PP (monomial ζ 1)) := by
  rw [Th_monomial]
  apply integral_mul' (integral_monomial' _ (by simp))
  apply integral_sum'
  intro b _
  exact integral_smul' (hccint _ (D.pullE_deg j ζ hζ) b) (hPP b)

/- English proof (translation)
Establish `hsum : (∑ b, cc (D.pullE j ζ) b • rename (Prod.map (D.eA j) id) (Ψ b)) = D.ph p (monomial (eIn (D.outSeg j) ζ) 1)`. Rewrite using `[← D.mapDomain_pullE j ζ, ← MvPolynomial.rename_monomial, substitution_rename_first_embedding, hcc _ (D.pullE_deg j ζ hζ), map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[Th_monomial, map_mul, map_sum]`. Simplify using `only [map_smul, hPP]`.

Rewrite using `[hsum, ← map_mul, MvPolynomial.monomial_mul, one_mul, eOut_add_eIn]`.
-/
theorem Th_ph (p : ℕ) (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (hPP : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    D.ph p (D.Th j cc PP (monomial ζ 1)) = D.ph p (monomial ζ 1) := by
  have hsum : (∑ b, cc (D.pullE j ζ) b • rename (Prod.map (D.eA j) id) (Ψ b)) =
      D.ph p (monomial (eIn (D.outSeg j) ζ) 1) := by
    rw [← D.mapDomain_pullE j ζ, ← MvPolynomial.rename_monomial, substitution_rename_first_embedding,
      hcc _ (D.pullE_deg j ζ hζ), map_sum]
    simp only [map_smul]
  rw [Th_monomial, map_mul, map_sum]
  simp only [map_smul, hPP]
  rw [hsum, ← map_mul, MvPolynomial.monomial_mul, one_mul, eOut_add_eIn]

/- English proof (translation)
Rewrite `h` using `[Th_monomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul']`. Use `split_ifs at h with hle`. Rewrite `h` using `[one_mul, MvPolynomial.coeff_sum]`. Take `⟨b, -, hb⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Rewrite `hb` using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Use `⟨b, ζ' - eOut (D.outSeg j) ζ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Conclude with `right_ne_zero_of_mul hb`. Conclude with `(add_tsub_cancel_of_le hle).symm`. Conclude with `absurd rfl h`.
-/
theorem Th_supp (ζ ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    ∃ b, ∃ ξ ∈ (PP b).support, ζ' = eOut (D.outSeg j) ζ + ξ := by
  rw [Th_monomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul'] at h
  split_ifs at h with hle
  · rw [one_mul, MvPolynomial.coeff_sum] at h
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [MvPolynomial.coeff_smul, smul_eq_mul] at hb
    refine ⟨b, ζ' - eOut (D.outSeg j) ζ, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      exact right_ne_zero_of_mul hb
    · exact (add_tsub_cancel_of_le hle).symm
  · exact absurd rfl h

/- English proof (translation)
Introduce and unpack `⟨k, rfl⟩`. Apply `hi` to reduce the goal to its premises. Unfold `SegL`. Consider the cases of `k using Fin.addCases with`. Consider the case `left a`.

Rewrite using `[first_embedding_castAdd]`. Conclude with `Or.inl ⟨D.eB j a, (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2, rfl⟩`. Consider the case `right m`. Rewrite using `[first_embedding_natAdd]`. Conclude with `Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)`.
-/
theorem outSeg_of_not_segL (i : D.ML) (hi : ¬ D.SegL j i) : D.outSeg j i := by
  rintro ⟨k, rfl⟩
  apply hi
  unfold SegL
  cases k using Fin.addCases with
  | left a =>
    rw [first_embedding_castAdd]
    exact Or.inl ⟨D.eB j a, (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2, rfl⟩
  | right m =>
    rw [first_embedding_natAdd]
    exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)

/- English proof (translation)
Take `⟨b, ξ, hξ, rfl⟩` from `D.Th_supp j cc PP ζ ζ' h`. Take `⟨hpost, hzero⟩` from `hPP b ξ hξ`. Establish `hO : ∀ i, ¬ D.outSeg j i → ∀ a, eOut (D.outSeg j) ζ (i, a) = 0`. Introduce `i hi a`. Conclude with `(eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_neg hi)`.

Establish `hmb : ∀ c, D.seg c = j → ¬ D.outSeg j (D.mb c)`. Introduce `c hc hout`. Take `⟨a, rfl⟩` from `eB_surj (D := D) (j := j) c hc`. Conclude with `hout ⟨Fin.castAdd D.r a, by rw [first_embedding_castAdd]⟩`. Establish `hml : ∀ m, ¬ D.outSeg j (D.mlab (j, m))`.

Introduce `m hout`. Conclude with `hout ⟨Fin.natAdd (D.nB j) (Fin.rev m), by rw [first_embedding_natAdd, Fin.rev_rev]⟩`. Establish `hmt : ∀ m a, eOut (D.outSeg j) ζ (D.mtp (j, m), a) = 0`. Introduce `m a`. Rewrite using `[eOut_apply]`.

Use `split_ifs`. Conclude with `hζ.2.2 m a`. Both sides reduce to the same expression. Establish `hldeg : ∀ i, (∀ a, eOut (D.outSeg j) ζ (i, a) = 0) → ldeg (eOut (D.outSeg j) ζ + ξ) i = ldeg ξ i`. Introduce `i hi`.

Simplify using `only [ldeg, Finsupp.add_apply, hi, zero_add]`. Use `⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Rewrite using `[hldeg _ (hO _ (hmb c hc))]`. Conclude with `hpost.1 c hc`.

Introduce `m`. Rewrite using `[hldeg _ (hO _ (hml m)), hldeg _ (hmt m)]`. Conclude with `hpost.2.1 m`. Introduce `m`. Rewrite using `[hldeg _ (hmt m)]`.

Conclude with `hpost.2.2.1 m`. Introduce `m hm a`. Rewrite using `[Finsupp.add_apply, hmt m a, zero_add]`. Conclude with `hpost.2.2.2 m hm a`. Introduce `i hi a`.

Rewrite using `[Finsupp.add_apply, hzero i hi a, add_zero]`. Conclude with `(eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos (D.outSeg_of_not_segL j i hi))`.
-/
theorem Th_post (hPP : ∀ b, ∀ ξ ∈ (PP b).support, D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (ζ : D.EM) (hζ : D.PreE j ζ) (ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a) := by
  obtain ⟨b, ξ, hξ, rfl⟩ := D.Th_supp j cc PP ζ ζ' h
  obtain ⟨hpost, hzero⟩ := hPP b ξ hξ
  have hO : ∀ i, ¬ D.outSeg j i → ∀ a, eOut (D.outSeg j) ζ (i, a) = 0 := by
    intro i hi a
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_neg hi)
  have hmb : ∀ c, D.seg c = j → ¬ D.outSeg j (D.mb c) := by
    intro c hc hout
    obtain ⟨a, rfl⟩ := eB_surj (D := D) (j := j) c hc
    exact hout ⟨Fin.castAdd D.r a, by rw [first_embedding_castAdd]⟩
  have hml : ∀ m, ¬ D.outSeg j (D.mlab (j, m)) := by
    intro m hout
    exact hout ⟨Fin.natAdd (D.nB j) (Fin.rev m), by rw [first_embedding_natAdd, Fin.rev_rev]⟩
  have hmt : ∀ m a, eOut (D.outSeg j) ζ (D.mtp (j, m), a) = 0 := by
    intro m a
    rw [eOut_apply]
    split_ifs
    · exact hζ.2.2 m a
    · rfl
  have hldeg : ∀ i, (∀ a, eOut (D.outSeg j) ζ (i, a) = 0) →
      ldeg (eOut (D.outSeg j) ζ + ξ) i = ldeg ξ i := by
    intro i hi
    simp only [ldeg, Finsupp.add_apply, hi, zero_add]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    rw [hldeg _ (hO _ (hmb c hc))]
    exact hpost.1 c hc
  · intro m
    rw [hldeg _ (hO _ (hml m)), hldeg _ (hmt m)]
    exact hpost.2.1 m
  · intro m
    rw [hldeg _ (hmt m)]
    exact hpost.2.2.1 m
  · intro m hm a
    rw [Finsupp.add_apply, hmt m a, zero_add]
    exact hpost.2.2.2 m hm a
  · intro i hi a
    rw [Finsupp.add_apply, hzero i hi a, add_zero]
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos (D.outSeg_of_not_segL j i hi))

/- English proof (translation)
Establish `hIn : ∀ α : D.EM, eIn (fun i => ¬ D.outSeg j i) α = eOut (D.outSeg j) α`. Introduce `α`. Use extensionality with `x`. Simplify using `[eIn, eOut, Finsupp.filter_apply]`. Establish `hOut : ∀ α : D.EM, eOut (fun i => ¬ D.outSeg j i) α = eIn (D.outSeg j) α`.

Introduce `α`. Use extensionality with `x`. Simplify using `[eIn, eOut, Finsupp.filter_apply]`. Establish `hIn1 : ∀ α : D.EM, D.Th j cc PP (monomial (eIn (D.outSeg j) α) 1) = ∑ b, cc (D.pullE j α) b • PP b`. Introduce `α`.

Rewrite using `[Th_monomial, eOut_eIn, pullE_eIn, ← C_apply, map_one, one_mul]`. Use `valS_outside_linear (fun i => ¬ D.outSeg j i) D.msg S (D.Th j cc PP) ?_ ?_ ?_ Z` and prove the remaining obligations. Introduce `i hi h`. Conclude with `h (D.outSeg_of_not_segL j i (hS i hi))`. Introduce `α`.

Rewrite using `[hIn, hOut, hIn1, Th_monomial]`. Introduce `α`. Rewrite using `[hOut, hIn1]`. Apply `valS_sum_le` to reduce the goal to its premises. Introduce `b _`.

Rewrite using `[smul_eq_C_mul]`. Use `le_trans ?_ (valS_C_mul_le _ _ _ _)` and prove the remaining obligations. Apply `valS_nonneg_of_vecS` to reduce the goal to its premises. Introduce `ξ hξ i a hne hiS`. Conclude with `absurd (hPP b ξ hξ i (hS i hiS) a) hne`.
-/
theorem Th_away (hPP : ∀ b, ∀ ξ ∈ (PP b).support, ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (S : Finset D.ML) (hS : ∀ i ∈ S, ¬ D.SegL j i) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    valS D.msg S Z ≤ valS D.msg S (D.Th j cc PP Z) := by
  have hIn : ∀ α : D.EM, eIn (fun i => ¬ D.outSeg j i) α = eOut (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hOut : ∀ α : D.EM, eOut (fun i => ¬ D.outSeg j i) α = eIn (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hIn1 : ∀ α : D.EM,
      D.Th j cc PP (monomial (eIn (D.outSeg j) α) 1) = ∑ b, cc (D.pullE j α) b • PP b := by
    intro α
    rw [Th_monomial, eOut_eIn, pullE_eIn, ← C_apply, map_one, one_mul]
  refine valS_outside_linear (fun i => ¬ D.outSeg j i) D.msg S (D.Th j cc PP) ?_ ?_ ?_ Z
  · intro i hi h
    exact h (D.outSeg_of_not_segL j i (hS i hi))
  · intro α
    rw [hIn, hOut, hIn1, Th_monomial]
  · intro α
    rw [hOut, hIn1]
    apply valS_sum_le
    intro b _
    rw [smul_eq_C_mul]
    refine le_trans ?_ (valS_C_mul_le _ _ _ _)
    apply valS_nonneg_of_vecS
    intro ξ hξ i a hne hiS
    exact absurd (hPP b ξ hξ i (hS i hiS) a) hne

end TwistData

end Formalism.MainNotions.PlaneGram
