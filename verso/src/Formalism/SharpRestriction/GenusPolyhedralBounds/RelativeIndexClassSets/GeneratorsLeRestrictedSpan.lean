import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def In64 : Prop :=
  ∀ x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la), rhoK X la G.w wF (a0 D j T) T x = 0 → x = 0

/- English proof (translation)
Take `⟨k, hk⟩` from `hf`. Rewrite using `[rhoK_eq_zero_iff, mem_Fil]`. Use `⟨f.2, a0 D j T, le_rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, zK, mul_left_comm, Nat.sub_self]`. Use `secPow_mul_mem_Mon X la G.w (hal k) ?_` and prove the remaining obligations.

Rewrite using `[addL_zero]`. Establish `h0 : emb X la G.N (X.inc _ (G.th0 k)) ∈ Vw X la G.N (addL wF wL (WeightFamilies.dimY D j))` using `emb_mem_Vw X la G.N _ (G.th0 k)`. Establish `h1` using `sec_pow_mul_mem X la G.w 0 wF (WeightFamilies.dimY D j) (a0 D j T) h0`. Establish `h2 : WeightFamilies.dimY D j + a0 D j T = T` using `by unfold a0; omega`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem rhoK_Zg (hDT : WeightFamilies.dimY D j ≤ T) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    {f : ↥(Vw X la G.N (addL wF wL T))} (hf : f ∈ Zg G la) : rhoK X la G.w wF (a0 D j T) T f = 0 := by
  obtain ⟨k, hk⟩ := hf
  rw [rhoK_eq_zero_iff, mem_Fil]
  refine ⟨f.2, a0 D j T, le_rfl, ?_⟩
  rw [hk, zK, mul_left_comm, Nat.sub_self]
  refine secPow_mul_mem_Mon X la G.w (hal k) ?_
  rw [addL_zero]
  have h0 : emb X la G.N (X.inc _ (G.th0 k)) ∈ Vw X la G.N (addL wF wL (WeightFamilies.dimY D j)) :=
    emb_mem_Vw X la G.N _ (G.th0 k)
  have h1 := sec_pow_mul_mem X la G.w 0 wF (WeightFamilies.dimY D j) (a0 D j T) h0
  have h2 : WeightFamilies.dimY D j + a0 D j T = T := by unfold a0; omega
  rwa [h2] at h1

/- English proof (translation)
The claim follows from `Submodule.span_le.2 fun _ hf => rhoK_Zg G la hDT hal hf`.
-/
theorem ZK_le_ker (hDT : WeightFamilies.dimY D j ≤ T) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    ZK G la ≤ LinearMap.ker (rhoK X la G.w wF (a0 D j T) T) :=
  Submodule.span_le.2 fun _ hf => rhoK_Zg G la hDT hal hf

/- English proof (translation)
Unfold `NovK N1 Zl ZK`. Rewrite using `[← Submodule.span_union, Submodule.span_span_of_tower, Submodule.span_union]`.
-/
theorem NovK_eq : NovK G la = Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la) ⊔ ZK G la := by
  unfold NovK N1 Zl ZK
  rw [← Submodule.span_union, Submodule.span_span_of_tower, Submodule.span_union]

/- English proof (translation)
Introduce `_ hx` and use `Submodule.subset_span (Submodule.mem_sup_left hx)`.
-/
theorem generators_le_restricted_span : N1 G la ≤ (NovK G la).restrictScalars (Op X la G.N) :=
  fun _ hx => Submodule.subset_span (Submodule.mem_sup_left hx)

/- English proof (translation)
Rewrite using `[NovK_eq]`. Conclude with `le_sup_right`.
-/
theorem ZK_le_NovK : ZK G la ≤ NovK G la := by
  rw [NovK_eq]; exact le_sup_right

/- English proof (translation)
The claim follows from `le_sup_of_le_left le_sup_right`.
-/
theorem generators_le_poleSpan (e : ℕ) : N1 G la ≤ Np G la e := le_sup_of_le_left le_sup_right

/- English proof (translation)
The claim follows from `le_sup_right`.
-/
theorem Zm_le_Np (e : ℕ) : Zm G la ≤ Np G la e := le_sup_right

/- English proof (translation)
The claim follows from `sup_le (sup_le inf_le_right (generators_le_restricted_span G la)) (fun _ hx => ZK_le_NovK G la hx.2)`.
-/
theorem Np_le_NovK (e : ℕ) : Np G la e ≤ (NovK G la).restrictScalars (Op X la G.N) :=
  sup_le (sup_le inf_le_right (generators_le_restricted_span G la)) (fun _ hx => ZK_le_NovK G la hx.2)

/- English proof (translation)
Use `sup_le (sup_le (inf_le_left.trans ?_) h) inf_le_left` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem poleSpan_le_integralForms (e : ℕ) (h : N1 G la ≤ M1 X la G.N (addL wF wL T)) : Np G la e ≤ M1 X la G.N (addL wF wL T) := by
  refine sup_le (sup_le (inf_le_left.trans ?_) h) inf_le_left
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.smul_mem _ _ hy

/- English proof (translation)
The claim follows from `le_inf h (Submodule.span_le.2 fun _ hx => Submodule.subset_span hx)`.
-/
theorem Zl_le_Zm (h : Zl G la ≤ M1 X la G.N (addL wF wL T)) : Zl G la ≤ Zm G la :=
  le_inf h (Submodule.span_le.2 fun _ hx => Submodule.subset_span hx)

/- English proof (translation)
Use extensionality with `⟨x, hx⟩`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_comap]`. Use `show rhoK X la G.w wF (a0 D j T) T x = 0 ↔ x ∈ Zm G la`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨poleSpan_le_integralForms G la e hN hx, ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ NovK G la` using `Np_le_NovK G la e hx`. Rewrite `hx'` using `[NovK_eq]`. Take `⟨n, hn, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx'`. Establish `hz0 : rhoK X la G.w wF (a0 D j T) T z = 0` using `ZK_le_ker G la hDT hal hz`.

Rewrite `h` using `[map_add, hz0, add_zero]`. Rewrite using `[h64 n hn h, zero_add]`. Conclude with `hz`. Introduce `h`. Conclude with `ZK_le_ker G la hDT hal h.2`.
-/
theorem ker_rhoN (e : ℕ) (h64 : In64 G la) (hN : N1 G la ≤ M1 X la G.N (addL wF wL T)) (hDT : WeightFamilies.dimY D j ≤ T)
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    LinearMap.ker (rhoN G la e) = (Zm G la).comap (Np G la e).subtype := by
  ext ⟨x, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  show rhoK X la G.w wF (a0 D j T) T x = 0 ↔ x ∈ Zm G la
  constructor
  · intro h
    refine ⟨poleSpan_le_integralForms G la e hN hx, ?_⟩
    have hx' : x ∈ NovK G la := Np_le_NovK G la e hx
    rw [NovK_eq] at hx'
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz0 : rhoK X la G.w wF (a0 D j T) T z = 0 := ZK_le_ker G la hDT hal hz
    rw [map_add, hz0, add_zero] at h
    rw [h64 n hn h, zero_add]
    exact hz
  · intro h
    exact ZK_le_ker G la hDT hal h.2

/- English proof (translation)
Rewrite using `[reducedGenerators_eq_map]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx⟩, hx1, rfl⟩`. Conclude with `⟨x, hx1, rfl⟩`.

Introduce and unpack `⟨x, hx1, rfl⟩`. Conclude with `⟨⟨x, generators_le_poleSpan G la e hx1⟩, hx1, rfl⟩`.
-/
theorem map_reduction_generators_eq (e : ℕ) : ((N1 G la).comap (Np G la e).subtype).map (rhoN G la e) = firstLength_le_prime_bound G la T := by
  rw [reducedGenerators_eq_map]
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hx1, rfl⟩; exact ⟨x, hx1, rfl⟩
  · rintro ⟨x, hx1, rfl⟩; exact ⟨⟨x, generators_le_poleSpan G la e hx1⟩, hx1, rfl⟩

/- English proof (translation)
Establish `h : Np G la e ≤ (Q.AAp T (Q.mm S T e)).comap (rhoO G la)`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Conclude with `fun y hy => reduction_uniformizer_smul_mem Q S hC hT hw e hy.1`. Introduce `y hy`. Use `AA_le_AAp Q _ (reduced_generators_le Q S hC hT hw hth ?_)` and prove the remaining obligations.

Rewrite using `[reducedGenerators_eq_map]`. Conclude with `⟨y, hy, rfl⟩`. Introduce `y hy`. Establish `h0 : rhoK X la G.w wF (a0 D j T) T y = 0` using `ZK_le_ker G la hDT hal hy.2`. Use `show rhoK X la G.w wF (a0 D j T) T y ∈ Q.AAp T (Q.mm S T e)`.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Conclude with `h x.2`.
-/
theorem rhoN_mem {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (e : ℕ) (hC : Q.InCurve) (hT : Q.InTie S)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ i, G.th' i ∈ B.Mlat j wF) (hDT : WeightFamilies.dimY D j ≤ T)
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) (x : ↥(Np G la e)) : rhoN G la e x ∈ Q.AAp T (Q.mm S T e) := by
  have h : Np G la e ≤ (Q.AAp T (Q.mm S T e)).comap (rhoO G la) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun y hy => reduction_uniformizer_smul_mem Q S hC hT hw e hy.1
    · intro y hy
      refine AA_le_AAp Q _ (reduced_generators_le Q S hC hT hw hth ?_)
      rw [reducedGenerators_eq_map]
      exact ⟨y, hy, rfl⟩
    · intro y hy
      have h0 : rhoK X la G.w wF (a0 D j T) T y = 0 := ZK_le_ker G la hDT hal hy.2
      show rhoK X la G.w wF (a0 D j T) T y ∈ Q.AAp T (Q.mm S T e)
      rw [h0]
      exact Submodule.zero_mem _
  exact h x.2

end Formalism.MainNotions.Gaps.EtaleWeightGaps
