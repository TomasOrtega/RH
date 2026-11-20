import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SingleMemStandardLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField
open scoped ComplexOrder

noncomputable def hQdist {K : Type} [Field K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (q : Fin r → K) : ℝ :=
  ⨅ z : Fin k → ℂ, Real.sqrt (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2)

section Final

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

/- English proof (translation)
Use `set v : Fin r → ℂ := fun i => σ (q i) with hv`. Use `set G := (hBm σ b)ᴴ * hBm σ b with hG`. Establish `hterm : ∀ z : Fin k → ℂ, (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2) = hns (v + hBm σ b *ᵥ z)`. Introduce `z`. Simplify using `only [hns]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[v, hBm, mulVec, dotProduct, mul_comm]`. Establish `hdec : ∀ z, v + hBm σ b *ᵥ z = hPm σ b *ᵥ v + hBm σ b *ᵥ (z + G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v))`. Introduce `z`. Simplify using `only [hPm, sub_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec]`.

Normalize the expressions using the abelian group laws. Establish `hmin : ∀ z, hns (hPm σ b *ᵥ v) ≤ hns (v + hBm σ b *ᵥ z)`. Introduce `z`. Rewrite using `[hdec z, normSqSum_add_of_orthogonal _ _ (orthogonalProjector_orthogonal σ hb _ _)]`. Conclude with `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)`.

Establish `hat : v + hBm σ b *ᵥ (-(G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v))) = hPm σ b *ᵥ v`. Rewrite using `[hdec, neg_add_cancel, mulVec_zero, add_zero]`. Unfold `hQdist`. Repeatedly rewrite using `[hterm]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `(ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩ _).trans_eq (by rw [hat])`. Conclude with `le_ciInf fun z => Real.sqrt_le_sqrt (hmin z)`.
-/
theorem quotDist_eq_sqrt_norm (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hQdist σ b q = Real.sqrt (hns (hPm σ b *ᵥ fun i => σ (q i))) := by
  set v : Fin r → ℂ := fun i => σ (q i) with hv
  set G := (hBm σ b)ᴴ * hBm σ b with hG
  have hterm : ∀ z : Fin k → ℂ,
      (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2) = hns (v + hBm σ b *ᵥ z) := by
    intro z
    simp only [hns]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [v, hBm, mulVec, dotProduct, mul_comm]
  have hdec : ∀ z, v + hBm σ b *ᵥ z =
      hPm σ b *ᵥ v + hBm σ b *ᵥ (z + G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v)) := by
    intro z
    simp only [hPm, sub_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec]
    abel
  have hmin : ∀ z, hns (hPm σ b *ᵥ v) ≤ hns (v + hBm σ b *ᵥ z) := by
    intro z
    rw [hdec z, normSqSum_add_of_orthogonal _ _ (orthogonalProjector_orthogonal σ hb _ _)]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  have hat : v + hBm σ b *ᵥ (-(G⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ v))) = hPm σ b *ᵥ v := by
    rw [hdec, neg_add_cancel, mulVec_zero, add_zero]
  unfold hQdist
  simp_rw [hterm]
  apply le_antisymm
  · exact (ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩ _).trans_eq (by rw [hat])
  · exact le_ciInf fun z => Real.sqrt_le_sqrt (hmin z)

/- English proof (translation)
Rewrite using `[hpv, norm_realCoords_sq]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (by unfold hns; positivity)]`.
-/
theorem norm_orthProj_sq_sum {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (q : Fin r → K) :
    ‖hpv b q‖ ^ 2 = ∑ σ, hQdist σ b q ^ 2 := by
  rw [hpv, norm_realCoords_sq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (by unfold hns; positivity)]

/- English proof (translation)
Take `⟨o, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 ht`. Establish `e : ∀ j, o j • c j = ∑ a, (RingOfIntegers.basis K).repr (o j) a • (integralBasis K a • c j)`. Introduce `j`. Use `conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr (o j)]`. Rewrite using `[Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, integralBasis_apply, algebraMap_smul]`. Establish `e2 : hpv b (∑ j, o j • c j) = ∑ j, ∑ a, (RingOfIntegers.basis K).repr (o j) a • hwv b c (j, a)`. Repeatedly rewrite using `[e]`. Express the relevant statement in the definitionally equal form `hpvHom b _ = _`.

Simplify using `only [map_sum, map_zsmul]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, a), rfl⟩)`.
-/
theorem orthProj_mem_span {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) {t : Fin r → K}
    (ht : t ∈ Submodule.span (𝓞 K) (Set.range c)) :
    hpv b t ∈ Submodule.span ℤ (Set.range (hwv b c)) := by
  classical
  obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 ht
  have e : ∀ j, o j • c j = ∑ a, (RingOfIntegers.basis K).repr (o j) a • (integralBasis K a • c j) := by
    intro j
    conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr (o j)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  have e2 : hpv b (∑ j, o j • c j) = ∑ j, ∑ a, (RingOfIntegers.basis K).repr (o j) a • hwv b c (j, a) := by
    simp_rw [e]
    change hpvHom b _ = _
    simp only [map_sum, map_zsmul]
    rfl
  rw [e2]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, a), rfl⟩)

/- English proof (translation)
Use `⟨integralBasis K p.2 • c p.1, ?_, rfl⟩` and prove the remaining obligations. Use `show integralBasis K p.2 • c p.1 ∈ hStd K r`. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (hc p.1)`.
-/
theorem orthProjVector_mem {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hc : ∀ j, c j ∈ hStd K r) (p : Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    hwv b c p ∈ (hStd K r).toAddSubgroup.map (hpvHom b) := by
  refine ⟨integralBasis K p.2 • c p.1, ?_, rfl⟩
  show integralBasis K p.2 • c p.1 ∈ hStd K r
  rw [integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (hc p.1)

/- English proof (translation)
Rewrite using `[← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup]`. Use `congr 1`. Use extensionality with `q`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hW, hq⟩`. Use `⟨?_, hq⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hW`. Use `set t : Fin r → K := ∑ p, n p • (integralBasis K p.2 • c p.1) with htdef`. Establish `ht : t ∈ Submodule.span (𝓞 K) (Set.range c)`.

Use `Submodule.sum_mem _ fun p _ => Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)`. Establish `hft : hpv b t = hpvHom b q`. Rewrite using `[← hn]`.

Express the relevant statement in the definitionally equal form `hpvHom b t = _`. Simplify using `only [t, map_sum, map_zsmul]`. Both sides reduce to the same expression. Establish `hz : hpv b (q - t) = 0`. Express the relevant statement in the definitionally equal form `hpvHom b (q - t) = 0`.

Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `hpvHom b q - hpv b t = 0`. Rewrite using `[hft, sub_self]`. Rewrite `hz` using `[projectedVector_eq_zero_iff hb]`. Establish `htL : t ∈ hStd K r` using `(Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hc j)) ht`.

Establish `hsat : q - t ∈ ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b` using `⟨Submodule.sub_mem _ hq htL, hz⟩`. Use `Submodule.add_mem_sup hsat ht` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨hS, hq⟩`. Use `⟨?_, hq⟩` and prove the remaining obligations.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hS`. Express the relevant statement in the definitionally equal form `hpvHom b (y + z) ∈ _`. Rewrite using `[map_add]`. Establish `hy0 : hpvHom b y = 0` using `(projectedVector_eq_zero_iff hb y).mpr hy.2`. Rewrite using `[hy0, zero_add]`.

Conclude with `orthProj_mem_span b c hz`.
-/
theorem relIndex_orthProj_lattice {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r) :
    (Submodule.span ℤ (Set.range (hwv b c))).toAddSubgroup.relIndex
        ((hStd K r).toAddSubgroup.map (hpvHom b)) =
      (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        (hStd K r).toAddSubgroup := by
  classical
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
      Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup]
  congr 1
  ext q
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨hW, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hW
    set t : Fin r → K := ∑ p, n p • (integralBasis K p.2 • c p.1) with htdef
    have ht : t ∈ Submodule.span (𝓞 K) (Set.range c) := by
      refine Submodule.sum_mem _ fun p _ => Submodule.smul_of_tower_mem _ _ ?_
      rw [integralBasis_apply, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)
    have hft : hpv b t = hpvHom b q := by
      rw [← hn]
      change hpvHom b t = _
      simp only [t, map_sum, map_zsmul]
      rfl
    have hz : hpv b (q - t) = 0 := by
      change hpvHom b (q - t) = 0
      rw [map_sub]
      change hpvHom b q - hpv b t = 0
      rw [hft, sub_self]
    rw [projectedVector_eq_zero_iff hb] at hz
    have htL : t ∈ hStd K r :=
      (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hc j)) ht
    have hsat : q - t ∈ ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b :=
      ⟨Submodule.sub_mem _ hq htL, hz⟩
    have := Submodule.add_mem_sup hsat ht
    rwa [sub_add_cancel] at this
  · rintro ⟨hS, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hS
    change hpvHom b (y + z) ∈ _
    rw [map_add]
    have hy0 : hpvHom b y = 0 := (projectedVector_eq_zero_iff hb y).mpr hy.2
    rw [hy0, zero_add]
    exact orthProj_mem_span b c hz

end Final

section Main

/- English proof (translation)
Use `set m := r - k with hmdef`. Establish `hm : 0 < m` using `by omega`. Establish `hkm : k + m = r` using `by omega`. Take `⟨c, hc, hli, hsp⟩` from `exists_integral_completion hb hk.le`. Establish `hdeg` using `latDeg_saturation hkm hbL c hc hli hsp`.

Use `set n := Module.finrank ℚ K with hndef`. Establish `hn : 0 < n` using `Module.finrank_pos`. Establish `hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = n`. Rewrite using `[hndef, Module.finrank_eq_card_basis (integralBasis K)]`. Establish `hcardE : Fintype.card (K →+* ℂ) = n` using `NumberField.Embeddings.card K ℂ`.

Use `set N := m * n with hNdef`. Establish `hN : 0 < N` using `Nat.mul_pos hm hn`. Establish `hcardJ : Fintype.card (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = N`. Rewrite using `[Fintype.card_prod, Fintype.card_fin, hcardI]`. Set `eN : Fin N ≃ (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K))` to `(Fintype.equivFinOfCardEq hcardJ).symm`.

Set `w` to `hwv b c ∘ eN`. Establish `hgw : gram ℝ w = (gram ℝ (hwv b c)).submatrix eN eN`. Use extensionality with `i j`. Simplify using `[gram_apply, w]`. Use `set P := ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re with hPdef`.

Use `set D := |(NumberField.discr K : ℝ)| with hDdef`. Establish `hdetw : (gram ℝ w).det = D ^ m * P`. Rewrite using `[hgw, det_submatrix_equiv_self, det_gram_projectedLatticeVectors b hb c]`. Establish `hdpos : 0 < D` using `abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)`. Establish `hPpos : 0 < P` using `Finset.prod_pos fun σ _ => quotGram_det_pos σ hb c hli`.

Establish `hGpos : 0 < (gram ℝ w).det` using `by rw [hdetw]; positivity`. Establish `hwli : LinearIndependent ℝ w` using `linearIndependent_of_det_gram_ne_zero hGpos.ne'`. Use `set Λ := (hStd K r).toAddSubgroup.map (hpvHom b) with hΛ`. Establish `hwmem : ∀ i, w i ∈ Λ` using `fun i => orthProjVector_mem b c hc (eN i)`. Establish `hrange : Set.range w = Set.range (hwv b c)` using `eN.surjective.range_comp _`.

Use `set I := (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex (hStd K r).toAddSubgroup with hIdef`. Establish `hrel : (Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex Λ = I`. Rewrite using `[hrange]`. Conclude with `relIndex_orthProj_lattice hb c hc`. Establish `hI0 : I ≠ 0`.

Establish `h1` using `ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg (hStd K r) standardLattice_fg (Fin.append b c) (fun x _ => hsp x)`. Establish `hle : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) ≤ ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations.

Rewrite using `[Fin.append_left]`. Conclude with `Submodule.mem_sup_left ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩`. Rewrite using `[Fin.append_right]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hdvd` using `AddSubgroup.relIndex_dvd_of_le_left (hStd K r).toAddSubgroup (show (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup ≤ (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup from hle)`.

Introduce `h0`. Rewrite `hdvd` using `[← hIdef, h0]`. Conclude with `h1 (Nat.eq_zero_of_zero_dvd hdvd)`. Take `⟨v, hvΛ, hv0, hvb⟩` from `exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex hN w hwli Λ hwmem (by rw [hrel]; exact hI0)`. Rewrite `hvb` using `[hrel, hdetw]`.

Take `⟨q, hqL, rfl⟩` from `AddSubgroup.mem_map.mp hvΛ`. Establish `hq : q ∉ Submodule.span K (Set.range b)` using `fun h => hv0 ((projectedVector_eq_zero_iff hb q).mpr h)`. Establish `hqL' : q ∈ hStd K r` using `hqL`. Rewrite `hqL'` using `[mem_standardLattice_iff]`. Use `choose q' hq' using hqL'`.

Establish `hqq : (fun i => ((q' i : 𝓞 K) : K)) = q` using `funext hq'`. Use `⟨q', by rw [hqq]; exact hq, ?_⟩` and prove the remaining obligations. Rewrite using `[hqq]`. Use `set X : (K →+* ℂ) → ℝ := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)) with hX`. Establish `hXpos : ∀ σ, 0 < X σ` using `fun σ => normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ hb hq)`.

Establish `hdist : ∀ σ, Real.log (hQdist σ b q) = Real.log (X σ) / 2` using `fun σ => by`. Rewrite using `[quotDist_eq_sqrt_norm σ hb, Real.log_sqrt (hXpos σ).le]`. Establish `hsumX : ∑ σ, X σ = ‖hpvHom b q‖ ^ 2` using `by show _ = ‖hpv b q‖ ^ 2`. Rewrite using `[norm_orthProj_sq_sum hb]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (hXpos σ).le]`. Establish `hnr : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hamgm : ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤ Real.log ((1 / (n : ℝ)) * ∑ σ, X σ)`. Establish `hw0 : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), (0 : ℝ) ≤ 1 / (n : ℝ)` using `fun _ _ => by positivity`. Establish `hw1 : ∑ σ ∈ (Finset.univ : Finset (K →+* ℂ)), 1 / (n : ℝ) = 1`.

Rewrite using `[Finset.sum_const, Finset.card_univ, hcardE, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `h` using `Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => 1 / (n : ℝ)) X hw0 hw1 (fun σ _ => (hXpos σ).le)`. Establish `hprod : 0 < ∏ σ, X σ ^ (1 / (n : ℝ))` using `Finset.prod_pos fun σ _ => Real.rpow_pos_of_pos (hXpos σ) _`. Establish `hlog` using `Real.log_le_log hprod h`.

Rewrite `hlog` using `[Real.log_prod (fun σ _ => (Real.rpow_pos_of_pos (hXpos σ) _).ne')]`. Simplify using `only [Real.log_rpow (hXpos _)] at hlog`. Rewrite using `[Finset.mul_sum]`. Conclude with `hlog`. Establish `hIr : (0 : ℝ) < I` using `by exact_mod_cast Nat.pos_of_ne_zero hI0`.

Establish `hquot : ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c = Real.log I - 1 / 2 * Real.log P`. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.quotDeg]`. Rewrite using `[hPdef, Real.log_prod (fun σ _ => (quotGram_det_pos σ hb c hli).ne')]`. Establish `hlogG : Real.log (D ^ m * P / (I : ℝ) ^ 2) = m * Real.log D + Real.log P - 2 * Real.log I`. Rewrite using `[Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hNr : (N : ℝ) = m * n` using `by rw [hNdef]; push_cast; ring`. Establish `hmr : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `hY : Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) = Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I)`.

Rewrite using `[show (1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ))) = (m : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) by rw [hNr]; field_simp]`. Rewrite using `[Real.log_mul hmr.ne' (Real.rpow_pos_of_pos (by positivity) _).ne', Real.log_rpow (by positivity), hlogG]`. Establish `hmean : meanK (fun σ => Real.log (hQdist σ b q)) = 1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ)`. Simplify using `only [meanK, hdist, hcardE]`. Rewrite using `[Finset.mul_sum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsum_pos : 0 < (1 / (n : ℝ)) * ∑ σ, X σ` using `mul_pos (by positivity) (Finset.sum_pos (fun σ _ => hXpos σ) Finset.univ_nonempty)`. Establish `hstep : Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) ≤ Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ))))`. Apply `Real.log_le_log hsum_pos` to reduce the goal to its premises.

Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Rewrite using `[hsumX]`. Conclude with `hvb`. Rewrite using `[hmean, hdeg, hquot]`. Establish `hD1 : Real.log (D ^ (1 / (n : ℝ))) = 1 / (n : ℝ) * Real.log D` using `Real.log_rpow hdpos _`.

Rewrite using `[hD1]`. Establish `key : 1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤ 1 / 2 * (Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I))`. Rewrite using `[← hY]`. Conclude with `mul_le_mul_of_nonneg_left (hamgm.trans hstep) (by norm_num)`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hNr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_small_saturating_vector (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ hStd K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (hQdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by
  classical
  set m := r - k with hmdef
  have hm : 0 < m := by omega
  have hkm : k + m = r := by omega
  obtain ⟨c, hc, hli, hsp⟩ := exists_integral_completion hb hk.le
  have hdeg := latDeg_saturation hkm hbL c hc hli hsp
  set n := Module.finrank ℚ K with hndef
  have hn : 0 < n := Module.finrank_pos
  have hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = n := by
    rw [hndef, Module.finrank_eq_card_basis (integralBasis K)]
  have hcardE : Fintype.card (K →+* ℂ) = n := NumberField.Embeddings.card K ℂ
  set N := m * n with hNdef
  have hN : 0 < N := Nat.mul_pos hm hn
  have hcardJ : Fintype.card (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = N := by
    rw [Fintype.card_prod, Fintype.card_fin, hcardI]
  let eN : Fin N ≃ (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :=
    (Fintype.equivFinOfCardEq hcardJ).symm
  let w := hwv b c ∘ eN
  have hgw : gram ℝ w = (gram ℝ (hwv b c)).submatrix eN eN := by
    ext i j
    simp [gram_apply, w]
  set P := ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re with hPdef
  set D := |(NumberField.discr K : ℝ)| with hDdef
  have hdetw : (gram ℝ w).det = D ^ m * P := by
    rw [hgw, det_submatrix_equiv_self, det_gram_projectedLatticeVectors b hb c]
  have hdpos : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hPpos : 0 < P := Finset.prod_pos fun σ _ => quotGram_det_pos σ hb c hli
  have hGpos : 0 < (gram ℝ w).det := by rw [hdetw]; positivity
  have hwli : LinearIndependent ℝ w := linearIndependent_of_det_gram_ne_zero hGpos.ne'
  set Λ := (hStd K r).toAddSubgroup.map (hpvHom b) with hΛ
  have hwmem : ∀ i, w i ∈ Λ := fun i => orthProjVector_mem b c hc (eN i)
  have hrange : Set.range w = Set.range (hwv b c) := eN.surjective.range_comp _
  set I := (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
    Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex (hStd K r).toAddSubgroup with hIdef
  have hrel : (Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex Λ = I := by
    rw [hrange]; exact relIndex_orthProj_lattice hb c hc
  have hI0 : I ≠ 0 := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg (hStd K r) standardLattice_fg (Fin.append b c)
      (fun x _ => hsp x)
    have hle : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) ≤
        ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Submodule.mem_sup_left ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩
      · rw [Fin.append_right]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
    have hdvd := AddSubgroup.relIndex_dvd_of_le_left (hStd K r).toAddSubgroup
      (show (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup ≤
        (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup
        from hle)
    intro h0
    rw [← hIdef, h0] at hdvd
    exact h1 (Nat.eq_zero_of_zero_dvd hdvd)
  obtain ⟨v, hvΛ, hv0, hvb⟩ := exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex hN w hwli Λ hwmem (by rw [hrel]; exact hI0)
  rw [hrel, hdetw] at hvb
  obtain ⟨q, hqL, rfl⟩ := AddSubgroup.mem_map.mp hvΛ
  have hq : q ∉ Submodule.span K (Set.range b) := fun h => hv0 ((projectedVector_eq_zero_iff hb q).mpr h)
  have hqL' : q ∈ hStd K r := hqL
  rw [mem_standardLattice_iff] at hqL'
  choose q' hq' using hqL'
  have hqq : (fun i => ((q' i : 𝓞 K) : K)) = q := funext hq'
  refine ⟨q', by rw [hqq]; exact hq, ?_⟩
  rw [hqq]
  set X : (K →+* ℂ) → ℝ := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)) with hX
  have hXpos : ∀ σ, 0 < X σ := fun σ => normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ hb hq)
  have hdist : ∀ σ, Real.log (hQdist σ b q) = Real.log (X σ) / 2 := fun σ => by
    rw [quotDist_eq_sqrt_norm σ hb, Real.log_sqrt (hXpos σ).le]
  have hsumX : ∑ σ, X σ = ‖hpvHom b q‖ ^ 2 := by
    show _ = ‖hpv b q‖ ^ 2
    rw [norm_orthProj_sq_sum hb]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (hXpos σ).le]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm : ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤ Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) := by
    have hw0 : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => by positivity
    have hw1 : ∑ σ ∈ (Finset.univ : Finset (K →+* ℂ)), 1 / (n : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, hcardE, nsmul_eq_mul]
      field_simp
    have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => 1 / (n : ℝ)) X hw0
      hw1 (fun σ _ => (hXpos σ).le)
    have hprod : 0 < ∏ σ, X σ ^ (1 / (n : ℝ)) :=
      Finset.prod_pos fun σ _ => Real.rpow_pos_of_pos (hXpos σ) _
    have hlog := Real.log_le_log hprod h
    rw [Real.log_prod (fun σ _ => (Real.rpow_pos_of_pos (hXpos σ) _).ne')] at hlog
    simp only [Real.log_rpow (hXpos _)] at hlog
    rw [Finset.mul_sum]
    exact hlog
  have hIr : (0 : ℝ) < I := by exact_mod_cast Nat.pos_of_ne_zero hI0
  have hquot : ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c =
      Real.log I - 1 / 2 * Real.log P := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotDeg]
    rw [hPdef, Real.log_prod (fun σ _ => (quotGram_det_pos σ hb c hli).ne')]
  have hlogG : Real.log (D ^ m * P / (I : ℝ) ^ 2) =
      m * Real.log D + Real.log P - 2 * Real.log I := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hNr : (N : ℝ) = m * n := by rw [hNdef]; push_cast; ring
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hY : Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) =
      Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I) := by
    rw [show (1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ))) =
        (m : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) by rw [hNr]; field_simp]
    rw [Real.log_mul hmr.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow (by positivity), hlogG]
  have hmean : meanK (fun σ => Real.log (hQdist σ b q)) =
      1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) := by
    simp only [meanK, hdist, hcardE]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hsum_pos : 0 < (1 / (n : ℝ)) * ∑ σ, X σ :=
    mul_pos (by positivity) (Finset.sum_pos (fun σ _ => hXpos σ) Finset.univ_nonempty)
  have hstep : Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) ≤
      Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) := by
    apply Real.log_le_log hsum_pos
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hsumX]
    exact hvb
  rw [hmean, hdeg, hquot]
  have hD1 : Real.log (D ^ (1 / (n : ℝ))) = 1 / (n : ℝ) * Real.log D := Real.log_rpow hdpos _
  rw [hD1]
  have key : 1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤
      1 / 2 * (Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I)) := by
    rw [← hY]
    exact mul_le_mul_of_nonneg_left (hamgm.trans hstep) (by norm_num)
  refine key.trans (le_of_eq ?_)
  rw [hNr]
  field_simp
  ring

end Main

end ReciprocityTheory.ChartRestriction.G.T0
