import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfMulMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotentStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.PerDat

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := k) (t := s.image k) (fun i hi => Finset.mem_image_of_mem k hi)]`. Use `(Finset.sum_le_card_nsmul _ _ B fun y hy => ?_).trans ?_` and prove the remaining obligations. Take `⟨i₀, hi, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `h i₀ hi`. Rewrite using `[nsmul_eq_mul]`.

Conclude with `mul_le_mul_of_nonneg_right hM hB`.
-/
theorem sum_le_of_fibres {ι α : Type} [DecidableEq α] (s : Finset ι) (k : ι → α) (f : ι → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hM : ((s.image k).card : ℝ) ≤ M) (h : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => k i = k i₀), f i ≤ B) :
    ∑ i ∈ s, f i ≤ M * B := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := s.image k) (fun i hi => Finset.mem_image_of_mem k hi)]
  refine (Finset.sum_le_card_nsmul _ _ B fun y hy => ?_).trans ?_
  · obtain ⟨i₀, hi, rfl⟩ := Finset.mem_image.1 hy
    exact h i₀ hi
  · rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hM hB

section Carry
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Carr (s : V ≃ₗ[K] V) (A B : FlagD H r) : Prop := ∀ a : Fin (r + 1), s (A.e a) - B.e a ∈ B.Xa a.val

/- English proof (translation)
Establish `: A.Xa n ≤ (B.Xa n).comap (s : V →ₗ[K] V)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Use `Submodule.add_mem _ (AdaptInv.xa_mono B (le_of_lt hb) (h b.castSucc)) (AdaptInv.e_mem_xa B b hb)` as an intermediate fact. Simplify using `using this`.

Conclude with `this hx`.
-/
theorem Carr.map_xa {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : Carr s A B) (n : ℕ) {x : V} (hx : x ∈ A.Xa n) :
    s x ∈ B.Xa n := by
  have : A.Xa n ≤ (B.Xa n).comap (s : V →ₗ[K] V) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have := Submodule.add_mem _ (AdaptInv.xa_mono B (le_of_lt hb) (h b.castSucc)) (AdaptInv.e_mem_xa B b hb)
    simpa using this
  exact this hx

/- English proof (translation)
Introduce `a` and use `by have := Submodule.add_mem _ (h'.map_xa _ (h a)) (h' a) simpa using this`.
-/
theorem Carr.trans {s t : V ≃ₗ[K] V} {A B C : FlagD H r} (h : Carr s A B) (h' : Carr t B C) :
    Carr (t * s) A C := fun a => by
  have := Submodule.add_mem _ (h'.map_xa _ (h a)) (h' a)
  simpa using this

/- English proof (translation)
Introduce `a` and use `h a`.
-/
theorem carr_of_sameGr {A B : FlagD H r} (h : SameGr B A) : Carr 1 A B := fun a => h a

/- English proof (translation)
Introduce `a` and use `by rw [h a, sub_self]; exact zero_mem _`.
-/
theorem carr_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s A B := fun a => by
  rw [h a, sub_self]; exact zero_mem _

/- English proof (translation)
The claim follows from `carr_of_eq fun a => by rw [← h a]; exact s.symm_apply_apply _`.
-/
theorem carr_inv_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s⁻¹ B A :=
  carr_of_eq fun a => by rw [← h a]; exact s.symm_apply_apply _

/- English proof (translation)
Introduce `a` and use `by induction a using Fin.lastCases with | last => exact GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem h | cast b => exact h.2.2.1 b`.
-/
theorem carr_of_inN {s : V ≃ₗ[K] V} {A : FlagD H r} (h : A.InN (s : V →ₗ[K] V)) : Carr s A A := fun a => by
  induction a using Fin.lastCases with
  | last => exact GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem h
  | cast b => exact h.2.2.1 b

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))`. Consider the case `cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X A b))`.
-/
theorem flagFrameVector_mem_commonSubspace (A B : FlagD H r) (a : Fin (r + 1)) : A.e a ∈ V0 A B := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X A b))

end Carry

section Main
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {e : W →ₗ[K] V} {r : ℕ}

omit [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
/- English proof (translation)
Apply the tactic sequence `obtain ⟨hfull, hlift, -⟩ := GlobalTheory.DegCnt.NF.geometry K V H hK r N`. Establish `hX : N.F.X = F.X` using `AdaptInv.x_eq hN.2.1`. Establish `hV : V0 N.F N.F' = V0 F G` using `AdaptInv.sitesCommonSpace_v0_eq_Vp hN.2.1 hN.2.2`. Establish `hperp : ∀ (w : W) (a : Fin (r + 1)), H.B (F.e a) (e w) = 0` using `fun w => (he.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩)`. Establish `hinj : Function.Injective e`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`. Use `HW.nondeg w fun y => ?_` and prove the remaining obligations. Rewrite using `[← he.1, hw]`. Simplify using the standard rewrite rules.

Establish `h1 : LinearMap.range e ⊓ F.X = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨⟨w, rfl⟩, hw⟩`. Establish `: w = 0` using `HW.nondeg w fun y => by`. Rewrite using `[← he.1]`.

Conclude with `GlobalTheory.UnipStab.orth_X F (fun a => hperp y _) hw`. Simplify using `[this]`. Establish `h2 : N.Wt ⊓ F.X = ⊥`. Rewrite using `[eq_bot_iff, ← hlift.2.1, ← hX]`. Introduce and unpack `x ⟨hx, hx'⟩`.

Conclude with `⟨hx, (hfull.2.2.2.2.2.1 x hx').1 (hlift.1 x hx)⟩`. Establish `h3 : N.Wt ⊔ F.X = LinearMap.range e ⊔ F.X`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (fun x hx => (he.2 x).1 fun a => hlift.1 x hx _ ?_) le_sup_right` and prove the remaining obligations. Rewrite using `[hV]`.

Conclude with `flagFrameVector_mem_commonSubspace F G a`. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨x, hx, hx'⟩` from `hfull.2.2.2.2.2.2.2.1 (e w) fun a => by`. Establish `a1 : N.F.e a - F.e a ∈ F.X` using `AdaptInv.xa_mono F (Nat.lt_succ_iff.1 a.2) (hN.2.1 a)`.

Establish `a2` using `GlobalTheory.UnipStab.orth_X F (fun a => hperp w _) a1`. Simplify `a2` using `[hperp w a]`. Establish `a3 : e w - x ∈ N.Wt ⊔ F.X`. Use `(sup_le_sup_left (show II N.F N.F' ≤ F.X from hX ▸ inf_le_left) _) (hlift.2.2 _ hx')` and prove the remaining obligations. Use `Submodule.add_mem _ a3 (Submodule.mem_sup_right (hX ▸ hx))` as an intermediate fact.

Simplify using `using this`. Establish `d1` using `Submodule.finrank_sup_add_finrank_inf_eq N.Wt F.X`. Establish `d2` using `Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) F.X`. Rewrite `d1` using `[h2, h3]`. Rewrite `d2` using `[h1, LinearMap.finrank_range_of_inj hinj]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_wt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (he : IsEmb F HW e) (hN : Adapt F G 𝔡 N) : Module.finrank K N.Wt = Module.finrank K W := by
  obtain ⟨hfull, hlift, -⟩ := GlobalTheory.DegCnt.NF.geometry K V H hK r N
  have hX : N.F.X = F.X := AdaptInv.x_eq hN.2.1
  have hV : V0 N.F N.F' = V0 F G := AdaptInv.sitesCommonSpace_v0_eq_Vp hN.2.1 hN.2.2
  have hperp : ∀ (w : W) (a : Fin (r + 1)), H.B (F.e a) (e w) = 0 :=
    fun w => (he.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine HW.nondeg w fun y => ?_
    rw [← he.1, hw]; simp
  have h1 : LinearMap.range e ⊓ F.X = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    have : w = 0 := HW.nondeg w fun y => by
      rw [← he.1]
      exact GlobalTheory.UnipStab.orth_X F (fun a => hperp y _) hw
    simp [this]
  have h2 : N.Wt ⊓ F.X = ⊥ := by
    rw [eq_bot_iff, ← hlift.2.1, ← hX]
    rintro x ⟨hx, hx'⟩
    exact ⟨hx, (hfull.2.2.2.2.2.1 x hx').1 (hlift.1 x hx)⟩
  have h3 : N.Wt ⊔ F.X = LinearMap.range e ⊔ F.X := by
    apply le_antisymm
    · refine sup_le (fun x hx => (he.2 x).1 fun a => hlift.1 x hx _ ?_) le_sup_right
      rw [hV]; exact flagFrameVector_mem_commonSubspace F G a
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, hx, hx'⟩ := hfull.2.2.2.2.2.2.2.1 (e w) fun a => by
        have a1 : N.F.e a - F.e a ∈ F.X := AdaptInv.xa_mono F (Nat.lt_succ_iff.1 a.2) (hN.2.1 a)
        have a2 := GlobalTheory.UnipStab.orth_X F (fun a => hperp w _) a1
        simpa [hperp w a] using a2
      have a3 : e w - x ∈ N.Wt ⊔ F.X := by
        refine (sup_le_sup_left (show II N.F N.F' ≤ F.X from hX ▸ inf_le_left) _) (hlift.2.2 _ hx')
      have := Submodule.add_mem _ a3 (Submodule.mem_sup_right (hX ▸ hx))
      simpa using this
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt F.X
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) F.X
  rw [h2, h3] at d1
  rw [h1, LinearMap.finrank_range_of_inj hinj] at d2
  omega

/- English proof (translation)
Establish `hex : ∀ i ∈ s, ∃ σ : V ≃ₗ[K] V, F.InN (σ : V →ₗ[K] V) ∧ ∀ a, σ (N₀.F.e a) = (N i).F.e a ∧ σ (N₀.F'.e a) = (N i).F'.e a` using `fun i hi => by`. Take `⟨a1, -, a2, a3, a4, a5, -⟩` from `hN i hi`. Conclude with `GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent K V H hK r F N₀ (N i) h₀.2.1 a1.2.1 a2 a3 a4 a5`. Use `choose! σ hσ hσe using hex`. Establish `hcan : ∀ i, σ i • ((σ i)⁻¹ • Λ) = Λ` using `fun i => smul_inv_smul _ _`.

Establish `hmove : ∀ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.om ((σ i)⁻¹ • Λ) ∧ N₀.IsTerm g ((σ i)⁻¹ • Λ)` using `fun i hi => by`. Take `⟨a1, a2, -⟩` from `hN i hi`. Apply the tactic sequence `obtain ⟨N', b1, -, -, -, b2, -, b3⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N₀ (σ i) ((mem_isomGrp H _).2 (hσ i hi).1)`. Take `⟨c1, c2, -⟩` from `b3 g ((σ i)⁻¹ • Λ)`. Rewrite `c1`, `c2` using `[hcan]`.

Establish `hA : Adapt F (G i) 𝔡 N'`. Use `⟨b2.trans h₀.1, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[(b1 a).1, (hσe i hi a).1]`. Conclude with `a1.2.1 a`. Rewrite using `[(b1 a).2, (hσe i hi a).2]`.

Conclude with `a1.2.2 a`. Use `⟨c1 ▸ ((WeightInf.main K V H hK r).2 F (G i) 𝔡 Λ).2.1 N' hA, c2.1 ?_⟩` and prove the remaining obligations. Establish `haa : N'.aa = (N i).aa`. Use function extensionality and compare the values at `a`. Simplify using `only [NF.aa, hA.1, a1.1]`.

Rewrite using `[((adapt_invariants K V H hK r F (G i) 𝔡 N' hA).2.2.2.2.2.2.2.2 g Λ).1, haa]`. Conclude with `((adapt_invariants K V H hK r F (G i) 𝔡 (N i) a1).2.2.2.2.2.2.2.2 g Λ).1.1 a2`. Use `(Finset.sum_le_sum fun i hi => (hmove i hi).1).trans ?_` and prove the remaining obligations. Rewrite using `[← finrank_wt hK he h₀]`. Use `GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le K V H hK r N₀ g Λ ι s (fun i => (σ i)⁻¹ • Λ) hg ht₀ (fun i hi => ?_) ?_` and prove the remaining obligations.

Take `⟨a1, -, -, -, -, -, a2⟩` from `hN i hi`. Establish `hc : Carr (1 * (σ i * 1)) G₀ (G i)` using `((carr_of_sameGr (AdaptInv.sameGr_symm h₀.2.2)).trans (carr_of_eq fun a => (hσe i hi a).2)).trans (carr_of_sameGr a1.2.2)`. Rewrite `hc` using `[one_mul, mul_one]`. Take `⟨d1, d2⟩` from `GlobalTheory.T.embeddedDatum_invariant_under_unipotent K V W H HW e hK r F G₀ (G i) 𝔡 N₀ g he h₀`. Take `⟨e1, -, e2⟩` from `d1 (σ i) ((σ i)⁻¹ • Λ) (hσ i hi) hc`.

Rewrite `e1`, `e2` using `[hcan]`. Take `⟨f1, f2⟩` from `d2 ((σ i)⁻¹ • Λ) Λ (e1.symm.trans a2)`. Use `⟨(hmove i hi).2, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AdaptInv.latL_eq h₀.2.1 h₀.2.2, AdaptInv.latL_eq h₀.2.1 h₀.2.2, e2]`. Rewrite using `[AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, f1]`.

Rewrite using `[AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, f2]`. Introduce and unpack `i hi i' hi' ⟨ρ, hρ, hρe⟩`. Take `⟨r1, r2⟩` from `(GlobalTheory.UnipStab.mem_R N₀ ρ).1 hρ`. Use `hinj i hi i' hi' ⟨σ i' * (ρ * (σ i)⁻¹), GlobalTheory.UnipStab.inN_mul (hσ i' hi') (GlobalTheory.UnipStab.inN_mul (AdaptInv.inN_of (AdaptInv.sameGr_symm h₀.2.1) _ r1) (GlobalTheory.UnipStab.inN_inv (hσ i hi))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul]`.

Conclude with `(congrArg (fun L => σ i' • L) hρe).trans (hcan i')`. Establish `hc : Carr (1 * (σ i' * (ρ * ((σ i)⁻¹ * 1)))) (G i) (G i')` using `((((carr_of_sameGr (AdaptInv.sameGr_symm (hN i hi).1.2.2)).trans (carr_inv_of_eq fun a => (hσe i hi a).2)).trans (carr_of_inN r2)).trans (carr_of_eq fun a => (hσe i' hi' a).2)).trans (carr_of_sameGr (hN i' hi').1.2.2)`. Rewrite `hc` using `[one_mul, mul_one]`. Conclude with `hc`.
-/
theorem one_class (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F : FlagD H r} {𝔡 : Ideal (𝓞 K)} {g : ℕ} {Λ : Submodule (𝓞 K) V}
    {ι : Type} (s : Finset ι) (G : ι → FlagD H r) (N : ι → NF H r) (G₀ : FlagD H r) (N₀ : NF H r) (hg : 1 ≤ g)
    (he : IsEmb F HW e) (h₀ : Adapt F G₀ 𝔡 N₀) (ht₀ : N₀.IsTerm g Λ)
    (hN : ∀ i ∈ s, Adapt F (G i) 𝔡 (N i) ∧ (N i).IsTerm g Λ ∧ N₀.j = (N i).j ∧ N₀.c = (N i).c ∧ N₀.T = (N i).T ∧
      pairM N₀.F N₀.F' N₀.j = pairM (N i).F (N i).F' (N i).j ∧ datOf F (G i) e g Λ = datOf F G₀ e g Λ)
    (hinj : ∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') :
    ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.NT ^ 2 * ((N₀.Del / N₀.gI g Λ) ^ ((Module.finrank K W : ℝ) / 2) *
      N₀.Del ^ (cf K + 2) * (N₀.Db * N₀.Del * N₀.NT) ^ (10000 * (r + 1) ^ 3)) := by
  have hex : ∀ i ∈ s, ∃ σ : V ≃ₗ[K] V, F.InN (σ : V →ₗ[K] V) ∧
      ∀ a, σ (N₀.F.e a) = (N i).F.e a ∧ σ (N₀.F'.e a) = (N i).F'.e a := fun i hi => by
    obtain ⟨a1, -, a2, a3, a4, a5, -⟩ := hN i hi
    exact GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent K V H hK r F N₀ (N i) h₀.2.1 a1.2.1 a2 a3 a4 a5
  choose! σ hσ hσe using hex
  have hcan : ∀ i, σ i • ((σ i)⁻¹ • Λ) = Λ := fun i => smul_inv_smul _ _
  have hmove : ∀ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.om ((σ i)⁻¹ • Λ) ∧ N₀.IsTerm g ((σ i)⁻¹ • Λ) := fun i hi => by
    obtain ⟨a1, a2, -⟩ := hN i hi
    obtain ⟨N', b1, -, -, -, b2, -, b3⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N₀ (σ i) ((mem_isomGrp H _).2 (hσ i hi).1)
    obtain ⟨c1, c2, -⟩ := b3 g ((σ i)⁻¹ • Λ)
    rw [hcan] at c1 c2
    have hA : Adapt F (G i) 𝔡 N' := by
      refine ⟨b2.trans h₀.1, fun a => ?_, fun a => ?_⟩
      · rw [(b1 a).1, (hσe i hi a).1]; exact a1.2.1 a
      · rw [(b1 a).2, (hσe i hi a).2]; exact a1.2.2 a
    refine ⟨c1 ▸ ((WeightInf.main K V H hK r).2 F (G i) 𝔡 Λ).2.1 N' hA, c2.1 ?_⟩
    have haa : N'.aa = (N i).aa := by
      funext a; simp only [NF.aa, hA.1, a1.1]
    rw [((adapt_invariants K V H hK r F (G i) 𝔡 N' hA).2.2.2.2.2.2.2.2 g Λ).1, haa]
    exact ((adapt_invariants K V H hK r F (G i) 𝔡 (N i) a1).2.2.2.2.2.2.2.2 g Λ).1.1 a2
  refine (Finset.sum_le_sum fun i hi => (hmove i hi).1).trans ?_
  rw [← finrank_wt hK he h₀]
  refine GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le K V H hK r N₀ g Λ ι s (fun i => (σ i)⁻¹ • Λ) hg ht₀ (fun i hi => ?_) ?_
  · obtain ⟨a1, -, -, -, -, -, a2⟩ := hN i hi
    have hc : Carr (1 * (σ i * 1)) G₀ (G i) :=
      ((carr_of_sameGr (AdaptInv.sameGr_symm h₀.2.2)).trans (carr_of_eq fun a => (hσe i hi a).2)).trans
        (carr_of_sameGr a1.2.2)
    rw [one_mul, mul_one] at hc
    obtain ⟨d1, d2⟩ := GlobalTheory.T.embeddedDatum_invariant_under_unipotent K V W H HW e hK r F G₀ (G i) 𝔡 N₀ g he h₀
    obtain ⟨e1, -, e2⟩ := d1 (σ i) ((σ i)⁻¹ • Λ) (hσ i hi) hc
    rw [hcan] at e1 e2
    obtain ⟨f1, f2⟩ := d2 ((σ i)⁻¹ • Λ) Λ (e1.symm.trans a2)
    refine ⟨(hmove i hi).2, ?_, ?_, ?_⟩
    · rw [AdaptInv.latL_eq h₀.2.1 h₀.2.2, AdaptInv.latL_eq h₀.2.1 h₀.2.2, e2]
    · rw [AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, f1]
    · rw [AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, f2]
  · rintro i hi i' hi' ⟨ρ, hρ, hρe⟩
    obtain ⟨r1, r2⟩ := (GlobalTheory.UnipStab.mem_R N₀ ρ).1 hρ
    refine hinj i hi i' hi' ⟨σ i' * (ρ * (σ i)⁻¹), GlobalTheory.UnipStab.inN_mul (hσ i' hi') (GlobalTheory.UnipStab.inN_mul
      (AdaptInv.inN_of (AdaptInv.sameGr_symm h₀.2.1) _ r1) (GlobalTheory.UnipStab.inN_inv (hσ i hi))), ?_, ?_⟩
    · rw [mul_smul, mul_smul]
      exact (congrArg (fun L => σ i' • L) hρe).trans (hcan i')
    · have hc : Carr (1 * (σ i' * (ρ * ((σ i)⁻¹ * 1)))) (G i) (G i') :=
        ((((carr_of_sameGr (AdaptInv.sameGr_symm (hN i hi).1.2.2)).trans
          (carr_inv_of_eq fun a => (hσe i hi a).2)).trans (carr_of_inN r2)).trans
          (carr_of_eq fun a => (hσe i' hi' a).2)).trans (carr_of_sameGr (hN i' hi').1.2.2)
      rw [one_mul, mul_one] at hc
      exact hc
end Main

section Count
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def sqM (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) : Matrix (Fin j) (Fin j) K :=
  fun a b => H.B (N.F.e (Fin.castLE hj a)) (N.F'.e (Fin.castLE hj b))

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨N.w, N.sgn, N.pair⟩`.
-/
theorem sqM_shape (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) (h : N.j = j) :
    ∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, sqM N j hj a b = w.mat a b * ((sgn b : ℤ) : K) := by
  subst h
  exact ⟨N.w, N.sgn, N.pair⟩

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Unfold `pairM`. Use `split_ifs with hab`. Conclude with `congrFun (congrFun h ⟨a.val, hab.1⟩) ⟨b.val, hab.2⟩`. Both sides reduce to the same expression.
-/
theorem pairM_eq {N N' : NF H r} {j : ℕ} {hj : j ≤ r + 1} (h : sqM N j hj = sqM N' j hj) :
    pairM N.F N.F' j = pairM N'.F N'.F' j := by
  funext a b
  unfold pairM
  split_ifs with hab
  · exact congrFun (congrFun h ⟨a.val, hab.1⟩) ⟨b.val, hab.2⟩
  · rfl

end Count

end GlobalTheory.DegAsm.PerDat

namespace GlobalTheory.DegAsm
open PerDat

/- English proof (translation)
Introduce `K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F 𝔡 g j T x δ Λ d Del Db ι s G hg hx hDel hDb he hN hd hinj`. Establish `hDel0 : 0 < Del` using `by linarith`. Establish `hDb0 : 0 < Db` using `by linarith`. Break down `s.eq_empty_or_nonempty with rfl | ⟨i₁, hi₁⟩` into its components or cases. Rewrite using `[Finset.sum_empty]`.

Unfold `datBd`. Check the signs of the components of the expression. Use `haveI : Nonempty (NF H r) := ⟨(hN i₁ hi₁).choose⟩`. Use `choose! N hA ht hj hT hD hB hI using hN`. Establish `hjr : j ≤ r` using `hj i₁ hi₁ ▸ (N i₁).j_le`.

Establish `hjr' : j ≤ r + 1` using `by omega`. Establish `c1 : ((s.image fun i => sqM (N i) j hjr').card : ℝ) ≤ 8 ^ r`. Establish `h1` using `GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le K j δ`. Establish `h2` using `(Set.encard_le_encard (s := ((s.image fun i => sqM (N i) j hjr' : Finset _) : Set _)) ?_).trans h1`. Rewrite `h2` using `[Set.encard_coe_eq_coe_finsetCard]`.

Establish `h3 : (s.image fun i => sqM (N i) j hjr').card ≤ 8 ^ j` using `by exact_mod_cast h2`. Establish `h4 : 8 ^ j ≤ 8 ^ r` using `Nat.pow_le_pow_right (by norm_num) hjr`. Conclude with `h3.trans h4` after adjusting the coercions. Introduce `P hP`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hP)`.

Use `⟨sqM_shape _ _ _ (hj i hi), fun l hl => ?_⟩` and prove the remaining obligations. Establish `hl' : l ≤ r + 1` using `by omega`. Rewrite using `[← (hd i hi).1, lab, dif_pos ⟨hl, hl'⟩, ← AdaptInv.dl_eq (hA i hi).2.1 (hA i hi).2.2]`. Both sides reduce to the same expression. Establish `c2 : ((s.image fun i => (N i).c).card : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K))`.

Establish `h1` using `GlobalTheory.DegCnt.NormOneCount.main K hK Del hDel`. Establish `h2` using `(ENat.toENNReal_le.2 (Set.encard_le_encard (s := ((s.image fun i => (N i).c : Finset _) : Set _)) ?_)).trans h1`. Rewrite `h2` using `[Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Conclude with `h2`. Introduce `c hc`.

Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hc)`. Use `⟨(N i).c_norm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hD i hi]`. Conclude with `GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le K V H hK r (N i) g Λ hg (ht i hi)`. Establish `c3 : ((s.image fun i => (sqM (N i) j hjr', (N i).c)).card : ℝ) ≤ 8 ^ r * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K)))`.

Establish `h1 : (s.image fun i => (sqM (N i) j hjr', (N i).c)).card ≤ (s.image fun i => sqM (N i) j hjr').card * (s.image fun i => (N i).c).card`. Rewrite using `[← Finset.card_product]`. Use `Finset.card_le_card fun p hp => ?_` and prove the remaining obligations. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 hp`. Conclude with `Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩`.

Use `le_trans ?_ (mul_le_mul c1 c2 (by positivity) (by positivity))` and prove the remaining obligations. Conclude with `h1` after adjusting the coercions. Use `(sum_le_of_fibres s _ _ (((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ 2 * ((Del / x) ^ ((Module.finrank K W : ℝ) / 2) * Del ^ (cf K + 2) * (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3))) _ (by positivity) c3 fun i₀ hi₀ => ?_).tr …` and prove the remaining obligations. Use `one_class (HW := HW) (e := e) hK (s.filter fun i => (sqM (N i) j hjr', (N i).c) = (sqM (N i₀) j hjr', (N i₀).c)) G N (G i₀) (N i₀) hg he (hA i₀ hi₀) (ht i₀ hi₀) (fun i hi => ?_) fun i hi i' hi' => hinj i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1` as an intermediate fact. Rewrite `this` using `[NF.NT, hT i₀ hi₀, hD i₀ hi₀, hB i₀ hi₀, hI i₀ hi₀]`.

Conclude with `this`. Take `⟨hi, hk⟩` from `Finset.mem_filter.1 hi`. Take `⟨k1, k2⟩` from `Prod.mk.inj hk`. Use `⟨hA i hi, ht i hi, (hj i₀ hi₀).trans (hj i hi).symm, k2.symm, (hT i₀ hi₀).trans (hT i hi).symm, ?_, (hd i hi).2.trans (hd i₀ hi₀).2.symm⟩` and prove the remaining obligations. Rewrite using `[hj i₀ hi₀, hj i hi]`.

Conclude with `pairM_eq k1.symm`. Unfold `datBd`. Rewrite using `[show 3 * cf K + 6 = 2 * (2 + cf K) + (cf K + 2) by ring, Real.rpow_add hDel0 (2 * (2 + cf K))]`. Generalize the expression as in `(Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3) = y`. Generalize the expression as in `Del ^ (2 * (2 + cf K)) = y₁`.

Generalize the expression as in `Del ^ (cf K + 2) = y₂`. Generalize the expression as in `(Del / x) ^ ((Module.finrank K W : ℝ) / 2) = y₃`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_weights_per_datum : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (g j T x : ℕ) (δ : ℕ → K) (Λ : Submodule (𝓞 K) V) (d : Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W)) (Del Db : ℝ) (ι : Type) (s : Finset ι) (G : ι → FlagD H r), 1 ≤ g → 1 ≤ x → 1 ≤ Del → 1 ≤ Db → IsEmb F HW e → (∀ i ∈ s, ∃ N : NF H r, Adapt F (G i) 𝔡 N ∧ N.IsTerm g Λ ∧ N.j = j ∧ N.T = T ∧ N.Del = Del ∧ N.Db = Db ∧ N.gI g Λ = x) → (∀ i ∈ s, lab F (G i) j = δ ∧ datOf F (G i) e g Λ = d) → (∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') → ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ datBd K (Module.finrank K W) r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F 𝔡 g j T x δ Λ d Del Db ι s G hg hx hDel hDb he hN hd hinj
  have hDel0 : 0 < Del := by linarith
  have hDb0 : 0 < Db := by linarith
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₁, hi₁⟩
  · rw [Finset.sum_empty]; unfold datBd; positivity
  haveI : Nonempty (NF H r) := ⟨(hN i₁ hi₁).choose⟩
  choose! N hA ht hj hT hD hB hI using hN
  have hjr : j ≤ r := hj i₁ hi₁ ▸ (N i₁).j_le
  have hjr' : j ≤ r + 1 := by omega
  have c1 : ((s.image fun i => sqM (N i) j hjr').card : ℝ) ≤ 8 ^ r := by
    have h1 := GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le K j δ
    have h2 := (Set.encard_le_encard (s := ((s.image fun i => sqM (N i) j hjr' : Finset _) : Set _)) ?_).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard] at h2
      have h3 : (s.image fun i => sqM (N i) j hjr').card ≤ 8 ^ j := by exact_mod_cast h2
      have h4 : 8 ^ j ≤ 8 ^ r := Nat.pow_le_pow_right (by norm_num) hjr
      exact_mod_cast h3.trans h4
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hP)
      refine ⟨sqM_shape _ _ _ (hj i hi), fun l hl => ?_⟩
      have hl' : l ≤ r + 1 := by omega
      rw [← (hd i hi).1, lab, dif_pos ⟨hl, hl'⟩, ← AdaptInv.dl_eq (hA i hi).2.1 (hA i hi).2.2]
      rfl
  have c2 : ((s.image fun i => (N i).c).card : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K)) := by
    have h1 := GlobalTheory.DegCnt.NormOneCount.main K hK Del hDel
    have h2 := (ENat.toENNReal_le.2
      (Set.encard_le_encard (s := ((s.image fun i => (N i).c : Finset _) : Set _)) ?_)).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
      exact h2
    · intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
      refine ⟨(N i).c_norm, ?_⟩
      rw [← hD i hi]
      exact GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le K V H hK r (N i) g Λ hg (ht i hi)
  have c3 : ((s.image fun i => (sqM (N i) j hjr', (N i).c)).card : ℝ) ≤
      8 ^ r * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K))) := by
    have h1 : (s.image fun i => (sqM (N i) j hjr', (N i).c)).card ≤
        (s.image fun i => sqM (N i) j hjr').card * (s.image fun i => (N i).c).card := by
      rw [← Finset.card_product]
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩
    refine le_trans ?_ (mul_le_mul c1 c2 (by positivity) (by positivity))
    exact_mod_cast h1
  refine (sum_le_of_fibres s _ _ (((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ 2 * ((Del / x) ^ ((Module.finrank K W : ℝ) / 2) *
      Del ^ (cf K + 2) * (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3))) _ (by positivity) c3
      fun i₀ hi₀ => ?_).trans (le_of_eq ?_)
  · have := one_class (HW := HW) (e := e) hK
      (s.filter fun i => (sqM (N i) j hjr', (N i).c) = (sqM (N i₀) j hjr', (N i₀).c)) G N (G i₀) (N i₀) hg he
      (hA i₀ hi₀) (ht i₀ hi₀) (fun i hi => ?_)
      fun i hi i' hi' => hinj i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1
    · rw [NF.NT, hT i₀ hi₀, hD i₀ hi₀, hB i₀ hi₀, hI i₀ hi₀] at this
      exact this
    · obtain ⟨hi, hk⟩ := Finset.mem_filter.1 hi
      obtain ⟨k1, k2⟩ := Prod.mk.inj hk
      refine ⟨hA i hi, ht i hi, (hj i₀ hi₀).trans (hj i hi).symm, k2.symm, (hT i₀ hi₀).trans (hT i hi).symm, ?_,
        (hd i hi).2.trans (hd i₀ hi₀).2.symm⟩
      rw [hj i₀ hi₀, hj i hi]
      exact pairM_eq k1.symm
  · unfold datBd
    rw [show 3 * cf K + 6 = 2 * (2 + cf K) + (cf K + 2) by ring, Real.rpow_add hDel0 (2 * (2 + cf K))]
    generalize (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3) = y
    generalize Del ^ (2 * (2 + cf K)) = y₁
    generalize Del ^ (cf K + 2) = y₂
    generalize (Del / x) ^ ((Module.finrank K W : ℝ) / 2) = y₃
    ring

end GlobalTheory.DegAsm
