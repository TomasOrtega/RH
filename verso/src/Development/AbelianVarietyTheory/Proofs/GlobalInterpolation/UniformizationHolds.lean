import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds

noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

/- English proof (translation)
Rewrite using `[AddSubgroup.map_map]`. Establish `: cj.comp cj = AddMonoidHom.id ℂ` using `by ext z; simp [cj_apply]`. Rewrite using `[this, AddSubgroup.map_id]`.
-/
theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

/- English proof (translation)
Unfold `eisG`. Set `e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0}` to `{ toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩ invFun := fun w => ⟨starRingEnd ℂ w.1, by`. Take `⟨v, hv, hv'⟩` from `AddSubgroup.mem_map.1 w.2.1`. Establish `: starRingEnd ℂ w.1 = v` using `by rw [← hv']; simp [cj_apply]`. Rewrite using `[this]; exact hv, by simpa using w.2.2⟩`.

Use `left_inv := fun w => by ext; simp`. Use `right_inv := fun w => by ext; simp }`. Rewrite using `[← e.tsum_eq, Complex.conj_tsum]`. Use `congr 1`. Use extensionality with `w`.

Use `show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))`. Simplify using `[map_div₀, map_pow]`.
-/
theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

/- English proof (translation)
Unfold `g2`. Rewrite using `[eisG_map_cj, map_mul, map_ofNat]`.
-/
theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

/- English proof (translation)
Unfold `g3`. Rewrite using `[eisG_map_cj, map_mul, map_ofNat]`.
-/
theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

/- English proof (translation)
Unfold `Formalism.MainNotions.TaylorLogMetric.discr`. Rewrite using `[eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]`.
-/
theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

/- English proof (translation)
Establish `hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩` using `dif_pos h2`. Establish `hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩` using `dif_pos h3`. Establish `hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1`. Apply `M.val.injective` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]`.

Conclude with `h1`. Establish `hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1`. Rewrite using `[← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]`. Take `⟨Λ', -, h2', h3'⟩` from `(hU _ _ (by rw [hab]; exact one_ne_zero)).1`. Establish `hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ))` using `⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩`.

Establish `hs` using `Classical.epsilon_spec hex`. Establish `e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩` using `hs.1.trans (by rw [hl2])`. Establish `e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩` using `hs.2.trans (by rw [hl3])`. Use `⟨e2, e3, ?_⟩` and prove the remaining obligations. Use `show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1`.

Rewrite using `[e2, e3, hab]`.
-/
theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

/- English proof (translation)
Use `haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host`. Establish `h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E)`. Rewrite using `[conjO, RingOfIntegers.mapRingEquiv_apply]`. Conclude with `AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)`. Rewrite using `[h]`.

Conclude with `D.host.toHostAx.conjE_apply _ _`.
-/
theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

/- English proof (translation)
Unfold `lamOf`. Rewrite using `[AddMonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, ha, rfl⟩, rfl⟩`. Use `⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩` and prove the remaining obligations. Rewrite using `[phi_conjO, cj_apply, map_mul]`. Introduce and unpack `⟨b, hb, rfl⟩`.

Rewrite `hb` using `[Ideal.mem_map_of_equiv]`. Take `⟨a, ha, rfl⟩` from `hb`. Conclude with `⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩`.
-/
theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
Use `⟨fun x => ?_, h.2.1, h.2.2⟩` and prove the remaining obligations. Use `h.1 (D.eTau.symm 1) (x : D.host.E)` as an intermediate fact. Rewrite `this` using `[show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2]`. Then use the resulting hypothesis.
-/
theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

/- English proof (translation)
Introduce `hU hCE _ D cc δ M _ t hS ρ`. Take `⟨hcc, hδ, hM, -⟩` from `hS`. Establish `h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ`. Establish `h2 : g2 (lamOf D cc δ) ∈ M` using `hM.2.1`. Establish `h3 : g3 (lamOf D cc δ) ∈ M` using `hM.2.2`.

Establish `hsp` using `fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1`. Use `⟨(hsp ρ).2.2, ?_⟩` and prove the remaining obligations. Take `⟨⟨c, hcH, -⟩, hC2, -⟩` from `hCE D cc δ hcc hδ M (containsData hM)`. Distinguish the cases in `hρ : EquidistributedConjugates.FixesK D M ρ`. Take `⟨x, hx, hxe⟩` from `hcH ⟨ρ, hρ⟩`.

Conclude with `⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩`. Take `⟨hρ', -⟩` from `hC2 ρ hρ`. Take `⟨x, hx, hxe⟩` from `hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩`. Establish `hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU`. Establish `hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)`.

Apply `hUI` to reduce the goal to its premises. Rewrite using `[discr_map_cj, (hsp ρ).2.2, map_one]`. Conclude with `one_ne_zero`. Rewrite using `[eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]`. Conclude with `(EquidistributedConjugates.conjEmb_apply _ _ _).symm`.

Rewrite using `[eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]`. Conclude with `(EquidistributedConjugates.conjEmb_apply _ _ _).symm`. Establish `hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj`. Rewrite using `[← hmap, map_cj_map_cj]`. Use `⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩` and prove the remaining obligations.

Introduce `hbot`. Rewrite `hbot` using `[Ideal.map_eq_bot_iff_of_injective (conjO D).injective]`. Conclude with `nonZeroDivisors.coe_ne_zero _ hbot`.
-/
theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
Introduce `a b h`. Use `⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩` and prove the remaining obligations. Take `⟨L, h2, h3⟩` from `GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h`. Take `⟨e2, e3, hΔ, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)`. Conclude with `⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩`.
-/
theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

/- English proof (translation)
The claim follows from `conj_lattice uniformization_holds`.
-/
theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
