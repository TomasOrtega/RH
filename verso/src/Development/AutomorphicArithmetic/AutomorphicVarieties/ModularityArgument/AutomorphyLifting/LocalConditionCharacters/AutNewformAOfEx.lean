import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.NewDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AUpDownOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AIsoTwOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV UpperTheory.V.Z.Win.RR
open scoped Matrix Pointwise

open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
open private UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.flag_stable UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.dual_det UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.ss_tw UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cyc_inf UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.charpoly_smul UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cont_cycBar from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
open private cc_ex kills_cc kills_pow pairing2 from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
open private UpperTheory.V.Z.Win.polarized_of_att from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AUpDownOf
open private UpperTheory.V.Z.Win.tw_tw_inv from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AIsoTwOf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.RR

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Take `⟨M, χ, hM, hχ, hθ⟩` from `hdet`. Rewrite `hθ` using `[zpow_zero, one_mul]`. Take `⟨k, hk, hpow⟩` from `kills_pow hM hχ`. Use `(algOfCyc P ℚ Ω l ι).1 _ ?_ fun w _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ m` using `(Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cont_cycBar ℚ Ω l))`.

Conclude with `h1`. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Use `⟨A, hA, m, k, hk, fun s _ => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, hθ, hpow]`.
-/
private theorem alg0 (P : HypothesesH) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (m : ℤ) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ m) := by
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  refine (algOfCyc P ℚ Ω l ι).1 _ ?_ fun w _ => ?_
  · have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ m :=
      (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cont_cycBar ℚ Ω l))
    exact h1
  · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, m, k, hk, fun s _ => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, hθ, hpow]

/- English proof (translation)
The claim follows from `alg0 P ι W hW hdet _`.
-/
private theorem alg_det (P : HypothesesH) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := alg0 P ι W hW hdet _

/- English proof (translation)
Establish `: IsGalois ℚ Ω` using `{}`. Use `Subgroup.quotient_finite_of_isOpen H hH` as an intermediate fact. Establish `: H.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `hn : H.normalCore.Normal` using `H.normalCore_normal`. Establish `hH' : IsOpen (H.normalCore : Set (G ℚ Ω))` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))`.

Establish `hk : H.normalCore.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Use `⟨H.normalCore, hH', fun w hw A hA => ?_⟩` and prove the remaining obligations. Establish `hAl : A.valuation (l : Ω) < 1` using `((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 w hA).2 hw`. Take `⟨s, hs, hs'⟩` from `UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cyc_inf hAl`. Establish `hs0 : s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F` using `ℚ) A := ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩`.

Establish `hinf : ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l (s ^ H.normalCore.index) ^ k ≠ 1` using `fun k hk0 h => by`. Rewrite `h` using `[map_pow, ← pow_mul]`. Conclude with `hs' _ (mul_ne_zero hk hk0) h`. Use `⟨⟨_, hs0, hinf⟩, ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw) hA`.

Establish `hfl' : IsFlagOn W (H.normalCore ⊓ Ine (F` using `ℚ) (g • B)) (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H.normalCore ⊓ Ine (F := ℚ) (g • B)).subtype) := by`. Take `⟨p, hp⟩` from `hfl`. Use `⟨p * (W g)⁻¹, fun t => ?_⟩` and prove the remaining obligations. Establish `hm : g⁻¹ * (t : G ℚ Ω) * g ∈ H ⊓ Ine (F` using `ℚ) B := ⟨H.normalCore_le (hn.conj_mem' _ t.2.1 g), GlobalTheory.PointIrredCompare.conj_mem_Ine_of_smul t.2.2⟩`. Establish `e1 : p * (W g)⁻¹ * W t * (p * (W g)⁻¹)⁻¹ = p * W (g⁻¹ * (t : G ℚ Ω) * g) * p⁻¹`.

Rewrite using `[map_mul, map_mul, map_inv]`. Use `group`. Take `⟨h1, h2⟩` from `hp ⟨_, hm⟩`. Rewrite using `[e1]`. Use `⟨h1, fun i => (h2 i).trans ?_⟩` and prove the remaining obligations.

Use `congr 1`. Express the relevant statement in the definitionally equal form `((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (g⁻¹ * (t : G ℚ Ω) * g) = ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) t`. Rewrite using `[map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]`. Conclude with `UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.flag_stable W (Dec (F := ℚ) (g • B)) (H.normalCore ⊓ Ine (F := ℚ) (g • B)) _ le_rfl (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d, by simpa using conj_mem_Ine ((Dec (F := ℚ) (g • B)).inv_mem hd) hs.2⟩) (fun i => (cycBar ℚ Ω l) ^ …`. Use `⟨_, hs0, fun h1 => hinf (e + e) (by omega) ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[MonoidHom.zpow_apply, MonoidHom.zpow_apply]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1`. Rewrite using `[pow_add]`. Conclude with `mul_eq_one_iff_eq_inv.2 h1) hfl'`.
-/
private theorem flag_all {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) {B : ValuationSubring Ω}
    (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∃ N : Subgroup (G ℚ Ω), IsOpen (N : Set (G ℚ Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∃ s ∈ N ⊓ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1) ∧
        ∃ κ, IsFlagOn W (Dec (F := ℚ) A) κ ∧ ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ N ⊓ Ine (F := ℚ) A →
          κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.normalCore, hH', fun w hw A hA => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 w hA).2 hw
  obtain ⟨s, hs, hs'⟩ := UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cyc_inf hAl
  have hs0 : s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) A :=
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hinf : ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l (s ^ H.normalCore.index) ^ k ≠ 1 := fun k hk0 h => by
    rw [map_pow, ← pow_mul] at h
    exact hs' _ (mul_ne_zero hk hk0) h
  refine ⟨⟨_, hs0, hinf⟩, ?_⟩
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw) hA
  have hfl' : IsFlagOn W (H.normalCore ⊓ Ine (F := ℚ) (g • B))
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H.normalCore ⊓ Ine (F := ℚ) (g • B)).subtype) := by
    obtain ⟨p, hp⟩ := hfl
    refine ⟨p * (W g)⁻¹, fun t => ?_⟩
    have hm : g⁻¹ * (t : G ℚ Ω) * g ∈ H ⊓ Ine (F := ℚ) B :=
      ⟨H.normalCore_le (hn.conj_mem' _ t.2.1 g), GlobalTheory.PointIrredCompare.conj_mem_Ine_of_smul t.2.2⟩
    have e1 : p * (W g)⁻¹ * W t * (p * (W g)⁻¹)⁻¹ = p * W (g⁻¹ * (t : G ℚ Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    obtain ⟨h1, h2⟩ := hp ⟨_, hm⟩
    rw [e1]
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    congr 1
    change ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (g⁻¹ * (t : G ℚ Ω) * g) = ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) t
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  exact UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.flag_stable W (Dec (F := ℚ) (g • B)) (H.normalCore ⊓ Ine (F := ℚ) (g • B)) _ le_rfl
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d, by simpa using conj_mem_Ine ((Dec (F := ℚ) (g • B)).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      refine ⟨_, hs0, fun h1 => hinf (e + e) (by omega) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl'

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : x ^ (a - b) = 1` using `by rw [zpow_sub, e, mul_inv_cancel]`. Use `h (a - b).natAbs (by omega) ?_` and prove the remaining obligations. Break down `Int.natAbs_eq (a - b) with h2 | h2` into its components or cases. Rewrite using `[← zpow_natCast, ← h2, h1]`.

Rewrite using `[← zpow_natCast, ← inv_inj, ← zpow_neg, ← h2, h1, inv_one]`.
-/
private theorem zpow_ne {C : Type} [Group C] {x : C} (h : ∀ k : ℕ, k ≠ 0 → x ^ k ≠ 1) {a b : ℤ} (e : x ^ a = x ^ b) : a = b := by
  by_contra hne
  have h1 : x ^ (a - b) = 1 := by rw [zpow_sub, e, mul_inv_cancel]
  refine h (a - b).natAbs (by omega) ?_
  rcases Int.natAbs_eq (a - b) with h2 | h2
  · rw [← zpow_natCast, ← h2, h1]
  · rw [← zpow_natCast, ← inv_inj, ← zpow_neg, ← h2, h1, inv_one]

/- English proof (translation)
Introduce `v`. Take `⟨hdet, L, _, _, _, _, _, hirr, ⟨η, σ₀, hσ₀, hησ, hηL⟩, ka, hka, hWit⟩` from `hU`. Use `haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩`. Take `⟨K, hK, hKC⟩` from `Z.Bc.exists_quad L Ω η σ₀ hσ₀ hησ hηL`.

Use `haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Use `haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L`. Use `haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm a.is_comm.comm`. Establish `ec : W.comp (galEmb ℚ L Ω) = (W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω)` using `MonoidHom.ext fun _ => rfl`.

Establish `hirr' : IsIrr ((W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω))` using `ec ▸ hirr`. Take `⟨P₁, a1, a2, a3⟩` from `Z.Bc.upQuadI_of P.toClassicalTheorems (Z.Bc.quadLiftRealToComplex_of_base_change P.bc) ℚ K Ω l ι hK W π hW hreg hatt ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr')`. Take `⟨Q, b1, b2, b3⟩` from `Z.Bc.upSolI_of P.toClassicalTheorems (Z.Bc.cyclicLiftRankTwo_of_cyclic_base_change P.cyc) K L Ω l ι _ P₁ (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) a1 a2 hirr'`. Rewrite `b2` using `[← ec]`. Establish `hWL : Continuous (W.comp (galEmb ℚ L Ω))` using `hW.comp (continuous_restrictScalarsHom ℚ L Ω)`.

Establish `hpol : Sol.Pol ι W`. Establish `halg` using `alg0 P ι W hW hdet 0`. Rewrite `halg` using `[zpow_zero, mul_one]`. Take `⟨M, χ, hM, hχ, hθ⟩` from `hdet`. Rewrite `hθ` using `[zpow_zero, one_mul]`.

Take `⟨c, hc⟩` from `cc_ex Ω`. Take `⟨J, hJ⟩` from `pairing2 W c`. Conclude with `⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J, halg, fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hJ⟩`. Establish `hQ` using `UpperTheory.V.Z.Win.polarized_of_att P one_le_two (UpperTheory.solvable_polarized_restriction ℚ L Ω l ι 2 W hpol) b2`. Establish `hka' : IsAlgChar ι ka`.

Take `⟨h1, art, χ, a, h2, h3, h4⟩` from `hka`. Conclude with `⟨χ, h1, art, a, h2, h3, h4⟩`. Establish `hWA : WitA ι (W.comp (galEmb ℚ L Ω))`. Use `(aIsoTwOf flagLaws ImaginaryQuadraticEtaCharacter.winTw P.toClassicalTheorems L Ω l ι 2 _ hWit).2 ka⁻¹ ((algOfCyc P L Ω l ι).2.1 ka ka hka' hka').2` as an intermediate fact. Rewrite `this` using `[UpperTheory.V.Z.Win.tw_tw_inv]`. Then use the resulting hypothesis.

Take `⟨N, hN, hall⟩` from `flag_all he W hB H hH hfl`. Take `⟨p1, p2, p3, -⟩` from `UpperTheory.V.Base.places L Ω l B`. Take `⟨w, h⟩` from `p1 fun h0 => (p2 h0).2 hB`. Establish `hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal` using `(p3 w h).1 hB`. Establish `hw0 : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal`.

Rewrite using `[HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]`. Conclude with `hw`. Establish `hpot : PotUnl W (w.under (𝓞 ℚ))` using `fun A hA => by`. Take `⟨⟨s, hs, hs'⟩, κ, hκ, hI⟩` from `hall _ hw0 A hA`. Use `⟨κ, hκ, fun i j m hm e0 => ?_⟩` and prove the remaining obligations.

Establish `e1` using `DFunLike.congr_fun e0 ⟨s, Ine_le_Dec A hs.2⟩`. Rewrite `e1` using `[MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.mul_apply, hI i _ hs, hI j _ hs]`. Express the relevant statement in the definitionally equal form `(cycBar ℚ Ω l s ^ _) ^ m = (cycBar ℚ Ω l s ^ _ * cycBar ℚ Ω l s) ^ m at e1`. Rewrite `e1` using `[← zpow_add_one, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]`. Establish `e2` using `mul_right_cancel₀ (show (m : ℤ) ≠ 0 by omega) (zpow_ne hs' e1)`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at e2 <;> omega`. Establish `hpotL : PotUnl (W.comp (galEmb ℚ L Ω)) w` using `(((flagLaws ℚ Ω l 2 W).2.2.2 L).2.2 w hw).1 hpot`. Take `⟨HT, hwt, hloc⟩` from `hC L Ω l ι 2 one_le_two _ Q hWL b1 hQ b2`. Take `⟨⟨σ, hσ⟩, -⟩` from `locCompC P.toClassicalTheorems L 2 Q w`. Take `⟨rc, hrc⟩` from `recTExists L Ω B w h`.

Establish `hpl` using `(guard_of plainRec b1 b2 hWA (Or.inr (Or.inr hpotL)) hrc hσ).1`. Take `⟨j, L0, hj, hBw⟩` from `GlobalTheory.PlaceBridge.exists_locBridge l L Ω w B hw h`. Take `⟨Bw, hBj, -⟩` from `hBw L0 le_rfl`. Establish `hInd : Induces Bw` using `fun x => by rw [hBj]; exact hj x`. Establish `hJ` using `((hloc w σ hσ).2 hpl B h _ Bw hInd).2 (Bw.j.comp (algebraMap L Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl`.

Take `⟨-, κ, ⟨g, hg⟩, hI⟩` from `hall _ hw0 B (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw0)`. Set `ρ : ↥(Dec (F` to `L) B) →* ↥(Dec (F := ℚ) B) := ((galEmb ℚ L Ω).comp (Dec (F := L) B).subtype).codRestrict _ fun s => s.2`. Establish `hH2` using `jumpsOpen ![(e : ℤ), -(e : ℤ)] _ hWL B Bw hInd (fun i => (κ i).comp ρ) (N.comap (galEmb ℚ L Ω)) (hN.preimage (continuous_restrictScalarsHom ℚ L Ω)) ⟨g, fun s => hg (ρ s)⟩ (fun i s hs => hI i (ρ s) ⟨hs.1, hs.2⟩) _ _ hJ`. Take `⟨μ, hμ, -⟩` from `hreg v`. Establish `hμQ : Q.HasInfChar (ι.toRingHom.comp (Bw.j.comp (algebraMap L Ω))) μ` using `b3 _ μ (a3 _ μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v]))`.

Establish `hW2` using `hwt (Bw.j.comp (algebraMap L Ω))`. Rewrite `hW2` using `[hH2, CG.HasInfChar.infChar_eq (π := CG.mk Q) hμQ]`. Rewrite `hμ` using `[UpperTheory.V.Af.infOf_of_weights _ μ hW2]`. Then use the resulting hypothesis.
-/
private theorem inf_char (P : HypothesesH) (hC : CompatT) (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hW : Continuous W) (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π) (hU : WitUp ι W)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  intro v
  obtain ⟨hdet, L, _, _, _, _, _, hirr, ⟨η, σ₀, hσ₀, hησ, hηL⟩, ka, hka, hWit⟩ := hU
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  obtain ⟨K, hK, hKC⟩ := Z.Bc.exists_quad L Ω η σ₀ hσ₀ hησ hηL
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm a.is_comm.comm
  have ec : W.comp (galEmb ℚ L Ω) = (W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) := MonoidHom.ext fun _ => rfl
  have hirr' : IsIrr ((W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω)) := ec ▸ hirr
  obtain ⟨P₁, a1, a2, a3⟩ := Z.Bc.upQuadI_of P.toClassicalTheorems (Z.Bc.quadLiftRealToComplex_of_base_change P.bc) ℚ K Ω l ι hK W π hW hreg hatt
    ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr')
  obtain ⟨Q, b1, b2, b3⟩ := Z.Bc.upSolI_of P.toClassicalTheorems (Z.Bc.cyclicLiftRankTwo_of_cyclic_base_change P.cyc) K L Ω l ι _ P₁
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) a1 a2 hirr'
  rw [← ec] at b2
  have hWL : Continuous (W.comp (galEmb ℚ L Ω)) := hW.comp (continuous_restrictScalarsHom ℚ L Ω)
  have hpol : Sol.Pol ι W := by
    have halg := alg0 P ι W hW hdet 0
    rw [zpow_zero, mul_one] at halg
    obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
    rw [zpow_zero, one_mul] at hθ
    obtain ⟨c, hc⟩ := cc_ex Ω
    obtain ⟨J, hJ⟩ := pairing2 W c
    exact ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J, halg,
      fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hJ⟩
  have hQ := UpperTheory.V.Z.Win.polarized_of_att P one_le_two (UpperTheory.solvable_polarized_restriction ℚ L Ω l ι 2 W hpol) b2
  have hka' : IsAlgChar ι ka := by
    obtain ⟨h1, art, χ, a, h2, h3, h4⟩ := hka
    exact ⟨χ, h1, art, a, h2, h3, h4⟩
  have hWA : WitA ι (W.comp (galEmb ℚ L Ω)) := by
    have := (aIsoTwOf flagLaws ImaginaryQuadraticEtaCharacter.winTw P.toClassicalTheorems L Ω l ι 2 _ hWit).2 ka⁻¹ ((algOfCyc P L Ω l ι).2.1 ka ka hka' hka').2
    rwa [UpperTheory.V.Z.Win.tw_tw_inv] at this
  obtain ⟨N, hN, hall⟩ := flag_all he W hB H hH hfl
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places L Ω l B
  obtain ⟨w, h⟩ := p1 fun h0 => (p2 h0).2 hB
  have hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := (p3 w h).1 hB
  have hw0 : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]; exact hw
  have hpot : PotUnl W (w.under (𝓞 ℚ)) := fun A hA => by
    obtain ⟨⟨s, hs, hs'⟩, κ, hκ, hI⟩ := hall _ hw0 A hA
    refine ⟨κ, hκ, fun i j m hm e0 => ?_⟩
    have e1 := DFunLike.congr_fun e0 ⟨s, Ine_le_Dec A hs.2⟩
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.mul_apply, hI i _ hs, hI j _ hs] at e1
    change (cycBar ℚ Ω l s ^ _) ^ m = (cycBar ℚ Ω l s ^ _ * cycBar ℚ Ω l s) ^ m at e1
    rw [← zpow_add_one, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at e1
    have e2 := mul_right_cancel₀ (show (m : ℤ) ≠ 0 by omega) (zpow_ne hs' e1)
    fin_cases i <;> fin_cases j <;> simp at e2 <;> omega
  have hpotL : PotUnl (W.comp (galEmb ℚ L Ω)) w := (((flagLaws ℚ Ω l 2 W).2.2.2 L).2.2 w hw).1 hpot
  obtain ⟨HT, hwt, hloc⟩ := hC L Ω l ι 2 one_le_two _ Q hWL b1 hQ b2
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P.toClassicalTheorems L 2 Q w
  obtain ⟨rc, hrc⟩ := recTExists L Ω B w h
  have hpl := (guard_of plainRec b1 b2 hWA (Or.inr (Or.inr hpotL)) hrc hσ).1
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l L Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := ((hloc w σ hσ).2 hpl B h _ Bw hInd).2 (Bw.j.comp (algebraMap L Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl
  obtain ⟨-, κ, ⟨g, hg⟩, hI⟩ := hall _ hw0 B (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw0)
  let ρ : ↥(Dec (F := L) B) →* ↥(Dec (F := ℚ) B) :=
    ((galEmb ℚ L Ω).comp (Dec (F := L) B).subtype).codRestrict _ fun s => s.2
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] _ hWL B Bw hInd (fun i => (κ i).comp ρ) (N.comap (galEmb ℚ L Ω))
    (hN.preimage (continuous_restrictScalarsHom ℚ L Ω)) ⟨g, fun s => hg (ρ s)⟩ (fun i s hs => hI i (ρ s) ⟨hs.1, hs.2⟩) _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hμQ : Q.HasInfChar (ι.toRingHom.comp (Bw.j.comp (algebraMap L Ω))) μ :=
    b3 _ μ (a3 _ μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v]))
  have hW2 := hwt (Bw.j.comp (algebraMap L Ω))
  rw [hH2, CG.HasInfChar.infChar_eq (π := CG.mk Q) hμQ] at hW2
  rwa [UpperTheory.V.Af.infOf_of_weights _ μ hW2] at hμ

end UpperTheory.V.Z.Win.RR
