import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.JumpShapeAt

open Classical

/- English proof (translation)
Establish `h : ((D.nbr i w hw).LL.1.val.toRingHom.comp (Br.toLLK (D.nbr i w hw))) = D.naut.iotaQ i`. Use `IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i)) (RingHom.ext fun c => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Br.toLLK_alg]`. Conclude with `((D.loc_tie i w hw).1 c).symm`.

Conclude with `RingHom.congr_fun h z`.
-/
theorem toLLK_val (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (z : FractionRing (D.nd.O i)) :
    ((Br.toLLK (D.nbr i w hw) z : ↥(D.nbr i w hw).LL.1) : Om (D.nd.l i)) = D.naut.iotaQ i z := by
  have h : ((D.nbr i w hw).LL.1.val.toRingHom.comp (Br.toLLK (D.nbr i w hw))) = D.naut.iotaQ i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i)) (RingHom.ext fun c => ?_)
    simp only [RingHom.comp_apply]
    rw [Br.toLLK_alg]
    exact ((D.loc_tie i w hw).1 c).symm
  exact RingHom.congr_fun h z

/- English proof (translation)
Use `D.nd.lPrime i` as an intermediate fact. Establish `hsplit : ∀ y, (C.LL.1.val.comp τ) y ∈ (D.nbr i w hw).LL.1.toSubalgebra` using `fun y => (D.nbr i w hw).LL_split (C.LL.1.val.comp τ) y`. Set `τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw` to `(C.LL.1.val.comp τ).codRestrict (D.nbr i w hw).LL.1.toSubalgebra hsplit`. Establish `hτ₀ : ∀ x, τ x = C.inc (τ₀ x)` using `fun x => Subtype.ext rfl`. Establish `hE : EmbeddingTypes.EmbU C ep τ ↔ EmbeddingTypes.EmbTypeUe ep τ₀`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ₁, h1, h2⟩`. Establish `: τ₁ = τ₀` using `AlgHom.ext fun x => C.inc.injective ((h2 x).symm.trans (hτ₀ x))`. Conclude with `this ▸ h1`. Introduce `h1`.

Conclude with `⟨τ₀, h1, hτ₀⟩`. Take `⟨g', key, hU⟩` from `GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ₀`. Establish `hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g' x)) = D.host.emb g' x` using `fun x => DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g' x)`. Establish `hgg : g' = g`. Apply `(factEmb D.R D.host).1.1` to reduce the goal to its premises.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[← h.1, ← hemb x, ← D.naut.iota_LL i, ← toLLK_val D i w hw, ← key x]`. Both sides reduce to the same expression. Substitute `hgg` using the available equality. Rewrite using `[hE]`.

Consider the cases of `ep`. Rewrite using `[GlobalTheory.SplitDecl.embTypeUe_iff]`. Simplify using `only [AdmissibleParameterJ.TypeU, Bool.false_eq_true, iff_false]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, φ, hφ, h3⟩`.

Establish `hφe : φ = D.host.emb g'` using `RingHom.ext fun x => by`. Rewrite using `[← h3 x _ (key x).symm, hemb]`. Establish `h4 : D.host.emb (g' * D.R.cc) ∈ D.host.cmType`. Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp, ← hφe]`. Conclude with `hφ`.

Establish `h5` using `((factEmb D.R D.host).2 _).1 h4`. Conclude with `fun hg => (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g').1 hg h5`. Introduce `hg`. Establish `h5 : g' * D.R.cc ∈ D.R.Psi`. Assume the negation of the conclusion as `hc`.

Conclude with `hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g').2 hc)`. Establish `h4` using `((factEmb D.R D.host).2 _).2 h5`. Rewrite `h4` using `[Formalism.L2.Geo.emb_mul_cc_comp]`. Use `⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g', h4, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : y = D.embE (D.host.sigmaOf g' x)` using `(D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))`.

Rewrite using `[hy', hemb]`. Simplify using `only [EmbeddingTypes.EmbTypeUe, if_true, AdmissibleParameterJ.TypeU, iff_true]`. Conclude with `hU`.
-/
theorem embU_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (ep : Bool) (g : D.R.GG)
    (ρ : D.what₂.Tau) (h : AdmissibleParameterJ.ReadAt D i (AdmissibleParameterJ.gEmb C τ) g ρ) :
    EmbeddingTypes.EmbU C ep τ ↔ AdmissibleParameterJ.TypeU D ep g := by
  have := D.nd.lPrime i

  have hsplit : ∀ y, (C.LL.1.val.comp τ) y ∈ (D.nbr i w hw).LL.1.toSubalgebra := fun y =>
    (D.nbr i w hw).LL_split (C.LL.1.val.comp τ) y
  let τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw :=
    (C.LL.1.val.comp τ).codRestrict (D.nbr i w hw).LL.1.toSubalgebra hsplit
  have hτ₀ : ∀ x, τ x = C.inc (τ₀ x) := fun x => Subtype.ext rfl
  have hE : EmbeddingTypes.EmbU C ep τ ↔ EmbeddingTypes.EmbTypeUe ep τ₀ := by
    constructor
    · rintro ⟨τ₁, h1, h2⟩
      have : τ₁ = τ₀ := AlgHom.ext fun x => C.inc.injective ((h2 x).symm.trans (hτ₀ x))
      exact this ▸ h1
    · intro h1
      exact ⟨τ₀, h1, hτ₀⟩
  obtain ⟨g', key, hU⟩ := GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ₀
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g' x)) = D.host.emb g' x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g' x)
  have hgg : g' = g := by
    apply (factEmb D.R D.host).1.1
    refine RingHom.ext fun x => ?_
    rw [← h.1, ← hemb x, ← D.naut.iota_LL i, ← toLLK_val D i w hw, ← key x]
    rfl
  subst hgg
  rw [hE]
  cases ep
  · rw [GlobalTheory.SplitDecl.embTypeUe_iff]
    simp only [AdmissibleParameterJ.TypeU, Bool.false_eq_true, iff_false]
    constructor
    · rintro ⟨-, φ, hφ, h3⟩
      have hφe : φ = D.host.emb g' := RingHom.ext fun x => by
        rw [← h3 x _ (key x).symm, hemb]
      have h4 : D.host.emb (g' * D.R.cc) ∈ D.host.cmType := by
        rw [Formalism.L2.Geo.emb_mul_cc_comp, ← hφe]; exact hφ
      have h5 := ((factEmb D.R D.host).2 _).1 h4
      exact fun hg => (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g').1 hg h5
    · intro hg
      have h5 : g' * D.R.cc ∈ D.R.Psi := by
        by_contra hc
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g').2 hc)
      have h4 := ((factEmb D.R D.host).2 _).2 h5
      rw [Formalism.L2.Geo.emb_mul_cc_comp] at h4
      refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g', h4, fun x y hy => ?_⟩
      have hy' : y = D.embE (D.host.sigmaOf g' x) :=
        (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
      rw [hy', hemb]
  · simp only [EmbeddingTypes.EmbTypeUe, if_true, AdmissibleParameterJ.TypeU, iff_true]
    exact hU

/- English proof (translation)
Take `⟨ep', hd⟩` from `hd`. Take `⟨sg, cτ, hs1, hs2, hmap, -⟩` from `hd i τ₀ g ρ h`. Establish `hsg : sg * sg = 1`. Distinguish the cases in `hT : AdmissibleParameterJ.TypeU D ep' g`. Rewrite using `[hs1 hT]`.

Evaluate the numerical expressions. Rewrite using `[hs2 hT]`. Evaluate the numerical expressions. Introduce `p hp`. Establish `hm : sg * p + cτ ∈ (D.naut.locAutHodgeTateWeightsLevelZero i τ₀).map (fun n : ℤ => (n : ℚ))`.

Rewrite using `[hmap]`. Conclude with `Multiset.mem_map_of_mem _ hp`. Take `⟨n, -, hn⟩` from `Multiset.mem_map.1 hm`. Use `⟨sg.num * (n - cτ), ?_⟩` and prove the remaining obligations. Establish `hden : sg = (sg.num : ℚ)`.

Distinguish the cases in `hT : AdmissibleParameterJ.TypeU D ep' g`. Rewrite using `[hs1 hT]`. Both sides reduce to the same expression. Rewrite using `[hs2 hT]`. Both sides reduce to the same expression.

Use `push_cast`. Rewrite using `[← hden, hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ppm_int (D : D7) (hd : AdmissibleParameterJ.AdmDict D) (i : D.nd.Loc)
    (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG) (ρ : D.what₂.Tau)
    (h : AdmissibleParameterJ.ReadAt D i τ₀ g ρ) : ∀ p ∈ AdmissibleParameterJ.PPm D (D.nd.j i) ρ, ∃ n : ℤ, p = n := by
  obtain ⟨ep', hd⟩ := hd
  obtain ⟨sg, cτ, hs1, hs2, hmap, -⟩ := hd i τ₀ g ρ h
  have hsg : sg * sg = 1 := by
    by_cases hT : AdmissibleParameterJ.TypeU D ep' g
    · rw [hs1 hT]; norm_num
    · rw [hs2 hT]; norm_num
  intro p hp
  have hm : sg * p + cτ ∈ (D.naut.locAutHodgeTateWeightsLevelZero i τ₀).map (fun n : ℤ => (n : ℚ)) := by
    rw [hmap]; exact Multiset.mem_map_of_mem _ hp
  obtain ⟨n, -, hn⟩ := Multiset.mem_map.1 hm
  refine ⟨sg.num * (n - cτ), ?_⟩
  have hden : sg = (sg.num : ℚ) := by
    by_cases hT : AdmissibleParameterJ.TypeU D ep' g
    · rw [hs1 hT]; rfl
    · rw [hs2 hT]; rfl
  push_cast
  rw [← hden, hn]
  calc p = (sg * sg) * p := by rw [hsg, one_mul]
    _ = sg * (sg * p + cτ - cτ) := by ring

/- English proof (translation)
Establish `hj` using `D.nd.j_range i`. Establish `hF` using `GlobalTheory.JumpSets.jFacts_of hP _ hj.1 hj.2 ρ`. Establish `hI` using `ppm_int D hd i τ₀ g ρ h`. Establish `hsh : ∃ m : ℤ, AdmissibleParameterJ.sz D (D.nd.j i) ρ + AdmissibleParameterJ.c0 D = m`. Establish `hmem : -AdmissibleParameterJ.sz D (D.nd.j i) ρ + ((D.R.t : ℚ) + 1) / 2 - (((0 : ℕ) : ℚ) + 1) ∈ AdmissibleParameterJ.PPm D (D.nd.j i) ρ`.

Unfold `AdmissibleParameterJ.PPm`. Use `Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨0, ?_, rfl⟩))` and prove the remaining obligations. Simplify using `only [Finset.mem_val, Finset.mem_range]`. Conclude with `hF.t_pos`. Take `⟨m, hm⟩` from `hI _ hmem`.

Use `⟨-m + (D.R.t : ℤ) - 1, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hm]`. Simplify using `only [AdmissibleParameterJ.c0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hJp : ∀ q ∈ AdmissibleParameterJ.Jp D (D.nd.j i) ρ, ∃ n : ℤ, q = n`. Introduce `q hq`. Take `⟨n, hn⟩` from `hI _ ((GlobalTheory.JumpSets.jp_mem_iff hF q).2 hq)`. Take `⟨m, hm⟩` from `hsh`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[← hn, ← hm]`. Expand and normalize the polynomial expressions, which then agree. Introduce `q hq`. Consider the cases of `up`.

Establish `hq' : AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.Jp D (D.nd.j i) ρ` using `hq`. Take `⟨n, hn⟩` from `hJp _ hq'`. Use `⟨(D.R.t : ℤ) - 1 - n, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hn]`.

Simplify using `only [AdmissibleParameterJ.refl]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hJp q hq`.
-/
theorem jj_int (D : D7) (L : SizeData₂ D) (hP : AdmissibleParameterJ.AdmPar L) (hd : AdmissibleParameterJ.AdmDict D) (i : D.nd.Loc)
    (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG) (ρ : D.what₂.Tau)
    (h : AdmissibleParameterJ.ReadAt D i τ₀ g ρ) (up : Bool) :
    ∀ q ∈ AdmissibleParameterJ.JJ D up (D.nd.j i) ρ, ∃ n : ℤ, q = n := by
  have hj := D.nd.j_range i
  have hF := GlobalTheory.JumpSets.jFacts_of hP _ hj.1 hj.2 ρ
  have hI := ppm_int D hd i τ₀ g ρ h

  have hsh : ∃ m : ℤ, AdmissibleParameterJ.sz D (D.nd.j i) ρ + AdmissibleParameterJ.c0 D = m := by
    have hmem : -AdmissibleParameterJ.sz D (D.nd.j i) ρ + ((D.R.t : ℚ) + 1) / 2 - (((0 : ℕ) : ℚ) + 1) ∈ AdmissibleParameterJ.PPm D (D.nd.j i) ρ := by
      unfold AdmissibleParameterJ.PPm
      refine Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨0, ?_, rfl⟩))
      simp only [Finset.mem_val, Finset.mem_range]
      exact hF.t_pos
    obtain ⟨m, hm⟩ := hI _ hmem
    refine ⟨-m + (D.R.t : ℤ) - 1, ?_⟩
    push_cast
    rw [← hm]
    simp only [AdmissibleParameterJ.c0]
    ring
  have hJp : ∀ q ∈ AdmissibleParameterJ.Jp D (D.nd.j i) ρ, ∃ n : ℤ, q = n := by
    intro q hq
    obtain ⟨n, hn⟩ := hI _ ((GlobalTheory.JumpSets.jp_mem_iff hF q).2 hq)
    obtain ⟨m, hm⟩ := hsh
    refine ⟨n + m, ?_⟩
    push_cast
    rw [← hn, ← hm]
    ring
  intro q hq
  cases up
  · have hq' : AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.Jp D (D.nd.j i) ρ := hq
    obtain ⟨n, hn⟩ := hJp _ hq'
    refine ⟨(D.R.t : ℤ) - 1 - n, ?_⟩
    push_cast
    rw [← hn]
    simp only [AdmissibleParameterJ.refl]
    ring
  · exact hJp q hq

/- English proof (translation)
Rewrite using `[Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, rfl⟩`. Rewrite `hq` using `[Set.Finite.mem_toFinset]`. Take `⟨n, rfl⟩` from `hint q hq`.

Rewrite using `[Int.floor_intCast]`. Conclude with `hq`. Introduce `ha`. Conclude with `⟨a, (Set.Finite.mem_toFinset hS).2 ha, Int.floor_intCast a⟩`.
-/
theorem mem_floorImg (S : Set ℚ) (hS : S.Finite) (hint : ∀ q ∈ S, ∃ n : ℤ, q = n) (a : ℤ) :
    a ∈ hS.toFinset.image (fun q : ℚ => ⌊q⌋) ↔ (a : ℚ) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨n, rfl⟩ := hint q hq
    rw [Int.floor_intCast]; exact hq
  · intro ha
    exact ⟨a, (Set.Finite.mem_toFinset hS).2 ha, Int.floor_intCast a⟩

/- English proof (translation)
Rewrite using `[Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card S hS]`. Introduce `q hq q' hq' he`. Rewrite `hq`, `hq'` using `[Finset.mem_coe, Set.Finite.mem_toFinset]`. Take `⟨n, rfl⟩` from `hint q hq`. Take `⟨n', rfl⟩` from `hint q' hq'`.

Simplify using `only [Int.floor_intCast] at he`. Rewrite using `[he]`.
-/
theorem card_floorImg (S : Set ℚ) (hS : S.Finite) (hint : ∀ q ∈ S, ∃ n : ℤ, q = n) :
    (hS.toFinset.image (fun q : ℚ => ⌊q⌋)).card = S.ncard := by
  rw [Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card S hS]
  intro q hq q' hq' he
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hq hq'
  obtain ⟨n, rfl⟩ := hint q hq
  obtain ⟨n', rfl⟩ := hint q' hq'
  simp only [Int.floor_intCast] at he
  rw [he]

/- English proof (translation)
The claim follows from `Set.ncard_preimage_of_injective_subset_range GlobalTheory.HostJumpSets.refl_injective (fun q _ => GlobalTheory.HostJumpSets.refl_surjective q)`.
-/
theorem reflS_ncard (D : D7) (S : Set ℚ) : (AdmissibleParameterJ.reflS D S).ncard = S.ncard :=
  Set.ncard_preimage_of_injective_subset_range GlobalTheory.HostJumpSets.refl_injective
    (fun q _ => GlobalTheory.HostJumpSets.refl_surjective q)

/- English proof (translation)
Take `⟨a, ha⟩` from `h1`. Take `⟨b, hb⟩` from `h2`. Establish `h3` using `hF.v_nonneg a`. Establish `h4` using `GlobalTheory.JumpSets.jp_b_pos hF b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_not_low {D : D7} {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : GlobalTheory.JumpSets.JFacts L j ρ)
    (q : ℚ) (h1 : q ∈ AdmissibleParameterJ.cloudJ D j ρ) (h2 : q ∈ AdmissibleParameterJ.lowJ D j ρ) : False := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have h3 := hF.v_nonneg a
  have h4 := GlobalTheory.JumpSets.jp_b_pos hF b
  linarith

/- English proof (translation)
Establish `hF` using `GlobalTheory.JumpSets.jFacts_of hP j hj1 hjm ρ`. Establish `hfin` using `GlobalTheory.HostJumpSets.JJ_finite (D := D) up j ρ`. Establish `hcl : AdmissibleParameterJ.cloudT D up j ρ ⊆ AdmissibleParameterJ.JJ D up j ρ`. Introduce `q hq`. Consider the cases of `up`.

Conclude with `Or.inl (Or.inl hq)`. Conclude with `Or.inl (Or.inl hq)`. Establish `hlo : AdmissibleParameterJ.lowT D up j ρ ⊆ AdmissibleParameterJ.JJ D up j ρ`. Introduce `q hq`. Consider the cases of `up`.

Conclude with `Or.inl (Or.inr hq)`. Conclude with `Or.inl (Or.inr hq)`. Establish `hfC` using `hfin.subset hcl`. Establish `hfL` using `hfin.subset hlo`. Establish `hiC : ∀ q ∈ AdmissibleParameterJ.cloudT D up j ρ, ∃ n : ℤ, q = n` using `fun q hq => hint q (hcl hq)`.

Establish `hiL : ∀ q ∈ AdmissibleParameterJ.lowT D up j ρ, ∃ n : ℤ, q = n` using `fun q hq => hint q (hlo hq)`. Use `set Cl := hfC.toFinset.image (fun q : ℚ => ⌊q⌋) with hCl`. Use `set Lo := hfL.toFinset.image (fun q : ℚ => ⌊q⌋) with hLo`. Establish `mC : ∀ a, a ∈ Cl ↔ (a : ℚ) ∈ AdmissibleParameterJ.cloudT D up j ρ` using `mem_floorImg _ hfC hiC`. Establish `mL : ∀ a, a ∈ Lo ↔ (a : ℚ) ∈ AdmissibleParameterJ.lowT D up j ρ` using `mem_floorImg _ hfL hiL`.

Establish `hJW : ∀ a : ℤ, (a ∈ Cl ∨ a ∈ Lo) ↔ (a : ℚ) ∈ AdmissibleParameterJ.JW D up j ρ`. Introduce `a`. Rewrite using `[mC, mL]`. Both sides reduce to the same expression. Take `⟨-, -, -, hncC, hncL, -⟩` from `hb j hj1 hjm ρ`.

Establish `ht0 : (0 : ℚ) ≤ D.R.t` using `Nat.cast_nonneg _`. Use `⟨Cl, Lo, ⟨⟨1, ∑ a ∈ Cl, |(a : ℚ)| + 1, ∑ a ∈ Lo, |(a : ℚ)| + 1, one_pos, by positivity, by positivity, fun a ha => ⟨?_, ?_⟩, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `(mC a).1 ha`. Consider the cases of `up`. Establish `h2` using `(hc j hj1 hjm ρ).2.2.1 _ h`.

Simplify using `only [AdmissibleParameterJ.refl] at h2`. Establish `h3 : a < -2`. Establish `: (a : ℚ) < -2` using `by linarith`. Conclude with `this` after adjusting the coercions. Simplify using `only [Bool.false_eq_true, ↓reduceIte]`.

Use `push_cast`. Establish `: (a : ℚ) ≤ -3` using `by exact_mod_cast (show a ≤ -3 by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `(hc j hj1 hjm ρ).2.2.1 _ h`. Establish `h3 : (1 : ℚ) < a` using `by linarith`.

Simplify using `only [↓reduceIte]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((((if up then 1 else -1) * a : ℤ)) : ℚ) ≤ |(a : ℚ)|`. Consider the cases of `up`.

Simplify using `only [Bool.false_eq_true, ↓reduceIte]`. Use `push_cast`. Combine the linear relations using `[neg_abs_le (a : ℚ)]`. Simplify using `only [↓reduceIte]`. Use `push_cast`.

Combine the linear relations using `[le_abs_self (a : ℚ)]`. Establish `h2 : |(a : ℚ)| ≤ ∑ a ∈ Cl, |(a : ℚ)|` using `Finset.single_le_sum (f := fun a : ℤ => |(a : ℚ)|) (fun _ _ => abs_nonneg _) ha`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : |(a : ℚ)| ≤ ∑ a ∈ Lo, |(a : ℚ)|` using `Finset.single_le_sum (f := fun a : ℤ => |(a : ℚ)|) (fun _ _ => abs_nonneg _) ha`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hCl, card_floorImg _ hfC hiC]`. Consider the cases of `up`. Conclude with `(reflS_ncard D _).trans hncC`. Conclude with `hncC`. Rewrite using `[hLo, card_floorImg _ hfL hiL]`.

Consider the cases of `up`. Conclude with `(reflS_ncard D _).trans hncL`. Conclude with `hncL`. Rewrite using `[Finset.disjoint_left]`. Introduce `a ha1 ha2`.

Establish `h1` using `(mC a).1 ha1`. Establish `h2` using `(mL a).1 ha2`. Consider the cases of `up`. Conclude with `cloud_not_low hF _ h1 h2`. Conclude with `cloud_not_low hF _ h1 h2`.

Rewrite using `[Finset.disjoint_left]`. Introduce `a ha1 ha2`. Rewrite `ha2` using `[Finset.mem_Ico]`. Conclude with `GlobalTheory.JumpSets.block_not_mem_JW hF up _ ((GlobalTheory.JumpSets.block_mem_iff a).2 ha2) ((hJW a).1 (Or.inl ha1))`. Rewrite using `[Finset.disjoint_left]`.

Introduce `a ha1 ha2`. Rewrite `ha2` using `[Finset.mem_Ico]`. Conclude with `GlobalTheory.JumpSets.block_not_mem_JW hF up _ ((GlobalTheory.JumpSets.block_mem_iff a).2 ha2) ((hJW a).1 (Or.inr ha1))`. Introduce `h`. Establish `hJ : (((-1 : ℤ)) : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ`.

Break down `Finset.mem_union.1 h with h | h` into its components or cases. Conclude with `hcl ((mC _).1 h)`. Conclude with `hlo ((mL _).1 h)`. Move the coercions through the operations in `at hJ`. Conclude with `((hc j hj1 hjm ρ).2.1 up).1 hJ`.

Introduce `h`. Establish `hJ : (((D.R.t : ℤ)) : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ`. Break down `Finset.mem_union.1 h with h | h` into its components or cases. Conclude with `hcl ((mC _).1 h)`. Conclude with `hlo ((mL _).1 h)`.

Move the coercions through the operations in `at hJ`. Conclude with `((hc j hj1 hjm ρ).2.1 up).2 hJ`. Establish `hiff : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ ↔ a ∈ Cl ∪ Lo ∪ Finset.Ico 0 (D.R.t : ℤ)`. Rewrite using `[Finset.mem_union, Finset.mem_union, Finset.mem_Ico]`. Distinguish the cases in `hbk : (a : ℚ) ∈ AdmissibleParameterJ.blockJ D`.

Use `(GlobalTheory.JumpSets.block_mem_iff a).1 hbk` as an intermediate fact. Conclude with `⟨fun _ => Or.inr this, fun _ => GlobalTheory.JumpSets.block_sub_JJ up j ρ _ hbk⟩`. Rewrite using `[GlobalTheory.JumpSets.JJ_iff_JW hF up _ hbk, ← hJW]`. Establish `: ¬ (0 ≤ a ∧ a < (D.R.t : ℤ))` using `fun h => hbk ((GlobalTheory.JumpSets.block_mem_iff a).2 h)`. The claim follows by propositional logic.

Use `show (if (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ then (1 : ℤ) else 0) = _`. Distinguish the cases in `h : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ`. Rewrite using `[if_pos h, if_pos (hiff.1 h)]`. Rewrite using `[if_neg h, if_neg (mt hiff.2 h)]`.
-/
theorem shape (D : D7) (L : SizeData₂ D) (hP : AdmissibleParameterJ.AdmPar L) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hc : AdmissibleParameterJ.jcCondition L)
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) (ρ : D.what₂.Tau) (up : Bool)
    (hint : ∀ q ∈ AdmissibleParameterJ.JJ D up j ρ, ∃ n : ℤ, q = n) :
    ∃ Cl Lo : Finset ℤ, EmbeddingTypes.ShapeJumps D.R.k D.R.m D.R.t (if up then 1 else -1) Cl Lo
      (fun a => if (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ then 1 else 0) := by
  have hF := GlobalTheory.JumpSets.jFacts_of hP j hj1 hjm ρ
  have hfin := GlobalTheory.HostJumpSets.JJ_finite (D := D) up j ρ
  have hcl : AdmissibleParameterJ.cloudT D up j ρ ⊆ AdmissibleParameterJ.JJ D up j ρ := by
    intro q hq
    cases up
    · exact Or.inl (Or.inl hq)
    · exact Or.inl (Or.inl hq)
  have hlo : AdmissibleParameterJ.lowT D up j ρ ⊆ AdmissibleParameterJ.JJ D up j ρ := by
    intro q hq
    cases up
    · exact Or.inl (Or.inr hq)
    · exact Or.inl (Or.inr hq)
  have hfC := hfin.subset hcl
  have hfL := hfin.subset hlo
  have hiC : ∀ q ∈ AdmissibleParameterJ.cloudT D up j ρ, ∃ n : ℤ, q = n := fun q hq => hint q (hcl hq)
  have hiL : ∀ q ∈ AdmissibleParameterJ.lowT D up j ρ, ∃ n : ℤ, q = n := fun q hq => hint q (hlo hq)
  set Cl := hfC.toFinset.image (fun q : ℚ => ⌊q⌋) with hCl
  set Lo := hfL.toFinset.image (fun q : ℚ => ⌊q⌋) with hLo
  have mC : ∀ a, a ∈ Cl ↔ (a : ℚ) ∈ AdmissibleParameterJ.cloudT D up j ρ := mem_floorImg _ hfC hiC
  have mL : ∀ a, a ∈ Lo ↔ (a : ℚ) ∈ AdmissibleParameterJ.lowT D up j ρ := mem_floorImg _ hfL hiL
  have hJW : ∀ a : ℤ, (a ∈ Cl ∨ a ∈ Lo) ↔ (a : ℚ) ∈ AdmissibleParameterJ.JW D up j ρ := by
    intro a
    rw [mC, mL]; rfl
  obtain ⟨-, -, -, hncC, hncL, -⟩ := hb j hj1 hjm ρ
  have ht0 : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Cl, Lo, ⟨⟨1, ∑ a ∈ Cl, |(a : ℚ)| + 1, ∑ a ∈ Lo, |(a : ℚ)| + 1, one_pos, by positivity,
    by positivity, fun a ha => ⟨?_, ?_⟩, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩⟩
  ·
    have h := (mC a).1 ha
    cases up
    · have h2 := (hc j hj1 hjm ρ).2.2.1 _ h
      simp only [AdmissibleParameterJ.refl] at h2
      have h3 : a < -2 := by
        have : (a : ℚ) < -2 := by linarith
        exact_mod_cast this
      simp only [Bool.false_eq_true, ↓reduceIte]
      push_cast
      have : (a : ℚ) ≤ -3 := by exact_mod_cast (show a ≤ -3 by omega)
      linarith
    · have h2 := (hc j hj1 hjm ρ).2.2.1 _ h
      have h3 : (1 : ℚ) < a := by linarith
      simp only [↓reduceIte]
      push_cast
      linarith
  · have h1 : ((((if up then 1 else -1) * a : ℤ)) : ℚ) ≤ |(a : ℚ)| := by
      cases up
      · simp only [Bool.false_eq_true, ↓reduceIte]; push_cast; linarith [neg_abs_le (a : ℚ)]
      · simp only [↓reduceIte]; push_cast; linarith [le_abs_self (a : ℚ)]
    have h2 : |(a : ℚ)| ≤ ∑ a ∈ Cl, |(a : ℚ)| :=
      Finset.single_le_sum (f := fun a : ℤ => |(a : ℚ)|) (fun _ _ => abs_nonneg _) ha
    linarith
  · have h2 : |(a : ℚ)| ≤ ∑ a ∈ Lo, |(a : ℚ)| :=
      Finset.single_le_sum (f := fun a : ℤ => |(a : ℚ)|) (fun _ _ => abs_nonneg _) ha
    linarith
  · rw [hCl, card_floorImg _ hfC hiC]
    cases up
    · exact (reflS_ncard D _).trans hncC
    · exact hncC
  · rw [hLo, card_floorImg _ hfL hiL]
    cases up
    · exact (reflS_ncard D _).trans hncL
    · exact hncL
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    have h1 := (mC a).1 ha1
    have h2 := (mL a).1 ha2
    cases up
    · exact cloud_not_low hF _ h1 h2
    · exact cloud_not_low hF _ h1 h2
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_Ico] at ha2
    exact GlobalTheory.JumpSets.block_not_mem_JW hF up _ ((GlobalTheory.JumpSets.block_mem_iff a).2 ha2)
      ((hJW a).1 (Or.inl ha1))
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_Ico] at ha2
    exact GlobalTheory.JumpSets.block_not_mem_JW hF up _ ((GlobalTheory.JumpSets.block_mem_iff a).2 ha2)
      ((hJW a).1 (Or.inr ha1))
  · intro h
    have hJ : (((-1 : ℤ)) : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ := by
      rcases Finset.mem_union.1 h with h | h
      · exact hcl ((mC _).1 h)
      · exact hlo ((mL _).1 h)
    push_cast at hJ
    exact ((hc j hj1 hjm ρ).2.1 up).1 hJ
  · intro h
    have hJ : (((D.R.t : ℤ)) : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ := by
      rcases Finset.mem_union.1 h with h | h
      · exact hcl ((mC _).1 h)
      · exact hlo ((mL _).1 h)
    push_cast at hJ
    exact ((hc j hj1 hjm ρ).2.1 up).2 hJ
  · have hiff : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ ↔ a ∈ Cl ∪ Lo ∪ Finset.Ico 0 (D.R.t : ℤ) := by
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_Ico]
      by_cases hbk : (a : ℚ) ∈ AdmissibleParameterJ.blockJ D
      · have := (GlobalTheory.JumpSets.block_mem_iff a).1 hbk
        exact ⟨fun _ => Or.inr this, fun _ => GlobalTheory.JumpSets.block_sub_JJ up j ρ _ hbk⟩
      · rw [GlobalTheory.JumpSets.JJ_iff_JW hF up _ hbk, ← hJW]
        have : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hbk ((GlobalTheory.JumpSets.block_mem_iff a).2 h)
        tauto
    show (if (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ then (1 : ℤ) else 0) = _
    by_cases h : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ
    · rw [if_pos h, if_pos (hiff.1 h)]
    · rw [if_neg h, if_neg (mt hiff.2 h)]

/- English proof (translation)
Introduce `hPr D L P nch HW F Cm X C₂ S ep hJ i h0 h1 w hw C`. Establish `hR : GoodR D.nd i (X.r i)` using `S.canon.fam.good i`. Establish `hA` using `S.facts.toCore.admA`. Establish `hg : D.nd.l i ∉ TwistedPlaces.gset D`. Simplify using `only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]`.

Conclude with `⟨h0, h1⟩`. Establish `hChi` using `GlobalTheory.ChiOneNoPt.main hPr.font D hA.1 hA.2.2.2.1 hA.2.2.2.2.2.2 S.facts.block S.facts.muUnr i hg`. Establish `hG2` using `S.facts.g2.1 i (X.r i) hR`. Establish `hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i (X.r i) x)))` using `fun x => GlobalTheory.DualTwistCrys.crys_coef D i (X.r i) w hw C x (GlobalTheory.DualTwistCrys.crys_bridge D i (X.r i) hR hG2 h0 h1 w hw x)`. Use `⟨hcr, fun x => GlobalTheory.DualTwistCrys.tw_crys D i (X.r i) w hw C x (GlobalTheory.DualTwistCrys.crys_chi D i hChi w hw C) (hcr x), fun τ => ?_⟩` and prove the remaining obligations.

Take `⟨g, ρ, hRd, hx, -⟩` from `hJ i (X.r i) hR w hw C τ`. Establish `hAJ` using `S.facts.admJ L S.par`. Establish `hJall : AdmissibleParameterJ.JumpConditions L` using `GlobalTheory.JumpStatement.holds_all D L hAJ`. Establish `hj` using `D.nd.j_range i`. Establish `hint` using `jj_int D L S.par hAJ.2.2.2.1 i _ g ρ hRd (decide (AdmissibleParameterJ.TypeU D ep g))`.

Take `⟨Cl, Lo, hS⟩` from `shape D L S.par hJall.2.1 hJall.2.2.1 _ hj.1 hj.2 ρ _ hint`. Use `⟨Cl, Lo, fun x => ?_⟩` and prove the remaining obligations. Establish `hsg : (if EmbeddingTypes.EmbU C ep τ then (1 : ℤ) else -1) = (if decide (AdmissibleParameterJ.TypeU D ep g) then 1 else -1)`. Distinguish the cases in `hT : AdmissibleParameterJ.TypeU D ep g`. Rewrite using `[if_pos ((embU_iff D i w hw C τ ep g ρ hRd).2 hT), decide_eq_true hT]`.

Both sides reduce to the same expression. Rewrite using `[if_neg (mt (embU_iff D i w hw C τ ep g ρ hRd).1 hT), decide_eq_false hT]`. Both sides reduce to the same expression. Rewrite using `[hsg]`. Use `hS using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `a`. Rewrite using `[(hx x a).2.1]`.
-/
theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  intro hPr D L P nch HW F Cm X C₂ S ep hJ i h0 h1 w hw C
  have hR : GoodR D.nd i (X.r i) := S.canon.fam.good i
  have hA := S.facts.toCore.admA
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h0, h1⟩
  have hChi := GlobalTheory.ChiOneNoPt.main hPr.font D hA.1 hA.2.2.2.1 hA.2.2.2.2.2.2 S.facts.block S.facts.muUnr i hg
  have hG2 := S.facts.g2.1 i (X.r i) hR
  have hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i (X.r i) x))) :=
    fun x => GlobalTheory.DualTwistCrys.crys_coef D i (X.r i) w hw C x
      (GlobalTheory.DualTwistCrys.crys_bridge D i (X.r i) hR hG2 h0 h1 w hw x)
  refine ⟨hcr, fun x => GlobalTheory.DualTwistCrys.tw_crys D i (X.r i) w hw C x
    (GlobalTheory.DualTwistCrys.crys_chi D i hChi w hw C) (hcr x), fun τ => ?_⟩
  obtain ⟨g, ρ, hRd, hx, -⟩ := hJ i (X.r i) hR w hw C τ
  have hAJ := S.facts.admJ L S.par
  have hJall : AdmissibleParameterJ.JumpConditions L := GlobalTheory.JumpStatement.holds_all D L hAJ
  have hj := D.nd.j_range i
  have hint := jj_int D L S.par hAJ.2.2.2.1 i _ g ρ hRd (decide (AdmissibleParameterJ.TypeU D ep g))
  obtain ⟨Cl, Lo, hS⟩ := shape D L S.par hJall.2.1 hJall.2.2.1 _ hj.1 hj.2 ρ _ hint
  refine ⟨Cl, Lo, fun x => ?_⟩
  have hsg : (if EmbeddingTypes.EmbU C ep τ then (1 : ℤ) else -1) = (if decide (AdmissibleParameterJ.TypeU D ep g) then 1 else -1) := by
    by_cases hT : AdmissibleParameterJ.TypeU D ep g
    · rw [if_pos ((embU_iff D i w hw C τ ep g ρ hRd).2 hT), decide_eq_true hT]; rfl
    · rw [if_neg (mt (embU_iff D i w hw C τ ep g ρ hRd).1 hT), decide_eq_false hT]; rfl
  rw [hsg]
  convert hS using 1
  funext a
  rw [(hx x a).2.1]

end GlobalTheory.JumpShapeAt
