import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

namespace ModelTwistGenerated

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K] {ι : K → Type}

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule] at ha hb ⊢`. Introduce `c hc`. Establish `: a * b * ∏ k, y ⟨k, c k⟩ ^ (-(β + γ) k) = (a * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (b * ∏ k, y ⟨k, c k⟩ ^ (-γ k))`. Rewrite using `[mul_mul_mul_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, neg_add, zpow_add₀ (hc k)]`. Rewrite using `[this]`. Conclude with `Subalgebra.mul_mem _ (ha c hc) (hb c hc)`.
-/
theorem secOver_mul (y : (Σ k, ι k) → Ω) {β γ : K → ℤ} {a b : Ω} (ha : a ∈ secOver S y β)
    (hb : b ∈ secOver S y γ) : a * b ∈ secOver S y (β + γ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule] at ha hb ⊢
  intro c hc
  have : a * b * ∏ k, y ⟨k, c k⟩ ^ (-(β + γ) k) =
      (a * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (b * ∏ k, y ⟨k, c k⟩ ^ (-γ k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
  rw [this]
  exact Subalgebra.mul_mem _ (ha c hc) (hb c hc)

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]`. Introduce `c _`. Simplify using `only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]`. Conclude with `Subalgebra.one_mem _`.
-/
theorem one_mem_secOver (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ secOver S y 0 := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using one_mem_secOver (S := S) y`. Consider the case `succ m ih`. Establish `h` using `secOver_mul y ih ha`. Rewrite using `[pow_succ]`.

Use `h using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[add_smul, one_smul]`.
-/
theorem pow_mem_secOver (y : (Σ k, ι k) → Ω) {δ : K → ℤ} {a : Ω} (ha : a ∈ secOver S y δ) (m : ℕ) :
    a ^ m ∈ secOver S y ((m : ℤ) • δ) := by
  induction m with
  | zero => simpa using one_mem_secOver (S := S) y
  | succ m ih =>
    have h := secOver_mul y ih ha
    rw [pow_succ]
    convert h using 2
    push_cast
    rw [add_smul, one_smul]

variable [DecidableEq K]

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]`. Introduce `c _`. Rewrite using `[Fintype.prod_eq_single k₀ fun k hk => by rw [Pi.single_eq_of_ne hk]; simp]`. Rewrite using `[Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]`. Conclude with `Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩`.
-/
theorem coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) (i : ι k₀) :
    y ⟨k₀, i⟩ ∈ secOver S y (IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  intro c _
  rw [Fintype.prod_eq_single k₀ fun k hk => by rw [Pi.single_eq_of_ne hk]; simp]
  rw [Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using one_mem_secOver (S := S) y`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.card_insert_of_notMem hj]`. Establish `h` using `secOver_mul y (coord_mem_secOver (S := S) y k₀ (e.symm j)) ih`.

Apply the tactic sequence `convert h using 2 <;> first | rfl | (push_cast; rw [add_smul, one_smul, add_comm])`.
-/
theorem prod_coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (s : Finset (Fin (N + 1))) :
    ∏ j ∈ s, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) j ∈
      secOver S y ((s.card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_secOver (S := S) y
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have h := secOver_mul y (coord_mem_secOver (S := S) y k₀ (e.symm j)) ih
    convert h using 2 <;> first | rfl | (push_cast; rw [add_smul, one_smul, add_comm])

variable {N : ℕ} {y : (Σ k, ι k) → Ω} {k₀ : K} (e : ι k₀ ≃ Fin (N + 1))

local notation "X" => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm

/- English proof (translation)
Establish `hsubQ : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I`. Use `Set.ext fun t => ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_sub_iff_gam]`. Use `exists_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[Kleiman.SubSystem.gam, hQ]`.

Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : X i ≠ 0` using `(Kleiman.mem_support _).mp (I.2.2 hi)`. Establish `hcard` using `Finset.card_erase_add_one hi`. Establish `hxI : Kleiman.xProd I = X i * ∏ j ∈ I.1.erase i, X j` using `(Finset.mul_prod_erase I.1 _ hi).symm`. Establish `hxic : X i ^ c ∈ secOver S y ((c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)` using `pow_mem_secOver y (coord_mem_secOver y k₀ (e.symm i)) c`.

Establish `hP : (∏ j ∈ I.1.erase i, X j) ^ c ∈ secOver S y ((c : ℤ) • (((I.1.erase i).card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))` using `pow_mem_secOver y (prod_coord_mem_secOver y k₀ e _) c`. Use extensionality with `t`. Rewrite using `[SetLike.mem_coe, twist_sub_eq_mul]`. Express the relevant statement in the definitionally equal form `t ∈ Kleiman.twistMod S X (c : ℤ) I * Q.sub I ↔ _`. Rewrite using `[Kleiman.twistMod_eq_span (c : ℤ) I hi, Submodule.mem_span_singleton_mul, zpow_natCast]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Establish `hb' : b ∈ chartSecOver S y k₀ e β I` using `by rw [← hsubQ]; exact hb`. Take `⟨n, hn⟩` from `hb'`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `h` using `secOver_mul y hxic hn`. Rewrite using `[show Kleiman.xProd I ^ n * (X i ^ c * b) = X i ^ c * (Kleiman.xProd I ^ n * b) by ring]`. Use `h using 2` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨n, hn⟩`.

Use `⟨(X i ^ c)⁻¹ * t, ?_, by field_simp⟩` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, hsubQ]`. Use `⟨n + c, ?_⟩` and prove the remaining obligations. Establish `h` using `secOver_mul y hP hn`. Rewrite using `[show Kleiman.xProd I ^ (n + c) * ((X i ^ c)⁻¹ * t) = (∏ j ∈ I.1.erase i, X j) ^ c * (Kleiman.xProd I ^ n * t) by`.

Rewrite using `[hxI]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring]`. Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Rewrite using `[← hcard]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twist_sub_eq_chartSecOver (β : K → ℤ)
    (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (c : ℕ) (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) :
    ((Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (c : ℤ))).sub I : Set Ω) =
      chartSecOver S y k₀ e (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) I := by
  have hsubQ : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I := by
    refine Set.ext fun t => ?_
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : X i ≠ 0 := (Kleiman.mem_support _).mp (I.2.2 hi)
  have hcard := Finset.card_erase_add_one hi
  have hxI : Kleiman.xProd I = X i * ∏ j ∈ I.1.erase i, X j := (Finset.mul_prod_erase I.1 _ hi).symm
  have hxic : X i ^ c ∈ secOver S y ((c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) :=
    pow_mem_secOver y (coord_mem_secOver y k₀ (e.symm i)) c
  have hP : (∏ j ∈ I.1.erase i, X j) ^ c ∈
      secOver S y ((c : ℤ) • (((I.1.erase i).card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) :=
    pow_mem_secOver y (prod_coord_mem_secOver y k₀ e _) c
  ext t
  rw [SetLike.mem_coe, twist_sub_eq_mul]
  change t ∈ Kleiman.twistMod S X (c : ℤ) I * Q.sub I ↔ _
  rw [Kleiman.twistMod_eq_span (c : ℤ) I hi, Submodule.mem_span_singleton_mul, zpow_natCast]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ chartSecOver S y k₀ e β I := by rw [← hsubQ]; exact hb
    obtain ⟨n, hn⟩ := hb'
    refine ⟨n, ?_⟩
    have h := secOver_mul y hxic hn
    rw [show Kleiman.xProd I ^ n * (X i ^ c * b) = X i ^ c * (Kleiman.xProd I ^ n * b) by ring]
    convert h using 2
    abel
  · rintro ⟨n, hn⟩
    refine ⟨(X i ^ c)⁻¹ * t, ?_, by field_simp⟩
    rw [← SetLike.mem_coe, hsubQ]
    refine ⟨n + c, ?_⟩
    have h := secOver_mul y hP hn
    rw [show Kleiman.xProd I ^ (n + c) * ((X i ^ c)⁻¹ * t) =
        (∏ j ∈ I.1.erase i, X j) ^ c * (Kleiman.xProd I ^ n * t) by
      rw [hxI]; field_simp; ring]
    convert h using 2
    funext k
    rw [← hcard]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end ModelTwistGenerated

open ModelTwistGenerated in

/- English proof (translation)
Introduce `S _ K _ _ ι _ Ω _ _ y k₀ hS hM β`. Take `⟨i₀, -⟩` from `hM.1 k₀`. Establish `hpos : 0 < Fintype.card (ι k₀)` using `Fintype.card_pos_iff.mpr ⟨i₀⟩`. Use `set N := Fintype.card (ι k₀) - 1`. Establish `hcard : Fintype.card (ι k₀) = N + 1` using `by omega`.

Set `e : ι k₀ ≃ Fin (N + 1)` to `Fintype.equivFinOfCardEq hcard`. Use `set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx`. Take `⟨Q, hQ⟩` from `BundleOfDeg.full S K ι Ω y k₀ N e hM β`. Take `⟨c₀, hc₀⟩` from `GroundTheory.Heights₂.Heights.Kleiman.Generated.full S Ω N x Q`. Use `⟨max c₀ 0, fun c hc => ?_⟩` and prove the remaining obligations.

Use `lift c to ℕ using le_trans (le_max_right _ _) hc with m`. Use `set L := Q.twist (Kleiman.twistSys S x (m : ℤ)) with hL`. Establish `hgen : L.Generated` using `hc₀ m (le_trans (le_max_left _ _) hc)`. Establish `hfin : ∀ I : Kleiman.Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ L.secs ∧ Submodule.span (Kleiman.chartRing S x I) (T : Set Ω) = L.sub I`. Introduce `I`.

Take `⟨i, hi⟩` from `I.2.1`. Establish `hfg : (L.sub I).FG`. Rewrite using `[hL, twist_sub_eq_mul]`. Express the relevant statement in the definitionally equal form `(Kleiman.twistMod S x (m : ℤ) I * Q.sub I).FG`. Rewrite using `[Kleiman.twistMod_eq_span (m : ℤ) I hi]`.

Conclude with `(Submodule.fg_span_singleton _).mul (Q.fg I)`. Rewrite `hfg`, the goal using `[← hgen I]`. Take `⟨T, hT, hTs⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg`. Conclude with `⟨T, hT, hTs.symm⟩`. Use `choose T hTsub hTspan using hfin`.

Set `_ : Fintype (Kleiman.Chart x)` to `Fintype.ofFinite _`. Set `U : Finset Ω` to `Finset.univ.biUnion T`. Establish `hUsub : (U : Set Ω) ⊆ L.secs`. Introduce `z hz`. Take `⟨I, -, hzI⟩` from `Finset.mem_biUnion.mp hz`.

Conclude with `hTsub I hzI`. Establish `hUspan : ∀ I, Submodule.span (Kleiman.chartRing S x I) (U : Set Ω) = L.sub I`. Introduce `I`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hgen I]`.

Conclude with `Submodule.span_mono hUsub`. Rewrite using `[← hTspan I]`. Conclude with `Submodule.span_mono fun z hz => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, hz⟩`. Establish `hsecs : L.secs = secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)` using `hQ m`. Set `η : Fin U.card → Ω` to `fun j => (U.equivFin.symm j : Ω)`.

Establish `hrange : Set.range η = (U : Set Ω)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`. Conclude with `(U.equivFin.symm j).2`.

Introduce `hz`. Conclude with `⟨U.equivFin ⟨z, hz⟩, by simp [η]⟩`. Establish `hη : ∀ j, η j ∈ secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)`. Introduce `j`. Rewrite using `[← hsecs]`.

Conclude with `hUsub (U.equivFin.symm j).2`. Use `⟨U.card, η, hη, (hCG S K ι Ω y k₀ N e hM _ U.card η hη).mpr fun I => ?_⟩` and prove the remaining obligations. Rewrite using `[hrange, hUspan I]`. Conclude with `twist_sub_eq_chartSecOver e β Q hQ m I`.
-/
theorem ModelTwistGenerated.proof (hCG : ChartSecGen.Statement) : ModelTwistGenerated.Statement := by
  classical
  intro S _ K _ _ ι _ Ω _ _ y k₀ hS hM β
  obtain ⟨i₀, -⟩ := hM.1 k₀
  have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  set N := Fintype.card (ι k₀) - 1
  have hcard : Fintype.card (ι k₀) = N + 1 := by omega
  let e : ι k₀ ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full S K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := GroundTheory.Heights₂.Heights.Kleiman.Generated.full S Ω N x Q
  refine ⟨max c₀ 0, fun c hc => ?_⟩
  lift c to ℕ using le_trans (le_max_right _ _) hc with m
  set L := Q.twist (Kleiman.twistSys S x (m : ℤ)) with hL
  have hgen : L.Generated := hc₀ m (le_trans (le_max_left _ _) hc)
  have hfin : ∀ I : Kleiman.Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ L.secs ∧
      Submodule.span (Kleiman.chartRing S x I) (T : Set Ω) = L.sub I := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hfg : (L.sub I).FG := by
      rw [hL, twist_sub_eq_mul]
      change (Kleiman.twistMod S x (m : ℤ) I * Q.sub I).FG
      rw [Kleiman.twistMod_eq_span (m : ℤ) I hi]
      exact (Submodule.fg_span_singleton _).mul (Q.fg I)
    rw [← hgen I] at hfg ⊢
    obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
    exact ⟨T, hT, hTs.symm⟩
  choose T hTsub hTspan using hfin
  let _ : Fintype (Kleiman.Chart x) := Fintype.ofFinite _
  let U : Finset Ω := Finset.univ.biUnion T
  have hUsub : (U : Set Ω) ⊆ L.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hTsub I hzI
  have hUspan : ∀ I, Submodule.span (Kleiman.chartRing S x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hUsub
    · rw [← hTspan I]
      exact Submodule.span_mono fun z hz => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, hz⟩
  have hsecs : L.secs = secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := hQ m
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hz
      exact ⟨U.equivFin ⟨z, hz⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro j
    rw [← hsecs]
    exact hUsub (U.equivFin.symm j).2
  refine ⟨U.card, η, hη, (hCG S K ι Ω y k₀ N e hM _ U.card η hη).mpr fun I => ?_⟩
  rw [hrange, hUspan I]
  exact twist_sub_eq_chartSecOver e β Q hQ m I

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
