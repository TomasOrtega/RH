import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LB (resG_resG resG_self homOfLinear toMod)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM germ_resM)

namespace GlobalTheory

section FiniteSets

/- English proof (translation)
Use `lift S to Finset T using hS`. Proceed by induction on `S using Finset.strongInduction with`. Consider the case `H S ih`. Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨⊥, h0, by simp, bot_le⟩`.

Use `letI := specializationPreorder T`. Take `⟨x, hx, hmax⟩` from `S.exists_maximal hne`. Take `⟨A, hA, hSA, hAU⟩` from `ih (S.erase x) (Finset.erase_ssubset hx) fun y hy => hU (Finset.mem_of_mem_erase hy)`. Establish `hcl : IsClosed (⋃ y ∈ S.erase x, closure ({y} : Set T))` using `isClosed_biUnion_finset fun _ _ => isClosed_closure`. Take `⟨B, hB, hxB, hBU⟩` from `hb x (U ⊓ ⟨_, hcl.isOpen_compl⟩) ⟨hU hx, fun h => by`.

Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 h`. Establish `h₁ : y ⤳ x` using `specializes_iff_mem_closure.2 hxy`. Establish `h₂ : x ⤳ y` using `hmax (Finset.mem_of_mem_erase hy) h₁`. Conclude with `Finset.ne_of_mem_erase hy (h₁.antisymm h₂).eq⟩`. Distinguish the cases in `hxA : x ∈ A`.

Use `⟨A, hA, fun y hy => ?_, hAU⟩` and prove the remaining obligations. Break down `eq_or_ne y x with rfl | hyx` into its components or cases. Use `exacts [hxA, hSA (Finset.mem_erase.2 ⟨hyx, hy⟩)]`. Take `⟨C, hC, hle, h₁, h₂⟩` from `hadd A B hA hB`. Use `⟨C, hC, fun y hy => ?_, hle.trans (sup_le hAU (hBU.trans inf_le_left))⟩` and prove the remaining obligations.

Break down `eq_or_ne y x with rfl | hyx` into its components or cases. Conclude with `(h₂ y hxB).resolve_right hxA`. Establish `hy' : y ∈ S.erase x` using `Finset.mem_erase.2 ⟨hyx, hy⟩`. Conclude with `(h₁ y (hSA hy')).resolve_right fun h => (hBU h).2 (Set.mem_iUnion₂.2 ⟨y, hy', subset_closure rfl⟩)`.
-/
theorem exists_finite_subset_le_of_basis {T : Type*} [TopologicalSpace T] [T0Space T]
    (P : Opens T → Prop) (h0 : P ⊥) (hb : ∀ (x : T) (U : Opens T), x ∈ U → ∃ A, P A ∧ x ∈ A ∧ A ≤ U)
    (hadd : ∀ A B, P A → P B → ∃ C, P C ∧ C ≤ A ⊔ B ∧ (∀ x ∈ A, x ∈ C ∨ x ∈ B) ∧
      ∀ x ∈ B, x ∈ C ∨ x ∈ A)
    {S : Set T} (hS : S.Finite) {U : Opens T} (hU : S ⊆ U) : ∃ A, P A ∧ S ⊆ A ∧ A ≤ U := by
  classical
  lift S to Finset T using hS
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, h0, by simp, bot_le⟩
    letI := specializationPreorder T
    obtain ⟨x, hx, hmax⟩ := S.exists_maximal hne
    obtain ⟨A, hA, hSA, hAU⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
      fun y hy => hU (Finset.mem_of_mem_erase hy)
    have hcl : IsClosed (⋃ y ∈ S.erase x, closure ({y} : Set T)) :=
      isClosed_biUnion_finset fun _ _ => isClosed_closure
    obtain ⟨B, hB, hxB, hBU⟩ := hb x (U ⊓ ⟨_, hcl.isOpen_compl⟩) ⟨hU hx, fun h => by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 h
      have h₁ : y ⤳ x := specializes_iff_mem_closure.2 hxy
      have h₂ : x ⤳ y := hmax (Finset.mem_of_mem_erase hy) h₁
      exact Finset.ne_of_mem_erase hy (h₁.antisymm h₂).eq⟩
    by_cases hxA : x ∈ A
    · refine ⟨A, hA, fun y hy => ?_, hAU⟩
      rcases eq_or_ne y x with rfl | hyx
      exacts [hxA, hSA (Finset.mem_erase.2 ⟨hyx, hy⟩)]
    obtain ⟨C, hC, hle, h₁, h₂⟩ := hadd A B hA hB
    refine ⟨C, hC, fun y hy => ?_, hle.trans (sup_le hAU (hBU.trans inf_le_left))⟩
    rcases eq_or_ne y x with rfl | hyx
    · exact (h₂ y hxB).resolve_right hxA
    · have hy' : y ∈ S.erase x := Finset.mem_erase.2 ⟨hyx, hy⟩
      exact (h₁ y (hSA hy')).resolve_right fun h =>
        (hBU h).2 (Set.mem_iUnion₂.2 ⟨y, hy', subset_closure rfl⟩)

variable {X : Scheme.{0}} {L M : LB X}

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hx rw [mem_nonzeroLocus_iff_basicOpen _ hk, X.mem_basicOpen _ x hk, LB.add_f, map_add] at hx rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx with h | h · exact Or.inl (basicOpen_le_nonzeroLocus s k ((X.mem_basicOpen _ x h …`.
-/
theorem nonzeroLocus_add_le (s t : M.Sec) :
    nonzeroLocus (s + t) ≤ nonzeroLocus s ⊔ nonzeroLocus t := fun x hx => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hx
  rw [mem_nonzeroLocus_iff_basicOpen _ hk, X.mem_basicOpen _ x hk, LB.add_f,
    map_add] at hx
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx with h | h
  · exact Or.inl (basicOpen_le_nonzeroLocus s k ((X.mem_basicOpen _ x hk).2 h))
  · exact Or.inr (basicOpen_le_nonzeroLocus t k ((X.mem_basicOpen _ x hk).2 h))

/- English proof (translation)
The claim follows from `iSup_congr fun k => by rw [LB.neg_f, ← neg_one_mul, Scheme.basicOpen_mul, X.basicOpen_of_isUnit isUnit_one.neg, inf_eq_right.2 (X.basicOpen_le _)]`.
-/
theorem nonzeroLocus_neg (s : M.Sec) : nonzeroLocus (-s) = nonzeroLocus s :=
  iSup_congr fun k => by
    rw [LB.neg_f, ← neg_one_mul, Scheme.basicOpen_mul, X.basicOpen_of_isUnit isUnit_one.neg,
      inf_eq_right.2 (X.basicOpen_le _)]

/- English proof (translation)
Use `nonzeroLocus_add_le (s + t) (-t)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right, nonzeroLocus_neg]`. Then use the resulting hypothesis.
-/
theorem nonzeroLocus_le_add_sup (s t : M.Sec) :
    nonzeroLocus s ≤ nonzeroLocus (s + t) ⊔ nonzeroLocus t := by
  have := nonzeroLocus_add_le (s + t) (-t)
  rwa [add_neg_cancel_right, nonzeroLocus_neg] at this

/- English proof (translation)
Use `isAffineOpen_of_isAffineOpen_basicOpen _ {ProjSpace.secRatio (s + t) s, ProjSpace.secRatio (s + t) t} ?_ ?_` and prove the remaining obligations. Establish `h : ProjSpace.secRatio (s + t) s + ProjSpace.secRatio (s + t) t = 1`. Use `(ProjSpace.eq_secRatio (s + t) (s + t) fun l => ?_).trans (ProjSpace.secRatio_self _)` and prove the remaining obligations. Rewrite using `[map_add, add_mul, ← ProjSpace.secRatio_spec, ← ProjSpace.secRatio_spec, LB.add_f, map_add]`. Rewrite using `[Ideal.eq_top_iff_one, ← h]`.

Conclude with `add_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))`. Apply the tactic sequence `rintro _ (rfl | rfl) <;>`. Rewrite using `[ProjSpace.basicOpen_secRatio, inf_comm, ← ProjSpace.basicOpen_secRatio]`. Use `exacts [hs.basicOpen _, ht.basicOpen _]`.
-/
theorem isAffineOpen_nonzeroLocus_add {s t : M.Sec} (hs : IsAffineOpen (nonzeroLocus s))
    (ht : IsAffineOpen (nonzeroLocus t)) : IsAffineOpen (nonzeroLocus (s + t)) := by
  refine isAffineOpen_of_isAffineOpen_basicOpen _
    {ProjSpace.secRatio (s + t) s, ProjSpace.secRatio (s + t) t} ?_ ?_
  · have h : ProjSpace.secRatio (s + t) s + ProjSpace.secRatio (s + t) t = 1 := by
      refine (ProjSpace.eq_secRatio (s + t) (s + t) fun l => ?_).trans (ProjSpace.secRatio_self _)
      rw [map_add, add_mul, ← ProjSpace.secRatio_spec, ← ProjSpace.secRatio_spec, LB.add_f, map_add]
    rw [Ideal.eq_top_iff_one, ← h]
    exact add_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  · rintro _ (rfl | rfl) <;>
      rw [ProjSpace.basicOpen_secRatio, inf_comm, ← ProjSpace.basicOpen_secRatio]
    exacts [hs.basicOpen _, ht.basicOpen _]

/- English proof (translation)
Take `⟨_, ⟨n, hn, s, rfl, ha⟩, h₁, h₂⟩` from `exists_finite_subset_le_of_basis (fun A : X.Opens => ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, nonzeroLocus s = A ∧ IsAffineOpen A) ⟨1, le_rfl, _, nonzeroLocus_secZero, isAffineOpen_bot X⟩ (fun x U hx => by`. Take `⟨n, hn, s, h₁, h₂, h₃⟩` from `h.exists_affine_le hx`. Conclude with `⟨_, ⟨n, hn, s, rfl, h₃⟩, h₁, h₂⟩)`. Use the proof step `(by`. Introduce and unpack `_ _ ⟨m, hm, s, rfl, hs⟩ ⟨n, hn, t, rfl, ht⟩`.

Take `⟨s', e₁⟩ : ∃ s' : (lbPow L (m * n)).Sec, nonzeroLocus s' = nonzeroLocus s` from `⟨secPow s n, nonzeroLocus_secPow s hn⟩`. Take `⟨t', e₂⟩ : ∃ t' : (lbPow L (m * n)).Sec, nonzeroLocus t' = nonzeroLocus t` from `⟨secCast (Nat.mul_comm n m) (secPow t m), nonzeroLocus_secPow t hm⟩`. Rewrite `hs`, the goal using `[← e₁]`. Rewrite `ht`, the goal using `[← e₂]`. Conclude with `⟨_, ⟨m * n, Nat.mul_pos hm hn, s' + t', rfl, isAffineOpen_nonzeroLocus_add hs ht⟩, nonzeroLocus_add_le _ _, nonzeroLocus_le_add_sup _ _, add_comm t' s' ▸ nonzeroLocus_le_add_sup t' s'⟩) hS hU`.

Conclude with `⟨n, hn, s, h₁, h₂, ha⟩`.
-/
theorem IsAmpleLB.exists_affine_finite_subset (h : IsAmpleLB L) {S : Set X} (hS : S.Finite)
    {U : X.Opens} (hU : S ⊆ U) : ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec,
      S ⊆ nonzeroLocus s ∧ nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨_, ⟨n, hn, s, rfl, ha⟩, h₁, h₂⟩ := exists_finite_subset_le_of_basis
    (fun A : X.Opens => ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, nonzeroLocus s = A ∧ IsAffineOpen A)
    ⟨1, le_rfl, _, nonzeroLocus_secZero, isAffineOpen_bot X⟩
    (fun x U hx => by
      obtain ⟨n, hn, s, h₁, h₂, h₃⟩ := h.exists_affine_le hx
      exact ⟨_, ⟨n, hn, s, rfl, h₃⟩, h₁, h₂⟩)
    (by
      rintro _ _ ⟨m, hm, s, rfl, hs⟩ ⟨n, hn, t, rfl, ht⟩
      obtain ⟨s', e₁⟩ : ∃ s' : (lbPow L (m * n)).Sec, nonzeroLocus s' = nonzeroLocus s :=
        ⟨secPow s n, nonzeroLocus_secPow s hn⟩
      obtain ⟨t', e₂⟩ : ∃ t' : (lbPow L (m * n)).Sec, nonzeroLocus t' = nonzeroLocus t :=
        ⟨secCast (Nat.mul_comm n m) (secPow t m), nonzeroLocus_secPow t hm⟩
      rw [← e₁] at hs ⊢
      rw [← e₂] at ht ⊢
      exact ⟨_, ⟨m * n, Nat.mul_pos hm hn, s' + t', rfl, isAffineOpen_nonzeroLocus_add hs ht⟩,
        nonzeroLocus_add_le _ _, nonzeroLocus_le_add_sup _ _,
        add_comm t' s' ▸ nonzeroLocus_le_add_sup t' s'⟩) hS hU
  exact ⟨n, hn, s, h₁, h₂, ha⟩

/- English proof (translation)
Take `⟨_, ⟨s, rfl, ha⟩, h₁, h₂⟩` from `exists_finite_subset_le_of_basis (fun A : X.Opens => ∃ s : M.Sec, nonzeroLocus s = A ∧ IsAffineOpen A) ⟨_, nonzeroLocus_secZero, isAffineOpen_bot X⟩ (fun x U hx => by`. Take `⟨k, hk⟩` from `exists_chart hM x`. Take `⟨_, ⟨r, hr, rfl⟩, hx, hle⟩` from `Opens.isBasis_iff_nbhd.1 (Scheme.IsQuasiAffine.isBasis_basicOpen X) (show x ∈ U ⊓ M.U k from ⟨hx, hk⟩)`. Take `⟨u, hu⟩` from `exists_sec_nonzeroLocus_eq_basicOpen hM r k (hle.trans inf_le_right)`. Conclude with `⟨_, ⟨u, hu, hr⟩, hx, hle.trans inf_le_left⟩)`.

Use the proof step `(by`. Introduce and unpack `_ _ ⟨s, rfl, hs⟩ ⟨t, rfl, ht⟩`. Conclude with `⟨_, ⟨s + t, rfl, isAffineOpen_nonzeroLocus_add hs ht⟩, nonzeroLocus_add_le _ _, nonzeroLocus_le_add_sup _ _, add_comm t s ▸ nonzeroLocus_le_add_sup t s⟩) hS hU`. Conclude with `⟨s, h₁, h₂, ha⟩`.
-/
theorem exists_sec_finite_subset_of_isQuasiAffine [X.IsQuasiAffine] (hM : M.IsLB) {S : Set X}
    (hS : S.Finite) {U : X.Opens} (hU : S ⊆ U) : ∃ s : M.Sec,
      S ⊆ nonzeroLocus s ∧ nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨_, ⟨s, rfl, ha⟩, h₁, h₂⟩ := exists_finite_subset_le_of_basis
    (fun A : X.Opens => ∃ s : M.Sec, nonzeroLocus s = A ∧ IsAffineOpen A)
    ⟨_, nonzeroLocus_secZero, isAffineOpen_bot X⟩
    (fun x U hx => by
      obtain ⟨k, hk⟩ := exists_chart hM x
      obtain ⟨_, ⟨r, hr, rfl⟩, hx, hle⟩ := Opens.isBasis_iff_nbhd.1
        (Scheme.IsQuasiAffine.isBasis_basicOpen X) (show x ∈ U ⊓ M.U k from ⟨hx, hk⟩)
      obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hM r k (hle.trans inf_le_right)
      exact ⟨_, ⟨u, hu, hr⟩, hx, hle.trans inf_le_left⟩)
    (by
      rintro _ _ ⟨s, rfl, hs⟩ ⟨t, rfl, ht⟩
      exact ⟨_, ⟨s + t, rfl, isAffineOpen_nonzeroLocus_add hs ht⟩,
        nonzeroLocus_add_le _ _, nonzeroLocus_le_add_sup _ _,
        add_comm t s ▸ nonzeroLocus_le_add_sup t s⟩) hS hU
  exact ⟨s, h₁, h₂, ha⟩

/- English proof (translation)
Establish `hu : ∀ i, IsUnit (s.f i)` using `fun i => by`. Simplify `ProjSpace.isUnit_resG_sec s i (h.ge.trans' le_top) le_rfl` using `only [resG_self]`. Conclude with `⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩`.
-/
theorem exists_isGen_of_nonzeroLocus_eq_top (s : M.Sec) (h : nonzeroLocus s = ⊤) :
    ∃ t : M.Gen, t.IsGen := by
  have hu : ∀ i, IsUnit (s.f i) := fun i => by
    simpa only [resG_self] using ProjSpace.isUnit_resG_sec s i (h.ge.trans' le_top) le_rfl
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

/- English proof (translation)
Establish `: IsAffine W` using `hW`. Take `⟨s, h₁, -, h₂⟩` from `exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_pull hM W.ι) (S := W.ι ⁻¹' S) (hS.preimage W.ι.isOpenEmbedding.injective.injOn) (U := ⊤) (Set.subset_univ _)`. Establish `hle : W.ι ''ᵁ nonzeroLocus s ≤ W` using `W.ι_image_le _`. Use `⟨W.ι ''ᵁ nonzeroLocus s, h₂.image_of_isOpenImmersion _, fun x hx => ⟨⟨x, hSW hx⟩, h₁ hx, rfl⟩, hle, ?_⟩` and prove the remaining obligations. Use `exists_isGen_of_nonzeroLocus_eq_top (chartSec (chartPullSame M (fun _ : PUnit => (W.ι ''ᵁ nonzeroLocus s).ι) (fun _ => W.ι) (fun _ => 1) (X.homOfLE hle) fun _ => (X.homOfLE_ι hle).symm) s) ?_` and prove the remaining obligations.

Rewrite using `[nonzeroLocus_chartSec _ _ fun y _ _ => exists_chart (LB.isLB_pull hM _) y]`. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨z, hz, e⟩` from `y.2`. Establish `: X.homOfLE hle y = z` using `Subtype.ext ((X.homOfLE_apply hle y).trans e.symm)`. Conclude with `(this ▸ hz : X.homOfLE hle y ∈ nonzeroLocus s)`.
-/
theorem exists_affine_finite_subset_trivial (hM : M.IsLB) {S : Set X} (hS : S.Finite) {W : X.Opens}
    (hW : IsAffineOpen W) (hSW : S ⊆ W) : ∃ V : X.Opens, IsAffineOpen V ∧ S ⊆ V ∧ V ≤ W ∧
      ∃ t : (M.pull V.ι).Gen, t.IsGen := by
  have : IsAffine W := hW
  obtain ⟨s, h₁, -, h₂⟩ := exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_pull hM W.ι)
    (S := W.ι ⁻¹' S) (hS.preimage W.ι.isOpenEmbedding.injective.injOn) (U := ⊤) (Set.subset_univ _)
  have hle : W.ι ''ᵁ nonzeroLocus s ≤ W := W.ι_image_le _
  refine ⟨W.ι ''ᵁ nonzeroLocus s, h₂.image_of_isOpenImmersion _,
    fun x hx => ⟨⟨x, hSW hx⟩, h₁ hx, rfl⟩, hle, ?_⟩
  refine exists_isGen_of_nonzeroLocus_eq_top (chartSec (chartPullSame M
    (fun _ : PUnit => (W.ι ''ᵁ nonzeroLocus s).ι) (fun _ => W.ι) (fun _ => 1) (X.homOfLE hle)
    fun _ => (X.homOfLE_ι hle).symm) s) ?_
  rw [nonzeroLocus_chartSec _ _ fun y _ _ => exists_chart (LB.isLB_pull hM _) y]
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨z, hz, e⟩ := y.2
  have : X.homOfLE hle y = z := Subtype.ext ((X.homOfLE_apply hle y).trans e.symm)
  exact (this ▸ hz : X.homOfLE hle y ∈ nonzeroLocus s)

/- English proof (translation)
Take `⟨n, -, s, h₁, h₂, h₃⟩` from `h.exists_affine_finite_subset hS hU`. Take `⟨V, hV, hSV, hle, ht⟩` from `GlobalTheory.exists_affine_finite_subset_trivial hM hS h₃ h₁`. Conclude with `⟨V, hV, hSV, hle.trans h₂, ht⟩`.
-/
theorem IsAmpleLB.exists_affine_finite_subset_trivial (h : IsAmpleLB L) (hM : M.IsLB) {S : Set X}
    (hS : S.Finite) {U : X.Opens} (hU : S ⊆ U) : ∃ V : X.Opens, IsAffineOpen V ∧ S ⊆ V ∧ V ≤ U ∧
      ∃ t : (M.pull V.ι).Gen, t.IsGen := by
  obtain ⟨n, -, s, h₁, h₂, h₃⟩ := h.exists_affine_finite_subset hS hU
  obtain ⟨V, hV, hSV, hle, ht⟩ := GlobalTheory.exists_affine_finite_subset_trivial hM hS h₃ h₁
  exact ⟨V, hV, hSV, hle.trans h₂, ht⟩

end FiniteSets

namespace QCoh

variable {X : Scheme.{0}} {F G : X.Modules} {ι : Type}

variable (F) in

def IsGloballyGenerated : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (φ : freeModule X ι ⟶ F), Epi φ

def SpanStalks (s : ι → Γ(F, ⊤)) : Prop :=
  ∀ x : X, Submodule.span (X.presheaf.stalk x)
    (Set.range fun i => (F.presheaf.germ ⊤ x trivial (s i) : (F.presheaf.stalk x :))) = ⊤

def sectionHom (s : Γ(F, ⊤)) : structureModule X ⟶ F :=
  homOfLinear (fun V => LinearMap.toSpanSingleton Γ(X, V) Γ(F, V) (resM F le_top s) ∘ₗ
    (structureModuleSectionsEquiv V).toLinearMap) fun h a =>
      ((resM_smul h (structureModuleSectionsEquiv _ a) (resM F le_top s)).trans
        (congrArg (_ • ·) (resM_resM _ _ _))).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sectionHom_app (s : Γ(F, ⊤)) (V : X.Opens) (a : Γ(structureModule X, V)) :
    (sectionHom s).app V a = structureModuleSectionsEquiv V a • resM F le_top s := rfl

def sectionsHom (s : ι → Γ(F, ⊤)) : freeModule X ι ⟶ F :=
  Sigma.desc (f := fun _ : ι => structureModule X) fun i => sectionHom (s i)

variable (X) in

def freeι (i : ι) : structureModule X ⟶ freeModule X ι :=
  Sigma.ι (fun _ : ι => structureModule X) i

variable (X) in

def freeBasis (i : ι) : Γ(freeModule X ι, ⊤) :=
  (freeι X i).app ⊤ ((structureModuleSectionsEquiv ⊤).symm 1)

/- English proof (translation)
Rewrite using `[← app_resM, ← Scheme.Modules.Hom.app_smul]`. Use `congr 1`. Apply `(structureModuleSectionsEquiv V).injective` to reduce the goal to its premises. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `((congrArg (_ * ·) (map_one (resG X le_top))).trans (mul_one _)).symm`.
-/
theorem app_eq_smul (φ : structureModule X ⟶ F) (V : X.Opens) (a : Γ(structureModule X, V)) :
    φ.app V a = structureModuleSectionsEquiv V a •
      resM F le_top (φ.app ⊤ ((structureModuleSectionsEquiv ⊤).symm 1)) := by
  rw [← app_resM, ← Scheme.Modules.Hom.app_smul]
  congr 1
  apply (structureModuleSectionsEquiv V).injective
  rw [map_smul, smul_eq_mul]
  exact ((congrArg (_ * ·) (map_one (resG X le_top))).trans (mul_one _)).symm

/- English proof (translation)
Establish `e : freeι X i ≫ sectionsHom s = sectionHom (s i)` using `Sigma.ι_desc _ _`. Rewrite using `[freeBasis, app_app, e, sectionHom_app, LinearEquiv.apply_symm_apply, one_smul, Twist.resM_self]`.
-/
@[simp] theorem sectionsHom_app_freeBasis (s : ι → Γ(F, ⊤)) (i : ι) :
    (sectionsHom s).app ⊤ (freeBasis X i) = s i := by
  have e : freeι X i ≫ sectionsHom s = sectionHom (s i) := Sigma.ι_desc _ _
  rw [freeBasis, app_app, e, sectionHom_app, LinearEquiv.apply_symm_apply, one_smul,
    Twist.resM_self]

/- English proof (translation)
Set `p : ι → (freeModule X ι ⟶ structureModule X)` to `fun i => Sigma.desc (f := fun _ : ι => structureModule X) fun j => if j = i then 𝟙 _ else 0`. Establish `hp : ∀ i j, freeι X j ≫ p i = if j = i then 𝟙 _ else 0` using `fun i j => Sigma.ι_desc _ _`. Establish `h : ∑ i, p i ≫ freeι X i = 𝟙 _`. Use `Sigma.hom_ext (f := fun _ : ι => structureModule X) _ _ fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `freeι X j ≫ _ = freeι X j ≫ _`.

Simplify using `[Preadditive.comp_sum, reassoc_of% hp, ite_comp]`. Use `⟨fun i => structureModuleSectionsEquiv V ((p i).app V t), ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← sum_app_app p (freeι X) h t]`. Conclude with `Finset.sum_congr rfl fun i _ => (app_eq_smul _ _ _).symm`.
-/
theorem exists_sum_smul_freeBasis [Fintype ι] (V : X.Opens) (t : Γ(freeModule X ι, V)) :
    ∃ a : ι → Γ(X, V), ∑ i, a i • resM _ le_top (freeBasis X i) = t := by
  classical
  let p : ι → (freeModule X ι ⟶ structureModule X) := fun i =>
    Sigma.desc (f := fun _ : ι => structureModule X) fun j => if j = i then 𝟙 _ else 0
  have hp : ∀ i j, freeι X j ≫ p i = if j = i then 𝟙 _ else 0 := fun i j => Sigma.ι_desc _ _
  have h : ∑ i, p i ≫ freeι X i = 𝟙 _ := by
    refine Sigma.hom_ext (f := fun _ : ι => structureModule X) _ _ fun j => ?_
    change freeι X j ≫ _ = freeι X j ≫ _
    simp [Preadditive.comp_sum, reassoc_of% hp, ite_comp]
  refine ⟨fun i => structureModuleSectionsEquiv V ((p i).app V t), ?_⟩
  conv_rhs => rw [← sum_app_app p (freeι X) h t]
  exact Finset.sum_congr rfl fun i _ => (app_eq_smul _ _ _).symm

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `le_antisymm ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨a, rfl⟩` from `exists_sum_smul_freeBasis V t`. Rewrite using `[map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, appLinear_apply, app_resM]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨_, app_resM φ le_top _⟩`.
-/
theorem range_appLinear_free [Finite ι] (φ : freeModule X ι ⟶ F) (V : X.Opens) :
    LinearMap.range (appLinear φ V) =
      Submodule.span Γ(X, V) (Set.range fun i => resM F le_top (φ.app ⊤ (freeBasis X i))) := by
  have := Fintype.ofFinite ι
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨t, rfl⟩
    obtain ⟨a, rfl⟩ := exists_sum_smul_freeBasis V t
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, app_resM φ le_top _⟩

/- English proof (translation)
Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem _ h`. Take `⟨i, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨i, (germ_resM le_top hx _).symm⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h h' => rw [map_add]`. Conclude with `add_mem h h'`. Consider the case `smul a _ _ h => rw [germ_smul]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem germ_mem_span (s : ι → Γ(F, ⊤)) {V : X.Opens} {x : X} (hx : x ∈ V) {t : Γ(F, V)}
    (ht : t ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F le_top (s i))) :
    F.presheaf.germ V x hx t ∈ Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => (F.presheaf.germ ⊤ x trivial (s i) : (F.presheaf.stalk x :))) := by
  induction ht using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact Submodule.subset_span ⟨i, (germ_resM le_top hx _).symm⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a _ _ h => rw [germ_smul]; exact Submodule.smul_mem _ _ h

/- English proof (translation)
Rewrite using `[epi_iff_stalkLinear_surjective]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.range_eq_top]`. Use `iff_of_eq (congrArg (· = ⊤) (le_antisymm ?_ (Submodule.span_le.2 ?_)))` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Take `⟨V, hx, t, rfl⟩` from `(freeModule X ι).presheaf.exists_germ_eq t`. Rewrite using `[stalkLinear_germ]`. Conclude with `germ_mem_span _ hx ((range_appLinear_free φ V).le ⟨t, rfl⟩)`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨_, stalkLinear_germ (U := ⊤) φ x trivial _⟩`.
-/
theorem epi_iff_spanStalks [Finite ι] (φ : freeModule X ι ⟶ F) :
    Epi φ ↔ SpanStalks fun i => φ.app ⊤ (freeBasis X i) := by
  rw [epi_iff_stalkLinear_surjective]
  refine forall_congr' fun x => ?_
  rw [← LinearMap.range_eq_top]
  refine iff_of_eq (congrArg (· = ⊤) (le_antisymm ?_ (Submodule.span_le.2 ?_)))
  · rintro _ ⟨t, rfl⟩
    obtain ⟨V, hx, t, rfl⟩ := (freeModule X ι).presheaf.exists_germ_eq t
    rw [stalkLinear_germ]
    exact germ_mem_span _ hx ((range_appLinear_free φ V).le ⟨t, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, stalkLinear_germ (U := ⊤) φ x trivial _⟩

/- English proof (translation)
Simplify using `only [epi_iff_spanStalks, sectionsHom_app_freeBasis]`.
-/
theorem epi_sectionsHom_iff [Finite ι] (s : ι → Γ(F, ⊤)) : Epi (sectionsHom s) ↔ SpanStalks s := by
  simp only [epi_iff_spanStalks, sectionsHom_app_freeBasis]

/- English proof (translation)
Assemble the required witnesses or components as `⟨ι, inferInstance, sectionsHom s, (epi_sectionsHom_iff s).2 h⟩`.
-/
theorem SpanStalks.isGloballyGenerated [Finite ι] {s : ι → Γ(F, ⊤)} (h : SpanStalks s) :
    IsGloballyGenerated F :=
  ⟨ι, inferInstance, sectionsHom s, (epi_sectionsHom_iff s).2 h⟩

/- English proof (translation)
Use `⟨fun ⟨ι, _, φ, hφ⟩ => ?_, fun ⟨_, _, h⟩ => h.isGloballyGenerated⟩` and prove the remaining obligations. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin ι`. Use `⟨n, fun i => φ.app ⊤ (freeBasis X (e.symm i)), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← (epi_iff_spanStalks φ).1 hφ x]`. Conclude with `congrArg _ (e.symm.surjective.range_comp fun i => (F.presheaf.germ ⊤ x trivial (φ.app ⊤ (freeBasis X i)) : (F.presheaf.stalk x :)))`.
-/
theorem isGloballyGenerated_iff_spanStalks :
    IsGloballyGenerated F ↔ ∃ (n : ℕ) (s : Fin n → Γ(F, ⊤)), SpanStalks s := by
  refine ⟨fun ⟨ι, _, φ, hφ⟩ => ?_, fun ⟨_, _, h⟩ => h.isGloballyGenerated⟩
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨n, fun i => φ.app ⊤ (freeBasis X (e.symm i)), fun x => ?_⟩
  rw [← (epi_iff_spanStalks φ).1 hφ x]
  exact congrArg _ (e.symm.surjective.range_comp
    fun i => (F.presheaf.germ ⊤ x trivial (φ.app ⊤ (freeBasis X i)) : (F.presheaf.stalk x :)))

/- English proof (translation)
The claim follows from `have ⟨ι, hι, ψ, _⟩ := h ⟨ι, hι, ψ ≫ φ, inferInstance⟩`.
-/
theorem IsGloballyGenerated.of_epi (h : IsGloballyGenerated F) (φ : F ⟶ G) [Epi φ] :
    IsGloballyGenerated G :=
  have ⟨ι, hι, ψ, _⟩ := h
  ⟨ι, hι, ψ ≫ φ, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.of_epi e.hom, fun h => h.of_epi e.inv⟩`.
-/
theorem isGloballyGenerated_iff_of_iso (e : F ≅ G) :
    IsGloballyGenerated F ↔ IsGloballyGenerated G :=
  ⟨fun h => h.of_epi e.hom, fun h => h.of_epi e.inv⟩

/- English proof (translation)
The claim follows from `have ⟨_, _, φ, _⟩ := h .of_epi φ`.
-/
theorem IsGloballyGenerated.isFiniteQC (h : IsGloballyGenerated F) [F.IsQuasicoherent] :
    IsFiniteQC F :=
  have ⟨_, _, φ, _⟩ := h
  .of_epi φ

/- English proof (translation)
Introduce `x`. Take `⟨V, hV, hx, hs⟩` from `h x`. Take `⟨x, rfl⟩ : ∃ x' : V, x' = x` from `⟨⟨x, hx⟩, rfl⟩`. Use `hV.isLocalization_stalk x` as an intermediate fact. Use `isLocalizedModule_germLinear F hV x` as an intermediate fact.

Use `top_le_iff.1 ((span_eq_top_of_isLocalizedModule (X.presheaf.stalk (x : X)) (hV.primeIdealOf x).asIdeal.primeCompl (germLinear F x) (Submodule.span_univ)).ge.trans (Submodule.span_le.2 ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨t, -, rfl⟩`. Conclude with `germ_mem_span s x.2 (hs.ge trivial)`.
-/
theorem spanStalks_of_forall_exists_affine [F.IsQuasicoherent] (s : ι → Γ(F, ⊤))
    (h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      Submodule.span Γ(X, V) (Set.range fun i => resM F (le_top : V ≤ ⊤) (s i)) = ⊤) : SpanStalks s := by
  intro x
  obtain ⟨V, hV, hx, hs⟩ := h x
  obtain ⟨x, rfl⟩ : ∃ x' : V, x' = x := ⟨⟨x, hx⟩, rfl⟩
  have := hV.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hV x
  refine top_le_iff.1 ((span_eq_top_of_isLocalizedModule (X.presheaf.stalk (x : X))
    (hV.primeIdealOf x).asIdeal.primeCompl (germLinear F x) (Submodule.span_univ)).ge.trans
      (Submodule.span_le.2 ?_))
  rintro _ ⟨t, -, rfl⟩
  exact germ_mem_span s x.2 (hs.ge trivial)

end QCoh

open QCoh Twist

section Ample

variable {X : Scheme.{0}} {L M : LB X} {F : X.Modules}

/- English proof (translation)
Take `⟨m, b, hb⟩` from `isGloballyGenerated_iff_spanStalks.1 h`. Establish `hM'` using `hM.isLB`. Take `⟨n, s, hs⟩` from `hM`. Use `SpanStalks.isGloballyGenerated (s := fun p : Fin n × Fin m => (secHom F (s p.1)).app ⊤ (b p.2)) fun x => top_le_iff.1 fun t _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))`.

Take `⟨V, hV, hx, t, rfl⟩` from `exists_germ_eq_of_mem hi t`. Take `⟨u, rfl⟩` from `(bijective_secHom_app hM' (s i) hV).2 t`. Rewrite using `[← stalkLinear_germ]`. Use `Submodule.mem_map_of_mem (f := stalkLinear (secHom F (s i)) x) ((hb x).ge (Submodule.mem_top (x := F.presheaf.germ V x hx u)))` as an intermediate fact. Rewrite `this` using `[Submodule.map_span]`.

Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `⟨(i, j), (stalkLinear_germ (U := ⊤) _ x trivial _).symm⟩`.
-/
theorem QCoh.IsGloballyGenerated.twist (h : IsGloballyGenerated F) (hM : IsGenerated M) :
    IsGloballyGenerated (twist F M) := by
  obtain ⟨m, b, hb⟩ := isGloballyGenerated_iff_spanStalks.1 h
  have hM' := hM.isLB
  obtain ⟨n, s, hs⟩ := hM
  refine SpanStalks.isGloballyGenerated
    (s := fun p : Fin n × Fin m => (secHom F (s p.1)).app ⊤ (b p.2)) fun x => top_le_iff.1 fun t _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
  obtain ⟨V, hV, hx, t, rfl⟩ := exists_germ_eq_of_mem hi t
  obtain ⟨u, rfl⟩ := (bijective_secHom_app hM' (s i) hV).2 t
  rw [← stalkLinear_germ]
  have := Submodule.mem_map_of_mem (f := stalkLinear (secHom F (s i)) x)
    ((hb x).ge (Submodule.mem_top (x := F.presheaf.germ V x hx u)))
  rw [Submodule.map_span] at this
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact ⟨(i, j), (stalkLinear_germ (U := ⊤) _ x trivial _).symm⟩

/- English proof (translation)
Use `isFiniteQC_twist (F := F) (isLB_lbZPow hL r)` as an intermediate fact. Use `finite_sections (twistZ F L r) hσ` as an intermediate fact. Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := Γ(X, nonzeroLocus σ)) (M := Γ(twistZ F L r, nonzeroLocus σ))`. Use `(eventually_all.2 fun j => eventually_exists_resM_eq_mulSecOfEq_zpowSec hL σ (W := ⊤) isCompact_univ isQuasiSeparated_univ le_top (top_inf_eq _).symm (b j)).mono fun k hk n hn => ?_` and prove the remaining obligations. Use `choose a ha using fun j => hk j n hn`.

Use `⟨m, a, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (Submodule.map (appLinear (mulSecOfEq F (zpowSec σ k) hn) _)) hb`. Rewrite `e` using `[Submodule.map_span, ← Set.range_comp, Submodule.map_top, (LinearMap.range_eq_top (f := appLinear (mulSecOfEq F (zpowSec σ k) hn) _)).2 (bijective_mulSecOfEq_app hL _ hn (nonzeroLocus_le_zpowSec hL σ k)).2]`. Rewrite using `[← e]`. Conclude with `congrArg (fun f => Submodule.span _ (Set.range f)) (funext ha)`.
-/
theorem Twist.eventually_exists_span_resM_eq_top [CompactSpace X] [QuasiSeparatedSpace X]
    [IsFiniteQC F] (hL : L.IsLB) {d : ℤ} (σ : LB.Sec (lbZPow L d))
    (hσ : IsAffineOpen (nonzeroLocus σ)) (r : ℤ) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℤ, r + k * d = n → ∃ (m : ℕ) (a : Fin m → Γ(twistZ F L n, ⊤)),
      Submodule.span Γ(X, nonzeroLocus σ)
        (Set.range fun j => resM _ (le_top : nonzeroLocus σ ≤ ⊤) (a j)) = ⊤ := by
  have := isFiniteQC_twist (F := F) (isLB_lbZPow hL r)
  have := finite_sections (twistZ F L r) hσ
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := Γ(X, nonzeroLocus σ))
    (M := Γ(twistZ F L r, nonzeroLocus σ))
  refine (eventually_all.2 fun j => eventually_exists_resM_eq_mulSecOfEq_zpowSec hL σ (W := ⊤)
    isCompact_univ isQuasiSeparated_univ le_top (top_inf_eq _).symm (b j)).mono fun k hk n hn => ?_
  choose a ha using fun j => hk j n hn
  refine ⟨m, a, ?_⟩
  have e := congrArg (Submodule.map (appLinear (mulSecOfEq F (zpowSec σ k) hn) _)) hb
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    (LinearMap.range_eq_top (f := appLinear (mulSecOfEq F (zpowSec σ k) hn) _)).2
    (bijective_mulSecOfEq_app hL _ hn (nonzeroLocus_le_zpowSec hL σ k)).2] at e
  rw [← e]
  exact congrArg (fun f => Submodule.span _ (Set.range f)) (funext ha)

/- English proof (translation)
Use `h.compactSpace` as an intermediate fact. Use `h.quasiSeparatedSpace` as an intermediate fact. Take `⟨d, hd, N, σ, hσ, ha⟩` from `h.exists_cover`. Establish `hd' : (0 : ℤ) < d` using `by exact_mod_cast hd`. Take `⟨K, hK⟩` from `eventually_atTop.1 ((eventually_all_finset (Finset.Ico (0 : ℤ) d)).2 fun r _ => eventually_all.2 fun i => eventually_exists_span_resM_eq_top (F := F) h.isLB (d := d) (σ i) (ha i) r)`.

Use `eventually_atTop.2 ⟨K * d, fun n hn => ?_⟩` and prove the remaining obligations. Establish `h₁ : (K : ℤ) ≤ n / d` using `(Int.le_ediv_iff_mul_le hd').2 hn`. Establish `h₂ : ((n / d).toNat : ℤ) = n / d` using `Int.toNat_of_nonneg (by omega)`. Use `choose m a hs using fun i => hK (n / d).toNat (by omega) (n % d) (Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩) i n (by rw [h₂]; exact Int.emod_add_ediv_mul n d)`. Use `isQuasicoherent_twist (F := F) (isLB_lbZPow h.isLB n)` as an intermediate fact.

Use `(spanStalks_of_forall_exists_affine (fun p : Σ i, Fin (m i) => a p.1 p.2) fun x => ?_).isGloballyGenerated` and prove the remaining obligations. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 (hσ.ge (Set.mem_univ x))`. Use `⟨_, ha i, hi, top_le_iff.1 ((hs i).ge.trans (Submodule.span_mono ?_))⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨⟨i, j⟩, rfl⟩`.
-/
theorem IsAmpleLB.eventually_isGloballyGenerated_twistZ (h : IsAmpleLB L) (F : X.Modules)
    [IsFiniteQC F] : ∀ᶠ n : ℤ in atTop, IsGloballyGenerated (twistZ F L n) := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨d, hd, N, σ, hσ, ha⟩ := h.exists_cover
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((eventually_all_finset (Finset.Ico (0 : ℤ) d)).2 fun r _ =>
    eventually_all.2 fun i =>
      eventually_exists_span_resM_eq_top (F := F) h.isLB (d := d) (σ i) (ha i) r)
  refine eventually_atTop.2 ⟨K * d, fun n hn => ?_⟩
  have h₁ : (K : ℤ) ≤ n / d := (Int.le_ediv_iff_mul_le hd').2 hn
  have h₂ : ((n / d).toNat : ℤ) = n / d := Int.toNat_of_nonneg (by omega)
  choose m a hs using fun i => hK (n / d).toNat (by omega) (n % d)
    (Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩) i n
    (by rw [h₂]; exact Int.emod_add_ediv_mul n d)
  have := isQuasicoherent_twist (F := F) (isLB_lbZPow h.isLB n)
  refine (spanStalks_of_forall_exists_affine (fun p : Σ i, Fin (m i) => a p.1 p.2)
    fun x => ?_).isGloballyGenerated
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hσ.ge (Set.mem_univ x))
  refine ⟨_, ha i, hi, top_le_iff.1 ((hs i).ge.trans (Submodule.span_mono ?_))⟩
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨i, j⟩, rfl⟩

/- English proof (translation)
The claim follows from `tendsto_natCast_atTop_atTop.eventually (h.eventually_isGloballyGenerated_twistZ F)`.
-/
theorem IsAmpleLB.eventually_isGloballyGenerated_twist (h : IsAmpleLB L) (F : X.Modules)
    [IsFiniteQC F] : ∀ᶠ n : ℕ in atTop, IsGloballyGenerated (twist F (lbPow L n)) :=
  tendsto_natCast_atTop_atTop.eventually (h.eventually_isGloballyGenerated_twistZ F)

/- English proof (translation)
Take `⟨k, s, hs⟩` from `isGloballyGenerated_iff_spanStalks.1 h`. Use `(epi_sectionsHom_iff s).2 hs` as an intermediate fact. Establish `hL'` using `isLB_lbZPow hL (-n)`. Use `(epi_map_iff hL' (sectionsHom s)).2 this` as an intermediate fact. Use `preservesColimits_twistFunctor hL'` as an intermediate fact.

Set `e : (∐ fun _ : Fin k => toMod (lbZPow L (-n))) ≅ GlobalTheory.twist (freeModule X (Fin k)) (lbZPow L (-n))` to `Sigma.mapIso (fun _ => (unitTwistIso (lbZPow L (-n))).symm) ≪≫ (PreservesCoproduct.iso (twistFunctor (lbZPow L (-n))) fun _ : Fin k => structureModule X).symm`. Conclude with `⟨k, e.hom ≫ Twist.map _ (sectionsHom s) ≫ (twistZAddIso F hL (add_neg_cancel n)).hom ≫ (twistZZeroIso F hL).inv, inferInstance⟩`.
-/
theorem QCoh.IsGloballyGenerated.exists_epi_sigma (hL : L.IsLB) {n : ℤ}
    (h : IsGloballyGenerated (twistZ F L n)) :
    ∃ (k : ℕ) (φ : (∐ fun _ : Fin k => toMod (lbZPow L (-n))) ⟶ F), Epi φ := by
  obtain ⟨k, s, hs⟩ := isGloballyGenerated_iff_spanStalks.1 h
  have := (epi_sectionsHom_iff s).2 hs
  have hL' := isLB_lbZPow hL (-n)
  have := (epi_map_iff hL' (sectionsHom s)).2 this
  have := preservesColimits_twistFunctor hL'
  let e : (∐ fun _ : Fin k => toMod (lbZPow L (-n))) ≅
      GlobalTheory.twist (freeModule X (Fin k)) (lbZPow L (-n)) :=
    Sigma.mapIso (fun _ => (unitTwistIso (lbZPow L (-n))).symm) ≪≫
      (PreservesCoproduct.iso (twistFunctor (lbZPow L (-n))) fun _ : Fin k => structureModule X).symm
  exact ⟨k, e.hom ≫ Twist.map _ (sectionsHom s) ≫ (twistZAddIso F hL (add_neg_cancel n)).hom ≫
    (twistZZeroIso F hL).inv, inferInstance⟩

/- English proof (translation)
The claim follows from `(h.eventually_isGloballyGenerated_twistZ F).mono fun _ hn => hn.exists_epi_sigma h.isLB`.
-/
theorem IsAmpleLB.eventually_exists_epi_sigma (h : IsAmpleLB L) (F : X.Modules) [IsFiniteQC F] :
    ∀ᶠ n : ℤ in atTop,
      ∃ (k : ℕ) (φ : (∐ fun _ : Fin k => toMod (lbZPow L (-n))) ⟶ F), Epi φ :=
  (h.eventually_isGloballyGenerated_twistZ F).mono fun _ hn => hn.exists_epi_sigma h.isLB

end Ample

section Converse

variable {X : Scheme.{0}} {L M : LB X} {J : X.Modules}

def Twist.secOfTwist (j : J ⟶ structureModule X) (a : Γ(twist J M, ⊤)) : M.Sec :=
  LB.globalEquiv M ((unitTwistIso M).hom.app ⊤ ((Twist.map M j).app ⊤ a))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Twist.secOfTwist_f (j : J ⟶ structureModule X) (a : Γ(twist J M, ⊤)) (i : M.ι) :
    (secOfTwist j a).f i = resG X (le_inf le_top le_rfl)
      (structureModuleSectionsEquiv _ (j.app _ (coord a i))) := rfl

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_chart hM x`. Set `l` to `(structureModuleStalkEquiv x).toLinearMap ∘ₗ stalkLinear j x ∘ₗ (stalkEquiv J hM c hc).toLinearMap`. Use `by_contra! H`. Establish `hle : (⊤ : Submodule (X.presheaf.stalk x) ((twist J M).presheaf.stalk x :)) ≤ Submodule.comap l (IsLocalRing.maximalIdeal _)`. Rewrite using `[← ha x, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩ hu`. Use `H i (basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_))` and prove the remaining obligations. Establish `hm : x ∈ ⊤ ⊓ M.U c` using `⟨trivial, hc⟩`. Establish `e : l ((twist J M).presheaf.germ ⊤ x trivial (a i)) = X.presheaf.germ _ x hm (structureModuleSectionsEquiv _ (j.app _ (coord (a i) c)))`. Rewrite using `[← structureModuleStalkEquiv_germ, ← stalkLinear_germ]`.

Conclude with `congrArg (fun u => structureModuleStalkEquiv x (stalkLinear j x u)) (stalkEquiv_germ hM c hc (V := ⊤) trivial (a i))`. Rewrite `hu` using `[e]`. Rewrite using `[secOfTwist_f]`. Conclude with `(congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu`. Use `hle (Submodule.mem_top (x := (stalkEquiv J hM c hc).symm (J.presheaf.germ U x hx t))) ?_` and prove the remaining obligations.

Simplify using `only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, stalkLinear_germ, structureModuleStalkEquiv_germ, ht, map_one, isUnit_one]`.
-/
theorem Twist.exists_mem_nonzeroLocus_secOfTwist (hM : M.IsLB) (j : J ⟶ structureModule X)
    {ι : Type} {a : ι → Γ(twist J M, ⊤)} (ha : SpanStalks a) {U : X.Opens} {x : X} (hx : x ∈ U)
    (t : Γ(J, U)) (ht : structureModuleSectionsEquiv U (j.app U t) = 1) :
    ∃ i, x ∈ nonzeroLocus (secOfTwist j (a i)) := by
  obtain ⟨c, hc⟩ := exists_chart hM x
  let l := (structureModuleStalkEquiv x).toLinearMap ∘ₗ stalkLinear j x ∘ₗ
    (stalkEquiv J hM c hc).toLinearMap
  by_contra! H
  have hle : (⊤ : Submodule (X.presheaf.stalk x) ((twist J M).presheaf.stalk x :)) ≤
      Submodule.comap l (IsLocalRing.maximalIdeal _) := by
    rw [← ha x, Submodule.span_le]
    rintro _ ⟨i, rfl⟩ hu
    refine H i (basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_))
    have hm : x ∈ ⊤ ⊓ M.U c := ⟨trivial, hc⟩
    have e : l ((twist J M).presheaf.germ ⊤ x trivial (a i)) = X.presheaf.germ _ x hm
        (structureModuleSectionsEquiv _ (j.app _ (coord (a i) c))) := by
      rw [← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
      exact congrArg (fun u => structureModuleStalkEquiv x (stalkLinear j x u))
        (stalkEquiv_germ hM c hc (V := ⊤) trivial (a i))
    rw [e] at hu
    rw [secOfTwist_f]
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
  refine hle (Submodule.mem_top (x := (stalkEquiv J hM c hc).symm (J.presheaf.germ U x hx t))) ?_
  simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    stalkLinear_germ, structureModuleStalkEquiv_germ, ht, map_one, isUnit_one]

/- English proof (translation)
Rewrite using `[← isGloballyGenerated_iff_of_iso (unitTwistIso M)]`. Use `⟨fun h => ?_, fun h => IsGloballyGenerated.twist ?_ h⟩` and prove the remaining obligations. Take `⟨n, a, ha⟩` from `isGloballyGenerated_iff_spanStalks.1 h`. Conclude with `⟨n, fun i => secOfTwist (𝟙 _) (a i), top_le_iff.1 fun x _ => Opens.mem_iSup.2 (exists_mem_nonzeroLocus_secOfTwist hM (𝟙 _) ha (U := ⊤) trivial ((structureModuleSectionsEquiv ⊤).symm 1) rfl)⟩`. Use `SpanStalks.isGloballyGenerated (s := fun _ : Unit => (structureModuleSectionsEquiv ⊤).symm 1) fun x => top_le_iff.1 fun t _ => ?_` and prove the remaining obligations.

Take `⟨V, hx, t, rfl⟩` from `(structureModule X).presheaf.exists_germ_eq t`. Rewrite using `[← germ_smul_germ_one]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)`.
-/
theorem isGloballyGenerated_toMod_iff (hM : M.IsLB) :
    IsGloballyGenerated (toMod M) ↔ IsGenerated M := by
  rw [← isGloballyGenerated_iff_of_iso (unitTwistIso M)]
  refine ⟨fun h => ?_, fun h => IsGloballyGenerated.twist ?_ h⟩
  · obtain ⟨n, a, ha⟩ := isGloballyGenerated_iff_spanStalks.1 h
    exact ⟨n, fun i => secOfTwist (𝟙 _) (a i), top_le_iff.1 fun x _ => Opens.mem_iSup.2
      (exists_mem_nonzeroLocus_secOfTwist hM (𝟙 _) ha (U := ⊤) trivial
        ((structureModuleSectionsEquiv ⊤).symm 1) rfl)⟩
  · refine SpanStalks.isGloballyGenerated
      (s := fun _ : Unit => (structureModuleSectionsEquiv ⊤).symm 1) fun x => top_le_iff.1 fun t _ => ?_
    obtain ⟨V, hx, t, rfl⟩ := (structureModule X).presheaf.exists_germ_eq t
    rw [← germ_smul_germ_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)

def QCoh.toSubscheme (I : X.IdealSheafData) : structureModule X ⟶
    (Scheme.Modules.pushforward I.subschemeι).obj (structureModule I.subscheme) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

def QCoh.idealModule (I : X.IdealSheafData) : X.Modules := kernel (toSubscheme I)

def QCoh.idealModuleι (I : X.IdealSheafData) : idealModule I ⟶ structureModule X :=
  kernel.ι (toSubscheme I)

instance QCoh.mono_idealModuleι (I : X.IdealSheafData) : Mono (idealModuleι I) :=
  inferInstanceAs (Mono (kernel.ι _))

instance QCoh.isQuasicoherent_idealModule (I : X.IdealSheafData) : (idealModule I).IsQuasicoherent :=
  inferInstanceAs (kernel (toSubscheme I)).IsQuasicoherent

instance QCoh.isFiniteQC_idealModule [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    IsFiniteQC (idealModule I) := .of_mono (idealModuleι I)

/- English proof (translation)
The claim follows from `(exact_kernel_ι_app (toSubscheme I) V f).symm`.
-/
theorem QCoh.exists_idealModuleι_app_eq_iff (I : X.IdealSheafData) (V : X.Opens) (f : Γ(X, V)) :
    (∃ t, structureModuleSectionsEquiv V ((idealModuleι I).app V t) = f) ↔
      I.subschemeι.app V f = 0 :=
  (exact_kernel_ι_app (toSubscheme I) V f).symm

/- English proof (translation)
Rewrite using `[exists_idealModuleι_app_eq_iff, ← I.ker_subschemeι_app V]`. Both sides reduce to the same expression.
-/
theorem QCoh.exists_idealModuleι_app_eq_iff_mem (I : X.IdealSheafData) (V : X.affineOpens)
    (f : Γ(X, V)) :
    (∃ t, structureModuleSectionsEquiv V.1 ((idealModuleι I).app V t) = f) ↔ f ∈ I.ideal V := by
  rw [exists_idealModuleι_app_eq_iff, ← I.ker_subschemeι_app V]
  rfl

/- English proof (translation)
Introduce `h` and use `by obtain ⟨z, rfl⟩ := I.range_subschemeι.ge h have hz := (Scheme.preimage_basicOpen I.subschemeι _).le hx rw [(exists_idealModuleι_app_eq_iff I V _).1 ⟨t, rfl⟩, Scheme.basicOpen_zero] at hz exact hz`.
-/
theorem QCoh.notMem_support_of_mem_basicOpen (I : X.IdealSheafData) {V : X.Opens}
    (t : Γ(idealModule I, V)) {x : X}
    (hx : x ∈ X.basicOpen (structureModuleSectionsEquiv V ((idealModuleι I).app V t))) :
    x ∉ I.support := fun h => by
  obtain ⟨z, rfl⟩ := I.range_subschemeι.ge h
  have hz := (Scheme.preimage_basicOpen I.subschemeι _).le hx
  rw [(exists_idealModuleι_app_eq_iff I V _).1 ⟨t, rfl⟩, Scheme.basicOpen_zero] at hz
  exact hz

/- English proof (translation)
Rewrite using `[exists_idealModuleι_app_eq_iff]`. Establish `e : I.subschemeι ⁻¹ᵁ V = ⊥` using `eq_bot_iff.2 fun z hz => (hV _ hz (I.range_subschemeι.le ⟨z, rfl⟩)).elim`. Establish `: Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)`. Rewrite using `[e]`. Use `infer_instance`.

Conclude with `Subsingleton.elim _ _`.
-/
theorem QCoh.exists_idealModuleι_app_eq_one (I : X.IdealSheafData) {V : X.Opens}
    (hV : ∀ x ∈ V, x ∉ I.support) :
    ∃ t, structureModuleSectionsEquiv V ((idealModuleι I).app V t) = 1 := by
  rw [exists_idealModuleι_app_eq_iff]
  have e : I.subschemeι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun z hz => (hV _ hz (I.range_subschemeι.le ⟨z, rfl⟩)).elim
  have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) := by
    rw [e]
    infer_instance
  exact Subsingleton.elim _ _

end Converse

/- English proof (translation)
The claim follows from `(isGloballyGenerated_toMod_iff (ProjSpace.O1_isLB ℚ 2)).2 (isGenerated_O1 ℚ 2)`.
-/
example : IsGloballyGenerated (toMod (ProjSpace.O1 ℚ 2)) :=
  (isGloballyGenerated_toMod_iff (ProjSpace.O1_isLB ℚ 2)).2 (isGenerated_O1 ℚ 2)

/- English proof (translation)
Introduce `h` and use `not_isFiniteQC_tilde_rat h.isFiniteQC`.
-/
example : ¬ IsGloballyGenerated (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ)) :=
  fun h => not_isFiniteQC_tilde_rat h.isFiniteQC

end GlobalTheory
