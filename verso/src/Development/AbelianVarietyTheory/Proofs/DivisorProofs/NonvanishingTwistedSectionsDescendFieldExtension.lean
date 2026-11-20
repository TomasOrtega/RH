import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_eq gs_mul gs_pull gs_res gs_compat mem_pull chartPullOut chartPullUnpull)

/- English proof (translation)
Set `V` to `Submodule.span k (Set.range v)`. Use `haveI : Module.Finite k V := FiniteDimensional.span_of_finite k (Set.finite_range v)`. Set `bV` to `Module.finBasis k V`. Establish `hv' : ∀ j, v j ∈ V` using `fun j => Submodule.subset_span ⟨j, rfl⟩`. Establish `hli : LinearIndependent k (fun l => (bV l : K))` using `bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)`.

Take `⟨c, hc⟩ : ∃ c : Fin (Module.finrank k V) → Fin a → k, ∀ j, v j = ∑ l, c l j • (bV l : K)` from `⟨fun l j => bV.repr ⟨v j, hv' j⟩ l, fun j => by`. Use `congrArg Subtype.val (bV.sum_repr ⟨v j, hv' j⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `using this.symm⟩`. Use `⟨_, fun l => (bV l : K), c, fun l => ?_, fun j => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Establish `hp` using `congrFun hv p`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, hc, Finset.mul_sum] at hp`. Rewrite `hp` using `[Finset.sum_comm]`. Establish `: ∑ l, (∑ j, D p j * c l j) • (bV l : K) = 0`.

Rewrite using `[← hp]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Fintype.linearIndependent_iff.1 hli _ this l`. Rewrite using `[hc j]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`.
-/
theorem ker_descend {k K : Type} [Field k] [Field K] [Algebra k K] {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) k) (v : Fin a → K) (hv : (D.map (algebraMap k K)).mulVec v = 0) :
    ∃ (r : ℕ) (e : Fin r → K) (u : Fin r → Fin a → k), (∀ l, D.mulVec (u l) = 0) ∧
      ∀ j, v j = ∑ l, e l * algebraMap k K (u l j) := by
  classical
  let V := Submodule.span k (Set.range v)
  haveI : Module.Finite k V := FiniteDimensional.span_of_finite k (Set.finite_range v)
  let bV := Module.finBasis k V
  have hv' : ∀ j, v j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hli : LinearIndependent k (fun l => (bV l : K)) :=
    bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank k V) → Fin a → k, ∀ j, v j = ∑ l, c l j • (bV l : K) :=
    ⟨fun l j => bV.repr ⟨v j, hv' j⟩ l, fun j => by
      have := congrArg Subtype.val (bV.sum_repr ⟨v j, hv' j⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm⟩
  refine ⟨_, fun l => (bV l : K), c, fun l => ?_, fun j => ?_⟩
  · funext p
    have hp := congrFun hv p
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, hc, Finset.mul_sum] at hp
    rw [Finset.sum_comm] at hp
    have : ∑ l, (∑ j, D p j * c l j) • (bV l : K) = 0 := by
      rw [← hp]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    exact Fintype.linearIndependent_iff.1 hli _ this l
  · rw [hc j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, mul_comm]

/- English proof (translation)
Establish `key : ∀ {j : N.ι} (hj : r z ∈ N.U j), IsUnit (gs r z _ (s.f j)) ↔ r z ∈ X.basicOpen (s.f j)`. Introduce `j hj`. Rewrite using `[gs_eq r z _ hj]`. Use `((Z.mem_basicOpen ((r.app _).hom (s.f j)) z hj).symm).trans ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.preimage_basicOpen]`.

Both sides reduce to the same expression. Rewrite using `[key hj]`. Use `⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨j, h⟩⟩` and prove the remaining obligations. Take `⟨j', hj'⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Establish `hm : r z ∈ N.U j'` using `X.basicOpen_le _ hj'`.

Rewrite using `[← key hj, gs_compat s r z hj hm]`. Conclude with `(Units.isUnit _).mul ((key hm).2 hj')`.
-/
theorem mem_nonzeroLocus_iff_isUnit {X Z : Scheme.{0}} {N : LB X} (s : LB.Sec N) (r : Z ⟶ X) (z : Z) {j : N.ι}
    (hj : r z ∈ N.U j) : r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f j)) := by
  have key : ∀ {j : N.ι} (hj : r z ∈ N.U j), IsUnit (gs r z _ (s.f j)) ↔ r z ∈ X.basicOpen (s.f j) := by
    intro j hj
    rw [gs_eq r z _ hj]
    refine ((Z.mem_basicOpen ((r.app _).hom (s.f j)) z hj).symm).trans ?_
    rw [← Scheme.Hom.preimage_basicOpen]
    rfl
  rw [key hj]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨j, h⟩⟩
  obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hm : r z ∈ N.U j' := X.basicOpen_le _ hj'
  rw [← key hj, gs_compat s r z hj hm]
  exact (Units.isUnit _).mul ((key hm).2 hj')

/- English proof (translation)
Unfold `twistLB`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Use `show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left`.

Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Use `show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `[translPt, comp_lift_assoc]`.
-/
theorem linComb_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

/- English proof (translation)
Introduce `S P k _ K _ _ t c hK y`. Set `ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)` to `Spec.map (CommRingCat.ofHom (algebraMap k K))`. Set `T` to `Over.mk t`. Set `h : Over.mk (ιK ≫ t) ⟶ T` to `Over.homMk ιK rfl`. Rewrite `hK` using `[← linComb_whisker P.A P.L 2 h c]`.

Set `M : LB (T ⊗ P.A).left` to `twistLB P.A P.L 2 c`. Establish `hM : M.IsLB` using `LB.isLB_linComb P.isLB _ _`. Set `f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of k)` to `(fst T P.A).left`. Set `π` to `(h ▷ P.A).left`. Set `f' : (Over.mk (ιK ≫ t) ⊗ P.A).left ⟶ Spec (CommRingCat.of K)` to `(fst (Over.mk (ιK ≫ t)) P.A).left`.

Establish `H : IsPullback π f' f ιK` using `GlobalTheory.AbLaw.SecBC.isPullback_whisker P.A h`. Establish `hpb` using `GlobalTheory.AbLaw.SecBC.isPullback_snd P.A T`. Use `haveI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb P.isAb.proper`. Use `haveI : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hpb P.isAb.smooth`. Use `haveI : Flat f := inferInstance`.

Take `⟨Q⟩` from `GlobalTheory.ProperFinite.nonempty_perf_of_isProper f hM`. Use `haveI hι : Surjective ιK := ⟨fun p => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩`. Establish `hπ : Surjective π` using `MorphismProperty.of_isPullback (P := @Surjective) H.flip hι`. Take `⟨z, rfl⟩` from `hπ.surj y`. Assume the negation of the conclusion as `hy`.

Use `push Not at hy`. Take `⟨sK, hsK⟩` from `hK z`. Take `⟨i, hi⟩` from `GlobalTheory.SecTwist.perf_cover Q (π z)`. Establish `m₁ : π z ∈ M.U (Q.ch i)` using `Q.le i hi`. Establish `m₂ : z ∈ (LB.LinComb P.L (K` using `Fin 2) (fun k => π ≫ ![(snd T P.A).left, (translPt P.A c).left] k) ![((2 : ℕ) : ℤ) - 1, 1]).U (Q.ch i) := Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k`.

Set `sb : LB.Sec (M.pull π)` to `GlobalTheory.SecTwist.pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK`. Take `⟨E, hE⟩` from `GlobalTheory.SecTwist.perf_sec Q (algebraMap k K) H`. Establish `hu1 : IsUnit (gs (𝟙 _) z ((M.pull π).U (fun _ => Q.ch i)) (sb.f (fun _ => Q.ch i)))`. Establish `a₁` using `GlobalTheory.SecTwist.gs_pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK (𝟙 _) z (fun _ => Q.ch i) (mem_pull.2 m₁)`. Rewrite `a₁` using `[Category.id_comp]`.

Use `a₁ ▸ (mem_nonzeroLocus_iff_isUnit sK (𝟙 _) z m₂).1 hsK` and prove the remaining obligations. Take `⟨r, e, u, hu, hvu⟩` from `ker_descend Q.D₀ (E.symm sb).1 (E.symm sb).2`. Establish `h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id k)))`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Conclude with `IsPullback.of_horiz_isIso ⟨by simp⟩`.

Take `⟨E₀, hE₀⟩` from `GlobalTheory.SecTwist.perf_sec Q (RingHom.id k) h₀`. Establish `ker : ∀ l, (Q.D₀.map (RingHom.id k)).mulVec (u l) = 0` using `fun l => by`. Rewrite using `[show Q.D₀.map (RingHom.id k) = Q.D₀ from rfl]`. Conclude with `hu l`. Set `s : Fin r → LB.Sec M` to `fun l => GlobalTheory.SecTwist.pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩)`.

Establish `hG : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) = ∑ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z (u l j) * gs π z (Q.W i) (Q.u j i)` using `fun l => by`. Establish `a₃` using `GlobalTheory.SecTwist.gs_pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩) π z (Q.ch i) m₁`. Establish `a₄` using `hE₀ ⟨u l, ker l⟩ i _ π z hi`. Rewrite `a₃`, `a₄` using `[Category.comp_id]`. Conclude with `a₃.trans a₄`.

Establish `hnu : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _` using `fun l => by`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← mem_nonzeroLocus_iff_isUnit (s l) π z m₁]`. Conclude with `hy (s l)`. Establish `e1 : ∀ a : k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (algebraMap k K a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z a` using `fun a => by`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp]`.

Use `congr 1`. Conclude with `H.w.symm`. Establish `hsb` using `hE (E.symm sb) i _ (𝟙 _) z hi`. Rewrite `hsb` using `[Equiv.apply_symm_apply]`. Simplify using `only [Category.id_comp, hvu, ← GlobalTheory.SecTwist.cstHom_apply, map_sum, map_mul] at hsb`.

Simplify using `only [GlobalTheory.SecTwist.cstHom_apply, e1] at hsb`. Use `(IsLocalRing.mem_maximalIdeal _).1 ?_ hu1` and prove the remaining obligations. Rewrite using `[hsb]`. Establish `key : ∀ l, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (e l) * gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _` using `fun l => Ideal.mul_mem_left _ _ (hnu l)`. Use `Ideal.sum_mem (IsLocalRing.maximalIdeal _) fun l (_ : l ∈ Finset.univ) => key l` as an intermediate fact.

Simplify using `only [hG, Finset.mul_sum] at this`. Rewrite `this` using `[Finset.sum_comm]`. Use `this using 2 with j` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sec_of_baseChange : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A), (∀ z : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 ((Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) rfl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t) ≫ c)), z ∈ nonzeroLocus s) → ∀ y : (Over.mk t ⊗ P.A).left, ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ K _ _ t c hK y
  classical
  let ιK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Over.mk t
  let h : Over.mk (ιK ≫ t) ⟶ T := Over.homMk ιK rfl
  rw [← linComb_whisker P.A P.L 2 h c] at hK
  let M : LB (T ⊗ P.A).left := twistLB P.A P.L 2 c
  have hM : M.IsLB := LB.isLB_linComb P.isLB _ _
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of k) := (fst T P.A).left
  let π := (h ▷ P.A).left
  let f' : (Over.mk (ιK ≫ t) ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk (ιK ≫ t)) P.A).left
  have H : IsPullback π f' f ιK := GlobalTheory.AbLaw.SecBC.isPullback_whisker P.A h
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_snd P.A T
  haveI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb P.isAb.proper
  haveI : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hpb P.isAb.smooth
  haveI : Flat f := inferInstance
  obtain ⟨Q⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f hM
  haveI hι : Surjective ιK := ⟨fun p => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have hπ : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip hι
  obtain ⟨z, rfl⟩ := hπ.surj y
  by_contra hy
  push Not at hy
  obtain ⟨sK, hsK⟩ := hK z
  obtain ⟨i, hi⟩ := GlobalTheory.SecTwist.perf_cover Q (π z)
  have m₁ : π z ∈ M.U (Q.ch i) := Q.le i hi
  have m₂ : z ∈ (LB.LinComb P.L (K := Fin 2) (fun k => π ≫ ![(snd T P.A).left, (translPt P.A c).left] k)
      ![((2 : ℕ) : ℤ) - 1, 1]).U (Q.ch i) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₁ k
  let sb : LB.Sec (M.pull π) := GlobalTheory.SecTwist.pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK
  obtain ⟨E, hE⟩ := GlobalTheory.SecTwist.perf_sec Q (algebraMap k K) H
  have hu1 : IsUnit (gs (𝟙 _) z ((M.pull π).U (fun _ => Q.ch i)) (sb.f (fun _ => Q.ch i))) := by
    have a₁ := GlobalTheory.SecTwist.gs_pullSec (chartPullOut P.L _ _ π _ fun _ => rfl) sK (𝟙 _) z (fun _ => Q.ch i)
      (mem_pull.2 m₁)
    rw [Category.id_comp] at a₁
    refine a₁ ▸ (mem_nonzeroLocus_iff_isUnit sK (𝟙 _) z m₂).1 hsK
  obtain ⟨r, e, u, hu, hvu⟩ := ker_descend Q.D₀ (E.symm sb).1 (E.symm sb).2
  have h₀ : IsPullback (𝟙 _) f f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.SecTwist.perf_sec Q (RingHom.id k) h₀
  have ker : ∀ l, (Q.D₀.map (RingHom.id k)).mulVec (u l) = 0 := fun l => by
    rw [show Q.D₀.map (RingHom.id k) = Q.D₀ from rfl]
    exact hu l
  let s : Fin r → LB.Sec M := fun l => GlobalTheory.SecTwist.pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩)
  have hG : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) =
      ∑ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z (u l j) * gs π z (Q.W i) (Q.u j i) := fun l => by
    have a₃ := GlobalTheory.SecTwist.gs_pullSec (chartPullUnpull M (𝟙 _) rfl) (E₀ ⟨u l, ker l⟩) π z (Q.ch i) m₁
    have a₄ := hE₀ ⟨u l, ker l⟩ i _ π z hi
    rw [Category.comp_id] at a₃ a₄
    exact a₃.trans a₄
  have hnu : ∀ l, gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈ IsLocalRing.maximalIdeal _ := fun l => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← mem_nonzeroLocus_iff_isUnit (s l) π z m₁]
    exact hy (s l)
  have e1 : ∀ a : k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (algebraMap k K a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst (π ≫ f) z a :=
    fun a => by
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp]
      congr 1
      exact H.w.symm
  have hsb := hE (E.symm sb) i _ (𝟙 _) z hi
  rw [Equiv.apply_symm_apply] at hsb
  simp only [Category.id_comp, hvu, ← GlobalTheory.SecTwist.cstHom_apply, map_sum, map_mul] at hsb
  simp only [GlobalTheory.SecTwist.cstHom_apply, e1] at hsb
  refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hu1
  rw [hsb]
  have key : ∀ l, ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst f' z (e l) * gs π z (M.U (Q.ch i)) ((s l).f (Q.ch i)) ∈
      IsLocalRing.maximalIdeal _ := fun l => Ideal.mul_mem_left _ _ (hnu l)
  have := Ideal.sum_mem (IsLocalRing.maximalIdeal _) fun l (_ : l ∈ Finset.univ) => key l
  simp only [hG, Finset.mul_sum] at this
  rw [Finset.sum_comm] at this
  convert this using 2 with j
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TwistDescent
