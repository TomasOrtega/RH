import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.JacProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.SuppOfTypeOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Conclude with `SupportUnique.eq_of_hasSupport L.geo L.zel N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv (IrrGL.equivOf _ _ _)) (ht.of_equiv (IrrGL.equivOf _ _ _))`.
-/
theorem supp_unique (L : Loc) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {s t : Multiset (IrrGL k)} (hs : HasSupport π s) (ht : HasSupport π t) : s = t := by
  exact SupportUnique.eq_of_hasSupport L.geo L.zel N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t
    (hs.of_equiv (IrrGL.equivOf _ _ _)) (ht.of_equiv (IrrGL.equivOf _ _ _))

/- English proof (translation)
Take `⟨μ, hμ, rfl⟩` from `hx`. Introduce `h`. Establish `h' : (IrrGL.ofChar μ (isSmoothChar_of_isUnram hμ)).nu ((0:ℝ):ℂ) = (IrrGL.ofChar μ (isSmoothChar_of_isUnram hμ)).nu ((1:ℝ):ℂ)`. Rewrite using `[Complex.ofReal_zero, Complex.ofReal_one]`. Simplify using `using h`.

Use `(IrrGL.nu_ofChar_inj μ _).1 h'` as an intermediate fact. Evaluate the numerical expressions using `at this`.
-/
theorem ne_nu_one_of_char {x : IrrGL k} (hx : x.IsUnramChar) : x ≠ x.nu 1 := by
  obtain ⟨μ, hμ, rfl⟩ := hx
  intro h
  have h' : (IrrGL.ofChar μ (isSmoothChar_of_isUnram hμ)).nu ((0:ℝ):ℂ) =
      (IrrGL.ofChar μ (isSmoothChar_of_isUnram hμ)).nu ((1:ℝ):ℂ) := by
    rw [Complex.ofReal_zero, Complex.ofReal_one]
    simpa using h
  have := (IrrGL.nu_ofChar_inj μ _).1 h'
  norm_num at this

/- English proof (translation)
Establish `c1 : ∀ i, (Δ i).carrier = {(Δ i).first}`. Introduce `i`. Use extensionality with `w`. Rewrite using `[Segment.mem_carrier, hl i]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩`. Take `rfl : a = 0` from `by omega`. Simplify using the standard rewrite rules. Introduce `hw`. Use `⟨0, by omega, ?_⟩` and prove the remaining obligations.

Simplify using `[Set.mem_singleton_iff.1 hw]`. Establish `memf : ∀ w, w ∈ ∑ i, (Δ i).ms → ∃ i, w = (Δ i).first`. Introduce `w hw`. Take `⟨i, -, hi⟩` from `Multiset.mem_sum.1 hw`. Rewrite `hi` using `[Segment.mem_ms, c1 i]`.

Conclude with `⟨i, hi⟩`. Introduce `y hy z hz heq`. Take `⟨i, rfl⟩` from `memf y hy`. Take `⟨j, rfl⟩` from `memf z hz`. Establish `hz1 : (Δ j).first ≠ ((Δ j).first).nu 1` using `ne_nu_one_of_char (hu j)`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `hz1 heq`. Apply `hn i j hij` to reduce the goal to its premises. Use `⟨⟨Segment.ofFirst (Δ j).first (Segment.isCusp_first _) 2 (by norm_num), ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `w`. Rewrite using `[Segment.mem_carrier, Segment.len_ofFirst, Segment.first_ofFirst, c1 i, c1 j, heq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩ interval_cases a`. Use `right`.

Simplify using the standard rewrite rules. Use `left`. Simplify using the standard rewrite rules. Introduce and unpack `(hw | hw)`. Use `⟨1, by norm_num, ?_⟩` and prove the remaining obligations.

Simplify using `[Set.mem_singleton_iff.1 hw]`. Use `⟨0, by norm_num, ?_⟩` and prove the remaining obligations. Simplify using `[Set.mem_singleton_iff.1 hw]`. Rewrite using `[c1 i, c1 j, Set.singleton_subset_iff, Set.mem_singleton_iff, heq]`. Conclude with `fun h => hz1 h.symm`.

Rewrite using `[c1 i, c1 j, Set.singleton_subset_iff, Set.mem_singleton_iff, heq]`. Conclude with `hz1`.
-/
private theorem unlinked_sum_ms_of_len_one_unram_not_linked {h : ℕ} (Δ : Fin h → Segment k) (hl : ∀ i, (Δ i).len = 1)
    (hu : ∀ i, (Δ i).first.IsUnramChar) (hn : ∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) :
    GlobalTheory.RoadU.Unlinked (∑ i, (Δ i).ms) := by
  have c1 : ∀ i, (Δ i).carrier = {(Δ i).first} := by
    intro i
    ext w
    rw [Segment.mem_carrier, hl i]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain rfl : a = 0 := by omega
      simp
    · intro hw
      refine ⟨0, by omega, ?_⟩
      simp [Set.mem_singleton_iff.1 hw]
  have memf : ∀ w, w ∈ ∑ i, (Δ i).ms → ∃ i, w = (Δ i).first := by
    intro w hw
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hw
    rw [Segment.mem_ms, c1 i] at hi
    exact ⟨i, hi⟩
  intro y hy z hz heq
  obtain ⟨i, rfl⟩ := memf y hy
  obtain ⟨j, rfl⟩ := memf z hz
  have hz1 : (Δ j).first ≠ ((Δ j).first).nu 1 := ne_nu_one_of_char (hu j)
  by_cases hij : i = j
  · subst hij
    exact hz1 heq
  · apply hn i j hij
    refine ⟨⟨Segment.ofFirst (Δ j).first (Segment.isCusp_first _) 2 (by norm_num), ?_⟩, ?_, ?_⟩
    · ext w
      rw [Segment.mem_carrier, Segment.len_ofFirst, Segment.first_ofFirst, c1 i, c1 j, heq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        interval_cases a
        · right
          simp
        · left
          simp
      · rintro (hw | hw)
        · refine ⟨1, by norm_num, ?_⟩
          simp [Set.mem_singleton_iff.1 hw]
        · refine ⟨0, by norm_num, ?_⟩
          simp [Set.mem_singleton_iff.1 hw]
    · rw [c1 i, c1 j, Set.singleton_subset_iff, Set.mem_singleton_iff, heq]
      exact fun h => hz1 h.symm
    · rw [c1 i, c1 j, Set.singleton_subset_iff, Set.mem_singleton_iff, heq]
      exact hz1

/- English proof (translation)
Take `⟨h, Δ, x, hd, hlink, hL, ⟨e⟩⟩` from `hGU k N V π hs hi hg`. Establish `hsq : IsSubquotient π (prodIrr x hd)` using `IsSubquotient.of_injective e.toIntertwiningMap (by`. Introduce `a b hab`. Conclude with `e.toLinearEquiv.injective hab)`. Establish `hsph` using `GlobalTheory.LocLanglands.SphFac.isSpherical_factor k h N x hd V π hsq hsp`.

Establish `key` using `fun a => GlobalTheory.SphSeg.len_eq_one_and_isUnramChar hM hC L.zel L.geo L.bz k (Δ a) (x a) (hL a) (hsph a)`. Establish `hsupp : HasSupport π (∑ a, (Δ a).ms)`. Take `⟨Z, Ψ, -, hΨ, -⟩` from `L.zel k`. Conclude with `SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hL a).hasSupport) hi hsq`. Rewrite using `[supp_unique L hS hsupp]`.

Conclude with `unlinked_sum_ms_of_len_one_unram_not_linked Δ (fun a => (key a).1) (fun a => (key a).2) hlink`.
-/
theorem unlinked_of_spherical [CharZero k] (L : Loc) (hGU : GlobalTheory.Published.GenericUnlinkedGL)
    (hM : GlobalTheory.Published.LanglandsMultisegments) (hC : GlobalTheory.Published.StandardCosocleGL)
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hg : IsGeneric π) (hsp : IsSpherical π) {s : Multiset (IrrGL k)}
    (hS : HasSupport π s) : GlobalTheory.RoadU.Unlinked s := by
  obtain ⟨h, Δ, x, hd, hlink, hL, ⟨e⟩⟩ := hGU k N V π hs hi hg
  have hsq : IsSubquotient π (prodIrr x hd) :=
    IsSubquotient.of_injective e.toIntertwiningMap (by
      intro a b hab
      exact e.toLinearEquiv.injective hab)
  have hsph := GlobalTheory.LocLanglands.SphFac.isSpherical_factor k h N x hd V π hsq hsp
  have key := fun a => GlobalTheory.SphSeg.len_eq_one_and_isUnramChar hM hC L.zel L.geo L.bz k (Δ a) (x a) (hL a) (hsph a)
  have hsupp : HasSupport π (∑ a, (Δ a).ms) := by
    obtain ⟨Z, Ψ, -, hΨ, -⟩ := L.zel k
    exact SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hL a).hasSupport) hi hsq
  rw [supp_unique L hS hsupp]
  exact unlinked_sum_ms_of_len_one_unram_not_linked Δ (fun a => (key a).1) (fun a => (key a).2) hlink

/- English proof (translation)
Establish `hη' : IsSmoothChar η⁻¹` using `hη.inv`. Establish `hsph` using `(UpperTheory.TNZ.step_detVec k N V π η).2 hv`. Establish `hS'` using `hS.tw η⁻¹ hη'`. Establish `hg'` using `(isGeneric_twist_iff (π := π) η⁻¹).2 hg`. Establish `hU` using `unlinked_of_spherical L hGU hM hC hS'.isSmooth hS'.isIrreducible hg' hsph hS'`.

Introduce `y hy z hz heq`. Apply `hU (y.tw η⁻¹ hη') (Multiset.mem_map_of_mem _ hy) (z.tw η⁻¹ hη') (Multiset.mem_map_of_mem _ hz)` to reduce the goal to its premises. Rewrite using `[heq, IrrGL.tw_nu]`.
-/
theorem unlinked_of_detVec [CharZero k] (L : Loc) (hGU : GlobalTheory.Published.GenericUnlinkedGL)
    (hM : GlobalTheory.Published.LanglandsMultisegments) (hC : GlobalTheory.Published.StandardCosocleGL)
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hg : IsGeneric π) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) (hv : UpperTheory.TNZ.HasDetVec π η) {s : Multiset (IrrGL k)}
    (hS : HasSupport π s) : GlobalTheory.RoadU.Unlinked s := by
  have hη' : IsSmoothChar η⁻¹ := hη.inv
  have hsph := (UpperTheory.TNZ.step_detVec k N V π η).2 hv
  have hS' := hS.tw η⁻¹ hη'
  have hg' := (isGeneric_twist_iff (π := π) η⁻¹).2 hg
  have hU := unlinked_of_spherical L hGU hM hC hS'.isSmooth hS'.isIrreducible hg' hsph hS'
  intro y hy z hz heq
  apply hU (y.tw η⁻¹ hη') (Multiset.mem_map_of_mem _ hy) (z.tw η⁻¹ hη') (Multiset.mem_map_of_mem _ hz)
  rw [heq, IrrGL.tw_nu]

/- English proof (translation)
Take `⟨η, hη, X, _, _, σ, hsm, hirr, hdv, ⟨e⟩⟩` from `h`. Establish `hgM : IsGeneric (multiProd (stdBlocks d hd) σ)` using `(isGeneric_congr e).1 hg`. Establish `hgσ` using `(hP c N d hd X σ hsm).1 hgM`. Establish `hcs` using `fun a => UpperTheory.TNZ.stepL_cuspSupp L k (d a) (X a) (σ a) (hsm a) (hirr a) (η a) (hη a).1 (hdv a)`. Use `choose μ hμ hcsp using hcs`.

Set `t : Fin c → Multiset (IrrGL k)` to `fun a => Multiset.map (fun j => IrrGL.ofChar (μ a j) (hμ a j).1) Finset.univ.val`. Establish `ht : ∀ a, HasSupport (σ a) (t a)` using `fun a => hasSupport_of_isCuspSupport (hcsp a)`. Establish `hSM : HasSupport (multiProd (stdBlocks d hd) σ) s` using `hS.of_equiv e`. Establish `hsum` using `SupportRing.hasSupport_multiProd L.zel hd σ hsm hirr ht hSM.isIrreducible`. Rewrite using `[supp_unique L hS (hsum.of_equiv e.symm)]`.

Introduce `y hy z hz heq`. Take `⟨a, -, hya⟩` from `Multiset.mem_sum.1 hy`. Take `⟨b, -, hzb⟩` from `Multiset.mem_sum.1 hz`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Conclude with `unlinked_of_detVec L hGU hM hC (hgσ a) (hη a).1 (hdv a) (ht a) y hya z hzb heq`. Apply `hab` to reduce the goal to its premises. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hya`. Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hzb`. Simplify using `only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at heq`.

Apply `hθ` to reduce the goal to its premises. Use `(lifts k).2.2 (η b) _ _ ?_ (hη b).2` and prove the remaining obligations. Introduce `u`. Establish `hv : valuation k ↑(unitIncl k u) = 1` using `valuation_eq_one_iff.2 ⟨u, rfl⟩`. Rewrite using `[← (hη a).2 u, ← (hμ a i).2 _ hv, ← (hμ b j).2 _ hv, heq, MonoidHom.mul_apply, isUnram_absPow k 1 _ hv, mul_one]`.
-/
theorem unlinked_of_tameSphProd [CharZero k] (L : Loc) (hGU : GlobalTheory.Published.GenericUnlinkedGL)
    (hM : GlobalTheory.Published.LanglandsMultisegments) (hC : GlobalTheory.Published.StandardCosocleGL) (hP : GlobalTheory.BZMir.Leib.GenericProdIff k)
    {N c : ℕ} {d : Fin c → ℕ} {hd : ∑ a, d a = N} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hg : IsGeneric π) {θ : Fin c → 𝓀[k]ˣ →* ℂˣ} (hθ : Function.Injective θ)
    (h : IsTameSphProd π d hd θ) {s : Multiset (IrrGL k)} (hS : HasSupport π s) : GlobalTheory.RoadU.Unlinked s := by
  obtain ⟨η, hη, X, _, _, σ, hsm, hirr, hdv, ⟨e⟩⟩ := h
  have hgM : IsGeneric (multiProd (stdBlocks d hd) σ) := (isGeneric_congr e).1 hg
  have hgσ := (hP c N d hd X σ hsm).1 hgM
  have hcs := fun a => UpperTheory.TNZ.stepL_cuspSupp L k (d a) (X a) (σ a) (hsm a) (hirr a) (η a) (hη a).1 (hdv a)
  choose μ hμ hcsp using hcs
  let t : Fin c → Multiset (IrrGL k) := fun a =>
    Multiset.map (fun j => IrrGL.ofChar (μ a j) (hμ a j).1) Finset.univ.val
  have ht : ∀ a, HasSupport (σ a) (t a) := fun a => hasSupport_of_isCuspSupport (hcsp a)
  have hSM : HasSupport (multiProd (stdBlocks d hd) σ) s := hS.of_equiv e
  have hsum := SupportRing.hasSupport_multiProd L.zel hd σ hsm hirr ht hSM.isIrreducible
  rw [supp_unique L hS (hsum.of_equiv e.symm)]
  intro y hy z hz heq
  obtain ⟨a, -, hya⟩ := Multiset.mem_sum.1 hy
  obtain ⟨b, -, hzb⟩ := Multiset.mem_sum.1 hz
  by_cases hab : a = b
  · subst hab
    exact unlinked_of_detVec L hGU hM hC (hgσ a) (hη a).1 (hdv a) (ht a) y hya z hzb heq
  · apply hab
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hya
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hzb
    simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at heq
    apply hθ
    refine (lifts k).2.2 (η b) _ _ ?_ (hη b).2
    intro u
    have hv : valuation k ↑(unitIncl k u) = 1 := valuation_eq_one_iff.2 ⟨u, rfl⟩
    rw [← (hη a).2 u, ← (hμ a i).2 _ hv, ← (hμ b j).2 _ hv, heq, MonoidHom.mul_apply,
      isUnram_absPow k 1 _ hv, mul_one]

end UpperTheory.Gal.TypesAndIwahori
