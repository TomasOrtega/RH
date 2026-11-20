import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj K hK jN hjN`. Use `haveI := hj`. Establish `hinj : Function.Injective (algebraMap R C)` using `hv.hom_inj`. Establish `hpow : ∀ x, (pt x) ^ p = 1` using `fun x => (hpt.range _).2 ⟨x, rfl⟩`. Establish `hpow' : ∀ x, (pt' x) ^ p = 1` using `fun x => (hpt'.range _).2 ⟨x, rfl⟩`.

Use `choose φ hφ hφu using fun x => T.univ R (pt x) (hpow x)`. Use `choose φ' hφ' hφu' using fun x => T'.univ R (pt' x) (hpow' x)`. Establish `h0' : pt' 0 = 1`. Establish `h` using `hpt'.add 0 0`. Rewrite `h` using `[add_zero]`.

Simplify using `using h.symm`. Establish `hyp : (T.y ≫ j) ^ p = 1`. Rewrite using `[← MonObj.pow_comp, T.y_p, MonObj.one_comp]`. Take `⟨ψ, hψ, -⟩` from `T'.univ T.A (T.y ≫ j) hyp`. Establish `hcomp : ∀ x, (φ x).comp ψ = φ' (jN x)`.

Introduce `x`. Apply `hφu'` to reduce the goal to its premises. Rewrite using `[← Chart.spMap_comp ψ (φ x), Category.assoc, hψ, ← Category.assoc, hφ x, hjN]`. Establish `hker : ∀ x, jN x = 0 ↔ pt x ≫ j = 1`. Introduce `x`.

Rewrite using `[← hjN, ← h0']`. Conclude with `hpt'.inj.eq_iff.symm`. Establish `hfac : ∀ x, pt x ≫ j = 1 ↔ ∀ a ∈ vanIdeal T pt (K : Set N), φ x a = 0`. Introduce `x`. Rewrite using `[hK R (pt x)]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨χ, hχ⟩ a ha`. Establish `e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = φ x`. Apply `hφu` to reduce the goal to its premises. Rewrite using `[← Chart.spMap_comp, Category.assoc]`.

Conclude with `hχ`. Rewrite using `[← e, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]`. Introduce `h`. Use `⟨Ideal.Quotient.liftₐ _ (φ x) h, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, Chart.spMap_comp, Ideal.Quotient.liftₐ_comp]`.

Conclude with `hφ x`. Establish `hK1 : jN.ker = K`. Use extensionality with `x`. Rewrite using `[AddMonoidHom.mem_ker, hker, hfac]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Assume the negation of the conclusion as `hx`. Establish `hne : ∀ k ∈ K, ∃ c : T.A, φ k c ≠ φ x c`. Introduce `k hk`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Establish `e1 : φ k = φ x` using `AlgHom.ext hall`. Establish `e2 : pt k = pt x` using `by rw [← hφ k, ← hφ x, e1]`. Conclude with `hx (hpt.inj e2 ▸ hk)`. Use `choose! c hc using hne`.

Set `a : T.A` to `∏ k ∈ Finset.univ.filter (· ∈ K), (c k - algebraMap R T.A (φ k (c k)))`. Establish `ha : a ∈ vanIdeal T pt (K : Set N)`. Rewrite using `[PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]`. Introduce `k hk`. Simplify using `only [a, map_prod]`.

Apply `Finset.prod_eq_zero (i := k)` to reduce the goal to its premises. Simplify using `using hk`. Simplify using the standard rewrite rules. Establish `h1` using `h a ha`. Use `apply_fun algebraMap R C at h1`.

Simplify using `only [a, map_prod, map_sub, AlgHom.commutes, map_zero] at h1`. Rewrite `h1` using `[Finset.prod_eq_zero_iff]`. Take `⟨k, hk, hk0⟩` from `h1`. Rewrite `hk0` using `[sub_eq_zero]`. Conclude with `hc k (by simpa using hk) (hinj (by simpa using hk0)).symm`.

Introduce `hx a ha`. Conclude with `(PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ _ a).1 ha x hx`. Use `⟨hK1, ?_⟩` and prove the remaining obligations. Introduce `g hg hgK`. Rewrite `hg` using `[PositivityTheory.HtPt.Rf.mem_torsFun T hφ]`.

Take `⟨a, rfl⟩` from `hg`. Establish `haI : a ∈ vanIdeal T pt (K : Set N)`. Rewrite using `[PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]`. Introduce `k hk`. Establish `h3` using `hgK k (by rw [hK1]; exact hk)`.

Conclude with `hinj (by rw [map_zero]; exact h3)`. Take `⟨J, hJ⟩ : ∃ J : Ideal T.A, J = Ideal.map ψ (RingHom.ker (φ' 0))` from `⟨_, rfl⟩`. Establish `hIJ : vanIdeal T pt (K : Set N) ≤ J`. Establish `hzp : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ^ p = 1`. Rewrite using `[← MonObj.comp_pow, T.y_p, MonObj.comp_one]`.

Establish `hqψ : (Ideal.Quotient.mkₐ R J).comp ψ = (Algebra.ofId R (T.A ⧸ J)).comp (φ' 0)`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `b`. Establish `hb : b - algebraMap R T'.A (φ' 0 b) ∈ RingHom.ker (φ' 0)`. Simplify using `[RingHom.mem_ker]`.

Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← AlgHom.commutes ψ, ← map_sub, hJ]`. Conclude with `Ideal.mem_map_of_mem _ hb`. Establish `hz1 : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, Chart.spMap_comp]`.

Use `_ = spMap ((Algebra.ofId R (T.A ⧸ J)).comp (φ' 0)) ≫ T'.y := by rw [hqψ]`. Use `_ = spMap (Algebra.ofId R (T.A ⧸ J)) ≫ pt' 0 := by`. Rewrite using `[← Chart.spMap_comp, Category.assoc, hφ' 0]`. Use `_ = 1 := by rw [h0', MonObj.comp_one]`. Take `⟨χ, hχ⟩` from `(hK (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y)).1 hz1`.

Take `⟨w, -, hu⟩` from `T.univ (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) hzp`. Establish `e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = Ideal.Quotient.mkₐ R J`. Rewrite using `[hu _ rfl]`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← Chart.spMap_comp, Category.assoc]`.

Conclude with `hχ`. Introduce `b hb`. Establish `h2` using `AlgHom.congr_fun e b`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2`. Rewrite `h2` using `[Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h2.symm`. Establish `ha : a ∈ J` using `hIJ haI`. Rewrite `ha` using `[hJ]`. Express the relevant statement in the definitionally equal form `a ∈ Submodule.span T.A (⇑ψ '' (RingHom.ker (φ' 0) : Set T'.A)) at ha`. Use `clear hgK haI hIJ hJ`.

It suffices to establish `H : ∀ c : T.A, (fun x => algebraMap R C (φ x (c * a))) ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt by`. Establish `H1` using `H 1`. Rewrite `H1` using `[_root_.one_mul]`. Then use the resulting hypothesis. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, rfl⟩` from `hx`. Introduce `c`. Establish `e : (fun y => algebraMap R C (φ y (c * ψ b))) = (fun y => algebraMap R C (φ y (ψ b))) * (fun y => algebraMap R C (φ y c))`. Use function extensionality and compare the values at `y`. Simplify using `[map_mul, mul_comm]`.

Rewrite using `[e]`. Apply `Submodule.mul_mem_mul` to reduce the goal to its premises. Rewrite using `[Submodule.mem_map]`. Use `⟨fun y => algebraMap R C (φ' y b), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]`.

Use `⟨(PositivityTheory.HtPt.Rf.mem_torsFun T' hφ' _).2 ⟨b, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[SetLike.mem_coe, RingHom.mem_ker]`. Simplify using `only [hb, map_zero]`. Use function extensionality and compare the values at `y`. Rewrite using `[LinearMap.funLeft_apply, ← hcomp y, AlgHom.comp_apply]`.

Conclude with `(PositivityTheory.HtPt.Rf.mem_torsFun T hφ _).2 ⟨c, rfl⟩`. Consider the case `zero`. Introduce `c`. Simplify using `only [mul_zero, map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Introduce `c`. Establish `h4` using `Submodule.add_mem _ (hx c) (hy c)`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using `[mul_add]`. Consider the case `smul r x _ hx`. Introduce `c`. Use `hx (c * r) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Rewrite using `[smul_eq_mul, _root_.mul_assoc]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ hv _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj K hK jN hjN
  haveI := hj
  classical
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hpow : ∀ x, (pt x) ^ p = 1 := fun x => (hpt.range _).2 ⟨x, rfl⟩
  have hpow' : ∀ x, (pt' x) ^ p = 1 := fun x => (hpt'.range _).2 ⟨x, rfl⟩
  choose φ hφ hφu using fun x => T.univ R (pt x) (hpow x)
  choose φ' hφ' hφu' using fun x => T'.univ R (pt' x) (hpow' x)
  have h0' : pt' 0 = 1 := by
    have h := hpt'.add 0 0
    rw [add_zero] at h
    simpa using h.symm
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  have hcomp : ∀ x, (φ x).comp ψ = φ' (jN x) := by
    intro x
    apply hφu'
    rw [← Chart.spMap_comp ψ (φ x), Category.assoc, hψ, ← Category.assoc, hφ x, hjN]
  have hker : ∀ x, jN x = 0 ↔ pt x ≫ j = 1 := by
    intro x
    rw [← hjN, ← h0']
    exact hpt'.inj.eq_iff.symm
  have hfac : ∀ x, pt x ≫ j = 1 ↔ ∀ a ∈ vanIdeal T pt (K : Set N), φ x a = 0 := by
    intro x
    rw [hK R (pt x)]
    constructor
    · rintro ⟨χ, hχ⟩ a ha
      have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = φ x := by
        apply hφu
        rw [← Chart.spMap_comp, Category.assoc]
        exact hχ
      rw [← e, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    · intro h
      refine ⟨Ideal.Quotient.liftₐ _ (φ x) h, ?_⟩
      rw [← Category.assoc, Chart.spMap_comp, Ideal.Quotient.liftₐ_comp]
      exact hφ x
  have hK1 : jN.ker = K := by
    ext x
    rw [AddMonoidHom.mem_ker, hker, hfac]
    constructor
    · intro h
      by_contra hx
      have hne : ∀ k ∈ K, ∃ c : T.A, φ k c ≠ φ x c := by
        intro k hk
        by_contra hall
        push_neg at hall
        have e1 : φ k = φ x := AlgHom.ext hall
        have e2 : pt k = pt x := by rw [← hφ k, ← hφ x, e1]
        exact hx (hpt.inj e2 ▸ hk)
      choose! c hc using hne
      let a : T.A := ∏ k ∈ Finset.univ.filter (· ∈ K), (c k - algebraMap R T.A (φ k (c k)))
      have ha : a ∈ vanIdeal T pt (K : Set N) := by
        rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
        intro k hk
        simp only [a, map_prod]
        apply Finset.prod_eq_zero (i := k)
        · simpa using hk
        · simp
      have h1 := h a ha
      apply_fun algebraMap R C at h1
      simp only [a, map_prod, map_sub, AlgHom.commutes, map_zero] at h1
      rw [Finset.prod_eq_zero_iff] at h1
      obtain ⟨k, hk, hk0⟩ := h1
      rw [sub_eq_zero] at hk0
      exact hc k (by simpa using hk) (hinj (by simpa using hk0)).symm
    · intro hx a ha
      exact (PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ _ a).1 ha x hx
  refine ⟨hK1, ?_⟩
  intro g hg hgK
  rw [PositivityTheory.HtPt.Rf.mem_torsFun T hφ] at hg
  obtain ⟨a, rfl⟩ := hg
  have haI : a ∈ vanIdeal T pt (K : Set N) := by
    rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
    intro k hk
    have h3 := hgK k (by rw [hK1]; exact hk)
    exact hinj (by rw [map_zero]; exact h3)
  obtain ⟨J, hJ⟩ : ∃ J : Ideal T.A, J = Ideal.map ψ (RingHom.ker (φ' 0)) := ⟨_, rfl⟩
  have hIJ : vanIdeal T pt (K : Set N) ≤ J := by
    have hzp : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ^ p = 1 := by
      rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]
    have hqψ : (Ideal.Quotient.mkₐ R J).comp ψ = (Algebra.ofId R (T.A ⧸ J)).comp (φ' 0) := by
      apply AlgHom.ext
      intro b
      have hb : b - algebraMap R T'.A (φ' 0 b) ∈ RingHom.ker (φ' 0) := by
        simp [RingHom.mem_ker]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply,
        ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← AlgHom.commutes ψ, ← map_sub, hJ]
      exact Ideal.mem_map_of_mem _ hb
    have hz1 : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j = 1 := by
      calc (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j
          = spMap (Ideal.Quotient.mkₐ R J) ≫ spMap ψ ≫ T'.y := by rw [Category.assoc, hψ]
        _ = spMap ((Ideal.Quotient.mkₐ R J).comp ψ) ≫ T'.y := by
          rw [← Category.assoc, Chart.spMap_comp]
        _ = spMap ((Algebra.ofId R (T.A ⧸ J)).comp (φ' 0)) ≫ T'.y := by rw [hqψ]
        _ = spMap (Algebra.ofId R (T.A ⧸ J)) ≫ pt' 0 := by
          rw [← Chart.spMap_comp, Category.assoc, hφ' 0]
        _ = 1 := by rw [h0', MonObj.comp_one]
    obtain ⟨χ, hχ⟩ := (hK (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y)).1 hz1
    obtain ⟨w, -, hu⟩ := T.univ (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) hzp
    have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = Ideal.Quotient.mkₐ R J := by
      rw [hu _ rfl]
      apply hu
      rw [← Chart.spMap_comp, Category.assoc]
      exact hχ
    intro b hb
    have h2 := AlgHom.congr_fun e b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  have ha : a ∈ J := hIJ haI
  rw [hJ] at ha
  change a ∈ Submodule.span T.A (⇑ψ '' (RingHom.ker (φ' 0) : Set T'.A)) at ha
  clear hgK haI hIJ hJ
  suffices H : ∀ c : T.A, (fun x => algebraMap R C (φ x (c * a))) ∈
      (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt by
    have H1 := H 1
    rwa [_root_.one_mul] at H1
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro c
    have e : (fun y => algebraMap R C (φ y (c * ψ b))) =
        (fun y => algebraMap R C (φ y (ψ b))) * (fun y => algebraMap R C (φ y c)) := by
      funext y
      simp [map_mul, mul_comm]
    rw [e]
    apply Submodule.mul_mem_mul
    · rw [Submodule.mem_map]
      refine ⟨fun y => algebraMap R C (φ' y b), ?_, ?_⟩
      · rw [augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
        refine ⟨(PositivityTheory.HtPt.Rf.mem_torsFun T' hφ' _).2 ⟨b, rfl⟩, ?_⟩
        rw [SetLike.mem_coe, RingHom.mem_ker] at hb
        simp only [hb, map_zero]
      · funext y
        rw [LinearMap.funLeft_apply, ← hcomp y, AlgHom.comp_apply]
    · exact (PositivityTheory.HtPt.Rf.mem_torsFun T hφ _).2 ⟨c, rfl⟩
  | zero =>
    intro c
    simp only [mul_zero, map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro c
    have h4 := Submodule.add_mem _ (hx c) (hy c)
    convert h4 using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    intro c
    convert hx (c * r) using 1
    funext z
    rw [smul_eq_mul, _root_.mul_assoc]
