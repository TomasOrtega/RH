import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisMore
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.KerToDivisible

/- English proof (translation)
Establish `hdvd : ∀ y : O, y ≠ 0 → ∃ n : ℕ, y ∣ ℓ ^ n`. Introduce `y hy`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Take `⟨e, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ`.

Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Apply `hℓ` to reduce the goal to its premises. Rewrite using `[hv, pow_zero, mul_one]`. Conclude with `v.isUnit`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hv, mul_pow, Units.mul_left_dvd]`. Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Rewrite using `[← pow_mul]`. Conclude with `pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))`.

Use `haveI : Module.Finite O ↥(Submodule.torsion O M) := Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)`. Take `⟨y, hy, hy0⟩` from `Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := O) (M := M))`. Take `⟨k, t, ht⟩` from `hdvd y (nonZeroDivisors.ne_zero hy0)`. Establish `hk : ∀ x : ↥(Submodule.torsion O M), ℓ ^ k • x = 0`. Introduce `x`.

Rewrite using `[ht, mul_comm, mul_smul, Submodule.mem_annihilator.1 hy x Submodule.mem_top, smul_zero]`. Use `⟨?_, k, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩` and prove the remaining obligations. Establish `hT : Module.IsTorsionBy O ↥(Submodule.torsion O M) (ℓ ^ k)` using `fun x => hk x`. Use `letI := hT.module`. Use `haveI := hfin k`.

Use `haveI : IsScalarTower O (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) := Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff _).mpr hT)`. Use `haveI : Module.Finite (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) := Module.Finite.of_restrictScalars_finite O _ _`. Conclude with `Module.finite_of_finite (O ⧸ Ideal.span {ℓ ^ k})`.
-/
theorem torsion_finite_and_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : O) (hℓ0 : ℓ ≠ 0) (hℓ : ¬ IsUnit ℓ) (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n}))
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Finite ↥(Submodule.torsion O M) ∧ ∃ k : ℕ, ∀ x ∈ Submodule.torsion O M, ℓ ^ k • x = 0 := by
  have hdvd : ∀ y : O, y ≠ 0 → ∃ n : ℕ, y ∣ ℓ ^ n := by
    intro y hy
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
    have he : e ≠ 0 := by
      rintro rfl; apply hℓ; rw [hv, pow_zero, mul_one]; exact v.isUnit
    refine ⟨n, ?_⟩
    rw [hu, hv, mul_pow, Units.mul_left_dvd]
    apply Dvd.dvd.mul_left
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))
  haveI : Module.Finite O ↥(Submodule.torsion O M) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  obtain ⟨y, hy, hy0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := O) (M := M))
  obtain ⟨k, t, ht⟩ := hdvd y (nonZeroDivisors.ne_zero hy0)
  have hk : ∀ x : ↥(Submodule.torsion O M), ℓ ^ k • x = 0 := by
    intro x
    rw [ht, mul_comm, mul_smul, Submodule.mem_annihilator.1 hy x Submodule.mem_top, smul_zero]
  refine ⟨?_, k, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩
  have hT : Module.IsTorsionBy O ↥(Submodule.torsion O M) (ℓ ^ k) := fun x => hk x
  letI := hT.module
  haveI := hfin k
  haveI : IsScalarTower O (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff _).mpr hT)
  haveI : Module.Finite (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ Ideal.span {ℓ ^ k})

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
  [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  {ρ : Representation LL G V}

/- English proof (translation)
Rewrite `ha` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨x, hx, hxa⟩` from `ha`. Use `⟨I.mkQ ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `h1 : evT L g a = actT L g ⟨x, hx⟩ - ⟨x, hx⟩` using `Subtype.ext (congrFun hxa g).symm`.

Use `show actQ L I hI g (I.mkQ ⟨x, hx⟩) - I.mkQ ⟨x, hx⟩ = I.mkQ (evT L g a)`. Rewrite using `[h1, map_sub]`. Both sides reduce to the same expression.
-/
theorem redT_mem_BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (a : ↥(latticeCocycles L)) (ha : (Submodule.Quotient.mk a : LatticeCohomology L) = 0) : redT L I a ∈ BQ L I hI := by
  rw [Submodule.Quotient.mk_eq_zero] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  refine ⟨I.mkQ ⟨x, hx⟩, ?_⟩
  funext g
  have h1 : evT L g a = actT L g ⟨x, hx⟩ - ⟨x, hx⟩ := Subtype.ext (congrFun hxa g).symm
  show actQ L I hI g (I.mkQ ⟨x, hx⟩) - I.mkQ ⟨x, hx⟩ = I.mkQ (evT L g a)
  rw [h1, map_sub]
  rfl

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem`. Consider the case `exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem`. Consider the case `(apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem ..)`.
-/
theorem exists_smul_mem [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) (w : V) :
    ∃ b : O, b ≠ 0 ∧ b • w ∈ L.T := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem ..)

/- English proof (translation)
Take `⟨vb, hvb⟩` from `hc`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ vb`. Establish `h1 : ∀ g, (ρ g v - v) - σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∈ L.T`. Introduce `g`. Rewrite using `[← Submodule.Quotient.eq, ← congrFun hvb g, Submodule.Quotient.mk_sub]`.

Both sides reduce to the same expression. Establish `hspec : ∀ g, ∃ y : ↥L.T, (y : V) = Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∧ Submodule.Quotient.mk y = c g` using `fun g => ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (c g)).choose_spec⟩`. Use `choose y hy hyc using hspec`. Use `set w : V := σ • v with hw`. Establish `h2 : ∀ g, ρ g w - w = (y g : V) + s • ((⟨_, h1 g⟩ : ↥L.T) : V)`.

Introduce `g`. Rewrite using `[← algebraMap_smul LL s, hs, hy, hw, map_smul]`. Simplify using `only [smul_sub, smul_smul, mul_inv_cancel₀ hσ, one_smul]`. Normalize the expressions using the abelian group laws. Establish `h3 : ∀ g, ρ g w - w ∈ L.T` using `fun g => by`.

Rewrite using `[h2]`. Conclude with `L.T.add_mem (y g).2 (L.T.smul_mem _ (h1 g))`. Establish `hZ : (fun g => ρ g w - w) ∈ latticeCocycles L`. Use `Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => h3 g⟩` and prove the remaining obligations. Repeatedly rewrite using `[sub_eq_add_neg]`.

Conclude with `(hρ w).add continuous_const`. Simplify using `only [map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Use `⟨⟨_, hZ⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb, hbw⟩` from `exists_smul_mem L w`.

Use `⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩, ?_⟩` and prove the remaining obligations. Use `show b • (Submodule.Quotient.mk ⟨_, hZ⟩ : LatticeCohomology L) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `⟨b • w, hbw, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Use `show ρ g (b • w) - b • w = b • (ρ g w - w)`. Rewrite using `[smul_sub, LinearMap.map_smul_of_tower]`. Use function extensionality and compare the values at `g`. Rewrite using `[← hyc g]`. Use `show (Submodule.Quotient.mk (evT L g ⟨_, hZ⟩) : ↥L.T ⧸ _) = _`.

Rewrite using `[Submodule.Quotient.eq, GlobalTheory.TateOrth.mem_span_smul_top]`. Use `⟨⟨_, h1 g⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (ρ g w - w) - y g = _`. Rewrite using `[h2, add_sub_cancel_left]`. Both sides reduce to the same expression.
-/
theorem exists_torsion_lift [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ)
    (hρ : ∀ m, Continuous fun g => ρ g m) (s : O) (σ : LL) (hs : algebraMap O LL s = σ) (hσ : σ ≠ 0)
    (c : G → ↥L.T ⧸ (Ideal.span {s} • ⊤ : Submodule O ↥L.T))
    (hc : (fun g => (Submodule.Quotient.mk (σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) : V ⧸ L.T)) ∈ BD L) :
    ∃ a : ↥(latticeCocycles L), (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) ∧
      redT L _ a = c := by
  obtain ⟨vb, hvb⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ vb
  have h1 : ∀ g, (ρ g v - v) - σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∈ L.T := by
    intro g
    rw [← Submodule.Quotient.eq, ← congrFun hvb g, Submodule.Quotient.mk_sub]
    rfl
  have hspec : ∀ g, ∃ y : ↥L.T, (y : V) = Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∧
      Submodule.Quotient.mk y = c g := fun g =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (c g)).choose_spec⟩
  choose y hy hyc using hspec
  set w : V := σ • v with hw
  have h2 : ∀ g, ρ g w - w = (y g : V) + s • ((⟨_, h1 g⟩ : ↥L.T) : V) := by
    intro g
    rw [← algebraMap_smul LL s, hs, hy, hw, map_smul]
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hσ, one_smul]
    abel
  have h3 : ∀ g, ρ g w - w ∈ L.T := fun g => by
    rw [h2]; exact L.T.add_mem (y g).2 (L.T.smul_mem _ (h1 g))
  have hZ : (fun g => ρ g w - w) ∈ latticeCocycles L := by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => h3 g⟩
    · simp_rw [sub_eq_add_neg]
      exact (hρ w).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
  refine ⟨⟨_, hZ⟩, ?_, ?_⟩
  · obtain ⟨b, hb, hbw⟩ := exists_smul_mem L w
    refine ⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩, ?_⟩
    show b • (Submodule.Quotient.mk ⟨_, hZ⟩ : LatticeCohomology L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨b • w, hbw, ?_⟩
    funext g
    show ρ g (b • w) - b • w = b • (ρ g w - w)
    rw [smul_sub, LinearMap.map_smul_of_tower]
  · funext g
    rw [← hyc g]
    show (Submodule.Quotient.mk (evT L g ⟨_, hZ⟩) : ↥L.T ⧸ _) = _
    rw [Submodule.Quotient.eq, GlobalTheory.TateOrth.mem_span_smul_top]
    refine ⟨⟨_, h1 g⟩, Subtype.ext ?_⟩
    show (ρ g w - w) - y g = _
    rw [h2, add_sub_cancel_left]
    rfl

/- English proof (translation)
Use `letI := Fintype.ofFinite ↥(Submodule.torsion O (LatticeCohomology L))`. Establish `key : ∀ t : ↥(Submodule.torsion O (LatticeCohomology L)), ∃ x : QuotientCohomology L I hI, ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t → redT L I a = c → (Submodule.Quotient.mk c : QuotientCohomology L I hI) = …`. Introduce `t`. Distinguish the cases in `h : ∃ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t ∧ redT L I a = c`. Take `⟨c0, a0, h0, h0'⟩` from `h`.

Use `⟨Submodule.Quotient.mk c0, fun c a h1 h1' => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.eq]`. Use `redT_mem_BQ L I hI (a - a0) (by rw [Submodule.Quotient.mk_sub, h0, h1, sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, h0', h1']`. Conclude with `this`.

Conclude with `⟨0, fun c a h1 h1' => absurd ⟨c, a, h1, h1'⟩ h⟩`. Use `choose ψ hψ using key`. Use `⟨Finset.univ.image ψ, ?_, fun c a ha hac => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Nat.card_eq_fintype_card, Finset.card_univ]`.

Conclude with `Finset.mem_image.2 ⟨⟨_, ha⟩, Finset.mem_univ _, (hψ ⟨_, ha⟩ c a rfl hac).symm⟩`.
-/
theorem exists_finset_red (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    [Finite ↥(Submodule.torsion O (LatticeCohomology L))] :
    ∃ F : Finset (QuotientCohomology L I hI), F.card ≤ Nat.card ↥(Submodule.torsion O (LatticeCohomology L)) ∧
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)),
        (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) → redT L I a = c →
        (Submodule.Quotient.mk c : QuotientCohomology L I hI) ∈ F := by
  classical
  letI := Fintype.ofFinite ↥(Submodule.torsion O (LatticeCohomology L))
  have key : ∀ t : ↥(Submodule.torsion O (LatticeCohomology L)), ∃ x : QuotientCohomology L I hI,
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t →
        redT L I a = c → (Submodule.Quotient.mk c : QuotientCohomology L I hI) = x := by
    intro t
    by_cases h : ∃ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t ∧
        redT L I a = c
    · obtain ⟨c0, a0, h0, h0'⟩ := h
      refine ⟨Submodule.Quotient.mk c0, fun c a h1 h1' => ?_⟩
      rw [Submodule.Quotient.eq]
      have := redT_mem_BQ L I hI (a - a0) (by rw [Submodule.Quotient.mk_sub, h0, h1, sub_self])
      rw [map_sub, h0', h1'] at this
      exact this
    · exact ⟨0, fun c a h1 h1' => absurd ⟨c, a, h1, h1'⟩ h⟩
  choose ψ hψ using key
  refine ⟨Finset.univ.image ψ, ?_, fun c a ha hac => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  · exact Finset.mem_image.2 ⟨⟨_, ha⟩, Finset.mem_univ _, (hψ ⟨_, ha⟩ c a rfl hac).symm⟩

/- English proof (translation)
Establish `hℓ0 : ℓ ≠ 0` using `fun h => hσ (by rw [← hs, h, map_zero])`. Take `⟨hF, k, hk⟩` from `torsion_finite_and_killed ℓ hℓ0 hℓ hfin (LatticeCohomology L)`. Use `⟨Nat.card ↥(Submodule.torsion O (LatticeCohomology L)), k, fun r hI => ?_⟩` and prove the remaining obligations. Take `⟨F, hFc, hFm⟩` from `exists_finset_red L _ hI`. Use `⟨F, hFc, fun c hc => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, hac⟩` from `exists_torsion_lift L hρ (ℓ ^ r) (σ ^ r) (by rw [map_pow, hs]) (pow_ne_zero _ hσ) _ hc`. Use `⟨hFm c a ha hac, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `redT_mem_BQ L _ hI (ℓ ^ k • a) (by rw [Submodule.Quotient.mk_smul]; exact hk _ ha)` as an intermediate fact. Rewrite `this` using `[map_smul, hac]`.

Conclude with `this`.
-/
theorem ker_bounded_gen [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (hfg : Module.Finite O (LatticeCohomology L))
    (ℓ : O) (σ : LL) (hs : algebraMap O LL ℓ = σ) (hσ : σ ≠ 0) (hℓ : ¬ IsUnit ℓ)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n})) :
    ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI : StableSub L (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)),
      ∃ F : Finset (QuotientCohomology L _ hI), F.card ≤ C0 ∧ ∀ c : ↥(quotientCocycles L _ hI),
        (fun g => (Submodule.Quotient.mk ((σ ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _
          ((c : G → ↥L.T ⧸ (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)) g)) : V ⧸ L.T)) ∈ BD L →
        (Submodule.Quotient.mk c : QuotientCohomology L _ hI) ∈ F ∧
          (ℓ ^ k0) • (Submodule.Quotient.mk c : QuotientCohomology L _ hI) = 0 := by
  have hℓ0 : ℓ ≠ 0 := fun h => hσ (by rw [← hs, h, map_zero])
  obtain ⟨hF, k, hk⟩ := torsion_finite_and_killed ℓ hℓ0 hℓ hfin (LatticeCohomology L)
  refine ⟨Nat.card ↥(Submodule.torsion O (LatticeCohomology L)), k, fun r hI => ?_⟩
  obtain ⟨F, hFc, hFm⟩ := exists_finset_red L _ hI
  refine ⟨F, hFc, fun c hc => ?_⟩
  obtain ⟨a, ha, hac⟩ := exists_torsion_lift L hρ (ℓ ^ r) (σ ^ r)
    (by rw [map_pow, hs]) (pow_ne_zero _ hσ) _ hc
  refine ⟨hFm c a ha hac, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have := redT_mem_BQ L _ hI (ℓ ^ k • a)
    (by rw [Submodule.Quotient.mk_smul]; exact hk _ ha)
  rw [map_smul, hac] at this
  exact this

end Gen

/- English proof (translation)
Introduce `hT l _ P K LL _ _ _ O _ _ hO A' LA'`. Establish `hgc` using `GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO`. Establish `hfg : Module.Finite O (LatticeCohomology LA')` using `GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'`. Use `letI hD : IsDomain O := hO.1.choose`. Use `haveI : IsDiscreteValuationRing O := hO.1.choose_spec.1`.

Use `haveI : IsFractionRing O LL := hO.1.choose_spec.2`. Establish `hlLL : ((l : ℕ) : LL) ≠ 0`. Introduce `h`. Establish `h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0` using `by rw [map_natCast]; exact h`. Rewrite `h'` using `[map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective]`.

Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h')`. Establish `hℓu : ¬ IsUnit ((l : ℕ) : O)` using `GlobalTheory.DoubleAnnihilator.not_isUnit_of_adicComplete _ hgc.2.2.2`. Conclude with `ker_bounded_gen (G := ↥(GK K)) (LL := LL) (O := O) (V := A'.V) (ρ := A'.ρ) LA' A'.cont hfg ((l : ℕ) : O) ((l : ℕ) : LL) (map_natCast (algebraMap O LL) l) hlLL hℓu hgc.2.2.1`.
-/
theorem ker_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hO A' LA'
  have hgc := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO
  have hfg : Module.Finite O (LatticeCohomology LA') := GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  letI hD : IsDomain O := hO.1.choose
  haveI : IsDiscreteValuationRing O := hO.1.choose_spec.1
  haveI : IsFractionRing O LL := hO.1.choose_spec.2
  have hlLL : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have hℓu : ¬ IsUnit ((l : ℕ) : O) :=
    GlobalTheory.DoubleAnnihilator.not_isUnit_of_adicComplete _ hgc.2.2.2
  exact ker_bounded_gen (G := ↥(GK K)) (LL := LL) (O := O) (V := A'.V) (ρ := A'.ρ) LA' A'.cont hfg
    ((l : ℕ) : O) ((l : ℕ) : LL) (map_natCast (algebraMap O LL) l) hlLL hℓu hgc.2.2.1

end GlobalTheory.KerToDivisible
