import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyReductionModuloHighDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeriStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumIsotypicProjectorsEqIdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmoduleStatement

noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

/- English proof (translation)
Introduce `x hx`. Establish `hpow : ∀ n : ℕ, (T ^ n) x ∈ W`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hx`.

Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply]`. Conclude with `hT _ ih`. Rewrite using `[Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `(IsUnitBall.mem_range_iff (O := O) (p.coeff i)).2 (hp i)`.

Rewrite using `[LinearMap.smul_apply, ← hc, algebraMap_smul]`. Conclude with `W.smul_mem c (hpow i)`.
-/
theorem aeval_mem_of_stable {O K V : Type} [CommRing O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (W : Submodule O V)
    (T : Module.End K V) (hT : ∀ x ∈ W, T x ∈ W) (p : Polynomial K) (hp : ∀ n, ‖p.coeff n‖ ≤ 1) :
    ∀ x ∈ W, Polynomial.aeval T p x ∈ W := by
  intro x hx
  have hpow : ∀ n : ℕ, (T ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (p.coeff i)).2 (hp i)
  rw [LinearMap.smul_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (hpow i)

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (v : Vec K a ι), F.app ((P.conn ^ n) v) = (Q.conn ^ n) (F.app v)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v`. Both sides reduce to the same expression.

Consider the case `succ n ih`. Introduce `v`. Simplify using `only [pow_succ', Module.End.mul_apply]`. Rewrite using `[F.app_conn, ih]`. Rewrite using `[Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, hpow]`.
-/
theorem app_aeval {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (p : Polynomial K)
    (v : Vec K a ι) : F.app (Polynomial.aeval P.conn p v) = Polynomial.aeval Q.conn p (F.app v) := by
  have hpow : ∀ (n : ℕ) (v : Vec K a ι), F.app ((P.conn ^ n) v) = (Q.conn ^ n) (F.app v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      simp only [pow_succ', Module.End.mul_apply]
      rw [F.app_conn, ih]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, hpow]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • P.MM at hh`. Express the relevant statement in the definitionally equal form `F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • Q.MM`. Use `Submodule.smul_induction_on hh (fun s hs m hm => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem_smul hs (F.app_mem_ext (A_le_S l e) hm)`.

Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.
-/
theorem app_mem_MMHigh [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q)
    {h : Vec K a ι} (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh P) : F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh Q := by
  change h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • P.MM at hh
  change F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • Q.MM
  refine Submodule.smul_induction_on hh (fun s hs m hm => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_smul hs (F.app_mem_ext (A_le_S l e) hm)
  · rw [map_add]
    exact add_mem hx hy

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx`. Use `set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ`. Use `set b := ρ + 1 with hb`. Use `set A' := H + η + b with hA'`. Establish `ha : 1 ≤ a` using `Nat.one_le_iff_ne_zero.2 (NeZero.ne a)`.

Establish `he : e + 1 = l ^ a` using `TameDescentExponentData.succ_eq (K := K)`. Establish `horb` using `GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) ha he Sig N hB.frob_mem hB.zero_mem_Sig hB.card_Sig hB.two_le`. Establish `hnum` using `GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large`. Establish `hA'l : 2 * A' + 2 < l`. Establish `: A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1`.

Simplify using `only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hnum.1`. Establish `hred` using `GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a`.

Establish `hdeg` using `GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree O K l e a`. Take `⟨α, β, hαβ⟩` from `GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span l e a ha he Sig c A' N hB.card_Sig hA'l`. Establish `hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v` using `fun n v => by`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]`. Establish `hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v` using `fun n v => by`.

Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul K⟦X⟧, hlpow]`. Establish `hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K` using `fun n => pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n`. Establish `vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L` using `fun n v hv => D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv`. Use `set T := Tsub F A' b with hT`. Establish `memT1 : ∀ y ∈ D₁.L, ((X : K⟦X⟧) ^ e) ^ A' • F.app y ∈ T` using `fun y hy => Submodule.mem_sup_left (Submodule.mem_sup_left ⟨F.app y, ⟨y, hy, rfl⟩, rfl⟩)`.

Establish `memT2 : ∀ z ∈ D₂.L, (l : K) ^ b • z ∈ T` using `fun z hz => Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, hz, by simp [hlpow']⟩)`. Establish `memT3 : ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod, h ∈ T` using `fun h hh => Submodule.mem_sup_right hh`. Establish `hTc : ∀ w ∈ T, D₂.conn w ∈ T` using `GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule O K l e a ι κ η H D₁ D₂ F A' b hred`. Establish `a3` using `GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)`. Take `⟨y₀, hy₀, z₀, hz₀, h3⟩` from `a3 x hx`.

Establish `hyd : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) = F.app (isoProj D₁.desc c y₀) + (l : K) ^ b • isoProj D₂.desc c z₀`. Rewrite using `[h3, map_add, map_smul, app_isoProj]`. Establish `hy_iso` using `GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a κ D₂.toPhiMod D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x)`. Establish `hy_v : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod A'`. Rewrite using `[isoProj_vpow]`.

Conclude with `⟨_, GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c x hx, rfl⟩`. Establish `hy₁L` using `GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a ι D₁.toPhiMod D₁.desc c y₀ hy₀`. Establish `hy₁iso` using `GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a ι D₁.toPhiMod D₁.desc c y₀`. Establish `hz₁L` using `GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c z₀ hz₀`. Use `set y := isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) with hy`.

Set `φ : ℤ_[l] →+* K` to `(algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom`. Establish `hφ : ∀ t, ‖φ t‖ ≤ 1` using `fun t => by`. Simplify using `only [φ, RingHom.comp_apply, norm_algebraMap']`. Conclude with `PadicInt.norm_le_one t`. Establish `hPZ : ∀ p : Polynomial ℤ, (p.map (Int.castRingHom ℤ_[l])).map φ = p.map (Int.castRingHom K)`.

Introduce `p`. Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Establish `hZ : ∀ (p : Polynomial ℤ), ∀ (m : ℕ), ‖(p.map (Int.castRingHom K)).coeff m‖ ≤ 1`.

Introduce `p m`. Rewrite using `[Polynomial.coeff_map, eq_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one K _`. Establish `haeZ : ∀ {μ : Type} [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a μ) (p : Polynomial ℤ) (v : Vec K a μ), Polynomial.aeval P.conn p v = Polynomial.aeval P.conn (p.map (Int.castRingHom K)) v`. Introduce `μ _ _ P p v`.

Rewrite using `[← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]`. Establish `key : (l : K) ^ ρ • y = Polynomial.aeval D₂.conn (α.map φ) (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y) + Polynomial.aeval D₂.conn (β.map φ) (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStabl …`. Establish `h1` using `congrArg (Polynomial.map φ) hαβ`. Rewrite `h1` using `[Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hPZ, hPZ]`. Establish `h2` using `congrArg (fun p => Polynomial.aeval D₂.conn p y) h1`.

Rewrite `h2` using `[Polynomial.aeval_C, Module.algebraMap_end_apply, map_pow, map_natCast]`. Simplify using `only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply] at h2`. Rewrite using `[h2, haeZ, haeZ]`. Establish `hA : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y ∈ T`. Rewrite using `[haeZ, hyd, map_add, map_smul, ← app_aeval, ← haeZ]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Establish `hr` using `((hdeg Sig c A' (by omega)).2 ι η H D₁ h₁).aeval₁ _ ⟨hy₁L, hy₁iso⟩`. Take `⟨u, hu, h, hh, hsum⟩` from `Submodule.mem_sup.1 hr`. Rewrite using `[← hsum, map_add]`. Take `⟨w, hw, rfl⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu`.

Rewrite using `[map_smul]`. Conclude with `add_mem (memT1 w hw) (memT3 _ (app_mem_MMHigh F.toHom hh))`. Establish `hMM : isoProj D₂.desc c z₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O)` using `⟨D₂.ext_mono (A_le_S l e) hz₁L, Submodule.mem_top⟩`. Establish `hst` using `aeval_mem_of_stable (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O)) D₂.conn ((hred.2.1 κ η H D₂).1.conn_MM) _ (hZ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A')) _ hMM`. Rewrite `hst` using `[(hred.2.1 κ η H D₂).1.MM_eq]`.

Take `⟨u, hu, h, hh, hsum⟩` from `Submodule.mem_sup.1 hst`. Rewrite using `[← hsum, smul_add]`. Use `add_mem (memT2 _ hu.1) (memT3 _ ?_)` and prove the remaining obligations. Rewrite using `[hlpow]`. Conclude with `(GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod).toAddSubmonoid.nsmul_mem hh.1 _`.

Establish `hB' : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y ∈ T`. Establish `hr` using `((hdeg Sig c A' (by omega)).2 κ η H D₂ h₂).aeval₂ _ ⟨hy_v, hy_iso⟩`. Take `⟨u, hu, h, hh, hsum⟩` from `Submodule.mem_sup.1 hr`. Rewrite using `[← hsum]`. Use `add_mem ?_ (memT3 _ hh)` and prove the remaining obligations.

Take `⟨w, hw, rfl⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu`. Take `⟨y', hy', z', hz', h4⟩` from `a3 w hw`. Establish `: ((X : K⟦X⟧) ^ e) ^ (2 * A') • w = ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ A' • w`. Rewrite using `[smul_smul, ← pow_add, two_mul]`. Rewrite using `[this, h4, smul_add, smul_comm _ ((l : K) ^ b)]`.

Conclude with `add_mem (memT1 y' hy') (memT2 _ (vmemL _ _ hz'))`. Rewrite using `[key]`. Conclude with `add_mem (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hA) (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hB')`.
-/
theorem isotypic_step : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → ∀ c : ZMod e, ∀ x ∈ D₂.L, (l : K) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N • isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) • x) ∈ Tsub F (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) ha he Sig N hB.frob_mem hB.zero_mem_Sig
    hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a
  have hdeg := GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree O K l e a
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span l e a ha he Sig c A' N hB.card_Sig hA'l

  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K⟦X⟧, hlpow]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv

  set T := Tsub F A' b with hT
  have memT1 : ∀ y ∈ D₁.L, ((X : K⟦X⟧) ^ e) ^ A' • F.app y ∈ T := fun y hy =>
    Submodule.mem_sup_left (Submodule.mem_sup_left ⟨F.app y, ⟨y, hy, rfl⟩, rfl⟩)
  have memT2 : ∀ z ∈ D₂.L, (l : K) ^ b • z ∈ T := fun z hz =>
    Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, hz, by simp [hlpow']⟩)
  have memT3 : ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod, h ∈ T := fun h hh =>
    Submodule.mem_sup_right hh
  have hTc : ∀ w ∈ T, D₂.conn w ∈ T := GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule O K l e a ι κ η H D₁ D₂ F A' b hred

  have a3 := GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)
  obtain ⟨y₀, hy₀, z₀, hz₀, h3⟩ := a3 x hx
  have hyd : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) =
      F.app (isoProj D₁.desc c y₀) + (l : K) ^ b • isoProj D₂.desc c z₀ := by
    rw [h3, map_add, map_smul, app_isoProj]
  have hy_iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a κ D₂.toPhiMod D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x)
  have hy_v : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod A' := by
    rw [isoProj_vpow]
    exact ⟨_, GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c x hx, rfl⟩
  have hy₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a ι D₁.toPhiMod D₁.desc c y₀ hy₀
  have hy₁iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a ι D₁.toPhiMod D₁.desc c y₀
  have hz₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c z₀ hz₀
  set y := isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) with hy

  let φ : ℤ_[l] →+* K := (algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom
  have hφ : ∀ t, ‖φ t‖ ≤ 1 := fun t => by
    simp only [φ, RingHom.comp_apply, norm_algebraMap']
    exact PadicInt.norm_le_one t
  have hPZ : ∀ p : Polynomial ℤ, (p.map (Int.castRingHom ℤ_[l])).map φ = p.map (Int.castRingHom K) := by
    intro p
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hZ : ∀ (p : Polynomial ℤ), ∀ (m : ℕ), ‖(p.map (Int.castRingHom K)).coeff m‖ ≤ 1 := by
    intro p m
    rw [Polynomial.coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have haeZ : ∀ {μ : Type} [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a μ) (p : Polynomial ℤ)
      (v : Vec K a μ), Polynomial.aeval P.conn p v = Polynomial.aeval P.conn (p.map (Int.castRingHom K)) v := by
    intro μ _ _ P p v
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
  have key : (l : K) ^ ρ • y =
      Polynomial.aeval D₂.conn (α.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y) +
        Polynomial.aeval D₂.conn (β.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y) := by
    have h1 := congrArg (Polynomial.map φ) hαβ
    rw [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hPZ, hPZ] at h1
    have h2 := congrArg (fun p => Polynomial.aeval D₂.conn p y) h1
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, map_pow, map_natCast] at h2
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply] at h2
    rw [h2, haeZ, haeZ]

  have hA : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y ∈ T := by
    rw [haeZ, hyd, map_add, map_smul, ← app_aeval, ← haeZ]
    refine add_mem ?_ ?_
    · have hr := ((hdeg Sig c A' (by omega)).2 ι η H D₁ h₁).aeval₁ _ ⟨hy₁L, hy₁iso⟩
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
      rw [← hsum, map_add]
      obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
      rw [map_smul]
      exact add_mem (memT1 w hw) (memT3 _ (app_mem_MMHigh F.toHom hh))
    · have hMM : isoProj D₂.desc c z₀ ∈
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) :=
        ⟨D₂.ext_mono (A_le_S l e) hz₁L, Submodule.mem_top⟩
      have hst := aeval_mem_of_stable (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O)) D₂.conn
        ((hred.2.1 κ η H D₂).1.conn_MM) _ (hZ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A')) _ hMM
      rw [(hred.2.1 κ η H D₂).1.MM_eq] at hst
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hst
      rw [← hsum, smul_add]
      refine add_mem (memT2 _ hu.1) (memT3 _ ?_)
      rw [hlpow]
      exact (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod).toAddSubmonoid.nsmul_mem hh.1 _

  have hB' : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y ∈ T := by
    have hr := ((hdeg Sig c A' (by omega)).2 κ η H D₂ h₂).aeval₂ _ ⟨hy_v, hy_iso⟩
    obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
    rw [← hsum]
    refine add_mem ?_ (memT3 _ hh)
    obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
    obtain ⟨y', hy', z', hz', h4⟩ := a3 w hw
    have : ((X : K⟦X⟧) ^ e) ^ (2 * A') • w = ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ A' • w := by
      rw [smul_smul, ← pow_add, two_mul]
    rw [this, h4, smul_add, smul_comm _ ((l : K) ^ b)]
    exact add_mem (memT1 y' hy') (memT2 _ (vmemL _ _ hz'))
  rw [key]
  exact add_mem
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hA)
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hB')

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl`. Use `set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ`. Use `set b := ρ + 1 with hb`. Use `set A' := H + η + b with hA'`. Establish `horb` using `GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) (TameDescentExponentData.succ_eq (K := K)) Sig N hB.frob_mem hB.zero_mem_Sig hB.card_Sig hB.two_le`.

Establish `hnum` using `GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large`. Establish `hA'l : 2 * A' + 2 < l`. Establish `: A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1`. Simplify using `only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `hnum.1`. Establish `hns : ∀ (n : ℕ) (v : Vec K a κ), ((n : K)) • v = n • v` using `fun n v => Nat.cast_smul_eq_nsmul K n v`. Establish `hns' : ∀ (n : ℕ) (v : Vec K a κ), ((n : K⟦X⟧)) • v = n • v` using `fun n v => Nat.cast_smul_eq_nsmul K⟦X⟧ n v`. Establish `hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v` using `fun n v => by`.

Rewrite using `[← Nat.cast_pow, hns]`. Establish `hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v` using `fun n v => by`. Rewrite using `[← Nat.cast_pow, hns', hlpow]`. Establish `hlpow₁ : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v` using `fun n v => by`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]`.

Establish `hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K` using `fun n => pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n`. Establish `vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L` using `fun n v hv => D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv`. Establish `lmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, (l : K) ^ n • v ∈ D₂.L` using `fun n v hv => by`. Rewrite using `[hlpow]`. Conclude with `D₂.L.toAddSubmonoid.nsmul_mem hv _`.

Establish `lmemL₁ : ∀ n : ℕ, ∀ v ∈ D₁.L, (l : K) ^ n • v ∈ D₁.L` using `fun n v hv => by`. Rewrite using `[hlpow₁]`. Conclude with `D₁.L.toAddSubmonoid.nsmul_mem hv _`. Establish `appL : ∀ v ∈ D₁.L, F.app v ∈ D₂.L` using `fun v hv => F.app_mem_ext le_rfl hv`. Establish `hred` using `GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a`.

Establish `a3 : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ A' • x = F.app y + (l : K) ^ b • z` using `GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)`. Establish `stepP : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, (l : K) ^ ρ • x = F.app y + (l : K) ^ b • z`. Introduce `x hx`. Establish `hT : (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.CokerL.Tsub F A' b`. Rewrite using `[← GlobalTheory.T.sum_isotypicProjectors_eq_id O K l e a κ D₂.toPhiMod D₂.desc (((X : K⟦X⟧) ^ e) ^ A' • x), Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.CokerL.isotypic_step O K l e a ι κ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx`. Take `⟨t, ht, h, hh, hth⟩` from `Submodule.mem_sup.1 hT`. Take `⟨t₁, ht₁, t₂, ht₂, rfl⟩` from `Submodule.mem_sup.1 ht`. Take `⟨u₁, hu₁, rfl⟩` from `Submodule.mem_map.1 ht₁`.

Take `⟨y', hy', rfl⟩` from `Submodule.mem_map.1 (Submodule.restrictScalars_mem _ _ _ |>.1 hu₁)`. Take `⟨z', hz', rfl⟩` from `Submodule.mem_map.1 ht₂`. Simplify using `only [LinearMap.restrictScalars_apply, GlobalTheory.BK.mulV_apply] at hth`. Establish `hz'L : z' ∈ D₂.L` using `hz'`. Establish `hhL : h ∈ D₂.L`.

Establish `: h = (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) - (((X : K⟦X⟧) ^ e) ^ A' • F.app y' + (l : K⟦X⟧) ^ b • z')` using `by rw [← hth]; abel`. Rewrite using `[this]`. Conclude with `sub_mem (lmemL _ _ (vmemL _ _ hx)) (add_mem (vmemL _ _ (appL _ hy')) (by rw [hlpow']; exact lmemL _ _ hz'L))`. Establish `hv : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod l`. Establish `hi` using `(hred.2.1 κ η H D₂).1.inter_eq`.

Establish `hmem : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.L.restrictScalars O) ⊓ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod)` using `⟨⟨hhL, Submodule.mem_top⟩, ⟨hh, Submodule.mem_top⟩⟩`. Rewrite `hmem` using `[hi]`. Conclude with `hmem.1`. Take `⟨h₀, hh₀, rfl⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hv`. Establish `hle : A' ≤ l` using `by omega`.

Establish `hwL : (l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ ∈ D₂.L` using `sub_mem (sub_mem (lmemL _ _ hx) (appL _ hy')) (vmemL _ _ hh₀)`. Establish `hw : ((X : K⟦X⟧) ^ e) ^ A' • ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) = (l : K) ^ b • z'`. Rewrite using `[smul_sub, smul_sub, smul_comm (((X : K⟦X⟧) ^ e) ^ A') ((l : K) ^ ρ), smul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← hth, hlpow']`. Normalize the expressions using the abelian group laws. Take `⟨z'', hz'', hw'⟩` from `GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem O K l e a κ D₂.toPhiMod A' b _ z' hwL hz'L hw`.

Take `⟨y₂, hy₂, z₂, hz₂, h2⟩` from `a3 _ (vmemL (l - 2 * A') _ hh₀)`. Establish `e1 : ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ = ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ (l - 2 * A') • h₀`. Rewrite using `[smul_smul, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Use `⟨y' + y₂, add_mem hy' hy₂, z'' + z₂, add_mem hz'' hz₂, ?_⟩` and prove the remaining obligations. Establish `key : (l : K) ^ ρ • x = ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) + F.app y' + ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀` using `by abel`. Rewrite using `[key, hw', e1, h2, map_add, smul_add]`. Normalize the expressions using the abelian group laws. Take `⟨m, hm⟩` from `GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries O K l F.coker hfl`.

Establish `killM : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ m) D₁.M D₂.M` using `(GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.killsCoker_M_iff F.toHom (l ^ m)).2 fun q => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (A O K), Nat.cast_pow]`. Conclude with `hm q`. Establish `killL : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, F.app y = (l ^ m) • x`. Introduce `x hx`.

Rewrite `hx` using `[D₂.toPhiMod.L_eq_span]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Take `⟨y₀, hy₀, hF⟩` from `killM w hw`.

Conclude with `⟨D₁.phi y₀, D₁.phi_mem_L hy₀, by rw [F.app_phi, hF, map_nsmul]⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a1, ha1, e1⟩` from `hx`. Take `⟨a2, ha2, e2⟩` from `hy`.

Conclude with `⟨a1 + a2, add_mem ha1 ha2, by rw [map_add, e1, e2, smul_add]⟩`. Consider the case `smul r x _ hx`. Take `⟨a1, ha1, e1⟩` from `hx`. Conclude with `⟨r • a1, D₁.L.smul_mem r ha1, by rw [LinearMap.map_smul_of_tower, e1, smul_comm]⟩`. Establish `Q : ∀ k : ℕ, ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, (l : K) ^ ρ • x = F.app y + (l : K) ^ (ρ + k) • z`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact fun x hx => ⟨0, zero_mem _, x, hx, by simp⟩`. Consider the case `succ k ih`. Introduce `x hx`.

Take `⟨y, hy, z, hz, e1⟩` from `ih x hx`. Take `⟨y₂, hy₂, z₂, hz₂, e2⟩` from `stepP z hz`. Use `⟨y + (l : K) ^ k • y₂, add_mem hy (lmemL₁ _ _ hy₂), z₂, hz₂, ?_⟩` and prove the remaining obligations. Establish `hp : (l : K) ^ (ρ + (k + 1)) = (l : K) ^ k * (l : K) ^ b`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, pow_add, mul_comm, mul_smul, e2, smul_add, smul_smul, ← hp, map_add, LinearMap.map_smul_of_tower, add_assoc]`. Introduce `x hx`. Take `⟨y, hy, z, hz, e1⟩` from `Q m x hx`.

Take `⟨y₃, hy₃, e3⟩` from `killL z hz`. Use `⟨y + (l : K) ^ ρ • y₃, add_mem hy (lmemL₁ _ _ hy₃), ?_⟩` and prove the remaining obligations. Rewrite using `[← hlpow ρ x, e1, pow_add, mul_smul, hlpow m z, map_add, LinearMap.map_smul_of_tower, e3]`.
-/
theorem kills_cokerL : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'

  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) (Nat.one_le_iff_ne_zero.2 (NeZero.ne a))
    (TameDescentExponentData.succ_eq (K := K)) Sig N hB.frob_mem hB.zero_mem_Sig hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1

  have hns : ∀ (n : ℕ) (v : Vec K a κ), ((n : K)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K n v
  have hns' : ∀ (n : ℕ) (v : Vec K a κ), ((n : K⟦X⟧)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K⟦X⟧ n v
  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, hns]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, hns', hlpow]
  have hlpow₁ : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv
  have lmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, (l : K) ^ n • v ∈ D₂.L := fun n v hv => by
    rw [hlpow]; exact D₂.L.toAddSubmonoid.nsmul_mem hv _
  have lmemL₁ : ∀ n : ℕ, ∀ v ∈ D₁.L, (l : K) ^ n • v ∈ D₁.L := fun n v hv => by
    rw [hlpow₁]; exact D₁.L.toAddSubmonoid.nsmul_mem hv _
  have appL : ∀ v ∈ D₁.L, F.app v ∈ D₂.L := fun v hv => F.app_mem_ext le_rfl hv
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a

  have a3 : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      ((X : K⟦X⟧) ^ e) ^ A' • x = F.app y + (l : K) ^ b • z :=
    GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)

  have stepP : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, (l : K) ^ ρ • x = F.app y + (l : K) ^ b • z := by
    intro x hx
    have hT : (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.CokerL.Tsub F A' b := by
      rw [← GlobalTheory.T.sum_isotypicProjectors_eq_id O K l e a κ D₂.toPhiMod D₂.desc (((X : K⟦X⟧) ^ e) ^ A' • x),
        Finset.smul_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      exact GlobalTheory.CokerL.isotypic_step O K l e a ι κ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
    obtain ⟨t, ht, h, hh, hth⟩ := Submodule.mem_sup.1 hT
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨u₁, hu₁, rfl⟩ := Submodule.mem_map.1 ht₁
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (Submodule.restrictScalars_mem _ _ _ |>.1 hu₁)
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.1 ht₂
    simp only [LinearMap.restrictScalars_apply, GlobalTheory.BK.mulV_apply] at hth
    have hz'L : z' ∈ D₂.L := hz'
    have hhL : h ∈ D₂.L := by
      have : h = (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) -
          (((X : K⟦X⟧) ^ e) ^ A' • F.app y' + (l : K⟦X⟧) ^ b • z') := by rw [← hth]; abel
      rw [this]
      exact sub_mem (lmemL _ _ (vmemL _ _ hx))
        (add_mem (vmemL _ _ (appL _ hy')) (by rw [hlpow']; exact lmemL _ _ hz'L))
    have hv : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod l := by
      have hi := (hred.2.1 κ η H D₂).1.inter_eq
      have hmem : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.L.restrictScalars O) ⊓
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod) :=
        ⟨⟨hhL, Submodule.mem_top⟩, ⟨hh, Submodule.mem_top⟩⟩
      rw [hi] at hmem
      exact hmem.1
    obtain ⟨h₀, hh₀, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hv
    have hle : A' ≤ l := by omega
    have hwL : (l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ ∈ D₂.L :=
      sub_mem (sub_mem (lmemL _ _ hx) (appL _ hy')) (vmemL _ _ hh₀)
    have hw : ((X : K⟦X⟧) ^ e) ^ A' • ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) =
        (l : K) ^ b • z' := by
      rw [smul_sub, smul_sub, smul_comm (((X : K⟦X⟧) ^ e) ^ A') ((l : K) ^ ρ), smul_smul, ← pow_add,
        Nat.add_sub_cancel' hle, ← hth, hlpow']
      abel
    obtain ⟨z'', hz'', hw'⟩ := GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem O K l e a κ D₂.toPhiMod A' b _ z' hwL hz'L hw
    obtain ⟨y₂, hy₂, z₂, hz₂, h2⟩ := a3 _ (vmemL (l - 2 * A') _ hh₀)
    have e1 : ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ =
        ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ (l - 2 * A') • h₀ := by
      rw [smul_smul, ← pow_add]
      congr 2
      omega
    refine ⟨y' + y₂, add_mem hy' hy₂, z'' + z₂, add_mem hz'' hz₂, ?_⟩
    have key : (l : K) ^ ρ • x = ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) +
        F.app y' + ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ := by abel
    rw [key, hw', e1, h2, map_add, smul_add]
    abel

  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries O K l F.coker hfl
  have killM : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ m) D₁.M D₂.M :=
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.killsCoker_M_iff F.toHom (l ^ m)).2 fun q => by
      rw [← Nat.cast_smul_eq_nsmul (A O K), Nat.cast_pow]
      exact hm q
  have killL : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, F.app y = (l ^ m) • x := by
    intro x hx
    rw [D₂.toPhiMod.L_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨y₀, hy₀, hF⟩ := killM w hw
      exact ⟨D₁.phi y₀, D₁.phi_mem_L hy₀, by rw [F.app_phi, hF, map_nsmul]⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a1, ha1, e1⟩ := hx
      obtain ⟨a2, ha2, e2⟩ := hy
      exact ⟨a1 + a2, add_mem ha1 ha2, by rw [map_add, e1, e2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a1, ha1, e1⟩ := hx
      exact ⟨r • a1, D₁.L.smul_mem r ha1, by rw [LinearMap.map_smul_of_tower, e1, smul_comm]⟩
  have Q : ∀ k : ℕ, ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      (l : K) ^ ρ • x = F.app y + (l : K) ^ (ρ + k) • z := by
    intro k
    induction k with
    | zero => exact fun x hx => ⟨0, zero_mem _, x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, e1⟩ := ih x hx
      obtain ⟨y₂, hy₂, z₂, hz₂, e2⟩ := stepP z hz
      refine ⟨y + (l : K) ^ k • y₂, add_mem hy (lmemL₁ _ _ hy₂), z₂, hz₂, ?_⟩
      have hp : (l : K) ^ (ρ + (k + 1)) = (l : K) ^ k * (l : K) ^ b := by
        rw [← pow_add]; congr 1; omega
      rw [e1, pow_add, mul_comm, mul_smul, e2, smul_add, smul_smul, ← hp, map_add,
        LinearMap.map_smul_of_tower, add_assoc]
  intro x hx
  obtain ⟨y, hy, z, hz, e1⟩ := Q m x hx
  obtain ⟨y₃, hy₃, e3⟩ := killL z hz
  refine ⟨y + (l : K) ^ ρ • y₃, add_mem hy (lmemL₁ _ _ hy₃), ?_⟩
  rw [← hlpow ρ x, e1, pow_add, mul_smul, hlpow m z, map_add, LinearMap.map_smul_of_tower, e3]

end GlobalTheory.CokerL
