import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamSat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Use `W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem γ_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Take `⟨h0, h1⟩` from `W.γ₀_X g`. Take `⟨u₀, hu₀⟩` from `PowerSeries.X_dvd_iff.mpr h0`. Establish `hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O)`. Rewrite using `[← h1, hu₀, PowerSeries.coeff_succ_X_mul]`. Simplify using the standard rewrite rules.

Use `⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `PowerSeries.mul_invOfUnit u₀ _ hc`. Use function extensionality and compare the values at `i`. Simplify using `[LocWach.γA, letγ, letπ, hu₀]`.
-/
theorem γA_π (g : W.Gam) : ∃ u u' : LetA O n, u * u' = 1 ∧ W.γA g letπ = letπ * u := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨u₀, hu₀⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hu₀, PowerSeries.coeff_succ_X_mul]
    simp
  refine ⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩
  · funext i
    exact PowerSeries.mul_invOfUnit u₀ _ hc
  · funext i
    simp [LocWach.γA, letγ, letπ, hu₀]

/- English proof (translation)
Introduce and unpack `_ ⟨n₁, hn₁, rfl⟩`. Use `⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)`. Conclude with `W.map_γ π W.gam n₁`.
-/
theorem map_γ_mem {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) :
    ∀ y ∈ (W.N T₁).map (mapA W π), W.γ T₂ y ∈ (W.N T₁).map (mapA W π) := by
  rintro _ ⟨n₁, hn₁, rfl⟩
  refine ⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩
  change W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)
  exact W.map_γ π W.gam n₁

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `hP _ h1` as an intermediate fact. Rewrite `this` using `[γ_smul, map_pow, map_natCast]`. Conclude with `this`. Take `⟨u, u', huu, hu⟩` from `γA_π W W.gam`.

Use `P.smul_mem (u' ^ k) (hP _ h2)` as an intermediate fact. Establish `e : u' ^ k * (letπ * u) ^ k = letπ ^ k`. Rewrite using `[← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]`. Rewrite `this` using `[γ_smul, map_pow, hu, smul_smul, e]`. Conclude with `this`.
-/
theorem pow_smul_γ_mem (T : LocLat G Qp LL O) (P : Submodule (LetA O n) (W.DD T))
    (hP : ∀ y ∈ P, W.γ T y ∈ P) (p k : ℕ) (x : W.DD T)
    (h1 : ((p : LetA O n)) ^ k • x ∈ P) (h2 : (letπ : LetA O n) ^ k • x ∈ P) :
    ((p : LetA O n)) ^ k • W.γ T x ∈ P ∧ (letπ : LetA O n) ^ k • W.γ T x ∈ P := by
  constructor
  · have := hP _ h1
    rw [γ_smul, map_pow, map_natCast] at this
    exact this
  · obtain ⟨u, u', huu, hu⟩ := γA_π W W.gam
    have := P.smul_mem (u' ^ k) (hP _ h2)
    have e : u' ^ k * (letπ * u) ^ k = letπ ^ k := by
      rw [← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]
    rw [γ_smul, map_pow, hu, smul_smul, e] at this
    exact this

/- English proof (translation)
Use `set P := (W.N T₁).map (mapA W π) with hPdef`. Establish `hP` using `map_γ_mem W π`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hx, k, h1, h2⟩`. Conclude with `⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩`.

Introduce and unpack `x ⟨hx, k, h1, h2⟩`. Take `⟨y, hy, hxy⟩` from `W.N_π T₂ W.gam x hx`. Take `⟨n₁, hn₁, hn₁x⟩` from `h1`. Take `⟨m₁, hm₁, hnm⟩` from `W.N_π T₁ W.gam n₁ hn₁`. Establish `hγ` using `pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2`.

Establish `hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w`. Introduce `z w hzw`. Take `⟨u, hu⟩` from `W.EE_π`. Rewrite `hzw` using `[← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w, ← hu]`. Use `congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw` as an intermediate fact.

Simplify `this` using `[smul_smul]`. Establish `hly : ((p : LetA O n)) ^ k • y = mapA W π m₁`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]`. Establish `e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x`.

Use `γ_smul W T₂ (((p : LetA O n)) ^ k) x` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`. Conclude with `this`. Rewrite using `[← e1, ← hn₁x]`. Express the relevant statement in the definitionally equal form `W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)`.

Rewrite using `[map_sub, W.map_γ]`. Use `⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', mul_smul, hly]`. Conclude with `P.smul_mem _ ⟨m₁, hm₁, rfl⟩`. Rewrite using `[pow_succ, mul_smul, ← hxy, smul_sub]`.

Conclude with `P.sub_mem hγ.2 h2`. Express the relevant statement in the definitionally equal form `(letπ : LetA O n) • y = _`. Rewrite using `[← hxy]`. Both sides reduce to the same expression.
-/
theorem gam_sat (p : ℕ) (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) :
    (∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧
    ∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)).map
        (smulA W T₂ letπ) := by
  set P := (W.N T₁).map (mapA W π) with hPdef
  have hP := map_γ_mem W π
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, k, h1, h2⟩
    exact ⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩
  · rintro x ⟨hx, k, h1, h2⟩
    obtain ⟨y, hy, hxy⟩ := W.N_π T₂ W.gam x hx
    obtain ⟨n₁, hn₁, hn₁x⟩ := h1
    obtain ⟨m₁, hm₁, hnm⟩ := W.N_π T₁ W.gam n₁ hn₁
    have hγ := pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2

    have hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w := by
      intro z w hzw
      obtain ⟨u, hu⟩ := W.EE_π
      rw [← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w,
        ← hu] at hzw
      have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw
      simpa [smul_smul] using this
    have hly : ((p : LetA O n)) ^ k • y = mapA W π m₁ := by
      apply hinj
      rw [smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]
      have e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x := by
        have := γ_smul W T₂ (((p : LetA O n)) ^ k) x
        rw [map_pow, map_natCast] at this
        exact this
      rw [← e1, ← hn₁x]
      change W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)
      rw [map_sub, W.map_γ]
    refine ⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩
    · rw [pow_succ', mul_smul, hly]
      exact P.smul_mem _ ⟨m₁, hm₁, rfl⟩
    · rw [pow_succ, mul_smul, ← hxy, smul_sub]
      exact P.sub_mem hγ.2 h2
    · change (letπ : LetA O n) • y = _
      rw [← hxy]
      rfl

end Generic

/- English proof (translation)
Introduce `D HW F l _ K s LL h W T₁ T₂ π _ _`. Conclude with `gam_sat W l T₁ T₂ π`.
-/
theorem wachSaturation_gamma_stable_and_sub_one_mem_pi_smul : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _ _
  exact gam_sat W l T₁ T₂ π

end GlobalTheory.NL.GamSat
