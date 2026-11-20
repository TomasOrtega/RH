import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2TwistFromOpenUnionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapH2SubtypeInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowPSmulMemOneFractionRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFGTopPPowInverseLatticeStatement

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.InvColim

/- English proof (translation)
Establish `hinj` using `GlobalTheory.T.map_H2_subtype_injective Θ N hmono hopen hcov hfg`. Establish `hsurj` using `GlobalTheory.T.exists_H2_preimage_of_monotone_open_exhaustion ε N hmono hopen hcov`. Set `ι : ∀ n, H2 (twist ε (N n)) →ₗ[O] H2 (twist ε M)` to `fun n => mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)`. Set `ψ : ∀ n, N n →ₗ[O] H2 (twist ε M)` to `fun n => ι n ∘ₗ (Θ.θ (N n) (hfg n)).symm.toLinearMap`. Establish `hup : ∀ n m (h : n ≤ m) (y : N n), ψ m (Submodule.inclusion (hmono h) y) = ψ n y`.

Introduce `n m h y`. Set `inc` to `Submodule.inclusion (hmono h)`. Establish `hinc : Continuous inc` using `continuous_subtype_val.subtype_mk _`. Establish `hι : ∀ w, ι m (mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc) w) = ι n w`. Introduce `w`.

Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H w => rfl`. Establish `hw : (Θ.θ (N m) (hfg m)).symm (inc y) = mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc) ((Θ.θ (N n) (hfg n)).symm y)`. Rewrite using `[LinearEquiv.symm_apply_eq, Θ.nat _ _ (hfg n) (hfg m) inc hinc, LinearEquiv.apply_symm_apply]`. Use `show ι m ((Θ.θ (N m) (hfg m)).symm (inc y)) = ι n ((Θ.θ (N n) (hfg n)).symm y)`.

Rewrite using `[hw, hι]`. Establish `hind : ∀ n m (y : M) (hn : y ∈ N n) (hm : y ∈ N m), ψ n ⟨y, hn⟩ = ψ m ⟨y, hm⟩`. Introduce `n m y hn hm`. Rewrite using `[← hup n (max n m) (le_max_left _ _), ← hup m (max n m) (le_max_right _ _)]`. Both sides reduce to the same expression.

Set `nn : M → ℕ` to `fun y => (hcov y).choose`. Establish `hnn : ∀ y, y ∈ N (nn y)` using `fun y => (hcov y).choose_spec`. Set `Ψ : M →ₗ[O] H2 (twist ε M)` to `{ toFun := fun y => ψ (nn y) ⟨y, hnn y⟩ map_add' := fun y y' => by`. Establish `hy : y ∈ N (max (nn y) (nn y'))` using `hmono (le_max_left _ _) (hnn y)`. Establish `hy' : y' ∈ N (max (nn y) (nn y'))` using `hmono (le_max_right _ _) (hnn y')`.

Use `(hind _ _ (y + y') (hnn _) (add_mem hy hy')).trans ?_` and prove the remaining obligations. Rewrite using `[hind _ _ y (hnn y) hy, hind _ _ y' (hnn y') hy', ← map_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c y => by`. Use `(hind _ (nn y) (c • y) (hnn _) (Submodule.smul_mem _ c (hnn y))).trans ?_` and prove the remaining obligations.

Rewrite using `[RingHom.id_apply, ← map_smul]`. Use `rfl }`. Establish `hΨ : ∀ n (y : N n), Ψ y = ψ n y` using `fun n y => hind _ n y (hnn _) y.2`. Establish `hΨi : Function.Injective Ψ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `y hy`. Take `⟨n, hn⟩` from `hcov y`. Establish `h1 : ψ n ⟨y, hn⟩ = 0` using `(hΨ n ⟨y, hn⟩).symm.trans hy`. Establish `h2 : (Θ.θ (N n) (hfg n)).symm ⟨y, hn⟩ = 0` using `hinj n (by rw [map_zero]; exact h1)`. Establish `h3 : (⟨y, hn⟩ : N n) = 0` using `by simpa using h2`.

Conclude with `congrArg Subtype.val h3`. Establish `hΨs : Function.Surjective Ψ`. Introduce `z`. Take `⟨n, z', hz'⟩` from `hsurj z`. Use `⟨(Θ.θ (N n) (hfg n) z' : M), ?_⟩` and prove the remaining obligations.

Rewrite using `[hΨ n]`. Use `show ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z')) = z`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `hz'`. Use `⟨(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).symm, fun n z => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Use `show _ = Ψ _`. Rewrite using `[hΨ n]`. Use `show _ = ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z))`. Rewrite using `[LinearEquiv.symm_apply_apply]`.
-/
theorem colim_equiv {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G]
    [CompactSpace G] {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M) (hmono : Monotone N)
    (hopen : ∀ n, IsOpen (N n : Set M)) (hcov : ∀ x, ∃ n, x ∈ N n) (hfg : ∀ n, IsFGTop O (N n)) :
    ∃ e : H2 (twist ε M) ≃ₗ[O] M, ∀ n (z : H2 (twist ε (N n))),
      e (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val
        (twist_map ε (N n).subtype) z) = Θ.θ (N n) (hfg n) z := by
  have hinj := GlobalTheory.T.map_H2_subtype_injective Θ N hmono hopen hcov hfg
  have hsurj := GlobalTheory.T.exists_H2_preimage_of_monotone_open_exhaustion ε N hmono hopen hcov
  let ι : ∀ n, H2 (twist ε (N n)) →ₗ[O] H2 (twist ε M) := fun n =>
    mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)
  let ψ : ∀ n, N n →ₗ[O] H2 (twist ε M) := fun n => ι n ∘ₗ (Θ.θ (N n) (hfg n)).symm.toLinearMap
  have hup : ∀ n m (h : n ≤ m) (y : N n), ψ m (Submodule.inclusion (hmono h) y) = ψ n y := by
    intro n m h y
    let inc := Submodule.inclusion (hmono h)
    have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
    have hι : ∀ w, ι m (mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc) w) = ι n w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H w => rfl
    have hw : (Θ.θ (N m) (hfg m)).symm (inc y) = mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc)
        ((Θ.θ (N n) (hfg n)).symm y) := by
      rw [LinearEquiv.symm_apply_eq, Θ.nat _ _ (hfg n) (hfg m) inc hinc, LinearEquiv.apply_symm_apply]
    show ι m ((Θ.θ (N m) (hfg m)).symm (inc y)) = ι n ((Θ.θ (N n) (hfg n)).symm y)
    rw [hw, hι]
  have hind : ∀ n m (y : M) (hn : y ∈ N n) (hm : y ∈ N m), ψ n ⟨y, hn⟩ = ψ m ⟨y, hm⟩ := by
    intro n m y hn hm
    rw [← hup n (max n m) (le_max_left _ _), ← hup m (max n m) (le_max_right _ _)]
    rfl
  let nn : M → ℕ := fun y => (hcov y).choose
  have hnn : ∀ y, y ∈ N (nn y) := fun y => (hcov y).choose_spec
  let Ψ : M →ₗ[O] H2 (twist ε M) :=
    { toFun := fun y => ψ (nn y) ⟨y, hnn y⟩
      map_add' := fun y y' => by
        have hy : y ∈ N (max (nn y) (nn y')) := hmono (le_max_left _ _) (hnn y)
        have hy' : y' ∈ N (max (nn y) (nn y')) := hmono (le_max_right _ _) (hnn y')
        refine (hind _ _ (y + y') (hnn _) (add_mem hy hy')).trans ?_
        rw [hind _ _ y (hnn y) hy, hind _ _ y' (hnn y') hy', ← map_add]
        rfl
      map_smul' := fun c y => by
        refine (hind _ (nn y) (c • y) (hnn _) (Submodule.smul_mem _ c (hnn y))).trans ?_
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  have hΨ : ∀ n (y : N n), Ψ y = ψ n y := fun n y => hind _ n y (hnn _) y.2
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, hn⟩ := hcov y
    have h1 : ψ n ⟨y, hn⟩ = 0 := (hΨ n ⟨y, hn⟩).symm.trans hy
    have h2 : (Θ.θ (N n) (hfg n)).symm ⟨y, hn⟩ = 0 := hinj n (by rw [map_zero]; exact h1)
    have h3 : (⟨y, hn⟩ : N n) = 0 := by simpa using h2
    exact congrArg Subtype.val h3
  have hΨs : Function.Surjective Ψ := by
    intro z
    obtain ⟨n, z', hz'⟩ := hsurj z
    refine ⟨(Θ.θ (N n) (hfg n) z' : M), ?_⟩
    rw [hΨ n]
    show ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z')) = z
    rw [LinearEquiv.symm_apply_apply]
    exact hz'
  refine ⟨(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).symm, fun n z => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  show _ = Ψ _
  rw [hΨ n]
  show _ = ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z))
  rw [LinearEquiv.symm_apply_apply]

section Lat
variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

/- English proof (translation)
The claim follows from `GlobalTheory.T.isFGTop_p_pow_inverse_lattice hO hF n`.
-/
theorem frac_isFGTop (hO : PadicCoeff p O) (hF : FracTop O) (n : ℕ) :
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := GlobalTheory.T.isFGTop_p_pow_inverse_lattice hO hF n

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing hO y`.
-/
theorem frac_cover (hO : PadicCoeff p O) (y : FractionRing O) :
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing hO y

/- English proof (translation)
Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Establish `h1 : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) = Set.range (algebraMap O (FractionRing O))`. Use extensionality with `y`. Simplify using `[Submodule.mem_one]`. Establish `h2 : ({0} : Set (KO O)) = (1 : Submodule O (FractionRing O)).mkQ '' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨0, zero_mem _, map_zero _⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 hy`. Rewrite using `[h2]`. Conclude with `(Submodule.isOpenQuotientMap_mkQ _).isOpenMap _ (h1 ▸ hF.emb.isOpen_range)`.
-/
theorem ko_discrete (hF : FracTop O) : DiscreteTopology (KO O) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have h1 : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext y; simp [Submodule.mem_one]
  have h2 : ({0} : Set (KO O)) =
      (1 : Submodule O (FractionRing O)).mkQ '' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨0, zero_mem _, map_zero _⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 hy
  rw [h2]
  exact (Submodule.isOpenQuotientMap_mkQ _).isOpenMap _ (h1 ▸ hF.emb.isOpen_range)

end Lat

/- English proof (translation)
Introduce `p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hε`. Take `⟨Θ⟩` from `GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT hK hO i hε`. Use `haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace`. Use `haveI := ko_discrete hF`. Set `F : ℕ → Submodule O (FractionRing O)` to `fun n => (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))`.

Set `T : ℕ → Submodule O (KO O)` to `fun n => LinearMap.ker (LinearMap.lsmul O (KO O) ((p : O) ^ n))`. Establish `hFm : Monotone F`. Use `monotone_nat_of_le_succ fun n y hy => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_one.1 hy`. Use `Submodule.mem_one.2 ⟨(p : O) * a, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.lsmul_apply] at ha ⊢`. Rewrite using `[map_mul, ha, pow_succ, mul_comm _ (p : O), mul_smul, Algebra.smul_def (p : O) (((p : O) ^ n) • y)]`. Establish `hFo : ∀ n, IsOpen (F n : Set (FractionRing O))` using `fun n => by`. Establish `: (F n : Set (FractionRing O)) = (fun y : FractionRing O => ((p : O) ^ n) • y) ⁻¹' Set.range (algebraMap O (FractionRing O))`. Use extensionality with `y`.

Simplify using `[F, Submodule.mem_one]`. Rewrite using `[this]`. Conclude with `hF.emb.isOpen_range.preimage (continuous_const_smul _)`. Establish `hFfg` using `frac_isFGTop hO hF`. Establish `hred : ∀ n, ∀ y ∈ F n, toKO O y ∈ T n` using `fun n y hy => by`.

Simplify using `only [T, LinearMap.mem_ker, LinearMap.lsmul_apply, F, Submodule.mem_comap] at hy ⊢`. Rewrite using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 hy`. Establish `hTm : Monotone T`. Use `monotone_nat_of_le_succ fun n x hx => ?_` and prove the remaining obligations.

Simplify using `only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢`. Rewrite using `[pow_succ, mul_comm, mul_smul, hx, smul_zero]`. Establish `hTo : ∀ n, IsOpen (T n : Set (KO O))` using `fun n => isOpen_discrete _`. Establish `hTc : ∀ x, ∃ n, x ∈ T n` using `fun x => by`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Take `⟨n, hn⟩` from `frac_cover hO y`. Conclude with `⟨n, hred n y hn⟩`. Establish `hTsurj : ∀ n, (F n).map (toKO O) = T n` using `fun n => by`. Use `le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy => hred n y hy) fun x hx => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Use `⟨y, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx`. Rewrite `hx` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hx`. Establish `hTfg : ∀ n, IsFGTop O (T n)` using `fun n => by`.

Use `⟨?_, inferInstance, inferInstance⟩` and prove the remaining obligations. Use `(hFfg n).fg` as an intermediate fact. Rewrite using `[← hTsurj n, Module.Finite.iff_fg]`. Conclude with `Submodule.FG.map _ (Module.Finite.iff_fg.1 this)`. Take `⟨eF, heF⟩` from `colim_equiv Θ F hFm hFo (frac_cover hO) hFfg`.

Take `⟨eT, heT⟩` from `colim_equiv Θ T hTm hTo hTc hTfg`. Use `⟨eT, eF, fun z => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `frac_cover hO (eF z)`. Use `set z' := (Θ.θ (F n) (hFfg n)).symm ⟨eF z, hn⟩`. Establish `hz : mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε (F n).subtype) z' = z` using `eF.injective (by rw [heF, LinearEquiv.apply_symm_apply])`.

Set `red : F n →ₗ[O] T n` to `((toKO O).comp (F n).subtype).codRestrict (T n) fun y => hred n y y.2`. Establish `hredc : Continuous red` using `(toKO_cont.comp continuous_subtype_val).subtype_mk _`. Establish `e3 : mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε) (mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε _) z') = mapH2 (twist ε (T n)) (twist ε (KO O)) (T n).subtype continuous_subtype_val (twist …`. Proceed by induction on `z' using Submodule.Quotient.induction_on with`. Consider the case `H w => rfl`.

Rewrite using `[← hz, e3, heT, Θ.nat _ _ (hFfg n) (hTfg n) red hredc]`. Use `Eq.trans ?_ (congrArg (toKO O) (heF n z')).symm` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem inv_iso (hT : Formalism.GaloisCohomology.LocalTateDualityK) : InvIso := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hε
  obtain ⟨Θ⟩ := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT hK hO i hε
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI := ko_discrete hF
  let F : ℕ → Submodule O (FractionRing O) := fun n =>
    (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  let T : ℕ → Submodule O (KO O) := fun n => LinearMap.ker (LinearMap.lsmul O (KO O) ((p : O) ^ n))
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun n y hy => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hy
    refine Submodule.mem_one.2 ⟨(p : O) * a, ?_⟩
    simp only [LinearMap.lsmul_apply] at ha ⊢
    rw [map_mul, ha, pow_succ, mul_comm _ (p : O), mul_smul, Algebra.smul_def (p : O) (((p : O) ^ n) • y)]
  have hFo : ∀ n, IsOpen (F n : Set (FractionRing O)) := fun n => by
    have : (F n : Set (FractionRing O)) =
        (fun y : FractionRing O => ((p : O) ^ n) • y) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
      ext y; simp [F, Submodule.mem_one]
    rw [this]
    exact hF.emb.isOpen_range.preimage (continuous_const_smul _)
  have hFfg := frac_isFGTop hO hF
  have hred : ∀ n, ∀ y ∈ F n, toKO O y ∈ T n := fun n y hy => by
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply, F, Submodule.mem_comap] at hy ⊢
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy
  have hTm : Monotone T := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [pow_succ, mul_comm, mul_smul, hx, smul_zero]
  have hTo : ∀ n, IsOpen (T n : Set (KO O)) := fun n => isOpen_discrete _
  have hTc : ∀ x, ∃ n, x ∈ T n := fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := frac_cover hO y
    exact ⟨n, hred n y hn⟩
  have hTsurj : ∀ n, (F n).map (toKO O) = T n := fun n => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy => hred n y hy) fun x hx => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨y, ?_, rfl⟩
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hTfg : ∀ n, IsFGTop O (T n) := fun n => by
    refine ⟨?_, inferInstance, inferInstance⟩
    have := (hFfg n).fg
    rw [← hTsurj n, Module.Finite.iff_fg]
    exact Submodule.FG.map _ (Module.Finite.iff_fg.1 this)
  obtain ⟨eF, heF⟩ := colim_equiv Θ F hFm hFo (frac_cover hO) hFfg
  obtain ⟨eT, heT⟩ := colim_equiv Θ T hTm hTo hTc hTfg
  refine ⟨eT, eF, fun z => ?_⟩
  obtain ⟨n, hn⟩ := frac_cover hO (eF z)
  set z' := (Θ.θ (F n) (hFfg n)).symm ⟨eF z, hn⟩
  have hz : mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val
      (twist_map ε (F n).subtype) z' = z := eF.injective (by rw [heF, LinearEquiv.apply_symm_apply])
  let red : F n →ₗ[O] T n := ((toKO O).comp (F n).subtype).codRestrict (T n) fun y => hred n y y.2
  have hredc : Continuous red := (toKO_cont.comp continuous_subtype_val).subtype_mk _
  have e3 : mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε)
      (mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε _) z') =
      mapH2 (twist ε (T n)) (twist ε (KO O)) (T n).subtype continuous_subtype_val (twist_map ε _)
        (mapH2 (twist ε (F n)) (twist ε (T n)) red hredc (twist_map ε red) z') := by
    induction z' using Submodule.Quotient.induction_on with
    | H w => rfl
  rw [← hz, e3, heT, Θ.nat _ _ (hFfg n) (hTfg n) red hredc]
  refine Eq.trans ?_ (congrArg (toKO O) (heF n z')).symm
  rfl

end GlobalTheory.InvColim
