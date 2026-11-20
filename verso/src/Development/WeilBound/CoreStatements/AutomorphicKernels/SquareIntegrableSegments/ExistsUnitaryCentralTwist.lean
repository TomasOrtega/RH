import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.PfEss.H2

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Use `haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr`. Apply `(bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises.

Use extensionality with `v`. Rewrite using `[Subsingleton.elim v 0]`. Conclude with `⟨fun _ => (⊤ : Subrepresentation σ.ρ).toSubmodule.zero_mem, fun _ => (⊥ : Subrepresentation σ.ρ).toSubmodule.zero_mem⟩`.
-/
private theorem nontrivial_irrRep_V {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) :
    Nontrivial σ.V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
  apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => (⊤ : Subrepresentation σ.ρ).toSubmodule.zero_mem,
    fun _ => (⊥ : Subrepresentation σ.ρ).toSubmodule.zero_mem⟩

/- English proof (translation)
Use `haveI hnt : Nontrivial σ.V := nontrivial_irrRep_V σ`. Use `haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr`. Take `⟨v0, hv0⟩` from `exists_ne (0 : σ.V)`. Establish `hinv : ∀ (g : GL (Fin n) k) (v : σ.V), σ.ρ g⁻¹ (σ.ρ g v) = v`. Introduce `g v`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Set `S : Subgroup (GL (Fin n) k)` to `{ carrier := {g | σ.ρ g v0 = v0} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Combine the equalities or inequalities in the displayed calculation.

Establish `hSopen : IsOpen (S : Set (GL (Fin n) k))` using `σ.smooth v0`. Set `K : Subgroup (GL (Fin n) k)` to `KO k (Fin n) ⊓ S`. Establish `hKo : IsOpen (K : Set (GL (Fin n) k))`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `GlobalTheory.SplitFlip.isOpen_KO.inter hSopen`.

Establish `hKc : IsCompact (K : Set (GL (Fin n) k))` using `GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) (fun x hx => (Subgroup.mem_inf.mp hx).1)`. Use `haveI hfd : FiniteDimensional ℂ (fixed σ.ρ K) := hadm.2 K hKo hKc`. Establish `hv0K : v0 ∈ fixed σ.ρ K` using `by show ∀ h : K, σ.ρ h v0 = ((1 : K →* ℂˣ) h : ℂ) • v0`. Introduce `h`. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`.

Conclude with `(Subgroup.mem_inf.mp h.2).2`. Establish `hcomm : ∀ (t : kˣ) (g : GL (Fin n) k), Matrix.GeneralLinearGroup.scalar (Fin n) t * g = g * Matrix.GeneralLinearGroup.scalar (Fin n) t`. Introduce `t g`. Use extensionality with `: 1`. Simplify using `only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]`.

Conclude with `Matrix.scalar_commute _ (fun _ => Commute.all _ _) _`. Establish `key : ∀ t : kˣ, ∃ c : ℂ, ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v = c • v`. Introduce `t`. Use `set s := Matrix.GeneralLinearGroup.scalar (Fin n) t with hs`. Establish `hρc : ∀ g v, σ.ρ s (σ.ρ g v) = σ.ρ g (σ.ρ s v)`.

Introduce `g v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]`. Establish `hW : ∀ w ∈ fixed σ.ρ K, σ.ρ s w ∈ fixed σ.ρ K`. Introduce `w hw`. Establish `hw' : ∀ h : K, σ.ρ h w = ((1 : K →* ℂˣ) h : ℂ) • w` using `hw`.

Use `show ∀ h : K, σ.ρ h (σ.ρ s w) = ((1 : K →* ℂˣ) h : ℂ) • (σ.ρ s w)`. Introduce `h`. Use `hw' h` as an intermediate fact. Rewrite `this`, the goal using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Rewrite using `[← hρc, this]`.

Set `f : Module.End ℂ (fixed σ.ρ K)` to `(σ.ρ s).restrict hW`. Use `haveI : Nontrivial (fixed σ.ρ K) := ⟨⟨⟨v0, hv0K⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue f`. Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`. Set `E : Subrepresentation σ.ρ` to `{ toSubmodule := LinearMap.ker (σ.ρ s - c • LinearMap.id) apply_mem_toSubmodule := by`.

Introduce `g v hv`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢`. Rewrite using `[hρc, hv, map_smul] }`. Break down `IsSimpleOrder.eq_bot_or_eq_top E with hE | hE` into its components or cases. It suffices to derive a contradiction.

Establish `hwE : (w : σ.V) ∈ E.toSubmodule`. Simplify using `only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `congrArg Subtype.val hw.apply_eq_smul`. Rewrite `hwE` using `[hE]`. Conclude with `hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).mp hwE))`.

Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Establish `hvE : v ∈ (⊤ : Subrepresentation σ.ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `hvE` using `[← hE]`. Simplify `hvE` using `[E, sub_eq_zero]`. Use `choose c hc using key`.

Establish `huniq : ∀ a b : ℂ, a • v0 = b • v0 → a = b` using `fun a b h => smul_left_injective ℂ hv0 h`. Establish `hc0 : ∀ t, c t ≠ 0`. Introduce `t h`. Establish `h1` using `hc t v0`. Rewrite `h1` using `[h, zero_smul]`.

Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hinv (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0, h1, map_zero]`. Establish `hmul : ∀ a b, c (a * b) = c a * c b`. Introduce `a b`. Apply `huniq` to reduce the goal to its premises.

Rewrite using `[← hc, map_mul, map_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul, mul_comm]`. Establish `hone : c 1 = 1`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[← hc, map_one, map_one, Module.End.one_apply, one_smul]`. Set `ω : kˣ →* ℂˣ` to `{ toFun := fun t => Units.mk0 (c t) (hc0 t) map_one' := Units.ext (by simp [hone]) map_mul' := fun a b => Units.ext (by simp [hmul]) }`.

Establish `hcont : Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k)`. Apply `Units.continuous_iff.mpr` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Simplify using `only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)`.

Simplify using `only [Matrix.GeneralLinearGroup.scalar, Units.coe_map_inv, MonoidHom.coe_coe, map_inv]`. Conclude with `Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)`. Use `⟨ω, ?_, fun z v => hc z v⟩` and prove the remaining obligations. Use `show IsOpen (ω.ker : Set kˣ)`. Establish `hker : (ω.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ⁻¹' (S : Set (GL (Fin n) k))`.

Use extensionality with `t`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]`. Use `show Units.mk0 (c t) (hc0 t) = 1 ↔ σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0 = v0`. Rewrite using `[hc t v0, Units.ext_iff, Units.val_mk0, Units.val_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h, one_smul]`. Introduce `h`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[h, one_smul]`.

Rewrite using `[hker]`. Conclude with `hSopen.preimage hcont`.
-/
private theorem exists_smooth_central_character_of_admissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (σ : IrrRep (GL (Fin n) k)) (hadm : IsAdmissible σ.ρ) :
    ∃ ω : kˣ →* ℂˣ, IsSmoothChar ω ∧ HasCentralChar σ.ρ ω := by
  classical
  haveI hnt : Nontrivial σ.V := nontrivial_irrRep_V σ
  haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
  obtain ⟨v0, hv0⟩ := exists_ne (0 : σ.V)
  have hinv : ∀ (g : GL (Fin n) k) (v : σ.V), σ.ρ g⁻¹ (σ.ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | σ.ρ g v0 = v0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        calc σ.ρ a⁻¹ v0 = σ.ρ a⁻¹ (σ.ρ a v0) := by rw [ha]
          _ = v0 := hinv a v0 }
  have hSopen : IsOpen (S : Set (GL (Fin n) k)) := σ.smooth v0
  let K : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := by
    rw [Subgroup.coe_inf]
    exact GlobalTheory.SplitFlip.isOpen_KO.inter hSopen
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo)
      (fun x hx => (Subgroup.mem_inf.mp hx).1)
  haveI hfd : FiniteDimensional ℂ (fixed σ.ρ K) := hadm.2 K hKo hKc
  have hv0K : v0 ∈ fixed σ.ρ K := by
    show ∀ h : K, σ.ρ h v0 = ((1 : K →* ℂˣ) h : ℂ) • v0
    intro h
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact (Subgroup.mem_inf.mp h.2).2
  have hcomm : ∀ (t : kˣ) (g : GL (Fin n) k),
      Matrix.GeneralLinearGroup.scalar (Fin n) t * g = g * Matrix.GeneralLinearGroup.scalar (Fin n) t := by
    intro t g
    ext : 1
    simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
  have key : ∀ t : kˣ, ∃ c : ℂ, ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v = c • v := by
    intro t
    set s := Matrix.GeneralLinearGroup.scalar (Fin n) t with hs
    have hρc : ∀ g v, σ.ρ s (σ.ρ g v) = σ.ρ g (σ.ρ s v) := by
      intro g v
      rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    have hW : ∀ w ∈ fixed σ.ρ K, σ.ρ s w ∈ fixed σ.ρ K := by
      intro w hw
      have hw' : ∀ h : K, σ.ρ h w = ((1 : K →* ℂˣ) h : ℂ) • w := hw
      show ∀ h : K, σ.ρ h (σ.ρ s w) = ((1 : K →* ℂˣ) h : ℂ) • (σ.ρ s w)
      intro h
      have := hw' h
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
      rw [← hρc, this]
    let f : Module.End ℂ (fixed σ.ρ K) := (σ.ρ s).restrict hW
    haveI : Nontrivial (fixed σ.ρ K) :=
      ⟨⟨⟨v0, hv0K⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    let E : Subrepresentation σ.ρ :=
      { toSubmodule := LinearMap.ker (σ.ρ s - c • LinearMap.id)
        apply_mem_toSubmodule := by
          intro g v hv
          simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
            sub_eq_zero] at hv ⊢
          rw [hρc, hv, map_smul] }
    rcases IsSimpleOrder.eq_bot_or_eq_top E with hE | hE
    · exfalso
      have hwE : (w : σ.V) ∈ E.toSubmodule := by
        simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero]
        exact congrArg Subtype.val hw.apply_eq_smul
      rw [hE] at hwE
      exact hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).mp hwE))
    · refine ⟨c, fun v => ?_⟩
      have hvE : v ∈ (⊤ : Subrepresentation σ.ρ).toSubmodule := Submodule.mem_top
      rw [← hE] at hvE
      simpa [E, sub_eq_zero] using hvE
  choose c hc using key
  have huniq : ∀ a b : ℂ, a • v0 = b • v0 → a = b := fun a b h => smul_left_injective ℂ hv0 h
  have hc0 : ∀ t, c t ≠ 0 := by
    intro t h
    have h1 := hc t v0
    rw [h, zero_smul] at h1
    apply hv0
    rw [← hinv (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0, h1, map_zero]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply huniq
    rw [← hc, map_mul, map_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul, mul_comm]
  have hone : c 1 = 1 := by
    apply huniq
    rw [← hc, map_one, map_one, Module.End.one_apply, one_smul]
  let ω : kˣ →* ℂˣ :=
    { toFun := fun t => Units.mk0 (c t) (hc0 t)
      map_one' := Units.ext (by simp [hone])
      map_mul' := fun a b => Units.ext (by simp [hmul]) }
  have hcont : Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) := by
    apply Units.continuous_iff.mpr
    constructor
    · simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
    · simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map_inv, MonoidHom.coe_coe, map_inv]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)
  refine ⟨ω, ?_, fun z v => hc z v⟩
  show IsOpen (ω.ker : Set kˣ)
  have hker : (ω.ker : Set kˣ) =
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ⁻¹' (S : Set (GL (Fin n) k)) := by
    ext t
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
    show Units.mk0 (c t) (hc0 t) = 1 ↔ σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0 = v0
    rw [hc t v0, Units.ext_iff, Units.val_mk0, Units.val_one]
    constructor
    · intro h
      rw [h, one_smul]
    · intro h
      apply huniq
      rw [h, one_smul]
  rw [hker]
  exact hSopen.preimage hcont

/- English proof (translation)
Introduce `k _ _ _ _ y`. Take `⟨ω, hωs, hω⟩` from `exists_smooth_central_character_of_admissible y.fst y.snd.rep (hA k y.fst y.snd.rep.V y.snd.rep.ρ y.snd.rep.smooth y.snd.rep.irr)`. Take `⟨r, hr⟩` from `GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs`. Use `set s' : ℝ := -(r / (y.fst : ℝ)) with hs'`. Use `⟨absPow k (s' : ℂ), GlobalTheory.LocGL.isSmoothChar_absPow _, fun t c hsc => ?_⟩` and prove the remaining obligations.

Establish `hsc' : ∀ v, (y.nu (s' : ℂ)).rep (Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t) v = c • v` using `hsc`. Establish `hcc` using `GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu y hω (s' : ℂ)`. Use `haveI : Nontrivial (y.nu (s' : ℂ)).snd.rep.V := nontrivial_irrRep_V _`. Take `⟨v0, hv0⟩` from `exists_ne (0 : (y.nu (s' : ℂ)).snd.rep.V)`. Distinguish the cases in `hn : y.fst = 0`.

Establish `hn' : (y.nu (s' : ℂ)).fst = 0` using `hn`. Establish `h1` using `hsc' v0`. Establish `hs1 : Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t = 1`. Use extensionality with `i j`. Conclude with `absurd i.2 (by omega)`.

Rewrite `h1` using `[hs1, map_one, Module.End.one_apply]`. Establish `hc1 : c = 1` using `smul_left_injective ℂ hv0 (by show c • v0 = (1 : ℂ) • v0; rw [one_smul]; exact h1.symm)`. Rewrite using `[hc1, norm_one]`. Establish `hc : c = ((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ)` using `smul_left_injective ℂ hv0 ((hsc' v0).symm.trans (hcc t v0))`. Rewrite using `[hc]`.

Establish `hpos : 0 < ‖((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ)‖` using `norm_pos_iff.mpr (Units.ne_zero _)`. Establish `hL` using `GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow ω s' y.fst t`. Rewrite `hL` using `[hr t, Real.log_rpow (GlobalTheory.SplitWeil.nabs_pos k t)]`. Apply `Real.eq_one_of_pos_of_log_eq_zero hpos` to reduce the goal to its premises. Rewrite using `[hL, hs']`.

Establish `hn0 : (y.fst : ℝ) ≠ 0` using `by exact_mod_cast hn`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_unitary_central_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL k), ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ y
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_central_character_of_admissible y.fst y.snd.rep
    (hA k y.fst y.snd.rep.V y.snd.rep.ρ y.snd.rep.smooth y.snd.rep.irr)
  obtain ⟨r, hr⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  set s' : ℝ := -(r / (y.fst : ℝ)) with hs'
  refine ⟨absPow k (s' : ℂ), GlobalTheory.LocGL.isSmoothChar_absPow _, fun t c hsc => ?_⟩
  have hsc' : ∀ v, (y.nu (s' : ℂ)).rep (Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t) v = c • v :=
    hsc
  have hcc := GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu y hω (s' : ℂ)
  haveI : Nontrivial (y.nu (s' : ℂ)).snd.rep.V := nontrivial_irrRep_V _
  obtain ⟨v0, hv0⟩ := exists_ne (0 : (y.nu (s' : ℂ)).snd.rep.V)
  by_cases hn : y.fst = 0
  · have hn' : (y.nu (s' : ℂ)).fst = 0 := hn
    have h1 := hsc' v0
    have hs1 : Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t = 1 := by
      ext i j
      exact absurd i.2 (by omega)
    rw [hs1, map_one, Module.End.one_apply] at h1
    have hc1 : c = 1 := smul_left_injective ℂ hv0 (by show c • v0 = (1 : ℂ) • v0; rw [one_smul]; exact h1.symm)
    rw [hc1, norm_one]
  · have hc : c = ((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ) :=
      smul_left_injective ℂ hv0 ((hsc' v0).symm.trans (hcc t v0))
    rw [hc]
    have hpos : 0 < ‖((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    have hL := GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow ω s' y.fst t
    rw [hr t, Real.log_rpow (GlobalTheory.SplitWeil.nabs_pos k t)] at hL
    apply Real.eq_one_of_pos_of_log_eq_zero hpos
    rw [hL, hs']
    have hn0 : (y.fst : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring

end PositivityTheory.PfEss.H2

end
