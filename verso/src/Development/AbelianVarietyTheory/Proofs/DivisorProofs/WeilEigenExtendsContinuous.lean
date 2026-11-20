import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ThK.ModelLocInt

open scoped Classical
open Filter GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one (m : ℕ) : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Establish `hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w` using `fun w => by`. Establish `h` using `GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w`. Rewrite `h` using `[← (hvm w).2]`. Take `⟨ψ, hψ, e⟩` from `Submodule.mem_map.mp h`. Conclude with `⟨ψ, hψ, e⟩`.

Set `ψs : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ` to `fun w => if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose`. Establish `hψSB : ∀ w, ψs w ∈ SB _` using `fun w => by`. Distinguish the cases in `h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w`. Simplify using `only [ψs, if_pos h]`. Conclude with `(hM.vac w).1`.

Simplify using `only [ψs, if_neg h]`. Conclude with `(hpre w).choose_spec.1`. Establish `hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w` using `fun w => by`. Distinguish the cases in `h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w`. Simplify using `only [ψs, if_pos h]`.

Rewrite using `[(hvm w).1, h]`. Simplify using `only [ψs, if_neg h]`. Conclude with `(hpre w).choose_spec.2`. Establish `hψM : ∀ᶠ w in cofinite, ψs w = M.vac w` using `by filter_upwards [hM₁.std] with w hw`. Simplify using `only [ψs, if_pos hw]`.

Establish `hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `by filter_upwards [hψM, hM.std] with w h1 h2`. Rewrite using `[h1, h2]`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by`. Take `⟨f, hf⟩` from `DFunLike.ne_iff.mp hei`. Conclude with `⟨f, by simpa using hf⟩`.

Establish `hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ` using `Fin n × Fin d) w) = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind`. Take `⟨ρ₁, hρ₁, hρt₁⟩` from `GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind`. Establish `hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ` using `fun φ hφ => by`. Use `⟨hρ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hρt φ]`. Use `GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hψSB w`. Establish `hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁` using `fun φ hφ => by`. Use `⟨hρ₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[hρt₁ φ]`. Use `GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `GlobalTheory.StdVacuum.indicator_mem_SB w`. Establish `key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁` using `fun φ hφ => by`. Rewrite using `[hρt φ, hρt₁ (ev v φ)]`.

Establish `hSB : ∀ w, Function.update ψs v φ w ∈ SB _` using `fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ`.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `hψSB w`. Establish `hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w` using `by filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2`. Rewrite using `[Function.update_of_ne h2, h1]`. Rewrite using `[hloc f _ hSB hcof]`.

Use `congr 1`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`.

Rewrite using `[Function.update_of_ne hw, Function.update_of_ne hw, hψev w]`. Establish `canc` using `GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁`. Establish `h1` using `he.Heisenberg₂ z _ (hRest φ hφ).2`. Rewrite `h1` using `[incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]`. Rewrite `h1` using `[hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ]`.

Establish `hevφ : ev v φ ∈ SB _`. Rewrite using `[← (hvm v).2]`. Conclude with `Submodule.mem_map_of_mem hφ`. Rewrite `h1` using `[hA₁ ρ₁ (hRest₁ _ hevφ)]`. Conclude with `canc _ _ h1`.
-/
theorem heis_loc {B : Base F E} {M M₁ : Model σ X W} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n d} (he : IsEv B M M₁ 1 1 ∅ e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB _)
    (φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₁ : φ₁ ∈ SB _) (hA : Acts (evFin F v) (M.co.rho B.ψ z) φ φ₁)
    (χ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hA₁ : Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁) :
    ev v φ₁ = χ₁ := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
  have hevφ : ev v φ ∈ SB _ := by
    rw [← (hvm v).2]
    exact Submodule.mem_map_of_mem hφ
  rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
  exact canc _ _ h1

def ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k))

/- English proof (translation)
Introduce `a ha`. Unfold `ptAt`. Rewrite using `[← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]`. Use `congr 1`. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations.

Conclude with `GlobalTheory.LatVac.at_liftV v _ a ha`. Conclude with `GlobalTheory.LatVac.at_liftV v _ a ha`.
-/
theorem at_ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    At (evFin F v) (ptAt M v w) := by
  intro a ha
  unfold ptAt
  rw [← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]
  congr 1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · exact GlobalTheory.LatVac.at_liftV v _ a ha

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>`. Simplify using `[ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]`.
-/
theorem locCo_ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    GlobalTheory.LatVac.locCo M.co v (ptAt M v w) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.ThK.ModelLocInt

open GlobalTheory.ThK.ModelLocInt in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _`. Take `rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v` from `Subsingleton.elim _ _`. Establish `hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v`. Use extensionality with `t`. Conclude with `(GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm`.

Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)`. Rewrite using `[hψe]`. Conclude with `GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v`. Use `⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v, fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩` and prove the remaining obligations. Establish `hA` using `GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ`.

Rewrite `hA` using `[locCo_ptAt]`. Establish `hA₁` using `GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)`. Conclude with `heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁`.
-/
theorem GlobalTheory.ThK.ModelLocInt.exists_loc_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl F) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _
  obtain rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v :=
    by
    ext t
    exact (GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := by
    rw [hψe]; exact GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v
  refine ⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v,
    fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ
  rw [locCo_ptAt] at hA
  have hA₁ := GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)
  exact heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _
    (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁
