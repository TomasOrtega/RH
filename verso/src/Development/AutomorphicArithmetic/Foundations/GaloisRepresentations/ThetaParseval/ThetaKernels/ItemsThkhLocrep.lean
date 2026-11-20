import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocRepExK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKH.Locrep
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d B X W M om hP v`. Take `⟨χX, χW, hw⟩` from `hP.weil`. Establish `hs` using `IsUWeilPair.isUSplitting hw`. Establish `hstd` using `hP.base.std`. Establish `hne : B.ψ ≠ 1` using `fun h => GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hstd v (by rw [h]; rfl)`.

Establish `hH` using `(GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) B.ψ hstd.1 hne hstd.2.1).1`. Take `⟨r₀, x₀, h₀, h₁⟩` from `exists_base (Fin n × Fin d) v`. Set `loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v)` to `fun T => res v x₀ ∘ₗ T ∘ₗ tensL v r₀`. Establish `hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀))` using `fun _ _ => rfl`. Establish `pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _` using `fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)`.

Establish `presH : ∀ u, ∀ φ ∈ SB _, loc (schrL B.ψ (M.co.e u)) φ ∈ SB _` using `fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)`. Establish `acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ)`. Introduce `g hg h hh φ hφ`. Use `acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)` and prove the remaining obligations. Take `⟨u, rfl⟩` from `M.co.e.surjective w`.

Establish `hu : atPlace v (1 : Fv F v) • u = 0`. Apply `M.co.e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, map_zero]`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `atPlace v 1 * (M.co.e u).1 i = 0`.

Rewrite using `[atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]`. Express the relevant statement in the definitionally equal form `atPlace v 1 * (M.co.e u).2 i = 0`. Rewrite using `[atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]`. Use `hs.impl (g, h) u Φ hΦ` as an intermediate fact. Rewrite `this` using `[show actAB (cA σ) (g, h) u = u from act_away hg hh hu]`. Then use the resulting hypothesis.

Establish `actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, Acts (evFin F v) (M.co.rho B.ψ u) φ (loc (schrL B.ψ (M.co.e u)) φ)`. Introduce `u hu φ hφ`. Establish `e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0` using `fun a ha => by rw [← map_smul, hu a ha, map_zero]`. Establish `A : Acts (evFin F v) (M.co.rho B.ψ u) φ _` using `fun r hr => GlobalTheory.SchrLoc.schr_tens_of_at B.ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i) (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1`. Use `eq_of_acts v h₁ (h₀ φ hφ) A` as an intermediate fact.

Rewrite `A` using `[this]`. Conclude with `A`. Establish `one : ∀ φ ∈ SB _, loc (om 1) φ = φ` using `fun φ hφ => (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm`. Establish `mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ)` using `fun p g' hg' h' hh' φ hφ => by`. Rewrite using `[hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]`.

Both sides reduce to the same expression. Use `⟨fun p => loc (om p), fun u => loc (schrL B.ψ (M.co.e u)), fun g _ h _ => pres _, fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one, fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u, fun u hu φ hφ φ₁ => ⟨fun A => e …` and prove the remaining obligations. Take `⟨K, hK1, hK2, hK3, hK4⟩` from `exists_small_subgroups σ W v`. Take `⟨m, hm⟩` from `smooth_of_weak (SB _) K hK1 hK2 (fun h => loc (om (1, h))) (fun h _ => pres _) one (fun h _ h' hh' φ hφ => by`. Use `mul (1, h) 1 (one_mem_UAt X v) h' (hK3 0 hh') φ hφ` as an intermediate fact.

Rewrite using `[Prod.mk_mul_mk, one_mul] at this)` and apply the resulting hypothesis. Use the proof step `(fun l φ hφ => (hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2).comp (continuous_const.prodMk continuous_id)) φ hφ`. Take `⟨U, hU, hUK⟩` from `hK4 m`. Conclude with `⟨U, hU, fun h hh hv => hm h (hUK h hh hv)⟩`. Express the relevant statement in the definitionally equal form `loc (om (g, h)) (loc (schrL B.ψ (M.co.e u)) φ) = loc (schrL B.ψ (M.co.e _)) (loc (om (g, h)) φ)`.

Rewrite using `[hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ), ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]`. Both sides reduce to the same expression.
-/
theorem locRepEx_k : _root_.PositivityTheory.ThK.LocRepEx_k := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v
  obtain ⟨χX, χW, hw⟩ := hP.weil
  have hs := IsUWeilPair.isUSplitting hw
  have hstd := hP.base.std
  have hne : B.ψ ≠ 1 := fun h => GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hstd v (by rw [h]; rfl)
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) B.ψ hstd.1 hne hstd.2.1).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v) := fun T =>
    res v x₀ ∘ₗ T ∘ₗ tensL v r₀
  have hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _ := fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)
  have presH : ∀ u, ∀ φ ∈ SB _, loc (schrL B.ψ (M.co.e u)) φ ∈ SB _ := fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ) := by
    intro g hg h hh φ hφ
    refine acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)
    obtain ⟨u, rfl⟩ := M.co.e.surjective w
    have hu : atPlace v (1 : Fv F v) • u = 0 := by
      apply M.co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change atPlace v 1 * (M.co.e u).1 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]
      · change atPlace v 1 * (M.co.e u).2 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]
    have := hs.impl (g, h) u Φ hΦ
    rwa [show actAB (cA σ) (g, h) u = u from act_away hg hh hu] at this
  have actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      Acts (evFin F v) (M.co.rho B.ψ u) φ (loc (schrL B.ψ (M.co.e u)) φ) := by
    intro u hu φ hφ
    have e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
    have A : Acts (evFin F v) (M.co.rho B.ψ u) φ _ := fun r hr =>
      GlobalTheory.SchrLoc.schr_tens_of_at B.ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i)
        (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1
    have := eq_of_acts v h₁ (h₀ φ hφ) A
    rw [this] at A
    exact A
  have one : ∀ φ ∈ SB _, loc (om 1) φ = φ := fun φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm
  have mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ) := fun p g' hg' h' hh' φ hφ => by
    rw [hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]
    rfl
  refine ⟨fun p => loc (om p), fun u => loc (schrL B.ψ (M.co.e u)), fun g _ h _ => pres _,
    fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one,
    fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u,
    fun u hu φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ actsH u hu φ hφ⟩,
    fun g hg h hh u hu φ hφ => ?_⟩
  · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ W v
    obtain ⟨m, hm⟩ := smooth_of_weak (SB _) K hK1 hK2 (fun h => loc (om (1, h))) (fun h _ => pres _) one
      (fun h _ h' hh' φ hφ => by
        have := mul (1, h) 1 (one_mem_UAt X v) h' (hK3 0 hh') φ hφ
        rwa [Prod.mk_mul_mk, one_mul] at this)
      (fun l φ hφ => (hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2).comp (continuous_const.prodMk continuous_id)) φ hφ
    obtain ⟨U, hU, hUK⟩ := hK4 m
    exact ⟨U, hU, fun h hh hv => hm h (hUK h hh hv)⟩
  · change loc (om (g, h)) (loc (schrL B.ψ (M.co.e u)) φ) = loc (schrL B.ψ (M.co.e _)) (loc (om (g, h)) φ)
    rw [hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ),
      ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]
    rfl
end PositivityTheory.ThKH.Locrep
end
end
