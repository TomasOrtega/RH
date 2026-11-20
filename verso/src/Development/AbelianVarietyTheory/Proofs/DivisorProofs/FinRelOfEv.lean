import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.IsoUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

open scoped Classical in

/- English proof (translation)
Establish `hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w` using `fun w => by`. Establish `h` using `GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n₁ × Fin d₁) w`. Rewrite `h` using `[← (hvm w).2]`. Take `⟨ψ, hψ, e⟩` from `Submodule.mem_map.mp h`. Conclude with `⟨ψ, hψ, e⟩`.

Set `ψs : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ` to `fun w => if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose`. Establish `hψSB : ∀ w, ψs w ∈ SB _` using `fun w => by`. Distinguish the cases in `h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w`. Simplify using `only [ψs, if_pos h]`. Conclude with `(hM.vac w).1`.

Simplify using `only [ψs, if_neg h]`. Conclude with `(hpre w).choose_spec.1`. Establish `hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w` using `fun w => by`. Distinguish the cases in `h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w`. Simplify using `only [ψs, if_pos h]`.

Rewrite using `[(hvm w).1, h]`. Simplify using `only [ψs, if_neg h]`. Conclude with `(hpre w).choose_spec.2`. Establish `hψM : ∀ᶠ w in cofinite, ψs w = M.vac w` using `by filter_upwards [hM₁.std] with w hw`. Simplify using `only [ψs, if_pos hw]`.

Establish `hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `by filter_upwards [hψM, hM.std] with w h1 h2`. Rewrite using `[h1, h2]`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by`. Take `⟨f, hf⟩` from `DFunLike.ne_iff.mp hei`. Conclude with `⟨f, by simpa using hf⟩`.

Establish `hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ` using `Fin n₁ × Fin d₁) w) = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind`. Take `⟨ρ₁, hρ₁, hρt₁⟩` from `GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind`. Establish `hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ` using `fun φ hφ => by`. Use `⟨hρ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hρt φ]`. Use `GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hψSB w`. Establish `hRest₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁` using `fun φ hφ => by`. Use `⟨hρ₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[hρt₁ φ]`. Use `GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `GlobalTheory.StdVacuum.indicator_mem_SB w`. Establish `key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁` using `fun φ hφ => by`. Rewrite using `[hρt φ, hρt₁ (ev v φ)]`.

Establish `hSB : ∀ w, Function.update ψs v φ w ∈ SB _` using `fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ`.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `hψSB w`. Establish `hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w` using `by filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2`. Rewrite using `[Function.update_of_ne h2, h1]`. Rewrite using `[hloc f _ hSB hcof]`.

Use `congr 1`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`.

Rewrite using `[Function.update_of_ne hw, Function.update_of_ne hw, hψev w]`. Establish `canc` using `GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁`. Establish `h1` using `he.Heisenberg₂ z _ (hRest φ hφ).2`.

Rewrite `h1` using `[hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ]`. Establish `hevφ : ev v φ ∈ SB _`. Rewrite using `[← (hvm v).2]`. Conclude with `Submodule.mem_map_of_mem hφ`. Rewrite `h1` using `[hA₁ ρ₁ (hRest₁ _ hevφ)]`.

Conclude with `canc _ _ h1`. Introduce `u hu hz φ hφ φ₁ hφ₁ hA`. Establish `h1` using `he.inv u hu _ (hRest φ hφ).2`. Rewrite `h1` using `[hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ]`. Conclude with `canc _ _ h1`.
-/
theorem finRel_of_ev {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (he : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl F) : GlobalTheory.ThK.EvUniqB.FinRel B M M₁ ι ι' I v (ev v) := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n₁ × Fin d₁) w
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
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n₁ × Fin d₁) w) =
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
  have hRest₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
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
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁
    have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    have hevφ : ev v φ ∈ SB _ := by
      rw [← (hvm v).2]
      exact Submodule.mem_map_of_mem hφ
    rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
    exact canc _ _ h1
  · intro u hu hz φ hφ φ₁ hφ₁ hA
    have h1 := he.inv u hu _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    exact canc _ _ h1

open GlobalTheory.ThK.EvUniqInf in
open scoped Classical in

/- English proof (translation)
Establish `hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧ ev v p = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧ (M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → p = M.vac v)`. Introduce `v`. Distinguish the cases in `h : M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Conclude with `⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩`. Establish `hmem : Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v)`.

Rewrite using `[(hloc0 v).2]`. Conclude with `GlobalTheory.StdVacuum.indicator_mem_SB v`. Take `⟨p, hp, hpe⟩` from `Submodule.mem_map.1 hmem`. Conclude with `⟨p, hp, hpe, fun h' => absurd h' h⟩`. Use `choose φ hφSB hφev hφvac using hex`.

Establish `hcof : ∀ᶠ v in cofinite, φ v = M.vac v` using `by filter_upwards [hM₁.std] with v hv`. Conclude with `hφvac v hv`. Establish `hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `by filter_upwards [hcof, hM.std] with v h1 h2`. Rewrite using `[h1, h2]`. Establish `hevφ : (fun v => ev v (φ v)) = fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`.

Use function extensionality and compare the values at `hφev`. Establish `hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i))` using `fun g => rest_pure g φ hφSB hstd`. Establish `hRest₁ : ∀ g : SInf F (Fin n₁ × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i))` using `fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)`. Establish `he : ∀ g : SInf F (Fin n × Fin d), e (pure g φ) = pure (ei g) (fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)`. Introduce `g`.

Rewrite using `[hloc g φ hφSB hcof, hevφ]`. Use `⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩` and prove the remaining obligations. Establish `h1` using `hev.Heisenberg₂ z (pure f φ) (hRest f).2`. Establish `h2 : M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ) (pure f φ) = pure f₁ φ` using `hA _ (hRest f)`. Rewrite `h1` using `[h2, he, he]`.

Establish `h3 : M₁.co.rho B.ψ z (pure (ei f) (fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) = pure g₁ (fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)` using `hA₁ _ (hRest₁ (ei f))`. Conclude with `eq_of_pure_std _ _ (h1.trans h3)`. Establish `h1` using `hev.inv u hu (pure f φ) (hRest f).2`. Establish `h2 : M.co.rho B.ψ u (pure f φ) = pure f₁ φ` using `hA _ (hRest f)`. Rewrite `h1` using `[h2, he, he]`.

Conclude with `eq_of_pure_std _ _ h1`.
-/
theorem infRel_of_ev {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E}
    {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (hev : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hloc0 : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) :
    GlobalTheory.ThK.EvUniqB.InfRel B M M₁ ι ι' I ei := by

  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => rest_pure g φ hφSB hstd
  have hRest₁ : ∀ g : SInf F (Fin n₁ × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v,
      Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i)) :=
    fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)
  have he : ∀ g : SInf F (Fin n × Fin d), e (pure g φ) = pure (ei g) (fun v =>
      Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hloc g φ hφSB hcof, hevφ]
  refine ⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩
  · have h1 := hev.Heisenberg₂ z (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ) (pure f φ) = pure f₁ φ :=
      hA _ (hRest f)
    rw [h2, he, he] at h1
    have h3 : M₁.co.rho B.ψ z (pure (ei f) (fun v =>
        Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) = pure g₁ (fun v =>
        Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :=
      hA₁ _ (hRest₁ (ei f))
    exact eq_of_pure_std _ _ (h1.trans h3)
  · have h1 := hev.inv u hu (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ u (pure f φ) = pure f₁ φ := hA _ (hRest f)
    rw [h2, he, he] at h1
    exact eq_of_pure_std _ _ h1

end GlobalTheory.ThK.IsoUniq
