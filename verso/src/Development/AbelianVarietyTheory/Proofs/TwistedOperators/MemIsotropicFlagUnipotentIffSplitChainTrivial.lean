import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChain

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
The claim follows from `funext fun _ => map_sub _ _ _`.
-/
theorem splitVec_sub' (τ : E →ₐ[F] Fv F v) (y z : Fin V.rank → Fv F v ⊗[F] E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

variable (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v)

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hu`. Use `⟨act hc V g y - y, hg.2 y hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) = _`. Rewrite using `[splitVec_sub', splitVec_matHom_mulVec]`.
-/
theorem wPart_sub_of_mem_trivOn {A B : Submodule E V.V} {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (hg : g ∈ trivOn hc V (Fv F v) A B) {u : Fin V.rank → Fv F v} (hu : u ∈ wPart τ B) :
    (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨act hc V g y - y, hg.2 y hy, ?_⟩
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) = _
  rw [splitVec_sub', splitVec_matHom_mulVec]

variable (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram)

include h hJ in

/- English proof (translation)
Use `(mem_trivOn_iff_maps hAB).2 fun y hy => ?_` and prove the remaining obligations. Rewrite `hy`, the goal using `[mem_extSub_iff_split hc h τ]`. Express the relevant statement in the definitionally equal form `splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _ ∧ splitVec (τ.comp hc.sig) ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _`. Rewrite using `[splitVec_sub', splitVec_sub', splitVec_matHom_mulVec, splitVec_matHom_mulVec]`. Use `⟨h1 _ hy.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_wPart_comp_iff hc h hJ τ]`. Introduce `u hu`. Take `⟨u₀, hu₀, rfl⟩` from `h3 u hu`. Establish `e` using `(mem_wPart_comp_iff hc h hJ τ).1 hy.2 _ (h2 u₀ hu₀)`. Rewrite `e` using `[Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero]`.

Rewrite using `[sub_dotProduct, pairing_splitHom, e, sub_self]`.
-/
theorem mem_trivOn_of_wPart {A B : Submodule E V.V} (hAB : A ≤ B) {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (h1 : ∀ u ∈ wPart τ B, (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A)
    (h2 : ∀ u ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ (perp V B))
    (h3 : ∀ u ∈ wPart τ (perp V A), ∃ u₀ ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u) :
    g ∈ trivOn hc V (Fv F v) A B := by
  refine (mem_trivOn_iff_maps hAB).2 fun y hy => ?_
  rw [mem_extSub_iff_split hc h τ] at hy ⊢
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _ ∧
    splitVec (τ.comp hc.sig) ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _
  rw [splitVec_sub', splitVec_sub', splitVec_matHom_mulVec, splitVec_matHom_mulVec]
  refine ⟨h1 _ hy.1, ?_⟩
  rw [mem_wPart_comp_iff hc h hJ τ]
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := h3 u hu
  have e := (mem_wPart_comp_iff hc h hJ τ).1 hy.2 _ (h2 u₀ hu₀)
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at e
  rw [sub_dotProduct, pairing_splitHom, e, sub_self]

variable (𝔉 : IsoFlag V)

/- English proof (translation)
Use `i.2` as an intermediate fact. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]`. Apply the tactic sequence `exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))`. Apply the tactic sequence `rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]`.

Apply the tactic sequence `exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))`.
-/
theorem flagChain_step_lo (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = i) :
    flagChain 𝔉 τ j.succ = wPart τ (𝔉.X i.succ) ∧ flagChain 𝔉 τ j.castSucc = wPart τ (𝔉.X i.castSucc) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]`. Apply the tactic sequence `exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))`. Apply the tactic sequence `rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]`. Apply the tactic sequence `exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))`.
-/
theorem flagChain_step_mid (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V 𝔉.top) ∧ flagChain 𝔉 τ j.castSucc = wPart τ 𝔉.top := by
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

/- English proof (translation)
Use `i.2` as an intermediate fact. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]`. Apply the tactic sequence `exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))`. Apply the tactic sequence `rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]`.

Apply the tactic sequence `exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))`.
-/
theorem flagChain_step_hi (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) + i = 2 * 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V (𝔉.X i.castSucc)) ∧
      flagChain 𝔉 τ j.castSucc = wPart τ (perp V (𝔉.X i.succ)) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))

end GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act) in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g`. Prove the components needed by the constructor for the conclusion. Introduce `hg j u hu`. Simplify using `only [IsoFlag.unip, Subgroup.mem_inf, Subgroup.mem_iInf] at hg`. Take `⟨⟨hlo, hmid⟩, hhi⟩` from `hg`.

Use `j.2` as an intermediate fact. Break down `lt_trichotomy (j : ℕ) 𝔉.k with hj | hj | hj` into its components or cases. Take `⟨e1, e2⟩` from `GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 ⟨j, hj⟩ j rfl`. Rewrite `hu` using `[e1]`. Rewrite using `[e2]`.

Conclude with `GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hlo _) hu`. Take `⟨e1, e2⟩` from `GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 j hj`. Rewrite `hu` using `[e1]`. Rewrite using `[e2]`. Conclude with `GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ hmid hu`.

Take `⟨e1, e2⟩` from `GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 ⟨2 * 𝔉.k - j, by omega⟩ j (show (j : ℕ) + (2 * 𝔉.k - j) = 2 * 𝔉.k by omega)`. Rewrite `hu` using `[e1]`. Rewrite using `[e2]`. Conclude with `GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hhi _) hu`. Introduce `H`.

Establish `hstab : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j`. Introduce `j u hu`. Break down `Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩` into its components or cases. Rewrite `hu`, the goal using `[GlobalTheory.SplitFlag.flagChain_zero, Submodule.mem_bot]`. Rewrite using `[hu, Matrix.mulVec_zero]`.

Use `GlobalTheory.SplitFlag.flagChain_mono 𝔉 τ (Fin.castSucc_le_succ j') (H j' u hu)` as an intermediate fact. Simplify using `using add_mem this hu`. Establish `hsurj : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, ∃ u₀ ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u` using `fun j u hu => GlobalTheory.SplitFlag.exists_mulVec_eq_of_maps _ _ (hstab j) u hu`. Rewrite using `[IsoFlag.mem_unip]`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations.

Use `i.2` as an intermediate fact. Take `⟨e1, e2⟩` from `GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 i ⟨i, by omega⟩ rfl`. Take `⟨e3, e4⟩` from `GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 i ⟨2 * 𝔉.k - i, by omega⟩ (show 2 * 𝔉.k - (i : ℕ) + i = 2 * 𝔉.k by omega)`. Use `GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ (𝔉.le_succ i) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← e1, ← e2]`.

Conclude with `H _`. Rewrite using `[← e3, ← e4]`. Conclude with `H _`. Rewrite using `[← e3]`. Conclude with `hsurj _`.

Take `⟨e1, e2⟩` from `GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 ⟨𝔉.k, by omega⟩ rfl`. Use `GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ 𝔉.iso ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← e1, ← e2]`. Conclude with `H _`. Rewrite using `[GlobalTheory.SplitFlag.perp_perp, ← e1, ← e2]`.

Conclude with `H _`. Rewrite using `[← e1]`. Conclude with `hsurj _`.
-/
theorem GlobalTheory.SplitFlag.mem_unip_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    simp only [IsoFlag.unip, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    obtain ⟨⟨hlo, hmid⟩, hhi⟩ := hg
    have := j.2
    rcases lt_trichotomy (j : ℕ) 𝔉.k with hj | hj | hj
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 ⟨j, hj⟩ j rfl
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hlo _) hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 j hj
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ hmid hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 ⟨2 * 𝔉.k - j, by omega⟩ j
        (show (j : ℕ) + (2 * 𝔉.k - j) = 2 * 𝔉.k by omega)
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hhi _) hu
  · intro H
    have hstab : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        (splitHom hc.sig V.gram τ g).1 *ᵥ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
      intro j u hu
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [GlobalTheory.SplitFlag.flagChain_zero, Submodule.mem_bot] at hu ⊢
        rw [hu, Matrix.mulVec_zero]
      · have := GlobalTheory.SplitFlag.flagChain_mono 𝔉 τ (Fin.castSucc_le_succ j') (H j' u hu)
        simpa using add_mem this hu
    have hsurj : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        ∃ u₀ ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u :=
      fun j u hu => GlobalTheory.SplitFlag.exists_mulVec_eq_of_maps _ _ (hstab j) u hu
    rw [IsoFlag.mem_unip]
    refine ⟨fun i => ?_, ?_⟩
    · have := i.2
      obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 i ⟨i, by omega⟩ rfl
      obtain ⟨e3, e4⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 i ⟨2 * 𝔉.k - i, by omega⟩
        (show 2 * 𝔉.k - (i : ℕ) + i = 2 * 𝔉.k by omega)
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ (𝔉.le_succ i) ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [← e3, ← e4]; exact H _
      · rw [← e3]; exact hsurj _
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 ⟨𝔉.k, by omega⟩ rfl
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ 𝔉.iso ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [GlobalTheory.SplitFlag.perp_perp, ← e1, ← e2]; exact H _
      · rw [← e1]; exact hsurj _
