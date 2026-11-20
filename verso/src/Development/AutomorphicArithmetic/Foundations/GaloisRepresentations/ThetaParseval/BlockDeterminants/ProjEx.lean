import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonFormStatement

open GlobalTheory.UnitaryBC GlobalTheory.DefU

/- English proof (translation)
Set `P : Set (Submodule ℂ V)` to `{C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}`. Establish `hbot : (⊥ : Submodule ℂ V) ∈ P` using `⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _, fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩`. Take `⟨C, -, hC⟩` from `zorn_le_nonempty₀ P (fun c hcP hc y hy => by`. Establish `hdir : DirectedOn (· ≤ ·) c` using `hc.directedOn`. Establish `hne : c.Nonempty` using `⟨y, hy⟩`.

Use `⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Take `⟨z, hz, hvz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hv`. Conclude with `le_sSup hz ((hcP hz).2.1 x v hvz)`. Take `⟨z, hz, hvz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 h`. Conclude with `(hcP hz).2.2 hvz) ⊥ hbot`.

Take `⟨hCA, hCs, hψC⟩` from `hC.prop`. Establish `hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N`. Introduce `N hNA hNs hNC`. Assume the negation of the conclusion as `hn`. Establish `hm : C ⊔ N ∈ P` using `⟨sup_le hCA hNA, fun x v hv => by`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩`. Conclude with `hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))`. Choose the witnesses or unpack the hypotheses as in `⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Conclude with `hψC (sSup_le hn (hAS hψA))`. Establish `hUs` using `hSs U hUS`. Establish `hdisj : C ⊓ U = ⊥`.

Break down `hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (inf_eq_right.1 h) hUC`. Establish `hψU` using `hsup U (hSA U hUS) hUs hUC`. Establish `hAle : A ≤ C ⊔ U`.

Use `hAS.trans (sSup_le fun Y hY => ?_)` and prove the remaining obligations. Distinguish the cases in `hYC : Y ≤ C`. Conclude with `hYC.trans le_sup_left`. Establish `hYs` using `hSs Y hY`. Break down `hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by` into its components or cases.

Take `⟨a, ha, b, hb, e⟩` from `Submodule.mem_sup.1 hv.1`. Rewrite using `[← e, map_add]`. Conclude with `Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h`. It suffices to derive a contradiction. Take `⟨c, hc, y, hy, e⟩` from `Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)`.

Establish `hyCU : y ∈ C ⊔ U`. Establish `: y = ψ - c` using `by rw [← e]; abel`. Rewrite using `[this]`. Conclude with `sub_mem hψU (Submodule.mem_sup_left hc)`. Establish `hy0 : y = 0` using `(Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))`.

Rewrite `e` using `[hy0, add_zero]`. Conclude with `hψC (e ▸ hc)`. Conclude with `inf_eq_right.1 h`. Take `⟨D, hD⟩` from `Submodule.exists_isCompl (C ⊔ U)`. Establish `hc : IsCompl U (C ⊔ D)`.

Use `⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, d, hd, e⟩` from `Submodule.mem_sup.1 hu'`. Establish `hdCU : d ∈ C ⊔ U`. Establish `: d = u - c` using `by rw [← e]; abel`. Rewrite using `[this]`.

Conclude with `sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)`. Establish `hd0 : d = 0` using `Submodule.disjoint_def.1 hD.disjoint d hdCU hd`. Rewrite `e` using `[hd0, add_zero]`. Establish `: u ∈ C ⊓ U` using `⟨e ▸ hc, hu⟩`. Rewrite `this` using `[hdisj]`.

Conclude with `(Submodule.mem_bot ℂ).1 this`. Rewrite using `[codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]`. Conclude with `sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)`. Set `pr : V →ₗ[ℂ] V` to `U.subtype ∘ₗ Submodule.linearProjOfIsCompl U (C ⊔ D) hc`. Establish `hprU : ∀ u ∈ U, pr u = u` using `fun u hu => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)`.

Establish `hprC : ∀ c ∈ C, pr c = 0` using `fun c hc' => by`. Establish `h0 : Submodule.linearProjOfIsCompl U (C ⊔ D) hc c = 0` using `Submodule.linearProjOfIsCompl_apply_right' hc (Submodule.mem_sup_left hc')`. Simplify using `[pr, h0]`. Establish `hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u` using `fun c hc' u hu => by`. Rewrite using `[map_add, hprC c hc', hprU u hu, zero_add]`.

Use `⟨U, hUS, pr, ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨c, hc', u, hu, e⟩` from `Submodule.mem_sup.1 (hAle hψA)`. Rewrite using `[← e, hform c hc' u hu]`. Introduce `h0`. Rewrite `e` using `[h0, add_zero]`.

Conclude with `hψC (e ▸ hc')`. Take `⟨c, hc', u, hu, rfl⟩` from `Submodule.mem_sup.1 (hAle hf)`. Use `⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hform c hc' u hu, map_add, hform _ (hCs x c hc') _ (hUs x u hu)]`.
-/
private theorem proj_of_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G → V →ₗ[ℂ] V)
    (A : Submodule ℂ V) (S : Set (Submodule ℂ V))
    (hSA : ∀ U ∈ S, U ≤ A) (hSs : ∀ U ∈ S, ∀ x, ∀ v ∈ U, ρ x v ∈ U)
    (hSi : ∀ U ∈ S, ∀ N ≤ U, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → N = ⊥ ∨ N = U)
    (hAS : A ≤ sSup S) (ψ : V) (hψA : ψ ∈ A) (hψ : ψ ≠ 0) :
    ∃ U ∈ S, ∃ pr : V →ₗ[ℂ] V, pr ψ ≠ 0 ∧ ∀ f ∈ A, pr f ∈ U ∧ ∀ x, pr (ρ x f) = ρ x (pr f) := by
  classical
  let P : Set (Submodule ℂ V) := {C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}
  have hbot : (⊥ : Submodule ℂ V) ∈ P :=
    ⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _,
      fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨C, -, hC⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hz ((hcP hz).2.1 x v hvz)
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcP hz).2.2 hvz) ⊥ hbot
  obtain ⟨hCA, hCs, hψC⟩ := hC.prop
  have hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N := by
    intro N hNA hNs hNC
    by_contra hn
    have hm : C ⊔ N ∈ P := ⟨sup_le hCA hNA, fun x v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩
    exact hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))
  obtain ⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by
    by_contra hn
    push_neg at hn
    exact hψC (sSup_le hn (hAS hψA))
  have hUs := hSs U hUS
  have hdisj : C ⊓ U = ⊥ := by
    rcases hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_right.1 h) hUC
  have hψU := hsup U (hSA U hUS) hUs hUC
  have hAle : A ≤ C ⊔ U := by
    refine hAS.trans (sSup_le fun Y hY => ?_)
    by_cases hYC : Y ≤ C
    · exact hYC.trans le_sup_left
    have hYs := hSs Y hY
    rcases hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv.1
        rw [← e, map_add]
        exact Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h
    · exfalso
      obtain ⟨c, hc, y, hy, e⟩ := Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)
      have hyCU : y ∈ C ⊔ U := by
        have : y = ψ - c := by rw [← e]; abel
        rw [this]
        exact sub_mem hψU (Submodule.mem_sup_left hc)
      have hy0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))
      rw [hy0, add_zero] at e
      exact hψC (e ▸ hc)
    · exact inf_eq_right.1 h
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C ⊔ U)
  have hc : IsCompl U (C ⊔ D) := by
    refine ⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩
    · obtain ⟨c, hc, d, hd, e⟩ := Submodule.mem_sup.1 hu'
      have hdCU : d ∈ C ⊔ U := by
        have : d = u - c := by rw [← e]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)
      have hd0 : d = 0 := Submodule.disjoint_def.1 hD.disjoint d hdCU hd
      rw [hd0, add_zero] at e
      have : u ∈ C ⊓ U := ⟨e ▸ hc, hu⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot ℂ).1 this
    · rw [codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]
      exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)
  let pr : V →ₗ[ℂ] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U (C ⊔ D) hc
  have hprU : ∀ u ∈ U, pr u = u := fun u hu =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)
  have hprC : ∀ c ∈ C, pr c = 0 := fun c hc' => by
    have h0 : Submodule.linearProjOfIsCompl U (C ⊔ D) hc c = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc (Submodule.mem_sup_left hc')
    simp [pr, h0]
  have hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u := fun c hc' u hu => by
    rw [map_add, hprC c hc', hprU u hu, zero_add]
  refine ⟨U, hUS, pr, ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc', u, hu, e⟩ := Submodule.mem_sup.1 (hAle hψA)
    rw [← e, hform c hc' u hu]
    intro h0
    rw [h0, add_zero] at e
    exact hψC (e ▸ hc')
  · obtain ⟨c, hc', u, hu, rfl⟩ := Submodule.mem_sup.1 (hAle hf)
    refine ⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩
    rw [hform c hc' u hu, map_add, hform _ (hCs x c hc') _ (hUs x u hu)]

/- English proof (translation)
Introduce `E _ _ _ d ψ hψ hψ0`. Take `⟨B₀, -, -, hd, hi⟩` from `GlobalTheory.T.exists_invariant_positive_petersson_form E d`. Take `⟨p, hp⟩` from `LinearMap.exists_leftInverse_of_injective (autU E d).subtype (autU E d).ker_subtype`. Establish `hpv : ∀ (φ : UA E d → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩` using `fun φ h => LinearMap.congr_fun hp (⟨φ, h⟩ : autU E d)`. Set `B : (UA E d → ℂ) →ₗ⋆[ℂ] (UA E d → ℂ) →ₗ[ℂ] ℂ` to `(B₀.compl₂ p).comp p`.

Establish `hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ')` using `fun _ _ => rfl`. Establish `hsum : ∀ φ : UA E d → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U}`. Introduce `φ hφ`. Establish `h` using `UpperTheory.mem_iSup_automorphicReps_of_invariant_form E d B (fun f hf h0 => by`. Rewrite `h0` using `[hB, hpv f hf]`.

Conclude with `congrArg Subtype.val (hd _ h0))`. Use the proof step `(fun x f g hf hg => by`. Rewrite using `[hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]`. Conclude with `hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ`. Conclude with `(iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U}) h`.

Take `⟨U, hU, pr, h1, h2⟩` from `proj_of_sum (fun x => RU E d x) (autU E d) {U | IsAutRepU U} (fun U hU φ hφ => hU.aut φ hφ) (fun U hU => hU.stable) (fun U hU => hU.irred) (fun φ hφ => hsum φ hφ) ψ hψ hψ0`. Conclude with `⟨U, pr, hU, h1, fun f hf => h2 f hf⟩`.
-/
theorem UpperTheory.TP.projEx :
    UpperTheory.TP.ProjEx := by
  intro E _ _ _ d ψ hψ hψ0
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E d
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E d).subtype (autU E d).ker_subtype
  have hpv : ∀ (φ : UA E d → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E d)
  let B : (UA E d → ℂ) →ₗ⋆[ℂ] (UA E d → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E d → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E d B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U}) h
  obtain ⟨U, hU, pr, h1, h2⟩ := proj_of_sum (fun x => RU E d x) (autU E d)
    {U | IsAutRepU U} (fun U hU φ hφ => hU.aut φ hφ) (fun U hU => hU.stable)
    (fun U hU => hU.irred) (fun φ hφ => hsum φ hφ) ψ hψ hψ0
  exact ⟨U, pr, hU, h1, fun f hf => h2 f hf⟩
