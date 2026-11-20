import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

open Module

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `W hn hfin hne hW`. Distinguish the cases in `hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Conclude with `⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩`. Use `push_neg at hs`. Take `⟨i, hi⟩` from `hs`. Use `haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne`.

Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))`. Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Use `set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'`. Establish `hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x`. Introduce `x`.

Simplify using `[hW', sub_eq_zero]`. Establish `hle : W' ≤ W` using `inf_le_left`. Establish `hlt : W' < W`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `heq`.

Take `⟨x, hx, hne'⟩` from `hi μ`. Conclude with `hne' ((hmem x).1 (by rw [heq]; exact hx)).2`. Use `haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle`. Establish `hlt' : finrank ℂ W' < n` using `hn ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hne' : W' ≠ ⊥`.

Introduce `hbot`. Establish `hv0 : (v : E) ∈ W'` using `(hmem _).2 ⟨v.2, by`. Use `hv.apply_eq_smul` as an intermediate fact. Simplify using `using congrArg Subtype.val this⟩`. Rewrite `hv0` using `[hbot, Submodule.mem_bot]`.

Conclude with `hv.2 (Subtype.ext hv0)`. Establish `hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W'`. Introduce `j x hx`. Rewrite `hx`, the goal using `[hmem]`. Use `⟨hW j x hx.1, ?_⟩` and prove the remaining obligations.

Establish `h1` using `LinearMap.congr_fun (hT i j) x`. Simplify using `only [LinearMap.comp_apply] at h1`. Rewrite using `[h1, hx.2, map_smul]`. Take `⟨x, hx, hx0, hc⟩` from `ih _ hlt' W' rfl inferInstance hne' hW'inv`. Conclude with `⟨x, hle hx, hx0, hc⟩`.
-/
private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

/- English proof (translation)
Introduce `Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv`. Set `T : Z → (H → V) →ₗ[ℂ] (H → V)` to `fun z => { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a`. Introduce `a b`. Use `LinearMap.ext fun Φ => funext fun g => ?_` and prove the remaining obligations.

Use `show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)`. Rewrite using `[mul_assoc, mul_assoc, hζ a (ζ b)]`. Take `⟨Φ, hΦM, hΦ0, hc⟩` from `exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)`. Use `choose c hc using hc`. Establish `hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g` using `fun z g => congrFun (hc z) g`.

Take `⟨g0, hg0⟩` from `Function.ne_iff.mp hΦ0`. Establish `hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b` using `fun a b h => smul_left_injective ℂ hg0 h`. Establish `hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g` using `hM hΦM`. Establish `h1 : c 1 = 1`. Apply `hscal` to reduce the goal to its premises.

Rewrite using `[← hcg 1 g0, map_one, mul_one, one_smul]`. Establish `hmul : ∀ a b, c (a * b) = c a * c b`. Introduce `a b`. Apply `hscal` to reduce the goal to its premises. Rewrite using `[← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]`.

Set `χ : Z →* ℂ` to `{ toFun := c, map_one' := h1, map_mul' := hmul }`. Use `⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z g`. Conclude with `hcg z g`. Introduce `z hz`.

Apply `Units.ext` to reduce the goal to its premises. Use `show c z = 1`. Apply `hscal` to reduce the goal to its premises. Rewrite using `[← hcg z g0, hF.2 _ hz g0, one_smul]`. Introduce `z γ a hzγ hξ show c z = a`.

Apply `hscal` to reduce the goal to its premises. Rewrite using `[← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
