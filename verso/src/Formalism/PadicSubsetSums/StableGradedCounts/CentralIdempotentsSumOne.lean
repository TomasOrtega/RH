import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

namespace CISum

open Classical in
/- English proof (translation)
Use `hρ.1` as an intermediate fact. Use `hσ.1` as an intermediate fact. Establish `hirrρ : ρ.IsIrreducible` using `isIrreducible_of ρ hρ.2`. Establish `hirrσ : σ.IsIrreducible` using `isIrreducible_of σ hσ.2`. Establish `hc0 : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)`. Use `set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc`. Establish `e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g`. Unfold `centralIdem`. Simplify using `[map_sum]`.

Both sides reduce to the same expression. Take `⟨μ, hμ⟩` from `schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by`. Introduce `g k`. Establish `: (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹` using `by group`. Simplify using `only [this, Representation.char_conj])`.

Establish `htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹`. Establish `h1` using `congrArg (LinearMap.trace ℂ W) hμ`. Simplify using `only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1`. Rewrite using `[← h1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring`.

Establish `horth` using `Representation.char_orthonormal σ ρ`. Rewrite `horth` using `[Nat.card_eq_fintype_card]`. Establish `hd : (Module.finrank ℂ W : ℂ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℂ) (M := W)).ne'` after adjusting the coercions. Rewrite using `[e, hμ]`.

Use `split_ifs with hiso`. Rewrite `horth` using `[if_pos hiso]`. Take `⟨φ⟩` from `hiso`. Establish `hdim : Module.finrank ℂ V = Module.finrank ℂ W` using `φ.toLinearEquiv.finrank_eq`. Establish `hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ)`.

Clear denominators, using `at horth` for the nonvanishing conditions. Simplify using `using horth`. Rewrite `htr` using `[hsum, hc, hdim, div_mul_cancel₀ _ hc0]`. Establish `: μ = 1`. Use `mul_right_cancel₀ hd (htr.trans (one_mul _).symm)` as an intermediate fact.

Conclude with `this`. Rewrite using `[this, one_smul]`. Rewrite `horth` using `[if_neg hiso]`. Establish `hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0`. Simplify `horth` using `[hc0]`.

Rewrite `htr` using `[hsum, mul_zero]`. Rewrite using `[(mul_eq_zero.mp htr).resolve_right hd, zero_smul]`.
-/
theorem centralIdem_act {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  have := hρ.1
  have := hσ.1
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ.2
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ.2
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc
  have e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g := by
    unfold centralIdem
    simp [map_sum]
    rfl
  obtain ⟨μ, hμ⟩ := schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by
    intro g k
    have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    simp only [this, Representation.char_conj])
  have htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹ := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring
  have horth := Representation.char_orthonormal σ ρ
  rw [Nat.card_eq_fintype_card] at horth
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  rw [e, hμ]
  split_ifs with hiso
  · rw [if_pos hiso] at horth
    obtain ⟨φ⟩ := hiso
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ) := by
      field_simp at horth
      simpa using horth
    rw [hsum, hc, hdim, div_mul_cancel₀ _ hc0] at htr
    have : μ = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, one_smul]
  · rw [if_neg hiso] at horth
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc0] using horth
    rw [hsum, mul_zero] at htr
    rw [(mul_eq_zero.mp htr).resolve_right hd, zero_smul]

/- English proof (translation)
Unfold `Representation.IsIrreducible at h`. Use `⟨?_, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Conclude with `(bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))`.

Break down `h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1` into its components or cases. Use `left`. Conclude with `congrArg Subrepresentation.toSubmodule h1`. Use `right`. Conclude with `congrArg Subrepresentation.toSubmodule h1`.
-/
theorem isIrr_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by
  unfold Representation.IsIrreducible at h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
    · left
      exact congrArg Subrepresentation.toSubmodule h1
    · right
      exact congrArg Subrepresentation.toSubmodule h1

end CISum

open CISum in
set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `G I _ _ _ V _ _ _ ρ hirr hne hfull`. Use `set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz`. Establish `hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z`. Introduce `x`. Rewrite using `[hz, Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `(hirr i).1` as an intermediate fact. Conclude with `(central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x`. Establish `hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1`. Introduce `W _ _ _ σ hσ`.

Take `⟨i₀, φ, hφ⟩` from `hfull W σ hσ`. Rewrite using `[hz, map_sum, Finset.sum_eq_single i₀]`. Rewrite using `[centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]`. Conclude with `⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩`. Introduce `i _ hi`.

Rewrite using `[centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]`. Introduce and unpack `⟨ψ⟩`. Apply `hi` to reduce the goal to its premises. Apply `hne` to reduce the goal to its premises. Use `⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩` and prove the remaining obligations.

Establish `h1 : ψ (ρ i g x) = σ g (ψ x)` using `LinearMap.congr_fun (ψ.isIntertwining' g) x`. Simplify using `only [LinearEquiv.trans_apply]`. Use `erw [h1]`. Conclude with `hφ g _`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `: NeZero (Nat.card G : ℂ)` using `⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩`. Set `N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)` to `{ carrier := {x | z * x = x} add_mem' := by`. Introduce `x y hx hy`. Simplify using `only [Set.mem_ofPred_eq] at hx hy ⊢`.

Rewrite using `[mul_add, hx, hy]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `a x hx`. Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢`.

Rewrite using `[← mul_assoc, hcentral a, mul_assoc, hx] }`. Establish `hN : N = ⊤`. Rewrite using `[eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)]`. Apply `sSup_le` to reduce the goal to its premises. Introduce `S hS x hx`.

Establish `hS' : IsSimpleModule (MonoidAlgebra ℂ G) S` using `hS`. Establish `hirrS` using `(Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'`. Establish `hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S)`. Set `ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G` to `{ toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) : MonoidAlgebra ℂ G) map_add' := by intro a b; simp map_smul' := by`. Introduce `c y`.

Simplify using `[RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }`. Use `Module.Finite.of_injective ι ?_` and prove the remaining obligations. Introduce `a b hab`. Conclude with `(RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)`. Establish `h1` using `hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)`.

Establish `h2` using `LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)`. Rewrite `h2` using `[Representation.ofModule_asAlgebraHom_apply_apply]`. Establish `h3` using `(RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2`. Establish `h4 : z * x = x` using `by simpa using congrArg Subtype.val h3`. Conclude with `h4`.

Establish `h1 : (1 : MonoidAlgebra ℂ G) ∈ N` using `hN ▸ Submodule.mem_top`. Establish `h2 : z * 1 = 1` using `h1`. Rewrite `h2` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem central_idempotents_sum_one : CentralIdemSumOne := by
  intro G I _ _ _ V _ _ _ ρ hirr hne hfull
  classical
  set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz
  have hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z := by
    intro x
    rw [hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hirr i).1
    exact (central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x

  have hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1 := by
    intro W _ _ _ σ hσ
    obtain ⟨i₀, φ, hφ⟩ := hfull W σ hσ
    rw [hz, map_sum, Finset.sum_eq_single i₀]
    · rw [centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]
      exact ⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩
    · intro i _ hi
      rw [centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]
      rintro ⟨ψ⟩
      apply hi
      apply hne
      refine ⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩
      have h1 : ψ (ρ i g x) = σ g (ψ x) := LinearMap.congr_fun (ψ.isIntertwining' g) x
      simp only [LinearEquiv.trans_apply]
      erw [h1]
      exact hφ g _
    · intro h; exact absurd (Finset.mem_univ _) h
  have : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  let N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {x | z * x = x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_add, hx, hy]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc, hcentral a, mul_assoc, hx] }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)]
    apply sSup_le
    intro S hS x hx
    have hS' : IsSimpleModule (MonoidAlgebra ℂ G) S := hS
    have hirrS := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'
    have hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) := by
      let ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G :=
        { toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) :
            MonoidAlgebra ℂ G)
          map_add' := by intro a b; simp
          map_smul' := by
            intro c y
            simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
      refine Module.Finite.of_injective ι ?_
      intro a b hab
      exact (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)
    have h1 := hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)
    have h2 := LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    have h3 := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2
    have h4 : z * x = x := by simpa using congrArg Subtype.val h3
    exact h4
  have h1 : (1 : MonoidAlgebra ℂ G) ∈ N := hN ▸ Submodule.mem_top
  have h2 : z * 1 = 1 := h1
  rwa [mul_one] at h2

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
