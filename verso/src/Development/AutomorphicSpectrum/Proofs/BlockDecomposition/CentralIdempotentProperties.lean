import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open ReciprocityTheory.Ty.Fin CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

variable {Γ : Type} [Group Γ] [Fintype Γ]

/- English proof (translation)
Rewrite using `[GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩`. Conclude with `⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩`. Introduce and unpack `⟨φ⟩`.

Conclude with `⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩`.
-/
theorem nonempty_iso_iff_equiv (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ Nonempty (Representation.Equiv τ.ρ σ.ρ) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩

/- English proof (translation)
Establish `h` using `centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)`. Rewrite using `[zIdem_eq_centralIdem, h]`. Distinguish the cases in `hc : Nonempty (τ ≅ σ)`. Rewrite using `[if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]`. Rewrite using `[if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]`.
-/
theorem zIdem_act (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by
  have h := centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)
  rw [zIdem_eq_centralIdem, h]
  by_cases hc : Nonempty (τ ≅ σ)
  · rw [if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])`.
-/
theorem eq_of_act (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Γ _ _ τ hτ`. Use `⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [map_mul, zIdem_act τ W hτ hW] split_ifs <;> simp`. Apply the tactic sequence `rw [map_mul, map_mul, zIdem_act τ W hτ hW] split_ifs <;> simp`.

Introduce `Γ _ _ τ σ hτ hσ hne`. Use `eq_of_act _ _ fun W hW => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]`. Distinguish the cases in `h1 : Nonempty (τ ≅ W)`. Distinguish the cases in `h2 : Nonempty (σ ≅ W)`.

Conclude with `absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne`. Simplify using `[h2]`. Simplify using `[h1]`. Introduce `Γ _ _ τ σ hτ hσ hiso`. Rewrite using `[zIdem_act τ σ hτ hσ, if_pos hiso]`.

Introduce `Γ _ _ I _ V hV hinj hex classical`. Use `eq_of_act _ _ fun W hW => ?_` and prove the remaining obligations. Take `⟨i₀, ⟨e⟩⟩` from `hex W hW`. Establish `hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) = if i = i₀ then (1 : Module.End ℂ W) else 0`. Introduce `i`.

Rewrite using `[zIdem_act (V i) W (hV i) hW]`. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Rewrite using `[if_pos ⟨e.symm⟩, if_pos rfl]`. Rewrite using `[if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]`.

Rewrite using `[map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]`. Simplify using the standard rewrite rules.
-/
theorem zIdemFacts : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ hτ
    refine ⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩
    · rw [map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
    · rw [map_mul, map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
  · intro Γ _ _ τ σ hτ hσ hne
    refine eq_of_act _ _ fun W hW => ?_
    rw [map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]
    by_cases h1 : Nonempty (τ ≅ W)
    · by_cases h2 : Nonempty (σ ≅ W)
      · exact absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne
      · simp [h2]
    · simp [h1]
  · intro Γ _ _ τ σ hτ hσ hiso
    rw [zIdem_act τ σ hτ hσ, if_pos hiso]
  · intro Γ _ _ I _ V hV hinj hex
    classical
    refine eq_of_act _ _ fun W hW => ?_
    obtain ⟨i₀, ⟨e⟩⟩ := hex W hW
    have hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) =
        if i = i₀ then (1 : Module.End ℂ W) else 0 := by
      intro i
      rw [zIdem_act (V i) W (hV i) hW]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos ⟨e.symm⟩, if_pos rfl]
      · rw [if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]
    rw [map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]
    simp

end GlobalTheory.CompanionTheory.TyFin
