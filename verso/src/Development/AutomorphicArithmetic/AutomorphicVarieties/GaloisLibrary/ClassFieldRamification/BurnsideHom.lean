import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.PhiLe

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `p _ P _ _ hP K hK`. Break down `IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Take `⟨hMn, hMi, -⟩` from `UpperTheory.V.CF.phiLe p P hP M hM`.

Establish `hcardQ : Nat.card (P ⧸ M) = p` using `by rw [← Subgroup.index_eq_card, hMi]`. Establish `hcardZ : Nat.card (Multiplicative (ZMod p)) = p` using `by simp`. Set `e : (P ⧸ M) ≃* Multiplicative (ZMod p)` to `mulEquivOfPrimeCardEq hcardQ hcardZ`. Set `f : P →* Multiplicative (ZMod p)` to `e.toMonoidHom.comp (QuotientGroup.mk' M)`. Establish `hKf : K ≤ f.ker`.

Introduce `x hx`. Rewrite using `[MonoidHom.mem_ker]`. Establish `: (QuotientGroup.mk' M x) = 1` using `(QuotientGroup.eq_one_iff x).mpr (hKM hx)`. Use `show e (QuotientGroup.mk' M x) = 1`. Rewrite using `[this, map_one]`.

Establish `hf1` using `hK f hKf`. Apply `hM.1` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : f x = 1` using `by rw [hf1]; rfl`.

Establish `: QuotientGroup.mk' M x = 1` using `e.injective (by simpa [f] using hx)`. Conclude with `(QuotientGroup.eq_one_iff x).mp this`.
-/
theorem UpperTheory.V.CF.burnsideHom :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, (∀ f : P →* Multiplicative (ZMod p), K ≤ f.ker → f = 1) → K = ⊤ := by
  intro p _ P _ _ hP K hK
  rcases IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩
  · exact h
  exfalso
  obtain ⟨hMn, hMi, -⟩ := UpperTheory.V.CF.phiLe p P hP M hM
  have hcardQ : Nat.card (P ⧸ M) = p := by rw [← Subgroup.index_eq_card, hMi]
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by simp
  let e : (P ⧸ M) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardQ hcardZ
  let f : P →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hKf : K ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : (QuotientGroup.mk' M x) = 1 := (QuotientGroup.eq_one_iff x).mpr (hKM hx)
    show e (QuotientGroup.mk' M x) = 1
    rw [this, map_one]
  have hf1 := hK f hKf
  apply hM.1
  rw [eq_top_iff]
  intro x _
  have hx : f x = 1 := by rw [hf1]; rfl
  have : QuotientGroup.mk' M x = 1 := e.injective (by simpa [f] using hx)
  exact (QuotientGroup.eq_one_iff x).mp this
