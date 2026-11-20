import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardUnion
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ N r U hN hU h`. Establish `anti : ∀ {m n : ℕ}, m ≤ n → levU l U n ≤ levU l U m` using `fun hmn => inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti hmn))`. Establish `down : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l), ψ ∈ XDual N (levU l U m) (ZMod l) (ZMod l) → restr (ZMod l) (ZMod l) (anti hmn) ψ ∈ XDual N (levU l U n) (ZMod l) (ZMod l)`. Introduce `m n hmn ψ hψ`. Conclude with `(restrMem F Ω N _ _ (anti hmn) (ZMod l) (ZMod l) 1).1 (Submodule.mem_map_of_mem hψ)`.

Establish `comp : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l), restr (ZMod l) (ZMod l) (cycU_le_levU l U n) (restr (ZMod l) (ZMod l) (anti hmn) ψ) = restr (ZMod l) (ZMod l) (cycU_le_levU l U m) ψ` using `fun _ _ => rfl`. Unfold `XRk`. Set `X` to `XDual N (cycU l U) (ZMod l) (ZMod l)`. Set `S : ℕ → Set X` to `fun n => {φ | ∃ ψ ∈ XDual N (levU l U (n + 2)) (ZMod l) (ZMod l), restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ = (φ : ↥(cycU l U) → ZMod l)}`. Apply `cardUnion X S` to reduce the goal to its premises.

Introduce `m n hmn φ hφ`. Take `⟨ψ, hψ, e⟩` from `hφ`. Establish `hmn' : m + 2 ≤ n + 2` using `by omega`. Conclude with `⟨_, down hmn' ψ hψ, (comp hmn' ψ).trans e⟩`. Introduce `φ`.

Take `⟨n, ψ, hψ, e⟩` from `xdualExt F Ω l N U (ZMod l) (ZMod l) hN hU φ.1 φ.2`. Establish `hn : n ≤ n + 2` using `by omega`. Conclude with `⟨n, _, down hn ψ hψ, (comp hn ψ).trans e⟩`. Introduce `n`. Take `⟨hfin, hcard⟩` from `h (n + 2) (by omega)`.

Set `f : ↥(XDual N (levU l U (n + 2)) (ZMod l) (ZMod l)) → X` to `fun ψ => ⟨restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ.1, (restrMem F Ω N _ _ (cycU_le_levU l U (n + 2)) (ZMod l) (ZMod l) 1).1 (Submodule.mem_map_of_mem ψ.2)⟩`. Establish `hsub : S n ⊆ Set.range f`. Introduce and unpack `φ ⟨ψ, hψ, e⟩`. Conclude with `⟨⟨ψ, hψ⟩, Subtype.ext e⟩`. Use `⟨((Set.finite_range f).subset hsub).to_subtype, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Two.infRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ) (U : Subgroup (G F Ω)), N ≠ 0 → IsClosed (U : Set (G F Ω)) → (∀ n, 2 ≤ n → XRk l N (levU l U n) r) → XRk l N (cycU l U) r := by
  intro F Ω _ _ _ _ _ l _ N r U hN hU h
  have anti : ∀ {m n : ℕ}, m ≤ n → levU l U n ≤ levU l U m := fun hmn =>
    inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti hmn))
  have down : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l),
      ψ ∈ XDual N (levU l U m) (ZMod l) (ZMod l) →
      restr (ZMod l) (ZMod l) (anti hmn) ψ ∈ XDual N (levU l U n) (ZMod l) (ZMod l) := by
    intro m n hmn ψ hψ
    exact (restrMem F Ω N _ _ (anti hmn) (ZMod l) (ZMod l) 1).1 (Submodule.mem_map_of_mem hψ)
  have comp : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l),
      restr (ZMod l) (ZMod l) (cycU_le_levU l U n) (restr (ZMod l) (ZMod l) (anti hmn) ψ)
        = restr (ZMod l) (ZMod l) (cycU_le_levU l U m) ψ := fun _ _ => rfl
  unfold XRk
  let X := XDual N (cycU l U) (ZMod l) (ZMod l)
  let S : ℕ → Set X := fun n => {φ | ∃ ψ ∈ XDual N (levU l U (n + 2)) (ZMod l) (ZMod l),
    restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ = (φ : ↥(cycU l U) → ZMod l)}
  apply cardUnion X S
  · intro m n hmn φ hφ
    obtain ⟨ψ, hψ, e⟩ := hφ
    have hmn' : m + 2 ≤ n + 2 := by omega
    exact ⟨_, down hmn' ψ hψ, (comp hmn' ψ).trans e⟩
  · intro φ
    obtain ⟨n, ψ, hψ, e⟩ := xdualExt F Ω l N U (ZMod l) (ZMod l) hN hU φ.1 φ.2
    have hn : n ≤ n + 2 := by omega
    exact ⟨n, _, down hn ψ hψ, (comp hn ψ).trans e⟩
  · intro n
    obtain ⟨hfin, hcard⟩ := h (n + 2) (by omega)
    let f : ↥(XDual N (levU l U (n + 2)) (ZMod l) (ZMod l)) → X := fun ψ =>
      ⟨restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ.1,
        (restrMem F Ω N _ _ (cycU_le_levU l U (n + 2)) (ZMod l) (ZMod l) 1).1
          (Submodule.mem_map_of_mem ψ.2)⟩
    have hsub : S n ⊆ Set.range f := by
      rintro φ ⟨ψ, hψ, e⟩
      exact ⟨⟨ψ, hψ⟩, Subtype.ext e⟩
    refine ⟨((Set.finite_range f).subset hsub).to_subtype, ?_⟩
    calc Nat.card (S n) ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
      _ ≤ Nat.card ↥(XDual N (levU l U (n + 2)) (ZMod l) (ZMod l)) := Finite.card_range_le f
      _ ≤ l ^ r := hcard
