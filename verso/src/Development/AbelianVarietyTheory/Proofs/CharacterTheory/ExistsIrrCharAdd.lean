import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwiningStatement
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Establish `hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧ Module.finrank K S.toSubmodule = m` using `⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩`. Take `⟨S, hS, hm⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ → Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule`. Introduce `T hT`. Rewrite using `[hm]`.

Conclude with `Nat.find_min' hex ⟨T, hT, rfl⟩`. Establish `: Nontrivial S.toSubmodule` using `Submodule.nontrivial_iff_ne_bot.mpr hS`. Use `⟨S, ?_⟩` and prove the remaining obligations. Establish `: Nontrivial (Subrepresentation S.toRepresentation)` using `⟨⊥, ⊤, fun h => by`. Establish `h' : (⊥ : Submodule K S.toSubmodule) = ⊤` using `congrArg Subrepresentation.toSubmodule h`.

Conclude with `bot_ne_top h'⟩`. Use `⟨fun T => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hT : T.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hT)`. Use `right`.

Set `T' : Subrepresentation ρ` to `⟨T.toSubmodule.map S.toSubmodule.subtype, by`. Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Conclude with `⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩`. Establish `hT' : T'.toSubmodule ≠ ⊥`. Introduce `h`.

Apply `hT` to reduce the goal to its premises. Establish `h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥` using `h`. Rewrite `h2` using `[← Submodule.map_bot S.toSubmodule.subtype, (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff]`. Then use the resulting hypothesis. Establish `h1` using `hmin T' hT'`. Establish `h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule` using `Submodule.finrank_map_subtype_eq _ _`.

Establish `h3 : T.toSubmodule = ⊤` using `Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))`. Conclude with `Subrepresentation.toSubmodule_injective h3`.
-/
theorem exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

/- English proof (translation)
Introduce `K L _ _ _ G _ a ha h0`. Take `⟨n, ρ, hρ⟩` from `ha`. Establish `hn : Nontrivial (Fin n → K)`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`.

Apply `h0` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `: ρ g = 0` using `Subsingleton.elim _ _`. Simplify using `[hρ, Representation.character, this]`. Take `⟨S, hS⟩` from `exists_irreducible_subrepresentation ρ`.

Set `f : Representation.IntertwiningMap S.toRepresentation ρ` to `⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩`. Take `⟨c, hc, hcg⟩` from `GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f S.toSubmodule.injective_subtype`. Use `⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Rewrite using `[hρ, hcg]`.

Both sides reduce to the same expression.
-/
theorem exists_irrChar_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl

end GlobalTheory.BI
