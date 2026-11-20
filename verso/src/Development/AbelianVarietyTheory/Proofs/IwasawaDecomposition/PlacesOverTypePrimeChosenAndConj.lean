import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesOverG

/- English proof (translation)
Introduce `x y hxy`. Establish `hy : y = GlobalTheory.IdemSupport.cO D x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hxy, GlobalTheory.IdemSupport.cO_coe]`. Conclude with `(Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm`.

Rewrite using `[GlobalTheory.IdemSupport.mem_cP, hy, GlobalTheory.IdemSupport.cO_cO]`.
-/
theorem isConjPl_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.IdemSupport.cP (D := D) P) := by
  intro x y hxy
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [GlobalTheory.IdemSupport.mem_cP, hy, GlobalTheory.IdemSupport.cO_cO]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]`.
-/
theorem conjPrime_conjPrime₂ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.IdemSupport.cP (D := D) (GlobalTheory.IdemSupport.cP (D := D) P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

/- English proof (translation)
Establish `h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord` using `D.host.finrank_cmField`. Establish `h5 : D.R.f = 2 * D.R.ord` using `rfl`. Rewrite using `[h1, h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_E' (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

/- English proof (translation)
Introduce `D k`. Use `set f := Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) with hf`. Establish `hne : ∀ v v', D.naut.plGw k v ≠ GlobalTheory.IdemSupport.cP (D` using `D) (D.naut.plGw k v') := fun v v' e => D.naut.plGw_nconj k v' v (e ▸ isConjPl_cP _)`. Establish `hinj : Function.Injective f`. Introduce and unpack `(a | a) (b | b) e`.

Simplify using `only [hf, Sum.elim_inl] at e`. Rewrite using `[D.naut.plGw_inj k e]`. Simplify using `only [hf, Sum.elim_inl, Sum.elim_inr] at e`. Conclude with `absurd e (hne a b)`. Simplify using `only [hf, Sum.elim_inl, Sum.elim_inr] at e`.

Conclude with `absurd e.symm (hne b a)`. Simplify using `only [hf, Sum.elim_inr] at e`. Use `congrArg (GlobalTheory.IdemSupport.cP (D := D)) e` as an intermediate fact. Rewrite `this` using `[conjPrime_conjPrime₂, conjPrime_conjPrime₂]`. Rewrite using `[D.naut.plGw_inj k this]`.

Establish `hmem : ∀ i, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (f i).asIdeal`. Introduce and unpack `(v | v)`. Conclude with `D.naut.plGw_over k v`. Use `show _ ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)).asIdeal`. Rewrite using `[GlobalTheory.IdemSupport.mem_cP, map_natCast]`.

Conclude with `D.naut.plGw_over k v`. Establish `hcard : Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E`. Rewrite using `[Fintype.card_sum, D.nd.card_PlG k, finrank_E', two_mul]`. Use `⟨hinj, fun W => ⟨fun hW => ?_, ?_⟩, hcard⟩` and prove the remaining obligations. Establish `hfin : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).Finite`.

Apply `Set.finite_of_ncard_ne_zero` to reduce the goal to its premises. Rewrite using `[D.nd.g_split k]`. Conclude with `Module.finrank_pos.ne'`. Establish `hsub : Set.range f ⊆ Formalism.BasicNotions.placesOver D.host.E (D.host.g k)`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hmem i`. Establish `hle : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).ncard ≤ (Set.range f).ncard`. Rewrite using `[D.nd.g_split k, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard]`. Establish `heq` using `Set.eq_of_subset_of_ncard_le hsub hle hfin`. Establish `: W ∈ Set.range f` using `by rw [heq]; exact hW`.

Conclude with `this`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `hmem i`.
-/
theorem places_over_g_k : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  intro D k
  set f := Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) with hf
  have hne : ∀ v v', D.naut.plGw k v ≠ GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_cP _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e
    · simp only [hf, Sum.elim_inl] at e; rw [D.naut.plGw_inj k e]
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e (hne a b)
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e.symm (hne b a)
    · simp only [hf, Sum.elim_inr] at e
      have := congrArg (GlobalTheory.IdemSupport.cP (D := D)) e
      rw [conjPrime_conjPrime₂, conjPrime_conjPrime₂] at this
      rw [D.naut.plGw_inj k this]
  have hmem : ∀ i, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (f i).asIdeal := by
    rintro (v | v)
    · exact D.naut.plGw_over k v
    · show _ ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)).asIdeal
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact D.naut.plGw_over k v
  have hcard : Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
    rw [Fintype.card_sum, D.nd.card_PlG k, finrank_E', two_mul]
  refine ⟨hinj, fun W => ⟨fun hW => ?_, ?_⟩, hcard⟩
  · have hfin : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [D.nd.g_split k]; exact Module.finrank_pos.ne'
    have hsub : Set.range f ⊆ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := by
      rintro _ ⟨i, rfl⟩; exact hmem i
    have hle : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).ncard ≤ (Set.range f).ncard := by
      rw [D.nd.g_split k, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard]
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
    have : W ∈ Set.range f := by rw [heq]; exact hW
    exact this
  · rintro ⟨i, rfl⟩; exact hmem i

end GlobalTheory.PlacesOverG
