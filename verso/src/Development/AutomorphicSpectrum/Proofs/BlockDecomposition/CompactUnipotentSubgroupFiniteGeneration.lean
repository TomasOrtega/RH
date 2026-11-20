import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenExact

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem mem_span_openFns_of_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ Q hQ hex θ hθ f hf hker
  let σ : Representation ℂ Q (IndSp (stdBlocks d hd) ρ) := (parInd (stdBlocks d hd) ρ).comp Q.subtype
  have hI : ∀ t : Q, ∀ v ∈ openFns d hd ρ, σ t v ∈ openFns d hd ρ := by
    intro t v hv g hg
    have h1 : v.1.1 (g * (t : GL (Fin N) k)) ≠ 0 := hg
    obtain ⟨p, hp, n, hn, e⟩ := hv _ h1
    show ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k (wOpen d hd) * n
    refine ⟨p, hp, n * (t : GL (Fin N) k)⁻¹, mul_mem hn (inv_mem (hQ t.2)), ?_⟩
    rw [← mul_assoc, ← e]
    group
  have hσs : IsSmooth σ := fun v => (isSmooth_parInd (stdBlocks d hd) ρ v).preimage continuous_subtype_val
  let ρ' : Representation ℂ Q (openFns d hd ρ) := GlobalTheory.PRep.sub σ (openFns d hd ρ) hI
  have hρs : IsSmooth ρ' := by
    intro v
    have : {t : Q | ρ' t v = v} = {t : Q | σ t (v : IndSp (stdBlocks d hd) ρ) = v} := by
      ext t
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hσs _
  let θ' : (⊤ : Subgroup Q) →* ℂˣ := θ.comp (⊤ : Subgroup Q).subtype
  have hopen : IsOpen (θ'.ker : Set (⊤ : Subgroup Q)) := by
    have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
      GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
    let j : (⊤ : Subgroup Q) → unipB k (Fin N) := fun x => ⟨x.1.1, hQ x.1.2⟩
    have hj : Continuous j :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hset : (θ'.ker : Set (⊤ : Subgroup Q)) = j ⁻¹' ((whitChar ψ N).ker : Set (unipB k (Fin N))) := by
      ext x
      show θ x.1 = 1 ↔ whitChar ψ N (j x) = 1
      rw [hθ x.1 (hQ x.1.2)]
    rw [hset]
    exact hw.preimage hj
  have hexh : ∀ s : Finset Q, (↑s : Set Q) ⊆ (⊤ : Subgroup Q) →
      ∃ L : Subgroup Q, L ≤ ⊤ ∧ (↑s : Set Q) ⊆ L ∧ IsCompact (L : Set Q) := by
    classical
    intro s _
    obtain ⟨L, hLQ, hsL, hLc⟩ := hex (s.image Subtype.val) (by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2)
    refine ⟨L.subgroupOf Q, le_top, ?_, ?_⟩
    · intro x hx
      refine Subgroup.mem_subgroupOf.2 (hsL ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · rw [Subtype.isCompact_iff]
      have himg : ((↑) : Q → GL (Fin N) k) '' (L.subgroupOf Q : Set Q) = (L : Set (GL (Fin N) k)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hy
        · intro hx
          exact ⟨⟨x, hLQ hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [himg]
      exact hLc
  have hle : twKer (parInd (stdBlocks d hd) ρ) Q θ ≤ twKer σ ⊤ θ' :=
    Submodule.span_le.2 (by
      rintro w ⟨q, v, rfl⟩
      exact Submodule.subset_span ⟨⟨q, trivial⟩, v, rfl⟩)
  have key : (⟨f, hf⟩ : openFns d hd ρ) ∈ twKer ρ' ⊤ θ' :=
    GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρ' σ hρs hσs ⊤ θ' hopen hexh (openFns d hd ρ).subtype
      (Submodule.injective_subtype _) (fun _ _ => rfl) ⟨f, hf⟩ (hle hker)
  have hle2 : twKer ρ' ⊤ θ' ≤ (Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ,
      x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g}).comap (openFns d hd ρ).subtype :=
    Submodule.span_le.2 (by
      rintro _ ⟨q, g, rfl⟩
      exact Submodule.subset_span ⟨q.1, g.1, g.2, rfl⟩)
  exact hle2 key

end GlobalTheory.CompanionTheory.Rodier.OpenExact
