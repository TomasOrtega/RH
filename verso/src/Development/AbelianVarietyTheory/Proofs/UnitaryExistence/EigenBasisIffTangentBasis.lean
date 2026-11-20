import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSumStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

/- English proof (translation)
Establish `key : ∀ a : ∀ τ, Fin (m τ) → S, ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i`. Introduce `a`. Rewrite using `[e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]`. Establish `key' : ∀ a : Fin g → S, ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i`. Introduce `a`.

Rewrite using `[← key (fun τ i => a (e.symm ⟨τ, i⟩))]`. Simplify using the standard rewrite rules. Establish `hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ` using `fun τ a => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Take `⟨f, ⟨hf, hfn⟩, hu⟩` from `hs n`. Use `choose a ha hau using fun τ => h τ (f τ) (hf τ)`. Use `⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2`. Rewrite using `[key, ← hfn]`.

Conclude with `Finset.sum_congr rfl fun τ _ => ha τ`. Introduce `a' ha'`. Rewrite `ha'` using `[key']`. Establish `h1` using `hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩`. Use function extensionality and compare the values at `j`.

Establish `h2` using `hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm`. Establish `h3` using `congrFun h2 (e j).2`. Simplify using `using h3`. Introduce `h τ n hn`. Take `⟨a', ha', hu'⟩` from `h n`.

Establish `hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i → (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a'`. Introduce `a ha`. Apply `hu'` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2`. Rewrite using `[key, Finset.sum_eq_single τ]`.

Simplify using `using ha`. Introduce `σ _ hσ`. Simplify using `[Pi.single_eq_of_ne hσ]`. Simplify using the standard rewrite rules. Use `⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩` and prove the remaining obligations.

Establish `ha2 : n = ∑ j, a' j • b (e j).1 (e j).2` using `ha'`. Rewrite `ha2` using `[key']`. Establish `h1` using `(hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality.

Simplify using `using hn`. Simplify using `[Pi.single_eq_of_ne hσ], by simp⟩`. Establish `h2` using `congrFun h1 τ`. Simplify using `using h2.symm`. Introduce `a ha`.

Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun (hA a ha) (e.symm ⟨τ, i⟩)`. Rewrite using `[← h1, Equiv.apply_symm_apply]`. Simplify using the standard rewrite rules.
-/
theorem basis_iff_of_split {S N J : Type} [CommRing S] [AddCommGroup N] [Module S N] [Fintype J]
    (m : J → ℕ) (M : J → Submodule S N)
    (hs : ∀ n : N, ∃! f : J → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n)
    (b : ∀ τ, Fin (m τ) → N) (hb : ∀ τ i, b τ i ∈ M τ) (g : ℕ) (e : Fin g ≃ Σ τ : J, Fin (m τ)) :
    (∀ τ n, n ∈ M τ → ∃! a : Fin (m τ) → S, n = ∑ i, a i • b τ i) ↔
      ∀ n : N, ∃! a : Fin g → S, n = ∑ j, a j • b (e j).1 (e j).2 := by
  classical
  have key : ∀ a : ∀ τ, Fin (m τ) → S,
      ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i := by
    intro a
    rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]
  have key' : ∀ a : Fin g → S,
      ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i := by
    intro a
    rw [← key (fun τ i => a (e.symm ⟨τ, i⟩))]
    simp
  have hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ := fun τ a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)
  constructor
  · intro h n
    obtain ⟨f, ⟨hf, hfn⟩, hu⟩ := hs n
    choose a ha hau using fun τ => h τ (f τ) (hf τ)
    refine ⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩
    · change n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, ← hfn]
      exact Finset.sum_congr rfl fun τ _ => ha τ
    · intro a' ha'
      rw [key'] at ha'
      have h1 := hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩
      funext j
      have h2 := hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm
      have h3 := congrFun h2 (e j).2
      simpa using h3
  · intro h τ n hn
    obtain ⟨a', ha', hu'⟩ := h n
    have hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i →
        (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a' := by
      intro a ha
      apply hu'
      change n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, Finset.sum_eq_single τ]
      · simpa using ha
      · intro σ _ hσ
        simp [Pi.single_eq_of_ne hσ]
      · simp
    refine ⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩
    · have ha2 : n = ∑ j, a' j • b (e j).1 (e j).2 := ha'
      rw [key'] at ha2
      have h1 := (hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i)
        (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by
          by_cases hσ : σ = τ
          · subst hσ; simpa using hn
          · simp [Pi.single_eq_of_ne hσ], by simp⟩
      have h2 := congrFun h1 τ
      simpa using h2.symm
    · intro a ha
      funext i
      have h1 := congrFun (hA a ha) (e.symm ⟨τ, i⟩)
      rw [← h1, Equiv.apply_symm_apply]
      simp

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c S _ _ x u g e ht he`. Take `⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x`. Use `choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)`. Take `rfl : u = fun τ i => v (b τ i)` from `by funext τ i; exact (hb τ i).symm`. Set `M : (E →+* ℂ) → Submodule S N` to `fun τ => ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))`.

Establish `hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n`. Introduce `τ n`. Simplify using `only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Establish `hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ`. Introduce `τ n`.

Rewrite using `[hM]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← hρ, ← hsm, hinj.eq_iff]`. Establish `hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n`. Introduce `n`.

Simplify using `only [hM]`. Conclude with `GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ n`. Establish `hmain` using `basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e`. Establish `hT : ∀ n, IsTanAt x (v n)` using `fun n => (htan _).2 ⟨n, rfl⟩`. Establish `hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N), IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i`.

Introduce `k b a n`. Rewrite using `[hcomb, hinj.eq_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun j => hT _, fun w hw => ?_⟩` and prove the remaining obligations.

Take `⟨n, rfl⟩` from `(htan w).1 hw`. Establish `h1` using `hmain.1 (fun τ n hn => by`. Establish `h2` using `h τ (v n) (hT n) ((hE τ n).2 hn)`. Simplify `h2) n` using `only [hC]`. Simplify `h1` using `only [hC]`.

Introduce and unpack `⟨-, h⟩ τ w hw hew`. Take `⟨n, rfl⟩` from `(htan w).1 hw`. Establish `h1` using `hmain.2 (fun n => by`. Establish `h2` using `h (v n) (hT n)`. Simplify `h2) τ n ((hE τ n).1 hew)` using `only [hC]`.

Simplify `h1` using `only [hC]`.
-/
theorem eigBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  intro E _ _ _ H Dw l Xo c S _ _ x u g e ht he
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ n
  have hmain := basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAt x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h
    refine ⟨fun j => hT _, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · rintro ⟨-, h⟩ τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

end GlobalTheory.Frames
