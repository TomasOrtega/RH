import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyDiagonalAndSwapChainMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSimplexFacePairsAcyclicPositiveDegreeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.PrHomotopy

/- English proof (translation)
Introduce `z hz`. Break down `Finset.mem_union.1 (Finsupp.support_sub hz) with h | h` into its components or cases. Conclude with `ha z h`. Conclude with `hb z h`.
-/
lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

/- English proof (translation)
Introduce `z hz`. Simplify using `at hz`.
-/
lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

/- English proof (translation)
Simplify using `[Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]`.
-/
lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  simp [Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[Pr.aw, Pr.wa]`.
-/
lemma aw_zero_eq_wa_zero : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

open Classical in

noncomputable def step (N : ℕ) (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ :=
  if H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c then H.choose else 0

noncomputable def hom : ∀ N, Pr N →₀ ℤ
  | 0 => 0
  | N + 1 => step N (hom N)

/- English proof (translation)
Take `⟨-, -, -, hbdeg, -, hdbd, haw⟩` from `GlobalTheory.T.prism_chain_complex_boundary_identities`. Establish `H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c`. Apply `GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N` to reduce the goal to its premises. Conclude with `deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)`. Take `⟨h1, h2⟩` from `GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps N`.

Rewrite using `[map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]`. Unfold `step`. Rewrite using `[dif_pos H]`. Conclude with `H.choose_spec`.
-/
lemma step_spec (N : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (N + 1) c)
    (hd : Pr.bd (Pr.d N c) = Pr.bd (Pr.aw N - Pr.wa N)) :
    Pr.Deg (N + 2) (step N c) ∧ Pr.d (N + 1) (step N c) = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
  obtain ⟨-, -, -, hbdeg, -, hdbd, haw⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
  have H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
    apply GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N
    · exact deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps N
      rw [map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]
  unfold step
  rw [dif_pos H]
  exact H.choose_spec

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩`. Consider the case `succ N ih`. Take `⟨h1, h2⟩` from `step_spec N (hom N) ih.1 ih.2`. Take `⟨-, -, -, -, hbb, -, -⟩` from `GlobalTheory.T.prism_chain_complex_boundary_identities`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _`. Rewrite using `[h2, bd_sub, hbb, sub_zero]`.
-/
lemma hom_spec (N : ℕ) : Pr.Deg (N + 1) (hom N) ∧ Pr.bd (Pr.d N (hom N)) = Pr.bd (Pr.aw N - Pr.wa N) := by
  induction N with
  | zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩
  | succ N ih =>
    obtain ⟨h1, h2⟩ := step_spec N (hom N) ih.1 ih.2
    obtain ⟨-, -, -, -, hbb, -, -⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
    refine ⟨h1, ?_⟩
    show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _
    rw [h2, bd_sub, hbb, sub_zero]

end GlobalTheory.EtC.PrHomotopy

/- English proof (translation)
Use `⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩` and prove the remaining obligations. Simplify using `[PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]`. Use `(PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2 show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _` as an intermediate fact. Rewrite using `[this, sub_add_cancel]`.
-/
theorem GlobalTheory.EtC.pr_aw_wa_homotopy :
    ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
      ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  refine ⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩
  · simp [PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]
  · have := (PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2
    show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _
    rw [this, sub_add_cancel]
