import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZarCap

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem inU_inf {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V W : X.Opens) (T : Thick (nlFun γ p X q κ)) :
    InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
  unfold InU
  rw [← le_inf_iff]
  exact Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem irrelevant_le_span (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  have h0 : MvPolynomial.coeff 0 x = 0 := by
    erw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero] at hx
    exact MvPolynomial.C_eq_zero.1 hx
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hi
    exact hne ⟨i, Set.mem_univ i, hi⟩
  subst hm0
  exact (MvPolynomial.mem_support_iff.1 hm) h0

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem iSup_wch {K : Type} [Field K] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace K N) : (⨆ j, wch i j) = ⊤ := by
  have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun j => MvPolynomial.X j) (irrelevant_le_span K N)
  simp only [wch]
  rw [← Scheme.Hom.preimage_iSup, h, Scheme.Hom.preimage_top]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
theorem resU_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    resU (sq (thFil L r) (thFil L r')) h = (incl h).sq (incl_fil h r) (incl_fil h r') := by
  unfold resU CrystallineSemistableComparison.Pb.SMor.sq
  congr 1
  funext T
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨z, hz⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem isHecke_div_and_resEtaPow_div {X : Scheme.{0}} {m N : ℕ} (u : Fin m → X.Opens) (w : Fin (N + 1) → X.Opens)
    (hw : (⨆ j, w j) = ⊤) (S : Finset (Fin m)) :
    (⨅ k ∈ S, u k) ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact le_iSup_of_le (fun _ => 0) (by simp)
  · intro a S ha ih
    rw [Finset.iInf_insert]
    calc u a ⊓ ⨅ k ∈ S, u k ≤ (⨆ j, u a ⊓ w j) ⊓ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) :=
          inf_le_inf (by rw [← inf_iSup_eq, hw, inf_top_eq]) ih
      _ = ⨆ j, ⨆ c : Fin m → Fin (N + 1), (u a ⊓ w j) ⊓ ⨅ k ∈ S, (u k ⊓ w (c k)) := by
          rw [iSup_inf_eq]
          simp_rw [inf_iSup_eq]
      _ ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ insert a S, (u k ⊓ w (c k)) := by
          refine iSup_le fun j => iSup_le fun c => le_iSup_of_le (Function.update c a j) ?_
          rw [Finset.iInf_insert]
          refine inf_le_inf (by simp) (le_iInf₂ fun k hk => (iInf₂_le k hk).trans ?_)
          have hka : k ≠ a := fun h => ha (h ▸ hk)
          simp [hka]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  intro K _ X q N m i y s S hS r r' j
  classical
  have e : capS (wK q i y s) S = KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    funext T
    apply propext
    constructor
    · intro hT
      obtain ⟨k0, hk0⟩ := hS
      refine ⟨(hT k0 hk0).1, ?_⟩
      have hc : ∀ k, ∃ c : Fin (N + 1), k ∈ S → InU (uy i y k ⊓ wch i c) T := by
        intro k
        by_cases hk : k ∈ S
        · obtain ⟨_, V, ⟨c, rfl⟩, hV⟩ := hT k hk
          exact ⟨c, fun _ => hV⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose c hc using hc
      exact ⟨_, ⟨c, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).2 hc⟩
    · rintro ⟨hT, V, ⟨c, rfl⟩, hV⟩ k hk
      exact ⟨hT, _, ⟨c k, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk⟩
  rw [e]
  have hle : KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) ≤
      KS q s {⨅ k ∈ S, uy i y k} := by
    rintro T ⟨hT, V, ⟨c, rfl⟩, hV⟩
    refine ⟨hT, _, Set.mem_singleton _, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (uy i y) S _).2 fun k hk => ?_⟩
    exact ((inU_inf _ _ _).1 ((GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk)).1
  have hc : ∀ W ∈ ({⨅ k ∈ S, uy i y k} : Set X.Opens),
      W ≤ sSup (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [sSup_range]
    exact isHecke_div_and_resEtaPow_div (uy i y) (wch i) (iSup_wch N i) S
  refine ⟨hle, ?_⟩
  rw [resU_eq]
  exact (GlobalTheory.CompanionTheory.NlZar.zariski_descent (CrystallineSemistableComparison.Pb.TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) _ _ hle hc j).1 r r'

end GlobalTheory.CompanionTheory.ConeZarCap
