import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.StdBaseChange

def pureSet (K : Type) [CommRing K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) : Set (MvPolynomial (S × (Fin k × Fin n)) K) :=
  {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ A s) ∧ P = ∏ s, blockEmb K s (F s)}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Establish `h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s)` using `fun s => Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)`.

Establish `h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, Finset.prod_empty]`.

Conclude with `Submodule.one_le.mp le_rfl`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `Submodule.mul_mem_mul (h1 a) ih`. Establish `h3` using `h2 Finset.univ`.

Rewrite `h3` using `[Submodule.prod_span]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations. Introduce `P hP`. Take `⟨G, hG, rfl⟩` from `(Set.mem_fintype_prod _ _).mp hP`. Use `choose F' hF' hFG using hG`.

Conclude with `⟨F', hF', by simp only [hFG]⟩`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Conclude with `⟨F, fun s => Submodule.subset_span (hF s), rfl⟩`.
-/
theorem tensorLat_span (R K : Type) [CommRing R] [CommRing K] [Algebra R K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    tensorLat R K (fun s => Submodule.span R (A s)) = Submodule.span R (pureSet K A) := by
  classical
  apply le_antisymm
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s) := fun s =>
      Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)
    have h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.prod_empty]
        exact Submodule.one_le.mp le_rfl
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨G, hG, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose F' hF' hFG using hG
    exact ⟨F', hF', by simp only [hFG]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => Submodule.subset_span (hF s), rfl⟩

/- English proof (translation)
Establish `h : ∀ F : S → MvPolynomial (Fin k × Fin n) K, MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s))`. Introduce `F`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [blockEmb, map_rename]`.

Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨F, hF, rfl⟩, rfl⟩`. Conclude with `⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩`. Introduce and unpack `⟨G, hG, rfl⟩ choose F hF hFG using hG`.

Conclude with `⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩`.
-/
theorem image_pureSet {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    MvPolynomial.map φ '' pureSet K A = pureSet L fun s => MvPolynomial.map φ '' A s := by
  have h : ∀ F : S → MvPolynomial (Fin k × Fin n) K,
      MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s)) := by
    intro F
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [blockEmb, map_rename]
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩
  · rintro ⟨G, hG, rfl⟩
    choose F hF hFG using hG
    exact ⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy`.

Establish `e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y`. Rewrite using `[← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hy`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem span_map_span {R K O L σ : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing O] [CommRing L] [Algebra O L]
    (φ : K →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R K r)) (T : Set (MvPolynomial σ K)) :
    Submodule.span O (MvPolynomial.map φ '' (Submodule.span R T : Set (MvPolynomial σ K))) =
      Submodule.span O (MvPolynomial.map φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y := by
        rw [← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Rewrite using `[StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]`. Both sides reduce to the same expression.
-/
theorem dualWeyl_map (R K : Type) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (dualWeyl R n n ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.bidSet K n ν) := by
  rw [StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]
  rfl

/- English proof (translation)
Rewrite using `[StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]`. Both sides reduce to the same expression.
-/
theorem weyl_map (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (weyl R n n le_rfl ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.wordSet K n ν) := by
  rw [StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]
  rfl

/- English proof (translation)
Introduce `O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam`. Prove the components needed by the constructor for the conclusion. Establish `e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW)`. Unfold `nabStd`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Conclude with `dualWeyl_map (𝓞 K) K n (lam τ).natW`. Rewrite using `[e, tensorLat_span, span_map_span eK ψ h, image_pureSet]`. Simplify using `only [stdN, dualWeyl_map, StdDual.image_bidSet]`. Rewrite using `[tensorLat_span]`.

Establish `e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW)`. Unfold `delStd`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `weyl_map (𝓞 K) K n (lam τ).natW`.

Rewrite using `[e, tensorLat_span, span_map_span eK ψ h, image_pureSet]`. Simplify using `only [stdD, weyl_map, StdDual.image_wordSet]`. Rewrite using `[tensorLat_span]`.
-/
theorem std_baseChange : ∀ (O Kf K ι : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Field K] [NumberField K] [Fintype ι] (eK : K →+* Kf) (ψ : 𝓞 K →+* O), (∀ r, algebraMap O Kf (ψ r) = eK r) → ∀ (n : ℕ) (lam : ι → DomWeight n), Submodule.span O (MvPolynomial.map eK '' (nabStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdN O Kf n (lam τ).natW) ∧ Submodule.span O (MvPolynomial.map eK '' (delStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdD O Kf n (lam τ).natW) := by
  intro O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam
  constructor
  · have e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW) := by
      unfold nabStd
      congr 1
      funext τ
      exact dualWeyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdN, dualWeyl_map, StdDual.image_bidSet]
    rw [tensorLat_span]
  · have e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW) := by
      unfold delStd
      congr 1
      funext τ
      exact weyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdD, weyl_map, StdDual.image_wordSet]
    rw [tensorLat_span]

end GlobalTheory.StdBaseChange
