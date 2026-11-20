import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `h`. Conclude with `⟨h1, h2⟩`.
-/
theorem isLattice_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    Submodule.IsLattice E L := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2⟩

/- English proof (translation)
Take `⟨-, -, h3⟩` from `h`. Unfold `PI.UG.IsUnimodular PI.UG.dual`. Use extensionality with `y`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Rewrite using `[h3 y]`.

Conclude with `forall₂_congr fun x _ => RingHom.mem_range.symm`.
-/
theorem isUnimodular_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    IsUnimodular (hStd E N) L := by
  obtain ⟨-, -, h3⟩ := h
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [h3 y]
  exact forall₂_congr fun x _ => RingHom.mem_range.symm

/- English proof (translation)
Use `haveI := hQ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hle : hcompl (K` using `E) Q ≤ Q.primeCompl := Submonoid.closure_le.mpr fun s hs => hs.1`. Conclude with `hle h`.

Introduce `hs`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Use `⟨hs, fun t ht => ?_⟩` and prove the remaining obligations. Establish `htc : t = cj E s`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Conclude with `ht`. Substitute `htc` using the available equality. Introduce `hcs`. Apply `hs` to reduce the goal to its premises. Establish `h2 : s ∈ Q.comap (cj E)` using `Ideal.mem_comap.mpr hcs`.

Rewrite `h2` using `[hc]`. Then use the resulting hypothesis.
-/
theorem mem_hcompl_of_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) (s : 𝓞 E) :
    s ∈ hcompl (K := E) Q ↔ s ∉ Q := by
  haveI := hQ
  constructor
  · intro h
    have hle : hcompl (K := E) Q ≤ Q.primeCompl := Submonoid.closure_le.mpr fun s hs => hs.1
    exact hle h
  · intro hs
    apply Submonoid.subset_closure
    refine ⟨hs, fun t ht => ?_⟩
    have htc : t = cj E s := by
      apply RingOfIntegers.ext
      exact ht
    subst htc
    intro hcs
    apply hs
    have h2 : s ∈ Q.comap (cj E) := Ideal.mem_comap.mpr hcs
    rwa [hc] at h2

/- English proof (translation)
Simplify using `[loc, locS, mem_hcompl_of_inert hQ hc]`.
-/
theorem mem_loc_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ loc (K := E) Q L ↔ ∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L := by
  simp [loc, locS, mem_hcompl_of_inert hQ hc]

/- English proof (translation)
Rewrite using `[mem_loc_inert hQ hc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩ i`. Take `⟨w, hw⟩` from `Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))`. Use `⟨s, hs, w, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E s * x i = algebraMap (𝓞 E) E w`. Rewrite using `[hw, Pi.smul_apply, Algebra.smul_def]`. Introduce `h choose s hs w hw using h haveI := hQ`. Use `⟨∏ i, s i, ?_, ?_⟩` and prove the remaining obligations. Establish `: (∏ i, s i) ∈ Q.primeCompl` using `Submonoid.prod_mem _ fun i _ => hs i`.

Conclude with `this`. Use `Submodule.mem_pi.mpr fun i _ => Submodule.mem_one.mpr ⟨(∏ j ∈ Finset.univ.erase i, s j) * w i, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, map_mul, mul_assoc]`. Use `congr 1`. Conclude with `(hw i).symm`.
-/
theorem mem_loc_stdLat {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (x : Fin N → E) : x ∈ loc (K := E) Q (stdLat E N) ↔ ∀ i, IntAt Q (x i) := by
  rw [mem_loc_inert hQ hc]
  constructor
  · rintro ⟨s, hs, hx⟩ i
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    refine ⟨s, hs, w, ?_⟩
    change algebraMap (𝓞 E) E s * x i = algebraMap (𝓞 E) E w
    rw [hw, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose s hs w hw using h
    haveI := hQ
    refine ⟨∏ i, s i, ?_, ?_⟩
    · have : (∏ i, s i) ∈ Q.primeCompl := Submonoid.prod_mem _ fun i _ => hs i
      exact this
    · refine Submodule.mem_pi.mpr fun i _ => Submodule.mem_one.mpr
        ⟨(∏ j ∈ Finset.univ.erase i, s j) * w i, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul,
        map_mul, mul_assoc]
      congr 1
      exact (hw i).symm

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : hStd E N (g (PI.UG.W.eStd E N i)) (g (PI.UG.W.eStd E N j)) = if i = j then 1 else 0` using `(hg _ _).trans (PI.UG.W.hStd_eStd E N i j)`. Rewrite `h1` using `[PI.UG.W.hStd_apply]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← h1]`. Simplify using `only [conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, PI.UG.W.eStd]`.
-/
theorem unitary_of_isom {N : ℕ} {g : (Fin N → E) ≃ₗ[E] (Fin N → E)} (hg : g ∈ isom (hStd E N)) :
    (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *
      LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  ext i j
  have h1 : hStd E N (g (PI.UG.W.eStd E N i)) (g (PI.UG.W.eStd E N j)) = if i = j then 1 else 0 :=
    (hg _ _).trans (PI.UG.W.hStd_eStd E N i j)
  rw [PI.UG.W.hStd_apply] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  simp only [conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, PI.UG.W.eStd]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ hE N L hL Q hQ hc`. Take `⟨g, hg, hgL⟩` from `unimodular_genus_unique E N hE L (isLattice_of_isSDG hL) (isUnimodular_of_isSDG hL) Q hQ`. Establish `h1` using `unitary_of_isom hg`. Establish `h2` using `mul_eq_one_comm.mp h1`. Use `⟨LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)), h1, h2, fun y => ?_⟩` and prove the remaining obligations.

Establish `hQp` using `hQ.isPrime`. Rewrite using `[← mem_loc_inert hQp hc, ← mem_loc_stdLat hQp hc]`. Express the relevant statement in the definitionally equal form `y ∈ loc (K := E) Q L ↔ _`. Rewrite using `[← hgL]`. Establish `hs : g.symm y = (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *ᵥ y`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Rewrite using `[← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`. Rewrite using `[← hs]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Simplify using `using hx`. Introduce `h`. Conclude with `⟨g.symm y, h, by simp⟩`.
-/
theorem dict : Dict := by
  intro E _ _ _ hE N L hL Q hQ hc
  obtain ⟨g, hg, hgL⟩ := unimodular_genus_unique E N hE L (isLattice_of_isSDG hL) (isUnimodular_of_isSDG hL) Q hQ
  have h1 := unitary_of_isom hg
  have h2 := mul_eq_one_comm.mp h1
  refine ⟨LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)), h1, h2, fun y => ?_⟩
  have hQp := hQ.isPrime
  rw [← mem_loc_inert hQp hc, ← mem_loc_stdLat hQp hc]
  change y ∈ loc (K := E) Q L ↔ _
  rw [← hgL]
  have hs : g.symm y = (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *ᵥ y := by
    rw [LinearEquiv.symm_apply_eq]
    rw [← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← hs]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

end PI.SqPairLocal
