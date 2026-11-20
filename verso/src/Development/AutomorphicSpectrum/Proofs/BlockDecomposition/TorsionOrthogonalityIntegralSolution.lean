import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

variable {E : Type} [Field E] [NumberField E]

def kcSub {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : Submodule (𝓞 E) (Fin m → 𝓞 E) where
  carrier := (Kc c : Set (Fin m → 𝓞 E))
  add_mem' := fun hx hy => (Kc c).add_mem hx hy
  zero_mem' := (Kc c).zero_mem
  smul_mem' := by
    intro r y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨r * o, ?_⟩
    have h : (fun j => algebraMap (𝓞 E) E ((r • y) j)) =
        (algebraMap (𝓞 E) E r) • fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, ← ho, map_mul, smul_eq_mul]

def pair {m : ℕ} (w : Fin m → E) : (Fin m → 𝓞 E) →ₗ[𝓞 E] E where
  toFun y := ∑ j, w j * (y j : E)
  map_add' := by
    intro y z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change w j * ((r * y j : 𝓞 E) : E) = r • (w j * (y j : E))
    rw [Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring

def bMod {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : Submodule (𝓞 E) E :=
  1 ⊔ (kcSub c).map (pair w)

/- English proof (translation)
Use `Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))` and prove the remaining obligations. Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`.
-/
theorem bMod_fg {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : (bMod c w).FG := by
  refine Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))
  rw [Submodule.one_eq_span]
  exact Submodule.fg_span_singleton _

variable {F : Type} [Field F] [Algebra F E]

/- English proof (translation)
Establish `hmem : (sO σ a) • u ∈ lam c`. Use `GlobalTheory.T.mem_lattice_of_dual_pairing E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) _ ?_` and prove the remaining obligations. Introduce `a' hL`. Establish `hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m`. Introduce `j i`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp [Pi.single_apply, h]⟩`. Establish `hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j`.

Introduce `j`. Establish `h1` using `hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)`. Rewrite `h1` using `[Submodule.mem_one]`. Take `⟨o, ho⟩` from `h1`. Conclude with `⟨o, by rw [ho]; simp⟩`.

Use `choose o ho using hent`. Establish `hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i`. Introduce `i`. Establish `hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c` using `Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))`. Establish `h1` using `hL _ hx`.

Rewrite `h1` using `[Submodule.mem_one]`. Take `⟨p, hp⟩` from `h1`. Use `⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[hp]`. Simplify using `[dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]`.

Establish `hy : (fun j => sO σ (o j)) ∈ Kc c`. Introduce `i`. Take `⟨p, hp⟩` from `hcol i`. Use `⟨sO σ p, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p)` using `hsO p`.

Rewrite using `[e1, hp, map_sum]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j)`. Rewrite using `[← ho j]`.

Conclude with `hsO (o j)`. Rewrite using `[e2, map_mul, hc i j, mul_comm]`. Establish `h2` using `ha _ hy`. Rewrite `h2`, the goal using `[Submodule.mem_one]`. Take `⟨q, hq⟩` from `h2`.

Use `⟨sO σ q, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q)` using `hsO q`. Rewrite using `[e1, hq, map_mul, map_sum]`. Simplify using `only [dotProduct, Finset.mul_sum, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j)`. Rewrite using `[hsO, ← ho j]`. Simplify using `only [e3, map_mul, hinv, Algebra.smul_def]`. Establish `e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E)` using `hsO a`. Rewrite using `[e4]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem`.
-/
theorem sO_mem_tor (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (hsO : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E)) {m : ℕ}
    (c : Matrix (Fin m) (Fin m) E) (hc : ∀ a b, σ (c b a) = c a b) (u : Fin m → E) (a : 𝓞 E)
    (ha : ∀ y ∈ Kc c, (a : E) * ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E)) :
    sO σ a ∈ tor c u := by
  have hmem : (sO σ a) • u ∈ lam c := by
    refine GlobalTheory.T.mem_lattice_of_dual_pairing E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) _ ?_
    intro a' hL

    have hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m := by
      intro j i
      by_cases h : i = j
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, h]⟩
    have hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j := by
      intro j
      have h1 := hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)
      rw [Submodule.mem_one] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, by rw [ho]; simp⟩
    choose o ho using hent
    have hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i := by
      intro i
      have hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c :=
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))
      have h1 := hL _ hx
      rw [Submodule.mem_one] at h1
      obtain ⟨p, hp⟩ := h1
      refine ⟨p, ?_⟩
      rw [hp]
      simp [dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
    have hy : (fun j => sO σ (o j)) ∈ Kc c := by
      intro i
      obtain ⟨p, hp⟩ := hcol i
      refine ⟨sO σ p, ?_⟩
      have e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p) := hsO p
      rw [e1, hp, map_sum]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j) := by
        rw [← ho j]; exact hsO (o j)
      rw [e2, map_mul, hc i j, mul_comm]
    have h2 := ha _ hy
    rw [Submodule.mem_one] at h2 ⊢
    obtain ⟨q, hq⟩ := h2
    refine ⟨sO σ q, ?_⟩
    have e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q) := hsO q
    rw [e1, hq, map_mul, map_sum]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j) := by
      rw [hsO, ← ho j]
    simp only [e3, map_mul, hinv, Algebra.smul_def]
    have e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E) := hsO a
    rw [e4]
    ring
  rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm m c hc u b hb`. Take `⟨hinv, -, hsO, -⟩` from `GlobalTheory.T.cm_conjugation_properties F E σ hcm`. Use `set w : Fin m → E := fun j => σ (u j) with hw`. Set `B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E` to `⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩`. Establish `hB1 : (1 : E) ∈ B`.

Express the relevant statement in the definitionally equal form `(1 : E) ∈ bMod c w`. Conclude with `Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)`. Establish `hB0 : B ≠ 0`. Introduce `h`. Rewrite `hB1` using `[h, FractionalIdeal.mem_zero_iff]`.

Conclude with `one_ne_zero hB1`. Establish `hBi : B⁻¹ ≠ 0` using `inv_ne_zero hB0`. Establish `hbB : b ∈ B`. Establish `hbi : b ∈ (B⁻¹)⁻¹`. Rewrite using `[FractionalIdeal.mem_inv_iff hBi]`.

Introduce `x hx`. Rewrite `hx` using `[FractionalIdeal.mem_inv_iff hB0]`. Establish `hx1` using `hx 1 hB1`. Rewrite `hx1` using `[mul_one, FractionalIdeal.mem_one_iff]`. Take `⟨a, rfl⟩` from `hx1`.

Establish `ht : sO σ a ∈ tor c u`. Use `sO_mem_tor σ hinv hsO c hc u a ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hyB : ∑ j, σ (u j) * (y j : E) ∈ B`. Express the relevant statement in the definitionally equal form `_ ∈ bMod c w`.

Conclude with `Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))`. Use `hx _ hyB` as an intermediate fact. Rewrite `this` using `[FractionalIdeal.mem_one_iff]`. Take `⟨q, hq⟩` from `this`. Rewrite using `[Submodule.mem_one]`.

Conclude with `⟨q, hq⟩`. Establish `h` using `hb _ ht`. Rewrite `h` using `[hsO, hinv]`. Rewrite `h` using `[Submodule.mem_one]`. Take `⟨q, hq⟩` from `h`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `hq`. Rewrite `hbi` using `[inv_inv]`. Then use the resulting hypothesis.

Establish `hbB' : b ∈ bMod c w` using `hbB`. Take `⟨p, hp, z, hz, hpz⟩` from `Submodule.mem_sup.mp hbB'`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hz`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Establish `: b - ∑ j, σ (u j) * (y j : E) = p`.

Rewrite using `[← hpz]`. Express the relevant statement in the definitionally equal form `p + ∑ j, σ (u j) * (y j : E) - _ = p`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hp`.
-/
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  intro F E _ _ _ _ _ σ hcm m c hc u b hb
  obtain ⟨hinv, -, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  set w : Fin m → E := fun j => σ (u j) with hw
  let B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    ⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩
  have hB1 : (1 : E) ∈ B := by
    change (1 : E) ∈ bMod c w
    exact Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hB1
    exact one_ne_zero hB1
  have hBi : B⁻¹ ≠ 0 := inv_ne_zero hB0
  have hbB : b ∈ B := by
    have hbi : b ∈ (B⁻¹)⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hBi]
      intro x hx
      rw [FractionalIdeal.mem_inv_iff hB0] at hx
      have hx1 := hx 1 hB1
      rw [mul_one, FractionalIdeal.mem_one_iff] at hx1
      obtain ⟨a, rfl⟩ := hx1
      have ht : sO σ a ∈ tor c u := by
        refine sO_mem_tor σ hinv hsO c hc u a ?_
        intro y hy
        have hyB : ∑ j, σ (u j) * (y j : E) ∈ B := by
          change _ ∈ bMod c w
          exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))
        have := hx _ hyB
        rw [FractionalIdeal.mem_one_iff] at this
        obtain ⟨q, hq⟩ := this
        rw [Submodule.mem_one]
        exact ⟨q, hq⟩
      have h := hb _ ht
      rw [hsO, hinv] at h
      rw [Submodule.mem_one] at h
      obtain ⟨q, hq⟩ := h
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨q, ?_⟩
      rw [mul_comm]
      exact hq
    rwa [inv_inv] at hbi
  have hbB' : b ∈ bMod c w := hbB
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hbB'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨y, hy, ?_⟩
  have : b - ∑ j, σ (u j) * (y j : E) = p := by
    rw [← hpz]
    change p + ∑ j, σ (u j) * (y j : E) - _ = p
    ring
  rw [this]
  exact hp
