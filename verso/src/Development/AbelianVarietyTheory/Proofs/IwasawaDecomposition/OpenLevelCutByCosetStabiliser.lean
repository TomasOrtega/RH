import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.QthPrincInv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section CutOpen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

omit [StarRing E] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, hs, h⟩`. Establish `h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `hs`.

Establish `h2` using `congrArg (P.valuation E) h`. Rewrite `h2` using `[map_mul, h1, one_mul]`. Rewrite using `[h2]`. Conclude with `P.valuation_le_one r`. Introduce `h`.

Take `⟨r, s, hs⟩` from `P.exists_primeCompl_mul_eq_of_integer a h`. Conclude with `⟨r, s, s.2, by rw [mul_comm]; exact hs⟩`.
-/
theorem intAt_iff_val_le_one {P : HeightOneSpectrum (𝓞 E)} {a : E} : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  intro h
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

/- English proof (translation)
Rewrite using `[ciMem_stdAt]`. Conclude with `forall_congr' fun _ => intAt_iff_val_le_one`.
-/
theorem mem_stdAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  rw [ciMem_stdAt]
  exact forall_congr' fun _ => intAt_iff_val_le_one

/- English proof (translation)
Introduce `i j`. Use `(hg i j).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `WithZero.exp (-(N' : ℤ)) ≤ WithZero.exp (-(N : ℤ))`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lqPrinc_mono {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : lqPrinc P N' g) : lqPrinc P N g := by
  intro i j
  refine (hg i j).trans ?_
  change WithZero.exp (-(N' : ℤ)) ≤ WithZero.exp (-(N : ℤ))
  rw [WithZero.exp_le_exp]
  omega

/- English proof (translation)
Use `set f : Sp E n ≃ₗ[E] Sp E n := g.1 with hf`. Establish `hgw : f (c⁻¹ • (x - z)) ∈ stdAt E n P` using `(g.2 _).2 hx`. Establish `hsplit : c⁻¹ • (f x - z) = f (c⁻¹ • (x - z)) + c⁻¹ • (f z - z)`. Rewrite using `[map_smul, map_sub, smul_sub, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hsplit]`. Use `(stdAt E n P).add_mem hgw ?_` and prove the remaining obligations. Rewrite using `[mem_stdAt_iff_val]`. Introduce `i`. Establish `hfz : f z - z = (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) *ᵥ z`.

Rewrite using `[Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]`. Both sides reduce to the same expression. Establish `e : (c⁻¹ • (f z - z)) i = ∑ j, (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j * (c⁻¹ * z j)`. Rewrite using `[hfz, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_sum_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem smul_sub_mem_of_princ {P : HeightOneSpectrum (𝓞 E)} {N a : ℕ} (g : ↥(GLint E n P))
    (hg : lqPrinc P (N + a) (g : Sp E n ≃ₗ[E] Sp E n)) {c : E} {z : Sp E n}
    (ha : ∀ j, P.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ)) {x : Sp E n}
    (hx : c⁻¹ • (x - z) ∈ stdAt E n P) : c⁻¹ • ((g : Sp E n ≃ₗ[E] Sp E n) x - z) ∈ stdAt E n P := by
  set f : Sp E n ≃ₗ[E] Sp E n := g.1 with hf
  have hgw : f (c⁻¹ • (x - z)) ∈ stdAt E n P := (g.2 _).2 hx
  have hsplit : c⁻¹ • (f x - z) = f (c⁻¹ • (x - z)) + c⁻¹ • (f z - z) := by
    rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
    abel
  rw [hsplit]
  refine (stdAt E n P).add_mem hgw ?_
  rw [mem_stdAt_iff_val]
  intro i
  have hfz : f z - z = (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) *ᵥ z := by
    rw [Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    rfl
  have e : (c⁻¹ • (f z - z)) i = ∑ j, (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j * (c⁻¹ * z j) := by
    rw [hfz, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc P.valuation E ((LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j) * P.valuation E (c⁻¹ * z j)
      ≤ WithZero.exp (-((N + a : ℕ) : ℤ)) * WithZero.exp (a : ℤ) := mul_le_mul' (hg i j) (ha j)
    _ = WithZero.exp (-(N : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

/- English proof (translation)
Introduce `P`. Take `⟨N, hN, hT⟩` from `hΘ P`. Establish `hstab : ∃ N' : ℕ, N ≤ N' ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N' (g : Sp E n ≃ₗ[E] Sp E n) → g ∈ frStab P.1 (C P)`. Break down `hC P with h | ⟨z, c, _, h⟩` into its components or cases. Use `⟨N, le_rfl, fun g _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_frStab, h]`. Introduce `v`. Simplify using the standard rewrite rules. Take `⟨a, ha⟩` from `qth_bound P.1 (Matrix.of fun (_ j : Fin n) => c⁻¹ * z j)`. Establish `ha' : ∀ j, P.1.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ)` using `fun j => by`.

Simplify using `using ha j j`. Use `⟨N + a, by omega, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_frStab, h]`. Introduce `v`. Use `show c⁻¹ • (g.1 v - z) ∈ stdAt E n P.1 ↔ c⁻¹ • (v - z) ∈ stdAt E n P.1`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `hi` using `smul_sub_mem_of_princ g⁻¹ (qth_princ_inv P.1 g hg) ha' hv`. Establish `e : ((g⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) (g.1 v) = v` using `LinearEquiv.symm_apply_apply g.1 v`. Rewrite `hi` using `[e]`. Then use the resulting hypothesis.

Conclude with `smul_sub_mem_of_princ g hg ha'`. Take `⟨N', hNN, hS⟩` from `hstab`. Use `⟨N', by omega, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨hH, hl⟩` from `hT g (lqPrinc_mono hNN hg)`. Conclude with `⟨⟨hH, hS g hg⟩, hl⟩`.
-/
theorem thetaOpen_cutQ {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ)
    (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) :
    ThetaOpen (cutQ Θ C) := by
  intro P
  obtain ⟨N, hN, hT⟩ := hΘ P
  have hstab : ∃ N' : ℕ, N ≤ N' ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N' (g : Sp E n ≃ₗ[E] Sp E n) →
      g ∈ frStab P.1 (C P) := by
    rcases hC P with h | ⟨z, c, _, h⟩
    · refine ⟨N, le_rfl, fun g _ => ?_⟩
      rw [mem_frStab, h]
      intro v
      simp
    · obtain ⟨a, ha⟩ := qth_bound P.1 (Matrix.of fun (_ j : Fin n) => c⁻¹ * z j)
      have ha' : ∀ j, P.1.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ) := fun j => by
        simpa using ha j j
      refine ⟨N + a, by omega, fun g hg => ?_⟩
      rw [mem_frStab, h]
      intro v
      show c⁻¹ • (g.1 v - z) ∈ stdAt E n P.1 ↔ c⁻¹ • (v - z) ∈ stdAt E n P.1
      constructor
      · intro hv
        have hi := smul_sub_mem_of_princ g⁻¹ (qth_princ_inv P.1 g hg) ha' hv
        have e : ((g⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) (g.1 v) = v := LinearEquiv.symm_apply_apply g.1 v
        rwa [e] at hi
      · exact smul_sub_mem_of_princ g hg ha'
  obtain ⟨N', hNN, hS⟩ := hstab
  refine ⟨N', by omega, fun g hg => ?_⟩
  obtain ⟨hH, hl⟩ := hT g (lqPrinc_mono hNN hg)
  exact ⟨⟨hH, hS g hg⟩, hl⟩

end CutOpen

end GlobalTheory.Mem.Col2.ChEx
