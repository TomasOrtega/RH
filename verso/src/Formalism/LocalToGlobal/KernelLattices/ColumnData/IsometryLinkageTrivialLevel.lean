import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.G0

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Formalism.FrobeniusOrbits Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

/- English proof (translation)
Rewrite using `[← eq_ratCast (algebraMap ℚ D.host.E) t]`. Conclude with `D.host.K.algebraMap_mem t`.
-/
theorem rat_mem (t : ℚ) : (t : D.host.E) ∈ D.host.K := by
  rw [← eq_ratCast (algebraMap ℚ D.host.E) t]; exact D.host.K.algebraMap_mem t

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[CU.emb_conj, map_neg, CS.embedding_sqrt_neg_d, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_b : D.host.conj (D.host.sqd) = -D.host.sqd := by
  apply D.host.φ₀.injective
  rw [CU.emb_conj, map_neg, CS.embedding_sqrt_neg_d, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/- English proof (translation)
Take `⟨p, q, e⟩` from `CS.K_repr D _ k.2`. Rewrite using `[e, map_add, map_mul, map_ratCast, map_ratCast, conj_b]`. Conclude with `add_mem (rat_mem D p) (mul_mem (rat_mem D q) (neg_mem (FL.bE_mem D)))`.
-/
theorem conj_mem (k : D.host.K) : D.host.conj (k : D.host.E) ∈ D.host.K := by
  obtain ⟨p, q, e⟩ := CS.K_repr D _ k.2
  rw [e, map_add, map_mul, map_ratCast, map_ratCast, conj_b]
  exact add_mem (rat_mem D p) (mul_mem (rat_mem D q) (neg_mem (FL.bE_mem D)))

def cK : D.host.K →+* D.host.K where
  toFun k := ⟨D.host.conj (k : D.host.E), conj_mem D k⟩
  map_one' := Subtype.ext (by show D.host.conj ((1 : D.host.K) : D.host.E) = _; simp)
  map_mul' x y := Subtype.ext (by
    show D.host.conj ((x * y : D.host.K) : D.host.E) = D.host.conj x * D.host.conj y
    rw [IntermediateField.coe_mul, map_mul])
  map_zero' := Subtype.ext (by show D.host.conj ((0 : D.host.K) : D.host.E) = _; simp)
  map_add' x y := Subtype.ext (by
    show D.host.conj ((x + y : D.host.K) : D.host.E) = D.host.conj x + D.host.conj y
    rw [IntermediateField.coe_add, map_add])

def hK (x y : D.host.E) : D.host.K := Algebra.trace D.host.K D.host.E (x * D.host.conj y)

/- English proof (translation)
Rewrite using `[← Fintype.card_pos_iff, FL.card_tau]`. Check the signs of the components of the expression.
-/
theorem tau_nonempty : Nonempty D.what₂.Tau := by
  rw [← Fintype.card_pos_iff, FL.card_tau]; positivity

/- English proof (translation)
Simplify using `only [hK, add_mul, map_add] smul_left k x y := by simp only [hK, smul_mul_assoc, map_smul, smul_eq_mul]`. Use symmetry as in `x y := by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Use `show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (y * D.host.conj x) : D.host.K) : D.host.E) = D.host.φ₀ (D.host.conj ((Algebra.trace D.host.K D.host.E (x * D.host.conj y) : D.host.K) : D.host.E))`.

Rewrite using `[CU.emb_conj, ← FL.sum_tau_trace, ← FL.sum_tau_trace, map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, CU.emb_conj, CU.emb_conj, Complex.conj_conj, mul_comm]`. Use `pos x hx := by`. Establish `hφ : D.host.φ₀ ((hK D x x : D.host.K) : D.host.E) = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ)` using `by show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _`.

Rewrite using `[← FL.sum_tau_trace]`. Use `push_cast`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, CU.emb_conj, Complex.mul_conj]`. Establish `hpos : 0 < ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x)` using `by haveI := tau_nonempty D`.

Conclude with `Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ((map_ne_zero _).2 hx)) Finset.univ_nonempty`. Take `⟨p, q, e⟩` from `CS.K_repr D _ (hK D x x).2`. Establish `hs` using `IO.sqrt_d_pos D`. Rewrite `hφ` using `[e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]`. Establish `him` using `congrArg Complex.im hφ`.

Establish `hre` using `congrArg Complex.re hφ`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre`. Establish `hq : (q : ℝ) = 0`. Establish `: (q : ℝ) * Real.sqrt D.host.d = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hs.ne'`. Establish `hq' : q = 0` using `by exact_mod_cast hq`. Establish `hp : (0 : ℝ) < (p : ℝ)` using `by rw [hq] at hre; linarith`. Establish `hp' : 0 < p` using `by exact_mod_cast hp`.

Establish `hKp : hK D x x = ((p : ℚ) : D.host.K)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e, hq']`. Use `show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)`. Rewrite using `[map_ratCast]`.

Simplify using the standard rewrite rules. Take `⟨a, b, c, d, h4⟩` from `FS.rat_four_sq p hp'.le`. Use `⟨by rw [hKp]; exact Rat.cast_ne_zero.2 hp'.ne', (a : D.host.K), (b : D.host.K), (c : D.host.K), (d : D.host.K), map_ratCast _ a, map_ratCast _ b, map_ratCast _ c, map_ratCast _ d, ?_⟩` and prove the remaining obligations. Rewrite using `[hKp, h4]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm : FS.Herm4 (cK D) (hK D) where
  add_left x x' y := by simp only [hK, add_mul, map_add]
  smul_left k x y := by simp only [hK, smul_mul_assoc, map_smul, smul_eq_mul]
  symm x y := by
    apply Subtype.ext
    apply D.host.φ₀.injective
    show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (y * D.host.conj x) : D.host.K) : D.host.E)
      = D.host.φ₀ (D.host.conj ((Algebra.trace D.host.K D.host.E (x * D.host.conj y) : D.host.K) : D.host.E))
    rw [CU.emb_conj, ← FL.sum_tau_trace, ← FL.sum_tau_trace, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_mul, map_mul, CU.emb_conj, CU.emb_conj, Complex.conj_conj, mul_comm]
  pos x hx := by
    have hφ : D.host.φ₀ ((hK D x x : D.host.K) : D.host.E)
        = ((∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) : ℝ) : ℂ) := by
      show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (x * D.host.conj x) : D.host.K) : D.host.E) = _
      rw [← FL.sum_tau_trace]
      push_cast
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, CU.emb_conj, Complex.mul_conj]
    have hpos : 0 < ∑ τ : D.what₂.Tau, Complex.normSq (embT D τ x) := by
      haveI := tau_nonempty D
      exact Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ((map_ne_zero _).2 hx)) Finset.univ_nonempty
    obtain ⟨p, q, e⟩ := CS.K_repr D _ (hK D x x).2
    have hs := IO.sqrt_d_pos D
    rw [e, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d] at hφ
    have him := congrArg Complex.im hφ
    have hre := congrArg Complex.re hφ
    simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re] at him hre
    have hq : (q : ℝ) = 0 := by
      have : (q : ℝ) * Real.sqrt D.host.d = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hs.ne'
    have hq' : q = 0 := by exact_mod_cast hq
    have hp : (0 : ℝ) < (p : ℝ) := by rw [hq] at hre; linarith
    have hp' : 0 < p := by exact_mod_cast hp
    have hKp : hK D x x = ((p : ℚ) : D.host.K) := by
      apply Subtype.ext
      rw [e, hq']
      show _ = algebraMap D.host.K D.host.E ((p : ℚ) : D.host.K)
      rw [map_ratCast]; simp
    obtain ⟨a, b, c, d, h4⟩ := FS.rat_four_sq p hp'.le
    refine ⟨by rw [hKp]; exact Rat.cast_ne_zero.2 hp'.ne', (a : D.host.K), (b : D.host.K), (c : D.host.K), (d : D.host.K),
      map_ratCast _ a, map_ratCast _ b, map_ratCast _ c, map_ratCast _ d, ?_⟩
    rw [hKp, h4]; push_cast; ring

/- English proof (translation)
Use `letI := FL.algKC D`. Rewrite using `[← AlgHom.card D.host.K D.host.E ℂ]`. Conclude with `Fintype.card_of_bijective (FL.embA_bij D)`.
-/
theorem card_eq : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  letI := FL.algKC D
  rw [← AlgHom.card D.host.K D.host.E ℂ]
  exact Fintype.card_of_bijective (FL.embA_bij D)

/- English proof (translation)
Take `⟨g, hg⟩` from `(herm D).iso (n := D.what₂.Tau) (card_eq D)`. Use `⟨⟨g, fun x y => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hg x y`. Establish `h2 : (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a))) = ∑ w, g x w * cK D (g y w)` using `h.symm`. Rewrite using `[h2, map_sum]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem iso0 : Nonempty (IsoK D) := by
  obtain ⟨g, hg⟩ := (herm D).iso (n := D.what₂.Tau) (card_eq D)
  refine ⟨⟨g, fun x y => ?_⟩⟩
  have h := hg x y
  have h2 : (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a))) = ∑ w, g x w * cK D (g y w) := h.symm
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul]
  rfl

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.G0

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkIso0 : Prop := ∀ D : Car, Nonempty (IsoK D)

def LinkBaseP : Prop := ∀ D : Car, IsoPExists D → BaseExists D

def LinkTrivialLevelIsometry : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

/- English proof (translation)
The claim follows from `G0.iso0`.
-/
theorem isometry_linkage_trivial_level : LinkIso0 := G0.iso0

/- English proof (translation)
Introduce `D hp` and use `base_exists_link D (isometry_extension_link D (isometry_linkage_trivial_level D)) hp`.
-/
theorem base_linkage_at_prime : LinkBaseP :=
  fun D hp => base_exists_link D (isometry_extension_link D (isometry_linkage_trivial_level D)) hp

/- English proof (translation)
Introduce `D C hA hper hΔ hp h` and use `provision_extension_link D C hA hper hΔ (isometry_linkage_trivial_level D) hp h`.
-/
theorem eigen_linkage_at_prime : LinkTrivialLevelIsometry :=
  fun D C hA hper hΔ hp h => provision_extension_link D C hA hper hΔ (isometry_linkage_trivial_level D) hp h

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
