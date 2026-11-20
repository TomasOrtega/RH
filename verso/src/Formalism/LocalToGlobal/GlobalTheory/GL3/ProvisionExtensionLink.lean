import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.FrobeniusOrbits Classical

def LinkStdOK : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK

def LinkVecB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → NonzeroThetaVectorFamily D (tor0 D cc δ) (B.eNat χ)

def LinkThB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ →
      ThetaNormIndependent D (tor0 D cc δ) (B.eNat χ) ∧ th22U D (tor0 D cc δ) (B.eNat χ)

def LinkNormB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (B.eNat χ N N' L L')
        = normSq D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (B.thZero N N')

def LinkExistsBase : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

/- English proof (translation)
Introduce `_ _ hcc _ hδ B` and use `SO.stdOK B hcc hδ`.
-/
theorem standard_basis_ok_link : LinkStdOK := fun _ _ hcc _ hδ B => SO.stdOK B hcc hδ

/- English proof (translation)
Introduce `D cc hcc δ hδ B` and use `vector_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)`.
-/
theorem vector_bound_link : LinkVecB :=
  fun D cc hcc δ hδ B => vector_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)

/- English proof (translation)
Introduce `D cc hcc δ hδ B` and use `theta_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)`.
-/
theorem theta_bound_link : LinkThB :=
  fun D cc hcc δ hδ B => theta_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)

/- English proof (translation)
Introduce `D cc hcc δ hδ B χ hχ _ _ _ _ hA` and use `B.eNat_normSq hcc hδ (base_linkage_nonempty D cc δ B) (SO.stdOK B hcc hδ) χ hχ hA`.
-/
theorem norm_bound_link : LinkNormB :=
  fun D cc hcc δ hδ B χ hχ _ _ _ _ hA =>
    B.eNat_normSq hcc hδ (base_linkage_nonempty D cc δ B) (SO.stdOK B hcc hδ) χ hχ hA

/- English proof (translation)
Introduce `D C hA hper h`. Use `eigen_linkage_holds D C hA hper fun cc hcc δ hδ => ?_` and prove the remaining obligations. Take `⟨B, hB⟩` from `h cc hcc δ hδ`. Conclude with `⟨B, SO.stdOK B hcc hδ, hB⟩`.
-/
theorem provision_bound_link : LinkExistsBase := by
  intro D C hA hper h
  refine eigen_linkage_holds D C hA hper fun cc hcc δ hδ => ?_
  obtain ⟨B, hB⟩ := h cc hcc δ hδ
  exact ⟨B, SO.stdOK B hcc hδ, hB⟩

def LinkPeriodPair : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ δ : ℂ, δ ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = lamOf D cc δ

def BasePointExists : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∃ t : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t

def IsoExists (D : D7) : Prop :=
  ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    ∀ x : Fin 4 → D.host.E, gC (fun w => embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)

def IsoPExists (D : D7) : Prop :=
  ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p

def LinkBase : Prop :=
  ∀ D : D7, IsoExists D → IsoPExists D → BaseExists D

/- English proof (translation)
Take `⟨c1, hc1, c2, hc2, hspan, hind⟩` from `CS.cc_basis D cc hcc`. Use `set w1 := δ * D.host.φ₀ (((c1 : D.host.K) : D.host.E)) with hw1`. Use `set w2 := δ * D.host.φ₀ (((c2 : D.host.K) : D.host.E)) with hw2`. Establish `h1 : w1 ∈ lamOf D cc δ` using `AddSubgroup.subset_closure ⟨c1, hc1, rfl⟩`. Establish `h2 : w2 ∈ lamOf D cc δ` using `AddSubgroup.subset_closure ⟨c2, hc2, rfl⟩`.

Establish `hb : ∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2`. Introduce `w hw`. Take `⟨c, hc, rfl⟩` from `FL.lam_mem D cc δ w hw`. Take `⟨m, n, rfl⟩` from `hspan c hc`. Use `⟨m, n, ?_⟩` and prove the remaining obligations.

Establish `e : ((((m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2 : 𝓞 D.host.K) : D.host.K) : D.host.E) = (m : D.host.E) * ((c1 : D.host.K) : D.host.E) + (n : D.host.E) * ((c2 : D.host.K) : D.host.E)`. Rewrite using `[← CS.coe_intO D m, ← CS.coe_intO D n]`. Both sides reduce to the same expression. Rewrite using `[e, hw1, hw2, map_add, map_mul, map_mul, map_intCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨w1, h1, w2, h2, hb, ?_⟩` and prove the remaining obligations. Take `⟨p1, q1, e1⟩` from `CS.K_repr D _ (c1 : D.host.K).2`. Take `⟨p2, q2, e2⟩` from `CS.K_repr D _ (c2 : D.host.K).2`. Establish `hφ1 : D.host.φ₀ ((c1 : D.host.K) : D.host.E) = (p1 : ℂ) + (q1 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))`. Rewrite using `[e1, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]`.

Establish `hφ2 : D.host.φ₀ ((c2 : D.host.K) : D.host.E) = (p2 : ℂ) + (q2 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))`. Rewrite using `[e2, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]`. Establish `him : (starRingEnd ℂ w1 * w2).im = Complex.normSq δ * (((p1 * q2 - q1 * p2 : ℚ) : ℝ) * Real.sqrt D.host.d)`. Rewrite using `[hw1, hw2, CS.im_conj_mul, hφ1, hφ2]`. Use `congr 1`.

Simplify using `only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, map_ratCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[him]`. Establish `hsd : 0 < Real.sqrt D.host.d` using `IO.sqrt_d_pos D`.

Establish `hnδ : 0 < Complex.normSq δ` using `Complex.normSq_pos.mpr hδ`. Introduce `h0`. Establish `hpqR : ((p1 * q2 - q1 * p2 : ℚ) : ℝ) = 0`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd h hnδ.ne'`.

Break down `mul_eq_zero.mp h with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd h' hsd.ne'`. Establish `hpq : p1 * q2 - q1 * p2 = 0` using `by exact_mod_cast hpqR`. Establish `hpqE : (p1 : D.host.E) * q2 - q1 * p2 = 0`.

Use `congrArg (fun t : ℚ => (t : D.host.E)) hpq` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Distinguish the cases in `hq : q1 = 0 ∧ q2 = 0`. Establish `r` using `hind p2 (-p1) (by rw [e1, e2, hq.1, hq.2]; push_cast; ring)`.

Establish `hp1 : p1 = 0` using `by linarith [r.2]`. Establish `r2` using `hind 1 0 (by rw [e1, hp1, hq.1]; push_cast; ring)`. Conclude with `one_ne_zero r2.1`. Establish `r` using `hind q2 (-q1) (by rw [e1, e2]; push_cast; linear_combination hpqE)`. Conclude with `hq ⟨by linarith [r.2], r.1⟩`.
-/
theorem lam_basis (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w1 ∈ lamOf D cc δ, ∃ w2 ∈ lamOf D cc δ,
      (∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2) ∧ (starRingEnd ℂ w1 * w2).im ≠ 0 := by
  obtain ⟨c1, hc1, c2, hc2, hspan, hind⟩ := CS.cc_basis D cc hcc
  set w1 := δ * D.host.φ₀ (((c1 : D.host.K) : D.host.E)) with hw1
  set w2 := δ * D.host.φ₀ (((c2 : D.host.K) : D.host.E)) with hw2
  have h1 : w1 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c1, hc1, rfl⟩
  have h2 : w2 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c2, hc2, rfl⟩
  have hb : ∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2 := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
    obtain ⟨m, n, rfl⟩ := hspan c hc
    refine ⟨m, n, ?_⟩
    have e : ((((m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2 : 𝓞 D.host.K) : D.host.K) : D.host.E) =
        (m : D.host.E) * ((c1 : D.host.K) : D.host.E) + (n : D.host.E) * ((c2 : D.host.K) : D.host.E) := by
      rw [← CS.coe_intO D m, ← CS.coe_intO D n]
      rfl
    rw [e, hw1, hw2, map_add, map_mul, map_mul, map_intCast, map_intCast]
    ring
  refine ⟨w1, h1, w2, h2, hb, ?_⟩
  obtain ⟨p1, q1, e1⟩ := CS.K_repr D _ (c1 : D.host.K).2
  obtain ⟨p2, q2, e2⟩ := CS.K_repr D _ (c2 : D.host.K).2
  have hφ1 : D.host.φ₀ ((c1 : D.host.K) : D.host.E) =
      (p1 : ℂ) + (q1 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [e1, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
  have hφ2 : D.host.φ₀ ((c2 : D.host.K) : D.host.E) =
      (p2 : ℂ) + (q2 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [e2, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
  have him : (starRingEnd ℂ w1 * w2).im =
      Complex.normSq δ * (((p1 * q2 - q1 * p2 : ℚ) : ℝ) * Real.sqrt D.host.d) := by
    rw [hw1, hw2, CS.im_conj_mul, hφ1, hφ2]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
      Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, map_ratCast]
    push_cast
    ring
  rw [him]
  have hsd : 0 < Real.sqrt D.host.d := IO.sqrt_d_pos D
  have hnδ : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
  intro h0
  have hpqR : ((p1 * q2 - q1 * p2 : ℚ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hnδ.ne'
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hsd.ne'
  have hpq : p1 * q2 - q1 * p2 = 0 := by exact_mod_cast hpqR
  have hpqE : (p1 : D.host.E) * q2 - q1 * p2 = 0 := by
    have := congrArg (fun t : ℚ => (t : D.host.E)) hpq
    push_cast at this
    exact this
  by_cases hq : q1 = 0 ∧ q2 = 0
  · have r := hind p2 (-p1) (by rw [e1, e2, hq.1, hq.2]; push_cast; ring)
    have hp1 : p1 = 0 := by linarith [r.2]
    have r2 := hind 1 0 (by rw [e1, hp1, hq.1]; push_cast; ring)
    exact one_ne_zero r2.1
  · have r := hind q2 (-q1) (by rw [e1, e2]; push_cast; linear_combination hpqE)
    exact hq ⟨by linarith [r.2], r.1⟩

/- English proof (translation)
Introduce `D cc hcc δ hδ`. Take `⟨w1, h1, w2, h2, hb, hD⟩` from `lam_basis D cc hcc δ hδ`. Establish `hind : LinearIndependent ℝ ![w1, w2]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Simplify using `only [Complex.real_smul] at hst`. Establish `a1 : (starRingEnd ℂ w1 * ((s : ℂ) * w1 + (t : ℂ) * w2)).im = t * (starRingEnd ℂ w1 * w2).im`. Establish `: starRingEnd ℂ w1 * ((s : ℂ) * w1 + (t : ℂ) * w2) = ((s * Complex.normSq w1 : ℝ) : ℂ) + (t : ℂ) * (starRingEnd ℂ w1 * w2)` using `by push_cast; rw [Complex.normSq_eq_conj_mul_self]; ring`. Rewrite using `[this, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add]`. Establish `a2 : (((s : ℂ) * w1 + (t : ℂ) * w2) * starRingEnd ℂ w2).im = -(s * (starRingEnd ℂ w1 * w2).im)`.

Establish `: ((s : ℂ) * w1 + (t : ℂ) * w2) * starRingEnd ℂ w2 = (s : ℂ) * starRingEnd ℂ (starRingEnd ℂ w1 * w2) + ((t * Complex.normSq w2 : ℝ) : ℂ)` using `by push_cast; rw [Complex.normSq_eq_conj_mul_self, map_mul, Complex.conj_conj]; ring`. Rewrite using `[this, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.conj_im, add_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `a1`, `a2` using `[hst]`. Simplify using `only [mul_zero, zero_mul, Complex.zero_im] at a1 a2`.

Prove the components needed by the constructor for the conclusion. Break down `mul_eq_zero.mp (neg_eq_zero.mp a2.symm) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hD`. Break down `mul_eq_zero.mp a1.symm with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hD`. Use `⟨⟨w1, w2, hind⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Take `⟨m, n, rfl⟩` from `PeriodPair.mem_lattice.mp hw`. Establish `e1 : (m : ℂ) * w1 = m • w1` using `by simp`. Establish `e2 : (n : ℂ) * w2 = n • w2` using `by simp`. Use `show (m : ℂ) * w1 + (n : ℂ) * w2 ∈ lamOf D cc δ`.

Rewrite using `[e1, e2]`. Conclude with `add_mem (AddSubgroup.zsmul_mem _ h1 m) (AddSubgroup.zsmul_mem _ h2 n)`. Introduce `hw`. Take `⟨m, n, rfl⟩` from `hb w hw`. Conclude with `PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩`.
-/
theorem period_pair_link : LinkPeriodPair := by
  intro D cc hcc δ hδ
  obtain ⟨w1, h1, w2, h2, hb, hD⟩ := lam_basis D cc hcc δ hδ
  have hind : LinearIndependent ℝ ![w1, w2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Complex.real_smul] at hst
    have a1 : (starRingEnd ℂ w1 * ((s : ℂ) * w1 + (t : ℂ) * w2)).im = t * (starRingEnd ℂ w1 * w2).im := by
      have : starRingEnd ℂ w1 * ((s : ℂ) * w1 + (t : ℂ) * w2)
          = ((s * Complex.normSq w1 : ℝ) : ℂ) + (t : ℂ) * (starRingEnd ℂ w1 * w2) := by
        push_cast; rw [Complex.normSq_eq_conj_mul_self]; ring
      rw [this, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add]
    have a2 : (((s : ℂ) * w1 + (t : ℂ) * w2) * starRingEnd ℂ w2).im = -(s * (starRingEnd ℂ w1 * w2).im) := by
      have : ((s : ℂ) * w1 + (t : ℂ) * w2) * starRingEnd ℂ w2
          = (s : ℂ) * starRingEnd ℂ (starRingEnd ℂ w1 * w2) + ((t * Complex.normSq w2 : ℝ) : ℂ) := by
        push_cast; rw [Complex.normSq_eq_conj_mul_self, map_mul, Complex.conj_conj]; ring
      rw [this, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.conj_im, add_zero]; ring
    rw [hst] at a1 a2
    simp only [mul_zero, zero_mul, Complex.zero_im] at a1 a2
    constructor
    · rcases mul_eq_zero.mp (neg_eq_zero.mp a2.symm) with h | h
      · exact h
      · exact absurd h hD
    · rcases mul_eq_zero.mp a1.symm with h | h
      · exact h
      · exact absurd h hD
  refine ⟨⟨w1, w2, hind⟩, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
    have e1 : (m : ℂ) * w1 = m • w1 := by simp
    have e2 : (n : ℂ) * w2 = n • w2 := by simp
    show (m : ℂ) * w1 + (n : ℂ) * w2 ∈ lamOf D cc δ
    rw [e1, e2]
    exact add_mem (AddSubgroup.zsmul_mem _ h1 m) (AddSubgroup.zsmul_mem _ h2 n)
  · intro hw
    obtain ⟨m, n, rfl⟩ := hb w hw
    exact PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩

/- English proof (translation)
Introduce `D cc hcc δ hδ`. Use `set n : ℕ := Ideal.absNorm cc with hn`. Establish `hodd : Odd n`. Establish `h` using `Nat.Coprime.coprime_mul_right_right hcc.2`. Break down `Nat.even_or_odd n with he | ho` into its components or cases.

It suffices to derive a contradiction. Establish `h2` using `Nat.dvd_gcd he.two_dvd (dvd_refl 2)`. Rewrite `h2` using `[show Nat.gcd n 2 = 1 from h]`. Use linear arithmetic over natural numbers and integers. Conclude with `ho`.

Establish `hmem : (n : 𝓞 D.host.K) ∈ cc` using `Ideal.absNorm_mem cc`. Establish `hφ : D.host.φ₀ ((((n : 𝓞 D.host.K)) : D.host.K) : D.host.E) = (n : ℂ)`. Establish `e : ((n : ℕ) : 𝓞 D.host.K) = (((n : ℤ)) : 𝓞 D.host.K)` using `(Int.cast_natCast n).symm`. Rewrite using `[e, CS.coe_intO, map_intCast, Int.cast_natCast]`. Establish `hs : (0 : ℝ) < Real.sqrt D.host.d` using `IO.sqrt_d_pos D`.

Establish `key : ∀ ε : ℂ, ε.re = 1 / 2 → ε * (δ * (n : ℂ) / 2) ∉ lamOf D cc δ`. Introduce `ε hε hmem'`. Take `⟨c, -, hc⟩` from `FL.lam_mem D cc δ _ hmem'`. Establish `h1 : D.host.φ₀ ((c : D.host.K) : D.host.E) = ε * (n : ℂ) / 2`. Apply `mul_left_cancel₀ hδ` to reduce the goal to its premises.

Rewrite using `[← hc]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x, y, -, hxy⟩` from `AR.okc_of D c`. Rewrite `hxy` using `[h1]`. Establish `h2` using `congrArg Complex.re hxy`.

Establish `l : (ε * (n : ℂ) / 2).re = (n : ℝ) / 4`. Establish `: ε * (n : ℂ) / 2 = (((n : ℝ) / 2 : ℝ) : ℂ) * ε` using `by push_cast; ring`. Rewrite using `[this, Complex.re_ofReal_mul, hε]`. Expand and normalize the polynomial expressions, which then agree. Establish `r : (((x : ℂ) + (y : ℂ) * AR.be D) / 2).re = (x : ℝ) / 2`.

Establish `: ((x : ℂ) + (y : ℂ) * AR.be D) / 2 = (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[l, r]`. Establish `h3 : (n : ℤ) = 2 * x`.

Establish `: (n : ℝ) = 2 * (x : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Take `⟨j, hj⟩` from `hodd`. Use linear arithmetic over natural numbers and integers. Use `⟨δ * (n : ℂ) / 2, ?_, key _ (by simp), key _ (by simp)⟩` and prove the remaining obligations.

Establish `: 2 * (δ * (n : ℂ) / 2) = δ * D.host.φ₀ ((((n : 𝓞 D.host.K)) : D.host.K) : D.host.E)` using `by rw [hφ]; ring`. Rewrite using `[this]`. Conclude with `AddSubgroup.subset_closure ⟨_, hmem, rfl⟩`.
-/
theorem basePointExists : BasePointExists := by
  intro D cc hcc δ hδ
  set n : ℕ := Ideal.absNorm cc with hn
  have hodd : Odd n := by
    have h := Nat.Coprime.coprime_mul_right_right hcc.2
    rcases Nat.even_or_odd n with he | ho
    · exfalso
      have h2 := Nat.dvd_gcd he.two_dvd (dvd_refl 2)
      rw [show Nat.gcd n 2 = 1 from h] at h2
      omega
    · exact ho
  have hmem : (n : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  have hφ : D.host.φ₀ ((((n : 𝓞 D.host.K)) : D.host.K) : D.host.E) = (n : ℂ) := by
    have e : ((n : ℕ) : 𝓞 D.host.K) = (((n : ℤ)) : 𝓞 D.host.K) := (Int.cast_natCast n).symm
    rw [e, CS.coe_intO, map_intCast, Int.cast_natCast]
  have hs : (0 : ℝ) < Real.sqrt D.host.d := IO.sqrt_d_pos D
  have key : ∀ ε : ℂ, ε.re = 1 / 2 → ε * (δ * (n : ℂ) / 2) ∉ lamOf D cc δ := by
    intro ε hε hmem'
    obtain ⟨c, -, hc⟩ := FL.lam_mem D cc δ _ hmem'
    have h1 : D.host.φ₀ ((c : D.host.K) : D.host.E) = ε * (n : ℂ) / 2 := by
      apply mul_left_cancel₀ hδ
      rw [← hc]; ring
    obtain ⟨x, y, -, hxy⟩ := AR.okc_of D c
    rw [h1] at hxy
    have h2 := congrArg Complex.re hxy
    have l : (ε * (n : ℂ) / 2).re = (n : ℝ) / 4 := by
      have : ε * (n : ℂ) / 2 = (((n : ℝ) / 2 : ℝ) : ℂ) * ε := by push_cast; ring
      rw [this, Complex.re_ofReal_mul, hε]; ring
    have r : (((x : ℂ) + (y : ℂ) * AR.be D) / 2).re = (x : ℝ) / 2 := by
      have : ((x : ℂ) + (y : ℂ) * AR.be D) / 2
          = (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this]; simp
    rw [l, r] at h2
    have h3 : (n : ℤ) = 2 * x := by
      have : (n : ℝ) = 2 * (x : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨j, hj⟩ := hodd
    omega
  refine ⟨δ * (n : ℂ) / 2, ?_, key _ (by simp), key _ (by simp)⟩
  have : 2 * (δ * (n : ℂ) / 2) = δ * D.host.φ₀ ((((n : 𝓞 D.host.K)) : D.host.K) : D.host.E) := by rw [hφ]; ring
  rw [this]
  exact AddSubgroup.subset_closure ⟨_, hmem, rfl⟩

/- English proof (translation)
Introduce `D h1 h2 cc hcc δ hδ` and use `Base.nonempty_of cc δ (period_pair_link D cc hcc.1 δ hδ) (basePointExists D cc hcc δ hδ) h1 h2`.
-/
theorem base_exists_link : LinkBase :=
  fun D h1 h2 cc hcc δ hδ =>
    Base.nonempty_of cc δ (period_pair_link D cc hcc.1 δ hδ) (basePointExists D cc hcc δ hδ) h1 h2

/- English proof (translation)
Establish `repr : ∀ x, x = ∑ v, (g x v) • g.symm (Pi.single v 1)`. Introduce `x`. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Repeatedly rewrite using `[map_smul, LinearEquiv.apply_symm_apply]`.

Use function extensionality and compare the values at `w`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Set `hC : (I → ℂ) →ₗ[ℂ] (I → ℂ)` to `{ toFun := fun c => ∑ v, c v • em (g.symm (Pi.single v 1)) map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib] map_smul' := by intro a b; simp [Finset.smul_sum, mul_smul] }`. Establish `key : ∀ x, hC (fun w => φ (g x w)) = em x`. Introduce `x`.

Use `conv_rhs => rw [repr x]`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[hem]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective hC`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨_, key x⟩`. Establish `hinj : Function.Injective hC` using `LinearMap.injective_iff_surjective.2 hsurj`. Use `⟨(LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩).symm, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← key x]`. Conclude with `LinearEquiv.symm_apply_apply (LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩) _`.
-/
theorem ext_exists {K E : Type} [Field K] [Field E] [Algebra K E] {I : Type} [Fintype I] [DecidableEq I]
    (g : (Fin 4 → E) ≃ₗ[K] (I → K)) (φ : K →+* ℂ) (em : (Fin 4 → E) →+ (I → ℂ))
    (hem : ∀ (k : K) (y : Fin 4 → E), em (k • y) = φ k • em y)
    (hspan : Submodule.span ℂ (Set.range em) = ⊤) :
    ∃ G : (I → ℂ) ≃ₗ[ℂ] (I → ℂ), ∀ x, G (em x) = fun w => φ (g x w) := by
  have repr : ∀ x, x = ∑ v, (g x v) • g.symm (Pi.single v 1) := by
    intro x
    apply g.injective
    rw [map_sum]
    simp_rw [map_smul, LinearEquiv.apply_symm_apply]
    funext w
    simp [Finset.sum_apply, Pi.single_apply]
  let hC : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
    { toFun := fun c => ∑ v, c v • em (g.symm (Pi.single v 1))
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum, mul_smul] }
  have key : ∀ x, hC (fun w => φ (g x w)) = em x := by
    intro x
    conv_rhs => rw [repr x]
    rw [map_sum]
    simp_rw [hem]
    rfl
  have hsurj : Function.Surjective hC := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, key x⟩
  have hinj : Function.Injective hC := LinearMap.injective_iff_surjective.2 hsurj
  refine ⟨(LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
  rw [← key x]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩) _

def LinkIsoExt : Prop := ∀ D : D7, Nonempty (IsoK D) → IsoExists D

/- English proof (translation)
Introduce and unpack `D ⟨γ⟩`. Set `em : (Fin 4 → D.host.E) →+ (Fin 4 × D.what₂.Tau → ℂ)` to `{ toFun := emb4 D map_zero' := by funext w; simp [emb4] map_add' := by intro x y; funext w; simp [emb4] }`. Take `⟨G, hG⟩` from `ext_exists γ.g (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) em (by`. Introduce `k y`. Use function extensionality and compare the values at `w`.

Use `show embT D w.2 (k • y w.1) = D.host.φ₀ (algebraMap D.host.K D.host.E k) * embT D w.2 (y w.1)`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `congrArg (· * embT D w.2 (y w.1)) (FL.embT_K D w.2 _ k.2))`. Use the proof step `(span_range_emb4_eq_top D)`. Conclude with `⟨γ, G, hG⟩`.
-/
theorem isometry_extension_link : LinkIsoExt := by
  rintro D ⟨γ⟩
  let em : (Fin 4 → D.host.E) →+ (Fin 4 × D.what₂.Tau → ℂ) :=
    { toFun := emb4 D
      map_zero' := by funext w; simp [emb4]
      map_add' := by intro x y; funext w; simp [emb4] }
  obtain ⟨G, hG⟩ := ext_exists γ.g (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) em
    (by
      intro k y
      funext w
      show embT D w.2 (k • y w.1) = D.host.φ₀ (algebraMap D.host.K D.host.E k) * embT D w.2 (y w.1)
      rw [Algebra.smul_def, map_mul]
      exact congrArg (· * embT D w.2 (y w.1)) (FL.embT_K D w.2 _ k.2))
    (span_range_emb4_eq_top D)
  exact ⟨γ, G, hG⟩

def DiscrNe (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → discr (lamOf D cc 1) ≠ 0

def IsometryExtensionLink : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → Nonempty (IsoK D) → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

/- English proof (translation)
Introduce `D C hA hper hΔ hγ hp h`. Use `provision_bound_link D C hA hper fun cc hcc δ hδ => ?_` and prove the remaining obligations. Establish `h0 : δ ≠ 0`. Introduce `e`. Apply `hΔ cc hcc.1` to reduce the goal to its premises.

Rewrite using `[← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]`. Evaluate the numerical expressions. Take `⟨B⟩` from `base_exists_link D (isometry_extension_link D hγ) hp cc hcc δ h0`. Conclude with `⟨B, h cc hcc δ hδ B⟩`.
-/
theorem provision_extension_link : IsometryExtensionLink := by
  intro D C hA hper hΔ hγ hp h
  refine provision_bound_link D C hA hper fun cc hcc δ hδ => ?_
  have h0 : δ ≠ 0 := by
    intro e
    apply hΔ cc hcc.1
    rw [← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]
    norm_num
  obtain ⟨B⟩ := base_exists_link D (isometry_extension_link D hγ) hp cc hcc δ h0
  exact ⟨B, h cc hcc δ hδ B⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
