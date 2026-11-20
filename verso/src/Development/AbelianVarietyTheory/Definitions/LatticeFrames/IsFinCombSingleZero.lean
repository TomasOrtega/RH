import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Inh

variable {D : D7}

/- English proof (translation)
Introduce `u hu` and use `by have : u = 0 := Finset.mem_singleton.1 (Finsupp.support_single_subset hu) subst this exact Matrix.map_zero _ (map_zero (infPart D))`.
-/
theorem isFinComb_single_zero {S T : HSp D} (a : ℂ) : IsFinComb (Finsupp.single (0 : WO S T) a) := fun u hu => by
  have : u = 0 := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
  subst this
  exact Matrix.map_zero _ (map_zero (infPart D))

/- English proof (translation)
Distinguish the cases in `h : a = 0`. Simplify using `[comb, h]`. Simplify using `[comb, Finsupp.support_single_ne_zero _ h]`.
-/
theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  by_cases h : a = 0
  · simp [comb, h]
  · simp [comb, Finsupp.support_single_ne_zero _ h]

/- English proof (translation)
Take `⟨C, hC, rfl⟩` from `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp h.isStrictlyPositive`. Establish `hd : IsUnit C.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hC`. Use `⟨C⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ hd]`.
-/
theorem exists_onb {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : G.PosDef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ * G * B = 1 := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp h.isStrictlyPositive
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).1 hC
  refine ⟨C⁻¹, ?_⟩
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ hd]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Establish `hJ : Formalism.UG.Jpq 0 n = -1`. Unfold `Formalism.UG.Jpq`. Use extensionality with `(i | i) (j | j)`. Conclude with `i.elim0`.

Conclude with `i.elim0`. Conclude with `j.elim0`. Simplify using `[Matrix.one_apply]`. Establish `hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ) = star (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ)`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT, Matrix.star_apply]`. Rewrite `hP` using `[hJ, hc]`. Establish `h1 : star (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ) * (-(Matrix.reindex e e G)) * P = 1`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hP, neg_neg]`. Establish `h2 : (-(Matrix.reindex e e G)).PosDef`.

Rewrite using `[← P.isUnit.posDef_star_left_conjugate_iff, h1]`. Conclude with `Matrix.PosDef.one`. Establish `h3` using `h2.submatrix e.injective`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem posDef_neg_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G 0 n) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq 0 n = -1 := by
    unfold Formalism.UG.Jpq
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Matrix.one_apply]
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ) =
      star (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.star_apply]
  rw [hJ, hc] at hP
  have h1 : star (P : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ) * (-(Matrix.reindex e e G)) * P = 1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hP, neg_neg]
  have h2 : (-(Matrix.reindex e e G)).PosDef := by
    rw [← P.isUnit.posDef_star_left_conjugate_iff, h1]
    exact Matrix.PosDef.one
  have h3 := h2.submatrix e.injective
  convert h3 using 1
  ext i j
  simp

/- English proof (translation)
Break down `h with h | h` into its components or cases. Establish `hp` using `Formalism.IndefR.Fin.Lifts.posDef_of_sig G h`. Take `⟨B, hB⟩` from `exists_onb hp`. Use `⟨1, B, ⟨by simp, by simp, by simpa using hp⟩, Or.inl rfl, n, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hB`.

Simplify using the standard rewrite rules. Establish `hp` using `posDef_neg_of_sig G h`. Take `⟨B, hB⟩` from `exists_onb hp`. Establish `e : (Matrix.diagonal fun _ : Fin n => (-1 : ℂ)) = -1`. Rewrite using `[← Matrix.diagonal_one, Matrix.diagonal_neg]`.

Use `⟨-1, B, ⟨by simp, by simp, by simpa using hp⟩, Or.inr rfl, 0, fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hB` using `[Matrix.mul_neg, Matrix.neg_mul]`. Use `push_cast`. Rewrite using `[e, ← hB, neg_neg]`. Use `push_cast`.

Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem exists_cartan_pm {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0 ∨ Formalism.UG.HasSignature G 0 n) :
    ∃ s B : Matrix (Fin n) (Fin n) ℂ, IsCartanInv G s ∧ (s = 1 ∨ s = -1) ∧ ∃ p, IsONBasis G s B p := by
  rcases h with h | h
  · have hp := Formalism.IndefR.Fin.Lifts.posDef_of_sig G h
    obtain ⟨B, hB⟩ := exists_onb hp
    refine ⟨1, B, ⟨by simp, by simp, by simpa using hp⟩, Or.inl rfl, n, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simpa using hB
    · simp
  · have hp := posDef_neg_of_sig G h
    obtain ⟨B, hB⟩ := exists_onb hp
    have e : (Matrix.diagonal fun _ : Fin n => (-1 : ℂ)) = -1 := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
    refine ⟨-1, B, ⟨by simp, by simp, by simpa using hp⟩, Or.inr rfl, 0, fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩
    · rw [Matrix.mul_neg, Matrix.neg_mul] at hB
      push_cast
      rw [e, ← hB, neg_neg]
    · push_cast
      rw [e]; simp

/- English proof (translation)
The claim follows from `GlobalTheory.Unf.Inhab.coCpt_of_isAniso (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hs hd)`.
-/
theorem coCpt_of_isDefinite {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) : CoCpt V :=
  GlobalTheory.Unf.Inhab.coCpt_of_isAniso (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hs hd)

/- English proof (translation)
Establish `h : ∀ τ, ∃ s B, IsCartanInv (gramAt D V τ) s ∧ (s = 1 ∨ s = -1) ∧ ∃ p, IsONBasis (gramAt D V τ) s B p` using `fun τ => by`. Use `exists_cartan_pm _ ?_` and prove the remaining obligations. Establish `h1` using `hs (tauE D τ)`. Apply the tactic sequence `rcases hd (tauE D τ) with h2 | h2 <;> rw [h2] at h1`. Conclude with `Or.inl h1`.

Conclude with `Or.inr h1`. Use `choose s B h1 h2 h3 using h`. Conclude with `⟨⟨s, B, _, (GlobalTheory.Unf.Inhab.nonempty_vol V).some⟩, hs, coCpt_of_isDefinite hs hd, h1, h2, h3, GlobalTheory.PlaceModel.isSelfDualC_latFrame V⟩`.
-/
theorem exists_defSp {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) : ∃ x : DefSp V, x.Is := by
  have h : ∀ τ, ∃ s B, IsCartanInv (gramAt D V τ) s ∧ (s = 1 ∨ s = -1) ∧ ∃ p, IsONBasis (gramAt D V τ) s B p := fun τ => by
    refine exists_cartan_pm _ ?_
    have h1 := hs (tauE D τ)
    rcases hd (tauE D τ) with h2 | h2 <;> rw [h2] at h1
    · exact Or.inl h1
    · exact Or.inr h1
  choose s B h1 h2 h3 using h
  exact ⟨⟨s, B, _, (GlobalTheory.Unf.Inhab.nonempty_vol V).some⟩, hs, coCpt_of_isDefinite hs hd, h1, h2, h3,
    GlobalTheory.PlaceModel.isSelfDualC_latFrame V⟩

/- English proof (translation)
The claim follows from `exists_defSp (D.sp.X_sig j) (D.sp.X_def j hj)`.
-/
theorem exists_defSp_X (D : D7) (j : ℕ) (hj : j ≤ D.R.m) : ∃ x : DefSp (D.sp.X j), x.Is :=
  exists_defSp (D.sp.X_sig j) (D.sp.X_def j hj)

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨⟨p, hp⟩, h2⟩` from `h.2.norm`. Use `h2 p hp` as an intermediate fact. Simplify using `[nrm2] at this`.
-/
theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, h2⟩ := h.2.norm
  have := h2 p hp
  simp [nrm2] at this

/- English proof (translation)
Take `⟨χS, χT, om, hom⟩` from `GlobalTheory.Unf.Inhab.exists_weil_pair hψ S T`. Take `⟨f, hf⟩` from `GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ _ _ _ _ hx.sig hy.sig hx.cart hy.cart _ _ hx.sd hy.sd`. Conclude with `⟨⟨om, f, Finsupp.single 0 1⟩, ⟨⟨χS, χT, hom⟩, hf, isFinComb_single_zero 1⟩, vac_ne_zero hf, rfl⟩`.
-/
theorem exists_kerDat {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {S T : HSp D}
    {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is) : ∃ k : KerDat S T, k.Is ψ θ x y ∧ k.vac ≠ 0 ∧ k.c = Finsupp.single 0 1 := by
  obtain ⟨χS, χT, om, hom⟩ := GlobalTheory.Unf.Inhab.exists_weil_pair hψ S T
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ _ _ _ _ hx.sig hy.sig hx.cart hy.cart _ _ hx.sd hy.sd
  exact ⟨⟨om, f, Finsupp.single 0 1⟩, ⟨⟨χS, χT, hom⟩, hf, isFinComb_single_zero 1⟩, vac_ne_zero hf, rfl⟩

def besOf {ρ : ℕ} (B : BesLev D ρ) : BesAt B.V B.A ρ := ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

def jacOf {ρ : ℕ} (J : JacLev D ρ) : JacAt J.W J.W₀ ρ := ⟨J.d, J.cpt, J.vN⟩

def stOf (s : GlobalTheory.ChainOnto.PiLocalization₂ D) : StAt s.V := ⟨s.par, s.M, s.Λ, s.β, s.L, s.ν, s.fd⟩

end GlobalTheory.SeeSaw.Inh

end
