import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryMinorMapRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDetPowCharacterSeparatesWeightsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `h` using `Matrix.mem_unitaryGroup_iff.1 A.2`. Combine the equalities or inequalities in the displayed calculation. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, RCLike.star_def, Complex.conj_conj]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Use `_ = 1 := by rw [h, Matrix.transpose_one]`.
-/
theorem map_conj_mem_unitaryGroup {d : ℕ} (A : Matrix.unitaryGroup (Fin d) ℂ) :
    (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.1 A.2
  calc (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) * star ((A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ))
        = ((A : Matrix (Fin d) (Fin d) ℂ) * star (A : Matrix (Fin d) (Fin d) ℂ)).transpose := by
          ext i j
          simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, RCLike.star_def,
            Complex.conj_conj]
          exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = 1 := by rw [h, Matrix.transpose_one]

variable {ι : Type} [Fintype ι]

def conjFam {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) : ι → Matrix.unitaryGroup (Fin d) ℂ :=
  fun τ => ⟨(κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ), map_conj_mem_unitaryGroup (κ τ)⟩

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use extensionality with `i j`. Simplify using `[conjFam]`.
-/
theorem conjFam_map {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (fun τ => ((conjFam κ τ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) =
      fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) := by
  funext τ
  ext i j
  simp [conjFam]

/- English proof (translation)
Unfold `detChar`. Use `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_` and prove the remaining obligations. Establish `h` using `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 (κ τ).2)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
theorem detChar_unitary_ne_zero {d : ℕ} (n : ι → ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ≠ 0 := by
  unfold detChar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 (κ τ).2)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

/- English proof (translation)
Introduce `P hP`. Take `⟨hPV, hPk⟩` from `Submodule.mem_inf.1 hP`. Use `Submodule.mem_inf.2 ⟨rowSub_mem_inv _ hPV, ?_⟩` and prove the remaining obligations. Rewrite `hPk`, the goal using `[LinearMap.mem_ker]`. Use `hh (conjFam κ) P hPV` as an intermediate fact.

Rewrite `this` using `[conjFam_map]`. Rewrite using `[this, hPk, map_zero]`.
-/
theorem inv_inf_ker_stable {a d : ℕ} (n₀ : ι → ℕ) {Pr : Type} [AddCommGroup Pr] [Module ℂ Pr]
    (h : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr)
    (hh : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      h (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (h P))
    (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h := by
  intro P hP
  obtain ⟨hPV, hPk⟩ := Submodule.mem_inf.1 hP
  refine Submodule.mem_inf.2 ⟨rowSub_mem_inv _ hPV, ?_⟩
  rw [LinearMap.mem_ker] at hPk ⊢
  have := hh (conjFam κ) P hPV
  rw [conjFam_map] at this
  rw [this, hPk, map_zero]

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights a ha n n₀ hn`. Establish `h1` using `hq g P`. Rewrite `h1` using `[hP, map_smul]`. Establish `h2 : (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) - detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) • q P = 0`. Rewrite using `[sub_smul, h1, sub_self]`.

Conclude with `(smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hg)`.
-/
theorem quot_eq_zero_of_weight_ne {a d : ℕ} (ha : 0 < a) {n n₀ : ι → ℕ} (hn : n ≠ n₀) {Pr : Type} [AddCommGroup Pr]
    [Module ℂ Pr] (q : Pol ι d a →ₗ[ℂ] Pr)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    {P : Pol ι d a} (hP : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, colSub g P = detChar n g • P) : q P = 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights a ha n n₀ hn
  have h1 := hq g P
  rw [hP, map_smul] at h1
  have h2 : (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) - detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) • q P = 0 := by
    rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hg)

/- English proof (translation)
Establish `hfin : (Set.range (prodMinors (ι` using `ι) (a := a) (d := d) (n := n))).Finite := Set.finite_range _`. Use `haveI := FiniteDimensional.span_of_finite ℂ hfin`. Conclude with `Submodule.finiteDimensional_of_le (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n)`.
-/
theorem finiteDimensional_inv (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  have hfin : (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n))).Finite := Set.finite_range _
  haveI := FiniteDimensional.span_of_finite ℂ hfin
  exact Submodule.finiteDimensional_of_le (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n)

/- English proof (translation)
Use `set V := inv (ι := ι) a d n₀ with hV`. Establish `havg` using `GlobalTheory.T.exists_detCharInvariant_same_value_twisted a d n₀ Pr q hq`. Establish `hsurj : Function.Surjective (q ∘ₗ V.subtype)`. Introduce `x`. Take `⟨P, rfl⟩` from `hqs x`.

Take `⟨P₀, hP₀, he⟩` from `havg P`. Conclude with `⟨⟨P₀, hP₀⟩, he.symm⟩`. Establish `hker` using `GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker q) inf_le_left (inv_inf_ker_stable n₀ q σ hqσ)`. Establish `hinj : Function.Injective (q ∘ₗ V.subtype)`. Break down `hker with h0 | hV'` into its components or cases.

Rewrite using `[← LinearMap.ker_eq_bot]`. Rewrite `h0`, the goal using `[eq_bot_iff]`. Introduce `P hP`. Establish `h'` using `h0 (Submodule.mem_inf.2 ⟨P.2, hP⟩)`. Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))`.

It suffices to derive a contradiction. Take `⟨x, hx⟩` from `exists_ne (0 : Pr)`. Take `⟨P, hP⟩` from `hsurj x`. Establish `: (P : Pol ι d a) ∈ V ⊓ LinearMap.ker q` using `by rw [hV']; exact P.2`. Conclude with `hx (hP.symm.trans (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2))`.

Set `e : V ≃ₗ[ℂ] Pr` to `LinearEquiv.ofBijective (q ∘ₗ V.subtype) ⟨hinj, hsurj⟩`. Use `haveI : FiniteDimensional ℂ V := finiteDimensional_inv a d n₀`. Use `haveI : Nontrivial V := e.toEquiv.nontrivial`. Set `E : Module.End ℂ V` to `e.symm.toLinearMap ∘ₗ F ∘ₗ V.subtype`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue E`.

Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `hEv : E v = c • v` using `hv.apply_eq_smul`. Establish `hFv : F v = c • q v`. Establish `h1 : e (E v) = F v` using `by simp [E]`. Establish `h2 : e (c • v) = c • q v` using `by rw [map_smul]; rfl`.

Rewrite using `[← h1, hEv, h2]`. Establish `hFc : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ V, (F - c • q) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ((F - c • q) P)`. Introduce `κ P hP`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hFσ κ P hP, hqσ κ P hP]`. Establish `hker2` using `GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker (F - c • q)) inf_le_left (inv_inf_ker_stable n₀ (F - c • q) σ hFc)`.

Establish `hall : ∀ P ∈ V, F P = c • q P`. Break down `hker2 with h0 | hV'` into its components or cases. It suffices to derive a contradiction. Establish `: (v : Pol ι d a) ∈ V ⊓ LinearMap.ker (F - c • q)`. Use `Submodule.mem_inf.2 ⟨v.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]`. Conclude with `hFv`. Establish `h' : (v : Pol ι d a) ∈ (⊥ : Submodule ℂ (Pol ι d a))` using `h0 ▸ this`. Conclude with `hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))`. Introduce `P hP`.

Establish `: P ∈ V ⊓ LinearMap.ker (F - c • q)` using `by rw [hV']; exact hP`. Use `LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2` as an intermediate fact. Rewrite `this` using `[LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]`. Conclude with `this`. Use `⟨c, ?_, hall⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Take `⟨P, hP, hFP⟩` from `hF`. Conclude with `hFP (by rw [hall P hP, zero_smul])`.
-/
theorem exists_const_of_equivariant {a d : ℕ} (had : a ≤ d) (n₀ : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q F : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr) [Nontrivial Pr]
    (hqs : Function.Surjective q)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    (hqσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      q (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P))
    (hFσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P))
    (hF : ∃ P ∈ inv (ι := ι) a d n₀, F P ≠ 0) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ P ∈ inv (ι := ι) a d n₀, F P = ρ • q P := by
  set V := inv (ι := ι) a d n₀ with hV

  have havg := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a d n₀ Pr q hq
  have hsurj : Function.Surjective (q ∘ₗ V.subtype) := by
    intro x
    obtain ⟨P, rfl⟩ := hqs x
    obtain ⟨P₀, hP₀, he⟩ := havg P
    exact ⟨⟨P₀, hP₀⟩, he.symm⟩

  have hker := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker q) inf_le_left
    (inv_inf_ker_stable n₀ q σ hqσ)
  have hinj : Function.Injective (q ∘ₗ V.subtype) := by
    rcases hker with h0 | hV'
    · rw [← LinearMap.ker_eq_bot]
      rw [eq_bot_iff] at h0 ⊢
      intro P hP
      have h' := h0 (Submodule.mem_inf.2 ⟨P.2, hP⟩)
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
      obtain ⟨P, hP⟩ := hsurj x
      have : (P : Pol ι d a) ∈ V ⊓ LinearMap.ker q := by rw [hV']; exact P.2
      exact hx (hP.symm.trans (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2))
  let e : V ≃ₗ[ℂ] Pr := LinearEquiv.ofBijective (q ∘ₗ V.subtype) ⟨hinj, hsurj⟩
  haveI : FiniteDimensional ℂ V := finiteDimensional_inv a d n₀
  haveI : Nontrivial V := e.toEquiv.nontrivial
  let E : Module.End ℂ V := e.symm.toLinearMap ∘ₗ F ∘ₗ V.subtype
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue E
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hEv : E v = c • v := hv.apply_eq_smul
  have hFv : F v = c • q v := by
    have h1 : e (E v) = F v := by simp [E]
    have h2 : e (c • v) = c • q v := by rw [map_smul]; rfl
    rw [← h1, hEv, h2]

  have hFc : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ V,
      (F - c • q) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ((F - c • q) P) := by
    intro κ P hP
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hFσ κ P hP, hqσ κ P hP]
  have hker2 := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker (F - c • q)) inf_le_left
    (inv_inf_ker_stable n₀ (F - c • q) σ hFc)
  have hall : ∀ P ∈ V, F P = c • q P := by
    rcases hker2 with h0 | hV'
    · exfalso
      have : (v : Pol ι d a) ∈ V ⊓ LinearMap.ker (F - c • q) := by
        refine Submodule.mem_inf.2 ⟨v.2, ?_⟩
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
        exact hFv
      have h' : (v : Pol ι d a) ∈ (⊥ : Submodule ℂ (Pol ι d a)) := h0 ▸ this
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · intro P hP
      have : P ∈ V ⊓ LinearMap.ker (F - c • q) := by rw [hV']; exact hP
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at this
      exact this
  refine ⟨c, ?_, hall⟩
  rintro rfl
  obtain ⟨P, hP, hFP⟩ := hF
  exact hFP (by rw [hall P hP, zero_smul])

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

/- English proof (translation)
Unfold `GlobalTheory.BotFormula.minorF GlobalTheory.NormSum.minorPol prodMinors minorAt`. Rewrite using `[show (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2)) = id from`. Use function extensionality and compare the values at `fun k => rfl, MvPolynomial.rename_id]`. Both sides reduce to the same expression.
-/
theorem minorF_eq_prodMinors (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = prodMinors (ι := D.what₂.Tau) (n := n) T := by
  unfold GlobalTheory.BotFormula.minorF GlobalTheory.NormSum.minorPol prodMinors minorAt
  rw [show (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2)) = id from
    funext fun k => rfl, MvPolynomial.rename_id]
  rfl

/- English proof (translation)
Introduce `D a a' d had n₀ Pr _ _ q q' σ ha ha' hPr hqs hq's hq hq' hqσ hq'σ`. Take `⟨Pl, ε, hPlT, hPlκ⟩` from `GlobalTheory.T.exists_complementaryMinor_map_realPlaces D had n₀`. Establish `hPlV : ∀ P ∈ inv (ι` using `D.what₂.Tau) a d n₀, Pl P ∈ inv (ι := D.what₂.Tau) a' d n₀ := by`. Introduce `P hP`. Establish `hle : Submodule.span ℂ (Set.range (prodMinors (ι` using `D.what₂.Tau) (a := a) (d := d) (n := n₀))) ≤ (inv (ι := D.what₂.Tau) a' d n₀).comap Pl := by`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨T, rfl⟩`. Use `show Pl (prodMinors T) ∈ inv (ι := D.what₂.Tau) a' d n₀`. Establish `h` using `hPlT T`. Rewrite `h` using `[minorF_eq_prodMinors, minorF_eq_prodMinors]`.

Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ (prodMinors_mem_inv _)`. Conclude with `hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n₀ hP)`. Set `F : PolF D d a →ₗ[ℂ] Pr` to `q' ∘ₗ Pl`. Establish `hFσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι` using `D.what₂.Tau) a d n₀, F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P) := by`.

Introduce `κ P hP`. Simplify using `only [F, LinearMap.comp_apply]`. Rewrite using `[hPlκ κ P hP, map_smul, hq'σ κ (Pl P) (hPlV P hP), smul_smul, inv_mul_cancel₀ (detChar_unitary_ne_zero n₀ κ), one_smul]`. Establish `hF : ∃ P ∈ inv (ι` using `D.what₂.Tau) a d n₀, F P ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Take `⟨x, hx⟩` from `exists_ne (0 : Pr)`. Take `⟨P', rfl⟩` from `hq's x`. Take `⟨P₀, hP₀, he⟩` from `GlobalTheory.T.exists_detCharInvariant_same_value_twisted a' d n₀ Pr q' hq' P'`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[he]`. Establish `hle : Submodule.span ℂ (Set.range (prodMinors (ι` using `D.what₂.Tau) (a := a') (d := d) (n := n₀))) ≤ LinearMap.ker q' := by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨T', rfl⟩`. Take `⟨T, rfl⟩` from `(GlobalTheory.BotMatch.complTup_bijective D had).2 T'`.

Establish `h0` using `hcon (prodMinors T) (prodMinors_mem_inv T)`. Establish `h` using `hPlT T`. Rewrite `h` using `[minorF_eq_prodMinors, minorF_eq_prodMinors]`. Simplify using `only [F, LinearMap.comp_apply, h, map_smul] at h0`. Use `show q' (prodMinors (GlobalTheory.BotMatch.complTup D had T)) = 0`.

Establish `hε : ((ε T : ℤ) : ℂ) ≠ 0`. Apply the tactic sequence `rcases Int.units_eq_one_or (ε T) with h1 | h1 <;> simp [h1]`. Conclude with `(smul_eq_zero.1 h0).resolve_left hε`. Conclude with `hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a' d n₀ hP₀)`. Take `⟨ρ, hρ, hFq⟩` from `exists_const_of_equivariant (by omega) n₀ Pr q F σ hqs hq hqσ hFσ hF`.

Use `⟨ρ⁻¹, inv_ne_zero hρ, fun n T => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : n = n₀`. Substitute `hn` using the available equality. Use `⟨ε T, ?_⟩` and prove the remaining obligations. Establish `h` using `hFq (prodMinors T) (prodMinors_mem_inv T)`.

Establish `hT` using `hPlT T`. Rewrite `hT`, the goal using `[minorF_eq_prodMinors, minorF_eq_prodMinors]`. Simplify using `only [F, LinearMap.comp_apply, hT, map_smul] at h`. Rewrite using `[mul_smul, h, smul_smul, inv_mul_cancel₀ hρ, one_smul]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Rewrite using `[minorF_eq_prodMinors, minorF_eq_prodMinors]`. Rewrite using `[quot_eq_zero_of_weight_ne ha hn q hq (fun g => colSub_prodMinors g T), quot_eq_zero_of_weight_ne ha' hn q' hq' (fun g => colSub_prodMinors g _), smul_zero]`.
-/
theorem quot_minor_eq_const_smul_compl : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro D a a' d had n₀ Pr _ _ q q' σ ha ha' hPr hqs hq's hq hq' hqσ hq'σ
  obtain ⟨Pl, ε, hPlT, hPlκ⟩ := GlobalTheory.T.exists_complementaryMinor_map_realPlaces D had n₀

  have hPlV : ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀, Pl P ∈ inv (ι := D.what₂.Tau) a' d n₀ := by
    intro P hP
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a) (d := d) (n := n₀))) ≤
        (inv (ι := D.what₂.Tau) a' d n₀).comap Pl := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      show Pl (prodMinors T) ∈ inv (ι := D.what₂.Tau) a' d n₀
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      rw [h]
      exact Submodule.smul_mem _ _ (prodMinors_mem_inv _)
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n₀ hP)
  let F : PolF D d a →ₗ[ℂ] Pr := q' ∘ₗ Pl
  have hFσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P) := by
    intro κ P hP
    simp only [F, LinearMap.comp_apply]
    rw [hPlκ κ P hP, map_smul, hq'σ κ (Pl P) (hPlV P hP), smul_smul,
      inv_mul_cancel₀ (detChar_unitary_ne_zero n₀ κ), one_smul]

  have hF : ∃ P ∈ inv (ι := D.what₂.Tau) a d n₀, F P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P', rfl⟩ := hq's x
    obtain ⟨P₀, hP₀, he⟩ := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a' d n₀ Pr q' hq' P'
    apply hx
    rw [he]
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a') (d := d) (n := n₀))) ≤
        LinearMap.ker q' := by
      rw [Submodule.span_le]
      rintro _ ⟨T', rfl⟩
      obtain ⟨T, rfl⟩ := (GlobalTheory.BotMatch.complTup_bijective D had).2 T'
      have h0 := hcon (prodMinors T) (prodMinors_mem_inv T)
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      simp only [F, LinearMap.comp_apply, h, map_smul] at h0
      show q' (prodMinors (GlobalTheory.BotMatch.complTup D had T)) = 0
      have hε : ((ε T : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (ε T) with h1 | h1 <;> simp [h1]
      exact (smul_eq_zero.1 h0).resolve_left hε
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a' d n₀ hP₀)
  obtain ⟨ρ, hρ, hFq⟩ := exists_const_of_equivariant (by omega) n₀ Pr q F σ hqs hq hqσ hFσ hF
  refine ⟨ρ⁻¹, inv_ne_zero hρ, fun n T => ?_⟩
  by_cases hn : n = n₀
  · subst hn
    refine ⟨ε T, ?_⟩
    have h := hFq (prodMinors T) (prodMinors_mem_inv T)
    have hT := hPlT T
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at hT ⊢
    simp only [F, LinearMap.comp_apply, hT, map_smul] at h
    rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  · refine ⟨1, ?_⟩
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors]
    rw [quot_eq_zero_of_weight_ne ha hn q hq (fun g => colSub_prodMinors g T),
      quot_eq_zero_of_weight_ne ha' hn q' hq' (fun g => colSub_prodMinors g _), smul_zero]

end GlobalTheory.SchurQuot
