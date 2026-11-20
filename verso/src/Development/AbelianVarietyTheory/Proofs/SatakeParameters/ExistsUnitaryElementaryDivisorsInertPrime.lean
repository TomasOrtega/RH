import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertExist

section Local

open GlobalTheory.SelfDualGenus GlobalTheory.PlaceComp GlobalTheory.HeckeLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

/- English proof (translation)
Use `show x ∈ Formalism.L2.Col.stdLat E n ↔ _`. Simplify using `only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Use `forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩` and prove the remaining obligations.
-/
theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (x i) := by
  show x ∈ Formalism.L2.Col.stdLat E n ↔ _
  simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

/- English proof (translation)
Simplify using `only [Formalism.UG.antiJ, add_comm b.val a.val]`. Apply the tactic sequence `split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]`.
-/
theorem antiJ_herm (n : ℕ) (a b : Fin n) :
    ReciprocityTheory.ChartRestriction.G.FD.cc (Formalism.UG.antiJ E n a b) = Formalism.UG.antiJ E n b a := by
  simp only [Formalism.UG.antiJ, add_comm b.val a.val]
  split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`.
-/
theorem antiJ_det_ne_zero (n : ℕ) : (Formalism.UG.antiJ E n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite using `[mem_stdLat_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Rewrite `hy` using `[mem_stdLat_iff]`. Use `IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_` and prove the remaining obligations.

Use `((hx a).mul ?_).mul ?_` and prove the remaining obligations. Unfold `Formalism.UG.antiJ`. Use `split_ifs`. Conclude with `isIntegral_one`. Conclude with `isIntegral_zero`.

Conclude with `(hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom`. Introduce `h i`. Establish `hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E))`. Rewrite using `[mem_stdLat_iff]`. Introduce `j`.

Distinguish the cases in `hj : j = i.rev`. Substitute `hj` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[hj]`. Use `h _ hy` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos (by have := i.2; omega)]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `hc`. Apply `hb` to reduce the goal to its premises. Use `ext`. Use `i.2` as an intermediate fact.

Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem selfDual_antiJ (n : ℕ) (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔
      ∀ y ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)),
        IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm (Formalism.UG.antiJ E n) x y) := by
  rw [mem_stdLat_iff]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff] at hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
    refine ((hx a).mul ?_).mul ?_
    · unfold Formalism.UG.antiJ; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
  · intro h i
    have hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) := by
      rw [mem_stdLat_iff]
      intro j
      by_cases hj : j = i.rev
      · subst hj; simpa using isIntegral_one
      · simpa [hj] using isIntegral_zero
    have := h _ hy
    convert this using 1
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by have := i.2; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hc; apply hb; ext; have := i.2; have := b.2; omega
    · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i` from `⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩`. Use `show locEmb v (y i) ∈ locOrder v`.

Rewrite using `[← hz]`. Conclude with `locEmb_mem_locOrder v z`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx => exact Subalgebra.smul_mem _ hx c`.
-/
theorem locLattice_le {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {x : Fin n → LocAlg v} (hx : x ∈ locLattice v (Formalism.L2.Col.stdLat E n)) (i : Fin n) : x i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i := ⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩
    show locEmb v (y i) ∈ locOrder v
    rw [← hz]
    exact locEmb_mem_locOrder v z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Subalgebra.smul_mem _ hx c

/- English proof (translation)
Use `show ∑ j, M i j * z j ∈ O`. Conclude with `O.sum_mem fun j _ => mul_mem (hM i j) (hz j)`.
-/
theorem mulVec_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, M i j ∈ O) {z : Fin n → R} (hz : ∀ i, z i ∈ O) (i : Fin n) : (M *ᵥ z) i ∈ O := by
  show ∑ j, M i j * z j ∈ O
  exact O.sum_mem fun j _ => mul_mem (hM i j) (hz j)

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem single_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} (j i : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
Take `⟨h, h1, h2⟩` from `exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n) ⟨Formalism.L2.Col.stdLat_lattice.fg, Formalism.L2.Col.stdLat_lattice.span_eq_top⟩ (selfDual_antiJ n) v`. Establish `hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n)`. Introduce `j`. Use `Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]`.

Introduce `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[hi]`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hi]`.

Use `⟨h, ?_, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg Matrix.transpose h1`. Rewrite `h3` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.transpose_one]`. Establish `hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v)`. Use extensionality with `a b`.

Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]`. Rewrite `h3` using `[hT]`. Conclude with `h3`. Rewrite using `[mem_ordAt_iff]`. Establish `hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n)`.

Rewrite using `[h2]`. Introduce `k`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `single_int (O := (locOrder v).toSubring) j k`. Use `locLattice_le v hm i` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_single_one]`. Conclude with `this`. Rewrite using `[mem_ordAt_iff]`. Use `(h2 _).1 (hs j) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`.

Conclude with `this`.
-/
theorem exists_antiFrame [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) :
    ∃ h : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 *
        (Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)) * h.1 = 1 ∧
      (∀ i j, h.1 i j ∈ ordAt E v) ∧ ∀ i j, (h⁻¹).1 i j ∈ ordAt E v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n)
    ⟨Formalism.L2.Col.stdLat_lattice.fg, Formalism.L2.Col.stdLat_lattice.span_eq_top⟩ (selfDual_antiJ n) v
  have hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]
      intro i
      by_cases hi : i = j
      · subst hi; simpa using isIntegral_one
      · simpa [hi] using isIntegral_zero
    · funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  refine ⟨h, ?_, fun i j => ?_, fun i j => ?_⟩
  · have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.transpose_one] at h3
    have hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v) := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]
    rw [hT] at h3
    exact h3
  · rw [mem_ordAt_iff]
    have hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
      rw [h2]
      intro k
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact single_int (O := (locOrder v).toSubring) j k
    have := locLattice_le v hm i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · rw [mem_ordAt_iff]
    have := (h2 _).1 (hs j) i
    rw [Matrix.mulVec_single_one] at this
    exact this

/- English proof (translation)
Take `⟨h, hh, hi, hi'⟩` from `exists_antiFrame hc v n`. Establish `hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) = inclR (Fv (maximalRealSubfield E) v) (hc.sig x)` using `fun x => by show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) = (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Set `t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E` to `fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)`.

Set `t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E` to `fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))`. Establish `tt : ∀ i, t i * t' i = 1` using `fun i => by`. Simplify using `only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]`. Set `T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)` to `⟨Matrix.diagonal t, Matrix.diagonal t', by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i, by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩`. Establish `hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)))` using `by show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _`.

Rewrite using `[Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`. Distinguish the cases in `hij : i.val + j.val + 1 = n`. Establish `hj : j = i.rev` using `Fin.ext (by rw [Fin.val_rev]; omega)`.

Substitute `hj` using the available equality. Simplify using `only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]`. Use `show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) * inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1`. Rewrite using `[hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]`. Simplify using `only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]`.

Establish `hu` using `conj_mem_UJ _ hh hT`. Establish `hTv : ∀ w, T.1 *ᵥ w = t * w` using `fun w => funext fun k => by show (Matrix.diagonal t *ᵥ w) k = t k * w k`. Rewrite using `[Matrix.mulVec_diagonal]`. Use `⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[one_smul]`.

Conclude with `mulVec_int hi' hz i`. Rewrite using `[one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]`. Establish `hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.

Rewrite using `[one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]`.
-/
theorem exists_std [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) {ϖ : E} (h0 : ϖ ≠ 0) (hσ : hc.sig ϖ = ϖ) (d : ℕ → ℤ) (hd : ∀ i : Fin n, d i.rev.1 = -d i.1) :
    ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
      StdDiv (ordAt E v) 1 (fun i : Fin n => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) u.1 := by
  obtain ⟨h, hh, hi, hi'⟩ := exists_antiFrame hc v n
  have hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) =
      inclR (Fv (maximalRealSubfield E) v) (hc.sig x) := fun x => by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)
  let t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))
  have tt : ∀ i, t i * t' i = 1 := fun i => by
    simp only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
  let T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    ⟨Matrix.diagonal t, Matrix.diagonal t',
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩
  have hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig)
      ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v))) := by
    show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _
    rw [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = i.rev := Fin.ext (by rw [Fin.val_rev]; omega)
      subst hj
      simp only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]
      show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) *
        inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1
      rw [hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
    · simp only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]
  have hu := conj_mem_UJ _ hh hT
  have hTv : ∀ w, T.1 *ᵥ w = t * w := fun w => funext fun k => by
    show (Matrix.diagonal t *ᵥ w) k = t k * w k
    rw [Matrix.mulVec_diagonal]
  refine ⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩,
    fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩
  · rw [one_smul]; exact mulVec_int hi' hz i
  · rw [one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]
  · have hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]

end Local

section Host

open GlobalTheory.PlaceComp

/- English proof (translation)
Introduce `D V P e x ϖ d hP hx h1 h2 hlen hdual`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Use `haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm`. Choose the witnesses or unpack the hypotheses as in `⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by`. Break down `id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩` into its components or cases.

Rewrite `a3` using `[← he]`. Conclude with `⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩`. Conclude with `⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩`. Establish `h0 : (ϖ : D.host.E) ≠ 0` using `fun h => h2 (by`. Rewrite using `[show ϖ = 0 from Subtype.ext h]`.

Conclude with `zero_mem _)`. Establish `hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ`. Rewrite using `[hx]`. Conclude with `D.sp.cm.sig.commutes _`. Establish `hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0` using `fun i => by`.

Use `GlobalTheory.DualDivU.getD_dualLab d hlen i` as an intermediate fact. Rewrite `this` using `[hdual]`. Rewrite using `[this, neg_neg]`. Take `⟨u, hu, hs⟩` from `GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd`. Take `⟨g, hg, hg'⟩` from `(GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E) (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩`.

Conclude with `⟨g, hg, hlen, hg'⟩`.
-/
theorem exists_suppF_divAt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e x ϖ d hP hx h1 h2 hlen hdual
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by
    rcases id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩
    · rw [← he] at a3
      exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
    · exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _)
  have hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ := by
    rw [hx]
    exact D.sp.cm.sig.commutes _
  have hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0 := fun i => by
    have := GlobalTheory.DualDivU.getD_dualLab d hlen i
    rw [hdual] at this
    rw [this, neg_neg]
  obtain ⟨u, hu, hs⟩ := GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd
  obtain ⟨g, hg, hg'⟩ := (GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E)
    (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩
  exact ⟨g, hg, hlen, hg'⟩

end Host

end GlobalTheory.InertExist
