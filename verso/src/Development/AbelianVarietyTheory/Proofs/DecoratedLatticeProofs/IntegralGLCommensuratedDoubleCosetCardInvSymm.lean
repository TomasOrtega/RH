import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CosetSymGL

abbrev Cos {G : Type} [Group G] (K : Subgroup G) (g : G) : Type :=
  {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)}

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨k * a, K.mul_mem hk ha, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]`.

Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩` and prove the remaining obligations. Rewrite using `[e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]`.
-/
theorem card_cos_eq_of_mem {G : Type} [Group G] {K : Subgroup G} {g h a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : h = a * g * b) : Nat.card (Cos K h) = Nat.card (Cos K g) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, K.mul_mem hk ha, ?_⟩
    rw [e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]

def quotEquiv {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr θ.toEquiv fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel K (θ a) (θ b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, hθ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotEquiv_mk {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (x : G) :
    quotEquiv K θ hθ (x : G ⧸ K) = ((θ x : G) : G ⧸ K) := rfl

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩`. Introduce and unpack `⟨k, hk, e⟩`.

Use `⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩` and prove the remaining obligations. Rewrite using `[e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]`.
-/
theorem card_cos_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (g : G) :
    Nat.card (Cos K g) = Nat.card (Cos K (θ g)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩
    rw [e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `g` and use `by obtain ⟨a, ha, b, hb, e⟩ := h g exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)`.
-/
theorem cosetSym_of_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K)
    (h : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g⁻¹ * b) : CosetSym K := fun g => by
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)

end GlobalTheory.ChainOnto.CosetSymGL

namespace GlobalTheory.ChainOnto.CosetSymGL

open GlobalTheory.LFun.ConjPlace in

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]`. Use `conv_lhs => rw [← hd]`. Rewrite using `[← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]`.
-/
theorem invT_of_symm {L : Type} [Field L] {n : ℕ} (d : GL (Fin n) L)
    (hd : (d : Matrix (Fin n) (Fin n) L)ᵀ = (d : Matrix (Fin n) (Fin n) L)) : invT (RingEquiv.refl L) n d = d⁻¹ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]
  conv_lhs => rw [← hd]
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]

open GlobalTheory.LFun.ConjPlace in
/- English proof (translation)
The claim follows from `(mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm`.
-/
theorem invT_mem_iff {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L) :
    invT (RingEquiv.refl L) n g ∈ Formalism.UG.GLint (Fin n) O ↔ g ∈ Formalism.UG.GLint (Fin n) O :=
  (mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm

open GlobalTheory.LFun.ConjPlace in

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `GlobalTheory.LFun.exists_isUnifV (E := E) w`. Establish `hϖO : ϖ ∈ Formalism.UG.Ov E w`. Express the relevant statement in the definitionally equal form `Valued.v ϖ ≤ 1`. Unfold `Formalism.UG.IsUnifV at hϖ`. Rewrite using `[hϖ]`.

Conclude with `(WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)`. Take `⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩` from `Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g`. Use `set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd`. Establish `hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex`. Rewrite using `[hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.mul_inv, mul_one]`.

Establish `hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Rewrite using `[hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]`. Establish `hgd : g = k₁ * d * k₂` using `by rw [hd]; group`. Use `set θ := invT (RingEquiv.refl (w.adicCompletion E)) n`. Use `⟨θ k₁ * k₂, (KGL w n).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂, k₁ * θ k₂, (KGL w n).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩` and prove the remaining obligations.

Establish `hθd : θ d = d⁻¹` using `invT_of_symm d hsym`. Rewrite using `[hgd, map_mul, map_mul, hθd, hd]`. Use `group`.
-/
theorem invT_mem_doset (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) : ∃ a ∈ KGL w n, ∃ b ∈ KGL w n,
      invT (RingEquiv.refl _) n g = a * g⁻¹ * b := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := E) w
  have hϖO : ϖ ∈ Formalism.UG.Ov E w := by
    change Valued.v ϖ ≤ 1
    unfold Formalism.UG.IsUnifV at hϖ
    rw [hϖ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd
  have hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one]
  have hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]
  have hgd : g = k₁ * d * k₂ := by rw [hd]; group
  set θ := invT (RingEquiv.refl (w.adicCompletion E)) n
  refine ⟨θ k₁ * k₂, (KGL w n).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂,
    k₁ * θ k₂, (KGL w n).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩
  have hθd : θ d = d⁻¹ := invT_of_symm d hsym
  rw [hgd, map_mul, map_mul, hθd, hd]
  group

end GlobalTheory.ChainOnto.CosetSymGL

open GlobalTheory.ChainOnto.CosetSymGL GlobalTheory.LFun.ConjPlace in

/- English proof (translation)
Introduce `E _ _ w n` and use `⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x) (invT_mem_doset E w n)⟩`.
-/
theorem GlobalTheory.ChainOnto.kGL_commensurated_cosetSym : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w n) ∧ CosetSym (KGL w n) := fun E _ _ w n =>
  ⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x)
    (invT_mem_doset E w n)⟩
