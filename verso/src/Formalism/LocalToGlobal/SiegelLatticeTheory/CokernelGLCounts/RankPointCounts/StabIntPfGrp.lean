import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Lemmata.GeneralBFactRightBisAlt.Imports

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabIntGrp

section Tri

variable {K : Type*} [CommRing K] {n : ℕ}

def LoIn (S : Subring K) (l : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ S

/- English proof (translation)
Introduce `i j hij`. Conclude with `h.2.1 i j hij`.
-/
theorem loIn_lower {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (h : LoIn S l) : l.IsLowerTriangular := by
  intro i j hij
  exact h.2.1 i j hij

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_bis_other.goal1 .. | (apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply @B …`.
-/
theorem mul_diag_of_lower {l l' : Matrix (Fin n) (Fin n) K} (hl : ∀ a b, a < b → l a b = 0)
    (hl' : ∀ a b, a < b → l' a b = 0) (a : Fin n) : (l * l') a a = l a a * l' a a := by
  first | exact Bl.general_b_fact_right_bis_other.goal1 .. | (apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' a | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› | exact @Bl.general_b_fact_right_bis_other.goal1 K

/- English proof (translation)
Use `⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Conclude with `S.one_mem`.

Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `S.zero_mem`.
-/
theorem loIn_one (S : Subring K) : LoIn S (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => ?_⟩
  by_cases h : a = b
  · subst h; rw [Matrix.one_apply_eq]; exact S.one_mem
  · rw [Matrix.one_apply_ne h]; exact S.zero_mem

/- English proof (translation)
Use `⟨fun a => by rw [mul_diag_of_lower hl.2.1 hl'.2.1, hl.1, hl'.1, one_mul], fun a b hab => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Break down `lt_or_ge a c with h | h` into its components or cases. Rewrite using `[hl.2.1 a c h, zero_mul]`.

Rewrite using `[hl'.2.1 c b (lt_of_le_of_lt h hab), mul_zero]`. Rewrite using `[Matrix.mul_apply]`. Conclude with `S.sum_mem fun c _ => S.mul_mem (hl.2.2 a c) (hl'.2.2 c b)`.
-/
theorem loIn_mul {S : Subring K} {l l' : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) (hl' : LoIn S l') :
    LoIn S (l * l') := by
  refine ⟨fun a => by rw [mul_diag_of_lower hl.2.1 hl'.2.1, hl.1, hl'.1, one_mul], fun a b hab => ?_,
    fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with h | h
    · rw [hl.2.1 a c h, zero_mul]
    · rw [hl'.2.1 c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact S.sum_mem fun c _ => S.mul_mem (hl.2.2 a c) (hl'.2.2 c b)

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular l (loIn_lower hl)]`. Conclude with `Finset.prod_eq_one fun a _ => hl.1 a`.
-/
theorem det_loIn {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : l.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular l (loIn_lower hl)]
  exact Finset.prod_eq_one fun a _ => hl.1 a

/- English proof (translation)
Establish `hd : IsUnit l.det` using `by rw [det_loIn hl]; exact isUnit_one`. Establish `hinv : l⁻¹ = l.adjugate` using `by rw [Matrix.inv_def, det_loIn hl, Ring.inverse_one, one_smul]`. Use `letI : Invertible l := Matrix.invertibleOfIsUnitDet l hd`. Establish `hlow : l⁻¹.IsLowerTriangular` using `Matrix.blockTriangular_inv_of_blockTriangular (loIn_lower hl)`. Establish `hlow' : ∀ a b, a < b → l⁻¹ a b = 0` using `fun a b h => hlow h`.

Use `⟨fun a => ?_, hlow', fun a b => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun (Matrix.nonsing_inv_mul l hd) a) a`. Rewrite `h1` using `[mul_diag_of_lower hlow' hl.2.1, hl.1, mul_one, Matrix.one_apply_eq]`. Conclude with `h1`. Set `lS : Matrix (Fin n) (Fin n) S` to `fun i j => ⟨l i j, hl.2.2 i j⟩`.

Establish `hmap : l = S.subtype.mapMatrix lS` using `by ext i j; rfl`. Rewrite using `[hinv, hmap, ← RingHom.map_adjugate]`. Conclude with `(lS.adjugate a b).2`.
-/
theorem loIn_inv {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : LoIn S l⁻¹ := by
  have hd : IsUnit l.det := by rw [det_loIn hl]; exact isUnit_one
  have hinv : l⁻¹ = l.adjugate := by rw [Matrix.inv_def, det_loIn hl, Ring.inverse_one, one_smul]
  letI : Invertible l := Matrix.invertibleOfIsUnitDet l hd
  have hlow : l⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular (loIn_lower hl)
  have hlow' : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b h => hlow h
  refine ⟨fun a => ?_, hlow', fun a b => ?_⟩
  · have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul l hd) a) a
    rw [mul_diag_of_lower hlow' hl.2.1, hl.1, mul_one, Matrix.one_apply_eq] at h1
    exact h1
  · let lS : Matrix (Fin n) (Fin n) S := fun i j => ⟨l i j, hl.2.2 i j⟩
    have hmap : l = S.subtype.mapMatrix lS := by ext i j; rfl
    rw [hinv, hmap, ← RingHom.map_adjugate]
    exact (lS.adjugate a b).2

/- English proof (translation)
Unfold `LoIn`. Simplify using `only [Matrix.transpose_apply]`. Conclude with `⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩⟩`.
-/
theorem upIn_iff (S : Subring K) (ρ : Matrix (Fin n) (Fin n) K) :
    ((∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ S) ↔ LoIn S ρ.transpose := by
  unfold LoIn
  simp only [Matrix.transpose_apply]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩⟩

end Tri

section Loc

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

/- English proof (translation)
The claim follows from `upIn_iff Mp.R ρ`.
-/
theorem intUp_iff (ρ : Matrix (Fin n) (Fin n) E) : Formalism.MainNotions.S.TieN.IntUp Mp ρ ↔ LoIn Mp.R ρ.transpose :=
  upIn_iff Mp.R ρ

/- English proof (translation)
The claim follows from `loIn_one _`.
-/
theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) := loIn_one _

/- English proof (translation)
Rewrite using `[intUp_iff, Matrix.transpose_one]`. Conclude with `loIn_one _`.
-/
theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) := by
  rw [intUp_iff, Matrix.transpose_one]; exact loIn_one _

/- English proof (translation)
The claim follows from `loIn_mul h h'`.
-/
theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := loIn_mul h h'

/- English proof (translation)
Rewrite `*` using `[intUp_iff]`. Rewrite using `[Matrix.transpose_mul]`. Conclude with `loIn_mul h' h`.
-/
theorem intUp_mul {ρ ρ' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp ρ') : Formalism.MainNotions.S.TieN.IntUp Mp (ρ * ρ') := by
  rw [intUp_iff] at *; rw [Matrix.transpose_mul]; exact loIn_mul h' h

/- English proof (translation)
The claim follows from `loIn_inv h`.
-/
theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ := loIn_inv h

/- English proof (translation)
Rewrite `*` using `[intUp_iff]`. Rewrite using `[Matrix.transpose_nonsing_inv]`. Conclude with `loIn_inv h`.
-/
theorem intUp_inv {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) :
    Formalism.MainNotions.S.TieN.IntUp Mp ρ⁻¹ := by
  rw [intUp_iff] at *; rw [Matrix.transpose_nonsing_inv]; exact loIn_inv h

/- English proof (translation)
Rewrite using `[det_loIn h]`. Conclude with `isUnit_one`.
-/
theorem intLow_det {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) : IsUnit l.det := by
  rw [det_loIn h]; exact isUnit_one

/- English proof (translation)
Rewrite `h` using `[intUp_iff]`. Rewrite using `[← Matrix.det_transpose, det_loIn h]`. Conclude with `isUnit_one`.
-/
theorem intUp_det {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) : IsUnit ρ.det := by
  rw [intUp_iff] at h; rw [← Matrix.det_transpose, det_loIn h]; exact isUnit_one

end Loc

section Field

variable {E : Type*} [Field E] {n : ℕ}

/- English proof (translation)
Unfold `IsLoUni LoIn`. Conclude with `⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩, fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩`.
-/
theorem isLoUni_iff (a : Matrix (Fin n) (Fin n) E) : IsLoUni a ↔ LoIn (⊤ : Subring E) a := by
  unfold IsLoUni LoIn
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

/- English proof (translation)
Rewrite using `[← upIn_iff]`. Unfold `IsUpUni`. Conclude with `⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩, fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩`.
-/
theorem isUpUni_iff (b : Matrix (Fin n) (Fin n) E) : IsUpUni b ↔ LoIn (⊤ : Subring E) b.transpose := by
  rw [← upIn_iff]
  unfold IsUpUni
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

end Field

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [ZhatOM]`. Rewrite using `[← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`.
-/
theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  funext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word) (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
  (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Use `⟨(isLoUni_iff _).2 (by simpa using loIn_one _), 1, (isUpUni_iff _).2 (by simpa using loIn_one _), by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z => ?_⟩⟩` and prove the remaining obligations. Simplify using `[zhatOM_zhatOM]`.
-/
theorem one_mem_set : (1 : GLR D) ∈ stabIntSet D u u' δ M w := by
  refine ⟨(isLoUni_iff _).2 (by simpa using loIn_one _), 1, (isUpUni_iff _).2 (by simpa using loIn_one _),
    by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z => ?_⟩⟩
  simp [zhatOM_zhatOM]

/- English proof (translation)
Take `⟨hla, b, hb, hab, hp⟩` from `ha`. Take `⟨hla', b', hb', hab', hp'⟩` from `ha'`. Use `⟨?_, b' * b, ?_, ?_, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, isLoUni_iff]`. Conclude with `loIn_mul ((isLoUni_iff _).1 hla) ((isLoUni_iff _).1 hla')`.

Rewrite using `[isUpUni_iff, Matrix.transpose_mul]`. Conclude with `loIn_mul ((isUpUni_iff _).1 hb) ((isUpUni_iff _).1 hb')`. Rewrite using `[Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = ptMat w := by rw [hab', hab]`. Take `⟨l, ρ, hl, hρ, hm⟩` from `hp p`. Take `⟨l', ρ', hl', hρ', hm'⟩` from `hp' p`. Use `⟨l * l', ρ' * ρ, intLow_mul _ hl hl', intUp_mul _ hρ' hρ, fun Z => ?_⟩` and prove the remaining obligations. Establish `e : ((a * a' : GLR D) : MatR D) * ZhatOM Z * (b' * b) = (a : MatR D) * ZhatOM (ZhatOM ((a' : MatR D) * ZhatOM Z * b')) * b`.

Rewrite using `[zhatOM_zhatOM, Units.val_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hm, hm']`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem mul_mem_set {a a' : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) (ha' : a' ∈ stabIntSet D u u' δ M w) :
    a * a' ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  obtain ⟨hla', b', hb', hab', hp'⟩ := ha'
  refine ⟨?_, b' * b, ?_, ?_, fun p => ?_⟩
  · rw [Units.val_mul, isLoUni_iff]; exact loIn_mul ((isLoUni_iff _).1 hla) ((isLoUni_iff _).1 hla')
  · rw [isUpUni_iff, Matrix.transpose_mul]; exact loIn_mul ((isUpUni_iff _).1 hb) ((isUpUni_iff _).1 hb')
  · rw [Units.val_mul]
    calc (a : MatR D) * a' * ptMat w * (b' * b) = (a : MatR D) * ((a' : MatR D) * ptMat w * b') * b := by
          simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hab', hab]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    obtain ⟨l', ρ', hl', hρ', hm'⟩ := hp' p
    refine ⟨l * l', ρ' * ρ, intLow_mul _ hl hl', intUp_mul _ hρ' hρ, fun Z => ?_⟩
    have e : ((a * a' : GLR D) : MatR D) * ZhatOM Z * (b' * b) =
        (a : MatR D) * ZhatOM (ZhatOM ((a' : MatR D) * ZhatOM Z * b')) * b := by
      rw [zhatOM_zhatOM, Units.val_mul]; simp only [Matrix.mul_assoc]
    rw [e, hm, hm']
    simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hla, b, hb, hab, hp⟩` from `ha`. Establish `hbT` using `(isUpUni_iff _).1 hb`. Establish `hbd : IsUnit b.det` using `by rw [← Matrix.det_transpose, det_loIn hbT]; exact isUnit_one`. Establish `hai : ((a⁻¹ : GLR D) : MatR D) = (a : MatR D)⁻¹` using `Matrix.coe_units_inv a`. Establish `had : IsUnit (a : MatR D).det` using `by rw [det_loIn ((isLoUni_iff _).1 hla)]; exact isUnit_one`.

Use `⟨?_, b⁻¹, ?_, ?_, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[hai, isLoUni_iff]`. Conclude with `loIn_inv ((isLoUni_iff _).1 hla)`. Rewrite using `[isUpUni_iff, Matrix.transpose_nonsing_inv]`. Conclude with `loIn_inv hbT`.

Rewrite using `[hai]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ = ((a : MatR D)⁻¹ * (a : MatR D)) * ptMat w * (b * b⁻¹) by simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ had, Matrix.mul_nonsing_inv _ hbd, Matrix.one_mul, Matrix.mul_one]`. Take `⟨l, ρ, hl, hρ, hm⟩` from `hp p`. Use `⟨l⁻¹, ρ⁻¹, intLow_inv _ hl, intUp_inv _ hρ, fun Z => ?_⟩` and prove the remaining obligations.

Use `set Z' := ZhatOM (((a⁻¹ : GLR D) : MatR D) * ZhatOM Z * b⁻¹) with hZ'`. Establish `e : (a : MatR D) * ZhatOM Z' * b = ZhatOM Z`. Rewrite using `[hZ', zhatOM_zhatOM, hai, show (a : MatR D) * ((a : MatR D)⁻¹ * ZhatOM Z * b⁻¹) * b = ((a : MatR D) * (a : MatR D)⁻¹) * ZhatOM Z * (b⁻¹ * b) by simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ had, Matrix.nonsing_inv_mul _ hbd, Matrix.one_mul, Matrix.mul_one]`. Establish `h1` using `hm Z'`. Rewrite `h1` using `[e, zhatOM_zhatOM]`.

Rewrite using `[h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (intLow_det _ hl), Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ (intUp_det _ hρ)]`.
-/
theorem inv_mem_set {a : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) : a⁻¹ ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  have hbT := (isUpUni_iff _).1 hb
  have hbd : IsUnit b.det := by rw [← Matrix.det_transpose, det_loIn hbT]; exact isUnit_one
  have hai : ((a⁻¹ : GLR D) : MatR D) = (a : MatR D)⁻¹ := Matrix.coe_units_inv a
  have had : IsUnit (a : MatR D).det := by rw [det_loIn ((isLoUni_iff _).1 hla)]; exact isUnit_one
  refine ⟨?_, b⁻¹, ?_, ?_, fun p => ?_⟩
  · rw [hai, isLoUni_iff]; exact loIn_inv ((isLoUni_iff _).1 hla)
  · rw [isUpUni_iff, Matrix.transpose_nonsing_inv]; exact loIn_inv hbT
  · rw [hai]
    calc (a : MatR D)⁻¹ * ptMat w * b⁻¹ = (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ := by rw [hab]
      _ = ptMat w := by
        rw [show (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ =
            ((a : MatR D)⁻¹ * (a : MatR D)) * ptMat w * (b * b⁻¹) by simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ had, Matrix.mul_nonsing_inv _ hbd, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    refine ⟨l⁻¹, ρ⁻¹, intLow_inv _ hl, intUp_inv _ hρ, fun Z => ?_⟩
    set Z' := ZhatOM (((a⁻¹ : GLR D) : MatR D) * ZhatOM Z * b⁻¹) with hZ'
    have e : (a : MatR D) * ZhatOM Z' * b = ZhatOM Z := by
      rw [hZ', zhatOM_zhatOM, hai, show (a : MatR D) * ((a : MatR D)⁻¹ * ZhatOM Z * b⁻¹) * b =
          ((a : MatR D) * (a : MatR D)⁻¹) * ZhatOM Z * (b⁻¹ * b) by simp only [Matrix.mul_assoc],
        Matrix.mul_nonsing_inv _ had, Matrix.nonsing_inv_mul _ hbd, Matrix.one_mul, Matrix.mul_one]
    have h1 := hm Z'
    rw [e, zhatOM_zhatOM] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (intLow_det _ hl), Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (intUp_det _ hρ)]

def stabIntGrp : Subgroup (GLR D) where
  carrier := stabIntSet D u u' δ M w
  one_mem' := one_mem_set D u u' δ M w
  mul_mem' := mul_mem_set D u u' δ M w
  inv_mem' := inv_mem_set D u u' δ M w

/- English proof (translation)
Unfold `stabInt`. Conclude with `Subgroup.closure_eq (stabIntGrp D u u' δ M w)`.
-/
theorem stabInt_eq : stabInt D u u' δ M w = stabIntGrp D u u' δ M w := by
  unfold stabInt
  exact Subgroup.closure_eq (stabIntGrp D u u' δ M w)

/- English proof (translation)
Rewrite using `[stabInt_eq]`. Both sides reduce to the same expression.
-/
theorem mem_stabInt_iff (a : GLR D) : a ∈ stabInt D u u' δ M w ↔ a ∈ stabIntSet D u u' δ M w := by
  rw [stabInt_eq]; rfl

end Formalism.L2.SG.Pf.StabIntGrp
