import Formalism.LocalToGlobal.UnitaryNorms.PowValCast
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq

noncomputable section

open IntermediateField NumberField

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.L2.Host

variable {φ : Frame} (H : HostRaw φ)

def EQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, j.fieldRange

def FI : IntermediateField ℚ H.E := H.F.toIntermediateField fun x => by
  simpa using SubfieldClass.ratCast_mem H.F x

def FQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, H.FI.map j

/- English proof (translation)
The claim follows from `(le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) ⟨x, rfl⟩`.
-/
theorem mem_EQ (j : H.E →ₐ[ℚ] Qb) (x : H.E) : j x ∈ H.EQ :=
  (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) ⟨x, rfl⟩

def ActsAs (s : H.EQ →ₐ[ℚ] Qb) (g : φ.GG) : Prop :=
  ∀ (j : H.E →ₐ[ℚ] Qb) (x : H.E), s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)

def CondEQ : Prop := IsCond H.EQ H.condN

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosed.lift⟩`.
-/
theorem nonempty_emb : Nonempty (H.E →ₐ[ℚ] Qb) := ⟨IsAlgClosed.lift⟩

/- English proof (translation)
Use `H.galois` as an intermediate fact. Establish `inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E))`. Introduce `σ τ hst`. Conclude with `AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)`. Establish `hb` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by`.

Rewrite using `[AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩`. Take `⟨σ, hσ⟩` from `hb.2 j'`. Conclude with `⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩`.
-/
theorem exists_aut (j j' : H.E →ₐ[ℚ] Qb) : ∃ σ : H.E ≃ₐ[ℚ] H.E, ∀ x, j' x = j (σ x) := by
  have := H.galois
  have inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E)) := by
    intro σ τ hst
    exact AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)
  have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by
    rw [AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩
  obtain ⟨σ, hσ⟩ := hb.2 j'
  exact ⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩

/- English proof (translation)
Use `le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `H.exists_aut j j'`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨σ x, (hσ x).symm⟩`.
-/
theorem range_eq (j : H.E →ₐ[ℚ] Qb) : j.fieldRange = H.EQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, (hσ x).symm⟩

/- English proof (translation)
Introduce `ψ` and use `hx (ψ.comp (σ : H.E →+* H.E))`.
-/
theorem aut_mem_F (σ : H.E ≃ₐ[ℚ] H.E) {x : H.E} (hx : x ∈ H.F) : σ x ∈ H.F := fun ψ =>
  hx (ψ.comp (σ : H.E →+* H.E))

/- English proof (translation)
Use `le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => H.FI.map j) j) (iSup_le fun j' => ?_)` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `H.exists_aut j j'`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨σ x, H.aut_mem_F σ hx, (hσ x).symm⟩`.
-/
theorem map_FI (j : H.E →ₐ[ℚ] Qb) : H.FI.map j = H.FQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => H.FI.map j) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨σ x, H.aut_mem_F σ hx, (hσ x).symm⟩

/- English proof (translation)
Rewrite using `[← H.map_FI j, IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, rfl⟩`. Introduce and unpack `⟨y, hy, hxy⟩`.

Rewrite using `[← j.toRingHom.injective hxy]` and apply the resulting hypothesis.
-/
theorem mem_F_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.F ↔ j x ∈ H.FQ := by
  rw [← H.map_FI j, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [← j.toRingHom.injective hxy]

/- English proof (translation)
Establish `hb : j H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb)` using `by rw [← map_pow, H.sqd_sq]; simp`. Rewrite using `[K, adjoin_map, Set.image_singleton, KQ, sqQ_eq hb]`.
-/
theorem map_K (j : H.E →ₐ[ℚ] Qb) : H.K.map j = KQ H.d := by
  have hb : j H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) := by rw [← map_pow, H.sqd_sq]; simp
  rw [K, adjoin_map, Set.image_singleton, KQ, sqQ_eq hb]

/- English proof (translation)
Rewrite using `[← H.map_K j, IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, rfl⟩`. Introduce and unpack `⟨y, hy, hxy⟩`.

Rewrite using `[← j.toRingHom.injective hxy]` and apply the resulting hypothesis.
-/
theorem mem_K_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.K ↔ j x ∈ KQ H.d := by
  rw [← H.map_K j, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [← j.toRingHom.injective hxy]

/- English proof (translation)
The claim follows from `iSup_le fun j => by rintro _ ⟨x, -, rfl⟩ exact H.mem_EQ j x`.
-/
theorem FQ_le_EQ : H.FQ ≤ H.EQ := iSup_le fun j => by
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

/- English proof (translation)
Take `⟨j⟩` from `H.nonempty_emb`. Rewrite using `[← H.map_K j]`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `H.mem_EQ j x`.
-/
theorem KQ_le_EQ : KQ H.d ≤ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_K j]
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

def jOf (j : H.E →ₐ[ℚ] Qb) : H.E ≃ₐ[ℚ] H.EQ :=
  AlgEquiv.ofBijective (j.codRestrict H.EQ.toSubalgebra (H.mem_EQ j))
    ⟨fun x y hxy => j.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ j.fieldRange := by rw [H.range_eq j]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem jOf_coe (j : H.E →ₐ[ℚ] Qb) (x : H.E) : ((H.jOf j x : H.EQ) : Qb) = j x := rfl

instance fin_EQ : FiniteDimensional ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  exact (H.jOf j).toLinearEquiv.finiteDimensional

instance normal_EQ : Normal ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  have := H.galois
  exact Normal.of_algEquiv (H.jOf j)

instance fin_FQ : FiniteDimensional ℚ H.FQ :=
  FiniteDimensional.of_injective (inclusion H.FQ_le_EQ).toLinearMap (inclusion H.FQ_le_EQ).toRingHom.injective

/- English proof (translation)
Take `⟨j⟩` from `H.nonempty_emb`. Rewrite `hy` using `[← H.map_FI j]`. Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `hx (τ.comp j.toRingHom)`.
-/
theorem FQ_real (τ : Qb →+* ℂ) {y : Qb} (hy : y ∈ H.FQ) : starRingEnd ℂ (τ y) = τ y := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_FI j] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx (τ.comp j.toRingHom)

variable {H}

/- English proof (translation)
Introduce `j' x`. Take `⟨σ, hσ⟩` from `H.exists_aut j j'`. Establish `h1 : (⟨j' x, H.mem_EQ j' x⟩ : H.EQ) = ⟨j (σ x), H.mem_EQ j _⟩` using `Subtype.ext (hσ x)`. Rewrite using `[h1, h, hσ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, H.gal_comm]`.
-/
theorem actsAs_of_one {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (j : H.E →ₐ[ℚ] Qb)
    (h : ∀ x : H.E, s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)) : H.ActsAs s g := by
  intro j' x
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  have h1 : (⟨j' x, H.mem_EQ j' x⟩ : H.EQ) = ⟨j (σ x), H.mem_EQ j _⟩ := Subtype.ext (hσ x)
  rw [h1, h, hσ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, H.gal_comm]

/- English proof (translation)
Take `⟨j⟩` from `H.nonempty_emb`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `(H.jOf j).surjective y`. Conclude with `(h j x).trans (h' j x).symm`.
-/
theorem ActsAs.unique {s s' : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (h' : H.ActsAs s' g) : s = s' := by
  obtain ⟨j⟩ := H.nonempty_emb
  ext y
  obtain ⟨x, rfl⟩ := (H.jOf j).surjective y
  exact (h j x).trans (h' j x).symm

/- English proof (translation)
Take `⟨j⟩` from `H.nonempty_emb`. Apply `H.gal.symm.injective` to reduce the goal to its premises. Use extensionality with `x`. Conclude with `j.toRingHom.injective ((h j x).symm.trans (h' j x))`.
-/
theorem ActsAs.label_unique {s : H.EQ →ₐ[ℚ] Qb} {g g' : φ.GG} (h : H.ActsAs s g) (h' : H.ActsAs s g') : g = g' := by
  obtain ⟨j⟩ := H.nonempty_emb
  apply H.gal.symm.injective
  ext x
  exact j.toRingHom.injective ((h j x).symm.trans (h' j x))

/- English proof (translation)
Take `⟨j⟩` from `H.nonempty_emb`. Take `⟨y, rfl⟩` from `(H.jOf j).surjective x`. Establish `hy : y ^ 2 = H.sqd ^ 2`. Apply `j.toRingHom.injective` to reduce the goal to its premises. Use `show j (y ^ 2) = j (H.sqd ^ 2)`.

Rewrite using `[H.sqd_sq, map_pow, show j y ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) from hx]`. Simplify using the standard rewrite rules. Establish `h1` using `H.gal_sqd (H.gal.symm g)`. Rewrite `h1` using `[MulEquiv.apply_symm_apply]`. Use `(h j y).trans ?_` and prove the remaining obligations.

Rewrite using `[jOf_coe]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl` into its components or cases. Rewrite using `[h1, map_mul, map_intCast]`. Rewrite using `[map_neg, h1, map_neg, map_neg, map_mul, map_intCast, mul_neg]`.
-/
theorem ActsAs.sqrt_d {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (x : H.EQ) (hx : (x : Qb) ∈ sqrts (-(H.d : ℤ))) :
    s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x := by
  obtain ⟨j⟩ := H.nonempty_emb
  obtain ⟨y, rfl⟩ := (H.jOf j).surjective x
  have hy : y ^ 2 = H.sqd ^ 2 := by
    apply j.toRingHom.injective
    show j (y ^ 2) = j (H.sqd ^ 2)
    rw [H.sqd_sq, map_pow, show j y ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) from hx]; simp
  have h1 := H.gal_sqd (H.gal.symm g)
  rw [MulEquiv.apply_symm_apply] at h1
  refine (h j y).trans ?_
  rw [jOf_coe]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
  · rw [h1, map_mul, map_intCast]
  · rw [map_neg, h1, map_neg, map_neg, map_mul, map_intCast, mul_neg]

variable (H)

/- English proof (translation)
Use `actsAs_of_one j fun x => ?_` and prove the remaining obligations. Use `show j (σ ((H.jOf j).symm (H.jOf j x))) = _`. Rewrite using `[AlgEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]`.
-/
theorem actsAs_gal (j : H.E →ₐ[ℚ] Qb) (σ : H.E ≃ₐ[ℚ] H.E) :
    H.ActsAs ((j.comp (σ : H.E →ₐ[ℚ] H.E)).comp ((H.jOf j).symm : H.EQ →ₐ[ℚ] H.E)) (H.gal σ) := by
  refine actsAs_of_one j fun x => ?_
  show j (σ ((H.jOf j).symm (H.jOf j x))) = _
  rw [AlgEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : x ∈ Algebra.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN))`. Rewrite using `[IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `algebra_adjoin_le_adjoin ℚ _ h1`.
-/
theorem adjoin_cycZeta : IntermediateField.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ Algebra.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim]; trivial
  exact algebra_adjoin_le_adjoin ℚ _ h1

/- English proof (translation)
Set `κ : Cond.Cyc H.condN →ₐ[ℚ] Qb` to `IsAlgClosed.lift`. Establish `hz : IsPrimitiveRoot (κ H.cycZeta) H.condN` using `H.cycZeta_prim.map_of_injective κ.toRingHom.injective`. Establish `hκ : κ.fieldRange = cycQ H.condN`. Rewrite using `[AlgHom.fieldRange_eq_map, ← H.adjoin_cycZeta, adjoin_map, Set.image_singleton, cycQ_eq hz]`. Rewrite using `[← H.range_eq (κ.comp H.cycEmb), ← hκ]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨H.cycEmb x, rfl⟩`.
-/
theorem EQ_le_cycQ : H.EQ ≤ cycQ H.condN := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  have hz : IsPrimitiveRoot (κ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective κ.toRingHom.injective
  have hκ : κ.fieldRange = cycQ H.condN := by
    rw [AlgHom.fieldRange_eq_map, ← H.adjoin_cycZeta, adjoin_map, Set.image_singleton, cycQ_eq hz]
  rw [← H.range_eq (κ.comp H.cycEmb), ← hκ]
  rintro _ ⟨x, rfl⟩
  exact ⟨H.cycEmb x, rfl⟩

/- English proof (translation)
Set `κ : Cond.Cyc H.condN →ₐ[ℚ] Qb` to `IsAlgClosed.lift`. Take `⟨τ, hτ⟩` from `Cond.aut H.condN (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)`. Establish `hτz` using `hτ H.cycZeta H.cycZeta_prim.pow_eq_one`. Establish `hcomm : (s : Qb →ₐ[ℚ] Qb).comp κ = κ.comp (τ : Cond.Cyc H.condN →ₐ[ℚ] Cond.Cyc H.condN)`. Use `AlgHom.ext_of_adjoin_eq_top (s := {H.cycZeta}) (IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim) ?_` and prove the remaining obligations.

Introduce and unpack `_ rfl`. Use `show s (κ H.cycZeta) = κ (τ H.cycZeta)`. Rewrite using `[hτz, map_pow]`. Use `hs _ ?_` and prove the remaining obligations. Use `show κ H.cycZeta ^ H.condN = 1`.

Rewrite using `[← map_pow, H.cycZeta_prim.pow_eq_one, map_one]`. Use `actsAs_of_one (κ.comp H.cycEmb) fun x => ?_` and prove the remaining obligations. Use `show s (κ (H.cycEmb x)) = κ (H.cycEmb (H.gal.symm (H.art u) x))`. Rewrite using `[H.art_spec u τ hτz x]`. Conclude with `DFunLike.congr_fun hcomm (H.cycEmb x)`.
-/
theorem artin (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) :
    H.ActsAs (restr H.EQ s) (H.art u) := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  obtain ⟨τ, hτ⟩ := Cond.aut H.condN (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)
  have hτz := hτ H.cycZeta H.cycZeta_prim.pow_eq_one
  have hcomm : (s : Qb →ₐ[ℚ] Qb).comp κ = κ.comp (τ : Cond.Cyc H.condN →ₐ[ℚ] Cond.Cyc H.condN) := by
    refine AlgHom.ext_of_adjoin_eq_top (s := {H.cycZeta})
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim) ?_
    rintro _ rfl
    show s (κ H.cycZeta) = κ (τ H.cycZeta)
    rw [hτz, map_pow]
    refine hs _ ?_
    show κ H.cycZeta ^ H.condN = 1
    rw [← map_pow, H.cycZeta_prim.pow_eq_one, map_one]
  refine actsAs_of_one (κ.comp H.cycEmb) fun x => ?_
  show s (κ (H.cycEmb x)) = κ (H.cycEmb (H.gal.symm (H.art u) x))
  rw [H.art_spec u τ hτz x]
  exact DFunLike.congr_fun hcomm (H.cycEmb x)

/- English proof (translation)
The claim follows from `H.artin s u hs j x`.
-/
theorem artin_apply (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val)
    (j : H.E →ₐ[ℚ] Qb) (x : H.E) : s (j x) = j (H.gal.symm (H.art u) x) := H.artin s u hs j x

end Formalism.HC.HostRaw

end
