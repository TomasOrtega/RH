import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits

section Generic

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

/- English proof (translation)
Set `_ : Algebra E L` to `ι.toRingHom.toAlgebra`. Establish `: IsScalarTower ℚ E L` using `IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm`. Conclude with `⟨σ.liftNormal L, fun x => (AlgEquiv.liftNormal_commutes σ L x).symm⟩`.
-/
theorem exists_lift [IsGalois ℚ L] (ι : E →ₐ[ℚ] L) (σ : E ≃ₐ[ℚ] E) :
    ∃ τ : L ≃ₐ[ℚ] L, ∀ x, ι (σ x) = τ (ι x) := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact ⟨σ.liftNormal L, fun x => (AlgEquiv.liftNormal_commutes σ L x).symm⟩

/- English proof (translation)
Set `_ : Algebra E L` to `ι.toRingHom.toAlgebra`. Establish `: IsScalarTower ℚ E L` using `IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm`. Establish `: Algebra.IsAlgebraic E L` using `Algebra.IsAlgebraic.tower_top (K := ℚ) E`. Conclude with `⟨ComplexEmbedding.lift L ψ, fun x => ComplexEmbedding.lift_algebraMap_apply L ψ x⟩`.
-/
theorem exists_emb_lift (ι : E →ₐ[ℚ] L) (ψ : E →+* ℂ) : ∃ Ψ : L →+* ℂ, ∀ x, Ψ (ι x) = ψ x := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  exact ⟨ComplexEmbedding.lift L ψ, fun x => ComplexEmbedding.lift_algebraMap_apply L ψ x⟩

end Generic

section Cyc

variable (N : ℕ) [NeZero N]

def tauN : (ZMod N)ˣ ≃* (Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N)).symm

/- English proof (translation)
Rewrite using `[IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) _ hw, tauN, MulEquiv.apply_symm_apply]`.
-/
theorem tauN_root (u : (ZMod N)ˣ) (w : Cond.Cyc N) (hw : w ^ N = 1) : tauN N u w = w ^ (u : ZMod N).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) _ hw, tauN, MulEquiv.apply_symm_apply]

/- English proof (translation)
The claim follows from `IsCyclotomicExtension.isGalois {N} ℚ _`.
-/
theorem cyc_isGalois : IsGalois ℚ (Cond.Cyc N) := IsCyclotomicExtension.isGalois {N} ℚ _

/- English proof (translation)
Establish `key : (Ψ.comp (tauN N (-1) : Cond.Cyc N →+* Cond.Cyc N)).toRatAlgHom = ((starRingEnd ℂ).comp Ψ).toRatAlgHom`. Use `AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec N)) ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality.

Use `show Ψ (tauN N (-1) (Cond.z N)) = starRingEnd ℂ (Ψ (Cond.z N))`. Establish `hz` using `(Cond.z_spec N).pow_eq_one`. Establish `h1 : ‖Ψ (Cond.z N)‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) (NeZero.ne N)`. Establish `h2 : Cond.z N ^ ((-1 : (ZMod N)ˣ) : ZMod N).val * Cond.z N = 1`. Rewrite using `[← pow_succ, (Cond.z_spec N).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]`.

Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val]`. Simplify using the standard rewrite rules. Rewrite using `[tauN_root N _ _ hz, ← Complex.inv_eq_conj h1]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[← map_mul, h2, map_one]`. Conclude with `DFunLike.congr_fun key x`.
-/
theorem tauN_neg_one (Ψ : Cond.Cyc N →+* ℂ) (x : Cond.Cyc N) : Ψ (tauN N (-1) x) = starRingEnd ℂ (Ψ x) := by
  have key : (Ψ.comp (tauN N (-1) : Cond.Cyc N →+* Cond.Cyc N)).toRatAlgHom =
      ((starRingEnd ℂ).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec N)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN N (-1) (Cond.z N)) = starRingEnd ℂ (Ψ (Cond.z N))
    have hz := (Cond.z_spec N).pow_eq_one
    have h1 : ‖Ψ (Cond.z N)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) (NeZero.ne N)
    have h2 : Cond.z N ^ ((-1 : (ZMod N)ˣ) : ZMod N).val * Cond.z N = 1 := by
      rw [← pow_succ, (Cond.z_spec N).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    rw [tauN_root N _ _ hz, ← Complex.inv_eq_conj h1]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, h2, map_one]
  exact DFunLike.congr_fun key x

end Cyc

variable {φ : Frame} (H : HostRaw φ)

instance neZero_condN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩

def emb : H.E →ₐ[ℚ] Cond.Cyc H.condN := H.cycEmb

/- English proof (translation)
The claim follows from `H.art_spec u (tauN H.condN u) (tauN_root H.condN u _ H.cycZeta_prim.pow_eq_one) x`.
-/
theorem emb_art (u : (ZMod H.condN)ˣ) (x : H.E) :
    emb H (H.gal.symm (H.art u) x) = tauN H.condN u (emb H x) :=
  H.art_spec u (tauN H.condN u) (tauN_root H.condN u _ H.cycZeta_prim.pow_eq_one) x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Rewrite using `[← emb_art, ← h, MulEquiv.symm_apply_apply]`. Introduce `h`. Establish `h1 : σ = H.gal.symm (H.art u)` using `AlgEquiv.ext fun x => (emb H).injective (by show emb H _ = emb H _; rw [h, emb_art])`.

Rewrite using `[h1, MulEquiv.apply_symm_apply]`.
-/
theorem gal_eq_art_iff (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) :
    H.gal σ = H.art u ↔ ∀ x, emb H (σ x) = tauN H.condN u (emb H x) := by
  constructor
  · intro h x
    rw [← emb_art, ← h, MulEquiv.symm_apply_apply]
  · intro h
    have h1 : σ = H.gal.symm (H.art u) :=
      AlgEquiv.ext fun x => (emb H).injective (by show emb H _ = emb H _; rw [h, emb_art])
    rw [h1, MulEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `g`. Use `cyc_isGalois H.condN` as an intermediate fact. Take `⟨τ, hτ⟩` from `exists_lift (emb H) (H.gal.symm g)`. Take `⟨u, rfl⟩` from `(tauN H.condN).surjective τ`. Conclude with `⟨u, by rw [← (gal_eq_art_iff H _ u).mpr hτ, MulEquiv.apply_symm_apply]⟩`.
-/
theorem art_surj : Function.Surjective H.art := by
  intro g
  have := cyc_isGalois H.condN
  obtain ⟨τ, hτ⟩ := exists_lift (emb H) (H.gal.symm g)
  obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
  exact ⟨u, by rw [← (gal_eq_art_iff H _ u).mpr hτ, MulEquiv.apply_symm_apply]⟩

/- English proof (translation)
The claim follows from `H.gal.apply_symm_apply _`.
-/
theorem gal_conj : H.gal H.conj = φ.cc := H.gal.apply_symm_apply _

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `exists_emb_lift (emb H) ψ`. Rewrite using `[← hΨ, ← hΨ, ← tauN_neg_one, (gal_eq_art_iff H H.conj (-1)).mp ((gal_conj H).trans H.art_neg_one.symm)]`.
-/
theorem conj_apply (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := by
  obtain ⟨Ψ, hΨ⟩ := exists_emb_lift (emb H) ψ
  rw [← hΨ, ← hΨ, ← tauN_neg_one, (gal_eq_art_iff H H.conj (-1)).mp ((gal_conj H).trans H.art_neg_one.symm)]

/- English proof (translation)
Introduce `ψ σ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : σ = H.conj` using `AlgEquiv.ext fun x => ψ.injective (by rw [h, conj_apply])`. Rewrite using `[h1, gal_conj]`.

Introduce `h x`. Establish `h1 : σ = H.conj` using `H.gal.injective (h.trans (gal_conj H).symm)`. Rewrite using `[h1, conj_apply]`.
-/
theorem conj_iff : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc := by
  intro ψ σ
  constructor
  · intro h
    have h1 : σ = H.conj := AlgEquiv.ext fun x => ψ.injective (by rw [h, conj_apply])
    rw [h1, gal_conj]
  · intro h x
    have h1 : σ = H.conj := H.gal.injective (h.trans (gal_conj H).symm)
    rw [h1, conj_apply]

/- English proof (translation)
Introduce `h`. Establish `h1` using `H.sqd_sq`. Rewrite `h1` using `[h]`. Establish `h2 : (H.d : H.E) = 0` using `by simpa using h1.symm`. Conclude with `H.hyp.2.1.ne_zero (by exact_mod_cast h2)`.
-/
theorem sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have h2 : (H.d : H.E) = 0 := by simpa using h1.symm
  exact H.hyp.2.1.ne_zero (by exact_mod_cast h2)

/- English proof (translation)
Rewrite using `[H.gal_sqd, gal_conj]`. Simplify using `[Frame.cc, c0]`.
-/
theorem conj_sqd : H.conj H.sqd = -H.sqd := by
  rw [H.gal_sqd, gal_conj]
  simp [Frame.cc, c0]

/- English proof (translation)
Use `H.galois` as an intermediate fact. Establish `hTC : IsTotallyComplex H.E`. Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]`. Introduce `hw`.

Establish `h2` using `RingHom.congr_fun hw H.sqd`. Rewrite `h2` using `[ComplexEmbedding.conjugate_coe_eq, ← conj_apply, conj_sqd, map_neg]`. Establish `h3 : (2 : ℂ) * w.embedding H.sqd = 0` using `by linear_combination -h2`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `two_ne_zero h4`.

Conclude with `(map_ne_zero _).2 (sqd_ne_zero H) h4`. Use `IsCMField.of_forall_isConj H.E (σ := H.conj) (fun ψ => ?_)` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `(conj_apply H ψ x).symm`.
-/
theorem cm : IsCMField H.E := by
  have := H.galois
  have hTC : IsTotallyComplex H.E := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw H.sqd
    rw [ComplexEmbedding.conjugate_coe_eq, ← conj_apply, conj_sqd, map_neg] at h2
    have h3 : (2 : ℂ) * w.embedding H.sqd = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (sqd_ne_zero H) h4
  refine IsCMField.of_forall_isConj H.E (σ := H.conj) (fun ψ => ?_)
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (conj_apply H ψ x).symm

/- English proof (translation)
Use `H.galois` as an intermediate fact. Rewrite using `[← IsGalois.card_aut_eq_finrank, ← φ.natCard_GG]`. Conclude with `Nat.card_congr H.gal.toEquiv`.
-/
theorem finrank_E : Module.finrank ℚ H.E = 4 * φ.ord := by
  have := H.galois
  rw [← IsGalois.card_aut_eq_finrank, ← φ.natCard_GG]
  exact Nat.card_congr H.gal.toEquiv

/- English proof (translation)
Use `cm H` as an intermediate fact. Establish `h0` using `Module.finrank_mul_finrank ℚ H.F H.E`. Rewrite `h0` using `[Algebra.IsQuadraticExtension.finrank_eq_two H.F H.E, finrank_E]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_F : Module.finrank ℚ H.F = 2 * φ.ord := by
  have := cm H
  have h0 := Module.finrank_mul_finrank ℚ H.F H.E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two H.F H.E, finrank_E] at h0
  omega

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_maximalRealSubfield_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Set `ψ : H.E →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`.

Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[conj_apply]`. Conclude with `hx ψ`. Introduce `hx ψ`. Use `conj_apply H ψ x` as an intermediate fact.

Rewrite `this` using `[hx]`. Conclude with `this.symm`.
-/
theorem mem_F : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x := by
  intro x
  rw [mem_maximalRealSubfield_iff]
  constructor
  · intro hx
    let ψ : H.E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply ψ.injective
    rw [conj_apply]
    exact hx ψ
  · intro hx ψ
    have := conj_apply H ψ x
    rw [hx] at this
    exact this.symm

/- English proof (translation)
The claim follows from `D7.d4 H.hyp`.
-/
theorem d_mod_four : H.d % 4 = 3 := D7.d4 H.hyp

/- English proof (translation)
Introduce `u`. Establish `hd : H.d ∣ H.condN` using `dvd_mul_left _ _`. Establish `h1` using `D7.sqrt_act H.hyp.2.1 (d_mod_four H) hd u (tauN H.condN u) (tauN_root H.condN u) (emb H H.sqd) (by rw [← map_pow, H.sqd_sq, map_neg, map_natCast])`. Rewrite `h1` using `[← emb_art, H.gal_sqd, MulEquiv.apply_symm_apply, map_mul, map_intCast, D7.sgnN_val]`. Establish `h2` using `mul_right_cancel₀ ((map_ne_zero (emb H)).mpr (sqd_ne_zero H)) h1`.

Conclude with `h2` after adjusting the coercions.
-/
theorem art_ch : ∀ u : (ZMod H.condN)ˣ,
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  intro u
  have hd : H.d ∣ H.condN := dvd_mul_left _ _
  have h1 := D7.sqrt_act H.hyp.2.1 (d_mod_four H) hd u (tauN H.condN u) (tauN_root H.condN u) (emb H H.sqd)
    (by rw [← map_pow, H.sqd_sq, map_neg, map_natCast])
  rw [← emb_art, H.gal_sqd, MulEquiv.apply_symm_apply, map_mul, map_intCast, D7.sgnN_val] at h1
  have h2 := mul_right_cancel₀ ((map_ne_zero (emb H)).mpr (sqd_ne_zero H)) h1
  exact_mod_cast h2

/- English proof (translation)
Rewrite using `[Frame.mem_Psi_iff, H.gal_sqd σ]`. Break down `Int.units_eq_one_or (H.gal σ).1.2 with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[h]`. Use `iff_of_false (by decide) fun h1 => sqd_ne_zero H ?_` and prove the remaining obligations.

Establish `h2 : (2 : H.E) * H.sqd = 0`. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1`. Take the linear combination `-h1`. Simplify using `using h2`.
-/
theorem gal_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.mem_Psi_iff, H.gal_sqd σ]
  rcases Int.units_eq_one_or (H.gal σ).1.2 with h | h
  · simp [h]
  · rw [h]
    refine iff_of_false (by decide) fun h1 => sqd_ne_zero H ?_
    have h2 : (2 : H.E) * H.sqd = 0 := by
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
      linear_combination -h1
    simpa using h2

end Formalism.HC.Der

end
