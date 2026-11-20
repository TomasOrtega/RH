import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

/- English proof (translation)
Set `qP : Nat.Primes` to `⟨q, Fact.out⟩`. Set `v : IsDedekindDomain.HeightOneSpectrum ℤ` to `(Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm qP`. Establish `hgen : Rat.HeightOneSpectrum.natGenerator v = q` using `congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply qP)`. Establish `hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}`. Introduce `h`.

Establish `h1` using `Rat.HeightOneSpectrum.natGenerator_dvd_iff v (n := p)`. Rewrite `h1` using `[hgen, h, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton]`. Conclude with `hq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp (h1.mpr dvd_rfl))`. Set `w : AwayP p` to `⟨v, hv⟩`. Set `e` to `(Padic.adicCompletionEquiv ℤ qP).symm`.

Use `⟨(e.toAlgEquiv.toRingEquiv.toRingHom).comp (AfP.eval w).toRingHom, ?_⟩` and prove the remaining obligations. Conclude with `e.continuous.comp (RestrictedProduct.continuous_eval w)`.
-/
private theorem UpperTheory.Gal.Spc.boundQ_exists_hom (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hq : q ≠ p) :
    ∃ φ : AfP p →+* ℚ_[q], Continuous φ := by
  let qP : Nat.Primes := ⟨q, Fact.out⟩
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm qP
  have hgen : Rat.HeightOneSpectrum.natGenerator v = q :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply qP)
  have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := Rat.HeightOneSpectrum.natGenerator_dvd_iff v (n := p)
    rw [hgen, h, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at h1
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp (h1.mpr dvd_rfl))
  let w : AwayP p := ⟨v, hv⟩
  let e := (Padic.adicCompletionEquiv ℤ qP).symm
  refine ⟨(e.toAlgEquiv.toRingEquiv.toRingHom).comp (AfP.eval w).toRingHom, ?_⟩
  exact e.continuous.comp (RestrictedProduct.continuous_eval w)

/- English proof (translation)
Introduce `p _ G P x t hx L g q _ hqp`. Take `⟨φ, hφ⟩` from `UpperTheory.Gal.Spc.boundQ_exists_hom p q hqp`. Use `letI τ : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _`. Use `haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _`.

Set `b` to `Module.finBasis ℚ G.C`. Set `bA` to `b.baseChange (AfP p)`. Set `F : G.GAf → (Fin (Module.finrank ℚ G.C) → ℚ_[q])` to `fun v i => φ (bA.repr (((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (((v : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) * (x : AfP p ⊗[ℚ] G.C))) i)`. Establish `hval : Continuous (fun v : G.GAf => (((v : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)))` using `Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)`. Establish `hF : Continuous F`.

Use `continuous_pi fun i => hφ.comp ?_` and prove the remaining obligations. Establish `hc : Continuous (fun z : AfP p ⊗[ℚ] G.C => bA.repr z i)` using `IsModuleTopology.continuous_of_linearMap (bA.coord i)`. Conclude with `hc.comp (continuous_const.mul (hval.mul continuous_const))`. Establish `hconj : ⇑(MulAut.conj g).toMonoidHom = fun v => g * v * g⁻¹`. Use function extensionality and compare the values at `v`.

Simplify using `[MulAut.conj_apply]`. Establish `hK : IsCompact ((L.K.toSubgroup.map (MulAut.conj g).toMonoidHom : Subgroup G.GAf) : Set G.GAf)`. Rewrite using `[Subgroup.coe_map, hconj]`. Conclude with `L.compact.image ((continuous_const.mul continuous_id).mul continuous_const)`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn hF.continuousOn`.

Use `⟨B, fun w hw i => ?_⟩` and prove the remaining obligations. Establish `hv : (((P.toAf x t hx w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ((w : G.Cˣ × ℚˣ).1 : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)` using `rfl`. Establish `hFw : F (P.toAf x t hx w) i = (((b.repr ((w : G.Cˣ × ℚˣ).1 : G.C) i : ℚ)) : ℚ_[q])`. Simplify using `only [F, hv, mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]`. Simplify using `only [inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, bA, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]`.

Conclude with `eq_ratCast (φ.comp (algebraMap ℚ (AfP p))) _`. Rewrite using `[← hFw]`. Conclude with `(norm_le_pi_norm (F _) i).trans (hB _ hw)`.
-/
theorem UpperTheory.Gal.Spc.boundQ :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (L : G.Level) (g : G.GAf) (q : ℕ) [Fact q.Prime], q ≠ p → ∃ B : ℝ, ∀ w : P.cent, P.toAf x t hx w ∈ L.K.toSubgroup.map (MulAut.conj g).toMonoidHom → ∀ i, ‖(((Module.finBasis ℚ G.C).repr ((w : G.Cˣ × ℚˣ).1 : G.C) i : ℚ) : ℚ_[q])‖ ≤ B := by
  intro p _ G P x t hx L g q _ hqp
  obtain ⟨φ, hφ⟩ := UpperTheory.Gal.Spc.boundQ_exists_hom p q hqp
  letI τ : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  let b := Module.finBasis ℚ G.C
  let bA := b.baseChange (AfP p)
  let F : G.GAf → (Fin (Module.finrank ℚ G.C) → ℚ_[q]) := fun v i =>
    φ (bA.repr (((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((v : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) * (x : AfP p ⊗[ℚ] G.C))) i)
  have hval : Continuous (fun v : G.GAf =>
      (((v : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C))) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hF : Continuous F := by
    refine continuous_pi fun i => hφ.comp ?_
    have hc : Continuous (fun z : AfP p ⊗[ℚ] G.C => bA.repr z i) :=
      IsModuleTopology.continuous_of_linearMap (bA.coord i)
    exact hc.comp (continuous_const.mul (hval.mul continuous_const))
  have hconj : ⇑(MulAut.conj g).toMonoidHom = fun v => g * v * g⁻¹ := by
    funext v
    simp [MulAut.conj_apply]
  have hK : IsCompact ((L.K.toSubgroup.map (MulAut.conj g).toMonoidHom : Subgroup G.GAf) : Set G.GAf) := by
    rw [Subgroup.coe_map, hconj]
    exact L.compact.image ((continuous_const.mul continuous_id).mul continuous_const)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨B, fun w hw i => ?_⟩
  have hv : (((P.toAf x t hx w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) =
      (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ((w : G.Cˣ × ℚˣ).1 : G.C) *
        ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
  have hFw : F (P.toAf x t hx w) i = (((b.repr ((w : G.Cˣ × ℚˣ).1 : G.C) i : ℚ)) : ℚ_[q]) := by
    simp only [F, hv, mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
    simp only [inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, bA,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    exact eq_ratCast (φ.comp (algebraMap ℚ (AfP p))) _
  rw [← hFw]
  exact (norm_le_pi_norm (F _) i).trans (hB _ hw)
