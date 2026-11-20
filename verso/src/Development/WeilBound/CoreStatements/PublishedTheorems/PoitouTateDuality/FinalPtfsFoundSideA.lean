import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ExistsUniformizerOrd
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion PositivityTheory.LocalTateOrthogonality.Gcoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Roots

variable {Kf : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime]

def rvF (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
    ZMod (l ^ r) →+ gsRoots S (l ^ r) :=
  ZMod.lift (l ^ r) ⟨zmultiplesHom (gsRoots S (l ^ r))
    (Additive.ofMul u : Additive (rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))), by
    have h := nsmul_gsRoots S (l ^ r) (Additive.ofMul u : Additive (rootsOfUnity (l ^ r)
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)))
    rw [← natCast_zsmul] at h
    exact (zmultiplesHom_apply _ _ _).trans h⟩

/- English proof (translation)
Establish `ha : a = ((a.val : ℤ) : ZMod (l ^ r))` using `by simp`. Use `conv_lhs => rw [ha]`. Rewrite using `[rvF, ZMod.lift_coe]`. Use `erw [zmultiplesHom_apply, natCast_zsmul]`.
-/
theorem rvF_eq (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (a : ZMod (l ^ r)) : rvF S u a = Additive.ofMul (u ^ a.val) := by
  have ha : a = ((a.val : ℤ) : ZMod (l ^ r)) := by simp
  conv_lhs => rw [ha]
  rw [rvF, ZMod.lift_coe]
  erw [zmultiplesHom_apply, natCast_zsmul]

/- English proof (translation)
Rewrite using `[rvF_eq]`. Express the relevant statement in the definitionally equal form `(((((u ^ a.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ)) = _`. Rewrite using `[SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]`.
-/
theorem rvF_coe (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (a : ZMod (l ^ r)) :
    ((((Additive.toMul (rvF S u a) : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
      AlgebraicClosure ℚ) = ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) ^ a.val := by
  rw [rvF_eq]
  change (((((u ^ a.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
    (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
    AlgebraicClosure ℚ)) = _
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]

end Roots

section Cochains

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[inhomogeneousCochains.d_hom_apply, dn_app, map_add, map_sum, he]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]`.
-/
theorem d_comp_homF (rho : Representation R G M) (A : Rep.{0} k G) (e : M →+ A.V)
    (he : ∀ g m, e (rho g m) = A.ρ g (e m)) (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  funext s
  rw [inhomogeneousCochains.d_hom_apply, dn_app, map_add, map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]

end Cochains

/- English proof (translation)
Simplify using `only [urChar, map_mul, toAdd_mul, map_add]`.
-/
theorem urChar_mulF {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+)
    (σ τ : Gal(Ω/K)) : urChar K Ω N (σ * τ) = urChar K Ω N σ + urChar K Ω N τ := by
  simp only [urChar, map_mul, toAdd_mul, map_add]

/- English proof (translation)
Establish `h : urChar K Ω N = fun σ => unramifiedCoord K σ N` using `rfl`. Rewrite using `[h, IsLocallyConstant.iff_continuous]`. Conclude with `continuous_unramifiedCoord N`.
-/
theorem urChar_isLocallyConstant {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+) :
    IsLocallyConstant (urChar K Ω N) := by
  have h : urChar K Ω N = fun σ => unramifiedCoord K σ N := rfl
  rw [h, IsLocallyConstant.iff_continuous]
  exact continuous_unramifiedCoord N

/- English proof (translation)
Establish `hmod : ζ ^ a = ζ ^ (a % N)` using `by conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`. Rewrite `h` using `[hmod]`. Establish `h2` using `hζ.pow_inj (Nat.mod_lt _ (NeZero.pos N)) (ZMod.val_lt b) h`. Rewrite using `[← ZMod.natCast_mod, h2, ZMod.natCast_zmod_val]`.
-/
theorem zmod_eq_of_pow_eq {L : Type} [CommRing L] [IsDomain L] {N : ℕ} [NeZero N] {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) {a : ℕ} {b : ZMod N} (h : ζ ^ a = ζ ^ b.val) : (a : ZMod N) = b := by
  have hmod : ζ ^ a = ζ ^ (a % N) := by
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [hmod] at h
  have h2 := hζ.pow_inj (Nat.mod_lt _ (NeZero.pos N)) (ZMod.val_lt b) h
  rw [← ZMod.natCast_mod, h2, ZMod.natCast_zmod_val]

end PositivityTheory.Lit1.PTN
