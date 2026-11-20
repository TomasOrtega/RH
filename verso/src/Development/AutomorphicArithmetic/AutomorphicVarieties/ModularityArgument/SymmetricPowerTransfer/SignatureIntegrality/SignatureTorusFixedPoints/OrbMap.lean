import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

open MulAction

namespace UpperTheory.V.Z.Sym.Sig

/- English proof (translation)
Establish `hc : C.map (MulAut.conj t).toMonoidHom = C`. Rewrite using `[MulEquiv.toMonoidHom_eq_coe, ← Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.normalizer_eq_top_iff.mpr hC]`. Conclude with `Subgroup.mem_top t`. Rewrite using `[stabilizer_smul_eq_stabilizer_map_conj]`. Use `conv_lhs => rw [← hc]`.

Conclude with `Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective`.
-/
private theorem relIndex_smul {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (hC : C.Normal)
    (t : T) (y : Y) : (stabilizer T (t • y)).relIndex C = (stabilizer T y).relIndex C := by
  have hc : C.map (MulAut.conj t).toMonoidHom = C := by
    rw [MulEquiv.toMonoidHom_eq_coe, ← Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.normalizer_eq_top_iff.mpr hC]
    exact Subgroup.mem_top t
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hc]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

/- English proof (translation)
Establish `hkT : ∀ (t : T) (y : Y), k (t • y) = k y`. Introduce `t y`. Rewrite using `[hk, hk, hφ, hinv]`. Establish `hst : ∀ y : Y, stabilizer T (φ y) = stabilizer T y`. Introduce `y`.

Use extensionality with `t`. Rewrite using `[mem_stabilizer_iff, mem_stabilizer_iff, ← hφ]`. Conclude with `φ.injective.eq_iff`. Establish `cls' : ∀ (y z : Y'), z ∈ orbit T y → ((stabilizer T z).relIndex C : ℂ) * k' z = ((stabilizer T y).relIndex C : ℂ) * k' y`. Introduce `y z h`.

Take `⟨t, rfl⟩` from `mem_orbit_iff.mp h`. Rewrite using `[relIndex_smul C hC, hinv]`. Set `q : orbitRel.Quotient T Y ≃ orbitRel.Quotient T Y'` to `Quotient.congr φ (by`. Introduce `a b`. Rewrite using `[orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, h⟩`. Conclude with `⟨t, by rw [← hφ, h]⟩`. Introduce and unpack `⟨t, h⟩`. Conclude with `⟨t, φ.injective (by rw [hφ, h])⟩)`.

Unfold `wcount`. Use `finsum_eq_of_bijective q q.bijective ?_` and prove the remaining obligations. Introduce `o`. Establish `hq : q o = Quotient.mk _ (φ (Quotient.out o))` using `by conv_lhs => rw [← Quotient.out_eq o]`. Both sides reduce to the same expression.

Establish `ho : Quotient.out (q o) ∈ orbit T (φ (Quotient.out o))`. Rewrite using `[← orbitRel_apply]`. Conclude with `Quotient.exact (by rw [Quotient.out_eq]; exact hq)`. Rewrite using `[cls' _ _ ho, hst, ← hk]`.
-/
private theorem wcount_congr {T Y Y' : Type} [Group T] [MulAction T Y] [MulAction T Y']
    (C : Subgroup T) (hC : C.Normal) (φ : Y ≃ Y') (hφ : ∀ (t : T) (y : Y), φ (t • y) = t • φ y)
    (k : Y → ℂ) (k' : Y' → ℂ) (hk : ∀ y, k y = k' (φ y)) (hinv : ∀ (t : T) (y : Y'), k' (t • y) = k' y) :
    wcount C k = wcount C k' := by
  have hkT : ∀ (t : T) (y : Y), k (t • y) = k y := by
    intro t y
    rw [hk, hk, hφ, hinv]
  have hst : ∀ y : Y, stabilizer T (φ y) = stabilizer T y := by
    intro y
    ext t
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← hφ]
    exact φ.injective.eq_iff
  have cls' : ∀ (y z : Y'), z ∈ orbit T y →
      ((stabilizer T z).relIndex C : ℂ) * k' z = ((stabilizer T y).relIndex C : ℂ) * k' y := by
    intro y z h
    obtain ⟨t, rfl⟩ := mem_orbit_iff.mp h
    rw [relIndex_smul C hC, hinv]
  let q : orbitRel.Quotient T Y ≃ orbitRel.Quotient T Y' :=
    Quotient.congr φ (by
      intro a b
      rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
      constructor
      · rintro ⟨t, h⟩
        exact ⟨t, by rw [← hφ, h]⟩
      · rintro ⟨t, h⟩
        exact ⟨t, φ.injective (by rw [hφ, h])⟩)
  unfold wcount
  refine finsum_eq_of_bijective q q.bijective ?_
  intro o
  have hq : q o = Quotient.mk _ (φ (Quotient.out o)) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have ho : Quotient.out (q o) ∈ orbit T (φ (Quotient.out o)) := by
    rw [← orbitRel_apply]
    exact Quotient.exact (by rw [Quotient.out_eq]; exact hq)
  rw [cls' _ _ ho, hst, ← hk]

private def qmap {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') :
    G ⧸ U'.comap e → G' ⧸ U' :=
  Quotient.map' e (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa using h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem qmap_mk {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') (g : G) :
    qmap e U' (g : G ⧸ U'.comap e) = (e g : G' ⧸ U') := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective y`. Rewrite `h` using `[qmap_mk, qmap_mk, QuotientGroup.eq]`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `h`. Introduce `z`. Take `⟨c, rfl⟩` from `QuotientGroup.mk_surjective z`. Take `⟨a, rfl⟩` from `he.2 c`.

Conclude with `⟨a, qmap_mk e U' a⟩`.
-/
private theorem qmap_bij {G G' : Type} [Group G] [Group G'] (e : G →* G') (he : Function.Bijective e)
    (U' : Subgroup G') : Function.Bijective (qmap e U') := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [qmap_mk, qmap_mk, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  · intro z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, rfl⟩ := he.2 c
    exact ⟨a, qmap_mk e U' a⟩

/- English proof (translation)
Establish `hu : z⁻¹ * (z : G' ⧸ U').out ∈ U'` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (z : G' ⧸ U')).symm`. Take `⟨u, hu, hw⟩ : ∃ u ∈ U', (z : G' ⧸ U').out = z * u` from `⟨_, hu, (mul_inv_cancel_left z _).symm⟩`. Rewrite using `[hw, ← hf u hu (z⁻¹ * x * θ' z)]`. Use `congr 1`. Rewrite using `[map_mul]`.

Use `group`.
-/
private theorem f_out {G' : Type} [Group G'] (θ' : G' →* G') (U' : Subgroup G') (f : G' → ℂ)
    (hf : ∀ u ∈ U', ∀ x, f (u⁻¹ * x * θ' u) = f x) (x z : G') :
    f ((z : G' ⧸ U').out⁻¹ * x * θ' (z : G' ⧸ U').out) = f (z⁻¹ * x * θ' z) := by
  have hu : z⁻¹ * (z : G' ⧸ U').out ∈ U' :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (z : G' ⧸ U')).symm
  obtain ⟨u, hu, hw⟩ : ∃ u ∈ U', (z : G' ⧸ U').out = z * u :=
    ⟨_, hu, (mul_inv_cancel_left z _).symm⟩
  rw [hw, ← hf u hu (z⁻¹ * x * θ' z)]
  congr 1
  rw [map_mul]
  group

end UpperTheory.V.Z.Sym.Sig

/- English proof (translation)
Introduce `T G G' _ _ _ e he ι C θ θ' hθ U' f δ hf hδ hC`. Set `E : G ≃* G'` to `MulEquiv.ofBijective e he`. Establish `hc : ∀ (g : G), e (g⁻¹ * δ * θ g) = (e g)⁻¹ * e δ * θ' (e g)`. Introduce `g`. Rewrite using `[map_mul, map_mul, map_inv, hθ]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `letI : MulAction T (G ⧸ U'.comap e) := MulAction.compHom _ ι`. Use `letI : MulAction T (G' ⧸ U') := MulAction.compHom _ (e.comp ι)`. Unfold `UpperTheory.V.Z.Sym.orb`. Use `UpperTheory.V.Z.Sym.Sig.wcount_congr C hC (Equiv.ofBijective _ (UpperTheory.V.Z.Sym.Sig.qmap_bij e he U')) ?_ _ _ ?_ ?_` and prove the remaining obligations.

Introduce `t y`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective y`. Rewrite using `[MulAction.compHom_smul_def, MulAction.compHom_smul_def]`. Simplify using `only [Equiv.ofBijective_apply, MulAction.Quotient.smul_coe, smul_eq_mul, UpperTheory.V.Z.Sym.Sig.qmap_mk, map_mul, MonoidHom.comp_apply]`. Introduce `y`.

Simplify using `only [Equiv.ofBijective_apply]`. Use `conv_rhs => rw [← QuotientGroup.out_eq' y, UpperTheory.V.Z.Sym.Sig.qmap_mk, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf]`. Rewrite using `[hc]`. Introduce `t y`. Take `⟨z, rfl⟩` from `QuotientGroup.mk_surjective y`.

Rewrite using `[MulAction.compHom_smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, MonoidHom.comp_apply]`. Use `congr 1`. Establish `h1 : e ((ι t)⁻¹ * δ * θ (ι t)) = e δ` using `by rw [hδ]`. Rewrite `h1` using `[hc]`. Establish `key : (e (ι t) * z)⁻¹ * e δ * θ' (e (ι t) * z) = z⁻¹ * ((e (ι t))⁻¹ * e δ * θ' (e (ι t))) * θ' z`.

Rewrite using `[map_mul]`. Use `group`. Rewrite using `[key, h1]`. Unfold `UpperTheory.V.Z.Sym.FinOrb`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨S, hS⟩`. Use `⟨S.image e, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `he.2 y`. Rewrite `hy` using `[← hc]`. Take `⟨t, s, hs, u, hu, rfl⟩` from `hS g hy`.

Conclude with `⟨t, e s, Finset.mem_image_of_mem e hs, e u, hu, by simp [map_mul]⟩`. Introduce and unpack `⟨S, hS⟩`. Use `⟨S.image E.symm, fun g hg => ?_⟩` and prove the remaining obligations. Simplify using `only at hg`. Rewrite `hg` using `[hc]`.

Take `⟨t, s, hs, u, hu, h⟩` from `hS (e g) hg`. Use `⟨t, E.symm s, Finset.mem_image_of_mem _ hs, E.symm u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap] show E (E.symm u) ∈ U'`. Rewrite using `[MulEquiv.apply_symm_apply]`. Conclude with `hu`.

Apply `E.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]`. Conclude with `h`. Introduce `y`. Use extensionality with `t`.

Simplify using `only [Subgroup.mem_comap, mem_stabilizer_iff, MonoidHom.comp_apply, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, map_mul, map_inv]`.
-/
theorem UpperTheory.V.Z.Sym.Sig.orbMap :
    UpperTheory.V.Z.Sym.Sig.OrbMap := by
  classical
  intro T G G' _ _ _ e he ι C θ θ' hθ U' f δ hf hδ hC
  let E : G ≃* G' := MulEquiv.ofBijective e he
  have hc : ∀ (g : G), e (g⁻¹ * δ * θ g) = (e g)⁻¹ * e δ * θ' (e g) := by
    intro g
    rw [map_mul, map_mul, map_inv, hθ]
  refine ⟨?_, ?_, ?_⟩
  · letI : MulAction T (G ⧸ U'.comap e) := MulAction.compHom _ ι
    letI : MulAction T (G' ⧸ U') := MulAction.compHom _ (e.comp ι)
    unfold UpperTheory.V.Z.Sym.orb
    refine UpperTheory.V.Z.Sym.Sig.wcount_congr C hC
      (Equiv.ofBijective _ (UpperTheory.V.Z.Sym.Sig.qmap_bij e he U')) ?_ _ _ ?_ ?_
    · intro t y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
      simp only [Equiv.ofBijective_apply, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.qmap_mk, map_mul, MonoidHom.comp_apply]
    · intro y
      simp only [Equiv.ofBijective_apply]
      conv_rhs => rw [← QuotientGroup.out_eq' y, UpperTheory.V.Z.Sym.Sig.qmap_mk, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf]
      rw [hc]
    · intro t y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, MonoidHom.comp_apply]
      congr 1
      have h1 : e ((ι t)⁻¹ * δ * θ (ι t)) = e δ := by rw [hδ]
      rw [hc] at h1
      have key : (e (ι t) * z)⁻¹ * e δ * θ' (e (ι t) * z)
          = z⁻¹ * ((e (ι t))⁻¹ * e δ * θ' (e (ι t))) * θ' z := by
        rw [map_mul]
        group
      rw [key, h1]
  · unfold UpperTheory.V.Z.Sym.FinOrb
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S.image e, fun y hy => ?_⟩
      obtain ⟨g, rfl⟩ := he.2 y
      rw [← hc] at hy
      obtain ⟨t, s, hs, u, hu, rfl⟩ := hS g hy
      exact ⟨t, e s, Finset.mem_image_of_mem e hs, e u, hu, by simp [map_mul]⟩
    · rintro ⟨S, hS⟩
      refine ⟨S.image E.symm, fun g hg => ?_⟩
      simp only at hg
      rw [hc] at hg
      obtain ⟨t, s, hs, u, hu, h⟩ := hS (e g) hg
      refine ⟨t, E.symm s, Finset.mem_image_of_mem _ hs, E.symm u, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        show E (E.symm u) ∈ U'
        rw [MulEquiv.apply_symm_apply]
        exact hu
      · apply E.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h
  · intro y
    ext t
    simp only [Subgroup.mem_comap, mem_stabilizer_iff, MonoidHom.comp_apply,
      MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, map_mul, map_inv]
