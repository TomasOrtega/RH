import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.U3

/- English proof (translation)
Use `⟨fun w' => if h : ∃ y : O, w' = y • w then Ideal.Quotient.mk _ h.choose else 0, fun y => ?_⟩` and prove the remaining obligations. Establish `h : ∃ y' : O, y • w = y' • w` using `⟨y, rfl⟩`. Simplify using `only`. Rewrite using `[dif_pos h, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hw, sub_smul, ← h.choose_spec, sub_self]`.
-/
private theorem shaInj_phi {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (b : O) (w : W)
    (hw : ∀ y : O, y • w = 0 ↔ b ∣ y) :
    ∃ φ : W → O ⧸ Ideal.span {b}, ∀ y : O, φ (y • w) = Ideal.Quotient.mk _ y := by
  classical
  refine ⟨fun w' => if h : ∃ y : O, w' = y • w then Ideal.Quotient.mk _ h.choose else 0, fun y => ?_⟩
  have h : ∃ y' : O, y • w = y' • w := ⟨y, rfl⟩
  dsimp only
  rw [dif_pos h, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hw, sub_smul, ← h.choose_spec, sub_self]

/- English proof (translation)
Establish `hz : z.1 ∈ ReciprocityTheory.Gal.Z1 ((Formalism.GaloisCohomology.scalRep W α).comp (⊤ : Subgroup Γ).subtype)` using `z.2`. Rewrite `hz` using `[ReciprocityTheory.Gal.mem_Z1_iff_cocycle]`. Use `⟨hz.1.comp (continuous_id.subtype_mk _), fun g h => ?_⟩` and prove the remaining obligations. Use `hz.2 ⟨g, trivial⟩ ⟨h, trivial⟩` as an intermediate fact. Simplify using `[Formalism.GaloisCohomology.scalRep] at this`.

Conclude with `this`.
-/
private theorem continuous_and_cocycle_eq_of_z1U_whole_group {O Γ W : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul O W] (α : Γ →* Oˣ) (z : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ)) :
    Continuous (fun g : Γ => z.1 ⟨g, trivial⟩) ∧
      ∀ g h : Γ, z.1 ⟨g * h, trivial⟩ = z.1 ⟨g, trivial⟩ + (α g : O) • z.1 ⟨h, trivial⟩ := by
  have hz : z.1 ∈ ReciprocityTheory.Gal.Z1 ((Formalism.GaloisCohomology.scalRep W α).comp (⊤ : Subgroup Γ).subtype) := z.2
  rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle] at hz
  refine ⟨hz.1.comp (continuous_id.subtype_mk _), fun g h => ?_⟩
  have := hz.2 ⟨g, trivial⟩ ⟨h, trivial⟩
  simp [Formalism.GaloisCohomology.scalRep] at this
  exact this

/- English proof (translation)
Take `⟨u, hu⟩` from `hδ`. Set `L : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ) →ₗ[O] (Γ → W)` to `{ toFun := fun z g => z.1 ⟨g, trivial⟩ - ((u⁻¹ : Oˣ) : O) • (z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩ - z.1 ⟨δ, trivial⟩) map_add' := by`. Introduce `a b`. Use function extensionality and compare the values at `g`. Simplify using `only [Submodule.coe_add, Pi.add_apply, smul_sub, smul_add]`.

Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := by`. Introduce `c a`. Use function extensionality and compare the values at `g`. Simplify using `only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]`.

Rewrite using `[smul_comm ((u⁻¹ : Oˣ) : O) c, smul_comm ((u⁻¹ : Oˣ) : O) c, smul_comm ((u⁻¹ : Oˣ) : O) c] }`. Establish `hL : ∀ z g, L z g = z.1 ⟨g, trivial⟩ - ((α g : O) • (((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩) - ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩)`. Introduce `z g`. Establish `e : (α g : O) • z.1 ⟨δ, trivial⟩ = z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩`. Rewrite using `[(continuous_and_cocycle_eq_of_z1U_whole_group α z).2 g δ]`.

Normalize the expressions using the abelian group laws. Use `show z.1 ⟨g, trivial⟩ - ((u⁻¹ : Oˣ) : O) • (z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩ - z.1 ⟨δ, trivial⟩) = _`. Rewrite using `[smul_comm (α g : O), e, ← smul_sub]`. Establish `hu' : ∀ x : W, (α δ : O) • x - x = (u : O) • x` using `fun x => by rw [hu, sub_smul, one_smul]`. Establish `hB : ∀ z : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ), z.1 ∈ ReciprocityTheory.Gal.B1 ((Formalism.GaloisCohomology.scalRep W α).comp (⊤ : Subgroup Γ).subtype) ↔ L z = 0`.

Introduce `z`. Rewrite using `[ReciprocityTheory.Gal.mem_coboundaries1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Establish `hm' : ∀ g : Γ, z.1 ⟨g, trivial⟩ = (α g : O) • m - m`.

Introduce `g`. Use `hm ⟨g, trivial⟩` as an intermediate fact. Simplify `this` using `[Formalism.GaloisCohomology.scalRep]`. Establish `hmδ : ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩ = m`. Rewrite using `[hm' δ, hu', smul_smul, Units.inv_mul, one_smul]`.

Use function extensionality and compare the values at `g`. Rewrite using `[hL, hmδ, ← hm' g, Pi.zero_apply, sub_self]`. Introduce `h0`. Use `⟨((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩, fun g => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `g`.

Use `congrFun h0 g` as an intermediate fact. Rewrite `this` using `[hL, Pi.zero_apply, sub_eq_zero]`. Simplify using `[Formalism.GaloisCohomology.scalRep]`. Rewrite using `[smul_comm ((u⁻¹ : Oˣ) : O) (α g : O)]`. Conclude with `this`.

Use `⟨Submodule.liftQ _ L (fun z hz => LinearMap.mem_ker.2 ((hB z).1 hz)), ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[Submodule.liftQ_apply]`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ((hB z).2 hx)`. Simplify using `only [Submodule.liftQ_apply]`. Establish `hz` using `continuous_and_cocycle_eq_of_z1U_whole_group α z`. Use `⟨?_, ?_, ?_, ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩, fun g => hL z g⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_continuous]`.

Conclude with `hz.1.sub ((((hz.1.comp (continuous_mul_right δ)).sub hz.1).sub continuous_const).const_smul _)`. Introduce `g h`. Rewrite using `[hL, hL, hL, hz.2 g h, map_mul, Units.val_mul, mul_smul, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hL, hu', smul_smul, Units.mul_inv, one_smul, sub_self]`.
-/
private theorem shaInj_norm {O Γ W : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul O W] (α : Γ →* Oˣ) (δ : Γ) (hδ : IsUnit ((α δ : O) - 1)) :
    ∃ ν : H1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ) →ₗ[O] (Γ → W), Function.Injective ν ∧
      ∀ z : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ),
      IsLocallyConstant (ν (Submodule.Quotient.mk z)) ∧
      (∀ g h, ν (Submodule.Quotient.mk z) (g * h) =
        ν (Submodule.Quotient.mk z) g + (α g : O) • ν (Submodule.Quotient.mk z) h) ∧
      ν (Submodule.Quotient.mk z) δ = 0 ∧
      ∃ m : W, ∀ g, ν (Submodule.Quotient.mk z) g = z.1 ⟨g, trivial⟩ - ((α g : O) • m - m) := by
  obtain ⟨u, hu⟩ := hδ
  let L : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ) →ₗ[O] (Γ → W) :=
    { toFun := fun z g => z.1 ⟨g, trivial⟩ -
        ((u⁻¹ : Oˣ) : O) • (z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩ - z.1 ⟨δ, trivial⟩)
      map_add' := by
        intro a b
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, smul_sub, smul_add]
        abel
      map_smul' := by
        intro c a
        funext g
        simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]
        rw [smul_comm ((u⁻¹ : Oˣ) : O) c, smul_comm ((u⁻¹ : Oˣ) : O) c, smul_comm ((u⁻¹ : Oˣ) : O) c] }
  have hL : ∀ z g, L z g = z.1 ⟨g, trivial⟩ -
      ((α g : O) • (((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩) - ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩) := by
    intro z g
    have e : (α g : O) • z.1 ⟨δ, trivial⟩ = z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩ := by
      rw [(continuous_and_cocycle_eq_of_z1U_whole_group α z).2 g δ]
      abel
    show z.1 ⟨g, trivial⟩ - ((u⁻¹ : Oˣ) : O) • (z.1 ⟨g * δ, trivial⟩ - z.1 ⟨g, trivial⟩ - z.1 ⟨δ, trivial⟩) = _
    rw [smul_comm (α g : O), e, ← smul_sub]
  have hu' : ∀ x : W, (α δ : O) • x - x = (u : O) • x := fun x => by rw [hu, sub_smul, one_smul]
  have hB : ∀ z : Z1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ),
      z.1 ∈ ReciprocityTheory.Gal.B1 ((Formalism.GaloisCohomology.scalRep W α).comp (⊤ : Subgroup Γ).subtype) ↔ L z = 0 := by
    intro z
    rw [ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      have hm' : ∀ g : Γ, z.1 ⟨g, trivial⟩ = (α g : O) • m - m := by
        intro g
        have := hm ⟨g, trivial⟩
        simpa [Formalism.GaloisCohomology.scalRep] using this
      have hmδ : ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩ = m := by
        rw [hm' δ, hu', smul_smul, Units.inv_mul, one_smul]
      funext g
      rw [hL, hmδ, ← hm' g, Pi.zero_apply, sub_self]
    · intro h0
      refine ⟨((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩, fun g => ?_⟩
      obtain ⟨g, hg⟩ := g
      have := congrFun h0 g
      rw [hL, Pi.zero_apply, sub_eq_zero] at this
      simp [Formalism.GaloisCohomology.scalRep]
      rw [smul_comm ((u⁻¹ : Oˣ) : O) (α g : O)]
      exact this
  refine ⟨Submodule.liftQ _ L (fun z hz => LinearMap.mem_ker.2 ((hB z).1 hz)), ?_, fun z => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.liftQ_apply] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hB z).2 hx)
  · simp only [Submodule.liftQ_apply]
    have hz := continuous_and_cocycle_eq_of_z1U_whole_group α z
    refine ⟨?_, ?_, ?_, ((u⁻¹ : Oˣ) : O) • z.1 ⟨δ, trivial⟩, fun g => hL z g⟩
    · rw [IsLocallyConstant.iff_continuous]
      exact hz.1.sub ((((hz.1.comp (continuous_mul_right δ)).sub hz.1).sub continuous_const).const_smul _)
    · intro g h
      rw [hL, hL, hL, hz.2 g h, map_mul, Units.val_mul, mul_smul, smul_sub, smul_sub]
      abel
    · rw [hL, hu', smul_smul, Units.mul_inv, one_smul, sub_self]

private def shaInj_mat {C : Type} [CommRing C] (t : C) : Matrix (Fin 3) (Fin 3) C := !![0, 0, 0; t, 0, 0; 0, -t, 0]

/- English proof (translation)
Unfold `shaInj_mat`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> ring`.
-/
private theorem shaInj_mat_add {C : Type} [CommRing C] (s t : C) :
    shaInj_mat (s + t) = shaInj_mat s + shaInj_mat t := by
  unfold shaInj_mat
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/- English proof (translation)
Unfold `shaInj_mat`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> ring`.
-/
private theorem shaInj_mat_sub {C : Type} [CommRing C] (s t : C) :
    shaInj_mat (s - t) = shaInj_mat s - shaInj_mat t := by
  unfold shaInj_mat
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/- English proof (translation)
Unfold `shaInj_mat`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem shaInj_mat_zero {C : Type} [CommRing C] : shaInj_mat (0 : C) = 0 := by
  unfold shaInj_mat
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Unfold `gw`. Introduce `a b hab`. Unfold `shaInj_mat`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [wt, wt1]`.
-/
private theorem shaInj_mat_gw {C : Type} [CommRing C] (t : C) : shaInj_mat t ∈ gw C (-1) := by
  unfold gw
  intro a b hab
  unfold shaInj_mat
  fin_cases a <;> fin_cases b <;> simp_all [wt, wt1]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[adRep_baseLift_apply]`. Unfold `shaInj_mat`. Apply the tactic sequence `by_cases hη : η g = 1 <;> fin_cases a <;> fin_cases b <;> simp [hη, wt, wt1]`.
-/
private theorem shaInj_ad {Γ C : Type} [Group Γ] [CommRing C] (η : Γ →* ℤˣ) (Ψ : Γ →* Cˣ) (g : Γ) (t : C) :
    adRep (r0 η Ψ) g (shaInj_mat t) = shaInj_mat ((((Ψ g)⁻¹ : Cˣ) : C) * t) := by
  ext a b
  rw [adRep_baseLift_apply]
  unfold shaInj_mat
  by_cases hη : η g = 1 <;> fin_cases a <;> fin_cases b <;> simp [hη, wt, wt1]

/- English proof (translation)
Use extensionality with `g i j`. Unfold `GG.map r0`. Simplify using `[tor_val, Matrix.diagonal_apply]`. Use `split_ifs`. Rewrite using `[← map_zpow (Units.map (f : O →* C)) (Ψ g), Units.coe_map]`.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Unfold `GG.map r0`. Simplify using the standard rewrite rules.
-/
private theorem shaInj_map {Γ O C : Type} [Group Γ] [CommRing O] [CommRing C] (f : O →+* C) (η : Γ →* ℤˣ)
    (Ψ : Γ →* Oˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g i j
  · unfold GG.map r0
    simp [tor_val, Matrix.diagonal_apply]
    split_ifs
    · rw [← map_zpow (Units.map (f : O →* C)) (Ψ g), Units.coe_map]
      rfl
    · simp
  · unfold GG.map r0
    simp

/- English proof (translation)
Establish `hρ` using `shaInj_map (Ideal.Quotient.mk (Ideal.span {a})) η Ψ`. Establish `hU : ∀ g : Γ, ((((Units.map (Ideal.Quotient.mk (Ideal.span {a})).toMonoidHom).comp Ψ g)⁻¹ : (O ⧸ Ideal.span {a})ˣ) : O ⧸ Ideal.span {a}) = Ideal.Quotient.mk _ (((Ψ g)⁻¹ : Oˣ) : O)`. Introduce `g`. Simplify using `[map_inv]`. Establish `had : ∀ (g : Γ) (x : O ⧸ Ideal.span {a}), adRep ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) g (shaInj_mat x) = shaInj_mat (Ideal.Quotient.mk _ (((Ψ g)⁻¹ : Oˣ) : O) * x)`.

Introduce `g x`. Rewrite using `[hρ, shaInj_ad, hU]`. Establish `hz : shaInj_mat (0 : O ⧸ Ideal.span {a}) = 0` using `shaInj_mat_zero`. Unfold `shaCoc`. Use `⟨hl.comp shaInj_mat, fun g => shaInj_mat_gw _, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsCoc`. Introduce `g h`. Use `beta_reduce`. Rewrite using `[had, hc, shaInj_mat_add]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[h0, hz]`. Unfold `zvar beta_reduce`. Rewrite using `[h1, h2, hz]`. Simplify using the standard rewrite rules.

Unfold `zvar beta_reduce`. Rewrite using `[h1, h2, hz]`. Simplify using the standard rewrite rules. Introduce `g hg beta_reduce`. Rewrite using `[hN g hg, hz]`.

Take `⟨s, hs⟩` from `hι`. Use `⟨shaInj_mat s, shaInj_mat_gw _, fun h => ?_⟩` and prove the remaining obligations. Unfold `cob`. Use `beta_reduce`. Rewrite using `[had, hs h, shaInj_mat_sub]`.
-/
private theorem shaInj_mem {O Γ H : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ]
    [Group H] [TopologicalSpace H] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (N : Set Γ) (ι : H →* Γ) (c g₁ : Γ) (a : O)
    (t : Γ → O ⧸ Ideal.span {a}) (hl : IsLocallyConstant t)
    (hc : ∀ g h, t (g * h) = t g + Ideal.Quotient.mk _ (((Ψ g)⁻¹ : Oˣ) : O) * t h)
    (h0 : t c = 0) (h1 : t g₁ = 0) (h2 : t (gstar c g₁) = 0) (hN : ∀ g ∈ N, t g = 0)
    (hι : ∃ s, ∀ h, t (ι h) = s - Ideal.Quotient.mk _ (((Ψ (ι h))⁻¹ : Oˣ) : O) * s) :
    (fun g => shaInj_mat (t g)) ∈ shaCoc η Ψ N ι c g₁ a := by
  have hρ := shaInj_map (Ideal.Quotient.mk (Ideal.span {a})) η Ψ
  have hU : ∀ g : Γ, ((((Units.map (Ideal.Quotient.mk (Ideal.span {a})).toMonoidHom).comp Ψ g)⁻¹ :
      (O ⧸ Ideal.span {a})ˣ) : O ⧸ Ideal.span {a}) = Ideal.Quotient.mk _ (((Ψ g)⁻¹ : Oˣ) : O) := by
    intro g
    simp [map_inv]
  have had : ∀ (g : Γ) (x : O ⧸ Ideal.span {a}),
      adRep ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) g (shaInj_mat x) =
        shaInj_mat (Ideal.Quotient.mk _ (((Ψ g)⁻¹ : Oˣ) : O) * x) := by
    intro g x
    rw [hρ, shaInj_ad, hU]
  have hz : shaInj_mat (0 : O ⧸ Ideal.span {a}) = 0 := shaInj_mat_zero
  unfold shaCoc
  refine ⟨hl.comp shaInj_mat, fun g => shaInj_mat_gw _, ?_, ?_, ?_, ?_⟩
  · unfold IsCoc
    intro g h
    beta_reduce
    rw [had, hc, shaInj_mat_add]
  · refine ⟨?_, ?_, ?_⟩
    · beta_reduce
      rw [h0, hz]
    · unfold zvar
      beta_reduce
      rw [h1, h2, hz]
      simp
    · unfold zvar
      beta_reduce
      rw [h1, h2, hz]
      simp
  · intro g hg
    beta_reduce
    rw [hN g hg, hz]
  · obtain ⟨s, hs⟩ := hι
    refine ⟨shaInj_mat s, shaInj_mat_gw _, fun h => ?_⟩
    unfold cob
    beta_reduce
    rw [had, hs h, shaInj_mat_sub]

/- English proof (translation)
Establish `h1 : IsUnit ((x : O) - 1)` using `isUnit_of_mul_isUnit_left (by rwa [show ((x : O) - 1) * ((x : O) + 1) = (x : O) ^ 2 - 1 by ring])`. Establish `e : ((x⁻¹ : Oˣ) : O) - 1 = ((-x⁻¹ : Oˣ) : O) * ((x : O) - 1)`. Rewrite using `[Units.val_neg, neg_mul, mul_sub, Units.inv_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `(Units.isUnit _).mul h1`.
-/
private theorem shaInj_unit {O : Type} [CommRing O] (x : Oˣ) (h : IsUnit ((x : O) ^ 2 - 1)) :
    IsUnit (((x⁻¹ : Oˣ) : O) - 1) := by
  have h1 : IsUnit ((x : O) - 1) :=
    isUnit_of_mul_isUnit_left (by rwa [show ((x : O) - 1) * ((x : O) + 1) = (x : O) ^ 2 - 1 by ring])
  have e : ((x⁻¹ : Oˣ) : O) - 1 = ((-x⁻¹ : Oˣ) : O) * ((x : O) - 1) := by
    rw [Units.val_neg, neg_mul, mul_sub, Units.inv_mul]
    ring
  rw [e]
  exact (Units.isUnit _).mul h1

/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Establish `h' : (x - 1) • m = 0` using `by rw [sub_smul, one_smul]; exact h`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem shaInj_kill {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] {x : O} (hx : IsUnit (x - 1))
    {m : W} (h : x • m - m = 0) : m = 0 := by
  obtain ⟨u, hu⟩ := hx
  have h' : (x - 1) • m = 0 := by rw [sub_smul, one_smul]; exact h
  calc m = (((u⁻¹ : Oˣ) : O) * (x - 1)) • m := by rw [← hu, Units.inv_mul, one_smul]
    _ = 0 := by rw [mul_smul, h', smul_zero]

/- English proof (translation)
Take `⟨ν, hνi, hν⟩` from `shaInj_norm (W := W) α δ hδ`. Use `⟨ν, hνi, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨h1, h2, h3, m0, h4⟩` from `hν z`. Use `⟨h1, h2, h3, fun D hD => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩` from `UpperTheory.V.Base.mk_mem_locSel.1 hx D hD`. Use `⟨m - m0, fun g hg => ?_⟩` and prove the remaining obligations. Use `hm ⟨g, trivial⟩ hg` as an intermediate fact. Simplify using `[Formalism.GaloisCohomology.scalRep] at this`. Rewrite using `[h4, this, smul_sub]`.

Normalize the expressions using the abelian group laws.
-/
private theorem shaInj_sel {O Γ W : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul O W] (α : Γ →* Oˣ) (δ : Γ) (hδ : IsUnit ((α δ : O) - 1)) (𝒟 : Set (Subgroup Γ)) :
    ∃ ν : H1U (Formalism.GaloisCohomology.scalRep W α) (⊤ : Subgroup Γ) →ₗ[O] (Γ → W), Function.Injective ν ∧
      ∀ x ∈ LocSel (Formalism.GaloisCohomology.scalRep W α) ⊤ 𝒟, IsLocallyConstant (ν x) ∧
        (∀ g h, ν x (g * h) = ν x g + (α g : O) • ν x h) ∧ ν x δ = 0 ∧
        ∀ D ∈ 𝒟, ∃ m : W, ∀ g ∈ D, ν x g = (α g : O) • m - m := by
  obtain ⟨ν, hνi, hν⟩ := shaInj_norm (W := W) α δ hδ
  refine ⟨ν, hνi, fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨h1, h2, h3, m0, h4⟩ := hν z
  refine ⟨h1, h2, h3, fun D hD => ?_⟩
  obtain ⟨m, hm⟩ := UpperTheory.V.Base.mk_mem_locSel.1 hx D hD
  refine ⟨m - m0, fun g hg => ?_⟩
  have := hm ⟨g, trivial⟩ hg
  simp [Formalism.GaloisCohomology.scalRep] at this
  rw [h4, this, smul_sub]
  abel

/- English proof (translation)
Take `⟨φ, hφ⟩` from `shaInj_phi b w hw`. Establish `hcancel : ∀ (u : Oˣ) (m : W), (u : O) • m = 0 → m = 0`. Introduce `u m h`. Combine the equalities or inequalities in the displayed calculation. Establish `hφ0 : φ 0 = 0` using `by rw [← zero_smul O w, hφ, map_zero]`.

Establish `hφadd : ∀ u v : W, b • u = 0 → b • v = 0 → ∀ y : O, φ (u + y • v) = φ u + Ideal.Quotient.mk _ y * φ v`. Introduce `u v hu hv y`. Take `⟨yu, rfl⟩` from `hgen u hu`. Take `⟨yv, rfl⟩` from `hgen v hv`. Rewrite using `[smul_smul, ← add_smul, hφ, hφ, hφ, map_add, map_mul]`.

Establish `hφinj : ∀ u : W, b • u = 0 → φ u = 0 → u = 0`. Introduce `u hu h`. Take `⟨y, rfl⟩` from `hgen u hu`. Rewrite `h` using `[hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `(hw y).mpr h`.

Establish `htor : ∀ x : Submodule.torsionBy O S b, ∀ g, b • ν ((x : S) : X) g = 0`. Introduce `x g`. Establish `hx : b • (x : S) = 0` using `(Submodule.mem_torsionBy_iff _ _).mp x.2`. Establish `hx' : b • ((x : S) : X) = 0` using `congrArg Subtype.val hx`. Rewrite using `[← Pi.smul_apply, ← map_smul, hx', map_zero, Pi.zero_apply]`.

Use `⟨{ toFun := fun x g => shaInj_mat (φ (ν ((x : S) : X) g)), map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `[hφ0, shaInj_mat_zero]`. Introduce `x y`. Use function extensionality and compare the values at `g`.

Establish `e` using `hφadd _ _ (htor x g) (htor y g) 1`. Rewrite `e` using `[one_smul, map_one, one_mul]`. Simplify using `only [Submodule.coe_add, map_add, Pi.add_apply]`. Rewrite using `[e, shaInj_mat_add]`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `ht : ∀ g, ν ((x : S) : X) g = 0`. Introduce `g`. Establish `e` using `congrFun (congrFun (congrFun hx g) 1) 0`. Express the relevant statement in the definitionally equal form `shaInj_mat (φ (ν ((x : S) : X) g)) 1 0 = 0 at e`.

Unfold `shaInj_mat at e`. Simplify using `at e`. Conclude with `hφinj _ (htor x g) e`. Establish `hv : ((x : S) : X) = 0`. Apply `hνi` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `g`. Conclude with `ht g`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hv`. Introduce `x`. Take `⟨hlc, hcoc, hg1, hloc⟩` from `hν ((x : S) : X) (x : S).2`. Establish `hb'` using `htor x`. Establish `hone : ν ((x : S) : X) 1 = 0` using `by simpa using hcoc 1 1`.

Establish `hinv : ∀ g, ν ((x : S) : X) g = 0 → ν ((x : S) : X) g⁻¹ = 0`. Introduce `g hg`. Establish `e` using `hcoc g g⁻¹`. Rewrite `e` using `[mul_inv_cancel, hone, hg, zero_add]`. Conclude with `hcancel (α g) _ e.symm`.

Establish `hc0 : ν ((x : S) : X) c = 0`. Establish `e` using `hcoc c c`. Rewrite `e` using `[hM.csq, hone, hαΨ, hM.Ψc, inv_one, Units.val_one, one_smul]`. Take `⟨u, hu⟩` from `h2`. Apply `hcancel u` to reduce the goal to its premises.

Rewrite using `[hu, two_smul]`. Conclude with `e.symm`. Establish `hN0 : ∀ g, r0 η Ψ g = 1 → Ψ g = 1`. Introduce `g h`. Unfold `r0 at h`.

Establish `h1` using `congrArg SemidirectProduct.left h`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk, SemidirectProduct.one_left] at h1`. Establish `h2` using `congrArg (fun M : GL (Fin 3) O => (M : Matrix (Fin 3) (Fin 3) O) 0 0) h1`. Simplify `h2` using `[tor_val, wt1]`. Apply `shaInj_mem η Ψ N ι c g₁ b (fun g => φ (ν ((x : S) : X) g)) (hlc.comp φ)` to reduce the goal to its premises.

Introduce `g h`. Rewrite using `[hcoc g h, hαΨ g]`. Conclude with `hφadd _ _ (hb' g) (hb' h) _`. Rewrite using `[hc0, hφ0]`. Rewrite using `[hg1, hφ0]`.

Establish `e1` using `hcoc c g₁⁻¹`. Rewrite `e1` using `[hc0, hinv g₁ hg1, smul_zero, add_zero]`. Establish `e2` using `hcoc (c * g₁⁻¹) c`. Rewrite `e2` using `[hc0, smul_zero, add_zero, e1]`. Unfold `gstar`.

Rewrite using `[e2, hφ0]`. Introduce `g hg`. Take `⟨D, hD', hgD⟩` from `hK g hg`. Take `⟨m, hm⟩` from `hloc D hD'`. Rewrite using `[hm g hgD, hαΨ, hN0 g (hK0 g hg), inv_one, Units.val_one, one_smul, sub_self, hφ0]`.

Take `⟨m, hm⟩` from `hloc ι.range hD`. Establish `hbm : b • m = 0`. Establish `e` using `hb' (ι s')`. Rewrite `e` using `[hm _ (MonoidHom.mem_range.mpr ⟨s', rfl⟩), smul_sub, smul_comm b]`. Establish `hu` using `shaInj_unit (Ψ (ι s')) hsu`.

Rewrite `hu` using `[← hαΨ]`. Conclude with `shaInj_kill hu e`. Take `⟨y, rfl⟩` from `hgen m hbm`. Use `⟨Ideal.Quotient.mk _ (-y), fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hm _ (MonoidHom.mem_range.mpr ⟨h, rfl⟩), hαΨ, smul_smul, ← sub_smul, hφ, map_sub, map_mul, map_neg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem shaInj_gen {O Γ H W X : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ]
    [Group H] [TopologicalSpace H]
    [AddCommGroup W] [Module O W] [AddCommGroup X] [Module O X]
    (η : Γ →* ℤˣ) (Ψ α : Γ →* Oˣ) (N : Set Γ) (ι : H →* Γ) (c g₁ : Γ) (b : O)
    (𝒟 : Set (Subgroup Γ)) (hαΨ : ∀ g, α g = (Ψ g)⁻¹) (hM : Marks η Ψ c g₁) (h2 : IsUnit (2 : O))
    (w : W) (hw : ∀ y : O, y • w = 0 ↔ b ∣ y) (hgen : ∀ w' : W, b • w' = 0 → ∃ y : O, w' = y • w)
    (hK0 : ∀ g ∈ N, r0 η Ψ g = 1) (hK : ∀ g ∈ N, ∃ D ∈ 𝒟, g ∈ D) (hD : ι.range ∈ 𝒟)
    (s' : H) (hsu : IsUnit ((Ψ (ι s') : O) ^ 2 - 1)) (S : Submodule O X) (ν : X →ₗ[O] (Γ → W))
    (hνi : Function.Injective ν)
    (hν : ∀ x ∈ S, IsLocallyConstant (ν x) ∧ (∀ g h, ν x (g * h) = ν x g + (α g : O) • ν x h) ∧ ν x g₁ = 0 ∧
      ∀ D ∈ 𝒟, ∃ m : W, ∀ g ∈ D, ν x g = (α g : O) • m - m) :
    ∃ γ : Submodule.torsionBy O S b →+ (Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {b})),
      Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc η Ψ N ι c g₁ b := by
  obtain ⟨φ, hφ⟩ := shaInj_phi b w hw
  have hcancel : ∀ (u : Oˣ) (m : W), (u : O) • m = 0 → m = 0 := by
    intro u m h
    calc m = (((u⁻¹ : Oˣ) : O) * (u : O)) • m := by rw [Units.inv_mul, one_smul]
      _ = 0 := by rw [mul_smul, h, smul_zero]
  have hφ0 : φ 0 = 0 := by rw [← zero_smul O w, hφ, map_zero]
  have hφadd : ∀ u v : W, b • u = 0 → b • v = 0 → ∀ y : O,
      φ (u + y • v) = φ u + Ideal.Quotient.mk _ y * φ v := by
    intro u v hu hv y
    obtain ⟨yu, rfl⟩ := hgen u hu
    obtain ⟨yv, rfl⟩ := hgen v hv
    rw [smul_smul, ← add_smul, hφ, hφ, hφ, map_add, map_mul]
  have hφinj : ∀ u : W, b • u = 0 → φ u = 0 → u = 0 := by
    intro u hu h
    obtain ⟨y, rfl⟩ := hgen u hu
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    exact (hw y).mpr h
  have htor : ∀ x : Submodule.torsionBy O S b, ∀ g, b • ν ((x : S) : X) g = 0 := by
    intro x g
    have hx : b • (x : S) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    have hx' : b • ((x : S) : X) = 0 := congrArg Subtype.val hx
    rw [← Pi.smul_apply, ← map_smul, hx', map_zero, Pi.zero_apply]
  refine ⟨{ toFun := fun x g => shaInj_mat (φ (ν ((x : S) : X) g)), map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · funext g
    simp [hφ0, shaInj_mat_zero]
  · intro x y
    funext g
    have e := hφadd _ _ (htor x g) (htor y g) 1
    rw [one_smul, map_one, one_mul] at e
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
    rw [e, shaInj_mat_add]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have ht : ∀ g, ν ((x : S) : X) g = 0 := by
      intro g
      have e := congrFun (congrFun (congrFun hx g) 1) 0
      change shaInj_mat (φ (ν ((x : S) : X) g)) 1 0 = 0 at e
      unfold shaInj_mat at e
      simp at e
      exact hφinj _ (htor x g) e
    have hv : ((x : S) : X) = 0 := by
      apply hνi
      rw [map_zero]
      funext g
      exact ht g
    apply Subtype.ext
    apply Subtype.ext
    simpa using hv
  · intro x
    obtain ⟨hlc, hcoc, hg1, hloc⟩ := hν ((x : S) : X) (x : S).2
    have hb' := htor x
    have hone : ν ((x : S) : X) 1 = 0 := by simpa using hcoc 1 1
    have hinv : ∀ g, ν ((x : S) : X) g = 0 → ν ((x : S) : X) g⁻¹ = 0 := by
      intro g hg
      have e := hcoc g g⁻¹
      rw [mul_inv_cancel, hone, hg, zero_add] at e
      exact hcancel (α g) _ e.symm
    have hc0 : ν ((x : S) : X) c = 0 := by
      have e := hcoc c c
      rw [hM.csq, hone, hαΨ, hM.Ψc, inv_one, Units.val_one, one_smul] at e
      obtain ⟨u, hu⟩ := h2
      apply hcancel u
      rw [hu, two_smul]
      exact e.symm
    have hN0 : ∀ g, r0 η Ψ g = 1 → Ψ g = 1 := by
      intro g h
      unfold r0 at h
      have h1 := congrArg SemidirectProduct.left h
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, SemidirectProduct.one_left] at h1
      have h2 := congrArg (fun M : GL (Fin 3) O => (M : Matrix (Fin 3) (Fin 3) O) 0 0) h1
      simpa [tor_val, wt1] using h2
    apply shaInj_mem η Ψ N ι c g₁ b (fun g => φ (ν ((x : S) : X) g)) (hlc.comp φ)
    · intro g h
      rw [hcoc g h, hαΨ g]
      exact hφadd _ _ (hb' g) (hb' h) _
    · rw [hc0, hφ0]
    · rw [hg1, hφ0]
    · have e1 := hcoc c g₁⁻¹
      rw [hc0, hinv g₁ hg1, smul_zero, add_zero] at e1
      have e2 := hcoc (c * g₁⁻¹) c
      rw [hc0, smul_zero, add_zero, e1] at e2
      unfold gstar
      rw [e2, hφ0]
    · intro g hg
      obtain ⟨D, hD', hgD⟩ := hK g hg
      obtain ⟨m, hm⟩ := hloc D hD'
      rw [hm g hgD, hαΨ, hN0 g (hK0 g hg), inv_one, Units.val_one, one_smul, sub_self, hφ0]
    · obtain ⟨m, hm⟩ := hloc ι.range hD
      have hbm : b • m = 0 := by
        have e := hb' (ι s')
        rw [hm _ (MonoidHom.mem_range.mpr ⟨s', rfl⟩), smul_sub, smul_comm b] at e
        have hu := shaInj_unit (Ψ (ι s')) hsu
        rw [← hαΨ] at hu
        exact shaInj_kill hu e
      obtain ⟨y, rfl⟩ := hgen m hbm
      refine ⟨Ideal.Quotient.mk _ (-y), fun h => ?_⟩
      rw [hm _ (MonoidHom.mem_range.mpr ⟨h, rfl⟩), hαΨ, smul_smul, ← sub_smul, hφ, map_sub, map_mul, map_neg]
      ring

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hq` using `ML.qoCyc l O`. Establish `hw2 : ∀ a : O, a ≠ 0 → ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y` using `hq.2.1`. Establish `hw3 : ∀ (a : O) (w : QO l O), a ≠ 0 → (∀ y : O, y • w = 0 ↔ a ∣ y) → ∀ w' : QO l O, a • w' = 0 → ∃ y : O, w' = y • w` using `hq.2.2.1`. Take `⟨w, hw⟩` from `hw2 b hb`. Establish `hgen` using `hw3 b w hb hw`.

Establish `hαΨ : ∀ g, (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g = (Chr.Psi l e θ g)⁻¹`. Introduce `g`. Rewrite using `[← MonoidHom.inv_apply, Chr.Psi_inv]`. Establish `hδ : IsUnit ((((θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g₁ : Oˣ) : O) - 1)`. Rewrite using `[hαΨ]`.

Conclude with `shaInj_unit _ hM.Ψg`. Take `⟨ν, hνi, hν⟩` from `shaInj_sel (W := QO l O) (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g₁ hδ (shaFam ℚ Ω n)`. Conclude with `shaInj_gen η (Chr.Psi l e θ) (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) N ι c g₁ b (shaFam ℚ Ω n) hαΨ hM h2 w hw hgen hK0 hK hD s' hsu (ShaU (Chr.rho l e θ) n ⊤) ν hνi hν`.
-/
theorem UpperTheory.V.U3.sha_inj_gen {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] {H : Type} [Group H]
    [TopologicalSpace H] (e n : ℕ) (θ : G ℚ Ω →* Oˣ) (η : G ℚ Ω →* ℤˣ) (N : Set (G ℚ Ω)) (ι : H →* G ℚ Ω)
    (c g₁ : G ℚ Ω) (b : O) (hb : b ≠ 0) (hM : Marks η (Chr.Psi l e θ) c g₁) (h2 : IsUnit (2 : O))
    (hK0 : ∀ g ∈ N, r0 η (Chr.Psi l e θ) g = 1) (hK : ∀ g ∈ N, ∃ D ∈ shaFam ℚ Ω n, g ∈ D)
    (hD : ι.range ∈ shaFam ℚ Ω n) (s' : H) (hsu : IsUnit ((Chr.Psi l e θ (ι s') : O) ^ 2 - 1)) :
    ∃ γ : Submodule.torsionBy O (ShaU (Chr.rho l e θ) n ⊤) b →+
        (G ℚ Ω → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {b})),
      Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc η (Chr.Psi l e θ) N ι c g₁ b := by
  have hq := ML.qoCyc l O
  have hw2 : ∀ a : O, a ≠ 0 → ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y := hq.2.1
  have hw3 : ∀ (a : O) (w : QO l O), a ≠ 0 → (∀ y : O, y • w = 0 ↔ a ∣ y) →
      ∀ w' : QO l O, a • w' = 0 → ∃ y : O, w' = y • w := hq.2.2.1
  obtain ⟨w, hw⟩ := hw2 b hb
  have hgen := hw3 b w hb hw
  have hαΨ : ∀ g, (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g = (Chr.Psi l e θ g)⁻¹ := by
    intro g
    rw [← MonoidHom.inv_apply, Chr.Psi_inv]
  have hδ : IsUnit ((((θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g₁ : Oˣ) : O) - 1) := by
    rw [hαΨ]
    exact shaInj_unit _ hM.Ψg
  obtain ⟨ν, hνi, hν⟩ := shaInj_sel (W := QO l O) (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) g₁ hδ (shaFam ℚ Ω n)
  exact shaInj_gen η (Chr.Psi l e θ) (θ⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ))) N ι c g₁ b (shaFam ℚ Ω n) hαΨ hM h2
    w hw hgen hK0 hK hD s' hsu (ShaU (Chr.rho l e θ) n ⊤) ν hνi hν
