import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAutI
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
/- English proof (translation)
Simplify using `[conjBy, hg]`.
-/
private theorem conj_left_block_of_right_one {Γ R : Type} [Group Γ] [CommRing R] (M : GL (Fin 3) R) (r : Γ →* GG 3 R) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).left = M * (r g).left * M⁻¹ := by
  simp [conjBy, hg]
/- English proof (translation)
Establish `h1 : (r c).left = 1` using `Units.ext hc`. Establish `h2 : theta (1 : GL (Fin 3) R) = 1` using `map_one (thetaAut 3 R)`. Simplify using `[h1, hc', hg, h2]`.
-/
private theorem conj_left_block_eq_theta {Γ R : Type} [Group Γ] [CommRing R] (r : Γ →* GG 3 R) (c g : Γ)
    (hc : (r c).mat = 1) (hc' : (r c).right = -1) (hg : (r g).right = 1) : (r (c⁻¹ * g * c)).left = theta (r g).left := by
  have h1 : (r c).left = 1 := Units.ext hc
  have h2 : theta (1 : GL (Fin 3) R) = 1 := map_one (thetaAut 3 R)
  simp [h1, hc', hg, h2]
/- English proof (translation)
Establish `hm : ∀ i, ∀ s ∈ H, ∀ t ∈ H, (M * ρ (s * t) * M⁻¹ : GL (Fin n) k) i i = (M * ρ s * M⁻¹ : GL (Fin n) k) i i * (M * ρ t * M⁻¹ : GL (Fin n) k) i i`. Introduce `i s hs t ht`. Establish `e : M * ρ (s * t) * M⁻¹ = (M * ρ s * M⁻¹) * (M * ρ t * M⁻¹)` using `by simp [mul_assoc]`. Rewrite using `[e, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `j _ hj`.

Break down `lt_or_gt_of_ne hj with h1 | h1` into its components or cases. Rewrite using `[h s hs i j h1, zero_mul]`. Rewrite using `[h t ht j i h1, mul_zero]`. Simplify using the standard rewrite rules. Set `κ : Fin n → ↥H →* k` to `fun i => { toFun := fun s => (M * ρ s * M⁻¹ : GL (Fin n) k) i i map_one' := by simp map_mul' := fun s t => hm i s s.2 t t.2 }`.

Conclude with `⟨fun i => (κ i).toHomUnits, ⟨M, fun s => ⟨h s s.2, fun i => rfl⟩⟩, fun i s => rfl⟩`.
-/
private theorem exists_flag_characters_of_upper_triangular {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (H : Subgroup Γ) (M : GL (Fin n) k)
    (h : ∀ s ∈ H, ∀ i j, j < i → (M * ρ s * M⁻¹ : GL (Fin n) k) i j = 0) :
    ∃ κ : Fin n → ↥H →* kˣ, Af.IsFlagOn ρ H κ ∧ ∀ i (s : ↥H), (κ i s : k) = (M * ρ s * M⁻¹ : GL (Fin n) k) i i := by
  have hm : ∀ i, ∀ s ∈ H, ∀ t ∈ H, (M * ρ (s * t) * M⁻¹ : GL (Fin n) k) i i =
      (M * ρ s * M⁻¹ : GL (Fin n) k) i i * (M * ρ t * M⁻¹ : GL (Fin n) k) i i := by
    intro i s hs t ht
    have e : M * ρ (s * t) * M⁻¹ = (M * ρ s * M⁻¹) * (M * ρ t * M⁻¹) := by simp [mul_assoc]
    rw [e, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h1 | h1
      · rw [h s hs i j h1, zero_mul]
      · rw [h t ht j i h1, mul_zero]
    · simp
  let κ : Fin n → ↥H →* k := fun i =>
    { toFun := fun s => (M * ρ s * M⁻¹ : GL (Fin n) k) i i
      map_one' := by simp
      map_mul' := fun s t => hm i s s.2 t t.2 }
  exact ⟨fun i => (κ i).toHomUnits, ⟨M, fun s => ⟨h s s.2, fun i => rfl⟩⟩, fun i s => rfl⟩
/- English proof (translation)
Use `haveI := E.2`. Use `haveI : IsModuleTopology ℚ_[l] ↥E.1 := isModuleTopologyOfFiniteDimensional`. Use `haveI : IsModuleTopology ℚ_[l] (Fin 3 → ↥E.1) := isModuleTopologyOfFiniteDimensional`. Establish `h0 : Loc.IsCr φ (Loc.chRep (1 : H →* (↥E.1)ˣ))` using `Loc.crUnr φ hφ _ (by`. Establish `: ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2` using `fun p => by simp [Loc.chRep]`.

Conclude with `continuous_snd.congr fun p => (this p).symm) 0 fun g _ x => by simp [Loc.chRep]`. Establish `hc : ∀ σ : H →* GL (Fin 3) ↥E.1, Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) ↥E.1)) → ContAction (Loc.colRep σ)` using `fun σ hσ => (hσ.comp continuous_fst).matrix_mulVec continuous_snd`. Set `b : (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] ↥E.1` to `LinearMap.mk₂ ℚ_[l] (fun w x => (Jmat _ 3 *ᵥ w) ⬝ᵥ x) (fun _ _ _ => by simp [Matrix.mulVec_add]) (fun _ _ _ => by simp [Matrix.mulVec_smul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp)`. Use `(Loc.isCrys_isDR_internalHom φ hφ (Loc.colRep ρ) (Loc.chRep (1 : H →* (↥E.1)ˣ)) _ (hc ρ (Units.continuous_val.comp hρ)) ?_ (hc _ ?_) b (fun g w x => ?_) ?_).1 h h0` and prove the remaining obligations. Establish `: ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2` using `fun p => by simp [Loc.chRep]`.

Conclude with `continuous_snd.congr fun p => (this p).symm`. Conclude with `(continuous_const.matrix_mul (Units.continuous_coe_inv.comp hρ).matrix_transpose).matrix_mul continuous_const`. Express the relevant statement in the definitionally equal form `(Jmat _ 3 *ᵥ ((theta (ρ g) : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ w)) ⬝ᵥ ((ρ g : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ x) = (1 : ↥E.1) • ((Jmat _ 3 *ᵥ w) ⬝ᵥ x)`. Rewrite using `[one_smul, theta_val, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `w hw`. Establish `h1 : Jmat _ 3 *ᵥ w = 0` using `dotProduct_eq_zero _ fun x => LinearMap.congr_fun hw x`. Establish `h2` using `congrArg (Jmat _ 3 *ᵥ ·) h1`. Simplify `h2` using `[Matrix.mulVec_mulVec, Jmat_mul_Jmat]`.
-/
private theorem crystalline_of_theta_twist_gl3 {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* GQ l) (hφ : Topology.IsOpenEmbedding φ) (E : FinExt l) (ρ : H →* GL (Fin 3) ↥E.1) (hρ : Continuous ρ)
    (h : Loc.IsCr φ (Loc.colRep ρ)) :
    Loc.IsCr φ (Loc.colRep ((thetaAut 3 ↥E.1).toMonoidHom.comp ρ)) := by
  haveI := E.2
  haveI : IsModuleTopology ℚ_[l] ↥E.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] (Fin 3 → ↥E.1) := isModuleTopologyOfFiniteDimensional
  have h0 : Loc.IsCr φ (Loc.chRep (1 : H →* (↥E.1)ˣ)) :=
    Loc.crUnr φ hφ _ (by
      have : ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2 := fun p => by simp [Loc.chRep]
      exact continuous_snd.congr fun p => (this p).symm) 0 fun g _ x => by simp [Loc.chRep]
  have hc : ∀ σ : H →* GL (Fin 3) ↥E.1, Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) ↥E.1)) →
      ContAction (Loc.colRep σ) := fun σ hσ =>
    (hσ.comp continuous_fst).matrix_mulVec continuous_snd
  let b : (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] ↥E.1 :=
    LinearMap.mk₂ ℚ_[l] (fun w x => (Jmat _ 3 *ᵥ w) ⬝ᵥ x) (fun _ _ _ => by simp [Matrix.mulVec_add])
      (fun _ _ _ => by simp [Matrix.mulVec_smul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  refine (Loc.isCrys_isDR_internalHom φ hφ (Loc.colRep ρ) (Loc.chRep (1 : H →* (↥E.1)ˣ)) _ (hc ρ (Units.continuous_val.comp hρ)) ?_
    (hc _ ?_) b (fun g w x => ?_) ?_).1 h h0
  · have : ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2 := fun p => by simp [Loc.chRep]
    exact continuous_snd.congr fun p => (this p).symm
  · exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp hρ).matrix_transpose).matrix_mul continuous_const
  · change (Jmat _ 3 *ᵥ ((theta (ρ g) : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ w)) ⬝ᵥ ((ρ g : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ x) = (1 : ↥E.1) • ((Jmat _ 3 *ᵥ w) ⬝ᵥ x)
    rw [one_smul, theta_val, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec]
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : Jmat _ 3 *ᵥ w = 0 := dotProduct_eq_zero _ fun x => LinearMap.congr_fun hw x
    have h2 := congrArg (Jmat _ 3 *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, Jmat_mul_Jmat] using h2
/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]⟩`.
-/
private theorem continuous_of_matrix_units {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing k] [TopologicalSpace k]
    {n : ℕ} (ρ : Γ →* GL (Fin n) k) (h : Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) k)) : Continuous ρ :=
  Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]⟩
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
  {U : D.ULoc} {g₁ : G ℚ Ω} {r : G ℚ Ω →* GG 3 (PadicAlgCl l)}
/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`.
-/
private theorem isAlgClosure_of_number_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
/- English proof (translation)
Use `haveI := isAlgClosure_of_number_field Ω K`. Conclude with `continuous_of_matrix_units _ (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)`.
-/
private theorem continuous_rho_of_point (h : D.IsPt U g₁ r) : Continuous (D.rhoK r h.mult) := by
  haveI := isAlgClosure_of_number_field Ω K
  exact continuous_of_matrix_units _ (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)
/- English proof (translation)
Take `⟨f, hf, hker, hpush⟩` from `h.loc`. Use `haveI : IsLocalRing c.O := c.dvr.toIsLocalRing`. Use `haveI := (dvrFacts l c.O).2.2.2.1`. Take `⟨E, hE⟩` from `Loc.ptFin (l := l) U.R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf`. Establish `hE' : ∀ a, f a ∈ E.1` using `fun a => (hE a).1`.

Use `haveI := E.2`. Use `letI : Algebra c.O ↥E.1 := ((algebraMap c.O (PadicAlgCl l)).codRestrict E.1 fun a => f.commutes a ▸ hE' _).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] c.O ↥E.1 := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl`. Set `f' : U.R →ₐ[c.O] ↥E.1` to `{ (f : U.R →+* PadicAlgCl l).codRestrict E.1 hE' with commutes' := fun a => Subtype.ext (f.commutes a) }`. Take `⟨-, -, ρ, h1, h2⟩` from `Loc.rtPoints hI.loc D.loc U ↥E.1 (push f' U.r.hom) ⟨f', rfl, fun a ha => Subtype.ext (hker ha)⟩`.

Use `⟨E, ρ, fun g => ?_, h2⟩` and prove the remaining obligations. Rewrite using `[h1, ← MonoidHom.comp_apply r D.ι, ← hpush]`. Both sides reduce to the same expression.
-/
private theorem exists_local_crystalline_gl3_model (hI : CohInp) (h : D.IsPt U g₁ r) :
    ∃ (E : FinExt l) (ρ : ↥D.loc.HL →* GL (Fin 3) ↥E.1),
      (∀ g, GeneralLinearGroup.map (E.1.val : ↥E.1 →+* PadicAlgCl l) (ρ g) = (r (D.ι g)).left) ∧
      Loc.IsCr D.loc.HL.subtype (Loc.colRep ρ) := by
  obtain ⟨f, hf, hker, hpush⟩ := h.loc
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (dvrFacts l c.O).2.2.2.1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) U.R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  letI : Algebra c.O ↥E.1 := ((algebraMap c.O (PadicAlgCl l)).codRestrict E.1 fun a => f.commutes a ▸ hE' _).toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O ↥E.1 := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  let f' : U.R →ₐ[c.O] ↥E.1 :=
    { (f : U.R →+* PadicAlgCl l).codRestrict E.1 hE' with commutes' := fun a => Subtype.ext (f.commutes a) }
  obtain ⟨-, -, ρ, h1, h2⟩ := Loc.rtPoints hI.loc D.loc U ↥E.1 (push f' U.r.hom)
    ⟨f', rfl, fun a ha => Subtype.ext (hker ha)⟩
  refine ⟨E, ρ, fun g => ?_, h2⟩
  rw [h1, ← MonoidHom.comp_apply r D.ι, ← hpush]
  rfl
/- English proof (translation)
Use `haveI := isAlgClosure_of_number_field Ω K`. Take `⟨E, ρ, h1, h2⟩` from `exists_local_crystalline_gl3_model D hI h`. Take `⟨-, hcc, -, hη, -⟩` from `dat_facts D`. Establish `hop : IsOpen (D.loc.HL : Set (GQ l))` using `((hη.comp_continuous D.ι_cont).isOpen_fiber 1).inter D.τ_open`. Establish `hφ : Topology.IsOpenEmbedding D.loc.HL.subtype` using `hop.isOpenEmbedding_subtypeVal`.

Establish `hinj` using `(galEmbTop ℚ K Ω).1.injective`. Establish `hη1 : ∀ s : ↥D.loc.HL, D.η (D.ι s) = 1` using `fun s => s.2.1`. Set `ψ₀ : ↥D.loc.HL →* G ℚ Ω` to `(MulAut.conj g⁻¹).toMonoidHom.comp (D.ι.comp D.loc.HL.subtype)`. Establish `hψ₀ : ∀ s, ψ₀ s = g⁻¹ * D.ι s * g` using `fun s => by simp [ψ₀]`. Establish `hmem : ∀ s, ψ₀ s ∈ (galEmb ℚ K Ω).range` using `fun s => by`.

Rewrite using `[range_galEmb, ← D.η_ker, MonoidHom.mem_ker, hψ₀]`. Simplify using `[hη1]`. Set `ψ' : ↥D.loc.HL →* G K Ω` to `(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ψ₀.codRestrict _ hmem)`. Establish `hψ' : ∀ s, galEmb ℚ K Ω (ψ' s) = g⁻¹ * D.ι s * g` using `fun s => (MonoidHom.apply_ofInjective_symm hinj _).trans (hψ₀ s)`. Establish `hspec : ∀ (s : ↥D.loc.HL) (y : Ω), D.loc.HL.subtype s ((D.j.comp (g : Ω →+* Ω)) y) = (D.j.comp (g : Ω →+* Ω)) (ψ' s y)`.

Introduce `s y`. Express the relevant statement in the definitionally equal form `(s : GQ l) (D.j (g y)) = D.j (g (galEmb ℚ K Ω (ψ' s) y))`. Rewrite using `[D.ι_spec, hψ']`. Simplify using the standard rewrite rules. Establish `hρ : Continuous ρ`.

Use `continuous_of_matrix_units _ (continuous_pi fun a => continuous_pi fun b => continuous_induced_rng.2 ?_)` and prove the remaining obligations. Establish `h3 : Continuous fun s : ↥D.loc.HL => (r (D.ι s)).mat a b` using `(h.cont.comp (D.ι_cont.comp continuous_subtype_val)).matrix_elem a b`. Conclude with `h3.congr fun s => by rw [GG.mat, ← h1]; rfl`. Break down `hg with rfl | rfl` into its components or cases. Use `Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E ρ (fun s a b => ?_) h2` and prove the remaining obligations.

Rewrite using `[Dat.rhoK_apply, hψ', inv_one, one_mul, mul_one, ← h1]`. Both sides reduce to the same expression. Use `Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E _ (fun s a b => ?_) (crystalline_of_theta_twist_gl3 _ hφ E ρ hρ h2)` and prove the remaining obligations. Rewrite using `[Dat.rhoK_apply, hψ', conj_left_block_eq_theta r _ _ h.norm.atc ((h.mult _).trans hcc) ((h.mult _).trans (hη1 s)), ← h1, ← map_theta]`. Both sides reduce to the same expression.
-/
private theorem potentially_crystalline_conjugate_place (hI : CohInp) (h : D.IsPt U g₁ r) (g : G ℚ Ω) (hg : g = 1 ∨ g = D.cc) :
    Af.PotCrysAt (D.rhoK r h.mult) (Loc.placeJ (D.j.comp (g : Ω →+* Ω))) := by
  haveI := isAlgClosure_of_number_field Ω K
  obtain ⟨E, ρ, h1, h2⟩ := exists_local_crystalline_gl3_model D hI h
  obtain ⟨-, hcc, -, hη, -⟩ := dat_facts D
  have hop : IsOpen (D.loc.HL : Set (GQ l)) :=
    ((hη.comp_continuous D.ι_cont).isOpen_fiber 1).inter D.τ_open
  have hφ : Topology.IsOpenEmbedding D.loc.HL.subtype := hop.isOpenEmbedding_subtypeVal
  have hinj := (galEmbTop ℚ K Ω).1.injective
  have hη1 : ∀ s : ↥D.loc.HL, D.η (D.ι s) = 1 := fun s => s.2.1
  let ψ₀ : ↥D.loc.HL →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (D.ι.comp D.loc.HL.subtype)
  have hψ₀ : ∀ s, ψ₀ s = g⁻¹ * D.ι s * g := fun s => by simp [ψ₀]
  have hmem : ∀ s, ψ₀ s ∈ (galEmb ℚ K Ω).range := fun s => by
    rw [range_galEmb, ← D.η_ker, MonoidHom.mem_ker, hψ₀]
    simp [hη1]
  let ψ' : ↥D.loc.HL →* G K Ω := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ψ₀.codRestrict _ hmem)
  have hψ' : ∀ s, galEmb ℚ K Ω (ψ' s) = g⁻¹ * D.ι s * g := fun s =>
    (MonoidHom.apply_ofInjective_symm hinj _).trans (hψ₀ s)
  have hspec : ∀ (s : ↥D.loc.HL) (y : Ω), D.loc.HL.subtype s ((D.j.comp (g : Ω →+* Ω)) y) = (D.j.comp (g : Ω →+* Ω)) (ψ' s y) := by
    intro s y
    change (s : GQ l) (D.j (g y)) = D.j (g (galEmb ℚ K Ω (ψ' s) y))
    rw [D.ι_spec, hψ']
    simp
  have hρ : Continuous ρ := by
    refine continuous_of_matrix_units _ (continuous_pi fun a => continuous_pi fun b => continuous_induced_rng.2 ?_)
    have h3 : Continuous fun s : ↥D.loc.HL => (r (D.ι s)).mat a b :=
      (h.cont.comp (D.ι_cont.comp continuous_subtype_val)).matrix_elem a b
    exact h3.congr fun s => by rw [GG.mat, ← h1]; rfl
  rcases hg with rfl | rfl
  · refine Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E ρ (fun s a b => ?_) h2
    rw [Dat.rhoK_apply, hψ', inv_one, one_mul, mul_one, ← h1]
    rfl
  · refine Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E _ (fun s a b => ?_) (crystalline_of_theta_twist_gl3 _ hφ E ρ hρ h2)
    rw [Dat.rhoK_apply, hψ', conj_left_block_eq_theta r _ _ h.norm.atc ((h.mult _).trans hcc) ((h.mult _).trans (hη1 s)), ← h1,
      ← map_theta]
    rfl
/- English proof (translation)
Use `haveI := isAlgClosure_of_number_field Ω K`. Take `⟨-, hcc, -⟩` from `dat_facts D`. Take `⟨j, hj⟩` from `(Loc.decEmb (F := K) (Ω := Ω) (v := l)).1 _ w (isPlaceOver_placeOf Ω w) hw`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : G ℚ Ω, ∀ x, j x = D.j (g x) := by`. Use `letI : Algebra Ω (Om l) := D.j.toAlgebra`.

Use `haveI : IsScalarTower ℚ Ω (Om l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Conclude with `⟨AlgHom.restrictNormal' j.toRatAlgHom Ω, fun x => (AlgHom.restrictNormal_commutes j.toRatAlgHom Ω x).symm⟩`. Establish `key : ∀ g' : G ℚ Ω, D.η g' = D.η g → IsPlaceOver (Loc.placeJ (D.j.comp (g' : Ω →+* Ω))) w`. Introduce `g' hg' x`. Establish `h1 : g'⁻¹ * g ∈ (galEmb ℚ K Ω).range`.

Rewrite using `[range_galEmb, ← D.η_ker, MonoidHom.mem_ker]`. Simplify using `[hg']`. Take `⟨k, hk⟩` from `h1`. Establish `h2 : ∀ y : K, (D.j.comp (g' : Ω →+* Ω)) (algebraMap K Ω y) = j (algebraMap K Ω y)` using `fun y => by`. Rewrite using `[hg, ← mul_inv_cancel_left g' g, ← hk, AlgEquiv.mul_apply, galEmb_apply, AlgEquiv.commutes]`.

Both sides reduce to the same expression. Rewrite using `[← isPlaceOver_placeOf Ω w x, ← hj, ← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀]`. Simplify using `only [Loc.placeJ, ValuationSubring.mem_comap, h2]`. Break down `Int.units_eq_one_or (D.η g) with h1 | h1` into its components or cases. Conclude with `⟨1, Or.inl rfl, key _ (by rw [h1, map_one])⟩`.

Conclude with `⟨_, Or.inr rfl, key _ (by rw [h1, hcc])⟩`.
-/
private theorem exists_place_over_conjugate_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    ∃ g : G ℚ Ω, (g = 1 ∨ g = D.cc) ∧ IsPlaceOver (Loc.placeJ (D.j.comp (g : Ω →+* Ω))) w := by
  haveI := isAlgClosure_of_number_field Ω K
  obtain ⟨-, hcc, -⟩ := dat_facts D
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := K) (Ω := Ω) (v := l)).1 _ w (isPlaceOver_placeOf Ω w) hw
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, ∀ x, j x = D.j (g x) := by
    letI : Algebra Ω (Om l) := D.j.toAlgebra
    haveI : IsScalarTower ℚ Ω (Om l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact ⟨AlgHom.restrictNormal' j.toRatAlgHom Ω, fun x => (AlgHom.restrictNormal_commutes j.toRatAlgHom Ω x).symm⟩
  have key : ∀ g' : G ℚ Ω, D.η g' = D.η g → IsPlaceOver (Loc.placeJ (D.j.comp (g' : Ω →+* Ω))) w := by
    intro g' hg' x
    have h1 : g'⁻¹ * g ∈ (galEmb ℚ K Ω).range := by
      rw [range_galEmb, ← D.η_ker, MonoidHom.mem_ker]
      simp [hg']
    obtain ⟨k, hk⟩ := h1
    have h2 : ∀ y : K, (D.j.comp (g' : Ω →+* Ω)) (algebraMap K Ω y) = j (algebraMap K Ω y) := fun y => by
      rw [hg, ← mul_inv_cancel_left g' g, ← hk, AlgEquiv.mul_apply, galEmb_apply, AlgEquiv.commutes]
      rfl
    rw [← isPlaceOver_placeOf Ω w x, ← hj, ← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀]
    simp only [Loc.placeJ, ValuationSubring.mem_comap, h2]
  rcases Int.units_eq_one_or (D.η g) with h1 | h1
  · exact ⟨1, Or.inl rfl, key _ (by rw [h1, map_one])⟩
  · exact ⟨_, Or.inr rfl, key _ (by rw [h1, hcc])⟩
end
/- English proof (translation)
Introduce `hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h _ ι hT hA`. Use `haveI := isAlgClosure_of_number_field Ω K`. Establish `hη : ∀ s : G K Ω, D.η (galEmb ℚ K Ω s) = 1` using `fun s => by`. Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`. Conclude with `galEmb_mem ℚ K Ω s`.

Set `θ : G K Ω →* (Qbar l)ˣ` to `(Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))`. Establish `hθ : ∀ i : Fin 3, Af.KillsMu N (θ ^ wt1 i)` using `fun i s hs => by`. Establish `: Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1` using `(Chr.clsFacts ℚ Ω N).2.2.1 _ 1 fun ζ hζ => by`. Rewrite using `[Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one, galEmb_apply, hs ζ hζ]`. Simplify using `[θ, Chr.dirG, this]`.

Establish `hΨ : ∀ s : G K Ω, D.ΨQ (galEmb ℚ K Ω s) = cycBar K Ω l s ^ (e : ℤ) * θ s` using `fun s => by`. Establish `h1 : Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) = cycBar K Ω l s` using `Units.ext rfl`. Rewrite using `[← h1, ← map_zpow]`. Conclude with `map_mul (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) _ _`. Use `⟨⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => hT W fun g hg v hv => ?_⟩, hA, continuous_rho_of_point D h, fun w hw => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[D.η_ker, ← range_galEmb]`. Take `⟨s, rfl⟩` from `hg`. Conclude with `hW s v hv`. Establish `hB` using `isPlaceOver_placeOf Ω w`. Establish `hl : ¬ (placeOf Ω w).valuation (l : Ω) < 1` using `fun h => hw (((places K Ω l _).2.2.1 w hB).1 h)`.

Take `⟨M, hM⟩` from `pt_inertia_away D hM h _ hl`. Use `⟨_, hB, fun i => θ ^ wt1 i, hθ, M, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1` using `hM (galEmb ℚ K Ω s) hs (hη s)`. Establish `h2 : cycBar K Ω l s = 1`. Establish `: cycZ K Ω l s = 1` using `(places K Ω l _).2.2.2 hl hs`.

Simplify using `[cycBar, this]`. Rewrite using `[Units.val_mul, Units.val_mul, Dat.rhoK_apply, ← GG.mat, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, h2, _root_.one_zpow, one_mul]`. Both sides reduce to the same expression. Take `⟨g, hg, hB⟩` from `exists_place_over_conjugate_embedding D w hw`. Establish `hl` using `((places K Ω l _).2.2.1 w hB).2 hw`.

Take `⟨-, M, h1, h2⟩` from `pt_inertia_above hI D hM h _ hl`. Establish `hF` using `(galEmbFam ℚ K Ω l).1 (Loc.placeJ (D.j.comp (g : Ω →+* Ω)))`. Establish `hc : ∀ s : G K Ω, (conjBy M r (galEmb ℚ K Ω s)).left = M * D.rhoK r h.mult s * M⁻¹` using `fun s => conj_left_block_of_right_one M r _ ((h.mult _).trans (hη s))`. Take `⟨κ, hκ, hκ'⟩` from `exists_flag_characters_of_upper_triangular (D.rhoK r h.mult) (Dec (F := K) (Loc.placeJ (D.j.comp (g : Ω →+* Ω)))) M fun s hs i j hij => by`. Rewrite using `[← hc]`.

Rewrite `hs` using `[← hF.1]`. Conclude with `h1 _ hs (hη s) i j (by have : (j : ℕ) < i := hij; simp only [wt, wt1]; omega)`. Use `⟨_, hB, fun i => θ ^ wt1 i, κ, hθ, hκ, fun i s hs => Units.ext ?_, Or.inr (potentially_crystalline_conjugate_place D hI h g hg)⟩` and prove the remaining obligations. Apply the tactic sequence `have h3 : ![(e : ℤ), 0, -(e : ℤ)] i = e * wt1 i := by fin_cases i <;> simp [wt1]`. Rewrite using `[hκ', ← hc, h3, _root_.zpow_mul, MonoidHom.zpow_apply, ← _root_.mul_zpow, ← hΨ]`.

Use `(h2 _ hs i).trans ?_` and prove the remaining obligations. Rewrite using `[GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]`.
-/
theorem UpperTheory.V.U3.admissible_rank_three_of_type_one_of_automorphic_point :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ),
      TypeI D.η r → D.IsAutIAlt ι r h.mult → _root_.UpperTheory.V.Af.Adm3Alt ι e N (D.rhoK r h.mult) := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h _ ι hT hA
  haveI := isAlgClosure_of_number_field Ω K
  have hη : ∀ s : G K Ω, D.η (galEmb ℚ K Ω s) = 1 := fun s => by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω s
  let θ : G K Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp
    ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))
  have hθ : ∀ i : Fin 3, Af.KillsMu N (θ ^ wt1 i) := fun i s hs => by
    have : Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1 := (Chr.clsFacts ℚ Ω N).2.2.1 _ 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one, galEmb_apply, hs ζ hζ]
    simp [θ, Chr.dirG, this]
  have hΨ : ∀ s : G K Ω, D.ΨQ (galEmb ℚ K Ω s) = cycBar K Ω l s ^ (e : ℤ) * θ s := fun s => by
    have h1 : Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) =
        cycBar K Ω l s := Units.ext rfl
    rw [← h1, ← map_zpow]
    exact map_mul (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) _ _
  refine ⟨⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => hT W fun g hg v hv => ?_⟩, hA, continuous_rho_of_point D h,
    fun w hw => ?_, fun w hw => ?_⟩
  · rw [D.η_ker, ← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    exact hW s v hv
  · have hB := isPlaceOver_placeOf Ω w
    have hl : ¬ (placeOf Ω w).valuation (l : Ω) < 1 := fun h => hw (((places K Ω l _).2.2.1 w hB).1 h)
    obtain ⟨M, hM⟩ := pt_inertia_away D hM h _ hl
    refine ⟨_, hB, fun i => θ ^ wt1 i, hθ, M, fun s hs => ?_⟩
    have h1 := hM (galEmb ℚ K Ω s) hs (hη s)
    have h2 : cycBar K Ω l s = 1 := by
      have : cycZ K Ω l s = 1 := (places K Ω l _).2.2.2 hl hs
      simp [cycBar, this]
    rw [Units.val_mul, Units.val_mul, Dat.rhoK_apply, ← GG.mat, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      GG.mat, unitaryThreeReflection_left, tor_val, hΨ, h2, _root_.one_zpow, one_mul]
    rfl
  · obtain ⟨g, hg, hB⟩ := exists_place_over_conjugate_embedding D w hw
    have hl := ((places K Ω l _).2.2.1 w hB).2 hw
    obtain ⟨-, M, h1, h2⟩ := pt_inertia_above hI D hM h _ hl
    have hF := (galEmbFam ℚ K Ω l).1 (Loc.placeJ (D.j.comp (g : Ω →+* Ω)))
    have hc : ∀ s : G K Ω, (conjBy M r (galEmb ℚ K Ω s)).left = M * D.rhoK r h.mult s * M⁻¹ := fun s =>
      conj_left_block_of_right_one M r _ ((h.mult _).trans (hη s))
    obtain ⟨κ, hκ, hκ'⟩ := exists_flag_characters_of_upper_triangular (D.rhoK r h.mult) (Dec (F := K) (Loc.placeJ (D.j.comp (g : Ω →+* Ω)))) M
      fun s hs i j hij => by
        rw [← hc]
        rw [← hF.1] at hs
        exact h1 _ hs (hη s) i j (by have : (j : ℕ) < i := hij; simp only [wt, wt1]; omega)
    refine ⟨_, hB, fun i => θ ^ wt1 i, κ, hθ, hκ, fun i s hs => Units.ext ?_, Or.inr (potentially_crystalline_conjugate_place D hI h g hg)⟩
    have h3 : ![(e : ℤ), 0, -(e : ℤ)] i = e * wt1 i := by fin_cases i <;> simp [wt1]
    rw [hκ', ← hc, h3, _root_.zpow_mul, MonoidHom.zpow_apply, ← _root_.mul_zpow, ← hΨ]
    refine (h2 _ hs i).trans ?_
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]
end
