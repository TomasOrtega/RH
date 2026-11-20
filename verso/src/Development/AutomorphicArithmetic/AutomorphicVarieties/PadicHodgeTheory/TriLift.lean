import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusLiftToNilpotentThickening
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUnipotentFromTorusCoords
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTorusCoordsOfUnipotent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsContinuousIsGamOfTorusCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ConjugateRestrictionOpenNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCocycleExtensionOfConjugationInvariantRest
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFiniteCocyclesIffRestrictSubgroupMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffOfCharData
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallineTriangularLiftOfMemFiniteCocycl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffMemFiniteCocyclesOfCha
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorsionDatumFiniteCocyclesBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorsionDatumFiniteCocyclesCompare
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc.TriangularDeformation
open Topology

private def resH {G B : Type} [Group G] [CommRing B] (u : G →* GG 3 B) (H : Subgroup G)
    (h : ∀ g ∈ H, (u g).right = 1) : H →* GL (Fin 3) B where
  toFun g := (u g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

/- English proof (translation)
Use `⟨fun ⟨ρ, hρ, hc⟩ => ?_, fun hc => ⟨_, fun _ => rfl, hc⟩⟩` and prove the remaining obligations. Establish `: resH u H h = ρ` using `MonoidHom.ext fun g => (hρ g).symm`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
private theorem lcr_iff {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] (H : Subgroup (GQ l))
    (u : GQ l →* GG 3 B) (h : ∀ g ∈ H, (u g).right = 1) : LCr H u ↔ IsCr H.subtype (colRep (resH u H h)) := by
  refine ⟨fun ⟨ρ, hρ, hc⟩ => ?_, fun hc => ⟨_, fun _ => rfl, hc⟩⟩
  have : resH u H h = ρ := MonoidHom.ext fun g => (hρ g).symm
  rwa [this]

/- English proof (translation)
Use `MonoidHom.ext fun g => LinearMap.ext fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(T.χ2 g : B) * v = ((T.t g 0 / T.t g 2 : Bˣ) : B) * v`. Rewrite using `[Tor.χ2_apply, hH g g.2]`. Simplify using the standard rewrite rules.
-/
private theorem chi_res {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (H : Subgroup G)
    (hH : ∀ g ∈ H, η g = 1) :
    ((chRep T.χ2).comp H.subtype : Representation B H B) = chRep (T.ch H hH 0 / T.ch H hH 2) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
  change (T.χ2 g : B) * v = ((T.t g 0 / T.t g 2 : Bˣ) : B) * v
  rw [Tor.χ2_apply, hH g g.2]
  simp

/- English proof (translation)
Use `⟨cγ'.sub cγ, fun g g' => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, chRep_apply, g1 g g', g2 g g']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gam_sub {G B : Type} [Group G] [CommRing B] [TopologicalSpace G] [TopologicalSpace B]
    [IsTopologicalRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B} {γ γ' : G → B}
    (cγ : Continuous γ) (cγ' : Continuous γ') (g1 : T.IsGam h β γ) (g2 : T.IsGam h β γ') :
    γ' - γ ∈ Z1 (chRep T.χ2) := by
  refine ⟨cγ'.sub cγ, fun g g' => ?_⟩
  simp only [Pi.sub_apply, chRep_apply, g1 g g', g2 g g']
  ring

/- English proof (translation)
Introduce `g g'`. Simplify using `only [Pi.add_apply, chRep_apply, g1 g g', hδ.2 g g']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gam_add {G B : Type} [Group G] [CommRing B] [TopologicalSpace G] [TopologicalSpace B]
    [IsTopologicalRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B} {γ δ : G → B}
    (g1 : T.IsGam h β γ) (hδ : δ ∈ Z1 (chRep T.χ2)) : T.IsGam h β (γ + δ) := by
  intro g g'
  simp only [Pi.add_apply, chRep_apply, g1 g g', hδ.2 g g']
  ring

/- English proof (translation)
Introduce `hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β γ γ' u u' cβ cγ cγ' hβ g1 g2 c1 c2 hu`. Use `haveI := hD.normal`. Use `haveI := hD.fin`. Establish `hφ : IsOpenEmbedding H.subtype` using `hD.isOpen.isOpenEmbedding_subtypeVal`. Establish `r1 : ∀ g ∈ H, (u g).right = 1` using `fun g hg => (c1.right g).trans (hD.ηH g hg)`.

Establish `r2 : ∀ g ∈ H, (u' g).right = 1` using `fun g hg => (c2.right g).trans (hD.ηH g hg)`. Rewrite `hu` using `[lcr_iff H u r1]`. Establish `key` using `(UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ (hT.chars hD) (fun g => (β g).1) (fun g => (β g).2) (fun g => γ g + h * (β g).1 * (β g).2) (resH u H r1) (by fun_prop) (by fun_prop) (by fun_prop) (fun g => c1.mat g) (fun g => hβ g) hu …`. Rewrite using `[lcr_iff H u' r2, key, z1fDesc (MonoidHom.id _) (chRep T.χ2) H _ (gam_sub cγ cγ' g1 g2), chi_res T H hD.ηH]`. Establish `: ((fun g : H => γ' g + h * (β g).1 * (β g).2) - fun g : H => γ g + h * (β g).1 * (β g).2) = fun g : H => (γ' - γ) g`.

Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
private theorem gamDiff : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B) (β : GQ l → B × B) (γ γ' : GQ l → B) (u u' : GQ l →* GG 3 B), Continuous β → Continuous γ → Continuous γ' → (∀ g, π (β g).1 = 0) → T.IsGam h β γ → T.IsGam h β γ' → T.Coord h β γ u → T.Coord h β γ' u' → LCr H u → (LCr H u' ↔ γ' - γ ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T.χ2)) := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β γ γ' u u' cβ cγ cγ' hβ g1 g2 c1 c2 hu
  haveI := hD.normal
  haveI := hD.fin
  have hφ : IsOpenEmbedding H.subtype := hD.isOpen.isOpenEmbedding_subtypeVal
  have r1 : ∀ g ∈ H, (u g).right = 1 := fun g hg => (c1.right g).trans (hD.ηH g hg)
  have r2 : ∀ g ∈ H, (u' g).right = 1 := fun g hg => (c2.right g).trans (hD.ηH g hg)
  rw [lcr_iff H u r1] at hu
  have key := (UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ (hT.chars hD) (fun g => (β g).1) (fun g => (β g).2)
    (fun g => γ g + h * (β g).1 * (β g).2) (resH u H r1) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun g => c1.mat g) (fun g => hβ g) hu (fun g => γ' g + h * (β g).1 * (β g).2) (resH u' H r2) (by fun_prop)
    (fun g => c2.mat g)).2
  rw [lcr_iff H u' r2, key, z1fDesc (MonoidHom.id _) (chRep T.χ2) H _ (gam_sub cγ cγ' g1 g2), chi_res T H hD.ηH]
  have : ((fun g : H => γ' g + h * (β g).1 * (β g).2) - fun g : H => γ g + h * (β g).1 * (β g).2) =
      fun g : H => (γ' - γ) g := by
    funext g
    simp
  rw [this]
  rfl

private def nE {B : Type} [CommRing B] (c : B) : GL (Fin 3) B where
  val := !![1, 0, c; 0, 1, 0; 0, 0, 1]
  inv := !![1, 0, -c; 0, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nE_mul {B : Type} [CommRing B] (c : B) (t : Fin 3 → Bˣ) (x y z : B) :
    (nE c : Matrix (Fin 3) (Fin 3) B) * triM t x y z = triM t x y (z + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[theta_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nE, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]`.
-/
private theorem theta_nE {B : Type} [CommRing B] (c : B) : theta (nE c) = nE (-c) := by
  apply Units.ext
  rw [theta_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

/- English proof (translation)
Establish `e : ((t 0 / t 2 : Bˣ) : B) * t 2 = t 0` using `by rw [← Units.val_mul, div_mul_cancel]`. Rewrite using `[nE_mul]`. Generalize the expression as in `((t 0 / t 2 : Bˣ) : B) = q at e`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]`.

Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem triM_nE {B : Type} [CommRing B] (c : B) (t : Fin 3 → Bˣ) (x y z : B) :
    triM t x y z * (nE c : Matrix (Fin 3) (Fin 3) B) =
      (nE (((t 0 / t 2 : Bˣ) : B) * c) : Matrix (Fin 3) (Fin 3) B) * triM t x y z := by
  have e : ((t 0 / t 2 : Bˣ) : B) * t 2 = t 0 := by rw [← Units.val_mul, div_mul_cancel]
  rw [nE_mul]
  generalize ((t 0 / t 2 : Bˣ) : B) = q at e
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nE, triM, Matrix.mul_apply, Fin.sum_univ_three]
  rw [← e]
  ring

/- English proof (translation)
Use `SemidirectProduct.ext ?_ (by simp)` and prove the remaining obligations. Establish `hm : ((u s).left : Matrix (Fin 3) (Fin 3) B) = _` using `hu.mat s`. Apply `Units.ext` to reduce the goal to its premises. Apply the tactic sequence `rcases Int.units_eq_one_or (η s) with hs | hs <;>`. Apply the tactic sequence `simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, hu.right, hs, sgnAct_one, sgnAct_neg_one, theta_nE, Units.val_mul, hm, triM_nE, Tor.χ2_apply] <;> simp`.
-/
private theorem conj_nE {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} {T : Tor η B} {h : B} {β : G → B × B}
    {γ : G → B} {u : G →* GG 3 B} (hu : T.Coord h β γ u) (s : G) (c : B) :
    u s * GG.ofGL (nE c) = GG.ofGL (nE (T.χ2 s * c)) * u s := by
  refine SemidirectProduct.ext ?_ (by simp)
  have hm : ((u s).left : Matrix (Fin 3) (Fin 3) B) = _ := hu.mat s
  apply Units.ext
  rcases Int.units_eq_one_or (η s) with hs | hs <;>
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, hu.right, hs,
      sgnAct_one, sgnAct_neg_one, theta_nE, Units.val_mul, hm, triM_nE, Tor.χ2_apply] <;> simp

/- English proof (translation)
Introduce `hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h hh β hβ hβ0`. Use `haveI := hD.normal`. Use `haveI := hD.fin`. Establish `hφ : IsOpenEmbedding H.subtype` using `hD.isOpen.isOpenEmbedding_subtypeVal`. Establish `cβ : Continuous β` using `hβ.1.1`.

Take `⟨γ, cγ, gγ⟩` from `UpperTheory.exists_continuous_isGam_of_torus_cocycle hP hD π hπ T hT h β hβ.1`. Take `⟨u, cu⟩` from `UpperTheory.exists_unipotent_from_torus_coords T h hh β γ hβ.1.2 gγ`. Establish `r1 : ∀ g ∈ H, (u g).right = 1` using `fun g hg => (cu.right g).trans (hD.ηH g hg)`. Take `⟨hx, hy⟩` from `(UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π hπ T hT β hβ.1).1 hβ`. Establish `hch` using `hT.chars hD`.

Take `⟨z, ρ, cz, hρ, hcr⟩` from `UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles hP H.subtype hφ π hπ hch _ hx _ hy (fun g => hβ0 g)`. Establish `cx : Continuous fun g : H => (β g).1` using `by fun_prop`. Establish `cy : Continuous fun g : H => (β g).2` using `by fun_prop`. Establish `diff` using `UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ hch _ _ z ρ cx cy cz hρ (fun g => hβ0 g) hcr`. Use `set z₀ : H → B := fun g => γ g + h * (β g).1 * (β g).2 with hz₀`.

Establish `cz₀ : Continuous z₀` using `by fun_prop`. Establish `hc : z - z₀ ∈ Z1 ((chRep T.χ2).comp H.subtype : Representation B H B)`. Rewrite using `[chi_res T H hD.ηH, ← neg_sub]`. Conclude with `Submodule.neg_mem _ (diff z₀ (resH u H r1) cz₀ (fun g => cu.mat g)).1`. Establish `cχ` using `T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv`.

Establish `cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)`. Simplify using `only [hρ]`. Conclude with `continuous_triM hch.cont cx cy cz`. Establish `fac : ∀ g : H, GG.ofGL (ρ g) = GG.ofGL (nE ((z - z₀) g)) * u g`. Introduce `g`.

Use `SemidirectProduct.ext (Units.ext ?_) (by simp [r1 g g.2])` and prove the remaining obligations. Establish `hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _` using `cu.mat g`. Simplify using `only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, Units.val_mul, hm, nE_mul, hρ, Pi.sub_apply, hz₀, add_sub_cancel]`. Both sides reduce to the same expression. Take `⟨b, hb, hbN⟩` from `UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction (l := l) (chRep T.χ2) (contAction_chRep cχ) H hD.isOpen (UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 2))) (z - z₀) hc (by`.

Introduce `s c' hc'`. Set `τ : H →* H` to `(MulAut.conjNormal s⁻¹ : MulAut H).toMonoidHom`. Establish `hτ : ∀ g : H, ((τ g : H) : GQ l) = s⁻¹ * g * s` using `fun g => by simp [τ]`. Establish `cτ : Continuous τ`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations.

Establish `: (Subtype.val ∘ τ) = fun g : H => s⁻¹ * (g : GQ l) * s` using `funext hτ`. Rewrite using `[this]`. Use `fun_prop`. Establish `hw : ∀ g : H, u s * GG.ofGL (ρ (τ g)) * (u s)⁻¹ = GG.ofGL (nE (c' g)) * u g`. Introduce `g`.

Rewrite using `[fac, hτ, hc' g (τ g) (hτ g), chRep_apply, ← mul_assoc, conj_nE cu]`. Simplify using `only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]`. Set `ρ' : H →* GL (Fin 3) B` to `{ toFun := fun g => nE (c' g) * (u g).left map_one' := by`. Use `congrArg SemidirectProduct.left (hw 1)` as an intermediate fact. Simplify using `using this.symm`.

Use the proof step `map_mul' := fun g g' => by`. Establish `e : GG.ofGL (nE (c' (g * g'))) * u (g * g' : H) = (GG.ofGL (nE (c' g)) * u g) * (GG.ofGL (nE (c' g')) * u g')`. Rewrite using `[← hw, ← hw, ← hw]`. Simplify using `only [map_mul, mul_assoc, inv_mul_cancel_left]`. Use `congrArg SemidirectProduct.left e` as an intermediate fact.

Simplify `this }` using `[r1 g g.2]`. Establish `hρ' : ∀ g : H, GG.ofGL (ρ' g) = GG.ofGL (nE (c' g)) * u g` using `fun g => SemidirectProduct.ext (by simp [ρ']) (by simp [r1 g g.2])`. Establish `cr'` using `UpperTheory.conjugate_restriction_open_normal H hD.isOpen ρ ρ' cρ s (u s) (fun g g' e => by`. Establish `: g' = τ g` using `Subtype.ext (e.trans (hτ g).symm)`. Rewrite using `[hρ', this, hw]) hcr`.

Establish `cc' : Continuous c'`. Establish `: c' = fun g => (T.χ2 s : B) * (z - z₀) (τ g)` using `funext fun g => hc' g (τ g) (hτ g)`. Rewrite using `[this]`. Conclude with `continuous_const.mul ((cz.sub cz₀).comp cτ)`. Use `(diff (z₀ + c') ρ' (cz₀.add cc') (fun g => by` as an intermediate fact.

Establish `hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _` using `cu.mat g`. Express the relevant statement in the definitionally equal form `((nE (c' g) * (u g).left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _`. Rewrite using `[Units.val_mul, hm, nE_mul]`. Use the proof step `rfl)).2.1 cr'`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use the proof step `abel)`. Take `⟨u', cu'⟩` from `UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + b) hβ.1.2 (gam_add gγ hb)`. Use `⟨γ + b, u', cγ.add hb.1, gam_add gγ hb, cu', ?_⟩` and prove the remaining obligations. Establish `r2 : ∀ g ∈ H, (u' g).right = 1` using `fun g hg => (cu'.right g).trans (hD.ηH g hg)`. Establish `cb : Continuous b` using `hb.1`.

Rewrite using `[lcr_iff H u' r2]`. Use `(diff (fun g : H => (γ + b) g + h * (β g).1 * (β g).2) (resH u' H r2) (by fun_prop) (fun g => cu'.mat g)).2.2 ?_` and prove the remaining obligations. Use `hbN using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.sub_apply, Pi.add_apply, hz₀]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gamCr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), 2 * h = 1 → ∀ β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1, (∀ g, π (β g).1 = 0) → ∃ (γ : GQ l → B) (u : GQ l →* GG 3 B), Continuous γ ∧ T.IsGam h β γ ∧ T.Coord h β γ u ∧ LCr H u := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h hh β hβ hβ0
  haveI := hD.normal
  haveI := hD.fin
  have hφ : IsOpenEmbedding H.subtype := hD.isOpen.isOpenEmbedding_subtypeVal
  have cβ : Continuous β := hβ.1.1
  obtain ⟨γ, cγ, gγ⟩ := UpperTheory.exists_continuous_isGam_of_torus_cocycle hP hD π hπ T hT h β hβ.1
  obtain ⟨u, cu⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β γ hβ.1.2 gγ
  have r1 : ∀ g ∈ H, (u g).right = 1 := fun g hg => (cu.right g).trans (hD.ηH g hg)
  obtain ⟨hx, hy⟩ := (UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π hπ T hT β hβ.1).1 hβ
  have hch := hT.chars hD
  obtain ⟨z, ρ, cz, hρ, hcr⟩ := UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles hP H.subtype hφ π hπ hch _ hx _ hy (fun g => hβ0 g)
  have cx : Continuous fun g : H => (β g).1 := by fun_prop
  have cy : Continuous fun g : H => (β g).2 := by fun_prop
  have diff := UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData hP H.subtype hφ π hπ hch _ _ z ρ cx cy cz hρ (fun g => hβ0 g) hcr
  set z₀ : H → B := fun g => γ g + h * (β g).1 * (β g).2 with hz₀
  have cz₀ : Continuous z₀ := by fun_prop
  have hc : z - z₀ ∈ Z1 ((chRep T.χ2).comp H.subtype : Representation B H B) := by
    rw [chi_res T H hD.ηH, ← neg_sub]
    exact Submodule.neg_mem _ (diff z₀ (resH u H r1) cz₀ (fun g => cu.mat g)).1
  have cχ := T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv
  have cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM hch.cont cx cy cz
  have fac : ∀ g : H, GG.ofGL (ρ g) = GG.ofGL (nE ((z - z₀) g)) * u g := by
    intro g
    refine SemidirectProduct.ext (Units.ext ?_) (by simp [r1 g g.2])
    have hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _ := cu.mat g
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one,
      Units.val_mul, hm, nE_mul, hρ, Pi.sub_apply, hz₀, add_sub_cancel]
    rfl
  obtain ⟨b, hb, hbN⟩ := UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction (l := l) (chRep T.χ2) (contAction_chRep cχ) H hD.isOpen
    (UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 2))) (z - z₀) hc (by
      intro s c' hc'
      let τ : H →* H := (MulAut.conjNormal s⁻¹ : MulAut H).toMonoidHom
      have hτ : ∀ g : H, ((τ g : H) : GQ l) = s⁻¹ * g * s := fun g => by simp [τ]
      have cτ : Continuous τ := by
        refine continuous_induced_rng.2 ?_
        have : (Subtype.val ∘ τ) = fun g : H => s⁻¹ * (g : GQ l) * s := funext hτ
        rw [this]
        fun_prop
      have hw : ∀ g : H, u s * GG.ofGL (ρ (τ g)) * (u s)⁻¹ = GG.ofGL (nE (c' g)) * u g := by
        intro g
        rw [fac, hτ, hc' g (τ g) (hτ g), chRep_apply, ← mul_assoc, conj_nE cu]
        simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
      let ρ' : H →* GL (Fin 3) B :=
        { toFun := fun g => nE (c' g) * (u g).left
          map_one' := by
            have := congrArg SemidirectProduct.left (hw 1)
            simpa using this.symm
          map_mul' := fun g g' => by
            have e : GG.ofGL (nE (c' (g * g'))) * u (g * g' : H) =
                (GG.ofGL (nE (c' g)) * u g) * (GG.ofGL (nE (c' g')) * u g') := by
              rw [← hw, ← hw, ← hw]
              simp only [map_mul, mul_assoc, inv_mul_cancel_left]
            have := congrArg SemidirectProduct.left e
            simpa [r1 g g.2] using this }
      have hρ' : ∀ g : H, GG.ofGL (ρ' g) = GG.ofGL (nE (c' g)) * u g := fun g =>
        SemidirectProduct.ext (by simp [ρ']) (by simp [r1 g g.2])
      have cr' := UpperTheory.conjugate_restriction_open_normal H hD.isOpen ρ ρ' cρ s (u s) (fun g g' e => by
        have : g' = τ g := Subtype.ext (e.trans (hτ g).symm)
        rw [hρ', this, hw]) hcr
      have cc' : Continuous c' := by
        have : c' = fun g => (T.χ2 s : B) * (z - z₀) (τ g) := funext fun g => hc' g (τ g) (hτ g)
        rw [this]
        exact continuous_const.mul ((cz.sub cz₀).comp cτ)
      have := (diff (z₀ + c') ρ' (cz₀.add cc') (fun g => by
        have hm : ((u g).left : Matrix (Fin 3) (Fin 3) B) = _ := cu.mat g
        change ((nE (c' g) * (u g).left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
        rw [Units.val_mul, hm, nE_mul]
        rfl)).2.1 cr'
      convert this using 1
      abel)
  obtain ⟨u', cu'⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + b) hβ.1.2 (gam_add gγ hb)
  refine ⟨γ + b, u', cγ.add hb.1, gam_add gγ hb, cu', ?_⟩
  have r2 : ∀ g ∈ H, (u' g).right = 1 := fun g hg => (cu'.right g).trans (hD.ηH g hg)
  have cb : Continuous b := hb.1
  rw [lcr_iff H u' r2]
  refine (diff (fun g : H => (γ + b) g + h * (β g).1 * (β g).2) (resH u' H r2) (by fun_prop)
    (fun g => cu'.mat g)).2.2 ?_
  convert hbN using 1
  funext g
  simp only [Pi.sub_apply, Pi.add_apply, hz₀]
  ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [triM, ht]`.
-/
private theorem triM_map {B B' : Type} [CommRing B] [CommRing B'] (p : B →+* B') (t : Fin 3 → Bˣ) (t' : Fin 3 → B'ˣ)
    (ht : ∀ i, p (t i) = t' i) (x y z : B) : (triM t x y z).map p = triM t' (p x) (p y) (p z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, ht]

/- English proof (translation)
The claim follows from `SemidirectProduct.ext (Units.ext h1) h2`.
-/
private theorem gg_ext {B : Type} [CommRing B] {a b : GG 3 B} (h1 : a.mat = b.mat) (h2 : a.right = b.right) : a = b :=
  SemidirectProduct.ext (Units.ext h1) h2

/- English proof (translation)
Take `⟨ρ, hρ, hc⟩` from `hu`. Establish `cp : Continuous p` using `IsModuleTopology.continuous_of_linearMap p.toLinearMap`. Establish `cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)`. Simplify using `only [hρ]`. Conclude with `cu.comp continuous_subtype_val`.

Use `⟨(Matrix.GeneralLinearGroup.map (p : B →+* B')).comp ρ, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, hρ]`. Both sides reduce to the same expression. Use `((isCrys_isDR_sub_quot H.subtype hH.isOpenEmbedding_subtypeVal _ _ (contAction_colRep cρ) (contAction_colRep (cρ.matrix_map cp)) (p.toLinearMap.compLeft (Fin 3)) (fun g x => ?_)).2 fun v => ?_).1 hc` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec (p : B →+* B') _ x i`. Conclude with `⟨fun i => (hp (v i)).choose, funext fun i => (hp (v i)).choose_spec⟩`.
-/
private theorem lcr_map {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]
    {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B']
    [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] (p : B →ₐ[ℚ_[l]] B')
    (hp : Function.Surjective p) {H : Subgroup (GQ l)} (hH : IsOpen (H : Set (GQ l))) {u : GQ l →* GG 3 B}
    (cu : Continuous fun g => (u g).mat) (hu : LCr H u) : LCr H ((GG.map (p : B →+* B')).comp u) := by
  obtain ⟨ρ, hρ, hc⟩ := hu
  have cp : Continuous p := IsModuleTopology.continuous_of_linearMap p.toLinearMap
  have cρ : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact cu.comp continuous_subtype_val
  refine ⟨(Matrix.GeneralLinearGroup.map (p : B →+* B')).comp ρ, fun g => ?_, ?_⟩
  · rw [MonoidHom.comp_apply, hρ]
    rfl
  · refine ((isCrys_isDR_sub_quot H.subtype hH.isOpenEmbedding_subtypeVal _ _ (contAction_colRep cρ)
      (contAction_colRep (cρ.matrix_map cp)) (p.toLinearMap.compLeft (Fin 3)) (fun g x => ?_)).2 fun v => ?_).1 hc
    · funext i
      exact RingHom.map_mulVec (p : B →+* B') _ x i
    · exact ⟨fun i => (hp (v i)).choose, funext fun i => (hp (v i)).choose_spec⟩

/- English proof (translation)
Establish `hη : IsOpen (D.η.ker : Set (GQ l))`. Establish `: D.η.ker = GK D.Kv` using `Subgroup.ext fun g => D.η_ker g`. Rewrite using `[this]`. Use `haveI := D.Kv.2`. Conclude with `IntermediateField.fixingSubgroup_isOpen D.Kv.1`.

Establish `ho : IsOpen (D.HL : Set (GQ l))` using `hη.inter D.τ_open`. Use `⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ?_, fun g hg => hg.1, D.η_unr, ?_, D.e_pos, fun g hg hi => ?_, hc⟩` and prove the remaining obligations. Use `haveI := Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_` and prove the remaining obligations.

Establish `: IsOpen {y : GQ l | g⁻¹ * y ∈ D.η.ker}` using `hη.preimage (by fun_prop)`. Use `filter_upwards [this.mem_nhds (by simp)] with y hy`. Rewrite `hy` using `[MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]`. Conclude with `hy.symm`. Establish `ht : D.τ g = 1` using `hg.2`.

Rewrite using `[MonoidHom.comp_apply, D.Ψ_I g hi, ht, mul_one, map_pow]`. Use `congr 1`. Conclude with `Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm`.
-/
private theorem triDat {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
    (E : Type) [Field E] [Algebra ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E]
    (hc : QCont l fun g => algebraMap O E (D.Ψ g)) :
    TriDat D.η ((Units.map (algebraMap O E : O →* E)).comp D.Ψ) D.HL D.e := by
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ?_, fun g hg => hg.1, D.η_unr, ?_, D.e_pos, fun g hg hi => ?_, hc⟩
  · haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.finiteIndex_of_finite_quotient
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have : IsOpen {y : GQ l | g⁻¹ * y ∈ D.η.ker} := hη.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (by simp)] with y hy
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
    exact hy.symm
  · have ht : D.τ g = 1 := hg.2
    rw [MonoidHom.comp_apply, D.Ψ_I g hi, ht, mul_one, map_pow]
    congr 1
    exact Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm

end UpperTheory.V.Loc.TriangularDeformation

open UpperTheory.V.Loc.TriangularDeformation in
/- English proof (translation)
Introduce `hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpπ u' hu'`. Use `letI : TopologicalSpace B := moduleTopology ℚ_[l] B`. Use `haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩`. Use `haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B`. Use `letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'`.

Use `haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩`. Use `haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'`. Use `letI : TopologicalSpace E := moduleTopology ℚ_[l] E`. Use `haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩`. Use `haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E`.

Establish `cp : Continuous p` using `IsModuleTopology.continuous_of_linearMap (p.restrictScalars ℚ_[l]).toLinearMap`. Establish `cπ' : Continuous π'` using `IsModuleTopology.continuous_of_linearMap (π'.restrictScalars ℚ_[l]).toLinearMap`. Establish `hππ : ∀ b, π' (p b) = π b` using `fun b => AlgHom.congr_fun hpπ b`. Use `set Ψ : GQ l →* Eˣ := (Units.map (algebraMap O E : O →* E)).comp D.Ψ with hΨ`. Establish `hpow : ∀ g i, algebraMap O E ((D.Ψ g ^ wt1 i : Oˣ) : O) = ((Ψ g ^ wt1 i : Eˣ) : E)` using `fun g i => by`.

Rewrite using `[hΨ, MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O E : O →* E))]`. Both sides reduce to the same expression. Establish `red' : ∀ g a b, π' ((u' g).mat a b) = if a = b then ((Ψ g ^ wt1 a : Eˣ) : E) else 0` using `fun g a b => by`. Use `congrFun (congrFun (congrArg GG.mat (DFunLike.congr_fun hu'.red g)) a) b` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap O E (Matrix.diagonal (fun i => ((D.Ψ g ^ wt1 i : Oˣ) : O)) a b) = _`. Rewrite using `[Matrix.diagonal_apply]`. Use `split_ifs`. Conclude with `hpow g a`. Conclude with `map_zero _`.

Establish `cu' : ∀ a b, Continuous fun g => (u' g).mat a b` using `hu'.cont`. Establish `hD : TriDat D.η Ψ D.HL D.e` using `triDat D E (by`. Establish `: (fun g => algebraMap O E (D.Ψ g)) = fun g => π' ((u' g).mat 0 0)` using `funext fun g => by`. Rewrite using `[red', if_pos rfl, ← hpow]`. Simplify using `[wt1]`.

Rewrite using `[this]`. Conclude with `cπ'.comp (cu' 0 0))`. Use `haveI := hD.normal`. Use `set h : B := algebraMap E B 2⁻¹ with hh0`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective`.

Establish `hh : 2 * h = 1`. Rewrite using `[hh0, ← map_ofNat (algebraMap E B) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Establish `hh' : 2 * p h = 1`. Use `congrArg p hh` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis.

Take `⟨T', β', γ', c', zβ', gγ'⟩` from `UpperTheory.exists_torus_coords_of_unipotent (p h) hh' u' hu'.mult hu'.tri`. Establish `d' : ∀ g i, (T'.t g i : B') = (u' g).mat i i` using `fun g i => by`. Rewrite using `[c'.mat]`. Apply the tactic sequence `fin_cases i <;> rfl`. Establish `ct' : ∀ i, Continuous fun g => (T'.t g i : B')` using `fun i => by`.

Simplify using `only [d']`. Conclude with `cu' i i`. Establish `hT' : T'.Good π' Ψ` using `{ cont := ct' cont_inv := fun i => UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => T'.t g i) (ct' i) ine := fun g hg i => by`. Rewrite using `[d', triDiag D E B' π' hπ' u' hu' g hg i, IsScalarTower.algebraMap_apply O E B', ← hpow]`. Both sides reduce to the same expression.

Use `red := fun g i => by rw [d', red', if_pos rfl] }`. Establish `e1 : ∀ g, (β' g).1 = (u' g).mat 0 1 * ((T'.t g 1)⁻¹ : B'ˣ)` using `fun g => by`. Rewrite using `[c'.mat]`. Simplify using `[triM]`. Establish `e2 : ∀ g, (β' g).2 = (u' g).mat 1 2 * ((T'.t g 2)⁻¹ : B'ˣ)` using `fun g => by`.

Rewrite using `[c'.mat]`. Simplify using `[triM]`. Establish `e3 : ∀ g, γ' g = (u' g).mat 0 2 * ((T'.t g 2)⁻¹ : B'ˣ) - p h * (β' g).1 * (β' g).2` using `fun g => by`. Rewrite using `[c'.mat]`. Simplify using `[triM]`.

Establish `c1 : Continuous fun g => (β' g).1`. Simplify using `only [e1]`. Conclude with `(cu' 0 1).mul (hT'.cont_inv 1)`. Establish `c2 : Continuous fun g => (β' g).2`. Simplify using `only [e2]`.

Conclude with `(cu' 1 2).mul (hT'.cont_inv 2)`. Establish `cβ' : Continuous β'` using `c1.prodMk c2`. Establish `cγ' : Continuous γ'`. Rewrite using `[funext e3]`. Conclude with `((cu' 0 2).mul (hT'.cont_inv 2)).sub ((continuous_const.mul c1).mul c2)`.

Establish `β0' : ∀ g, π' (β' g).1 = 0` using `fun g => by`. Rewrite using `[e1, map_mul, red', if_neg (by decide), zero_mul]`. Establish `fβ' : β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1`. Take `⟨ρ, hρ, hcr⟩` from `hu'.cr`. Use `(UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π' hπ' T' hT' β' ⟨cβ', zβ'⟩).2 ?_` and prove the remaining obligations.

Use `UpperTheory.isCrystalline_triangular_iff_of_charData D.HL.subtype hD.isOpen.isOpenEmbedding_subtypeVal π' hπ' (hT'.chars hD) _ _ (fun g => γ' g + p h * (β' g).1 * (β' g).2) ρ (by fun_prop) (by fun_prop) (by fun_prop) (fun g => ?_) hcr` and prove the remaining obligations. Rewrite using `[hρ]`. Conclude with `c'.mat g`. Take `⟨T, hT, hTp⟩` from `UpperTheory.exists_torus_lift_to_nilpotent_thickening hD π hπ π' hπ' p hp hpπ T' hT'`. Take `⟨β, fβ, hβp⟩` from `UpperTheory.torsionDatum_finiteCocycles_baseChange hP hD π hπ π' hπ' p hp T T' hT hT' hTp β' fβ'`.

Establish `cβ : Continuous β` using `fβ.1.1`. Establish `β0 : ∀ g, π (β g).1 = 0` using `fun g => by rw [← hππ, (hβp g).1, β0']`. Take `⟨γ, u, cγ, gγ, cu, hu⟩` from `gamCr hP hD π hπ T hT h hh β fβ β0`. Establish `push : ∀ (γ : GQ l → B) (u : GQ l →* GG 3 B), T.Coord h β γ u → T'.Coord (p h) β' (fun g => p (γ g)) ((GG.map (p : B →+* B')).comp u)` using `fun γ u c => ⟨fun g => c.right g, fun g => by`. Rewrite using `[MonoidHom.comp_apply, GG.map_mat, c.mat, triM_map (p : B →+* B') _ _ (hTp g)]`.

Simplify using `only [RingHom.coe_coe, map_add, map_mul, (hβp g).1, (hβp g).2]⟩`. Establish `hq : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B')` using `fun g i j => by`. Establish `: ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i` using `fun i => Units.ext (hTp g i)`. Rewrite using `[← this, ← this, ← _root_.map_div]`. Both sides reduce to the same expression.

Establish `gp : T'.IsGam (p h) β' (fun g => p (γ g))` using `fun g g' => by`. Simplify using `only [gγ g g', omg, Tor.adjointSuperdiagRep_apply, Tor.χ2_apply]`. Apply the tactic sequence `split_ifs <;> simp only [map_add, map_mul, map_sub, map_neg, map_intCast, hq, (hβp _).1, (hβp _).2]`. Establish `cmat : ∀ (γ : GQ l → B) (u : GQ l →* GG 3 B), Continuous γ → T.Coord h β γ u → Continuous fun g => (u g).mat` using `fun γ u cγ c => by`. Simplify using `only [c.mat]`.

Conclude with `continuous_triM hT.cont (by fun_prop) (by fun_prop) (by fun_prop)`. Establish `hδ'` using `(gamDiff hP hD π' hπ' T' hT' (p h) β' (fun g => p (γ g)) γ' _ u' cβ' (cp.comp cγ) cγ' β0' gp gγ' (push γ u cu) c' (lcr_map (p.restrictScalars ℚ_[l]) hp hD.isOpen (cmat γ u cγ cu) hu)).1 hu'.cr`. Take `⟨δ, fδ, hδp⟩` from `UpperTheory.torsionDatum_finiteCocycles_compare hP hD π hπ π' hπ' p hp T T' hT hT' hTp _ hδ'`. Establish `g2` using `gam_add gγ fδ.1`. Take `⟨v, cv⟩` from `UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + δ) fβ.1.2 g2`.

Establish `c2 : Continuous (γ + δ)` using `cγ.add fδ.1.1`. Establish `hv : (GG.map (p : B →+* B')).comp v = u'`. Use `MonoidHom.ext fun g => gg_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[(push _ v cv).mat, c'.mat]`. Simplify using `[hδp]`.

Rewrite using `[(push _ v cv).right, c'.right]`. Use `⟨v, ⟨⟨cv.right, ?_, fun a b => (cmat _ v c2 cv).matrix_elem a b, ?_⟩, fun g a b hab => ?_⟩, hv⟩` and prove the remaining obligations. Rewrite using `[← hu'.red, ← hv]`. Use `MonoidHom.ext fun g => gg_ext ?_ rfl` and prove the remaining obligations. Use extensionality with `a b`.

Conclude with `(hππ _).symm`. Conclude with `(gamDiff hP hD π hπ T hT h β γ (γ + δ) u v cβ cγ c2 β0 gγ g2 cu cv hu).2 (by simpa using fδ)`. Apply the tactic sequence `rw [cv.mat] revert hab fin_cases a <;> fin_cases b <;> simp [triM, wt, wt1]`.
-/
theorem UpperTheory.V.Loc.triLift :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ u' : GQ l →* GG 3 B', D.InDtri (π' : B' →+* E) u' → ∃ u : GQ l →* GG 3 B, D.InDtri (π : B →+* E) u ∧ (GG.map (p : B →+* B')).comp u = u' := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpπ u' hu'
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have cp : Continuous p := IsModuleTopology.continuous_of_linearMap (p.restrictScalars ℚ_[l]).toLinearMap
  have cπ' : Continuous π' := IsModuleTopology.continuous_of_linearMap (π'.restrictScalars ℚ_[l]).toLinearMap
  have hππ : ∀ b, π' (p b) = π b := fun b => AlgHom.congr_fun hpπ b
  set Ψ : GQ l →* Eˣ := (Units.map (algebraMap O E : O →* E)).comp D.Ψ with hΨ
  have hpow : ∀ g i, algebraMap O E ((D.Ψ g ^ wt1 i : Oˣ) : O) = ((Ψ g ^ wt1 i : Eˣ) : E) := fun g i => by
    rw [hΨ, MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O E : O →* E))]
    rfl
  have red' : ∀ g a b, π' ((u' g).mat a b) = if a = b then ((Ψ g ^ wt1 a : Eˣ) : E) else 0 := fun g a b => by
    have := congrFun (congrFun (congrArg GG.mat (DFunLike.congr_fun hu'.red g)) a) b
    refine this.trans ?_
    change algebraMap O E (Matrix.diagonal (fun i => ((D.Ψ g ^ wt1 i : Oˣ) : O)) a b) = _
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hpow g a
    · exact map_zero _
  have cu' : ∀ a b, Continuous fun g => (u' g).mat a b := hu'.cont
  have hD : TriDat D.η Ψ D.HL D.e := triDat D E (by
    have : (fun g => algebraMap O E (D.Ψ g)) = fun g => π' ((u' g).mat 0 0) := funext fun g => by
      rw [red', if_pos rfl, ← hpow]
      simp [wt1]
    rw [this]
    exact cπ'.comp (cu' 0 0))
  haveI := hD.normal
  set h : B := algebraMap E B 2⁻¹ with hh0
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have hh : 2 * h = 1 := by
    rw [hh0, ← map_ofNat (algebraMap E B) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hh' : 2 * p h = 1 := by
    have := congrArg p hh
    rwa [map_mul, map_ofNat, map_one] at this
  obtain ⟨T', β', γ', c', zβ', gγ'⟩ := UpperTheory.exists_torus_coords_of_unipotent (p h) hh' u' hu'.mult hu'.tri
  have d' : ∀ g i, (T'.t g i : B') = (u' g).mat i i := fun g i => by
    rw [c'.mat]
    fin_cases i <;> rfl
  have ct' : ∀ i, Continuous fun g => (T'.t g i : B') := fun i => by
    simp only [d']
    exact cu' i i
  have hT' : T'.Good π' Ψ :=
    { cont := ct'
      cont_inv := fun i => UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => T'.t g i) (ct' i)
      ine := fun g hg i => by
        rw [d', triDiag D E B' π' hπ' u' hu' g hg i, IsScalarTower.algebraMap_apply O E B', ← hpow]
        rfl
      red := fun g i => by rw [d', red', if_pos rfl] }
  have e1 : ∀ g, (β' g).1 = (u' g).mat 0 1 * ((T'.t g 1)⁻¹ : B'ˣ) := fun g => by
    rw [c'.mat]
    simp [triM]
  have e2 : ∀ g, (β' g).2 = (u' g).mat 1 2 * ((T'.t g 2)⁻¹ : B'ˣ) := fun g => by
    rw [c'.mat]
    simp [triM]
  have e3 : ∀ g, γ' g = (u' g).mat 0 2 * ((T'.t g 2)⁻¹ : B'ˣ) - p h * (β' g).1 * (β' g).2 := fun g => by
    rw [c'.mat]
    simp [triM]
  have c1 : Continuous fun g => (β' g).1 := by
    simp only [e1]
    exact (cu' 0 1).mul (hT'.cont_inv 1)
  have c2 : Continuous fun g => (β' g).2 := by
    simp only [e2]
    exact (cu' 1 2).mul (hT'.cont_inv 2)
  have cβ' : Continuous β' := c1.prodMk c2
  have cγ' : Continuous γ' := by
    rw [funext e3]
    exact ((cu' 0 2).mul (hT'.cont_inv 2)).sub ((continuous_const.mul c1).mul c2)
  have β0' : ∀ g, π' (β' g).1 = 0 := fun g => by
    rw [e1, map_mul, red', if_neg (by decide), zero_mul]
  have fβ' : β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1 := by
    obtain ⟨ρ, hρ, hcr⟩ := hu'.cr
    refine (UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem hD π' hπ' T' hT' β' ⟨cβ', zβ'⟩).2 ?_
    refine UpperTheory.isCrystalline_triangular_iff_of_charData D.HL.subtype hD.isOpen.isOpenEmbedding_subtypeVal π' hπ' (hT'.chars hD) _ _
      (fun g => γ' g + p h * (β' g).1 * (β' g).2) ρ (by fun_prop) (by fun_prop) (by fun_prop) (fun g => ?_) hcr
    rw [hρ]
    exact c'.mat g
  obtain ⟨T, hT, hTp⟩ := UpperTheory.exists_torus_lift_to_nilpotent_thickening hD π hπ π' hπ' p hp hpπ T' hT'
  obtain ⟨β, fβ, hβp⟩ := UpperTheory.torsionDatum_finiteCocycles_baseChange hP hD π hπ π' hπ' p hp T T' hT hT' hTp β' fβ'
  have cβ : Continuous β := fβ.1.1
  have β0 : ∀ g, π (β g).1 = 0 := fun g => by rw [← hππ, (hβp g).1, β0']
  obtain ⟨γ, u, cγ, gγ, cu, hu⟩ := gamCr hP hD π hπ T hT h hh β fβ β0
  have push : ∀ (γ : GQ l → B) (u : GQ l →* GG 3 B), T.Coord h β γ u →
      T'.Coord (p h) β' (fun g => p (γ g)) ((GG.map (p : B →+* B')).comp u) := fun γ u c =>
    ⟨fun g => c.right g, fun g => by
      rw [MonoidHom.comp_apply, GG.map_mat, c.mat, triM_map (p : B →+* B') _ _ (hTp g)]
      simp only [RingHom.coe_coe, map_add, map_mul, (hβp g).1, (hβp g).2]⟩
  have hq : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B') := fun g i j => by
    have : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (hTp g i)
    rw [← this, ← this, ← _root_.map_div]
    rfl
  have gp : T'.IsGam (p h) β' (fun g => p (γ g)) := fun g g' => by
    simp only [gγ g g', omg, Tor.adjointSuperdiagRep_apply, Tor.χ2_apply]
    split_ifs <;> simp only [map_add, map_mul, map_sub, map_neg, map_intCast, hq, (hβp _).1, (hβp _).2]
  have cmat : ∀ (γ : GQ l → B) (u : GQ l →* GG 3 B), Continuous γ → T.Coord h β γ u →
      Continuous fun g => (u g).mat := fun γ u cγ c => by
    simp only [c.mat]
    exact continuous_triM hT.cont (by fun_prop) (by fun_prop) (by fun_prop)
  have hδ' := (gamDiff hP hD π' hπ' T' hT' (p h) β' (fun g => p (γ g)) γ' _ u' cβ' (cp.comp cγ) cγ' β0' gp gγ'
    (push γ u cu) c' (lcr_map (p.restrictScalars ℚ_[l]) hp hD.isOpen (cmat γ u cγ cu) hu)).1 hu'.cr
  obtain ⟨δ, fδ, hδp⟩ := UpperTheory.torsionDatum_finiteCocycles_compare hP hD π hπ π' hπ' p hp T T' hT hT' hTp _ hδ'
  have g2 := gam_add gγ fδ.1
  obtain ⟨v, cv⟩ := UpperTheory.exists_unipotent_from_torus_coords T h hh β (γ + δ) fβ.1.2 g2
  have c2 : Continuous (γ + δ) := cγ.add fδ.1.1
  have hv : (GG.map (p : B →+* B')).comp v = u' := by
    refine MonoidHom.ext fun g => gg_ext ?_ ?_
    · rw [(push _ v cv).mat, c'.mat]
      simp [hδp]
    · rw [(push _ v cv).right, c'.right]
  refine ⟨v, ⟨⟨cv.right, ?_, fun a b => (cmat _ v c2 cv).matrix_elem a b, ?_⟩, fun g a b hab => ?_⟩, hv⟩
  · rw [← hu'.red, ← hv]
    refine MonoidHom.ext fun g => gg_ext ?_ rfl
    ext a b
    exact (hππ _).symm
  · exact (gamDiff hP hD π hπ T hT h β γ (γ + δ) u v cβ cγ c2 β0 gγ g2 cu cv hu).2 (by simpa using fδ)
  · rw [cv.mat]
    revert hab
    fin_cases a <;> fin_cases b <;> simp [triM, wt, wt1]
