import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

section Lie

open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin n) R) B := g.toRingHom.toAlgebra`. Use `haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm`. Use `haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg`. Establish `hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧ ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j` using `fun m => etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by`. Rewrite using `[map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])`.

Use `choose π hπaug hπX using hπ`. Use `⟨π, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Use `etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, jetAug_comp_trunc]`.

Conclude with `hπaug (m + 1)`. Conclude with `hπaug m`. Introduce `j`. Rewrite using `[AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]`. Both sides reduce to the same expression.

Introduce `m`. Use `etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, jetAug_comp_zero]`. Conclude with `hπaug m`. Use extensionality with `s`.

Simplify using the standard rewrite rules. Introduce `j`. Rewrite using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]`. Both sides reduce to the same expression. Introduce `A _ _ aug m hJ φ' hφ'aug`.

Establish `hJn` using `nil_of_pow _ hJ`. Establish `hmem : ∀ j : Fin n, φ' (sX (S` using `B) R j) - algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by`. Introduce `j`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, ← AlgHom.comp_apply, hφ'aug, sub_self]`. Set `ψ` to `jetLift R (RingHom.ker aug) hJ (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem`.

Establish `hψaug : aug.comp ψ = jetAug R (Fin n) m` using `jet_ext fun j => by`. Rewrite using `[AlgHom.comp_apply, jetLift_zR, jetAug_zR]`. Conclude with `hmem j`. Establish `hψπ : ψ.comp (π m) = φ'`. Use `etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[← AlgHom.comp_assoc, hψaug]`. Conclude with `hπaug m`. Conclude with `hφ'aug`. Introduce `j`. Rewrite using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]`.

Use `⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ψ₂ ⟨_, h4⟩`. Apply `jet_ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[jetLift_zR]`.

Use `AlgHom.congr_fun h4 (sX R j)` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes]`. Rewrite using `[← this, add_sub_cancel_left]`.
-/
theorem algChart_of_etale {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {n : ℕ}
    (g : MvPolynomial (Fin n) R →ₐ[R] B) (hg : g.toRingHom.Etale) (ε' : B →ₐ[R] R) :
    ∃ π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m,
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε') ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = ε' →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  letI : Algebra (MvPolynomial (Fin n) R) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg
  have hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨π, ?_, ?_, ?_⟩
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ' hφ'aug
    have hJn := nil_of_pow _ hJ
    have hmem : ∀ j : Fin n, φ' (sX (S := B) R j) -
        algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩
    rintro ψ₂ ⟨_, h4⟩
    apply jet_ext
    intro j
    rw [jetLift_zR]
    have := AlgHom.congr_fun h4 (sX R j)
    rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
    rw [← this, add_sub_cancel_left]

/- English proof (translation)
Take `⟨C, g, hg⟩` from `NilCoord.exists_etale_chart G n hG`. Take `⟨π, htr, hze, huniv⟩` from `algChart_of_etale g hg (eps C)`. Use `⟨fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_pt, htr]`. Rewrite using `[spMap_pt, hze, pt_eps]`.

Introduce `A _ _ aug m hJ y hy`. Establish `hJn` using `nil_of_pow _ hJ`. Establish `hy' : spMap aug ≫ y = pt C ((Algebra.ofId R R).comp (eps C))` using `by rw [pt_eps]; exact hy`. Take `⟨φ, rfl⟩` from `exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')`. Establish `hφ : aug.comp φ = eps C`.

Use `pt_injective C ((spMap_pt C aug φ).symm.trans hy')` as an intermediate fact. Rewrite using `[this]`. Use extensionality with `b`. Both sides reduce to the same expression. Take `⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩` from `huniv A aug m hJ φ hφ`.

Use `⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ψ₂ ⟨h1, h2⟩`. Rewrite `h2` using `[spMap_pt]`. Conclude with `hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩`.
-/
theorem exists_isUnivChart {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {n : ℕ}
    (hG : SmoothOfRelativeDimension n G.hom) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G, IsUnivChart G n x := by
  obtain ⟨C, g, hg⟩ := NilCoord.exists_etale_chart G n hG
  obtain ⟨π, htr, hze, huniv⟩ := algChart_of_etale g hg (eps C)
  refine ⟨fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩
  · rw [spMap_pt, htr]
  · rw [spMap_pt, hze, pt_eps]
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    have hy' : spMap aug ≫ y = pt C ((Algebra.ofId R R).comp (eps C)) := by rw [pt_eps]; exact hy
    obtain ⟨φ, rfl⟩ := exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')
    have hφ : aug.comp φ = eps C := by
      have := pt_injective C ((spMap_pt C aug φ).symm.trans hy')
      rw [this]
      ext b
      rfl
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv A aug m hJ φ hφ
    refine ⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩
    rintro ψ₂ ⟨h1, h2⟩
    rw [spMap_pt] at h2
    exact hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_isUnivChart G hG`. Conclude with `⟨_, basis_of_chart hx⟩`.
-/
theorem exists_isLieBasis {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] {n : ℕ}
    (hG : SmoothOfRelativeDimension n G.hom) : ∃ v : Fin n → (epsR R ⟶ G), IsLieBasis v := by
  obtain ⟨x, hx⟩ := exists_isUnivChart G hG
  exact ⟨_, basis_of_chart hx⟩

end Lie

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {K : Type} [Field K]

/- English proof (translation)
Take `⟨i, hi⟩` from `h`. Use `P.isAb.smooth` as an intermediate fact. Use `isReduced_scheme_of_smooth_of_isIntegrallyClosed K P.A.hom` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, z ∈ P.A.left.basicOpen (th.f i) := by`. Assume the negation of the conclusion as `hn`.

Conclude with `hi ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, hz⟩))`. Conclude with `⟨z, Subsingleton.elim (α := PrimeSpectrum K) _ _, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hz⟩⟩`.
-/
theorem exists_mem_nonzeroLocus (P : Out.PolAV (Sp K)) (th : P.L.Sec) (h : ∃ i, th.f i ≠ 0) (s : Sp K) :
    ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th := by
  obtain ⟨i, hi⟩ := h
  have := P.isAb.smooth
  have := isReduced_scheme_of_smooth_of_isIntegrallyClosed K P.A.hom
  obtain ⟨z, hz⟩ : ∃ z, z ∈ P.A.left.basicOpen (th.f i) := by
    by_contra hn
    exact hi ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, hz⟩))
  exact ⟨z, Subsingleton.elim (α := PrimeSpectrum K) _ _, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hz⟩⟩

/- English proof (translation)
Take `⟨rig, hr⟩` from `P.rigid`. Take `⟨v, hv⟩` from `exists_isLieBasis P.A P.smoothDim`. Conclude with `⟨rig, hr, exists_mem_nonzeroLocus P th h, v, hv, rfl⟩`.
-/
theorem exists_keyIn_of_sec (P : Out.PolAV (Sp K)) (hg : 1 ≤ P.g) (th : P.L.Sec) (h : ∃ i, th.f i ≠ 0) :
    ∃ rig hr hth v hv, (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn K).P = P := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨v, hv⟩ := exists_isLieBasis P.A P.smoothDim
  exact ⟨rig, hr, exists_mem_nonzeroLocus P th h, v, hv, rfl⟩

/- English proof (translation)
Take `⟨b, hb⟩` from `principalPolarisation_exists_unique_section hT P`. Take `⟨a, -, hu⟩` from `hb b`. Establish `h : ∃ i, b.f i ≠ 0`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Conclude with `zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)`. Take `⟨rig, hr, hth, v, hv, e⟩` from `exists_keyIn_of_sec P hg b h`. Conclude with `⟨_, e⟩`.
-/
theorem exists_keyIn (hT : Out.SecTwistSt) (P : Out.PolAV (Sp K)) (hg : 1 ≤ P.g) : ∃ x : KeyIn K, x.P = P := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, -, hu⟩ := hb b
  have h : ∃ i, b.f i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)
  obtain ⟨rig, hr, hth, v, hv, e⟩ := exists_keyIn_of_sec P hg b h
  exact ⟨_, e⟩

/- English proof (translation)
Establish `e : spMap (RingHom.id R) = 𝟙 (Sp R)` using `Spec.map_id _`. Establish `e' : spMap (RingHom.id (DualNumber R)) = 𝟙 (Sp (DualNumber R))` using `Spec.map_id _`. Set `L : RigLB x.P.A` to `⟨x.P.L, x.rig, x.P.isLB, x.rig_gen⟩`. Establish `: IsMonHom (Iso.refl x.P.A).hom` using `inferInstanceAs (IsMonHom (𝟙 _))`. Use `⟨𝟙 _, by rw [e]; exact (Category.comp_id _).trans (Category.id_comp _).symm, isoPullId (idIso x.P.L) rfl, rfl, RingHom.id _, (isGrpPullback_of_iso (Iso.refl x.P.A)).congr e.symm rfl, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen x.P.isLB) rfl), isoPullId_maps (idIso_maps L) rfl e …` and prove the remaining obligations.

Establish `hj : y ∈ x.P.L.U (j PUnit.unit)` using `mem_pull.1 hy.1`. Use `(gs_appLE (𝟙 _) _ _ h (𝟙 _) y hy _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp, gs_compat x.th (𝟙 _) y hj hy.2, gs_mul _ y _ hy, gs_res _ y _ hy]`. Conclude with `congrArg (· * _) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gw_isoPullId (idIso x.P.L) rfl (𝟙 _) y _ i hj hy.2))).symm`.
-/
theorem keyPB_refl {R : Type} [CommRing R] (x : KeyIn R) : KeyPB x x (RingHom.id R) := by
  have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have e' : spMap (RingHom.id (DualNumber R)) = 𝟙 (Sp (DualNumber R)) := Spec.map_id _
  let L : RigLB x.P.A := ⟨x.P.L, x.rig, x.P.isLB, x.rig_gen⟩
  have : IsMonHom (Iso.refl x.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  refine ⟨𝟙 _, by rw [e]; exact (Category.comp_id _).trans (Category.id_comp _).symm, isoPullId (idIso x.P.L) rfl, rfl,
    RingHom.id _, (isGrpPullback_of_iso (Iso.refl x.P.A)).congr e.symm rfl,
    (isGen_iff _).2 (isoPullId_pgen (idIso_isGen x.P.isLB) rfl), isoPullId_maps (idIso_maps L) rfl e _,
    fun j i h => fn_ext fun y hy => ?_, fun _ => rfl, rfl,
    fun i => by rw [e']; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  have hj : y ∈ x.P.L.U (j PUnit.unit) := mem_pull.1 hy.1
  refine (gs_appLE (𝟙 _) _ _ h (𝟙 _) y hy _).trans ?_
  rw [Category.id_comp, gs_compat x.th (𝟙 _) y hj hy.2, gs_mul _ y _ hy, gs_res _ y _ hy]
  exact congrArg (· * _) ((gs_unit _ y _ hy _).trans
    (congrArg Units.val (gw_isoPullId (idIso x.P.L) rfl (𝟙 _) y _ i hj hy.2))).symm

/- English proof (translation)
The claim follows from `fn_ext fun y hy => by refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h y _ i (mem_pull.1 hy.1) hy.2).trans ?_) rw [gs_mul _ y _ hy, gs_res _ y _ hy] exact congrArg (· * _) (gs_unit _ y _ hy _).symm`.
-/
theorem appLE_eq_of_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (s : L.Sec)
    (s' : L'.Sec) (h : ∀ (z : X') j k, F z ∈ L.U j → z ∈ L'.U k →
      gs (𝟙 X' ≫ F) z _ (s.f j) = (gw w (𝟙 X') z j k).val * gs (𝟙 X') z _ (s'.f k))
    (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)) :
    (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
      (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i) :=
  fn_ext fun y hy => by
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback x.P.A (spMap f)`. Set `φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left` to `pullback.fst x.P.A.hom (spMap f)`. Express the relevant statement in the definitionally equal form `IsGrpPullback _ _ _ φ at h`. Establish `hL'` using `pull_isLB x.P.isLB φ`. Establish `hw` using `(isGen_iff _).1 (idIso_isGen hL')`.

Set `P' : Out.PolAV (Sp R')` to `{ A := (Over.pullback (spMap f)).obj x.P.A isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb g := x.P.g smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim L := x.P.L.pull φ isLB := hL' rigid := PolBaseChange.rigidified_pull …`. Establish `he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A` using `PolBaseChange.eSec_comm h`. Establish `hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen` using `Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A) (fun _ => he) x.rig x.rig_gen`. Take `⟨th', hth'⟩` from `sec_pull_down hw x.P.isLB hL' x.th`. Establish `sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (x.v i).left) ≫ x.P.A.hom = (epsR R').hom ≫ spMap f` using `fun i => by`.

Rewrite using `[Category.assoc, Over.w]`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.

Set `v' : Fin x.P.g → (epsR R' ⟶ P'.A)` to `fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)`. Establish `hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (x.v i).left` using `fun i => h.1.lift_fst _ _ _`. Use `x.P.isAb.smooth` as an intermediate fact. Use `⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', Chart.isLieBasis_baseChange f h x.basis hv'⟩, φ, he, idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', fun p => hr p.1 p.2, appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩` and prove the remaining obligations. Take `⟨z, hz, hz'⟩` from `x.th_ne (spMap f s)`.

Take `⟨y, rfl, hy⟩` from `Scheme.exists_preimage_of_isPullback h.1 z s hz`. Take `⟨k, hk, u⟩` from `(mem_nonzeroLocus _ _).1 hz'`. Use `⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩` and prove the remaining obligations. Establish `u₁ : IsUnit (gs φ y _ (x.th.f k))` using `by rw [gs_stalkMap φ y _ hk]; exact u.map _`. Establish `e` using `hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)`.

Rewrite `e` using `[Category.id_comp]`. Conclude with `isUnit_of_mul_isUnit_right (e ▸ u₁)`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR]`.
-/
theorem exists_keyPB {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ x' : KeyIn R', KeyPB x' x f := by
  have h := isGrpPullback_pullback x.P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left := pullback.fst x.P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB x.P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj x.P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
      g := x.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim
      L := x.P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h x.P.rigid
      sym := PolBaseChange.sym_pull h x.P.sym
      ample := relAmple_pull h.1 x.P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
      ktriv := kTriv_pull h x.P.isLB hL' hw x.P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (x.v i).left) ≫ x.P.A.hom = (epsR R').hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin x.P.g → (epsR R' ⟶ P'.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (x.v i).left := fun i => h.1.lift_fst _ _ _
  have := x.P.isAb.smooth
  refine ⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', Chart.isLieBasis_baseChange f h x.basis hv'⟩,
    φ, he, idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', fun p => hr p.1 p.2,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

/- English proof (translation)
Use `choose c hc using fun z => exists_chart hL ((u.ex z).left (default : PrimeSpectrum ℂ))`. Establish `hc'` using `fun z => (top_le_preimage_iff_mem _ _).2 (hc z)`. Use `⟨fun z => valAt' (u.ex z).left _ (s.f (c z)) / u.fr (c z) z, fun i z hi => ?_⟩` and prove the remaining obligations. Establish `hm` using `(top_le_preimage_inf _ _ _).2 ⟨hi, hc' z⟩`. Establish `e` using `congrArg (valAt' (u.ex z).left _) (s.compat i (c z))`.

Rewrite `e` using `[valAt'_mul, valAt'_map _ _ _ hm, valAt'_map _ _ _ hm]`. Use `u.fr_ne _ z (hc' z)` as an intermediate fact. Rewrite using `[e, u.fr_compat i (c z) z hm]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_isFn {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {g : ℕ} (u : HolUnif A L g) (s : L.Sec) :
    ∃ θ, u.IsFn s θ := by
  choose c hc using fun z => exists_chart hL ((u.ex z).left (default : PrimeSpectrum ℂ))
  have hc' := fun z => (top_le_preimage_iff_mem _ _).2 (hc z)
  refine ⟨fun z => valAt' (u.ex z).left _ (s.f (c z)) / u.fr (c z) z, fun i z hi => ?_⟩
  have hm := (top_le_preimage_inf _ _ _).2 ⟨hi, hc' z⟩
  have e := congrArg (valAt' (u.ex z).left _) (s.compat i (c z))
  rw [valAt'_mul, valAt'_map _ _ _ hm, valAt'_map _ _ _ hm] at e
  have := u.fr_ne _ z (hc' z)
  rw [e, u.fr_compat i (c z) z hm]
  field_simp

/- English proof (translation)
Use `u.discrete` as an intermediate fact. Establish `: IsZLattice ℝ u.Λ` using `⟨u.full⟩`. Conclude with `⟨_, ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ u.Λ) _⟩`.
-/
theorem exists_isAddFundamentalDomain {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    ∃ Fd, MeasureTheory.IsAddFundamentalDomain u.Λ Fd (MeasureTheory.volume : MeasureTheory.Measure (Fin g → ℂ)) := by
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  exact ⟨_, ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ u.Λ) _⟩

end GlobalTheory.KeyPow
