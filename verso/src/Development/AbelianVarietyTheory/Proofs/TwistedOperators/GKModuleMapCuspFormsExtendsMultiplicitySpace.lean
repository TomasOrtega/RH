import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachMultMapEquivariantSobolevContinuStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicFormMultMapValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKMapExtensionLevelCharacterCovariantStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExt

/- English proof (translation)
Establish `h1` using `(Matrix.mem_unitaryGroup_iff').1 hg.1`. Rewrite `h1` using `[Matrix.star_eq_conjTranspose]`. Use `show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem kset_sub {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ Formalism.MainNotions.S.UJset ε := by
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  rw [Matrix.star_eq_conjTranspose] at h1
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]`.
-/
theorem conj_back {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

/- English proof (translation)
Establish `hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0` using `hX`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, Matrix.one_mul]`. Use `show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0`.

Rewrite using `[← M.fr_gram τ]`. Establish `e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) + (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) = (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ)`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.add_mul, Matrix.mul_add]`. Rewrite using `[e, hX', Matrix.zero_mul, Matrix.mul_zero]`.
-/
theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_conj_inv {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `hk : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Establish `h1 : (P⁻¹)ᴴ * Pᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]`. Express the relevant statement in the definitionally equal form `(P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← h]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = G := by rw [h1, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]`.
-/
theorem conj_mem_UH {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  change (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g) * P := by
        rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

/- English proof (translation)
Introduce `hHC hCW D θ hθ V S M J χ μ 𝓕 _ _ T₀ hT₀`. Use `existsUnique_of_exists_of_unique ?_ ?_` and prove the remaining obligations. Take `⟨U, N, hU, hTU⟩` from `GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀`. Take `⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩` from `GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU`. Use `choose π dπ hπ using hπ`.

Establish `hmem : ∀ u, T₀ u ∈ LinearMap.range ι` using `fun u => by`. Establish `ha` using `hT₀.1 u`. Take `⟨x, hx⟩` from `(hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hT₀.2.1 u, hT₀.2.2.1 u, (hTU u).2⟩`. Conclude with `⟨x, hx⟩`. Set `e` to `LinearEquiv.ofInjective ι hinj`.

Set `T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E` to `e.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)`. Establish `hT₀' : ∀ u, ι (T₀' u) = T₀ u` using `fun u => by`. Establish `h1` using `congrArg Subtype.val (e.apply_symm_apply ⟨T₀ u, hmem u⟩)`. Rewrite `h1` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h1`.

Establish `hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u)`. Introduce `τ k hk u w hw`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[(hπ τ).2.1 k (kset_sub hk), hT₀', hT₀']`. Establish `hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k` using `conj_back (M.fr_unit τ)`.

Establish `hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ`. Express the relevant statement in the definitionally equal form `M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)`. Rewrite using `[hk']`. Conclude with `hk`. Use `(hT₀.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl` and prove the remaining obligations.

Rewrite using `[hw]`. Use `show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _`. Rewrite using `[hk']`. Establish `hL : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀' (Function.update u τ w) = dπ τ X (T₀' u)`. Introduce `τ X hX u w hw`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[(hπ τ).2.2 X hX, hT₀', hT₀']`. Establish `hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X`. Use function extensionality and compare the values at `y`. Unfold `dRep`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Use `show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _`. Rewrite using `[exp_conj_inv (M.fr_unit τ), conj_back (M.fr_unit τ)]`. Conclude with `hT₀.2.2.2.2.2.2.2 τ _ (conj_mem_lieAt M τ hX) u w (by rw [hw, hd])`.

Establish `hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)`. Introduce `τ τ' hne g hg g' hg'`. Use extensionality with `x`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [ContinuousLinearMap.comp_apply]`.

Rewrite using `[(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]`. Use function extensionality and compare the values at `y`. Simplify using `only [rTr, mul_assoc]`. Conclude with `congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _ (conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))`. Take `⟨TE, hTE1, hTE2, hTE3⟩` from `GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK hL`.

Take `⟨hequiv, hcont⟩` from `GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3`. Set `T : MMap M` to `ι.compMultilinearMap TE`. Establish `hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀` using `fun v u h => by show ι (TE v) = T₀ u`. Rewrite using `[hTE1 v u h, hT₀']`. Use `⟨T, ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, GlobalTheory.T.gKMap_extension_level_character_covariant hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont, hequiv, hcont⟩, hext⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by`. Establish `h` using `(hrange (ι (TE v))).1 ⟨TE v, rfl⟩`. Conclude with `⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont`. Introduce and unpack `T T' ⟨hT, hTe⟩ ⟨hT', hT'e⟩`. Establish `hd : T - T' ∈ Mult θ M J χ` using `Submodule.sub_mem _ (Submodule.subset_span hT) (Submodule.subset_span hT')`.

Use `sub_eq_zero.1 (GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M J χ (T - T') hd fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[MultilinearMap.sub_apply, hTe v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl), hT'e v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl), sub_self]`.
-/
theorem extExists : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7,
    GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D := by
  intro hHC hCW D θ hθ V S M J χ μ 𝓕 _ _ T₀ hT₀
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
    obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
      GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
    choose π dπ hπ using hπ
    have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
      have ha := hT₀.1 u
      obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hT₀.2.1 u, hT₀.2.2.1 u, (hTU u).2⟩
      exact ⟨x, hx⟩
    let e := LinearEquiv.ofInjective ι hinj
    let T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
      e.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
    have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨T₀ u, hmem u⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    have hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
        (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
      intro τ k hk u w hw
      apply hinj
      rw [(hπ τ).2.1 k (kset_sub hk), hT₀', hT₀']
      have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := conj_back (M.fr_unit τ)
      have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
        change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
        rw [hk']; exact hk
      refine (hT₀.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
      rw [hw]
      show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
      rw [hk']
    have hL : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
        (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
        T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
      intro τ X hX u w hw
      apply hinj
      rw [(hπ τ).2.2 X hX, hT₀', hT₀']
      have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
        funext y
        unfold dRep
        congr 1
        funext t
        show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
        rw [exp_conj_inv (M.fr_unit τ), conj_back (M.fr_unit τ)]
      exact hT₀.2.2.2.2.2.2.2 τ _ (conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
    have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
        (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
      intro τ τ' hne g hg g' hg'
      ext x
      apply hinj
      simp only [ContinuousLinearMap.comp_apply]
      rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
      funext y
      simp only [rTr, mul_assoc]
      exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
        (conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
    obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK hL
    obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
      (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
    let T : MMap M := ι.compMultilinearMap TE
    have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
      show ι (TE v) = T₀ u
      rw [hTE1 v u h, hT₀']
    refine ⟨T, ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1,
      GlobalTheory.T.gKMap_extension_level_character_covariant hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont, hequiv, hcont⟩, hext⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  · rintro T T' ⟨hT, hTe⟩ ⟨hT', hT'e⟩
    have hd : T - T' ∈ Mult θ M J χ := Submodule.sub_mem _ (Submodule.subset_span hT) (Submodule.subset_span hT')
    refine sub_eq_zero.1 (GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M J χ (T - T') hd fun v hv => ?_)
    rw [MultilinearMap.sub_apply, hTe v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl),
      hT'e v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl), sub_self]

end GlobalTheory.GKExt
