import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.CharRank

open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Serre GlobalTheory.EigenSplit Matrix GlobalTheory.LieUnif
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

/- English proof (translation)
Establish `key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈ maximalIdeal R ^ (e + 1)` using `fun e => by`. Set `f` to `Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))`. Establish `: IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1))`. Establish `: Nontrivial (R ⧸ maximalIdeal R ^ (e + 1))` using `Ideal.Quotient.nontrivial_iff.2 fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))`. Conclude with `IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective`.

Use `U.smooth` as an intermediate fact. Take `⟨v', ρ', hv', hρ', hM⟩` from `ToricRank.exists_action_pullback hv hρ f`. Take `⟨w', ρB', hw', hρB', hMB⟩` from `ToricRank.exists_action_pullback hw hρB f`. Set `gc` to `U.gt e`. Use `gc.q_hom` as an intermediate fact.

Use `gc.i_hom` as an intermediate fact. Use `gc.q_flat` as an intermediate fact. Use `gc.q_surj` as an intermediate fact. Use `gc.q_affine` as an intermediate fact. Use `(H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth` as an intermediate fact.

Establish `: Smooth gc.q.left`. Use `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_` and prove the remaining obligations. Conclude with `smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this`. Set `aK` to `@Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))`. Set `MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1))` to `fun x => (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)`.

Establish `hvK` using `Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b`. Establish `hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i)) (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x)` using `fun x i => Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i`. Establish `hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i` using `⟨inferInstance, fun x => by`. Take `⟨t, ht, hi⟩` from `hl.i_lin e x`. Take `rfl` from `ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht`.

Conclude with `hi.symm⟩`. Establish `h` using `trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK) (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _) (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a (MK a) ((Linea …`. Rewrite using `[← Ideal.Quotient.eq, map_add, map_intCast, trace_map_eq, trace_map_eq, h]`. Use `(add_comm _ _).trans (congrArg _ ?_)` and prove the remaining obligations. Simplify using `[MK, latTrace, Matrix.trace]`.

Rewrite using `[← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]`. Introduce `n`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ n) (key n)`.
-/
theorem trace_of_unif_loc {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) [IsCommMonObj D.toPre.P.A]
    [Smooth D.toPre.P.A.hom] {g h r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    {w : Fin h → (epsR R ⟶ D.toPre.P.A)} (hw : IsLieBasis w)
    {ρB : O →+* Module.End R (Fin h → R)}
    (hρB : ∀ a c, prodPts (ρB a c) w = prodPts c w ≫ (ofRingAct oD.onB.toRingAct).act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (a : O) :
    LinearMap.trace R _ (ρ a) = LinearMap.trace R _ (ρB a) + (latTrace b a : R) := by
  have key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈
      maximalIdeal R ^ (e + 1) := fun e => by
    let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) := by
      have : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
        (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))
      exact IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have := U.smooth
    obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
    obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
    let gc := U.gt e
    have := gc.q_hom
    have := gc.i_hom
    have := gc.q_flat
    have := gc.q_surj
    have := gc.q_affine
    have := (H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth
    have : Smooth gc.q.left := by
      refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip
        ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_
      exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
    let aK := @Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))
    let MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1)) := fun x =>
      (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)
    have hvK := Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b
    have hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i))
        (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x) := fun x i =>
      Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i
    have hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i := ⟨inferInstance, fun x => by
      obtain ⟨t, ht, hi⟩ := hl.i_lin e x
      obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht
      exact hi.symm⟩
    have h := trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK)
      (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _)
      (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a
      (MK a) ((LinearMap.toMatrix' (ρ a))ᵀ.map f) ((LinearMap.toMatrix' (ρB a))ᵀ.map f)
      (fun c => (ConstBasis.prodPts_act hvK hMK a c).symm) (fun c => by rw [← hM, hρ']) (fun c => by rw [← hMB, hρB'])
    rw [← Ideal.Quotient.eq, map_add, map_intCast, trace_map_eq, trace_map_eq, h]
    refine (add_comm _ _).trans (congrArg _ ?_)
    simp [MK, latTrace, Matrix.trace]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  intro n
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (key n)

/- English proof (translation)
Use `letI := H.starRing`. Use `haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩`. Use `P.U.smooth` as an intermediate fact. Establish `: Smooth P.D.toPre.P.A.hom` using `P.D.toPre.P.smoothDim.smooth`. Take `⟨g, v, hv⟩` from `Chart.exists_isLieBasis t.G P.U.smooth`.

Take `⟨ρ, hρ⟩` from `LieEigen.exists_action hv t.act`. Take `⟨h, w, hw⟩` from `Chart.exists_isLieBasis P.D.toPre.P.A this`. Take `⟨ρB, hρB⟩` from `LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)`. Set `b` to `Module.finBasis ℤ P.D.toPre.X`. Establish `htr` using `trace_of_unif_loc P.U.toUnifPre P.lin hv hρ hw hρB b`.

Take `⟨v', ρ', hv', hρ', hM⟩` from `ToricRank.exists_action_pullback hv hρ f`. Take `⟨w', ρB', hw', hρB', hMB⟩` from `ToricRank.exists_action_pullback hw hρB f`. Set `aG` to `t.act.pullback (spMap f) t.G`. Set `aB` to `(ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A`. Use `haveI := Module.Finite.of_basis (Lie.basis aG hv')`.

Use `haveI := Module.Finite.of_basis (Lie.basis aB hw')`. Establish `tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a))` using `fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])`. Establish `tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a))` using `fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])`. Set `σ : (E →+* F) → 𝓞 E →+* F` to `fun i => i.comp (algebraMap (𝓞 E) E)`. Establish `hinj : Function.Injective σ` using `fun i j hij => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij`.

Establish `hσ : IsSplitting σ`. Simplify using `using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F) (isUnit_discr_of_charZero F)`. Take `⟨j, rfl⟩ : ∃ j, σ j = τ` from `⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩`. Establish `: Module.Finite (𝓞 E) P.D.toPre.X` using `.of_restrictScalars_finite ℤ _ _`. Establish `he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X), Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j)` using `fun a => Submodule.ext fun v => by rw [mem_eigenSub]; rfl`.

Establish `hm` using `mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i))) (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i))) (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by`. Establish `hT` using `trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a`. Simplify using `only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT`. Rewrite using `[← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add, map_intCast]) j`. Rewrite `hN` using `[Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]`.

Use `⟨_, ?_, hm.symm.trans hN.2⟩` and prove the remaining obligations. Rewrite using `[Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]`. Conclude with `⟨inferInstance, rfl⟩`.
-/
theorem lieMult_unif_loc {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] (f : R →+* F) (hf : Function.Injective f)
    (τ : 𝓞 E →+* F) (N : ℕ) (hN : LieMult t.act (spMap f) τ N) :
    letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif_loc P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add, map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

/- English proof (translation)
Establish `h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2` using `by rw [← map_pow, H.rt_sq]; simp`. Use `(sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left fun h => ?_` and prove the remaining obligations. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E)`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]`.

Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h2`. Establish `h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Use `congrArg (φ.comp (algebraMap (𝓞 E) E)) H.rt_sq` as an intermediate fact. Rewrite `this` using `[map_pow, map_neg, map_natCast]`. Conclude with `this`.

Rewrite `h3` using `[hr]`. Establish `h4 : r ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast h3`. Establish `h5 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[sq_nonneg r]`.
-/
theorem bar_rt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left fun h => ?_
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (φ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

/- English proof (translation)
Set `e₀ : E →ₐ[ℚ] K` to `IsAlgClosed.lift`. Set `τ₀ : 𝓞 E →+* K` to `e₀.toRingHom.comp (algebraMap (𝓞 E) E)`. Set `τ' : 𝓞 E →+* K` to `τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)`. Establish `h' : τ' H.rt = -τ₀ H.rt`. Express the relevant statement in the definitionally equal form `τ₀ (H.bar H.rt) = _`.

Rewrite using `[bar_rt_neg, map_neg]`. Establish `h0 : (τ₀ H.rt) ^ 2 = δ ^ 2` using `by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]`. Establish `hne : δ ≠ -δ` using `fun h => by`. Establish `h2 : δ = 0`. Establish `: (2 : K) * δ = 0` using `by linear_combination h`.

Conclude with `(mul_eq_zero.1 this).resolve_left two_ne_zero`. Rewrite `hδ` using `[h2]`. Establish `: (H.d : K) = 0` using `by linear_combination hδ`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast this)`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h` into its components or cases.

Conclude with `⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩`. Conclude with `⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩`.
-/
theorem exists_chars {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (δ : K) (hδ : δ ^ 2 = -(H.d : K)) :
    ∃ τ₁ τ₂ : 𝓞 E →+* K, τ₁ H.rt = δ ∧ τ₂ H.rt ≠ δ := by
  let e₀ : E →ₐ[ℚ] K := IsAlgClosed.lift
  let τ₀ : 𝓞 E →+* K := e₀.toRingHom.comp (algebraMap (𝓞 E) E)
  let τ' : 𝓞 E →+* K := τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)
  have h' : τ' H.rt = -τ₀ H.rt := by
    change τ₀ (H.bar H.rt) = _
    rw [bar_rt_neg, map_neg]
  have h0 : (τ₀ H.rt) ^ 2 = δ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]
  have hne : δ ≠ -δ := fun h => by
    have h2 : δ = 0 := by
      have : (2 : K) * δ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h2] at hδ
    have : (H.d : K) = 0 := by linear_combination hδ
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h
  · exact ⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩
  · exact ⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hCN hEt _ _`. Take `⟨hNoeth, -, -, hChar⟩` from `hCN`. Use `haveI := hNoeth`. Use `haveI := hChar`. Use `haveI := c.fin`.

Use `haveI : NumberField c.F := {}`. Take `⟨y, hy⟩` from `DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense ξ hEt.1`. Set `K` to `AlgebraicClosure (FractionRing R)`. Set `f : R →+* K` to `(algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))`. Establish `hf : Function.Injective f` using `(algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))`.

Use `haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩`. Set `x' : Sp K ⟶ Xo.XF c` to `spMap (algebraMap (FractionRing R) K) ≫ y`. Establish `hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ`. Rewrite using `[← DomFine.spMap_comp', Category.assoc, hy]`. Both sides reduce to the same expression.

Take `⟨β₀, hβ₀⟩` from `Spec.map_surjective (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)`. Establish `hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom` using `hβ₀.symm`. Establish `hdet` using `(Z.oF.geom K x' β₀.hom hβ).1`. Establish `hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K)`. Rewrite using `[← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]`.

Establish `bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N → Module.finrank (𝓞 E) P.D.toPre.X ≤ N`. Introduce `τ N hN`. Establish `h₅` using `(GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN`. Rewrite `h₅` using `[hx]`. Establish `h₆` using `(GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅`.

Take `⟨n, -, hn⟩` from `lieMult_unif_loc H R t P K f hf τ N h₆`. Use linear arithmetic over natural numbers and integers. Take `⟨τ₁, τ₂, h₁, h₂⟩` from `exists_chars H K _ hr`. Conclude with `le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))`.
-/
theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ P : PELUnif (maximalIdeal R) t, IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hCN hEt _ _
  obtain ⟨hNoeth, -, -, hChar⟩ := hCN
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    rw [← DomFine.spMap_comp', Category.assoc, hy]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.CharRank
