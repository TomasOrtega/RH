import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead MonObj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hw : v.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ))` using `Over.w v`. Establish `u0` using `GlobalTheory.ShFam.Hor.LogCh.PushKer.unit_comp hψ`. Establish `u1` using `GlobalTheory.ShFam.Hor.LogCh.PushKer.one_left xc t.G`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (η[A]).left` using `h`. Use `⟨by rw [Category.assoc, hψ.1.w, ← Category.assoc, hw], ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, h', u0, u1]`. Introduce `h show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (η[A]).left`. Apply `hψ.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc]`. Conclude with `h.2.trans (u1.trans u0.symm)`. Establish `a : η[A].left ≫ A.hom = 𝟙 _` using `Over.w η[A]`. Rewrite using `[Category.assoc, hw, a, ← Spec.map_comp]`. Use `Eq.trans ?_ (Spec.map_id (CommRingCat.of ℂ))` and prove the remaining obligations.

Use `congr 1`.
-/
theorem UpperTheory.isTangent_iff_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {xc : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {ψ : A.left ⟶ t.G.left}
    (hψ : IsGrpPullback A t.G xc ψ) (v : epsR ℂ ⟶ A) : Geo.Tor.IsTangent v ↔ IsTanAtG t xc (v.left ≫ ψ) := by
  have hw : v.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  have u0 := GlobalTheory.ShFam.Hor.LogCh.PushKer.unit_comp hψ
  have u1 := GlobalTheory.ShFam.Hor.LogCh.PushKer.one_left xc t.G
  constructor
  · intro h
    have h' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (η[A]).left := h
    refine ⟨by rw [Category.assoc, hψ.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc, h', u0, u1]
  · intro h
    show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (η[A]).left
    apply hψ.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (u1.trans u0.symm)
    · have a : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hw, a, ← Spec.map_comp]
      refine Eq.trans ?_ (Spec.map_id (CommRingCat.of ℂ))
      congr 1

/- English proof (translation)
Introduce `E _ _ _ H X t xc Q ψ hψ hL g u Hm χ hAH`. Take `⟨Ef, hEf, -, -, t1, t2, hW⟩` from `GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH`. Set `T : Over (Sp ℂ)` to `MonoidalCategory.tensorUnit (Over (Sp ℂ))`. Set `τ : Over.mk xc ⟶ Over.mk (T.hom ≫ xc)` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))`. Set `β` to `GlobalTheory.UU.toBaseHom (hw := hψ.1.w) (GlobalTheory.TowerAlg.toBase_mul hψ) T`.

Establish `hinj : Function.Injective β` using `fun a b e => Over.OverMorphism.ext (hψ.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))`. Set `exx : (Fin g → ℂ) → (Over.mk xc ⟶ t.G)` to `fun z => τ ≫ β (u.ex z)`. Establish `hl : (fun z => (exx z).left) = fun z => (show Sp ℂ ⟶ Q.A.left from (u.ex z).left) ≫ ψ`. Use function extensionality and compare the values at `fun z => Category.id_comp _`. Establish `hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Q.A.left from (u.ex z).left))` using `fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f`.

Establish `hol'` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol ψ`. Establish `h0 : u.ex 0 = η[Q.A]`. Rewrite using `[(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]`. Establish `dv : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ Q.A), Geo.Tor.IsTangent v → u.IsDiff w v → IsDerivAt0 (fun z => (exx z).left) w (v.left ≫ ψ)` using `fun w v hv hd => by`. Rewrite using `[hl]`.

Use `ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom ⟨?_, hd⟩ ψ` and prove the remaining obligations. Simplify using `only [h0]`. Conclude with `hv`. Establish `vd : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ Q.A), IsDerivAt0 (fun z => (exx z).left) w (v.left ≫ ψ) → u.IsDiff w v` using `fun w v hd => by`. Rewrite `hd` using `[hl]`.

Conclude with `(GlobalTheory.TrueCx.TorFrHolo.isDerivAt0_of_cart hψ.1 (𝟙 _) (fun z => Over.w (u.ex z)) hol' ((Over.w v).trans (Category.comp_id _).symm) hd).2`. Establish `ker : ∀ z, exx z = 1 ↔ z ∈ u.Λ` using `fun z => by`. Rewrite using `[← u.ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_one]`. Establish `: IsIso τ` using `by haveI : IsIso ((Over.forget _).map τ) := inferInstanceAs (IsIso (𝟙 _))`. Conclude with `isIso_of_reflects_iso τ (Over.forget _)`. Rewrite using `[← cancel_epi τ, MonObj.comp_one]`.

Conclude with `h`. Introduce `h show τ ≫ β (u.ex z) = 1`. Rewrite using `[h, map_one, MonObj.comp_one]`. Use `⟨exx, ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩, hl ▸ hol', ⟨fun v w hv hw => ?_, ?_⟩, dv⟩` and prove the remaining obligations. Use `show τ ≫ β (u.ex (a + b)) = _`.

Rewrite using `[u.ex_add, map_mul, MonObj.comp_mul]`. Take `⟨v, ⟨hv, hd⟩, -⟩` from `t2 w`. Conclude with `⟨v.left ≫ ψ, ⟨(UpperTheory.isTangent_iff_pullback t hψ v).1 hv, dv w v hv hd⟩, fun v' h' => ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique h'.2 (dv w v hv hd)⟩`. Set `v' : epsR ℂ ⟶ Q.A` to `Over.homMk (hψ.1.lift v _ hv.1) (hψ.1.lift_snd _ _ _)`. Establish `e : v'.left ≫ ψ = v` using `hψ.1.lift_fst _ _ _`.

Rewrite `hv`, the goal using `[← e]`. Establish `ht` using `(UpperTheory.isTangent_iff_pullback t hψ v').2 hv`. Take `⟨w, hw, hw'⟩` from `t1 v' ht`. Conclude with `⟨w, dv w v' ht hw, fun w' h' => hw' w' (vd w' v' h')⟩`. Conclude with `⟨Ef ⟨v, (ker v).1 hv⟩ ⟨w, (ker w).1 hw⟩, (hEf ⟨v, (ker v).1 hv⟩ ⟨w, (ker w).1 hw⟩).symm⟩`.

Introduce `k v w ζ hk hv hw hζ`. Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `hv'` using `(ker v).1 hv`. Establish `hw'` using `(ker w).1 hw`. Establish `w₁` using `hW k ⟨v, hv'⟩ ⟨w, hw'⟩ ζ hk (by`.

Rewrite using `[hζ, ← hEf ⟨v, hv'⟩ ⟨w, hw'⟩]`. Use the proof step `norm_cast)`. Establish `tors : ∀ d ∈ u.Λ, β (u.ex ((k : ℂ)⁻¹ • d)) ^ k = 1` using `fun d hd => by`. Establish `hpow : ∀ (n : ℕ) (z : Fin g → ℂ), u.ex z ^ n = u.ex (n • z)` using `fun n z => by`. Proceed by induction on `n with`.

Consider the case `zero => simpa using ((u.ker 0).2 (zero_mem _)).symm`. Consider the case `succ n ih => rw [pow_succ, ih, ← u.ex_add, succ_nsmul]`. Establish `e : k • ((k : ℂ)⁻¹ • d) = d`. Use extensionality with `j`. Simplify using `[hk']`.

Rewrite using `[← map_pow, hpow, e, (u.ker d).2 hd, map_one]`. Take `⟨ζ', hζ', -⟩` from `GlobalTheory.UU.existsUnique_cubWeil t.cub (tors v hv') (tors w hw')`. Establish `hpr : IsProper (Limits.pullback.snd t.G.hom xc)`. Use `Q.isAb.proper` as an intermediate fact. Rewrite using `[← hψ.1.isoPullback_inv_snd]`.

Use `infer_instance`. Establish `w₂` using `GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper xc t.G t.semi hpr t.cub k T _ _ ζ' hζ'`. Establish `w₃` using `(GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G Q.A xc ψ t.PP.L Q.L t.PP.isLB Q.isLB hψ (by exact hL.symm) T k _ _ _ _ ζ' rfl rfl).2 w₂`. Take `rfl : ζ' = unitOn ζ` from `GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.SemiRigid.globalFns Q.isAb Q.isLB w₃ w₁`. Establish `h₄` using `hζ'.comp τ`.

Establish `e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ`. Establish `e₃ : τ.left = 𝟙 (Sp ℂ)` using `rfl`. Use `ext`. Simplify using `only [e₃]`. Apply the tactic sequence `first | rfl | simp | (erw [Scheme.Hom.id_appTop]; rfl)`.

Rewrite `h₄` using `[e₂]`. Conclude with `h₄`.
-/
theorem UpperTheory.exists_exponential_uniformization :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (xc : Sp ℂ ⟶ X) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ t.G.left), IsGrpPullback Q.A t.G xc ψ → LBIso (t.PP.L.pull ψ) Q.L → ∀ (g : ℕ) (u : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ exx : (Fin g → ℂ) → (Over.mk xc ⟶ t.G), GlobalTheory.ShFam.Hor.LogCh.IsExpAt t xc exx ∧ IsHolTo Set.univ (fun w => (exx w).left) ∧ ((∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ))) ∧ ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ Q.A), Geo.Tor.IsTangent v → u.IsDiff w v → IsDerivAt0 (fun z => (exx z).left) w (v.left ≫ ψ) := by
  intro E _ _ _ H X t xc Q ψ hψ hL g u Hm χ hAH
  obtain ⟨Ef, hEf, -, -, t1, t2, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let T : Over (Sp ℂ) := MonoidalCategory.tensorUnit (Over (Sp ℂ))
  let τ : Over.mk xc ⟶ Over.mk (T.hom ≫ xc) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let β := GlobalTheory.UU.toBaseHom (hw := hψ.1.w) (GlobalTheory.TowerAlg.toBase_mul hψ) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (hψ.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  let exx : (Fin g → ℂ) → (Over.mk xc ⟶ t.G) := fun z => τ ≫ β (u.ex z)
  have hl : (fun z => (exx z).left) = fun z => (show Sp ℂ ⟶ Q.A.left from (u.ex z).left) ≫ ψ :=
    funext fun z => Category.id_comp _
  have hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Q.A.left from (u.ex z).left)) :=
    fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f
  have hol' := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol ψ
  have h0 : u.ex 0 = η[Q.A] := by
    rw [(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  have dv : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ Q.A), Geo.Tor.IsTangent v → u.IsDiff w v →
      IsDerivAt0 (fun z => (exx z).left) w (v.left ≫ ψ) := fun w v hv hd => by
    rw [hl]
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom ⟨?_, hd⟩ ψ
    simp only [h0]
    exact hv
  have vd : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ Q.A),
      IsDerivAt0 (fun z => (exx z).left) w (v.left ≫ ψ) → u.IsDiff w v := fun w v hd => by
    rw [hl] at hd
    exact (GlobalTheory.TrueCx.TorFrHolo.isDerivAt0_of_cart hψ.1 (𝟙 _) (fun z => Over.w (u.ex z)) hol'
      ((Over.w v).trans (Category.comp_id _).symm) hd).2
  have ker : ∀ z, exx z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [← u.ker]
    constructor
    · intro h
      apply hinj
      rw [map_one]
      have : IsIso τ := by
        haveI : IsIso ((Over.forget _).map τ) := inferInstanceAs (IsIso (𝟙 _))
        exact isIso_of_reflects_iso τ (Over.forget _)
      rw [← cancel_epi τ, MonObj.comp_one]
      exact h
    · intro h
      show τ ≫ β (u.ex z) = 1
      rw [h, map_one, MonObj.comp_one]
  refine ⟨exx, ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩, hl ▸ hol', ⟨fun v w hv hw => ?_, ?_⟩, dv⟩
  · show τ ≫ β (u.ex (a + b)) = _
    rw [u.ex_add, map_mul, MonObj.comp_mul]
  · obtain ⟨v, ⟨hv, hd⟩, -⟩ := t2 w
    exact ⟨v.left ≫ ψ, ⟨(UpperTheory.isTangent_iff_pullback t hψ v).1 hv, dv w v hv hd⟩,
      fun v' h' => ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique h'.2 (dv w v hv hd)⟩
  · let v' : epsR ℂ ⟶ Q.A := Over.homMk (hψ.1.lift v _ hv.1) (hψ.1.lift_snd _ _ _)
    have e : v'.left ≫ ψ = v := hψ.1.lift_fst _ _ _
    rw [← e] at hv ⊢
    have ht := (UpperTheory.isTangent_iff_pullback t hψ v').2 hv
    obtain ⟨w, hw, hw'⟩ := t1 v' ht
    exact ⟨w, dv w v' ht hw, fun w' h' => hw' w' (vd w' v' h')⟩
  · exact ⟨Ef ⟨v, (ker v).1 hv⟩ ⟨w, (ker w).1 hw⟩, (hEf ⟨v, (ker v).1 hv⟩ ⟨w, (ker w).1 hw⟩).symm⟩
  · intro k v w ζ hk hv hw hζ
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hv' := (ker v).1 hv
    have hw' := (ker w).1 hw
    have w₁ := hW k ⟨v, hv'⟩ ⟨w, hw'⟩ ζ hk (by
      rw [hζ, ← hEf ⟨v, hv'⟩ ⟨w, hw'⟩]; norm_cast)
    have tors : ∀ d ∈ u.Λ, β (u.ex ((k : ℂ)⁻¹ • d)) ^ k = 1 := fun d hd => by
      have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), u.ex z ^ n = u.ex (n • z) := fun n z => by
        induction n with
        | zero => simpa using ((u.ker 0).2 (zero_mem _)).symm
        | succ n ih => rw [pow_succ, ih, ← u.ex_add, succ_nsmul]
      have e : k • ((k : ℂ)⁻¹ • d) = d := by
        ext j
        simp [hk']
      rw [← map_pow, hpow, e, (u.ker d).2 hd, map_one]
    obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil t.cub (tors v hv') (tors w hw')
    have hpr : IsProper (Limits.pullback.snd t.G.hom xc) := by
      have := Q.isAb.proper
      rw [← hψ.1.isoPullback_inv_snd]
      infer_instance
    have w₂ := GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper xc t.G t.semi hpr t.cub k T _ _ ζ' hζ'
    have w₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G Q.A xc ψ t.PP.L Q.L t.PP.isLB Q.isLB hψ
      (by exact hL.symm) T k _ _ _ _ ζ' rfl rfl).2 w₂
    obtain rfl : ζ' = unitOn ζ := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.SemiRigid.globalFns Q.isAb Q.isLB w₃ w₁
    have h₄ := hζ'.comp τ
    have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
      have e₃ : τ.left = 𝟙 (Sp ℂ) := rfl
      ext
      simp only [e₃]
      first | rfl | simp | (erw [Scheme.Hom.id_appTop]; rfl)
    rw [e₂] at h₄
    exact h₄
