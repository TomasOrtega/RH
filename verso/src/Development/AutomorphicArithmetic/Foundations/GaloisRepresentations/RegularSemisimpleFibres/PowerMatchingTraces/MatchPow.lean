import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]`. Conclude with `h _`.
-/
private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

/- English proof (translation)
Establish `hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E`. Rewrite using `[← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]`. Use `clear hw`. Take `⟨w, hwv⟩` from `w`. Take `rfl : GroundTheory.Global.AdeleBaseChange.below F w = v` from `(GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hwv`.

Use `haveI := hwv`. Set `y : (w.adicCompletion E)ˣ` to `Units.map (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).toMonoidHom x`. Establish `hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x ^ Module.finrank F E`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GroundTheory.LocalField.coe_normUnits]`.

Express the relevant statement in the definitionally equal form `Algebra.norm _ (algebraMap _ (w.adicCompletion E) (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F)) = _`. Rewrite using `[Algebra.norm_algebraMap, hrk, Units.val_pow_eq_pow_val]`. Establish `h2` using `GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y`. Rewrite `h2` using `[hn]`. Establish `h3` using `GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)`.

Rewrite `h3` using `[h2]`. Establish `h4` using `congrArg Subtype.val h3`. Rewrite `h4` using `[GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, Units.val_pow_eq_pow_val, norm_pow]`. Conclude with `h4.symm`.
-/
private theorem norm_incl {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (x : (v.adicCompletion F)ˣ) :
    ‖completionMap v w.1 (x : v.adicCompletion F)‖ = ‖(x : v.adicCompletion F)‖ ^ Module.finrank F E := by
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  clear hw
  obtain ⟨w, hwv⟩ := w
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hwv
  haveI := hwv
  let y : (w.adicCompletion E)ˣ := Units.map (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).toMonoidHom x
  have hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x ^ Module.finrank F E := by
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    change Algebra.norm _ (algebraMap _ (w.adicCompletion E) (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F)) = _
    rw [Algebra.norm_algebraMap, hrk, Units.val_pow_eq_pow_val]
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h2] at h3
  have h4 := congrArg Subtype.val h3
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding,
    Units.val_pow_eq_pow_val, norm_pow] at h4
  exact h4.symm

/- English proof (translation)
Establish `hfix : w.1 = σ • w.1` using `(congrArg Subtype.val (hw (σ • w))).symm`. Establish `h0 : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w)`. Take `⟨t, rfl⟩` from `(tensorEquiv' E v).surjective y`. Establish `h1 : galFin σ v (tensorEquiv' E v t) = tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t)`. Simplify using `[galFin, galOf]`.

Rewrite using `[h1]`. Use `clear h1`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]`.

Consider the case `tmul x a`. Rewrite using `[Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]`. Use `congr 1`. Conclude with `(galEquiv_algebraMap v σ w.1 w.1 hfix x).symm`. Conclude with `((galEquiv v σ w.1 w.1 hfix).commutes a).symm`.

Rewrite using `[h0]`. Establish `hk : ∀ x : E, ‖algebraMap E (w.1.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖`. Introduce `x`. Establish `key : ∀ u : HeightOneSpectrum (𝓞 E), u = σ • w.1 → ‖algebraMap E (u.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖`. Introduce and unpack `_ rfl`.

Conclude with `norm_algebraMap_smul σ w.1 x`. Conclude with `key _ hfix`. Use `congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer (continuous_norm.comp (continuous_galEquiv v σ w.1 w.1 hfix)) continuous_norm ?_) (y w)` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, galEquiv_algebraMap, hk]`.
-/
private theorem norm_gal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (y : CompletionsOver E v) : ‖galFin σ v y w‖ = ‖y w‖ := by
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have h0 : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 hfix x).symm
      · exact ((galEquiv v σ w.1 w.1 hfix).commutes a).symm
  rw [h0]
  have hk : ∀ x : E, ‖algebraMap E (w.1.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
    intro x
    have key : ∀ u : HeightOneSpectrum (𝓞 E), u = σ • w.1 →
        ‖algebraMap E (u.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
      rintro _ rfl
      exact norm_algebraMap_smul σ w.1 x
    exact key _ hfix
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
    (continuous_norm.comp (continuous_galEquiv v σ w.1 w.1 hfix)) continuous_norm ?_) (y w)
  funext x
  simp only [Function.comp_apply, galEquiv_algebraMap, hk]

/- English proof (translation)
Unfold `quotInt`. Use `split_ifs with h`. Rewrite using `[← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
private theorem quotInt_mul_const {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (Φ : X → ℂ) (c : ℂ) :
    quotInt μ u j ν (fun x => Φ x * c) = quotInt μ u j ν Φ * c := by
  unfold quotInt
  split_ifs with h
  · rw [← integral_mul_const]
    congr 1
    funext x
    ring
  · simp

/- English proof (translation)
The claim follows from `(RingHom.map_det f g.val).symm`.
-/
private theorem det_mapGL {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (f : R →+* S) (g : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (mapGL n f g) : Sˣ) : S) = f ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) :=
  (RingHom.map_det f g.val).symm

/- English proof (translation)
Unfold `chiAt`. Simplify using `only [map_mul, map_inv]`. Rewrite using `[mul_comm _ (χ.loc v (Matrix.GeneralLinearGroup.det x)), mul_inv_cancel_left]`.
-/
private theorem chiAt_conj {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) (x γ : Gw n v) :
    chiAt n χ v (x⁻¹ * γ * x) = chiAt n χ v γ := by
  unfold chiAt
  simp only [map_mul, map_inv]
  rw [mul_comm _ (χ.loc v (Matrix.GeneralLinearGroup.det x)), mul_inv_cancel_left]

/- English proof (translation)
Establish `hp : ∀ (k : ℕ) (y : G), N ((θ ^ k) y) = N y`. Introduce `k y`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', hθ, ih]`.

Proceed by induction on `m with`. Consider the case `zero => simp [h0]`. Consider the case `succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, h1, ih, hp, pow_succ]`.
-/
private theorem hom_twNorm {G : Type*} [Group G] (N : G → ℝ) (h0 : N 1 = 1) (h1 : ∀ a b, N (a * b) = N a * N b)
    (θ : Monoid.End G) (hθ : ∀ y, N (θ y) = N y) (m : ℕ) (δ : G) :
    N (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = N δ ^ m := by
  have hp : ∀ (k : ℕ) (y : G), N ((θ ^ k) y) = N y := by
    intro k y
    induction k with
    | zero => rfl
    | succ k ih => rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', hθ, ih]
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, h1, ih, hp, pow_succ]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn z χ χ' h h' v w hw`. Set `N : GL (Fin n) (CompletionsOver E v) → ℝ` to `fun g => ‖((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w‖`. Establish `hN0 : N 1 = 1` using `by simp [N]`. Establish `hN1 : ∀ a b, N (a * b) = N a * N b` using `fun a b => by simp [N]`. Establish `hNθ : ∀ y, N (mapGL n (galFin σ v) y) = N y` using `fun y => by`.

Simplify using `only [N]`. Rewrite using `[det_mapGL, norm_gal σ w hw]`. Establish `hχ' : ∀ g, chiAt n χ' w.1 (GM.cmp w g) = ((N g : ℝ) : ℂ) ^ z` using `fun g => by`. Unfold `chiAt`. Rewrite using `[pow_loc h']`.

Establish `e : ((Matrix.GeneralLinearGroup.det (GM.cmp w g) : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) = ((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w` using `det_mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g`. Rewrite using `[e]`. Establish `hθ : ∀ x, chiAt n χ' w.1 (GM.cmp w (mapGL n (galFin σ v) x)) = chiAt n χ' w.1 (GM.cmp w x)` using `fun x => by`. Rewrite using `[hχ', hχ', hNθ]`. Establish `hsurj : ∀ g : Gw n w.1, ∃ g₀, GM.cmp w g₀ = g` using `fun g => by`.

Take `⟨⟨e, he⟩, -, -⟩` from `cmpIso F E n v w hw`. Conclude with `⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩`. Establish `hl : Module.finrank F E ≠ 0` using `hp.ne_zero`. Establish `hnorm : ∀ (γ : Gw n v) (δ : GL (Fin n) (CompletionsOver E v)), PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ → chiAt n χ' w.1 (GM.cmp w δ) = chiAt n χ v γ` using `fun γ δ hδ => by`. Establish `h1` using `hom_twNorm N hN0 hN1 (mapGL n (galFin σ v)) hNθ (Module.finrank F E) δ`.

Rewrite `h1` using `[hδ]`. Establish `h2 : N (mapGL n (incFin E v) γ) = ‖((Matrix.GeneralLinearGroup.det γ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ Module.finrank F E`. Simplify using `only [N]`. Rewrite using `[det_mapGL]`. Conclude with `norm_incl w hw _`.

Rewrite `h1` using `[h2]`. Establish `h3` using `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hl).1 h1`. Rewrite using `[hχ']`. Unfold `chiAt`. Rewrite using `[pow_loc h, h3]`.

Use `⟨fun s hs g => ?_, ?_⟩` and prove the remaining obligations. Take `⟨g₀, rfl⟩` from `hsurj g`. Rewrite using `[← hs g₀, hθ]`. Introduce `c φ f hm _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν`. Take `⟨ha, hb⟩` from `hm mE mF hE hF h1 h2 γ hγ ν hν`.

Establish `horb : orb mF γ ν (fun g => f g * chiAt n χ v g) = orb mF γ ν f * chiAt n χ v γ`. Unfold `orb`. Rewrite using `[← quotInt_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Use `beta_reduce`. Rewrite using `[chiAt_conj]`. Use `⟨fun δ hδ => ?_, fun hne => ?_⟩` and prove the remaining obligations. Establish `htw : twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g) * chiAt n χ' w.1 (GM.cmp w g)) = twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g)) * chiAt n χ' w.1 (GM.cmp w δ)`. Unfold `twOrb`.

Rewrite using `[← quotInt_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `beta_reduce`. Establish `e : N x⁻¹ * N x = 1` using `by rw [← hN1, inv_mul_cancel, hN0]`.

Establish `hc : N (x⁻¹ * δ * mapGL n (galFin σ v) x) = N δ`. Rewrite using `[hN1, hN1, hNθ]`. Take the linear combination `(N δ) * e`. Rewrite using `[hχ' (x⁻¹ * δ * mapGL n (galFin σ v) x), hc, ← hχ' δ]`. Rewrite using `[htw, horb, ha δ hδ, hnorm γ δ hδ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[horb, hb hne, zero_mul]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.G.matchPow :
    UpperTheory.Gal.InertialTypesAlt.G.MatchPow := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn z χ χ' h h' v w hw

  let N : GL (Fin n) (CompletionsOver E v) → ℝ := fun g =>
    ‖((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w‖
  have hN0 : N 1 = 1 := by simp [N]
  have hN1 : ∀ a b, N (a * b) = N a * N b := fun a b => by simp [N]
  have hNθ : ∀ y, N (mapGL n (galFin σ v) y) = N y := fun y => by
    simp only [N]
    rw [det_mapGL, norm_gal σ w hw]
  have hχ' : ∀ g, chiAt n χ' w.1 (GM.cmp w g) = ((N g : ℝ) : ℂ) ^ z := fun g => by
    unfold chiAt
    rw [pow_loc h']
    have e : ((Matrix.GeneralLinearGroup.det (GM.cmp w g) : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
        ((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w :=
      det_mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g
    rw [e]
  have hθ : ∀ x, chiAt n χ' w.1 (GM.cmp w (mapGL n (galFin σ v) x)) = chiAt n χ' w.1 (GM.cmp w x) := fun x => by
    rw [hχ', hχ', hNθ]
  have hsurj : ∀ g : Gw n w.1, ∃ g₀, GM.cmp w g₀ = g := fun g => by
    obtain ⟨⟨e, he⟩, -, -⟩ := cmpIso F E n v w hw
    exact ⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩
  have hl : Module.finrank F E ≠ 0 := hp.ne_zero

  have hnorm : ∀ (γ : Gw n v) (δ : GL (Fin n) (CompletionsOver E v)),
      PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ →
      chiAt n χ' w.1 (GM.cmp w δ) = chiAt n χ v γ := fun γ δ hδ => by
    have h1 := hom_twNorm N hN0 hN1 (mapGL n (galFin σ v)) hNθ (Module.finrank F E) δ
    rw [hδ] at h1
    have h2 : N (mapGL n (incFin E v) γ) =
        ‖((Matrix.GeneralLinearGroup.det γ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ Module.finrank F E := by
      simp only [N]
      rw [det_mapGL]
      exact norm_incl w hw _
    rw [h2] at h1
    have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hl).1 h1
    rw [hχ']
    unfold chiAt
    rw [pow_loc h, h3]
  refine ⟨fun s hs g => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hsurj g
    rw [← hs g₀, hθ]
  intro c φ f hm _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
  obtain ⟨ha, hb⟩ := hm mE mF hE hF h1 h2 γ hγ ν hν
  have horb : orb mF γ ν (fun g => f g * chiAt n χ v g) = orb mF γ ν f * chiAt n χ v γ := by
    unfold orb
    rw [← quotInt_mul_const]
    congr 1
    funext x
    beta_reduce
    rw [chiAt_conj]
  refine ⟨fun δ hδ => ?_, fun hne => ?_⟩
  · have htw : twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g) * chiAt n χ' w.1 (GM.cmp w g)) =
        twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g)) * chiAt n χ' w.1 (GM.cmp w δ) := by
      unfold twOrb
      rw [← quotInt_mul_const]
      congr 1
      funext x
      beta_reduce
      have e : N x⁻¹ * N x = 1 := by rw [← hN1, inv_mul_cancel, hN0]
      have hc : N (x⁻¹ * δ * mapGL n (galFin σ v) x) = N δ := by
        rw [hN1, hN1, hNθ]
        linear_combination (N δ) * e
      rw [hχ' (x⁻¹ * δ * mapGL n (galFin σ v) x), hc, ← hχ' δ]
    rw [htw, horb, ha δ hδ, hnorm γ δ hδ]
    ring
  · rw [horb, hb hne, zero_mul]
