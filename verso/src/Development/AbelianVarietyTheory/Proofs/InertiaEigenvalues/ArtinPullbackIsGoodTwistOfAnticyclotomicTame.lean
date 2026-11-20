import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideOfLPowerGaloisCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)

namespace GlobalTheory.TwistPull

section General

variable {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω]

/- English proof (translation)
Establish `e : ((descend φ).ker : Set (Gab D.host.E Ω)) = (toAb D.host.E Ω) '' (φ.ker : Set (G D.host.E Ω))`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨σ, rfl⟩` from `QuotientGroup.mk'_surjective _ g`.

Use `⟨σ, ?_, rfl⟩` and prove the remaining obligations. Establish `h1 : descend φ (toAb D.host.E Ω σ) = 1` using `hg`. Rewrite `h1` using `[descend_toAb h]`. Conclude with `h1`. Introduce and unpack `⟨σ, hσ, rfl⟩ show descend φ (toAb D.host.E Ω σ) = 1`.

Rewrite using `[descend_toAb h]`. Conclude with `hσ`. Establish `ho : IsOpen ((descend φ).ker : Set (Gab D.host.E Ω))`. Rewrite using `[e]`. Conclude with `QuotientGroup.isOpenMap_coe _ h`.

Establish `hc : Continuous (a.sym)` using `ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)`. Conclude with `ho.preimage hc`.
-/
theorem isOpen_ker_pull {a : Recip D Ω} (ha : a.Good) {A : Type} [CommGroup A] {φ : G D.host.E Ω →* A}
    (h : IsOpen (φ.ker : Set (G D.host.E Ω))) : IsOpen ((a.pull φ).ker : Set (AE D)ˣ) := by
  have e : ((descend φ).ker : Set (Gab D.host.E Ω)) = (toAb D.host.E Ω) '' (φ.ker : Set (G D.host.E Ω)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective _ g
      refine ⟨σ, ?_, rfl⟩
      have h1 : descend φ (toAb D.host.E Ω σ) = 1 := hg
      rw [descend_toAb h] at h1
      exact h1
    · rintro ⟨σ, hσ, rfl⟩
      show descend φ (toAb D.host.E Ω σ) = 1
      rw [descend_toAb h]
      exact hσ
  have ho : IsOpen ((descend φ).ker : Set (Gab D.host.E Ω)) := by
    rw [e]
    exact QuotientGroup.isOpenMap_coe _ h
  have hc : Continuous (a.sym) := ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)
  exact ho.preimage hc

/- English proof (translation)
Establish `hk : Neutral.B1.diagUnits D.host.E x ∈ a.art.ker`. Rewrite using `[ha.artin.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨x, rfl⟩)`. Establish `e : Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom x) = Neutral.B1.diagUnits D.host.E x` using `Units.ext (ha.rat x)`. Establish `h1 : a.sym (Units.map (incA D).toMonoidHom x) = 1`.

Express the relevant statement in the definitionally equal form `a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom x)) = 1`. Rewrite using `[e]`. Conclude with `hk`. Express the relevant statement in the definitionally equal form `descend φ (a.sym _) = 1`. Rewrite using `[h1, map_one]`.
-/
theorem pull_rat {a : Recip D Ω} (ha : a.Good) {A : Type} [CommGroup A] (φ : G D.host.E Ω →* A) (x : D.host.Eˣ) :
    a.pull φ (Units.map (incA D).toMonoidHom x) = 1 := by
  have hk : Neutral.B1.diagUnits D.host.E x ∈ a.art.ker := by
    rw [ha.artin.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨x, rfl⟩)
  have e : Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom x) = Neutral.B1.diagUnits D.host.E x :=
    Units.ext (ha.rat x)
  have h1 : a.sym (Units.map (incA D).toMonoidHom x) = 1 := by
    change a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom x)) = 1
    rw [e]
    exact hk
  change descend φ (a.sym _) = 1
  rw [h1, map_one]

/- English proof (translation)
Take `⟨χ, hχ⟩` from `GlobalTheory.ToricDistribution.exists_corr ha.artin hr`. Establish `hu` using `GlobalTheory.ToricDistribution.isUnitary_of_pow hm (hχ.pow hp)`. Set `u : (AE D)ˣ →* Neutral.B1.Ideles D.host.E` to `Units.map a.κ.toMonoidHom`. Establish `hcu : Continuous u` using `Continuous.units_map _ ha.cont`. Set `c : (AE D)ˣ →* Circle` to `{ toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hu _)⟩ map_one' := Circle.ext (by simp) map_mul' := fun x y => Circle.ext (by`.

Express the relevant statement in the definitionally equal form `((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)`. Rewrite using `[map_mul, map_mul, Units.val_mul]) }`. Establish `hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ)` using `fun x => rfl`. Use `⟨c, χ, ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, hχ, fun x => ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hcu)) _`.

Establish `: u (Units.map (incA D).toMonoidHom x) = Neutral.B1.diagUnits D.host.E x` using `Units.ext (ha.rat x)`. Rewrite using `[hcoe, this, χ.2.2]`. Both sides reduce to the same expression. Establish `: u x = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)`. Use `Units.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `a.κ (x : AE D) = _`. Rewrite using `[hx, ha.loc P e he k]`. Rewrite using `[hcoe, this]`. Both sides reduce to the same expression. Take `⟨σ, hσ⟩` from `a.exists_sym x`.

Rewrite using `[hcoe, a.pull_eq hr hσ, hχ (u x) σ hσ]`.
-/
theorem exists_chrEq_pull {a : Recip D Ω} (ha : a.Good) {r : G D.host.E Ω →* ℂˣ}
    (hr : IsOpen (r.ker : Set (G D.host.E Ω))) {m : ℕ} (hm : m ≠ 0) (hp : ∀ σ, r σ ^ m = 1) :
    ∃ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ ∧
      GlobalTheory.ToricDistribution.Corr a.art r χ ∧ ∀ x, ((c x : Circle) : ℂ) = ((a.pull r x : ℂˣ) : ℂ) := by
  obtain ⟨χ, hχ⟩ := GlobalTheory.ToricDistribution.exists_corr ha.artin hr
  have hu := GlobalTheory.ToricDistribution.isUnitary_of_pow hm (hχ.pow hp)
  let u : (AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map a.κ.toMonoidHom
  have hcu : Continuous u := Continuous.units_map _ ha.cont
  let c : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hu _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c, χ, ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, hχ, fun x => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hcu)) _
  · have : u (Units.map (incA D).toMonoidHom x) = Neutral.B1.diagUnits D.host.E x := Units.ext (ha.rat x)
    rw [hcoe, this, χ.2.2]
    rfl
  · have : u x = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) := by
      refine Units.ext ?_
      change a.κ (x : AE D) = _
      rw [hx, ha.loc P e he k]
    rw [hcoe, this]
    rfl
  · obtain ⟨σ, hσ⟩ := a.exists_sym x
    rw [hcoe, a.pull_eq hr hσ, hχ (u x) σ hσ]

/- English proof (translation)
Take `⟨c, χ, hc, hχ, hcr⟩` from `exists_chrEq_pull ha hr (pow_ne_zero n hl.ne_zero) hp`. Establish `ht : χ.TameAt PP` using `GlobalTheory.ToricDistribution.levelLe_one_of_pow hl (hχ.pow hp) hlP`. Take `⟨ρ, hρ⟩` from `GlobalTheory.exists_isRes_of_tameAt D χ PP ht`. Conclude with `⟨ρ, fun x hx hi u hu => Units.ext ((hcr x).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ x hx hi u hu))⟩`.
-/
theorem exists_res_pull {a : Recip D Ω} (ha : a.Good) {r : G D.host.E Ω →* ℂˣ}
    (hr : IsOpen (r.ker : Set (G D.host.E Ω))) {l n : ℕ} (hl : l.Prime) (hp : ∀ σ, r σ ^ (l ^ n) = 1)
    {PP : Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (hlP : ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∃ ρ : (kP PP)ˣ →* ℂˣ, ∀ x : (AE D)ˣ, (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
      ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
        resS D.host.F PP ⟨_, hi⟩ = u → a.pull r x = ρ u := by
  obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha hr (pow_ne_zero n hl.ne_zero) hp
  have ht : χ.TameAt PP := GlobalTheory.ToricDistribution.levelLe_one_of_pow hl (hχ.pow hp) hlP
  obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
  exact ⟨ρ, fun x hx hi u hu =>
    Units.ext ((hcr x).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ x hx hi u hu))⟩

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Take `⟨f, hf⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity H ℂ hz`. Conclude with `hf (h f)`.
-/
theorem eq_one_of_forall_char {H : Type} [CommGroup H] [Finite H] {z : H} (h : ∀ f : H →* ℂˣ, f z = 1) : z = 1 := by
  by_contra hz
  obtain ⟨f, hf⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity H ℂ hz
  exact hf (h f)

variable [IsTopologicalGroup (G D.host.E Ω)] [CompactSpace (G D.host.E Ω)]

/- English proof (translation)
Use `haveI := Subgroup.quotient_finite_of_isOpen φ.ker h`. Conclude with `Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv`.
-/
theorem finite_range {A : Type} [CommGroup A] {φ : G D.host.E Ω →* A} (h : IsOpen (φ.ker : Set (G D.host.E Ω))) :
    Finite φ.range := by
  haveI := Subgroup.quotient_finite_of_isOpen φ.ker h
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv

/- English proof (translation)
Use `haveI := finite_range hφ`. Establish `h0 : IsOpen (φ.rangeRestrict.ker : Set (G D.host.E Ω))` using `by rw [MonoidHom.ker_rangeRestrict]; exact hφ`. Establish `e1 : φ = φ.range.subtype.comp φ.rangeRestrict` using `MonoidHom.ext fun _ => rfl`. Establish `e : a.pull φ = φ.range.subtype.comp (a.pull φ.rangeRestrict)` using `by conv_lhs => rw [e1]`. Conclude with `a.pull_comp h0 _`.

Establish `key : a.pull φ.rangeRestrict x * (a.pull φ.rangeRestrict y)⁻¹ = 1` using `eq_one_of_forall_char fun f => by`. Rewrite using `[map_mul, map_inv, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← a.pull_comp h0, h f, mul_inv_cancel]`. Rewrite using `[e, MonoidHom.comp_apply, MonoidHom.comp_apply, mul_inv_eq_one.1 key]`.
-/
theorem pull_eq_of_chars (a : Recip D Ω) {A : Type} [CommGroup A] {φ : G D.host.E Ω →* A}
    (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) {x y : (AE D)ˣ}
    (h : ∀ f : φ.range →* ℂˣ, a.pull (f.comp φ.rangeRestrict) x = a.pull (f.comp φ.rangeRestrict) y) :
    a.pull φ x = a.pull φ y := by
  haveI := finite_range hφ
  have h0 : IsOpen (φ.rangeRestrict.ker : Set (G D.host.E Ω)) := by rw [MonoidHom.ker_rangeRestrict]; exact hφ
  have e1 : φ = φ.range.subtype.comp φ.rangeRestrict := MonoidHom.ext fun _ => rfl
  have e : a.pull φ = φ.range.subtype.comp (a.pull φ.rangeRestrict) := by
    conv_lhs => rw [e1]
    exact a.pull_comp h0 _
  have key : a.pull φ.rangeRestrict x * (a.pull φ.rangeRestrict y)⁻¹ = 1 := eq_one_of_forall_char fun f => by
    rw [map_mul, map_inv, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← a.pull_comp h0, h f,
      mul_inv_cancel]
  rw [e, MonoidHom.comp_apply, MonoidHom.comp_apply, mul_inv_eq_one.1 key]

/- English proof (translation)
Use `haveI := finite_range hφ`. Use `haveI := Fintype.ofFinite φ.range`. Use `⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, ?_⟩` and prove the remaining obligations. Establish `: φ.rangeRestrict g = 1` using `Subtype.ext (MonoidHom.mem_ker.1 hg)`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]`.

Establish `hg : ∀ g : φ.range, ∃ n : ℕ, g ^ (l ^ n) = 1` using `fun g => by`. Take `⟨σ, hσ⟩` from `g.2`. Take `⟨n, hn⟩` from `hpow σ`. Conclude with `⟨n, Subtype.ext (by rw [SubmonoidClass.coe_pow, ← hσ, hn]; rfl)⟩`. Use `choose n hn using hg`.

Use `⟨Finset.univ.sup n, fun σ => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ (φ.rangeRestrict σ)))`. Rewrite using `[MonoidHom.comp_apply, ← map_pow, hk, pow_add, pow_mul, hn, one_pow, map_one]`.
-/
theorem char_props {A : Type} [CommGroup A] {φ : G D.host.E Ω →* A} (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) {l : ℕ}
    (hpow : ∀ σ, ∃ n : ℕ, φ σ ^ (l ^ n) = 1) (f : φ.range →* ℂˣ) :
    IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E Ω)) ∧
      ∃ n : ℕ, ∀ σ, (f.comp φ.rangeRestrict) σ ^ (l ^ n) = 1 := by
  classical
  haveI := finite_range hφ
  haveI := Fintype.ofFinite φ.range
  refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, ?_⟩
  · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
  · have hg : ∀ g : φ.range, ∃ n : ℕ, g ^ (l ^ n) = 1 := fun g => by
      obtain ⟨σ, hσ⟩ := g.2
      obtain ⟨n, hn⟩ := hpow σ
      exact ⟨n, Subtype.ext (by rw [SubmonoidClass.coe_pow, ← hσ, hn]; rfl)⟩
    choose n hn using hg
    refine ⟨Finset.univ.sup n, fun σ => ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ (φ.rangeRestrict σ)))
    rw [MonoidHom.comp_apply, ← map_pow, hk, pow_add, pow_mul, hn, one_pow, map_one]

end General

end GlobalTheory.TwistPull

namespace GlobalTheory.TwistPull

/- English proof (translation)
Introduce `D N X art ha r m hm hp hanti c χ hc hcorr y`. Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Establish `hpw` using `hcorr.pow hp`. Take `⟨j, hj⟩` from `X.cc_cm.1`. Establish `hT : χ.TrivOn D.host.F`.

Use `⟨GlobalTheory.ToricDistribution.resFin_of_anti (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _) GlobalTheory.ToricDistribution.host_unram (cc := X.cc) (fun x => j.injective ?_) (fun x => j.injective ?_) ha hcorr h …` and prove the remaining obligations. Rewrite using `[hj]`. Conclude with `(IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm`. Rewrite using `[hj, hj, Complex.conj_conj]`. Rewrite using `[Formalism.L2.Host.HChar.resInf_apply]`.

Conclude with `Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hm hpw w' _`. Set `ψ : Neutral.B1.Ideles D.host.F →* Circle` to `c.comp (Formalism.L2.Theta.idF D)`. Establish `hcI : Continuous (algebraMap (AF D.host.F) (AE D))` using `by haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Conclude with `(continuous_id.smul continuous_const).congr fun a => (Algebra.algebraMap_eq_smul_one a).symm`. Establish `hcont : Continuous ψ` using `hc.1.1.comp (Continuous.units_map _ hcI)`.

Establish `e : ∀ k : D.host.F, algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) k) = incA D (algebraMap D.host.F D.host.E k)`. Introduce `k`. Express the relevant statement in the definitionally equal form `(algebraMap D.host.F (AF D.host.F) k) ⊗ₜ[D.host.F] (1 : D.host.E) = (1 : AF D.host.F) ⊗ₜ (algebraMap _ _ k)`. Conclude with `Algebra.TensorProduct.tmul_one_eq_one_tmul k`. Establish `hdiag : ∀ k, ψ (Neutral.B1.diagUnits D.host.F k) = 1` using `fun k => by`.

Establish `: Formalism.L2.Theta.idF D (Neutral.B1.diagUnits D.host.F k) = Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom k)` using `Units.ext (e k)`. Express the relevant statement in the definitionally equal form `c (Formalism.L2.Theta.idF D _) = 1`. Rewrite using `[this]`. Conclude with `hc.1.2 _`. Establish `hloc : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ x, ψ (Neutral.B1.localIdele D.host.F v x) = 1` using `fun v _ x => by`.

Use `GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc hT _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (((Neutral.B1.localIdele D.host.F v x : Neutral.B1.Ideles D.host.F) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1`. Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]`. Establish `h1 : fstA D.host.F ((Neutral.B1.localIdele D.host.F v x : Neutral.B1.Ideles D.host.F) : AF D.host.F) = 1` using `rfl`. Rewrite using `[h1]`.

Both sides reduce to the same expression. Conclude with `DFunLike.congr_fun (GlobalTheory.FrobDense.eq_one_of_away ψ hcont hdiag ∅ hloc) y`.
-/
theorem real_C : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (m : ℕ), m ≠ 0 → (∀ σ, r σ ^ m = 1) → AntiHom X.cc r → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ y : (AF D.host.F)ˣ, c (Formalism.L2.Theta.idF D y) = 1 := by
  intro D N X art ha r m hm hp hanti c χ hc hcorr y
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hpw := hcorr.pow hp
  obtain ⟨j, hj⟩ := X.cc_cm.1
  have hT : χ.TrivOn D.host.F := by
    refine ⟨GlobalTheory.ToricDistribution.resFin_of_anti (IsCMField.complexConj D.host.E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _) GlobalTheory.ToricDistribution.host_unram
      (cc := X.cc) (fun x => j.injective ?_) (fun x => j.injective ?_) ha hcorr hanti, fun w k => ?_⟩
    · rw [hj]
      exact (IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm
    · rw [hj, hj, Complex.conj_conj]
    · rw [Formalism.L2.Host.HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hm hpw w' _
  let ψ : Neutral.B1.Ideles D.host.F →* Circle := c.comp (Formalism.L2.Theta.idF D)
  have hcI : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    exact (continuous_id.smul continuous_const).congr fun a => (Algebra.algebraMap_eq_smul_one a).symm
  have hcont : Continuous ψ := hc.1.1.comp (Continuous.units_map _ hcI)
  have e : ∀ k : D.host.F, algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) k) =
      incA D (algebraMap D.host.F D.host.E k) := by
    intro k
    change (algebraMap D.host.F (AF D.host.F) k) ⊗ₜ[D.host.F] (1 : D.host.E) = (1 : AF D.host.F) ⊗ₜ (algebraMap _ _ k)
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul k
  have hdiag : ∀ k, ψ (Neutral.B1.diagUnits D.host.F k) = 1 := fun k => by
    have : Formalism.L2.Theta.idF D (Neutral.B1.diagUnits D.host.F k) =
        Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom k) := Units.ext (e k)
    change c (Formalism.L2.Theta.idF D _) = 1
    rw [this]
    exact hc.1.2 _
  have hloc : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ x,
      ψ (Neutral.B1.localIdele D.host.F v x) = 1 := fun v _ x => by
    refine GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc hT _ ?_
    change (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      (((Neutral.B1.localIdele D.host.F v x : Neutral.B1.Ideles D.host.F) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    have h1 : fstA D.host.F ((Neutral.B1.localIdele D.host.F v x : Neutral.B1.Ideles D.host.F) : AF D.host.F) = 1 := rfl
    rw [h1]
    rfl
  exact DFunLike.congr_fun (GlobalTheory.FrobDense.eq_one_of_away ψ hcont hdiag ∅ hloc) y

end GlobalTheory.TwistPull

namespace GlobalTheory.TwistPull

/- English proof (translation)
Introduce `D N X a ha A _ φ l hl hpow hφ hanti Q hQ hQl hunr`. Establish `hr` using `fun f => char_props (D := D) hφ hpow f`. Establish `hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict)` using `fun f g g' hg => by`. Establish `e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹` using `Subtype.ext (hanti g g' hg)`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]`.

Use `⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩` and prove the remaining obligations. Use `(pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)` and prove the remaining obligations. Take `⟨h1, n, h2⟩` from `hr f`. Establish `hm` using `pow_ne_zero n hl.ne_zero`. Take `⟨c, χ, hc, hχ, hcr⟩` from `exists_chrEq_pull ha h1 hm h2`.

Rewrite using `[map_one]`. Use `Units.ext ((hcr _).symm.trans ?_)` and prove the remaining obligations. Rewrite using `[real_C D N X a.art ha.artin _ _ hm h2 (hanti' f) c χ hc hχ y]`. Simplify using the standard rewrite rules. Introduce `x h1 h2 h3 h4`.

Use `(pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)` and prove the remaining obligations. Take `⟨o1, n, o2⟩` from `hr f`. Take `⟨c, χ, hc, hχ, hcr⟩` from `exists_chrEq_pull ha o1 (pow_ne_zero n hl.ne_zero) o2`. Rewrite using `[map_one]`. Use `Units.ext ((hcr _).symm.trans ?_)` and prove the remaining obligations.

Rewrite using `[GlobalTheory.T.heckeChar_unramified_outside_of_lPower_galois_char D N a.art ha.artin _ l n hl o2 c χ hc hχ Q hQ hQl (fun v hv hc' B hB σ hσ => by`. Rewrite using `[MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]`. Simplify using the standard rewrite rules. Establish `hPP` using `hQ.isIdemAt hPP`. Establish `same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP → (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP → ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) …`.

Introduce `x x' u hx hx' hi hi' hu hu'`. Use `pull_eq_of_chars a hφ fun f => ?_` and prove the remaining obligations. Take `⟨o1, n, o2⟩` from `hr f`. Take `⟨ρ, hρ⟩` from `exists_res_pull ha o1 hl o2 hPP (hQl PP ‹_›)`. Rewrite using `[hρ x hx hi u hu, hρ x' hx' hi' u hu']`.

Establish `hlift` using `fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u`. Use `choose xs hxs using hlift`. Establish `hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v)` using `fun u v => by`. Take `⟨hi, hu⟩` from `(hxs (u * v)).res`. Take `⟨hi1, hu1⟩` from `(hxs u).res`.

Take `⟨hi2, hu2⟩` from `(hxs v).res`. Establish `hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Rewrite using `[Units.val_mul, map_mul]`. Conclude with `mul_mem hi1 hi2`. Use `same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]`. Establish `: (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)`. Rewrite using `[Units.val_mul, map_mul])`. Rewrite using `[this, map_mul, hu1, hu2, Units.val_mul]`.

Use `⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩` and prove the remaining obligations. Use `show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)`. Rewrite using `[hmul, map_mul]`. Introduce `x hx hi u hu show a.pull φ x = a.pull φ (xs u)`. Take `⟨hi', hu'⟩` from `(hxs u).res`.

Conclude with `same x (xs u) u hx (hxs u).off hi hi' hu hu'`.
-/
theorem good_pull : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A) (l : ℕ), l.Prime → (∀ σ, ∃ n : ℕ, φ σ ^ (l ^ n) = 1) → IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ l hl hpow hφ hanti Q hQ hQl hunr
  have hr := fun f => char_props (D := D) hφ hpow f
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, n, h2⟩ := hr f
    have hm := pow_ne_zero n hl.ne_zero
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hm h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hm h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, n, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 (pow_ne_zero n hl.ne_zero) o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_of_lPower_galois_char D N a.art ha.artin _ l n hl o2 c χ hc hχ Q hQ hQl (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, n, o2⟩ := hr f
      obtain ⟨ρ, hρ⟩ := exists_res_pull ha o1 hl o2 hPP (hQl PP ‹_›)
      rw [hρ x hx hi u hu, hρ x' hx' hi' u hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPull
