import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.Th
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.DetRootRead

/- English proof (translation)
Take `⟨hιc, hιc'⟩` from `GlobalTheory.HeckeTensorRead.continuous_finite_equiv D ι hint`. Take `⟨j, hjc, hjc', hj⟩` from `GlobalTheory.HeckeTensorRead.exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩`. Take `⟨s, hs, hsc, hsc'⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Set `Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E` to `s.trans (j.prodCongr ι)`. Establish `hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z))` using `fun z => Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)`.

Use `⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_, fun z => ⟨fun h => ?_, by rw [hΦ]⟩⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Conclude with `Prod.ext (hj x) (hι x)`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he`. Rewrite using `[hΦ]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `h5 : j (infPart D e) = 0` using `by rw [h1]; exact j.map_zero`. Conclude with `(GlobalTheory.HeckeTensorRead.map_loc (j.toRingHom.comp (infPart D)) e _).trans (by`. Express the relevant statement in the definitionally equal form `1 + j (infPart D e) * _ = 1`. Rewrite using `[h5, zero_mul, add_zero])`.

Establish `h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E)` using `hι k`. Use `(GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_` and prove the remaining obligations. Conclude with `GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3`. Rewrite `h` using `[hΦ]`. Conclude with `j.injective (h.trans j.map_one.symm)`.
-/
theorem exists_adele_equiv_fin (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E)) ∧
      ∀ z : AE D, ((Φ z).1 = 1 → infPart D z = 1) ∧ (Φ z).2 = ι (finPart D z) := by
  obtain ⟨hιc, hιc'⟩ := GlobalTheory.HeckeTensorRead.continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_,
    fun z => ⟨fun h => ?_, by rw [hΦ]⟩⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (GlobalTheory.HeckeTensorRead.map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  · rw [hΦ] at h
    exact j.injective (h.trans j.map_one.symm)

/- English proof (translation)
Set `u : Ideles D.host.E →* (AE D)ˣ` to `Units.map Φ.symm.toRingHom.toMonoidHom`. Establish `hu : Continuous u` using `Continuous.units_map _ hΦ`. Establish `ht : Continuous (Circle.toUnits : Circle →* ℂˣ)` using `Units.continuous_iff.2 ⟨continuous_subtype_val, by`. Establish `h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ)` using `continuous_subtype_val.comp continuous_inv`. Use `h.congr fun z => ?_` and prove the remaining obligations.

Use the proof step `simp⟩`. Set `χ' : HChar D.host.E` to `⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (h.1.1.comp hu), fun k => by`. Establish `: u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k` using `Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)`. Express the relevant statement in the definitionally equal form `Circle.toUnits (c (u _)) = 1`. Rewrite using `[this, h.1.2, map_one]⟩`.

Establish `h' : ChrEq c χ'` using `⟨h.1, fun P e he k x hx => by`. Establish `: x = u (localIdele D.host.E P (atFin P k))` using `Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))`. Rewrite using `[this]`. Use the proof step `rfl⟩`. Rewrite using `[GlobalTheory.ChrEqUnique.hchar_unique D c χ χ' h h']`.

Establish `: u (Units.map Φ.toRingHom.toMonoidHom z) = z` using `Units.ext (Φ.symm_apply_apply _)`. Use `show ((c z : Circle) : ℂ) = ((Circle.toUnits (c (u (Units.map Φ.toRingHom.toMonoidHom z))) : ℂˣ) : ℂ)`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem read_of_equiv (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ)
    (Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) (hΦ : Continuous Φ.symm)
    (h1 : ∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x)
    (h2 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E))
    (z : (AE D)ˣ) : ((c z : Circle) : ℂ) = ((χ.1 (Units.map Φ.toRingHom.toMonoidHom z) : ℂˣ) : ℂ) := by
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (h.1.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, h.1.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨h.1, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [GlobalTheory.ChrEqUnique.hchar_unique D c χ χ' h h']
  have : u (Units.map Φ.toRingHom.toMonoidHom z) = z := Units.ext (Φ.symm_apply_apply _)
  show ((c z : Circle) : ℂ) = ((Circle.toUnits (c (u (Units.map Φ.toRingHom.toMonoidHom z))) : ℂˣ) : ℂ)
  rw [this]
  rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add v w hv hw => rw [RingHom.map_add, map_add, hv, hw, map_add, RingHom.map_add]`.
-/
theorem comm_sigR (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add v w hv hw => rw [RingHom.map_add, map_add, hv, hw, map_add, RingHom.map_add]

end GlobalTheory.DetRootRead

namespace GlobalTheory.DetRootRead

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D c χ hc ht V n hn g y hg hy x hx a ha`. Set `ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E` to `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)`. Establish `hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x` using `fun x => afIso_tmul_one _ _ x`. Establish `hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1` using `fun y => (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (mem_rInt_iff _ _ _)`. Take `⟨Φ, -, hΦ', h1, h2, h3⟩` from `exists_adele_equiv_fin D ι hι hint`.

Set `b : (AE D)ˣ` to `Units.map Φ.symm.toRingHom.toMonoidHom (Chr.finPartI D.host.E a)`. Establish `hbΦ : Φ (b : AE D) = ((Chr.finPartI D.host.E a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E)` using `Φ.apply_symm_apply _`. Establish `hbinf : infPart D (b : AE D) = 1` using `(h3 _).1 (by rw [hbΦ]; rfl)`. Establish `hbfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (b : AE D)) = (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E)`. Apply `(afIso D.host.F D.host.E).injective` to reduce the goal to its premises.

Rewrite using `[afIso_finAf]`. Use `(h3 (b : AE D)).2` as an intermediate fact. Rewrite `this` using `[hbΦ]`. Conclude with `this.symm`. Establish `hcb : ((c b : Circle) : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ)`.

Rewrite using `[read_of_equiv D c χ hc Φ hΦ' h1 h2 b]`. Establish `hb' : Units.map Φ.toRingHom.toMonoidHom b = Chr.finPartI D.host.E a` using `Units.ext hbΦ`. Rewrite using `[hb']`. Rewrite using `[← hcb]`. Take `⟨d, hd_def⟩ : ∃ d : AE D, d = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det` from `⟨_, rfl⟩`.

Establish `hdinf : infPart D d = 1` using `by rw [hd_def]; exact GlobalTheory.DetOnto.infPart_det V g hg`. Establish `hdfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D d) = ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, ← hy]`. Unfold `GlobalTheory.AdForm.finM`. Rewrite using `[Matrix.det_reindex_self, hd_def]`.

Conclude with `(Formalism.IndefR.Datum.toEAf D).map_det (mt V g)`. Establish `hfa : (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) = ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) * Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (finAf D.h …`. Unfold `IsDetLift Formalism.L2.DIV.h90 at ha`. Rewrite `ha` using `[MonoidHom.div_apply, div_eq_iff_eq_mul]`. Conclude with `congrArg Units.val ha`.

Establish `hbfin' : finPart D (b : AE D) = finPart D d * sigR (Af D.host.F) D.sp.cm.sig (finPart D (b : AE D))`. Apply `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective` to reduce the goal to its premises. Establish `e1` using `comm_sigR D (finPart D (b : AE D))`. Rewrite `e1` using `[hbfin]`. Use `hbfin.trans (hfa.trans ?_)` and prove the remaining obligations.

Use `Eq.trans ?_ (map_mul (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) _ _).symm` and prove the remaining obligations. Rewrite using `[hdfin, e1]`. Take `⟨s, hs, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w` using `fun z w hi hf => s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))`. Establish `hbd : (b : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (b : AE D)`.

Use `split _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, GlobalTheory.DetOnto.infPart_sigR, hbinf, hdinf, map_one, one_mul]`. Rewrite using `[RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]`. Conclude with `hbfin'`. Set `σU : (AE D)ˣ →* (AE D)ˣ` to `Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom`.

Establish `key : x * σU b = σU x * b`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(x : AE D) * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) = sigR (AF D.host.F) D.sp.cm.sig (x : AE D) * (b : AE D)`. Establish `hx' : (x : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (x : AE D)` using `by rw [hd_def]; exact hx`. Use `conv_lhs => rw [hx']`.

Use `conv_rhs => rw [hbd]`. Expand and normalize the polynomial expressions, which then agree. Set `q : (AE D)ˣ` to `x * b⁻¹`. Establish `hq : σU q = q`. Express the relevant statement in the definitionally equal form `σU (x * b⁻¹) = x * b⁻¹`.

Rewrite using `[map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq]`. Conclude with `key.symm`. Establish `hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x` using `fun x => star_star x`. Establish `htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x`. Introduce `x`.

Apply `(D.sp.cm.fixed _).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `D.sp.cm.sig _ = _`. Rewrite using `[map_add, hσ, add_comm]`. Take `⟨t, htq⟩` from `GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr q (congrArg Units.val hq)`. Establish `hcq : c q = 1`.

Rewrite using `[← htq]`. Conclude with `GlobalTheory.GridWeil.triv_base hc ht t`. Establish `hxq : x = q * b` using `by simp [q]`. Rewrite using `[hxq, map_mul, hcq, one_mul]`.
-/
theorem chr_at_detRoot : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F →
  ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)), g ∈ GfC V →
    finM V hn g = (y : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) → ∀ x, IsDetRoot V g x → ∀ a : Neutral.B1.Ideles D.host.E,
      IsDetLift (host_cmData D.R D.host) y a → (c x : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
  intro D c χ hc ht V n hn g y hg hy x hx a ha
  let ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x => afIso_tmul_one _ _ x
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := fun y =>
    (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (mem_rInt_iff _ _ _)
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := exists_adele_equiv_fin D ι hι hint
  let b : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (Chr.finPartI D.host.E a)
  have hbΦ : Φ (b : AE D) = ((Chr.finPartI D.host.E a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) :=
    Φ.apply_symm_apply _
  have hbinf : infPart D (b : AE D) = 1 := (h3 _).1 (by rw [hbΦ]; rfl)
  have hbfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (b : AE D)) =
      (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    apply (afIso D.host.F D.host.E).injective
    rw [afIso_finAf]
    have := (h3 (b : AE D)).2
    rw [hbΦ] at this
    exact this.symm
  have hcb : ((c b : Circle) : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
    rw [read_of_equiv D c χ hc Φ hΦ' h1 h2 b]
    have hb' : Units.map Φ.toRingHom.toMonoidHom b = Chr.finPartI D.host.E a := Units.ext hbΦ
    rw [hb']
  rw [← hcb]
  obtain ⟨d, hd_def⟩ : ∃ d : AE D, d = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det := ⟨_, rfl⟩
  have hdinf : infPart D d = 1 := by rw [hd_def]; exact GlobalTheory.DetOnto.infPart_det V g hg
  have hdfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D d) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hy]
    unfold GlobalTheory.AdForm.finM
    rw [Matrix.det_reindex_self, hd_def]
    exact (Formalism.IndefR.Datum.toEAf D).map_det (mt V g)
  have hfa : (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) *
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    unfold IsDetLift Formalism.L2.DIV.h90 at ha
    rw [MonoidHom.div_apply, div_eq_iff_eq_mul] at ha
    exact congrArg Units.val ha
  have hbfin' : finPart D (b : AE D) = finPart D d * sigR (Af D.host.F) D.sp.cm.sig (finPart D (b : AE D)) := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    have e1 := comm_sigR D (finPart D (b : AE D))
    rw [hbfin] at e1
    refine hbfin.trans (hfa.trans ?_)
    refine Eq.trans ?_ (map_mul (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) _ _).symm
    rw [hdfin, e1]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hbd : (b : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) := by
    refine split _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.DetOnto.infPart_sigR, hbinf, hdinf, map_one, one_mul]
    · rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]
      exact hbfin'
  let σU : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom
  have key : x * σU b = σU x * b := by
    apply Units.ext
    change (x : AE D) * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) = sigR (AF D.host.F) D.sp.cm.sig (x : AE D) * (b : AE D)
    have hx' : (x : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by rw [hd_def]; exact hx
    conv_lhs => rw [hx']
    conv_rhs => rw [hbd]
    ring
  let q : (AE D)ˣ := x * b⁻¹
  have hq : σU q = q := by
    change σU (x * b⁻¹) = x * b⁻¹
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact key.symm
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨t, htq⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr q (congrArg Units.val hq)
  have hcq : c q = 1 := by
    rw [← htq]
    exact GlobalTheory.GridWeil.triv_base hc ht t
  have hxq : x = q * b := by simp [q]
  rw [hxq, map_mul, hcq, one_mul]

end GlobalTheory.DetRootRead
