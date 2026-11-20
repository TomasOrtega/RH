import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocDictP

/- English proof (translation)
The claim follows from `h.inj.comp e.symm.injective sq := by simpa using h.sq adj a := h.adj (e.symm a) comm a := h.comm (e.symm a) span x hx := by obtain ⟨a, b, hab⟩ := h.span x hx exact ⟨e a, e b, by simpa using hab⟩`.
-/
theorem frame_transport {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B B' : Type}
    [CommRing B] [CommRing B'] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (e : B ≃+* B')
    (h : IsFrame c δ s d ρ) : IsFrame c δ s (e d) (ρ.comp e.symm.toRingHom) where
  inj := h.inj.comp e.symm.injective
  sq := by simpa using h.sq
  adj a := h.adj (e.symm a)
  comm a := h.comm (e.symm a)
  span x hx := by
    obtain ⟨a, b, hab⟩ := h.span x hx
    exact ⟨e a, e b, by simpa using hab⟩

/- English proof (translation)
Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Establish `ha : (z + IsCMField.complexConj E z) / 2 ∈ maximalRealSubfield E`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]`. Establish `hb : (z - IsCMField.complexConj E z) / (2 * s) ∈ maximalRealSubfield E`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hsc]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = (z + IsCMField.complexConj E z) / 2 + s * ((z - IsCMField.complexConj E z) / (2 * s))`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs0 : s ≠ 0)
    (hsc : IsCMField.complexConj E s = -s) (z : E) :
    ∃ a b : (maximalRealSubfield E),
      z = algebraMap (maximalRealSubfield E) E a + s * algebraMap (maximalRealSubfield E) E b := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (z + IsCMField.complexConj E z) / 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat,
      add_comm]
  have hb : (z - IsCMField.complexConj E z) / (2 * s) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat,
      hsc]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change z = (z + IsCMField.complexConj E z) / 2 + s * ((z - IsCMField.complexConj E z) / (2 * s))
  field_simp
  ring

end PositivityTheory.Rg.BcB.G3.LocDictP

open PositivityTheory.Rg.BcB.G3.LocDictP in
/- English proof (translation)
Introduce `E _ _ _ hU s d hs0 hsc hd n δ hsep ι _ K _ _ _ ρ hfr w y hy`. Establish `hdne : d ≠ 0`. Introduce and unpack `rfl`. Apply `hs0` to reduce the goal to its premises. Establish `: s ^ 2 = 0` using `by rw [← hd, map_zero]`.

Conclude with `pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this`. Distinguish the cases in `hw : IsSplitAt w`. Establish `hthL : thL n w = MonoidHom.id _` using `by simp only [thL, if_pos hw]`. Establish `hy' : y.val.charpoly = atPl w (δ * thE E n δ).val.charpoly`. Use `hy` as an intermediate fact.

Simplify using `only [nrmL, if_pos hw] at this`. Conclude with `this`. Use `⟨fun _ _ => 1, fun t => ⟨fun _ => ?_, fun _ => ?_⟩⟩` and prove the remaining obligations. Introduce `i u`. Take `⟨r, hr⟩` from `h6 E s d hs0 hsc hd w hw`.

Take `⟨e, he⟩` from `h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))`. Establish `hq : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u = algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d)`. Rewrite using `[← he, ← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← hr, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]`. Establish `hti : ((t : ∀ i, K i) i) ≠ 0` using `((t.isUnit.map (Pi.evalRingHom K i)).ne_zero)`. Establish `hT : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ i, K i) i) ≠ 0` using `(_root_.map_ne_zero _).2 hti`.

Establish `hD : algebraMap (K i) (u.1.adicCompletion (K i)) (algebraMap (maximalRealSubfield E) (K i) d) ≠ 0` using `(_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hdne)`. Establish `hq0 : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u ≠ 0`. Introduce `h0`. Rewrite `hq` using `[h0, mul_zero]`. Conclude with `hD hq.symm`.

Use `⟨(1 + (algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹) / 2, ((algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹ - 1) / (2 * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u), ?_⟩` and prove the remaining obligations. Establish `: CharZero (u.1.adicCompletion (K i))` using `charZero_of_injective_algebraMap (algebraMap (K i) (u.1.adicCompletion (K i))).injective`. Simplify using `only [Units.val_one]`. Rewrite using `[← hq]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hinv : ∀ x : E, (IsCMField.complexConj E).toRingEquiv.toRingHom ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x` using `fun x => IsCMField.complexConj_apply_apply E x`. Establish `hN` using `h1 E n _ hinv δ s hs0 hsc (∀ i, K i) _ ρ.toRingHom hfr t`. Establish `hloc : locEl n w (pt δ ρ.toRingHom t) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)`. Simplify using `only [locEl, if_pos hw, thE, hN]`.

Establish `hc1 : y.val.charpoly = (locEl n w (pt δ ρ.toRingHom t)).val.charpoly`. Rewrite using `[hloc, hy']`. Express the relevant statement in the definitionally equal form `_ = (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly`. Rewrite using `[Matrix.charpoly_map]`. Take `⟨h, hh⟩` from `GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable _ n y _ hc1 (hy' ▸ hsep.map)`.

Conclude with `⟨h, by rw [hthL, MonoidHom.id_apply]; exact hh⟩`. Establish `hI` using `GlobalTheory.ConjAtPlace.main E hU w`. Establish `hcc : ∀ x, cj w (cj w x) = x` using `hI.2.1`. Establish `hcE` using `(hI.2.2.2.1 hw).1`. Establish `: CharZero (w.adicCompletion E)` using `charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`.

Take `⟨j, hj1, hj2, hj3⟩` from `h5 E hU s d hs0 hsc hd w hw`. Take `⟨ρ', hρ'1, hρ'⟩` from `h4 (maximalRealSubfield E) E ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) (w.adicCompletion E) (algebraMap E _) j (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) s d hj1 (fun x => hcE x) hj2 hs0 hsc (decomp E s hs0 hsc) hj3 n δ hsep (∀ i, …`. Establish `hTC` using `fun i => h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))`. Use `choose e he using hTC`. Take `⟨Φ, hΦ⟩ : ∃ Φ : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] (∀ i, K i)) ≃+* (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K …` from `⟨(Algebra.TensorProduct.piRight (maximalRealSubfield E) (maximalRealSubfield E) _ K).toRingEquiv.trans (RingEquiv.piCongrRight e), fun a => by`.

Use function extensionality and compare the values at `i u`. Simplify using `[Algebra.TensorProduct.piRight_tmul, he]⟩`. Establish `hfr''` using `frame_transport Φ hρ'`. Establish `hmapθ` using `GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) (fun x => (hcE x).symm) δ`. Establish `hNδ : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ * thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly`.

Rewrite using `[← hmapθ, ← map_mul]`. Express the relevant statement in the definitionally equal form `(((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly = _`. Rewrite using `[Matrix.charpoly_map]`. Establish `hsep' : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ * thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly.Separable`. Rewrite using `[hNδ]`.

Conclude with `hsep.map`. Establish `hy' : (y * thetaGL n (cj w) y).val.charpoly = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ * thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly`. Rewrite using `[hNδ]`. Use `hy` as an intermediate fact. Simplify using `only [nrmL, if_neg hw] at this`.

Conclude with `this`. Establish `hs0' : algebraMap E (w.adicCompletion E) s ≠ 0` using `(_root_.map_ne_zero _).2 hs0`. Establish `hsc' : cj w (algebraMap E (w.adicCompletion E) s) = -algebraMap E (w.adicCompletion E) s`. Rewrite using `[hcE, hsc, map_neg]`. Take `⟨t0, g0, hg0⟩` from `h2 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' hsep' y hy'`.

Use `⟨fun i u => Units.map (Pi.evalMonoidHom _ u) (Units.map (Pi.evalMonoidHom _ i) t0), fun t => ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩ : ∃ T : (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i))ˣ, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRea …` from `⟨Units.map (Φ.toMonoidHom.comp (Algebra.TensorProduct.includeRight : (∀ i, K i) →ₐ[maximalRealSubfield E] _).toRingHom.toMonoidHom) t, rfl⟩`. Establish `hpt : locEl n w (pt δ ρ.toRingHom t) = pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [locEl, if_neg hw, pt]`.

Express the relevant statement in the definitionally equal form `((ρ t * δ.val).map (algebraMap E (w.adicCompletion E))) = ρ' (Φ.symm (T : _)) * (δ.val.map (algebraMap E (w.adicCompletion E)))`. Rewrite using `[hT, RingEquiv.symm_apply_apply, hρ'1, Matrix.map_mul]`. Establish `hthL : thL n w = thetaGL n (cj w)` using `by simp only [thL, if_neg hw]`. Rewrite using `[hpt, hthL]`. Establish `step1 : (∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * y * thetaGL n (cj w) g) ↔ ∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * pt (GeneralLinearGroup.map (a …`.

Rewrite using `[hg0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨g0 * g, by rw [hg, map_mul]; group⟩`. Introduce and unpack `⟨g, hg⟩`.

Conclude with `⟨g0⁻¹ * g, by rw [hg, map_mul, map_inv]; group⟩`. Rewrite using `[step1, h3 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' t0 T]`. Establish `hTv : ∀ i u, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) i u = algebraMap (K i) _ ((t : ∀ i, K i) i)` using `fun i u => by rw [hT, hΦ]`. Establish `hdv : ∀ i u, Φ (1 ⊗ₜ algebraMap (maximalRealSubfield E) (∀ i, K i) d) i u = algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d)` using `fun i u => by rw [hΦ]; rfl`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨U, V, hUV⟩ i u`. Use `⟨U i u, V i u, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hUV i) u` as an intermediate fact. Simplify using `only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv] at this`. Simplify using `using this`.

Introduce `h choose a b hab using h`. Use `⟨fun i u => a i u, fun i u => b i u, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i u`. Simplify using `only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv]`. Simplify using `using hab i u`.
-/
theorem PositivityTheory.Rg.BcB.G3.locDict_pf (h1 : ClsNorm) (h2 : ClsOnto) (h3 : ClsEq) (h4 : BaseFrame) (h5 : InertBase)
    (h6 : SplitSq) (h7 : TensorCompl) : LocDict := by
  intro E _ _ _ hU s d hs0 hsc hd n δ hsep ι _ K _ _ _ ρ hfr w y hy
  have hdne : d ≠ 0 := by
    rintro rfl
    apply hs0
    have : s ^ 2 = 0 := by rw [← hd, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  by_cases hw : IsSplitAt w
  ·
    have hthL : thL n w = MonoidHom.id _ := by simp only [thL, if_pos hw]
    have hy' : y.val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
      have := hy; simp only [nrmL, if_pos hw] at this; exact this
    refine ⟨fun _ _ => 1, fun t => ⟨fun _ => ?_, fun _ => ?_⟩⟩
    · intro i u
      obtain ⟨r, hr⟩ := h6 E s d hs0 hsc hd w hw
      obtain ⟨e, he⟩ := h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
      have hq : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u =
          algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := by
        rw [← he, ← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← hr, mul_one,
          Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      have hti : ((t : ∀ i, K i) i) ≠ 0 := ((t.isUnit.map (Pi.evalRingHom K i)).ne_zero)
      have hT : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ i, K i) i) ≠ 0 := (_root_.map_ne_zero _).2 hti
      have hD : algebraMap (K i) (u.1.adicCompletion (K i)) (algebraMap (maximalRealSubfield E) (K i) d) ≠ 0 :=
        (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hdne)
      have hq0 : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hq; exact hD hq.symm
      refine ⟨(1 + (algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹) / 2,
        ((algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹ - 1) / (2 * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u), ?_⟩
      have : CharZero (u.1.adicCompletion (K i)) :=
        charZero_of_injective_algebraMap (algebraMap (K i) (u.1.adicCompletion (K i))).injective
      simp only [Units.val_one]
      rw [← hq]
      field_simp
      ring
    · have hinv : ∀ x : E, (IsCMField.complexConj E).toRingEquiv.toRingHom
          ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
      have hN := h1 E n _ hinv δ s hs0 hsc (∀ i, K i) _ ρ.toRingHom hfr t
      have hloc : locEl n w (pt δ ρ.toRingHom t) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
        simp only [locEl, if_pos hw, thE, hN]
      have hc1 : y.val.charpoly = (locEl n w (pt δ ρ.toRingHom t)).val.charpoly := by
        rw [hloc, hy']
        change _ = (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly
        rw [Matrix.charpoly_map]
      obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable _ n y _ hc1 (hy' ▸ hsep.map)
      exact ⟨h, by rw [hthL, MonoidHom.id_apply]; exact hh⟩
  ·
    have hI := GlobalTheory.ConjAtPlace.main E hU w
    have hcc : ∀ x, cj w (cj w x) = x := hI.2.1
    have hcE := (hI.2.2.2.1 hw).1
    have : CharZero (w.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    obtain ⟨j, hj1, hj2, hj3⟩ := h5 E hU s d hs0 hsc hd w hw
    obtain ⟨ρ', hρ'1, hρ'⟩ := h4 (maximalRealSubfield E) E
      ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) (w.adicCompletion E)
      (algebraMap E _) j (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) s d hj1 (fun x => hcE x) hj2 hs0 hsc
      (decomp E s hs0 hsc) hj3 n δ hsep (∀ i, K i) ρ hfr
    have hTC := fun i => h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
    choose e he using hTC
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E]
        (∀ i, K i)) ≃+* (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)),
        ∀ a : (∀ i, K i), Φ (1 ⊗ₜ a) = fun i u => algebraMap (K i) _ (a i) :=
      ⟨(Algebra.TensorProduct.piRight (maximalRealSubfield E) (maximalRealSubfield E) _ K).toRingEquiv.trans
        (RingEquiv.piCongrRight e), fun a => by
          funext i u
          simp [Algebra.TensorProduct.piRight_tmul, he]⟩
    have hfr'' := frame_transport Φ hρ'
    have hmapθ := GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E))
      (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) (fun x => (hcE x).symm) δ
    have hNδ : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly =
        atPl w (δ * thE E n δ).val.charpoly := by
      rw [← hmapθ, ← map_mul]
      change (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly = _
      rw [Matrix.charpoly_map]
    have hsep' : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly.Separable := by
      rw [hNδ]; exact hsep.map
    have hy' : (y * thetaGL n (cj w) y).val.charpoly = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly := by
      rw [hNδ]
      have := hy; simp only [nrmL, if_neg hw] at this; exact this
    have hs0' : algebraMap E (w.adicCompletion E) s ≠ 0 := (_root_.map_ne_zero _).2 hs0
    have hsc' : cj w (algebraMap E (w.adicCompletion E) s) = -algebraMap E (w.adicCompletion E) s := by
      rw [hcE, hsc, map_neg]
    obtain ⟨t0, g0, hg0⟩ := h2 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' hsep' y hy'
    refine ⟨fun i u => Units.map (Pi.evalMonoidHom _ u) (Units.map (Pi.evalMonoidHom _ i) t0), fun t => ?_⟩
    obtain ⟨T, hT⟩ : ∃ T : (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i))ˣ,
        (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) = Φ (1 ⊗ₜ (t : ∀ i, K i)) :=
      ⟨Units.map (Φ.toMonoidHom.comp
        (Algebra.TensorProduct.includeRight : (∀ i, K i) →ₐ[maximalRealSubfield E] _).toRingHom.toMonoidHom) t, rfl⟩
    have hpt : locEl n w (pt δ ρ.toRingHom t) = pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
        (ρ'.comp Φ.symm.toRingHom) T := by
      apply Units.ext
      simp only [locEl, if_neg hw, pt]
      change ((ρ t * δ.val).map (algebraMap E (w.adicCompletion E))) =
        ρ' (Φ.symm (T : _)) * (δ.val.map (algebraMap E (w.adicCompletion E)))
      rw [hT, RingEquiv.symm_apply_apply, hρ'1, Matrix.map_mul]
    have hthL : thL n w = thetaGL n (cj w) := by simp only [thL, if_neg hw]
    rw [hpt, hthL]
    have step1 : (∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T =
        g⁻¹ * y * thetaGL n (cj w) g) ↔ ∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
          (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
            (ρ'.comp Φ.symm.toRingHom) t0 * thetaGL n (cj w) g := by
      rw [hg0]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g0 * g, by rw [hg, map_mul]; group⟩
      · rintro ⟨g, hg⟩
        exact ⟨g0⁻¹ * g, by rw [hg, map_mul, map_inv]; group⟩
    rw [step1, h3 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' t0 T]
    have hTv : ∀ i u, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) i u =
        algebraMap (K i) _ ((t : ∀ i, K i) i) := fun i u => by rw [hT, hΦ]
    have hdv : ∀ i u, Φ (1 ⊗ₜ algebraMap (maximalRealSubfield E) (∀ i, K i) d) i u =
        algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := fun i u => by rw [hΦ]; rfl
    constructor
    · rintro ⟨U, V, hUV⟩ i u
      refine ⟨U i u, V i u, ?_⟩
      have := congrFun (congrFun hUV i) u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv] at this
      simpa using this
    · intro h
      choose a b hab using h
      refine ⟨fun i u => a i u, fun i u => b i u, ?_⟩
      funext i u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv]
      simpa using hab i u
