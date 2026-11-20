import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

/- English proof (translation)
Substitute using the available equality. Supply the required witnesses or components.
-/
private theorem isTr_transport {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} {p : Z ⟶ B}
    {q q' : Y ⟶ B} (e : q = q') {s : Y ⟶ Z} {tr : T.H q →ₗ[R] T.H p} (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} {r : X ⟶ B} (t : Y ⟶ X) (h₁ : t ≫ r = q) (h₂ : t ≫ r = q') (y : T.H r),
        tr' (T.pull t h₂ y) = tr (T.pull t h₁ y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ => rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
private theorem low_square {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : GlobalTheory.GalV.HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) :
    IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g) (pullback.fst C.p (gen O k)) := by
  have hls : (low D).s g ≫ pullback.snd C.p (gen O k) = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    bcMap_snd (gen O k) (D.s g) rfl
  have hlf : (low D).s g ≫ pullback.fst C.p (gen O k) = pullback.fst (D.s g ≫ C.p) (gen O k) ≫ D.s g :=
    bcMap_fst (gen O k) (D.s g) rfl
  refine IsPullback.of_bot ?_ hlf.symm (IsPullback.of_hasPullback C.p (gen O k))
  convert IsPullback.of_hasPullback (D.s g ≫ C.p) (gen O k) using 2
  exact hls

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G3.jLowHodge :
    HodgeGood → BcGood.{0} → FEtBasic → HodgeOpBc → CoverInv.{0} → LiesOp.{0} → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge := by
  intro hHG hBG hFB hOB hCI hLO k L F _ _ _ _ φ ψ H θ O _ _ C D hN hO a hH
  unfold HOcc at hH ⊢
  unfold Nice at hN
  obtain ⟨b, x, hx, he⟩ := hH
  unfold IsHEig at he
  set T' := (hodge F a b).bc (Spec.map (CommRingCat.ofHom φ)) with hT'
  have hgood : T'.Good := hBG _ _ (hHG F a b)
  obtain ⟨hinj, hsurj⟩ := hCI C hO T' hgood
  have hH' : ∀ g : H.Γ, ∃ trg : T'.H (H.s g ≫ H.q) →ₗ[F] T'.H H.q,
      T'.IsTr H.q (H.s g ≫ H.q) (H.s g) trg ∧ trg (T'.pull (H.t g) (H.comm g) x) = ψ (θ g) • x := by
    intro g
    obtain ⟨d, hd⟩ := hN.2.2 g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    obtain ⟨i1, i2, tr, htr, heq⟩ := hOB k F φ H g a b
    obtain ⟨j1, j2, hg⟩ := he g
    exact ⟨tr, htr, (heq j1 j2 x).symm.trans hg⟩
  obtain ⟨z, hz⟩ := hsurj x (fun g _ hθ => by
    obtain ⟨trg, htr, heq⟩ := hH' g
    exact ⟨trg, htr, by rw [heq, hθ, map_one, one_smul]⟩)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hz]; exact map_zero _)
  refine ⟨b, z, hz0, ?_⟩
  unfold IsHEig
  intro g
  have hfet : FEt ((low D).s g) (D.d g) := hFB.1 _ _ _ _ _ (low_square D g) (D.fet g)
  haveI : IsFinite ((low D).s g) := hfet.1
  haveI : Etale ((low D).s g) := hfet.2.1
  obtain ⟨i1, i2, trL, htrL, heqL⟩ := hOB k F φ (low D) g a b
  refine ⟨i1, i2, ?_⟩
  rw [heqL i1 i2 z]
  obtain ⟨tr', htr', htrans⟩ := isTr_transport T' (q := (low D).s g ≫ (low D).q)
    (q' := pullback.snd (D.s g ≫ C.p) (gen O k)) (bcMap_snd (gen O k) (D.s g) rfl) htrL
  obtain ⟨trg, htrg, hgeq⟩ := hH' g
  have hlies := hLO C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet T' hgood tr' trg htr' htrg z
  rw [hz, hgeq, ← hz, ← map_smul] at hlies
  have h := hinj ((map_smul (T'.pull (piK C) _) (ψ (θ g)) z).trans hlies)
  have h₂ : bcMap (gen O k) (D.t g) (D.comm g) ≫ (low D).q = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    ((low D).comm g).trans (bcMap_snd (gen O k) (D.s g) rfl)
  have h3 : tr' (T'.pull (bcMap (gen O k) (D.t g) (D.comm g)) h₂ z) =
      trL (T'.pull ((low D).t g) ((low D).comm g) z) := htrans ((low D).t g) ((low D).comm g) h₂ z
  have h' : ψ (θ g) • z = ((D.m g : ℕ) : F) • trL (T'.pull ((low D).t g) ((low D).comm g) z) :=
    h.trans (congrArg (fun w => ((D.m g : ℕ) : F) • w) h3)
  have hm : ((D.m g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
  have hw : trL (T'.pull ((low D).t g) ((low D).comm g) z) = ψ (θ g / (D.m g : L)) • z := by
    rw [map_div₀, map_natCast, div_eq_inv_mul, mul_smul, h']
    exact (inv_smul_smul₀ hm _).symm
  exact hw
