import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Unfold `pullHQ`. Rewrite using `[pullHl_comp, LinearMap.baseChange_comp]`. Both sides reduce to the same expression.
-/
private theorem pullHQ_comp_apply (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (a : E ⟶ E') (b : E' ⟶ E'') (n i : ℤ)
    (x : HQ l E'' n i) : pullHQ l (a ≫ b) n i x = pullHQ l a n i (pullHQ l b n i x) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem galHQ_eq_pullHQ_galMap (l : ℕ) [Fact l.Prime] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    {X : Scheme} (t : X ⟶ Spec (CommRingCat.of k)) (n i : ℤ) (σ : Gal(Ω/k)) (x : HQ l (sch.obj (geom Ω t)) n i) :
    galHQ l Ω t n i σ x = pullHQ l (sch.map (galMap Ω t σ)) n i x := rfl

/- English proof (translation)
Establish `hs : Function.Surjective (pullHl l f n i)`. Introduce `y`. Set `x : (k : ℕ) → HtL l k E' n i` to `fun k => (Equiv.ofBijective _ (h k)).symm (y.1 k)`. Establish `hx : ∀ k, GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n (x k) = y.1 k` using `fun k => Equiv.ofBijective_apply_symm_apply _ (h k) (y.1 k)`. Use `⟨⟨x, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `k`. Apply `(h k).1` to reduce the goal to its premises. Rewrite using `[pull_red, hx, hx]`. Conclude with `y.2 k`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Conclude with `hx k`. Unfold `pullHQ`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `LinearMap.lTensor_surjective _ hs`.
-/
private theorem pullHQ_surjective_of_forall_pull_bijective (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (h : ∀ k : ℕ, Function.Bijective (GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Surjective (pullHQ l f n i) := by
  have hs : Function.Surjective (pullHl l f n i) := by
    intro y
    let x : (k : ℕ) → HtL l k E' n i := fun k => (Equiv.ofBijective _ (h k)).symm (y.1 k)
    have hx : ∀ k, GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n (x k) = y.1 k := fun k =>
      Equiv.ofBijective_apply_symm_apply _ (h k) (y.1 k)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · intro k
      apply (h k).1
      rw [pull_red, hx, hx]
      exact y.2 k
    · apply Subtype.ext
      funext k
      exact hx k
  unfold pullHQ
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ hs

/- English proof (translation)
Introduce `hSG hES hNwt hFQ hBF hDG hFrEx hCP hCC`. Introduce `l _ p f n hp O _ _ _ ϖ hϖ hpu K _ _ κ _ _ hp0 hκ hfin Ω _ _ _ V hV kb _ _ _ r hr hrc hl Y g _ _ T hT hPt c hc σ hσ k`. Set `ρ : O →+* V` to `((algebraMap K Ω).comp (algebraMap O K)).codRestrict V hV`. Establish `hρ : CommRingCat.ofHom (algebraMap O κ) ≫ CommRingCat.ofHom (algebraMap κ kb) = CommRingCat.ofHom ρ ≫ CommRingCat.ofHom r`. Use extensionality with `a`.

Conclude with `(hrc a).symm`. Establish `hρK : CommRingCat.ofHom (algebraMap O K) ≫ CommRingCat.ofHom (algebraMap K Ω) = CommRingCat.ofHom ρ ≫ CommRingCat.ofHom V.subtype`. Use extensionality with `a`. Both sides reduce to the same expression. Set `iY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ⟶ pullback g (Spec.map (CommRingCat.ofHom ρ))` to `pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r)) (by`.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρ])`. Set `jY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ pullback g (Spec.map (CommRingCat.ofHom ρ))` to `pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom V.subtype)) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρK])`. Establish `HSG` using `@hSG O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrc Y g _ _ iY jY (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)`. Take `⟨sp, hsp1, hsp2⟩` from `HSG.2 l hl k 0`.

Establish `hpO : (p : O) ∈ Ideal.span {ϖ}`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hpu`. Establish `hpκ : (p : κ) = 0`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 hpO`.

Rewrite using `[← map_natCast (algebraMap O κ), ← hu, map_mul, hκ, mul_zero]`. Establish `hpkb : (p : kb) = 0`. Rewrite using `[← map_natCast (algebraMap κ kb), hpκ, map_zero]`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : CharP kb p := (CharP.charP_iff_prime_eq_zero hp).2 hpkb`.

Set `τ : Gal(kb/κ)` to `AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv kb p f) (fun a => by show iterateFrobenius kb p f _ = _`. Rewrite using `[iterateFrobenius_def, ← map_pow, hfin])`. Establish `hτ : ∀ a, τ a = a ^ p ^ f` using `fun a => iterateFrobeniusEquiv_apply kb p f a`. Use `⟨fun h1 => ?_, fun h2 => ?_⟩` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Take `⟨y, rfl⟩` from `sp.surjective x`. Establish `e` using `hsp2 σ 1 hσ (fun v => by rw [h1 v]; rfl) y`. Rewrite `e` using `[map_one]`. Conclude with `e.symm`.

Establish `hcomp : ∀ x, sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ (sp x)` using `hsp2 σ τ hσ (fun v => by rw [h2 v, hτ])`. Set `φG : kb →+* Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)` to `(pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom`. Establish `hpG : ((p : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) = 0`. Rewrite using `[← map_natCast φG p, hpkb, map_zero]`. Establish `hlG : IsUnit ((l : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤))`.

Rewrite using `[← map_natCast φG l]`. Conclude with `hl.map φG`. Take `⟨Fr, hFr1, hFr2, hFr3⟩` from `hFrEx p f hp κ kb hfin _ (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) hpG τ hτ`. Establish `hAF` using `hFQ l (geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) p f hp hpG hlG k`. Establish `hFG : ∀ x, pullHQ l (sch.map Fr) k 0 (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) = x`.

Introduce `x`. Rewrite using `[galHQ_eq_pullHQ_galMap, ← pullHQ_comp_apply, ← Functor.map_comp, hFr2, hAF]`. Both sides reduce to the same expression. Establish `hinvτ : ∀ x, galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) = x`. Introduce `x`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hsemi : ∀ x, sp (pullHQ l (sch.map Fr) k 0 x) = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x)`. Introduce `x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hinvτ]`. Use `_ = sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) := by`. Rewrite using `[hFG]`. Use `_ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ (sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Both sides reduce to the same expression. Use `_ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by`. Rewrite using `[← hcomp, hinvτ]`. Establish `hpO0 : (p : O) ≠ 0`. Introduce `h0`.

Apply `hp0` to reduce the goal to its premises. Rewrite using `[← map_natCast (algebraMap O K), h0, map_zero]`. Take `⟨hLoc, hGen, hSpe, hBO⟩` from `hBF p O ϖ hϖ hpO0 hpu Y g`. Establish `hOne : ∀ j, Mod.One (T j) (nwt (T j).p)` using `fun j => hNwt p Y (T j) hLoc hGen`. Establish `hβ : Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O κ)) = Spec.map (CommRingCat.ofHom ((algebraMap κ kb).comp (algebraMap O κ)))`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hPBS : IsPullback (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraM …`. Establish `e` using `IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))`. Rewrite `e` using `[hβ]`.

Conclude with `e`. Establish `hDense` using `hDG O ϖ hϖ kb ((algebraMap κ kb).comp (algebraMap O κ)) (by simp [hκ]) Y _ g _ _ hPBS`. Establish `hSep : ∀ (Ω' : Type) [Field Ω'] (x x' : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))), x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.ma …`. Introduce `Ω' _ x x' e1 e2`. Apply `pullback.hom_ext _ e2` to reduce the goal to its premises.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify `e1` using `only [Category.assoc]`. Simplify using `only [Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc, e2, Category.assoc]`. Establish `hTw : ∀ (Ω' : Type) [Field Ω'] (φ : Ω' →+* Ω'), (∀ a, φ a = a ^ p ^ f) → ∀ (x : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))), x ≫ Fr ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom …`.

Introduce `Ω' _ φ hφ x`. Establish `e` using `hFr3 Ω' φ hφ x`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Category.assoc]`. Use `_ = _ := by`.

Rewrite using `[e]`. Simplify using `only [Category.assoc]`. Both sides reduce to the same expression. Establish `hc'` using `fun j => hCP p g _ _ _ hPBS (T j) (nwt (T j).p) (hOne j).1 (hT j)`. Use `choose c' hc'' using hc'`.

Use `choose v hv using hc''`. Establish `hE` using `hES l p f n hp Y (fn g ϖ) T (fun j => nwt (T j).p) hOne hPt hSpe hBO _ _ _ _ Fr hlG hDense hSep hFr1 hTw c' v (fun j => (hv j).1) (fun j => (hv j).2.1) (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2) k 0`. Establish `hPBV` using `IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom ρ))`. Establish `hcV` using `fun j => hCP p g _ _ _ hPBV (T j) (nwt (T j).p) (hOne j).1 (hT j)`. Use `choose cV hcV' using hcV`.

Establish `hlVV : IsUnit ((l : ℕ) : V)`. Assume the negation of the conclusion as `h`. Establish `hm : ((l : ℕ) : V) ∈ IsLocalRing.maximalIdeal V` using `h`. Establish `hk : RingHom.ker r = IsLocalRing.maximalIdeal V` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)`. Rewrite `hm` using `[← hk, RingHom.mem_ker, map_natCast]`.

Conclude with `hl.ne_zero hm`. Set `φV : V →+* Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤)` to `(pullback.snd g (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom`. Establish `hlV : IsUnit ((l : ℕ) : Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤))`. Rewrite using `[← map_natCast φV l]`. Conclude with `hlVV.map φV`.

Establish `CCi` using `fun j => hCC l p g _ _ _ hPBV iY _ (Spec.map (CommRingCat.ofHom r)) (pullback.lift_snd _ _ _) hlV (T j) (nwt (T j).p) (cV j) (c' j) (hcV' j) (by rw [pullback.lift_fst]; exact ⟨v j, hv j⟩) k 0`. Establish `hcN : ∀ j, IsBC (T j) (nwt (T j).p) (jY ≫ pullback.fst g (Spec.map (CommRingCat.ofHom ρ))) (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) (c j)`. Introduce `j`. Take `⟨vK, e1, e2, e3, e4⟩` from `hc j`. Use `⟨vK, ?_, ?_, e3, ?_⟩` and prove the remaining obligations.

Rewrite using `[pullback.lift_fst]`. Conclude with `e1`. Rewrite using `[pullback.lift_fst]`. Conclude with `e2`. Rewrite using `[e4]`.

Use function extensionality and compare the values at `Ω' i1 i2 z`. Use `symm`. Apply `(hOne j).2 Ω' (z ≫ vK)` to reduce the goal to its premises. Introduce `h0`. Set `φ` to `Spec.preimage (z ≫ (c j).p ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))`.

Establish `h1 : φ.hom (p : Ω) = 0`. Rewrite using `[map_natCast]`. Conclude with `h0`. Establish `h2 : (p : Ω) = 0` using `φ.hom.injective (by rw [h1, map_zero])`. Apply `hp0` to reduce the goal to its premises.

Apply `(algebraMap K Ω).injective` to reduce the goal to its premises. Rewrite using `[map_natCast, h2, map_zero]`. Establish `CCj` using `fun j => hCC l p g _ _ _ hPBV jY _ (Spec.map (CommRingCat.ofHom V.subtype)) (pullback.lift_snd _ _ _) hlV (T j) (nwt (T j).p) (cV j) (c j) (hcV' j) (hcN j) k 0`. Establish `hunit : ∀ m : ℕ, IsUnit (((l ^ m : ℕ)) : kb)` using `fun m => by`. Rewrite using `[Nat.cast_pow]`.

Conclude with `hl.pow m`. Establish `hPs` using `pullHQ_surjective_of_forall_pull_bijective l (sch.map iY) k 0 (fun m => (HSG.1 (l ^ m) (hunit m) 0).1 k)`. Establish `hopc : ∀ j x, TranscendenceTraces.Corr.opQ l (c j) k 0 (sp x) = sp (TranscendenceTraces.Corr.opQ l (c' j) k 0 x)`. Introduce `j x`. Take `⟨y, rfl⟩` from `hPs x`.

Establish `e1` using `LinearMap.congr_fun (CCi j) y`. Establish `e2` using `LinearMap.congr_fun (CCj j) y`. Simplify using `only [LinearMap.comp_apply] at e1 e2`. Rewrite using `[hsp1, ← e2, ← hsp1, e1]`. Establish `hpow : ∀ (m : ℕ) y, (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ ^ m) (sp y) = sp ((pullHQ l (sch.map Fr) k 0 ^ m) y)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro y`. Both sides reduce to the same expression. Consider the case `succ m ih`.

Introduce `y`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← hsemi, ih]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨y, rfl⟩` from `sp.surjective x`.

Establish `hE'` using `LinearMap.congr_fun hE y`. Rewrite `hE'`, the goal using `[LinearMap.zero_apply]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at hE' ⊢`. Simplify using `only [hpow, hopc]`. Rewrite using `[← map_zero sp, ← hE', map_sum]`.

Simplify using `only [map_smul]`.
-/
theorem UpperTheory.Gal.Mod.esGen :
    SpecGood → ESPt → NwtOne → FrobQ → BaseFacts → DenseGen → FrEx → CorrPull → CorrComm → ESGen := by
  intro hSG hES hNwt hFQ hBF hDG hFrEx hCP hCC
  intro l _ p f n hp O _ _ _ ϖ hϖ hpu K _ _ κ _ _ hp0 hκ hfin Ω _ _ _ V hV kb _ _ _ r hr hrc hl Y g _ _ T hT hPt c hc σ hσ k
  let ρ : O →+* V := ((algebraMap K Ω).comp (algebraMap O K)).codRestrict V hV
  have hρ : CommRingCat.ofHom (algebraMap O κ) ≫ CommRingCat.ofHom (algebraMap κ kb) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom r := by
    ext a
    exact (hrc a).symm
  have hρK : CommRingCat.ofHom (algebraMap O K) ≫ CommRingCat.ofHom (algebraMap K Ω) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom V.subtype := by
    ext a
    rfl
  let iY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρ])
  let jY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom V.subtype)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρK])
  have HSG := @hSG O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrc Y g _ _ iY jY
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨sp, hsp1, hsp2⟩ := HSG.2 l hl k 0
  have hpO : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hpκ : (p : κ) = 0 := by
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hpO
    rw [← map_natCast (algebraMap O κ), ← hu, map_mul, hκ, mul_zero]
  have hpkb : (p : kb) = 0 := by
    rw [← map_natCast (algebraMap κ kb), hpκ, map_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP kb p := (CharP.charP_iff_prime_eq_zero hp).2 hpkb
  let τ : Gal(kb/κ) := AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv kb p f) (fun a => by
    show iterateFrobenius kb p f _ = _
    rw [iterateFrobenius_def, ← map_pow, hfin])
  have hτ : ∀ a, τ a = a ^ p ^ f := fun a => iterateFrobeniusEquiv_apply kb p f a
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have e := hsp2 σ 1 hσ (fun v => by rw [h1 v]; rfl) y
    rw [map_one] at e
    exact e.symm
  · have hcomp : ∀ x, sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ (sp x) :=
      hsp2 σ τ hσ (fun v => by rw [h2 v, hτ])
    let φG : kb →+* Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤) :=
      (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom
    have hpG : ((p : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) = 0 := by
      rw [← map_natCast φG p, hpkb, map_zero]
    have hlG : IsUnit ((l : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) := by
      rw [← map_natCast φG l]
      exact hl.map φG
    obtain ⟨Fr, hFr1, hFr2, hFr3⟩ := hFrEx p f hp κ kb hfin _
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) hpG τ hτ
    have hAF := hFQ l (geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) p f hp hpG hlG k
    have hFG : ∀ x, pullHQ l (sch.map Fr) k 0
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) = x := by
      intro x
      rw [galHQ_eq_pullHQ_galMap, ← pullHQ_comp_apply, ← Functor.map_comp, hFr2, hAF]
      rfl
    have hinvτ : ∀ x, galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) = x := by
      intro x
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hsemi : ∀ x, sp (pullHQ l (sch.map Fr) k 0 x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
      intro x
      calc sp (pullHQ l (sch.map Fr) k 0 x)
          = sp (pullHQ l (sch.map Fr) k 0
              (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
                (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [hinvτ]
        _ = sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) := by
            rw [hFG]
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹
              (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ
                (sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
            rw [← hcomp, hinvτ]
    have hpO0 : (p : O) ≠ 0 := by
      intro h0
      apply hp0
      rw [← map_natCast (algebraMap O K), h0, map_zero]
    obtain ⟨hLoc, hGen, hSpe, hBO⟩ := hBF p O ϖ hϖ hpO0 hpu Y g
    have hOne : ∀ j, Mod.One (T j) (nwt (T j).p) := fun j => hNwt p Y (T j) hLoc hGen
    have hβ : Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O κ)) =
        Spec.map (CommRingCat.ofHom ((algebraMap κ kb).comp (algebraMap O κ))) := by
      rw [← Spec.map_comp]
      rfl
    have hPBS : IsPullback
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        g (Mod.sp ((algebraMap κ kb).comp (algebraMap O κ))) := by
      have e := IsPullback.paste_horiz (IsPullback.of_hasPullback
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
      rw [hβ] at e
      exact e
    have hDense := hDG O ϖ hϖ kb ((algebraMap κ kb).comp (algebraMap O κ)) (by simp [hκ]) Y _ g _ _ hPBS
    have hSep : ∀ (Ω' : Type) [Field Ω'] (x x' : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        x' ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) →
        x ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
        x' ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) → x = x' := by
      intro Ω' _ x x' e1 e2
      apply pullback.hom_ext _ e2
      apply pullback.hom_ext
      · simpa only [Category.assoc] using e1
      · simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, e2, Category.assoc]
    have hTw : ∀ (Ω' : Type) [Field Ω'] (φ : Ω' →+* Ω'), (∀ a, φ a = a ^ p ^ f) →
        ∀ (x : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ Fr ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        twist φ Y (x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) := by
      intro Ω' _ φ hφ x
      have e := hFr3 Ω' φ hφ x
      calc _ = (x ≫ Fr ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
              (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))) := by
            simp only [Category.assoc]
        _ = _ := by
            rw [e]
            simp only [Category.assoc]
            rfl
    have hc' := fun j => hCP p g _ _ _ hPBS (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose c' hc'' using hc'
    choose v hv using hc''
    have hE := hES l p f n hp Y (fn g ϖ) T (fun j => nwt (T j).p) hOne hPt hSpe hBO _ _ _ _ Fr hlG hDense hSep hFr1 hTw c' v
      (fun j => (hv j).1) (fun j => (hv j).2.1) (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2) k 0
    have hPBV := IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom ρ))
    have hcV := fun j => hCP p g _ _ _ hPBV (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose cV hcV' using hcV
    have hlVV : IsUnit ((l : ℕ) : V) := by
      by_contra h
      have hm : ((l : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hk : RingHom.ker r = IsLocalRing.maximalIdeal V :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)
      rw [← hk, RingHom.mem_ker, map_natCast] at hm
      exact hl.ne_zero hm
    let φV : V →+* Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤) :=
      (pullback.snd g (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have hlV : IsUnit ((l : ℕ) : Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤)) := by
      rw [← map_natCast φV l]
      exact hlVV.map φV
    have CCi := fun j => hCC l p g _ _ _ hPBV iY _ (Spec.map (CommRingCat.ofHom r)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c' j) (hcV' j) (by rw [pullback.lift_fst]; exact ⟨v j, hv j⟩) k 0
    have hcN : ∀ j, IsBC (T j) (nwt (T j).p) (jY ≫ pullback.fst g (Spec.map (CommRingCat.ofHom ρ)))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) (c j) := by
      intro j
      obtain ⟨vK, e1, e2, e3, e4⟩ := hc j
      refine ⟨vK, ?_, ?_, e3, ?_⟩
      · rw [pullback.lift_fst]
        exact e1
      · rw [pullback.lift_fst]
        exact e2
      · rw [e4]
        funext Ω' i1 i2 z
        symm
        apply (hOne j).2 Ω' (z ≫ vK)
        intro h0
        let φ := Spec.preimage (z ≫ (c j).p ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
        have h1 : φ.hom (p : Ω) = 0 := by
          rw [map_natCast]
          exact h0
        have h2 : (p : Ω) = 0 := φ.hom.injective (by rw [h1, map_zero])
        apply hp0
        apply (algebraMap K Ω).injective
        rw [map_natCast, h2, map_zero]
    have CCj := fun j => hCC l p g _ _ _ hPBV jY _ (Spec.map (CommRingCat.ofHom V.subtype)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c j) (hcV' j) (hcN j) k 0
    have hunit : ∀ m : ℕ, IsUnit (((l ^ m : ℕ)) : kb) := fun m => by
      rw [Nat.cast_pow]
      exact hl.pow m
    have hPs := pullHQ_surjective_of_forall_pull_bijective l (sch.map iY) k 0 (fun m => (HSG.1 (l ^ m) (hunit m) 0).1 k)
    have hopc : ∀ j x, TranscendenceTraces.Corr.opQ l (c j) k 0 (sp x) = sp (TranscendenceTraces.Corr.opQ l (c' j) k 0 x) := by
      intro j x
      obtain ⟨y, rfl⟩ := hPs x
      have e1 := LinearMap.congr_fun (CCi j) y
      have e2 := LinearMap.congr_fun (CCj j) y
      simp only [LinearMap.comp_apply] at e1 e2
      rw [hsp1, ← e2, ← hsp1, e1]
    have hpow : ∀ (m : ℕ) y, (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ ^ m) (sp y) =
        sp ((pullHQ l (sch.map Fr) k 0 ^ m) y) := by
      intro m
      induction m with
      | zero => intro y; rfl
      | succ m ih =>
        intro y
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← hsemi, ih]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have hE' := LinearMap.congr_fun hE y
    rw [LinearMap.zero_apply] at hE' ⊢
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at hE' ⊢
    simp only [hpow, hopc]
    rw [← map_zero sp, ← hE', map_sum]
    simp only [map_smul]
