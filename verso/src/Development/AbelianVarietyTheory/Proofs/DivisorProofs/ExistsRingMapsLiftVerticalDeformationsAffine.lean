import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open TrivSqZeroExt in

/- English proof (translation)
Use `⟨PrimeSpectrum.comap (inlHom S S) s, ?_⟩` and prove the remaining obligations. Use `show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ s) = s`. Use extensionality with `x`. Establish `hr : inr x.snd ∈ s.asIdeal` using `s.2.mem_of_pow_mem 2 (by`. Apply the tactic sequence `rw [show (inr x.snd : DualNumber S) ^ 2 = 0 by ext <;> simp [pow_two]]`.

Conclude with `s.asIdeal.zero_mem)`. Simplify using `only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `inl x.fst ∈ s.asIdeal ↔ x ∈ s.asIdeal`. Establish `e1 : inl x.fst + inr x.snd = x` using `inl_fst_add_inr_snd_eq x`. Establish `e2 : inl x.fst = x - inr x.snd` using `eq_sub_of_add_eq e1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← e1]`. Conclude with `s.asIdeal.add_mem h hr`. Introduce `h`.

Rewrite using `[e2]`. Conclude with `s.asIdeal.sub_mem h hr`.
-/
theorem exists_spMap_fst_eq {S : Type} [CommRing S] (s : Sp (DualNumber S)) :
    ∃ t : Sp S, spMap (fstHom S S S).toRingHom t = s := by
  refine ⟨PrimeSpectrum.comap (inlHom S S) s, ?_⟩
  show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ s) = s
  ext x
  have hr : inr x.snd ∈ s.asIdeal := s.2.mem_of_pow_mem 2 (by
    rw [show (inr x.snd : DualNumber S) ^ 2 = 0 by ext <;> simp [pow_two]]
    exact s.asIdeal.zero_mem)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change inl x.fst ∈ s.asIdeal ↔ x ∈ s.asIdeal
  have e1 : inl x.fst + inr x.snd = x := inl_fst_add_inr_snd_eq x
  have e2 : inl x.fst = x - inr x.snd := eq_sub_of_add_eq e1
  constructor
  · intro h
    rw [← e1]
    exact s.asIdeal.add_mem h hr
  · intro h
    rw [e2]
    exact s.asIdeal.sub_mem h hr

/- English proof (translation)
Introduce `s _`. Take `⟨t, rfl⟩` from `exists_spMap_fst_eq s`. Conclude with `h (Set.mem_univ t)`.
-/
theorem le_preimage_of_fst {S : Type} [CommRing S] {T : Scheme.{0}} (x : Sp (DualNumber S) ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  obtain ⟨t, rfl⟩ := exists_spMap_fst_eq s
  exact h (Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

/- English proof (translation)
Establish `e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ X.ptY v = z ≫ toFlag M` using `(X.ptY_frMap hv).trans hz.symm`. Establish `hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z` using `fun s _ => by`. Use `ho (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`. Conclude with `this`.

Establish `hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange` using `le_preimage_of_fst _ _ (by`. Rewrite using `[e]`. Introduce and unpack `s -`. Conclude with `⟨(z ≫ M.σ) s, rfl⟩)`. Establish `hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z)`.

Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hb (Set.mem_univ s)`. Take `⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v` from `⟨_, IsOpenImmersion.lift_fac _ _ hr⟩`. Establish `ered : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = z ≫ M.σ`. Rewrite using `[← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]`.

Establish `hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z` using `le_preimage_of_fst _ _ (by rw [ered]; exact hU)`. Take `⟨zv, hzv, -⟩` from `M.existsUnique_lift w hwU`. Establish `hred : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z` using `(M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl`. Use `⟨zv, ?_, hred⟩` and prove the remaining obligations. Rewrite using `[toFlag, ← Category.assoc, hzv, hw]`.
-/
theorem exists_dualLift {S : Type} [CommRing S] [Algebra c.F S] {Q : FrPt Xo c S} {v : FrPt Xo c (DualNumber S)}
    (hv : FrMap (TrivSqZeroExt.fstHom c.F S S) v Q) {z : Sp S ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber S) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z := by
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ X.ptY v = z ≫ toFlag M :=
    (X.ptY_frMap hv).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_fst _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_fst _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

def vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (DualNumber S) :=
  Matrix.of fun i j => TrivSqZeroExt.inl ((1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j) +
    TrivSqZeroExt.inr ((Pi.single b.toF (1 : S) : GlobalTheory.FlagTan.FIx Dw → S) (some ⟨σ, i, j⟩))

/- English proof (translation)
Establish `e : (TrivSqZeroExt.fstHom S S S).toRingHom.mapMatrix (vertMat (S` using `S) b σ) = 1 := by`. Use extensionality with `i j`. Simplify using `[vertMat]`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Use `show IsUnit ((TrivSqZeroExt.fstHom S S S).toRingHom _)`.

Rewrite using `[RingHom.map_det, e, Matrix.det_one]`. Conclude with `isUnit_one`.
-/
theorem isUnit_det_vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    IsUnit (vertMat (S := S) b σ).det := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.mapMatrix (vertMat (S := S) b σ) = 1 := by
    ext i j; simp [vertMat]
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  show IsUnit ((TrivSqZeroExt.fstHom S S S).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
Establish `hτo : ⊤ ≤ tau hW ⁻¹ᵁ M.off` using `tau_le hW (hle.trans inf_le_left)`. Establish `hτk : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ X.F.U k` using `fun x hx => tau_le hW (hle.trans inf_le_right) hx`. Establish `hF : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ flagOpen X` using `fun x hx => by`. Use `hτo hx` as an intermediate fact. Rewrite `this` using `[M.off_eq]`.

Conclude with `this`. Take `⟨_, hch⟩` from `exists_chartFr _ hF`. Take `⟨Q₀, hQ₀⟩` from `hch k hτk`. Establish `e₀ : tau hW ≫ toFlag M = X.ptY Q₀` using `GlobalTheory.FlagMod.FlagCover.eq_ptY hQ₀.lies`. Take `⟨Q₁, hQ₁⟩` from `GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W)) Q₀`.

Establish `hred : FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) Q₁ Q₀` using `GlobalTheory.FlagTan.frMap_of_comp hQ₁ (GlobalTheory.FlagTan.frMap_id Q₀) fun _ => rfl`. Establish `hV : ∀ b : VIx Dw, ∃ V : FrPt Xo c (DualNumber Γ(M.X, W)), GlobalTheory.Frames.FrChg (vertMat b) ((1 : (DualNumber Γ(M.X, W))ˣ) : DualNumber Γ(M.X, W)) Q₁ V` using `fun b => (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ Q₁ (vertMat b) 1 (isUnit_det_vertMat b)).exists`. Use `choose V hV using hV`. Establish `hVr : ∀ b, FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) (V b) Q₀` using `fun b => by`. Use `(GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hred).2 ?_` and prove the remaining obligations.

Use `(GlobalTheory.Frames.frChg_calculus E H Dw l Xo c Γ(M.X, W)).2.1 Q₀ using 2 with σ` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[vertMat]`. Simplify using the standard rewrite rules. Use `choose zv hzv hzr using fun b => exists_dualLift M (hVr b) e₀ hτo`.

Establish `hzW : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ W` using `fun b => le_preimage_of_fst _ _ (by rw [hzr b]; exact tau_le hW le_rfl)`. Use `⟨fun b => GlobalTheory.FlagMod.ev (zv b) W (hzW b), fun b s => ?_, ?_⟩` and prove the remaining obligations. Establish `h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom Γ(M.X, W) Γ(M.X, W) Γ(M.X, W)).toRingHom ≫ zv b) ⁻¹ᵁ W`. Rewrite using `[hzr b]`. Conclude with `tau_le hW le_rfl`.

Establish `h1` using `GlobalTheory.FlagMod.ev_spMap _ (zv b) W (hzW b) h'`. Rewrite `h1` using `[GlobalTheory.FlagMod.ev_congr (hzr b) W h' (tau_le hW le_rfl), GlobalTheory.FlagMod.ev_tau_self]`. Conclude with `(DFunLike.congr_fun h1 s).symm`. Introduce `K _ _ ψ hk Q hQ b`. Establish `hx : frX Q = spMap ψ ≫ frX Q₀`.

Set `w₀ : Sp Γ(M.X, W) ⟶ X.Yo` to `pullback.lift (tau hW ≫ toFlag M) (frX Q₀) hQ₀.over.symm`. Set `w₁ : Sp K ⟶ X.Yo` to `pullback.lift ((spMap ψ ≫ tau hW) ≫ toFlag M) (frX Q) hQ.over.symm`. Establish `e : w₁ = spMap ψ ≫ w₀`. Rewrite using `[← cancel_mono X.inc]`. Simplify using `only [w₀, w₁, Category.assoc, pullback.lift_fst]`.

Use `congrArg (· ≫ pullback.snd X.π Y.j) e` as an intermediate fact. Simplify `this` using `only [w₀, w₁, Category.assoc, pullback.lift_snd]`. Establish `hs : spMap (algebraMap c.F K) = spMap (ψ.comp (algebraMap c.F Γ(M.X, W)))`. Rewrite using `[← frX_snd Q, hx, Category.assoc, frX_snd Q₀, spMap_comp']`. Establish `hψ : ψ.comp (algebraMap c.F Γ(M.X, W)) = algebraMap c.F K` using `(congrArg CommRingCat.Hom.hom (Spec.map_injective hs)).symm`.

Set `φ : Γ(M.X, W) →ₐ[c.F] K` to `{ ψ with commutes' := fun r => DFunLike.congr_fun hψ r }`. Set `φε : DualNumber Γ(M.X, W) →ₐ[c.F] DualNumber K` to `{ dualMap ψ with commutes' := fun r => by`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ← DFunLike.congr_fun hψ r] }`. Take `⟨Q', hQ'⟩` from `GlobalTheory.FlagTan.exists_frMap φ Q₀`. Establish `eQ : Q = Q'` using `hQ.unique (hQ₀.frMap hQ' (by rw [Category.assoc]) hk)`.

Substitute `eQ` using the available equality. Take `⟨y₀, hy₀⟩` from `GlobalTheory.FlagTan.exists_frMap φε Q₁`. Take `⟨w, hw⟩` from `GlobalTheory.FlagTan.exists_frMap φε (V b)`. Use `⟨w, ⟨y₀, GlobalTheory.FlagTan.frMap_of_comp hQ' (GlobalTheory.FlagTan.frMap_comp (χ := φε.comp (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W))) hQ₁ hy₀ fun _ => rfl) fun a => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [φ, φε, dualMap]`.

Establish `h2` using `(GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hy₀).1 hw`. Unfold `GlobalTheory.FlagTan.IsShift`. Use `h2 using 2 with σ` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i j <;> simp [GlobalTheory.FlagTan.unip, vertMat, φε, dualMap, Matrix.one_apply, Pi.single_apply] <;> split_ifs <;> simp`. Apply the tactic sequence `ext <;> simp [GlobalTheory.FlagTan.unip₀, φε, dualMap, GlobalTheory.FlagTan.VIx.toF]`.

Establish `h3 : spMap (GlobalTheory.FlagMod.ev (zv b) W (hzW b)) ≫ tau hW = zv b` using `GlobalTheory.FlagMod.spMap_ev (zv b) hW (hzW b)`. Rewrite using `[← spMap_comp', Category.assoc, ← Category.assoc (spMap _) (tau hW), h3, hzv b]`. Establish `e4 : dualMap ψ = φε.toRingHom` using `RingHom.ext fun _ => rfl`. Rewrite using `[e4]`. Conclude with `X.ptY_frMap hw`.
-/
theorem exists_vertLift (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) :
    ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  have hτo : ⊤ ≤ tau hW ⁻¹ᵁ M.off := tau_le hW (hle.trans inf_le_left)
  have hτk : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun x hx => tau_le hW (hle.trans inf_le_right) hx
  have hF : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun x hx => by
    have := hτo hx
    rw [M.off_eq] at this
    exact this
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q₀, hQ₀⟩ := hch k hτk
  have e₀ : tau hW ≫ toFlag M = X.ptY Q₀ := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ₀.lies
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W)) Q₀
  have hred : FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) Q₁ Q₀ :=
    GlobalTheory.FlagTan.frMap_of_comp hQ₁ (GlobalTheory.FlagTan.frMap_id Q₀) fun _ => rfl
  have hV : ∀ b : VIx Dw, ∃ V : FrPt Xo c (DualNumber Γ(M.X, W)),
      GlobalTheory.Frames.FrChg (vertMat b) ((1 : (DualNumber Γ(M.X, W))ˣ) : DualNumber Γ(M.X, W)) Q₁ V := fun b =>
    (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ Q₁ (vertMat b) 1 (isUnit_det_vertMat b)).exists
  choose V hV using hV
  have hVr : ∀ b, FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) (V b) Q₀ := fun b => by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hred).2 ?_
    convert (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c Γ(M.X, W)).2.1 Q₀ using 2 with σ
    · ext i j; simp [vertMat]
    · simp
  choose zv hzv hzr using fun b => exists_dualLift M (hVr b) e₀ hτo
  have hzW : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ W := fun b => le_preimage_of_fst _ _ (by rw [hzr b]; exact tau_le hW le_rfl)
  refine ⟨fun b => GlobalTheory.FlagMod.ev (zv b) W (hzW b), fun b s => ?_, ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom Γ(M.X, W) Γ(M.X, W) Γ(M.X, W)).toRingHom ≫ zv b) ⁻¹ᵁ W := by
      rw [hzr b]; exact tau_le hW le_rfl
    have h1 := GlobalTheory.FlagMod.ev_spMap _ (zv b) W (hzW b) h'
    rw [GlobalTheory.FlagMod.ev_congr (hzr b) W h' (tau_le hW le_rfl), GlobalTheory.FlagMod.ev_tau_self] at h1
    exact (DFunLike.congr_fun h1 s).symm
  intro K _ _ ψ hk Q hQ b

  have hx : frX Q = spMap ψ ≫ frX Q₀ := by
    let w₀ : Sp Γ(M.X, W) ⟶ X.Yo := pullback.lift (tau hW ≫ toFlag M) (frX Q₀) hQ₀.over.symm
    let w₁ : Sp K ⟶ X.Yo := pullback.lift ((spMap ψ ≫ tau hW) ≫ toFlag M) (frX Q) hQ.over.symm
    have e : w₁ = spMap ψ ≫ w₀ := by
      rw [← cancel_mono X.inc]
      simp only [w₀, w₁, Category.assoc, pullback.lift_fst]
    have := congrArg (· ≫ pullback.snd X.π Y.j) e
    simpa only [w₀, w₁, Category.assoc, pullback.lift_snd] using this
  have hs : spMap (algebraMap c.F K) = spMap (ψ.comp (algebraMap c.F Γ(M.X, W))) := by
    rw [← frX_snd Q, hx, Category.assoc, frX_snd Q₀, spMap_comp']
  have hψ : ψ.comp (algebraMap c.F Γ(M.X, W)) = algebraMap c.F K :=
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)).symm
  let φ : Γ(M.X, W) →ₐ[c.F] K := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  let φε : DualNumber Γ(M.X, W) →ₐ[c.F] DualNumber K :=
    { dualMap ψ with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ← DFunLike.congr_fun hψ r] }
  obtain ⟨Q', hQ'⟩ := GlobalTheory.FlagTan.exists_frMap φ Q₀
  have eQ : Q = Q' := hQ.unique (hQ₀.frMap hQ' (by rw [Category.assoc]) hk)
  subst eQ
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.FlagTan.exists_frMap φε Q₁
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φε (V b)
  refine ⟨w, ⟨y₀, GlobalTheory.FlagTan.frMap_of_comp hQ' (GlobalTheory.FlagTan.frMap_comp (χ := φε.comp (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W))) hQ₁ hy₀ fun _ => rfl) fun a => ?_, ?_⟩, ?_⟩
  · ext <;> simp [φ, φε, dualMap]
  · have h2 := (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hy₀).1 hw
    unfold GlobalTheory.FlagTan.IsShift
    convert h2 using 2 with σ
    · ext i j <;> simp [GlobalTheory.FlagTan.unip, vertMat, φε, dualMap, Matrix.one_apply, Pi.single_apply] <;> split_ifs <;> simp
    · ext <;> simp [GlobalTheory.FlagTan.unip₀, φε, dualMap, GlobalTheory.FlagTan.VIx.toF]
  · have h3 : spMap (GlobalTheory.FlagMod.ev (zv b) W (hzW b)) ≫ tau hW = zv b := GlobalTheory.FlagMod.spMap_ev (zv b) hW (hzW b)
    rw [← spMap_comp', Category.assoc, ← Category.assoc (spMap _) (tau hW), h3, hzv b]
    have e4 : dualMap ψ = φε.toRingHom := RingHom.ext fun _ => rfl
    rw [e4]
    exact X.ptY_frMap hw

end GlobalTheory.CompHS
