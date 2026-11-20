import Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsChartFrBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology

/- English proof (translation)
Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`. Conclude with `(congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)`.
-/
theorem openImmersion_comp_structure_eq_generic (Y : Model Xo c (RingHom.id c.F)) : Y.j ≫ Y.s = pullback.snd _ _ := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

/- English proof (translation)
Establish `hr : Set.range z ⊆ Set.range T.X.inc`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `(opensRange_inc T.X).ge (hO (Set.mem_univ s))`. Take `⟨w, rfl⟩ : ∃ w, w ≫ T.X.inc = z` from `⟨_, IsOpenImmersion.lift_fac T.X.inc z hr⟩`. Use `(T.X.exists_chartFr w ?_ k hz).imp fun _ => And.left` and prove the remaining obligations.

Rewrite using `[← hs, ← openImmersion_comp_structure_eq_generic T.Y, ← pullback.condition_assoc, Category.assoc]`.
-/
theorem exists_chartFr_alg (T : TorFlag Xo c) {S : Type} [CommRing S] [Algebra c.F S] (z : Sp S ⟶ T.X.YY)
    (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X) (hs : z ≫ flagStr T.X = spMap (algebraMap c.F S)) (k : T.X.F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) : ∃ Q : FrPt Xo c S, T.X.F.ChartFr k z hz Q := by
  have hr : Set.range z ⊆ Set.range T.X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc T.X).ge (hO (Set.mem_univ s))
  obtain ⟨w, rfl⟩ : ∃ w, w ≫ T.X.inc = z := ⟨_, IsOpenImmersion.lift_fac T.X.inc z hr⟩
  refine (T.X.exists_chartFr w ?_ k hz).imp fun _ => And.left
  rw [← hs, ← openImmersion_comp_structure_eq_generic T.Y, ← pullback.condition_assoc, Category.assoc]

def zOf {T : TorFlag Xo c} (y : GlobalTheory.CxPts (flagStr T.X) σ) : Sp (CAt σ) ⟶ T.X.YY := y.1

/- English proof (translation)
Establish `hf'` using `(GlobalTheory.AllWt.secZ_nat Xo c a n).ge hf`. Use `⟨(secOf T.X _ ⟨f, hf'⟩).loc i, fun y hz Q hO hQ => ?_⟩` and prove the remaining obligations. Establish `: _root_.IsReduced (CAt σ)` using `(inferInstance : _root_.IsReduced ℂ)`. Establish `a` using `evR_eq_val_secOf (z := zOf y) ⟨f, hf'⟩ hO hQ ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)).1 Q)`. Simplify using `only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a`.

Conclude with `(congrArg toC a).trans (ev_eq (mem_ptsIn_inf.2 ⟨hO, hz⟩) _).symm`.
-/
theorem exists_fun_chart (T : TorFlag Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (i : T.X.F.J) : ∃ u : Γ(T.X.YY, flagOpen T.X ⊓ T.X.F.U i), ∀ (y : GlobalTheory.CxPts (flagStr T.X) σ)
      (hz : ⊤ ≤ zOf y ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)), y ∈ ptsIn _ σ (flagOpen T.X) →
      T.X.F.ChartFr i (zOf y) hz Q → toC (evR Xo c f Q) = ev _ σ _ u y := by
  have hf' := (GlobalTheory.AllWt.secZ_nat Xo c a n).ge hf
  refine ⟨(secOf T.X _ ⟨f, hf'⟩).loc i, fun y hz Q hO hQ => ?_⟩
  have : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have a := evR_eq_val_secOf (z := zOf y) ⟨f, hf'⟩ hO hQ ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)).1 Q)
  simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a
  exact (congrArg toC a).trans (ev_eq (mem_ptsIn_inf.2 ⟨hO, hz⟩) _).symm

/- English proof (translation)
Take `⟨-, g1, g2, -⟩` from `GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)`. Take `⟨W, hW, hbW, hWle⟩` from `GlobalTheory.Points.exists_isAffineOpen_le (s b₀).1 hi`. Use `set B' := B ∩ s ⁻¹' ptsIn _ σ W with hB'`. Establish `hb₀' : b₀ ∈ B'` using `⟨hb₀, hbW⟩`. Set `A : Type` to `Γ(T.X.YY, W)`.

Set `α : c.F →+* A` to `(GlobalTheory.FlagMod.ev (GlobalTheory.FlagMod.tau hW ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)`. Use `letI : Algebra c.F A := α.toAlgebra`. Establish `hα : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap (algebraMap c.F A)` using `(GlobalTheory.FlagMod.spMap_ev_top _).symm`. Establish `hτi : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U i` using `GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_right)`. Take `⟨yA, hyA⟩` from `exists_chartFr_alg T (S := A) (GlobalTheory.FlagMod.tau hW) (GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_left)) hα i hτi`.

Establish `hφ : ∀ y : GlobalTheory.CxPts (flagStr T.X) σ, y ∈ ptsIn _ σ W → ∃ φ : A →ₐ[c.F] CAt σ, (∀ u, toC (φ u) = ev _ σ W u y) ∧ spMap φ.toRingHom ≫ GlobalTheory.FlagMod.tau hW = zOf y`. Introduce `y hy`. Set `ψ : A →+* CAt σ` to `GlobalTheory.FlagMod.ev (zOf y) W hy`. Establish `e₁ : spMap ψ ≫ GlobalTheory.FlagMod.tau hW = zOf y` using `GlobalTheory.FlagMod.spMap_ev (zOf y) hW hy`. Establish `e₂ : spMap (ψ.comp (algebraMap c.F A)) = spMap (algebraMap c.F (CAt σ))`.

Establish `e : spMap (ψ.comp (algebraMap c.F A)) = spMap ψ ≫ spMap (algebraMap c.F A)` using `Spec.map_comp _ _`. Rewrite using `[e, ← hα, ← Category.assoc, e₁]`. Conclude with `y.2`. Establish `e₃ : ψ.comp (algebraMap c.F A) = algebraMap c.F (CAt σ)` using `congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)`. Conclude with `⟨⟨ψ, fun x => RingHom.congr_fun e₃ x⟩, fun u => (ev_eq hy u).symm, e₁⟩`.

Use `choose φ' hφ₁ hφ₂ using hφ`. Set `φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)` to `fun b => if hb : b ∈ B' then φ' (s b) hb.2 else φ' (s b₀) hbW`. Establish `hφb : ∀ b (hb : b ∈ B'), φ b = φ' (s b) hb.2` using `fun b hb => dif_pos hb`. Use `choose y hy using fun b => GlobalTheory.FlagMod.exists_frMap (φ b) yA`. Establish `hsub : ∀ b ∈ B', s b ∈ ptsIn _ σ (flagOpen T.X) ∧ s b ∈ ptsIn _ σ (T.X.F.U i)` using `fun b hb => mem_ptsIn_inf.1 (ptsIn_mono hWle hb.2)`.

Establish `hQ : ∀ b (hb : b ∈ B'), T.X.F.ChartFr i (zOf (s b)) (hsub b hb).2 (y b)` using `fun b hb => hyA.frMap (hy b) (by rw [hφb b hb]; exact hφ₂ _ _) _`. Take `⟨k₀, x₀, t₀, ht₀⟩` from `hU.2.2.1 (y b₀)`. Take `⟨B₁, z, hB₁, hb₁, hs₁, hz, hz₀, hl⟩` from `GlobalTheory.HolChartLift.exists_hol_lift E H D l Xo c σ r V hσ hU A yA m B' φ y (ho W) (fun u => (hd W u).congr fun b hb => by rw [hφb b hb]; exact hφ₁ _ _ u) (fun b _ => hy b) b₀ hb₀' k₀ x₀ t₀ ht₀`. Distinguish the cases in `hk : k₀ = k`. Use `swap`.

Use `(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_ filter_upwards [hB₁.mem_nhds hb₁] with b hb` and prove the remaining obligations. Use `hZ i (s b) fun x hx e => hk ?_` and prove the remaining obligations. Take `⟨hc, t, ht⟩` from `hl b hb`. Establish `e' : T.X.ptY (V.un k ⟨x, hx⟩) = zOf (s b)` using `e`. Establish `hlx : T.X.F.Lies (zOf (s b)) (V.un k ⟨x, hx⟩)` using `e' ▸ T.X.lies_ptY _`.

Take `⟨t', ht'⟩` from `(hQ b (hs₁ hb)).exists_frBor hlx`. Take `⟨γ, -, β, -, h'⟩` from `(hU.2.2.2.1 k₀ k _ _).1 ⟨_, g1 _ _ _ _ _ ht ht'⟩`. Conclude with `(Sigma.mk.inj h').1.symm`. Substitute `hk` using the available equality. Take `⟨a', n', hD', g, hg, f, hf, hg0, hf0⟩` from `hN (y b₀)`.

Take `⟨ug, hug⟩` from `exists_fun_chart (σ := σ) T hg i`. Take `⟨uf, huf⟩` from `exists_fun_chart (σ := σ) T hf i`. Set `x : (Fin m → ℂ) → Frame (V.X k₀).Ψ r` to `fun b => ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt (V.X k₀) x₀.1 (z b)`. Establish `hx₀ : x b₀ = x₀.1`. Simplify using `only [x, hz₀]`.

Conclude with `ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.cpt_zero _ _`. Establish `hn` using `hB₁.mem_nhds hb₁`. Establish `hxd : DifferentiableOn ℂ x B₁` using `(ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.diff_cpt _ _).comp_differentiableOn hz`. Establish `hsec : ∀ {la Q}, (V.X k₀).IsSec la Q → DifferentiableAt ℂ (fun b => Q (x b)) b₀` using `fun hQ => (hQ.1.comp hxd fun b hb => (hl b hb).1).differentiableAt hn`. Establish `hfun : ∀ u : Γ(T.X.YY, flagOpen T.X ⊓ T.X.F.U i), DifferentiableAt ℂ (fun b => ev _ σ _ u (s b)) b₀` using `fun u => (hd _ u).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)`.

Establish `d₁` using `hsec hP`. Establish `d₂` using `hsec (hU.2.2.2.2.1 a' n' hD' g hg k₀)`. Establish `d₃` using `hsec (hU.2.2.2.2.1 _ _ (dom_add hD hD') f hf k₀)`. Establish `n₃ : rdU V f k₀ (x b₀) ≠ 0`. Rewrite using `[hx₀, rdU_eq, evR_frBor hf (g2 _ _ _ ht₀)]`.

Conclude with `mul_ne_zero (chr_ne_zero _ _) hf0`. Establish `n₂ : ev _ σ _ ug (s b₀) ≠ 0`. Rewrite using `[← hug _ _ _ (hsub b₀ hb₀').1 (hQ b₀ hb₀')]`. Conclude with `hg0`. Establish `hq : DifferentiableAt ℂ (fun b => P (x b) * rdU V g k₀ (x b) * ev _ σ _ uf (s b) * (rdU V f k₀ (x b) * ev _ σ _ ug (s b))⁻¹) b₀` using `((d₁.mul d₂).mul (hfun uf)).mul ((d₃.mul (hfun ug)).inv (mul_ne_zero n₃ n₂))`.

Use `hq.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hn, (d₃.mul (hfun ug)).continuousAt.eventually_ne (mul_ne_zero n₃ n₂)] with b hb hne`. Take `⟨hc, t, ht⟩` from `hl b hb`. Establish `hb'` using `hs₁ hb`. Establish `ht'` using `g2 _ _ _ ht`.

Establish `e₁ : P (x b) = chr (fun i => (ex D a n i : ℤ)) t⁻¹ * h i (s b)` using `hR (x b) hc i (s b) (hsub b hb').2 (y b) t⁻¹ (GlobalTheory.FlagMod.FlagCover.eq_ptY ((hQ b hb').lies.frBor ht')).symm (hQ b hb') ht'`. Establish `e₂ : rdU V g k₀ (x b) = _` using `(rdU_eq V g k₀ ⟨_, hc⟩).trans (evR_frBor hg ht')`. Establish `e₃ : rdU V f k₀ (x b) = _` using `(rdU_eq V f k₀ ⟨_, hc⟩).trans (evR_frBor hf ht')`. Rewrite `e₂` using `[hug _ _ _ (hsub b hb').1 (hQ b hb')]`. Rewrite `e₃` using `[huf _ _ _ (hsub b hb').1 (hQ b hb'), ex_add_int, chr_add]`.

Use `replace hne : rdU V f k₀ (x b) * ev _ σ _ ug (s b) ≠ 0 := hne`. Use `(eq_mul_inv_iff_mul_eq₀ hne).2 ?_` and prove the remaining obligations. Rewrite using `[e₁, e₂, e₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem differentiableAt_reads {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) (hN : NV Xo c σ a n) {k : V.Comp} {P : Frame (V.X k).Ψ r → ℂ}
    (hP : (V.X k).IsSec (laU V a n k) P)
    {h : (T.X.LL fun i => (ex D a n i : ℤ)).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T (fun i => (ex D a n i : ℤ)) k P h) (hZ : OffZero V T k h) (i : T.X.F.J) {m : ℕ}
    {B : Set (Fin m → ℂ)} (s : (Fin m → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ)
    (ho : ∀ W, IsOpen (B ∩ s ⁻¹' ptsIn _ σ W))
    (hd : ∀ W (u : Γ(T.X.YY, W)), DifferentiableOn ℂ (fun b => ev _ σ W u (s b)) (B ∩ s ⁻¹' ptsIn _ σ W))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hi : s b₀ ∈ ptsIn _ σ (flagOpen T.X ⊓ T.X.F.U i)) :
    DifferentiableAt ℂ (fun b => h i (s b)) b₀ := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  obtain ⟨W, hW, hbW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (s b₀).1 hi
  set B' := B ∩ s ⁻¹' ptsIn _ σ W with hB'
  have hb₀' : b₀ ∈ B' := ⟨hb₀, hbW⟩
  let A : Type := Γ(T.X.YY, W)
  let α : c.F →+* A := (GlobalTheory.FlagMod.ev (GlobalTheory.FlagMod.tau hW ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  letI : Algebra c.F A := α.toAlgebra
  have hα : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap (algebraMap c.F A) := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hτi : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_right)
  obtain ⟨yA, hyA⟩ := exists_chartFr_alg T (S := A) (GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_left)) hα i hτi
  have hφ : ∀ y : GlobalTheory.CxPts (flagStr T.X) σ, y ∈ ptsIn _ σ W → ∃ φ : A →ₐ[c.F] CAt σ,
      (∀ u, toC (φ u) = ev _ σ W u y) ∧ spMap φ.toRingHom ≫ GlobalTheory.FlagMod.tau hW = zOf y := by
    intro y hy
    let ψ : A →+* CAt σ := GlobalTheory.FlagMod.ev (zOf y) W hy
    have e₁ : spMap ψ ≫ GlobalTheory.FlagMod.tau hW = zOf y := GlobalTheory.FlagMod.spMap_ev (zOf y) hW hy
    have e₂ : spMap (ψ.comp (algebraMap c.F A)) = spMap (algebraMap c.F (CAt σ)) := by
      have e : spMap (ψ.comp (algebraMap c.F A)) = spMap ψ ≫ spMap (algebraMap c.F A) := Spec.map_comp _ _
      rw [e, ← hα, ← Category.assoc, e₁]
      exact y.2
    have e₃ : ψ.comp (algebraMap c.F A) = algebraMap c.F (CAt σ) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
    exact ⟨⟨ψ, fun x => RingHom.congr_fun e₃ x⟩, fun u => (ev_eq hy u).symm, e₁⟩
  choose φ' hφ₁ hφ₂ using hφ
  let φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b => if hb : b ∈ B' then φ' (s b) hb.2 else φ' (s b₀) hbW
  have hφb : ∀ b (hb : b ∈ B'), φ b = φ' (s b) hb.2 := fun b hb => dif_pos hb
  choose y hy using fun b => GlobalTheory.FlagMod.exists_frMap (φ b) yA
  have hsub : ∀ b ∈ B', s b ∈ ptsIn _ σ (flagOpen T.X) ∧ s b ∈ ptsIn _ σ (T.X.F.U i) := fun b hb =>
    mem_ptsIn_inf.1 (ptsIn_mono hWle hb.2)
  have hQ : ∀ b (hb : b ∈ B'), T.X.F.ChartFr i (zOf (s b)) (hsub b hb).2 (y b) := fun b hb =>
    hyA.frMap (hy b) (by rw [hφb b hb]; exact hφ₂ _ _) _
  obtain ⟨k₀, x₀, t₀, ht₀⟩ := hU.2.2.1 (y b₀)
  obtain ⟨B₁, z, hB₁, hb₁, hs₁, hz, hz₀, hl⟩ := GlobalTheory.HolChartLift.exists_hol_lift E H D l Xo c σ r V hσ hU A yA m B' φ y
    (ho W) (fun u => (hd W u).congr fun b hb => by rw [hφb b hb]; exact hφ₁ _ _ u) (fun b _ => hy b) b₀ hb₀' k₀ x₀ t₀ ht₀
  by_cases hk : k₀ = k
  swap
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hB₁.mem_nhds hb₁] with b hb
    refine hZ i (s b) fun x hx e => hk ?_
    obtain ⟨hc, t, ht⟩ := hl b hb
    have e' : T.X.ptY (V.un k ⟨x, hx⟩) = zOf (s b) := e
    have hlx : T.X.F.Lies (zOf (s b)) (V.un k ⟨x, hx⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := (hQ b (hs₁ hb)).exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k₀ k _ _).1 ⟨_, g1 _ _ _ _ _ ht ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨a', n', hD', g, hg, f, hf, hg0, hf0⟩ := hN (y b₀)
  obtain ⟨ug, hug⟩ := exists_fun_chart (σ := σ) T hg i
  obtain ⟨uf, huf⟩ := exists_fun_chart (σ := σ) T hf i
  let x : (Fin m → ℂ) → Frame (V.X k₀).Ψ r := fun b => ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt (V.X k₀) x₀.1 (z b)
  have hx₀ : x b₀ = x₀.1 := by
    simp only [x, hz₀]
    exact ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.cpt_zero _ _
  have hn := hB₁.mem_nhds hb₁
  have hxd : DifferentiableOn ℂ x B₁ := (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.diff_cpt _ _).comp_differentiableOn hz
  have hsec : ∀ {la Q}, (V.X k₀).IsSec la Q → DifferentiableAt ℂ (fun b => Q (x b)) b₀ := fun hQ =>
    (hQ.1.comp hxd fun b hb => (hl b hb).1).differentiableAt hn
  have hfun : ∀ u : Γ(T.X.YY, flagOpen T.X ⊓ T.X.F.U i), DifferentiableAt ℂ (fun b => ev _ σ _ u (s b)) b₀ := fun u =>
    (hd _ u).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)
  have d₁ := hsec hP
  have d₂ := hsec (hU.2.2.2.2.1 a' n' hD' g hg k₀)
  have d₃ := hsec (hU.2.2.2.2.1 _ _ (dom_add hD hD') f hf k₀)
  have n₃ : rdU V f k₀ (x b₀) ≠ 0 := by
    rw [hx₀, rdU_eq, evR_frBor hf (g2 _ _ _ ht₀)]
    exact mul_ne_zero (chr_ne_zero _ _) hf0
  have n₂ : ev _ σ _ ug (s b₀) ≠ 0 := by
    rw [← hug _ _ _ (hsub b₀ hb₀').1 (hQ b₀ hb₀')]
    exact hg0
  have hq : DifferentiableAt ℂ (fun b => P (x b) * rdU V g k₀ (x b) * ev _ σ _ uf (s b) *
      (rdU V f k₀ (x b) * ev _ σ _ ug (s b))⁻¹) b₀ :=
    ((d₁.mul d₂).mul (hfun uf)).mul ((d₃.mul (hfun ug)).inv (mul_ne_zero n₃ n₂))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hn, (d₃.mul (hfun ug)).continuousAt.eventually_ne (mul_ne_zero n₃ n₂)] with b hb hne
  obtain ⟨hc, t, ht⟩ := hl b hb
  have hb' := hs₁ hb
  have ht' := g2 _ _ _ ht
  have e₁ : P (x b) = chr (fun i => (ex D a n i : ℤ)) t⁻¹ * h i (s b) :=
    hR (x b) hc i (s b) (hsub b hb').2 (y b) t⁻¹
      (GlobalTheory.FlagMod.FlagCover.eq_ptY ((hQ b hb').lies.frBor ht')).symm (hQ b hb') ht'
  have e₂ : rdU V g k₀ (x b) = _ := (rdU_eq V g k₀ ⟨_, hc⟩).trans (evR_frBor hg ht')
  have e₃ : rdU V f k₀ (x b) = _ := (rdU_eq V f k₀ ⟨_, hc⟩).trans (evR_frBor hf ht')
  rw [hug _ _ _ (hsub b hb').1 (hQ b hb')] at e₂
  rw [huf _ _ _ (hsub b hb').1 (hQ b hb'), ex_add_int, chr_add] at e₃
  replace hne : rdU V f k₀ (x b) * ev _ σ _ ug (s b) ≠ 0 := hne
  refine (eq_mul_inv_iff_mul_eq₀ hne).2 ?_
  rw [e₁, e₂, e₃]
  ring

end DifferentiableLines
