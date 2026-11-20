import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PhiTransport
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusExpEqOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

/- English proof (translation)
Use `letI := P.τ.addCommGroup`. Take `⟨Φ, hΦ⟩` from `lie_equiv P.m.cart MV Mz`. Take `⟨d, β, h, t1, t2, t3⟩` from `torus_lift e hb P Mz hL`. Establish `key : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsAbLift e b P φ u ℓ → (∀ p, p ∈ I' …`. Introduce `A iA φ g' u Hm χ ℓ hφ hAH hℓ`.

Take `⟨hin, honto⟩` from `GlobalTheory.T.hol_unif_period_matrix_right E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ`. Take `⟨H', hH1, hH2, hH3⟩` from `exists_pull_form ℓ Hm hAH.1`. Establish `hE : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, (y ⬝ᵥ Hb *ᵥ star y').im = (ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im`. Introduce `y hy y' hy'`. Take `⟨k, hk, hc⟩` from `hW y hy y' hy'`.

Rewrite using `[hk]`. Use `eq_of_forall_exp fun N hN => ?_` and prove the remaining obligations. Use `GlobalTheory.T.hol_unif_period_matrix_middle E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ y y' hN hy hy' (hc N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (k : ℂ) / N))) hN rfl)` as an intermediate fact. Rewrite `this` using `[Units.val_mk0]`. Establish `c : ((k : ℝ) : ℂ) = (k : ℂ)` using `by push_cast; rfl`.

Rewrite using `[c]`. Conclude with `this`. Establish `k1 : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0` using `fun p => by`. Rewrite using `[hI']`. Use `and_congr_right fun hp => ⟨fun h0 => ?_, fun h0 y hy => ?_⟩` and prove the remaining obligations.

Use `eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `honto q hq`. Rewrite using `[← hE p hp y hy, h0 y hy]`. Rewrite using `[hE p hp y hy, h0]`. Simplify using the standard rewrite rules.

Use `⟨k1, fun p q => ?_⟩` and prove the remaining obligations. Rewrite using `[← hH2]`. Use `congr 2`. Use `herm_unique H' Hb hH1 hH (e.per b) {y | ℓ y = 0} (fun x hx y hy => by rw [hH2, hE x hx y hy]) hH3 (fun y hy => ?_) (fun p => ?_)` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(t3 A φ g' u ℓ hφ hℓ y).1 hy`.

Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `e1 : z = ∑ a, (z a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ)`. Use extensionality with `c`. Simplify using `[Finset.sum_apply, Pi.single_apply, h2]`. Establish `e2 : ∀ a, Hb *ᵥ star (h (Pi.single a (2 * Real.pi * Complex.I))) = 0` using `fun a => by`.

Use `hrad _ ((k1 _).2 ⟨(t2 _).2 ⟨(β.coord a).toAddMonoidHom, funext fun c => ?_⟩, (t3 A φ g' u ℓ hφ hℓ _).2 ⟨_, rfl⟩⟩)` and prove the remaining obligations. Distinguish the cases in `hc : c = a`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hc, Finsupp.single_apply]`.

Rewrite using `[e1, map_sum, star_sum, Matrix.mulVec_sum]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, star_smul, Matrix.mulVec_smul, e2, smul_zero]`. Establish `hp : ℓ p ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ))` using `by rw [u.full]; trivial`. Establish `: ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)), ∃ r ∈ Submodule.span ℝ (e.per b), ℓ r = w`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `honto x hx`. Conclude with `⟨y, Submodule.subset_span hy, rfl⟩`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨r', hr', rfl⟩` from `hy`. Conclude with `⟨r + r', Submodule.add_mem _ hr hr', map_add _ _ _⟩`.

Consider the case `smul c x _ hx`. Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨c • r, Submodule.smul_mem _ _ hr, ℓ.map_smul_of_tower c r⟩`. Take `⟨r, hr, hrp⟩` from `this _ hp`. Conclude with `⟨r, hr, by show ℓ (p - r) = 0; rw [map_sub, hrp, sub_self]⟩`.

Use `⟨Φ, hΦ, fun a x => ?_, fun x x' => ?_, fun p => ?_⟩` and prove the remaining obligations. Establish `d1` using `GlobalTheory.FibreDeriv.isDerivAt0_comp (DiffL.isDerivAt0_pt e hb Mz hL (Φ x)) (t.act.act a).left`. Establish `d2` using `PerGram.isDerivAt0_comp_linMap (PerSpan.isHolTo_ex_slice e hb) (Bb a) (DiffL.isDerivAt0_pt e hb Mz hL (Bb a (Φ x)))`. Establish `e1 : (fun z => (e.ex b (Bb a z)).left) = fun z => (e.ex b z).left ≫ (t.act.act a).left`. Use function extensionality and compare the values at `fun z => by rw [hB, Over.comp_left]`.

Rewrite `d2` using `[e1]`. Use `Mz.inj (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.VerticalDeriv.isDerivAt0_unique d2 d1, hΦ, hΦ, hact a x, Over.comp_left, Category.assoc, Category.assoc, P.m.act]`. Take `⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', hc⟩` from `hh x x'`. Take `⟨ℓ, hℓ⟩` from `GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP`.

Establish `e1 : a' = ℓ (Φ x)` using `DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _ v' a' (hΦ x).symm hv' ha'`. Establish `e2 : b' = ℓ (Φ x')` using `DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _ w' b' (hΦ x').symm hw' hb'`. Rewrite using `[hc, e1, e2, ← (key A φ g' u Hm χ ℓ hφ hAH hℓ).2]`. Take `⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, -⟩` from `hh 0 0`. Take `⟨ℓ, hℓ⟩` from `GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP`.

Take `⟨MT, hMT, hI⟩` from `hI`. Establish `k2 : ∀ x (δ : P.τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i ↔ Φ x = h fun a => (δ (β a) : ℂ)` using `fun x δ => by`. Establish `a1` using `t1 MT hMT ((Int.castAddHom ℂ).comp δ)`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `Mz.inj (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[hΦ, hx]`. Conclude with `a1.symm`. Introduce `hx`. Use `Over.OverMorphism.ext (P.m.cart.1.hom_ext ?_ ?_)` and prove the remaining obligations.

Rewrite using `[← hΦ, hx]`. Conclude with `a1`. Rewrite using `[Over.w (MV.pt x), Over.w (MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i)]`. Establish `k3 : ∀ δ : P.τ.X →+ ℤ, h (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = (2 * Real.pi * Complex.I : ℂ) • h fun a => (δ (β a) : ℂ)` using `fun δ => by`. Rewrite using `[← map_smul]`.

Both sides reduce to the same expression. Rewrite using `[(key A φ g' u Hm χ ℓ hφ hAH hℓ).1, t3 A φ g' u ℓ hφ hℓ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, z, rfl⟩`. Take `⟨δ, rfl⟩` from `(t2 z).1 hp`.

Use `⟨Φ.symm (h fun a => (δ (β a) : ℂ)), (hI _).2 ⟨δ, (k2 _ δ).2 (Φ.apply_symm_apply _)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Φ.apply_symm_apply, k3]`. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨δ, hδ⟩` from `(hI x).1 hx`. Rewrite using `[(k2 x δ).1 hδ, ← k3]`.

Conclude with `⟨(t2 _).2 ⟨δ, rfl⟩, _, rfl⟩`.
-/
theorem centre_ident (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (hP : IsPrincipal P.tB) (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, M.Lifts (ψ b) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1)))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρ)
    (hI : P.IsCochars MV I)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ c x, e.ex b (Bb c x) = e.ex b x ≫ t.act.act c)
    (Hb : Matrix (Fin g) (Fin g) ℂ) (hH : Hb.IsHermitian)
    (hW : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, ∃ k : ℤ, (y ⬝ᵥ Hb *ᵥ star y').im = k ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) →
      CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ))
    (I' : Set (Fin g → ℂ)) (hI' : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ∀ y ∈ e.per b, (p ⬝ᵥ Hb *ᵥ star y).im = 0)
    (hrad : ∀ p ∈ I', Hb *ᵥ star p = 0) :
    ∃ Φ : V ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ P.m.φ) ∧
      (∀ a x, Bb a (Φ x) = Φ (ρ a x)) ∧ (∀ x x', hf x x' = Real.pi * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) ∧
      ∀ p, p ∈ I' ↔ ∃ x ∈ I, p = (2 * Real.pi * Complex.I : ℂ) • Φ x := by
  letI := P.τ.addCommGroup
  obtain ⟨Φ, hΦ⟩ := lie_equiv P.m.cart MV Mz
  obtain ⟨d, β, h, t1, t2, t3⟩ := torus_lift e hb P Mz hL
  have key : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
      (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsAbLift e b P φ u ℓ →
      (∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0) ∧ ∀ p q, ℓ p ⬝ᵥ Hm *ᵥ star (ℓ q) = p ⬝ᵥ Hb *ᵥ star q := by
    intro A iA φ g' u Hm χ ℓ hφ hAH hℓ
    obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
    obtain ⟨H', hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
    have hE : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, (y ⬝ᵥ Hb *ᵥ star y').im = (ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im := by
      intro y hy y' hy'
      obtain ⟨k, hk, hc⟩ := hW y hy y' hy'
      rw [hk]
      refine eq_of_forall_exp fun N hN => ?_
      have := GlobalTheory.T.hol_unif_period_matrix_middle E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ y y' hN hy hy'
        (hc N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (k : ℂ) / N))) hN rfl)
      rw [Units.val_mk0] at this
      have c : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
      rw [c]
      exact this
    have k1 : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0 := fun p => by
      rw [hI']
      refine and_congr_right fun hp => ⟨fun h0 => ?_, fun h0 y hy => ?_⟩
      · refine eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_
        obtain ⟨y, hy, rfl⟩ := honto q hq
        rw [← hE p hp y hy, h0 y hy]
      · rw [hE p hp y hy, h0]
        simp
    refine ⟨k1, fun p q => ?_⟩
    rw [← hH2]
    congr 2
    refine herm_unique H' Hb hH1 hH (e.per b) {y | ℓ y = 0} (fun x hx y hy => by rw [hH2, hE x hx y hy]) hH3
      (fun y hy => ?_) (fun p => ?_)
    · obtain ⟨z, rfl⟩ := (t3 A φ g' u ℓ hφ hℓ y).1 hy
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have e1 : z = ∑ a, (z a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
        ext c
        simp [Finset.sum_apply, Pi.single_apply, h2]
      have e2 : ∀ a, Hb *ᵥ star (h (Pi.single a (2 * Real.pi * Complex.I))) = 0 := fun a => by
        refine hrad _ ((k1 _).2 ⟨(t2 _).2 ⟨(β.coord a).toAddMonoidHom, funext fun c => ?_⟩,
          (t3 A φ g' u ℓ hφ hℓ _).2 ⟨_, rfl⟩⟩)
        by_cases hc : c = a
        · subst hc; simp
        · simp [hc, Finsupp.single_apply]
      rw [e1, map_sum, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul, star_smul, Matrix.mulVec_smul, e2, smul_zero]
    · have hp : ℓ p ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)) := by rw [u.full]; trivial
      have : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)), ∃ r ∈ Submodule.span ℝ (e.per b), ℓ r = w := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, hy, rfl⟩ := honto x hx
          exact ⟨y, Submodule.subset_span hy, rfl⟩
        | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
        | add x y _ _ hx hy =>
          obtain ⟨r, hr, rfl⟩ := hx
          obtain ⟨r', hr', rfl⟩ := hy
          exact ⟨r + r', Submodule.add_mem _ hr hr', map_add _ _ _⟩
        | smul c x _ hx =>
          obtain ⟨r, hr, rfl⟩ := hx
          exact ⟨c • r, Submodule.smul_mem _ _ hr, ℓ.map_smul_of_tower c r⟩
      obtain ⟨r, hr, hrp⟩ := this _ hp
      exact ⟨r, hr, by show ℓ (p - r) = 0; rw [map_sub, hrp, sub_self]⟩
  refine ⟨Φ, hΦ, fun a x => ?_, fun x x' => ?_, fun p => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (DiffL.isDerivAt0_pt e hb Mz hL (Φ x)) (t.act.act a).left
    have d2 := PerGram.isDerivAt0_comp_linMap (PerSpan.isHolTo_ex_slice e hb) (Bb a)
      (DiffL.isDerivAt0_pt e hb Mz hL (Bb a (Φ x)))
    have e1 : (fun z => (e.ex b (Bb a z)).left) = fun z => (e.ex b z).left ≫ (t.act.act a).left :=
      funext fun z => by rw [hB, Over.comp_left]
    rw [e1] at d2
    refine Mz.inj (Over.OverMorphism.ext ?_)
    rw [GlobalTheory.VerticalDeriv.isDerivAt0_unique d2 d1, hΦ, hΦ, hact a x, Over.comp_left, Category.assoc, Category.assoc,
      P.m.act]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', hc⟩ := hh x x'
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    have e1 : a' = ℓ (Φ x) := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      v' a' (hΦ x).symm hv' ha'
    have e2 : b' = ℓ (Φ x') := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      w' b' (hΦ x').symm hw' hb'
    rw [hc, e1, e2, ← (key A φ g' u Hm χ ℓ hφ hAH hℓ).2]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, -⟩ := hh 0 0
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    obtain ⟨MT, hMT, hI⟩ := hI
    have k2 : ∀ x (δ : P.τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i ↔
        Φ x = h fun a => (δ (β a) : ℂ) := fun x δ => by
      have a1 := t1 MT hMT ((Int.castAddHom ℂ).comp δ)
      constructor
      · intro hx
        refine Mz.inj (Over.OverMorphism.ext ?_)
        rw [hΦ, hx]
        exact a1.symm
      · intro hx
        refine Over.OverMorphism.ext (P.m.cart.1.hom_ext ?_ ?_)
        · rw [← hΦ, hx]
          exact a1
        · rw [Over.w (MV.pt x), Over.w (MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i)]
    have k3 : ∀ δ : P.τ.X →+ ℤ, h (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) • h fun a => (δ (β a) : ℂ) := fun δ => by
      rw [← map_smul]
      rfl
    rw [(key A φ g' u Hm χ ℓ hφ hAH hℓ).1, t3 A φ g' u ℓ hφ hℓ]
    constructor
    · rintro ⟨hp, z, rfl⟩
      obtain ⟨δ, rfl⟩ := (t2 z).1 hp
      refine ⟨Φ.symm (h fun a => (δ (β a) : ℂ)), (hI _).2 ⟨δ, (k2 _ δ).2 (Φ.apply_symm_apply _)⟩, ?_⟩
      rw [Φ.apply_symm_apply, k3]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨δ, hδ⟩ := (hI x).1 hx
      rw [(k2 x δ).1 hδ, ← k3]
      exact ⟨(t2 _).2 ⟨δ, rfl⟩, _, rfl⟩

/- English proof (translation)
Take `⟨V, N, f, L, -, -, hL, -⟩` from `e.log b₀ hb`. Establish `hB' : ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.1 ∈ B` using `(continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually_mem hB`. Establish `hc : Continuous fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, (0 : Fin g → ℂ))` using `by fun_prop`. Establish `hL0` using `(hc.tendsto (b₀, 0)).eventually hL`. Use `filter_upwards [hL, hL0, hB'] with bz h1 h2 h3 hper`.

Establish `h0 : e.ex bz.1 0 = 1`. Establish `h4` using `e.add bz.1 h3 0 0`. Rewrite `h4` using `[add_zero]`. Simplify using `using h4.symm`. Establish `hx : e.ex bz.1 bz.2 = e.ex bz.1 0`.

Rewrite using `[h0]`. Conclude with `hper`. Rewrite using `[← h1, hx]`. Conclude with `h2`.
-/
theorem per_small (e : FamExp t.G M B ψ) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) (hB : B ∈ 𝓝 b₀) :
    ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.2 ∈ e.per bz.1 → bz.2 = 0 := by
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b₀ hb
  have hB' : ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.1 ∈ B :=
    (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually_mem hB
  have hc : Continuous fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, (0 : Fin g → ℂ)) := by fun_prop
  have hL0 := (hc.tendsto (b₀, 0)).eventually hL
  filter_upwards [hL, hL0, hB'] with bz h1 h2 h3 hper
  have h0 : e.ex bz.1 0 = 1 := by
    have h4 := e.add bz.1 h3 0 0
    rw [add_zero] at h4
    simpa using h4.symm
  have hx : e.ex bz.1 bz.2 = e.ex bz.1 0 := by
    rw [h0]
    exact hper
  rw [← h1, hx]
  exact h2

end LevelTowerAlt.Val
