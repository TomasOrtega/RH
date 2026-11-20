import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HodgeInteriorGram

/- English proof (translation)
Unfold `IsDerivAt0`. Simplify using `only [map_zero]`. Use `and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)` and prove the remaining obligations. Rewrite using `[show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv, map_zero]`. Both sides reduce to the same expression.
-/
theorem isDerivAt0_comp_equiv {g g' : ℕ} {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (y : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

/- English proof (translation)
Establish `hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m`. Introduce `K hK`. Take `⟨N, hN⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (h K hK)`. Establish `hkC : (K : ℂ) ≠ 0` using `by exact_mod_cast hK.ne'`.

Establish `e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ)`. Use `push_cast`. Take the linear combination `(norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨N, by exact_mod_cast e⟩`. Establish `hz : n - m = 0`. Use `Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_` and prove the remaining obligations. Rewrite using `[Int.abs_eq_natAbs]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem int_eq_of_exp_eq (m n : ℤ) (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m := by
    intro K hK
    obtain ⟨N, hN⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hK)
    have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ) := by
      push_cast
      linear_combination (norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN
      field_simp
      ring
    exact ⟨N, by exact_mod_cast e⟩
  have hz : n - m = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  omega

/- English proof (translation)
Establish `: Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.mulVec_transpose]`. Both sides reduce to the same expression. Rewrite using `[hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ)
    (z w : Fin g → ℂ) : hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end GlobalTheory.HodgeInteriorGram

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs`. Establish `hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀`. Rewrite using `[← hkx]`. Conclude with `⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩`. Establish `hg : ∀ τ, (hodgeMet Z U).gram x f τ = ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ)` using `fun τ => dif_pos hexf`.

Take `⟨k'', x'', hx'', hkx'', hv⟩` from `GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec`. Establish `hk : k'' = k`. Apply `hinj` to reduce the goal to its premises. Establish `e` using `x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))`. Conclude with `W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x') ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))`.

Substitute `hk` using the available equality. Establish `hu : W.F.u (W.ik k'') (W.Pm k'' x'') = (GlobalTheory.AllWt.ptF (S` using `CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := (W.lie k'' x'').1.symm.trans (ptF_fst _).symm`. Establish `hp : (GlobalTheory.AllWt.ptF (S` using `CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by`. Rewrite using `[← hkx'']`. Conclude with `(Category.assoc _ _ _).symm`.

Establish `hper` using `W.period k'' x''`. Establish `he'` using `isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper`. Establish `hhol'` using `pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper`. Establish `hker` using `pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper`. Establish `hcw` using `pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper`.

Take `⟨L, hL⟩` from `exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'`. Use `set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA`. Establish `hAv : ∀ z, A *ᵥ z = L z` using `fun z => LinearMap.toMatrix'_mulVec _ z`. Use `set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'`. Establish `hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w)` using `fun z w => by`.

Rewrite using `[hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]`. Establish `hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b`. Introduce `a b`. Rewrite using `[hpull]`. Establish `h1 : exx (L (W.Pm k'' x'' a)) = 1` using `by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩`.

Establish `h2 : exx (L (W.Pm k'' x'' b)) = 1` using `by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩`. Take `⟨m, hm⟩` from `hint _ _ h1 h2`. Rewrite using `[hm]`. Use `congr 1`. Use `GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_` and prove the remaining obligations.

Establish `w1` using `hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2 (by rw [hm, Complex.ofReal_intCast]; rfl)`. Establish `w2` using `hcw K a b (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl`. Rewrite `w2` using `[hL, hL, L.map_smul, L.map_smul]`. Conclude with `congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))`. Use `set Lc := L.toContinuousLinearEquiv with hLc`.

Establish `hLc' : ∀ z, Lc z = L z` using `fun z => rfl`. Use `choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) => GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b`. Establish `hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left) (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ)`. Introduce `τ b`. Use `isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_` and prove the remaining obligations.

Rewrite using `[hwm τ b]`. Establish `e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) = fun z => (exx (Lc z)).left` using `funext fun z => by`. Rewrite using `[hLc', ← hL]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Use `(GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_` and prove the remaining obligations. Rewrite using `[Lc.apply_symm_apply]`. Conclude with `hdirs ⟨τ, b⟩`. Establish `hmat` using `fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ' (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ) (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) …`. Use `⟨fun τ => ?_, fun p q hpq => ?_⟩` and prove the remaining obligations.

Take `⟨h1, -⟩` from `hmat τ τ`. Rewrite using `[hg τ]`. Establish `e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) = of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩))`. Use extensionality with `b b'`. Simplify using `only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]`.

Rewrite using `[e2, h1]`. Break down `Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0` into its components or cases. Use extensionality with `b`. Conclude with `absurd b.2 (by omega)`. Establish `hdp` using `hdpos k'' x'' hx'' τ h0`.

Rewrite using `[smul_smul, ← Complex.ofReal_mul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Establish `h2` using `(hmat q.1 p.1).2 hpq q.2 p.2`. Rewrite `h2` using `[hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply]`.

Conclude with `h2`.
-/
theorem GlobalTheory.HodgeInteriorGram.gram_eq_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs
  have hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀ := by
    rw [← hkx]; exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩
  have hg : ∀ τ, (hodgeMet Z U).gram x f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ) := fun τ => dif_pos hexf
  obtain ⟨k'', x'', hx'', hkx'', hv⟩ := GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec
  have hk : k'' = k := by
    apply hinj
    have e := x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))
    exact W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x')
      ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))
  subst hk
  have hu : W.F.u (W.ik k'') (W.Pm k'' x'') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k'' x'').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by
    rw [← hkx'']
    exact (Category.assoc _ _ _).symm
  have hper := W.period k'' x''
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k'' x'' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k'' x'' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left)
      (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs ⟨τ, b⟩
  have hmat := fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ'
    (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ)
    (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) (hder τ') (hwc τ) (hwc τ')
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · obtain ⟨h1, -⟩ := hmat τ τ
    rw [hg τ]
    have e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) =
        of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩)) := by
      ext b b'
      simp only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]
    rw [e2, h1]
    rcases Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0
    · ext b
      exact absurd b.2 (by omega)
    · have hdp := hdpos k'' x'' hx'' τ h0
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
  · have h2 := (hmat q.1 p.1).2 hpq q.2 p.2
    rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
    exact h2
