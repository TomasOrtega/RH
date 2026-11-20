import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsPointOfVal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CompanionTheory.SmallFin

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `hd i`. Consider the case `zero => show d ≤ v 0`.

Rewrite using `[hv.zero]`. Conclude with `le_top`. Consider the case `add x y _ _ hx hy => exact (le_min hx hy).trans (hv.add _ _)`. Consider the case `smul a x _ hx`. Establish `h1 : ((a • x : C) : R) = (a : K) • (x : R)` using `(algebraMap_smul K a (x : R)).symm`.

Rewrite using `[h1]`. Distinguish the cases in `ha : (a : K) = 0`. Rewrite using `[ha, zero_smul, hv.zero]`. Conclude with `le_top`. Rewrite using `[hv.smul _ _ ha]`.

Establish `h2 : (0 : EReal) ≤ (((vAdd la (a : K) : ℤ) : ℝ) : EReal)`. Conclude with `vAdd_int_nonneg la ha` after adjusting the coercions. Conclude with `hx.trans (le_add_of_nonneg_left h2)`.
-/
theorem le_of_mem_span {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v) {C : Submodule K R}
    {n : ℕ} (w : Fin n → C) {d : EReal} (hd : ∀ i, d ≤ v (w i : R)) {x : C}
    (hx : x ∈ Submodule.span (𝓞 K) (Set.range w)) : d ≤ v (x : R) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hd i
  | zero =>
    show d ≤ v 0
    rw [hv.zero]
    exact le_top
  | add x y _ _ hx hy => exact (le_min hx hy).trans (hv.add _ _)
  | smul a x _ hx =>
    have h1 : ((a • x : C) : R) = (a : K) • (x : R) := (algebraMap_smul K a (x : R)).symm
    rw [h1]
    by_cases ha : (a : K) = 0
    · rw [ha, zero_smul, hv.zero]
      exact le_top
    · rw [hv.smul _ _ ha]
      have h2 : (0 : EReal) ≤ (((vAdd la (a : K) : ℤ) : ℝ) : EReal) := by
        exact_mod_cast vAdd_int_nonneg la ha
      exact hx.trans (le_add_of_nonneg_left h2)

/- English proof (translation)
Use `set F := IntermediateField.adjoin K (Set.range fun i => ev (w i) / ev (w i₀)) with hF`. Establish `key : ∀ v, ev v / ev (w i₀) ∈ F` using `fun v => by`. Establish `hv : v ∈ Submodule.span K (Set.range w)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, add_div]`.

Conclude with `F.add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul, Algebra.smul_def, mul_div_assoc]`. Conclude with `F.mul_mem (F.algebraMap_mem a) hx`. Rewrite using `[eq_top_iff, ← hB, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_le_iff]`.

Introduce and unpack `_ ⟨v, v', rfl⟩`. Distinguish the cases in `h : ev v' = 0`. Rewrite using `[h, div_zero]`. Conclude with `F.zero_mem`. Establish `: ev v / ev v' = (ev v / ev (w i₀)) / (ev v' / ev (w i₀))` using `by field_simp`.

Rewrite using `[this]`. Conclude with `F.div_mem (key v) (key v')`.
-/
theorem adjoin_ratios {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω)
    (hB : GlobalTheory.DegVal.ratioField ev = ⊤) {n : ℕ} (w : Fin n → V) (hs : Submodule.span K (Set.range w) = ⊤) (i₀ : Fin n)
    (h0 : ev (w i₀) ≠ 0) : IntermediateField.adjoin K (Set.range fun i => ev (w i) / ev (w i₀)) = ⊤ := by
  set F := IntermediateField.adjoin K (Set.range fun i => ev (w i) / ev (w i₀)) with hF
  have key : ∀ v, ev v / ev (w i₀) ∈ F := fun v => by
    have hv : v ∈ Submodule.span K (Set.range w) := hs ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, add_div]
      exact F.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def, mul_div_assoc]
      exact F.mul_mem (F.algebraMap_mem a) hx
  rw [eq_top_iff, ← hB, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨v, v', rfl⟩
  by_cases h : ev v' = 0
  · rw [h, div_zero]
    exact F.zero_mem
  · have : ev v / ev v' = (ev v / ev (w i₀)) / (ev v' / ev (w i₀)) := by field_simp
    rw [this]
    exact F.div_mem (key v) (key v')

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [vV]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vV_pow {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
    [IsFractionRing V K'] {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = (n : ℤ) * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih =>
    rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

/- English proof (translation)
Distinguish the cases in `h : y = 0`. Rewrite using `[h, zero_mul, nval_zero]`. Conclude with `le_top`. Rewrite using `[nval_of_ne hx, nval_of_ne (mul_ne_zero h hx), vV_mul h hx]`. Use `EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e))` and prove the remaining obligations.

Establish `: vV V x ≤ vV V y + vV V x` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem nval_le_of_mul {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
    [IsFractionRing V K'] (e : ℕ) {x y : K'} (hx : x ≠ 0) (hy : 0 ≤ vV V y) : nval V e x ≤ nval V e (y * x) := by
  by_cases h : y = 0
  · rw [h, zero_mul, nval_zero]
    exact le_top
  · rw [nval_of_ne hx, nval_of_ne (mul_ne_zero h hx), vV_mul h hx]
    refine EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e))
    have : vV V x ≤ vV V y + vV V x := by omega
    exact_mod_cast this

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨⟨-, -, -, -, hA, hBC⟩, -⟩` from `GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c`. Establish `hE : IntFrExt Xo c`. Break down `Nat.eq_zero_or_pos (Dw.p + Dw.q) with h | h` into its components or cases. Conclude with `GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero E H Dw l Xo c h`. Conclude with `GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c h`.

Establish `hB : FrBaseChg Xo c` using `fun S S' _ _ _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S S' φ y`. Conclude with `intAll_of_allTest hE hB hA`.
-/
theorem intAll_all (Xo : Moduli Dw l) (c : Coeff l) : Formalism.L2.PjFree.IntAll Xo c := by
  obtain ⟨⟨-, -, -, -, hA, hBC⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hE : IntFrExt Xo c := by
    rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h | h
    · exact GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero E H Dw l Xo c h
    · exact GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c h
  have hB : FrBaseChg Xo c := fun S S' _ _ _ _ φ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S S' φ y
  exact intAll_of_allTest hE hB hA

/- English proof (translation)
Take `⟨⟨-, hC, -, -, -, -⟩, -⟩` from `GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c`. Establish `hWD` using `evalWD_fr hC`. Establish `hft : FromTest (K` using `c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, χ, u, hz⟩`. Unfold `evR evalAt`. Rewrite using `[dif_pos hft]`.

Conclude with `hWD g hg L _ p _ χ _ u z hft.choose_spec.choose_spec.choose_spec hz`.
-/
theorem evR_test {g : Rul Xo c}
    (hg : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g) {L : Type} [CommRing L]
    [Algebra c.F L] (p : TRing c.F) (χ : p.R →ₐ[c.F] L) (u : FrPt Xo c p.R) (z : FrPt Xo c L) (hz : FrMap χ u z) :
    evR Xo c g z = χ (g p u) := by
  obtain ⟨⟨-, hC, -, -, -, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hWD := evalWD_fr hC
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, χ, u, hz⟩
  unfold evR evalAt
  rw [dif_pos hft]
  exact hWD g hg L _ p _ χ _ u z hft.choose_spec.choose_spec.choose_spec hz

/- English proof (translation)
Take `⟨⟨-, -, hB, -, hA, -⟩, -⟩` from `GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c`. Rewrite using `[← evR_test hg.1 p χ u z hz]`. Conclude with `GlobalTheory.CompanionTheory.Ar.Rec.FinRd.evalAt_bor_zpow hB e hg.1 hg.2 L t z w (hA L z) (hA L w) hb`.
-/
theorem evR_bor {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) {L : Type} [Field L] [Algebra c.F L]
    (p : TRing c.F) (χ : p.R →ₐ[c.F] L) (u : FrPt Xo c p.R) (z w : FrPt Xo c L) (hz : FrMap χ u z)
    (t : Ix Dw → Lˣ) (hb : FrBor t z w) :
    evR Xo c g w = ((∏ i, t i ^ e i : Lˣ) : L) * χ (g p u) := by
  obtain ⟨⟨-, -, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  rw [← evR_test hg.1 p χ u z hz]
  exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.evalAt_bor_zpow hB e hg.1 hg.2 L t z w (hA L z) (hA L w) hb

/- English proof (translation)
Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: exZ Dw (n • G) i = exZ Dw G i * n`. Apply the tactic sequence `cases i <;> simp [exZ, mul_comm]`. Rewrite using `[this, zpow_mul, zpow_natCast]`.
-/
theorem prod_exZ_nsmul {M : Type} [CommGroup M] (t : Ix Dw → M) (G : WTZ E) (n : ℕ) :
    ∏ i, t i ^ exZ Dw (n • G) i = (∏ i, t i ^ exZ Dw G i) ^ n := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : exZ Dw (n • G) i = exZ Dw G i * n := by
    cases i <;> simp [exZ, mul_comm]
  rw [this, zpow_mul, zpow_natCast]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hGF, hGT⟩` from `GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c`. Take `⟨n, w, hw⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hFG`. Establish `hspan : Submodule.span c.F (Set.range w) = ⊤`.

Rewrite using `[← hsp, ← hw, Submodule.span_span_of_tower]`. Set `a : Fin n → Om Z` to `fun i => genVal Z (w i : Rul Xo c)`. Establish `hex : ∃ i, a i ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hB.1 (LinearMap.ext_on_range hspan fun i => hall i)`. Take `⟨i₁, hi₁⟩` from `hex`. Establish `: Nonempty (Fin n)` using `⟨i₁⟩`. Take `⟨i₀, hi₀⟩` from `Finite.exists_max fun i => ν (a i)`. Establish `ha0 : a i₀ ≠ 0` using `fun h => by`.

Establish `h3` using `hi₀ i₁`. Simplify using `only [h, map_zero] at h3`. Conclude with `hi₁ ((Valuation.zero_iff ν).1 (le_antisymm h3 zero_le'))`. Establish `hwlat : ∀ i, w i ∈ latOn U Z G` using `fun i => hw ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hlt : ν (a i₀) ^ τ < ν (genVal Z (f : Rul Xo c))` using `hcon (w i₀) (hwlat i₀)`.

Use `set b := genVal Z (f : Rul Xo c) with hbdef`. Establish `hb0 : b ≠ 0` using `fun h => by`. Rewrite `hlt` using `[h, map_zero]`. Conclude with `not_lt_zero' hlt`. Establish `hνa : 0 < ν (a i₀)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 ha0)`.

Establish `hνb : 0 < ν b` using `zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 hb0)`. Set `y : Fin n → Om Z` to `fun i => a i / a i₀`. Set `q : Om Z` to `a i₀ ^ τ / b`. Establish `hy : ∀ i, ν (y i) ≤ 1` using `fun i => by`. Simplify using `only [y, map_div₀]`.

Conclude with `div_le_one_of_le₀ (hi₀ i) hνa.le`. Establish `hq : ν q < 1`. Simplify using `only [q, map_div₀, map_pow]`. Conclude with `(div_lt_one hνb).2 hlt`. Set `Gn : Finset (Om Z)` to `Finset.univ.image y ∪ {q}`.

Establish `hGn : ∀ g ∈ Gn, ν g ≤ 1` using `fun g hg => by`. Break down `Finset.mem_union.1 hg with h | h` into its components or cases. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`. Conclude with `hy i`. Rewrite using `[Finset.mem_singleton.1 h]`.

Conclude with `hq.le`. Establish `hgen : IntermediateField.adjoin c.F (Gn : Set (Om Z)) = ⊤`. Rewrite using `[eq_top_iff, ← adjoin_ratios (genPoint Z (cuspOn U Z G)) hB.2 w hspan i₀ ha0]`. Use `IntermediateField.adjoin.mono _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))`. Take `⟨p, χ, u₀, hu⟩` from `hGT hGF Z`. Set `Wf : Finset (Om Z)` to `Finset.univ.image fun i : Fin p.n => χ (Ideal.Quotient.mk p.I (MvPolynomial.X i))`. Set `N : Finset (Om Z)` to `{a i₀, b}`. Establish `hN : ∀ x ∈ N, x ≠ 0` using `fun x hx => by`.

Break down `Finset.mem_insert.1 hx with h | h` into its components or cases. Conclude with `h ▸ ha0`. Rewrite using `[Finset.mem_singleton.1 h]`. Conclude with `hb0`. Take `⟨T, io, e, ho, hfin, S, ρ, hρK, hSG, hSW, hSN, hρN, hρG, hρL⟩` from `exists_cdvr_point la ν h1 h2 Gn Wf N hGn hgen hN`.

Establish `hχS : ∀ x : p.R, χ x ∈ S` using `fun x => by`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: χ (Ideal.Quotient.mk p.I (MvPolynomial.C a)) = algebraMap c.F (Om Z) a` using `χ.commutes a`.

Rewrite using `[this]`. Conclude with `S.algebraMap_mem a`. Consider the case `add P Q hP hQ`. Rewrite using `[map_add, map_add]`. Conclude with `S.add_mem hP hQ`.

Consider the case `mul_X P i hP`. Rewrite using `[map_mul, map_mul]`. Conclude with `S.mul_mem hP (hSW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Use `letI := io.toAlgebra`. Set `ψ : p.R →ₐ[c.F] T.Fr` to `{ (ρ.comp (χ.codRestrict S hχS).toRingHom) with commutes' := fun x => by`.

Establish `h3 : (χ.codRestrict S hχS) (algebraMap c.F p.R x) = algebraMap c.F S x` using `Subtype.ext (χ.commutes x)`. Use `show ρ ((χ.codRestrict S hχS) (algebraMap c.F p.R x)) = io x`. Rewrite using `[h3, hρK] }`. Establish `hψ : ∀ x, ψ x = ρ ⟨χ x, hχS x⟩` using `fun _ => rfl`. Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p.R T.Fr ψ u₀`.

Take `⟨T', io', r', y', hr, ho', hf', φ, z', t', h1', h2', hz', hb'⟩` from `GlobalTheory.IntegralFrameCheck.intAll_ramified (intAll_all Xo c) la T io e ho hfin z`. Use `letI := io'.toAlgebra`. Establish `hz2 : FrMap (φ.comp ψ) u₀ z'` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hz hz'`. Establish `hform : ∀ {G' : WTZ E} {g : Rul Xo c}, g ∈ secZ Xo c (exZ Dw G') → evI y' g = ((∏ i, t' i ^ exZ Dw G' i : T'.Frˣ) : T'.Fr) * φ (ψ (g p u₀))` using `fun hg => evR_bor hg p (φ.comp ψ) u₀ z' y'.1 hz2 t' hb'`. Establish `hgv : ∀ {e' : Ix Dw → ℤ} {g : Rul Xo c}, g ∈ secZ Xo c e' → genVal Z g = χ (g p u₀)` using `fun hg => (genVal_apply hGF Z _).trans (evR_test hg.1 p χ u₀ (genFr hGF Z) hu)`.

Establish `hmemG : ∀ i, (w i : Rul Xo c) ∈ secZ Xo c (exZ Dw G)` using `fun i => cuspW_le_secZ G (cuspOn_le U Z G (w i).2)`. Establish `hmemF : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G))` using `cuspW_le_secZ _ (cuspOn_le U Z _ f.2)`. Establish `ea : ∀ i, a i = χ ((w i : Rul Xo c) p u₀)` using `fun i => hgv (hmemG i)`. Establish `eb : b = χ ((f : Rul Xo c) p u₀)` using `hgv hmemF`. Set `Cu : T'.Frˣ` to `∏ i, t' i ^ exZ Dw G i`.

Set `A₀ : S` to `⟨χ ((w i₀ : Rul Xo c) p u₀), hχS _⟩`. Set `Bf : S` to `⟨χ ((f : Rul Xo c) p u₀), hχS _⟩`. Establish `hA₀ : ρ A₀ ≠ 0` using `hρN A₀ (by show χ _ ∈ N`. Rewrite using `[← ea]`. Conclude with `Finset.mem_insert_self _ _)`.

Establish `hBf : ρ Bf ≠ 0` using `hρN Bf (by show χ _ ∈ N`. Rewrite using `[← eb]`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_singleton_self _))`. Establish `hyG : ∀ i, y i ∈ Gn` using `fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i))`. Establish `hqG : q ∈ Gn` using `Finset.mem_union_right _ (Finset.mem_singleton_self _)`.

Set `Q : S` to `⟨q, hSG q hqG⟩`. Establish `hYi : ∀ i, (⟨y i, hSG _ (hyG i)⟩ : S) * A₀ = ⟨χ ((w i : Rul Xo c) p u₀), hχS _⟩` using `fun i => Subtype.ext (by show y i * χ _ = χ _`. Rewrite using `[← ea, ← ea]`. Conclude with `div_mul_cancel₀ _ ha0)`. Establish `hQ : Q * Bf = A₀ ^ τ` using `Subtype.ext (by show q * χ _ = (χ _) ^ τ`.

Rewrite using `[← ea, ← eb]`. Conclude with `div_mul_cancel₀ _ hb0)`. Establish `hb0' : φ (ρ A₀) ≠ 0` using `(map_ne_zero φ).2 hA₀`. Establish `hbf' : φ (ρ Bf) ≠ 0` using `(map_ne_zero φ).2 hBf`. Establish `hCu : (Cu : T'.Fr) ≠ 0` using `Cu.ne_zero`.

Set `v : Rul Xo c → EReal` to `fun g => nval T'.V (r' * e) (evI y' g)`. Establish `hvmem : v ∈ (recVals Xo c).1 la` using `⟨PtV.mk la ho' y' hf' () trivial, rfl⟩`. Establish `hval : IsVal la v` using `(recVals Xo c).2 la v hvmem`. Establish `hgens : ∀ i, nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (w i : Rul Xo c)` using `fun i => by show _ ≤ nval T'.V (r' * e) (evI y' (w i : Rul Xo c))`. Rewrite using `[hform (hmemG i)]`.

Establish `h3 : (Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)) = φ (ρ ⟨y i, hSG _ (hyG i)⟩) * ((Cu : T'.Fr) * φ (ρ A₀))`. Rewrite using `[hψ, ← hYi i, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)))`. Rewrite using `[h3]`.

Conclude with `nval_le_of_mul _ (mul_ne_zero hCu hb0') (by`. Rewrite using `[h1']`. Conclude with `mul_nonneg (Int.natCast_nonneg _) (hρG _ (hyG i)))`. Establish `hdep : nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ depthOn U Z G v` using `le_iInf₂ fun l hl => le_of_mem_span hval w hgens (hw ▸ hl)`. Establish `hτ0 : (0 : EReal) ≤ (τ : EReal)` using `by exact_mod_cast Nat.zero_le τ`.

Establish `h4 : (τ : EReal) * nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (f : Rul Xo c)` using `(mul_le_mul_of_nonneg_left hdep hτ0).trans (hf v hvmem)`. Establish `hvf : v (f : Rul Xo c) = nval T'.V (r' * e) ((Cu : T'.Fr) ^ τ * φ (ρ Bf))` using `by show nval T'.V (r' * e) (evI y' (f : Rul Xo c)) = _`. Rewrite using `[hform hmemF, prod_exZ_nsmul, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression. Establish `hX : (Cu : T'.Fr) * φ (ρ A₀) ≠ 0` using `mul_ne_zero hCu hb0'`.

Establish `hY : (Cu : T'.Fr) ^ τ * φ (ρ Bf) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hCu) hbf'`. Establish `hkey : ((Cu : T'.Fr) * φ (ρ A₀)) ^ τ = φ (ρ Q) * ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`. Rewrite using `[mul_pow, ← map_pow, ← map_pow, ← hQ, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : φ (ρ Q) ≠ 0` using `fun h => pow_ne_zero τ hX (by rw [hkey, h, zero_mul])`.

Establish `hρQ : ρ Q ≠ 0` using `fun h => hD0 (by rw [h, map_zero])`. Establish `hD : 0 < vV T'.V (φ (ρ Q))`. Rewrite using `[h1']`. Conclude with `mul_pos (by exact_mod_cast hr) (hρL Q hqG hq hρQ)`. Establish `hvv : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) = vV T'.V (φ (ρ Q)) + vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`.

Rewrite using `[← vV_pow hX, hkey, vV_mul hD0 hY]`. Rewrite `h4` using `[hvf, nval_of_ne hX, nval_of_ne hY, show (τ : EReal) = ((τ : ℝ) : EReal) from by simp, ← EReal.coe_mul, EReal.coe_le_coe_iff, ← mul_div_assoc]`. Establish `hE : (0 : ℝ) < ((r' * e : ℕ) : ℝ)` using `by exact_mod_cast ho'.1`. Establish `h5` using `(div_le_div_iff_of_pos_right hE).1 h4`. Establish `h6 : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) ≤ vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf))`.

Conclude with `h5` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem fin_small {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ E)
    (hFG : (latOn U Z G).FG) (hsp : Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) = ⊤)
    (hB : GlobalTheory.DegVal.BirOn U Z G) (la : HeightOneSpectrum (𝓞 c.F)) (ν : Valuation (Om Z) NNReal)
    (h1 : ∀ a : 𝓞 c.F, ν (algebraMap c.F (Om Z) (a : c.F)) ≤ 1)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap c.F (Om Z) (a : c.F)) < 1) (τ : ℕ) (f : cuspOn U Z (τ • G))
    (hf : ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) :
    ∃ l ∈ latOn U Z G, ν (genVal Z (f : Rul Xo c)) ≤ ν (genVal Z (l : Rul Xo c)) ^ τ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hGF, hGT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c
  obtain ⟨n, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hFG
  have hspan : Submodule.span c.F (Set.range w) = ⊤ := by
    rw [← hsp, ← hw, Submodule.span_span_of_tower]
  let a : Fin n → Om Z := fun i => genVal Z (w i : Rul Xo c)
  have hex : ∃ i, a i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hB.1 (LinearMap.ext_on_range hspan fun i => hall i)
  obtain ⟨i₁, hi₁⟩ := hex
  have : Nonempty (Fin n) := ⟨i₁⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ν (a i)
  have ha0 : a i₀ ≠ 0 := fun h => by
    have h3 := hi₀ i₁
    simp only [h, map_zero] at h3
    exact hi₁ ((Valuation.zero_iff ν).1 (le_antisymm h3 zero_le'))
  have hwlat : ∀ i, w i ∈ latOn U Z G := fun i => hw ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlt : ν (a i₀) ^ τ < ν (genVal Z (f : Rul Xo c)) := hcon (w i₀) (hwlat i₀)
  set b := genVal Z (f : Rul Xo c) with hbdef
  have hb0 : b ≠ 0 := fun h => by
    rw [h, map_zero] at hlt
    exact not_lt_zero' hlt
  have hνa : 0 < ν (a i₀) := zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 ha0)
  have hνb : 0 < ν b := zero_lt_iff.2 ((Valuation.ne_zero_iff ν).2 hb0)
  let y : Fin n → Om Z := fun i => a i / a i₀
  let q : Om Z := a i₀ ^ τ / b
  have hy : ∀ i, ν (y i) ≤ 1 := fun i => by
    simp only [y, map_div₀]
    exact div_le_one_of_le₀ (hi₀ i) hνa.le
  have hq : ν q < 1 := by
    simp only [q, map_div₀, map_pow]
    exact (div_lt_one hνb).2 hlt
  classical
  let Gn : Finset (Om Z) := Finset.univ.image y ∪ {q}
  have hGn : ∀ g ∈ Gn, ν g ≤ 1 := fun g hg => by
    rcases Finset.mem_union.1 hg with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hy i
    · rw [Finset.mem_singleton.1 h]
      exact hq.le
  have hgen : IntermediateField.adjoin c.F (Gn : Set (Om Z)) = ⊤ := by
    rw [eq_top_iff, ← adjoin_ratios (genPoint Z (cuspOn U Z G)) hB.2 w hspan i₀ ha0]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨i, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i)))
  obtain ⟨p, χ, u₀, hu⟩ := hGT hGF Z
  let Wf : Finset (Om Z) := Finset.univ.image fun i : Fin p.n => χ (Ideal.Quotient.mk p.I (MvPolynomial.X i))
  let N : Finset (Om Z) := {a i₀, b}
  have hN : ∀ x ∈ N, x ≠ 0 := fun x hx => by
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ ha0
    · rw [Finset.mem_singleton.1 h]
      exact hb0
  obtain ⟨T, io, e, ho, hfin, S, ρ, hρK, hSG, hSW, hSN, hρN, hρG, hρL⟩ :=
    exists_cdvr_point la ν h1 h2 Gn Wf N hGn hgen hN
  have hχS : ∀ x : p.R, χ x ∈ S := fun x => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction P using MvPolynomial.induction_on with
    | C a =>
      have : χ (Ideal.Quotient.mk p.I (MvPolynomial.C a)) = algebraMap c.F (Om Z) a := χ.commutes a
      rw [this]
      exact S.algebraMap_mem a
    | add P Q hP hQ =>
      rw [map_add, map_add]
      exact S.add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul, map_mul]
      exact S.mul_mem hP (hSW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  letI := io.toAlgebra
  let ψ : p.R →ₐ[c.F] T.Fr :=
    { (ρ.comp (χ.codRestrict S hχS).toRingHom) with
      commutes' := fun x => by
        have h3 : (χ.codRestrict S hχS) (algebraMap c.F p.R x) = algebraMap c.F S x := Subtype.ext (χ.commutes x)
        show ρ ((χ.codRestrict S hχS) (algebraMap c.F p.R x)) = io x
        rw [h3, hρK] }
  have hψ : ∀ x, ψ x = ρ ⟨χ x, hχS x⟩ := fun _ => rfl
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p.R T.Fr ψ u₀
  obtain ⟨T', io', r', y', hr, ho', hf', φ, z', t', h1', h2', hz', hb'⟩ :=
    GlobalTheory.IntegralFrameCheck.intAll_ramified (intAll_all Xo c) la T io e ho hfin z
  letI := io'.toAlgebra
  have hz2 : FrMap (φ.comp ψ) u₀ z' := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hz hz'
  have hform : ∀ {G' : WTZ E} {g : Rul Xo c}, g ∈ secZ Xo c (exZ Dw G') →
      evI y' g = ((∏ i, t' i ^ exZ Dw G' i : T'.Frˣ) : T'.Fr) * φ (ψ (g p u₀)) := fun hg =>
    evR_bor hg p (φ.comp ψ) u₀ z' y'.1 hz2 t' hb'
  have hgv : ∀ {e' : Ix Dw → ℤ} {g : Rul Xo c}, g ∈ secZ Xo c e' → genVal Z g = χ (g p u₀) := fun hg =>
    (genVal_apply hGF Z _).trans (evR_test hg.1 p χ u₀ (genFr hGF Z) hu)
  have hmemG : ∀ i, (w i : Rul Xo c) ∈ secZ Xo c (exZ Dw G) := fun i => cuspW_le_secZ G (cuspOn_le U Z G (w i).2)
  have hmemF : (f : Rul Xo c) ∈ secZ Xo c (exZ Dw (τ • G)) := cuspW_le_secZ _ (cuspOn_le U Z _ f.2)
  have ea : ∀ i, a i = χ ((w i : Rul Xo c) p u₀) := fun i => hgv (hmemG i)
  have eb : b = χ ((f : Rul Xo c) p u₀) := hgv hmemF
  let Cu : T'.Frˣ := ∏ i, t' i ^ exZ Dw G i
  let A₀ : S := ⟨χ ((w i₀ : Rul Xo c) p u₀), hχS _⟩
  let Bf : S := ⟨χ ((f : Rul Xo c) p u₀), hχS _⟩
  have hA₀ : ρ A₀ ≠ 0 := hρN A₀ (by
    show χ _ ∈ N
    rw [← ea]
    exact Finset.mem_insert_self _ _)
  have hBf : ρ Bf ≠ 0 := hρN Bf (by
    show χ _ ∈ N
    rw [← eb]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hyG : ∀ i, y i ∈ Gn := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem y (Finset.mem_univ i))
  have hqG : q ∈ Gn := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let Q : S := ⟨q, hSG q hqG⟩
  have hYi : ∀ i, (⟨y i, hSG _ (hyG i)⟩ : S) * A₀ = ⟨χ ((w i : Rul Xo c) p u₀), hχS _⟩ := fun i => Subtype.ext (by
    show y i * χ _ = χ _
    rw [← ea, ← ea]
    exact div_mul_cancel₀ _ ha0)
  have hQ : Q * Bf = A₀ ^ τ := Subtype.ext (by
    show q * χ _ = (χ _) ^ τ
    rw [← ea, ← eb]
    exact div_mul_cancel₀ _ hb0)
  have hb0' : φ (ρ A₀) ≠ 0 := (map_ne_zero φ).2 hA₀
  have hbf' : φ (ρ Bf) ≠ 0 := (map_ne_zero φ).2 hBf
  have hCu : (Cu : T'.Fr) ≠ 0 := Cu.ne_zero
  let v : Rul Xo c → EReal := fun g => nval T'.V (r' * e) (evI y' g)
  have hvmem : v ∈ (recVals Xo c).1 la := ⟨PtV.mk la ho' y' hf' () trivial, rfl⟩
  have hval : IsVal la v := (recVals Xo c).2 la v hvmem
  have hgens : ∀ i, nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (w i : Rul Xo c) := fun i => by
    show _ ≤ nval T'.V (r' * e) (evI y' (w i : Rul Xo c))
    rw [hform (hmemG i)]
    have h3 : (Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)) =
        φ (ρ ⟨y i, hSG _ (hyG i)⟩) * ((Cu : T'.Fr) * φ (ρ A₀)) := by
      rw [hψ, ← hYi i, map_mul, map_mul]
      ring
    show nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤
      nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ψ ((w i : Rul Xo c) p u₀)))
    rw [h3]
    exact nval_le_of_mul _ (mul_ne_zero hCu hb0') (by
      rw [h1']
      exact mul_nonneg (Int.natCast_nonneg _) (hρG _ (hyG i)))
  have hdep : nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ depthOn U Z G v :=
    le_iInf₂ fun l hl => le_of_mem_span hval w hgens (hw ▸ hl)
  have hτ0 : (0 : EReal) ≤ (τ : EReal) := by exact_mod_cast Nat.zero_le τ
  have h4 : (τ : EReal) * nval T'.V (r' * e) ((Cu : T'.Fr) * φ (ρ A₀)) ≤ v (f : Rul Xo c) :=
    (mul_le_mul_of_nonneg_left hdep hτ0).trans (hf v hvmem)
  have hvf : v (f : Rul Xo c) = nval T'.V (r' * e) ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    show nval T'.V (r' * e) (evI y' (f : Rul Xo c)) = _
    rw [hform hmemF, prod_exZ_nsmul, Units.val_pow_eq_pow_val]
    rfl
  have hX : (Cu : T'.Fr) * φ (ρ A₀) ≠ 0 := mul_ne_zero hCu hb0'
  have hY : (Cu : T'.Fr) ^ τ * φ (ρ Bf) ≠ 0 := mul_ne_zero (pow_ne_zero _ hCu) hbf'
  have hkey : ((Cu : T'.Fr) * φ (ρ A₀)) ^ τ = φ (ρ Q) * ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    rw [mul_pow, ← map_pow, ← map_pow, ← hQ, map_mul, map_mul]
    ring
  have hD0 : φ (ρ Q) ≠ 0 := fun h => pow_ne_zero τ hX (by rw [hkey, h, zero_mul])
  have hρQ : ρ Q ≠ 0 := fun h => hD0 (by rw [h, map_zero])
  have hD : 0 < vV T'.V (φ (ρ Q)) := by
    rw [h1']
    exact mul_pos (by exact_mod_cast hr) (hρL Q hqG hq hρQ)
  have hvv : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) =
      vV T'.V (φ (ρ Q)) + vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    rw [← vV_pow hX, hkey, vV_mul hD0 hY]
  rw [hvf, nval_of_ne hX, nval_of_ne hY, show (τ : EReal) = ((τ : ℝ) : EReal) from by simp, ← EReal.coe_mul,
    EReal.coe_le_coe_iff, ← mul_div_assoc] at h4
  have hE : (0 : ℝ) < ((r' * e : ℕ) : ℝ) := by exact_mod_cast ho'.1
  have h5 := (div_le_div_iff_of_pos_right hE).1 h4
  have h6 : (τ : ℤ) * vV T'.V ((Cu : T'.Fr) * φ (ρ A₀)) ≤ vV T'.V ((Cu : T'.Fr) ^ τ * φ (ρ Bf)) := by
    exact_mod_cast h5
  omega

end Main

/- English proof (translation)
Introduce `_ D T j Y e o _ _ Z u t hG hB _ _ la ν h1 h2 τ _ f hf`. Conclude with `fin_small Y.U Z _ hG.2.1 hG.2.2 hB la ν h1 h2 τ f fun v hv => hf.1 la v hv`.
-/
theorem small_le_pow : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (ν : Valuation (Om Z) NNReal), (∀ c : 𝓞 Y.d.c₂.F, ν (algebraMap Y.d.c₂.F (Om Z) (c : Y.d.c₂.F)) ≤ 1) → (∀ c ∈ la.asIdeal, ν (algebraMap Y.d.c₂.F (Om Z) (c : Y.d.c₂.F)) < 1) → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ∃ l ∈ latOn Y.U Z (wtOf (T.Q.Dw j) u 0), ν (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) ≤ ν (genVal Z (l : Rul Y.d.Xo₂ Y.d.c₂)) ^ τ := by
  intro _ D T j Y e o _ _ Z u t hG hB _ _ la ν h1 h2 τ _ f hf
  exact fin_small Y.U Z _ hG.2.1 hG.2.2 hB la ν h1 h2 τ f fun v hv => hf.1 la v hv

end GlobalTheory.CompanionTheory.SmallFin
