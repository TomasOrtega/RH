import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OmLink

noncomputable section

namespace LevelTowerAlt.Comparison₂

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (fun f => Over.Hom.left f) h`. Simplify using `only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1`. Use `epi_sp i` as an intermediate fact. Conclude with `(cancel_epi _).1 h1`.
-/
theorem lv_ext_cancel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} {k : Type} [Field k]
    (i : Ω →+* k) {x x' : Over.mk ξ ⟶ G} (h : GenWeilModel.ext i ≫ x = GenWeilModel.ext i ≫ x') : x = x' := by
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun f => Over.Hom.left f) h
  simp only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1
  have := epi_sp i
  exact (cancel_epi _).1 h1

section obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp only [pow_zero]`. Conclude with `push_one hp T`. Consider the case `succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]`.
-/
theorem lv_push_pow {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (a : T ⟶ G') (n : ℕ) :
    pushPt hp.1.w (a ^ n) = pushPt hp.1.w a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact push_one hp T
  | succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]

/- English proof (translation)
Establish `hp` using `m.cart`. Set `i : Ω →+* AlgebraicClosure Ω` to `algebraMap Ω (AlgebraicClosure Ω)`. Take `⟨a, ha, hpa⟩` from `pull_point hp i y hy`. Take `⟨T⟩` from `exists_tate o i`. Take `⟨α, rfl⟩` from `(T.onto n hn a).1 ha`.

Establish `hnr : 0 < n * r` using `Nat.mul_pos hn hr`. Take `⟨y', -, hy'a⟩` from `desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)`. Set `x : Over.mk ξ ⟶ t.G` to `Over.homMk (y'.left ≫ m.cm.F) (by`. Rewrite using `[Category.assoc, hp.1.w, ← Category.assoc, Over.w y']`. Use the proof step `simp)`.

Establish `hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hy'a]`. Simplify using `[x, pushPt, GenWeilModel.ext, ex]`. Establish `hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]`. Use `⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩` and prove the remaining obligations.

Rewrite using `[hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]`. Rewrite using `[hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]`.
-/
theorem lv_div (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) (y : Over.mk ξ ⟶ t.G) (hy : y ^ n = 1) :
    ∃ x : Over.mk ξ ⟶ t.G, x ^ (n * r) = 1 ∧ x ^ r = y := by
  classical
  have hp := m.cart
  let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨a, ha, hpa⟩ := pull_point hp i y hy
  obtain ⟨T⟩ := exists_tate o i
  obtain ⟨α, rfl⟩ := (T.onto n hn a).1 ha
  have hnr : 0 < n * r := Nat.mul_pos hn hr
  obtain ⟨y', -, hy'a⟩ := desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)
  let x : Over.mk ξ ⟶ t.G := Over.homMk (y'.left ≫ m.cm.F) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w y']
    simp)
  have hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α) := by
    apply Over.OverMorphism.ext
    rw [hy'a]
    simp [x, pushPt, GenWeilModel.ext, ex]
  have hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  refine ⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩
  · rw [hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]
  · rw [hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]

/- English proof (translation)
Take `⟨h0, W, f, h1, h2, h3⟩` from `h`. Use `⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩` and prove the remaining obligations. Establish `hp` using `m.cart`. Establish `hg' : g ^ (n * r) = 1` using `by rw [pow_mul, hg, one_pow]`. Take `⟨g₀, hg₀⟩` from `hf k i g hg'`.

Establish `hg₁ : g = GenWeilModel.ext i ≫ g₀` using `Over.OverMorphism.ext hg₀`. Establish `hg₂ : g₀ ^ n = 1` using `lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])`. Take `⟨a, ha, hpa⟩` from `pull_point hp i x hx`. Take `⟨a', ha', hpa'⟩` from `pull_point hp i g₀ hg₂`. Establish `e1 : a'.left ≫ m.φ = g.left` using `(congrArg (fun z => z.left) hpa').trans hg₀.symm`.

Establish `e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left` using `congrArg (fun z => z.left) hpa`. Establish `e3 : (a ^ r).left ≫ m.φ = xk.left`. Establish `h4` using `lv_push_pow hp a r`. Establish `h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r`. Rewrite using `[MonObj.comp_pow]`.

Conclude with `h4.trans (congrArg (· ^ r) hpa)`. Conclude with `(congrArg (fun z => z.left) h5).trans hxk.symm`. Use `h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]`. Rewrite `hc` using `[← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1]`.

Establish `hk : CharZero k` using `charZero_of_injective_ringHom i.injective`. Establish `hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤))`. Establish `h6 : IsUnit ((n * r : ℕ) : k)` using `(Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit`. Establish `h7` using `h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom`. Rewrite `h7` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `h8` using `((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc`. Rewrite using `[Nat.cast_mul]`. Conclude with `h8`. Take `⟨u, hu, he⟩` from `h3 e v hev hv`. Use `⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lv_down [CharZero Ω] (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (x : Over.mk ξ ⟶ t.G) (hx : x ^ (n * r) = 1) (q : Cpt ξ) (w : Module.Dual Ω V)
    (h : M.IsHTAt t.PP.L (n * r) x q w) : M.IsHTAt t.PP.L n (x ^ r) q w := by
  obtain ⟨h0, W, f, h1, h2, h3⟩ := h
  refine ⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩
  · have hp := m.cart
    have hg' : g ^ (n * r) = 1 := by rw [pow_mul, hg, one_pow]
    obtain ⟨g₀, hg₀⟩ := hf k i g hg'
    have hg₁ : g = GenWeilModel.ext i ≫ g₀ := Over.OverMorphism.ext hg₀
    have hg₂ : g₀ ^ n = 1 := lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])
    obtain ⟨a, ha, hpa⟩ := pull_point hp i x hx
    obtain ⟨a', ha', hpa'⟩ := pull_point hp i g₀ hg₂
    have e1 : a'.left ≫ m.φ = g.left := (congrArg (fun z => z.left) hpa').trans hg₀.symm
    have e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left := congrArg (fun z => z.left) hpa
    have e3 : (a ^ r).left ≫ m.φ = xk.left := by
      have h4 := lv_push_pow hp a r
      have h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r := by
        rw [MonObj.comp_pow]
        exact h4.trans (congrArg (· ^ r) hpa)
      exact (congrArg (fun z => z.left) h5).trans hxk.symm
    refine h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1] at hc
    have hk : CharZero k := charZero_of_injective_ringHom i.injective
    have hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤)) := by
      have h6 : IsUnit ((n * r : ℕ) : k) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit
      have h7 := h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      rwa [map_natCast] at h7
    have h8 := ((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc
    rw [Nat.cast_mul]
    exact h8
  · obtain ⟨u, hu, he⟩ := h3 e v hev hv
    refine ⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩
    rw [he]
    push_cast
    ring

end obj

/- English proof (translation)
Unfold `HT.IsCp at h`. Use `split_ifs at h with h2`. Substitute `h2 h` using the available equality. Use `⟨4, ?_, by norm_num⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Take `⟨ζ, hζ, rfl⟩` from `h`. Establish `hfact : Fact p.Prime` using `⟨hp⟩`. Establish `hmem : ζ ∈ primitiveRoots p Ω` using `(mem_primitiveRoots hp.pos).2 hζ`. Establish `hc` using `congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)`. Rewrite `hc` using `[Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod]`.

Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc`. Rewrite `hc` using `[← Finset.mul_prod_erase _ _ hmem]`. Use `⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.T.integral_element_regular X Ω ξ q hξ hq` to reduce the goal to its premises. Use `IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_` and prove the remaining obligations.

Use `IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_` and prove the remaining obligations. Conclude with `((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos`. Use `push_cast`. Rewrite using `[pow_succ, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lv_kappa {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    (hq : IsIntegrallyClosed (X.presheaf.stalk q.1)) {p : ℕ} (hp : p.Prime) {κ : Ω} (h : HT.IsCp p κ) :
    ∃ a ∈ regAt ξ q, ((p ^ 4 : ℕ) : Ω) = a * κ := by
  classical
  unfold HT.IsCp at h
  split_ifs at h with h2
  · subst h2 h
    refine ⟨4, ?_, by norm_num⟩
    simp
  · obtain ⟨ζ, hζ, rfl⟩ := h
    have hfact : Fact p.Prime := ⟨hp⟩
    have hmem : ζ ∈ primitiveRoots p Ω := (mem_primitiveRoots hp.pos).2 hζ
    have hc := congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at hc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc
    rw [← Finset.mul_prod_erase _ _ hmem] at hc
    refine ⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩
    · apply GlobalTheory.T.integral_element_regular X Ω ξ q hξ hq
      refine IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_
      refine IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_
      exact ((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos
    · push_cast
      rw [pow_succ, hc]
      ring

/- English proof (translation)
Introduce `hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq`. Establish `hp` using `𝔐.S_prime p hpS`. Use `haveI := Fact.mk hp`. Establish `: CharZero Ω` using `charZero_of_injective_ringHom 𝔐.cst.injective`. Establish `hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F))`.

Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))`. Use `infer_instance`. Take `⟨x₀, hx₀'⟩` from `GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono`.

Establish `hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j`. Rewrite using `[Category.assoc, ← hx₀']`. Conclude with `𝔐.fn_over`. Take `⟨s0, o, ⟨m⟩⟩` from `GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀`. Establish `hno` using `((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1`.

Establish `hnc` using `(GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal`. Take `⟨κ, hκ, hS⟩` from `GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree`. Establish `hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]`. Establish `hsw` using `(hS q hq).2.2.1`.

Establish `hf` using `𝔐.tors p hpS`. Unfold `HT.omP at hsw`. Rewrite `hsw`, `hf`, the goal using `[hR]`. Take `⟨a, ha, hae⟩` from `lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ`. Establish `hn : 0 < p ^ 4` using `pow_pos hp.pos _`.

Establish `hr : 0 < p ^ (𝔐.R p - 4)` using `pow_pos hp.pos _`. Generalize the expression as in `p ^ (𝔐.R p - 4) = r at *`. Generalize the expression as in `p ^ 4 = n at *`. Establish `hf' : FullTorsion 𝔐.t.G 𝔐.ξ n` using `fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])`. Establish `hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e` using `fun N hN hfN => by`.

Use `GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Take `⟨e, he⟩` from `hw n hn hf'`. Take `⟨e', he'⟩` from `hw _ (Nat.mul_pos hn hr) hf`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `w ⟨z, hz, hw⟩`. Take `⟨x, hx, rfl⟩` from `lv_div o 𝔐.t m hn hr hf z hz`. Take `⟨U, hU, w', hw'⟩` from `(GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he' _ 𝔐.M q).1`. Establish `h1` using `hw' x hx q hU`. Take `⟨u, hu, rfl⟩` from `((GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw`.

Use `add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_` and prove the remaining obligations. Establish `h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u`. Rewrite using `[← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]`. Both sides reduce to the same expression. Conclude with `h2 ▸ Submodule.smul_mem _ _ (hsw u hu)`.

Introduce and unpack `w ⟨x, hx, hw⟩`. Conclude with `Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩`.
-/
theorem levelFree : LevelFree := by
  intro hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq
  have hp := 𝔐.S_prime p hpS
  haveI := Fact.mk hp
  have : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono
  have hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']
    exact 𝔐.fn_over
  obtain ⟨s0, o, ⟨m⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀
  have hno := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have hnc := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree
  have hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4) := by
    rw [← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]
  have hsw := (hS q hq).2.2.1
  have hf := 𝔐.tors p hpS
  unfold HT.omP at hsw
  rw [hR] at hsw hf ⊢
  obtain ⟨a, ha, hae⟩ := lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ
  have hn : 0 < p ^ 4 := pow_pos hp.pos _
  have hr : 0 < p ^ (𝔐.R p - 4) := pow_pos hp.pos _
  generalize p ^ (𝔐.R p - 4) = r at *
  generalize p ^ 4 = n at *
  have hf' : FullTorsion 𝔐.t.G 𝔐.ξ n := fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])
  have hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e := fun N hN hfN => by
    have := GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN
      (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)
    rwa [Category.id_comp] at this
  obtain ⟨e, he⟩ := hw n hn hf'
  obtain ⟨e', he'⟩ := hw _ (Nat.mul_pos hn hr) hf
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro w ⟨z, hz, hw⟩
    obtain ⟨x, hx, rfl⟩ := lv_div o 𝔐.t m hn hr hf z hz
    obtain ⟨U, hU, w', hw'⟩ := (GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he'
      _ 𝔐.M q).1
    have h1 := hw' x hx q hU
    obtain ⟨u, hu, rfl⟩ := ((GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz
      (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw
    refine add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_
    have h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u := by
      rw [← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]
      rfl
    exact h2 ▸ Submodule.smul_mem _ _ (hsw u hu)
  · rintro w ⟨x, hx, hw⟩
    exact Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩

end LevelTowerAlt.Comparison₂
