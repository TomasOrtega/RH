import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HF

/- English proof (translation)
Establish `h : (((j : ZMod N).val : ℕ) : ℤ) = j % N` using `ZMod.val_intCast j`. Rewrite using `[← zpow_natCast, h, Int.emod_def, sub_eq_add_neg, zpow_add, ← mul_neg, zpow_mul, zpow_natCast, hg, one_zpow, _root_.mul_one]`.
-/
theorem pow_val_intCast {G : Type} [Group G] (g : G) (N : ℕ) [NeZero N] (hg : g ^ N = 1) (j : ℤ) :
    g ^ (j : ZMod N).val = g ^ j := by
  have h : (((j : ZMod N).val : ℕ) : ℤ) = j % N := ZMod.val_intCast j
  rw [← zpow_natCast, h, Int.emod_def, sub_eq_add_neg, zpow_add, ← mul_neg, zpow_mul, zpow_natCast, hg, one_zpow,
    _root_.mul_one]

/- English proof (translation)
Introduce `k _ i g hg`. Establish `hr : spMap i ≫ q = (spMap i ≫ ξ') ≫ f` using `by rw [hq, Category.assoc]`. Take `⟨e, he⟩` from `GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap i ≫ ξ')) (spMap i ≫ q) hr`. Establish `h1 : (e.symm g) ^ n = 1` using `by rw [← map_pow, hg, map_one]`. Take `⟨x, hx⟩` from `h k i (e.symm g) h1`.

Take `⟨e₀, he₀⟩` from `GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk ξ') q hq`. Use `⟨e₀ x, ?_⟩` and prove the remaining obligations. Establish `h2` using `he (e.symm g)`. Rewrite `h2` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[he₀, h2, hx, Category.assoc]`.
-/
theorem fullTorsion_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
    (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) {Ω : Type} [Field Ω] (ξ' : Sp Ω ⟶ X')
    (q : Sp Ω ⟶ X) (hq : q = ξ' ≫ f) (n : ℕ) (h : FullTorsion t'.G ξ' n) : FullTorsion t.G q n := by
  intro k _ i g hg
  have hr : spMap i ≫ q = (spMap i ≫ ξ') ≫ f := by rw [hq, Category.assoc]
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap i ≫ ξ')) (spMap i ≫ q) hr
  have h1 : (e.symm g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  obtain ⟨x, hx⟩ := h k i (e.symm g) h1
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk ξ') q hq
  refine ⟨e₀ x, ?_⟩
  have h2 := he (e.symm g)
  rw [MulEquiv.apply_symm_apply] at h2
  rw [he₀, h2, hx, Category.assoc]

/- English proof (translation)
Take `⟨P, hP⟩` from `GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk ξ') q hq`. Establish `hL : LBIso t'.PP.L (t.PP.L.pull m.φ)`. Take `⟨w, hw, -⟩` from `m.lin`. Conclude with `⟨w, hw⟩`. Establish `pw : ∀ x, x ^ n = 1 → P x ^ n = 1` using `fun x hx => by rw [← map_pow, hx, map_one]`.

Establish `pw' : ∀ x, x ^ n = 1 → P.symm x ^ n = 1` using `fun x hx => by rw [← map_pow, hx, map_one]`. Use `⟨fun a b => e (P a) (P b), ?_⟩` and prove the remaining obligations. Use `haveI := h.finite`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finite.of_injective (fun x : {x : Over.mk ξ' ⟶ t'.G // x ^ n = 1} => (⟨P x.1, pw _ x.2⟩ : {x : Over.mk q ⟶ t.G // x ^ n = 1})) fun x x' hxx => Subtype.ext (P.injective (congrArg Subtype.val hxx))`.

Introduce `x x' g hx hx' hg`. Simplify using `only [map_mul]`. Conclude with `h.mul_left _ _ _ (pw _ hx) (pw _ hx') (pw _ hg)`. Introduce `x g g' hx hg hg'`. Simplify using `only [map_mul]`.

Conclude with `h.mul_right _ _ _ (pw _ hx) (pw _ hg) (pw _ hg')`. Introduce `χ hχ`. Take `⟨x, hx, hxg⟩` from `h.perfect (fun g => χ (P.symm g)) fun g g' hg hg' => by`. Simplify using `only [map_mul]`. Conclude with `hχ _ _ (pw' _ hg) (pw' _ hg')`.

Use `⟨P.symm x, pw' _ hx, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h1` using `hxg (P g) (pw _ hg)`. Simplify using `using h1`. Introduce `g hg hall`. Establish `h1 : P g = 1` using `h.nondeg (P g) (pw _ hg) fun x hx => by`.

Establish `h2` using `hall (P.symm x) (pw' _ hx)`. Simplify using `using h2`. Conclude with `(map_eq_one_iff P P.injective).1 h1`. Introduce `x g hx hg k _ _ i xk gk c hxk hgk`. Establish `hr : spMap i ≫ q = (spMap i ≫ ξ') ≫ f` using `by rw [hq, Category.assoc]`.

Take `⟨Q, hQ⟩` from `GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap i ≫ ξ')) (spMap i ≫ q) hr`. Establish `key : ∀ (r : Sp k ⟶ X) (_ : r = (spMap i ≫ ξ') ≫ f) (a b : Over.mk r ⟶ t.G), a.left = xk.left ≫ m.φ → b.left = gk.left ≫ m.φ → (Out.WeilIs t'.G t'.PP.L n xk gk (unitOn c) ↔ Out.WeilIs t.G t.PP.L n a b (unitOn c))`. Introduce `r hr'`. Substitute `hr'` using the available equality. Conclude with `fun a b ha hb => GlobalTheory.weilIs_grpPullback_of_comm' _ _ _ _ f m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk (spMap i ≫ ξ')) n xk gk a b _ ha hb`.

Rewrite using `[key _ hr (Q xk) (Q gk) (hQ _) (hQ _)]`. Use `h.weil (P x) (P g) (pw _ hx) (pw _ hg) k i (Q xk) (Q gk) c ?_ ?_` and prove the remaining obligations. Rewrite using `[hQ, hP, hxk, Category.assoc]`. Rewrite using `[hQ, hP, hgk, Category.assoc]`.
-/
theorem genWeil_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
    (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) {Ω : Type} [Field Ω] (ξ' : Sp Ω ⟶ X')
    (q : Sp Ω ⟶ X) (hq : q = ξ' ≫ f) (n : ℕ) (e : (Over.mk q ⟶ t.G) → (Over.mk q ⟶ t.G) → Ωˣ)
    (h : GenWeil t.G t.PP.L q n e) : ∃ ew, GenWeil t'.G t'.PP.L ξ' n ew := by
  obtain ⟨P, hP⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk ξ') q hq
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have pw : ∀ x, x ^ n = 1 → P x ^ n = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  have pw' : ∀ x, x ^ n = 1 → P.symm x ^ n = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨fun a b => e (P a) (P b), ?_⟩
  haveI := h.finite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finite.of_injective (fun x : {x : Over.mk ξ' ⟶ t'.G // x ^ n = 1} =>
      (⟨P x.1, pw _ x.2⟩ : {x : Over.mk q ⟶ t.G // x ^ n = 1}))
      fun x x' hxx => Subtype.ext (P.injective (congrArg Subtype.val hxx))
  · intro x x' g hx hx' hg
    simp only [map_mul]
    exact h.mul_left _ _ _ (pw _ hx) (pw _ hx') (pw _ hg)
  · intro x g g' hx hg hg'
    simp only [map_mul]
    exact h.mul_right _ _ _ (pw _ hx) (pw _ hg) (pw _ hg')
  · intro χ hχ
    obtain ⟨x, hx, hxg⟩ := h.perfect (fun g => χ (P.symm g)) fun g g' hg hg' => by
      simp only [map_mul]
      exact hχ _ _ (pw' _ hg) (pw' _ hg')
    refine ⟨P.symm x, pw' _ hx, fun g hg => ?_⟩
    have h1 := hxg (P g) (pw _ hg)
    simpa using h1
  · intro g hg hall
    have h1 : P g = 1 := h.nondeg (P g) (pw _ hg) fun x hx => by
      have h2 := hall (P.symm x) (pw' _ hx)
      simpa using h2
    exact (map_eq_one_iff P P.injective).1 h1
  · intro x g hx hg k _ _ i xk gk c hxk hgk
    have hr : spMap i ≫ q = (spMap i ≫ ξ') ≫ f := by rw [hq, Category.assoc]
    obtain ⟨Q, hQ⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap i ≫ ξ')) (spMap i ≫ q) hr
    have key : ∀ (r : Sp k ⟶ X) (_ : r = (spMap i ≫ ξ') ≫ f) (a b : Over.mk r ⟶ t.G), a.left = xk.left ≫ m.φ →
        b.left = gk.left ≫ m.φ → (Out.WeilIs t'.G t'.PP.L n xk gk (unitOn c) ↔
          Out.WeilIs t.G t.PP.L n a b (unitOn c)) := by
      intro r hr'
      subst hr'
      exact fun a b ha hb => GlobalTheory.weilIs_grpPullback_of_comm' _ _ _ _ f m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL
        (Over.mk (spMap i ≫ ξ')) n xk gk a b _ ha hb
    rw [key _ hr (Q xk) (Q gk) (hQ _) (hQ _)]
    refine h.weil (P x) (P g) (pw _ hx) (pw _ hg) k i (Q xk) (Q gk) c ?_ ?_
    · rw [hQ, hP, hxk, Category.assoc]
    · rw [hQ, hP, hgk, Category.assoc]

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN0.ne'⟩`. Use `haveI : Epi (spMap iK) := WeilObj.epi_spMap_field Ω k iK`. Establish `inj : ∀ x x' : Over.mk ξ ⟶ t.G, WeilObj.extPt ξ iK ≫ x = WeilObj.extPt ξ iK ≫ x' → x = x'` using `fun x x' h => by`. Establish `h' : spMap iK ≫ x.left = spMap iK ≫ x'.left` using `congrArg CommaMorphism.left h`. Conclude with `Over.OverMorphism.ext ((cancel_epi (spMap iK)).1 h')`.

Establish `lift : ∀ a, ∃ x : Over.mk ξ ⟶ t.G, x ^ N = 1 ∧ WeilObj.extPt ξ iK ≫ x = I.ev N a`. Introduce `a`. Establish `ht : (I.ev N a) ^ N = 1` using `(I.onto N hN0 _).2 ⟨a, rfl⟩`. Take `⟨x, hx⟩` from `hFT k iK (I.ev N a) ht`. Establish `hxe : WeilObj.extPt ξ iK ≫ x = I.ev N a` using `Over.OverMorphism.ext hx.symm`.

Use `⟨x, inj _ _ ?_, hxe⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_pow, hxe, ht, MonObj.comp_one]`. Use `choose ev hevN hev using lift`. Establish `hadd : ∀ a b, ev (a + b) = ev a * ev b` using `fun a b => inj _ _ (by`. Rewrite using `[MonObj.comp_mul, hev, hev, hev, I.add])`.

Establish `hlin : ∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ t.act.act c` using `fun c a => inj _ _ (by`. Rewrite using `[← Category.assoc, hev, hev]`. Conclude with `I.lin N c a)`. Take `⟨φ, hφ1, hφ2⟩` from `GlobalTheory.T.projective_module_mod_N_basis E D.La D.fin D.proj (D.p + D.q) N D.rank hN0`. Establish `hζΩ : IsPrimitiveRoot (ζ : Ω) N` using `hζ.map_of_injective (f := Units.coeHom Ω) Units.val_injective`.

Establish `hζK : IsPrimitiveRoot (iK ζ) N` using `hζΩ.map_of_injective iK.injective`. Establish `hIK : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N` using `(I.ζ_prim N hN0).map_of_injective (f := Units.coeHom k) Units.val_injective`. Take `⟨u, -, hu⟩` from `hζK.eq_pow_of_pow_eq_one (ξ := ((I.ζ N : kˣ) : k)) hIK.pow_eq_one`. Establish `hcop : u.Coprime N`. Establish `h1 : IsPrimitiveRoot (iK ζ ^ u) N` using `by rw [hu]; exact hIK`.

Conclude with `(hζK.pow_iff_coprime hN0 u).1 h1`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : ZMod N, (u : ZMod N) * v = 1 := by`. Take `⟨w, hw⟩` from `(ZMod.isUnit_iff_coprime u N).2 hcop`. Conclude with `⟨((w⁻¹ : (ZMod N)ˣ) : ZMod N), by rw [← hw]; exact w.mul_inv⟩`. Set `e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N` to `AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun x' => (u : ZMod N) * ((D.EF (φ x) (φ x') : ℤ) : ZMod N)) fun a b => by simp only [map_add, Int.cast_add, mul_add]) fun a b => by`.

Use extensionality with `y`. Simplify using `[map_add, mul_add, LinearMap.add_apply]`. Establish `he : ∀ x x', e x x' = (u : ZMod N) * ((D.EF (φ x) (φ x') : ℤ) : ZMod N)` using `fun _ _ => rfl`. Establish `hevk : ∀ a, (I.ev N a).left = spMap iK ≫ (ev a).left` using `fun a => by rw [← hev a]; rfl`. Establish `hkill : ∀ (x : Fin (D.p + D.q) → 𝓞 E), ∀ b, ev (φ x + N • b) = ev (φ x)`.

Introduce `x b`. Use `inj _ _ ?_` and prove the remaining obligations. Rewrite using `[hev, hev, I.add, ((I.ker N hN0 (N • b)).2 ⟨b, rfl⟩), _root_.mul_one]`. Establish `hcast : ∀ x c, ∃ y, ((D.EF x c : ℤ) : ZMod N) = ((D.EF x (φ y) : ℤ) : ZMod N) ∧ ∃ b, c = φ y + N • b`. Introduce `x c`.

Take `⟨y, b, hb⟩` from `hφ1 c`. Use `⟨y, ?_, b, hb⟩` and prove the remaining obligations. Rewrite using `[hb, map_add, map_nsmul]`. Simplify using the standard rewrite rules. Establish `hcastL : ∀ x b c, ((D.EF (x + N • b) c : ℤ) : ZMod N) = ((D.EF x c : ℤ) : ZMod N)`.

Introduce `x b c`. Rewrite using `[map_add, map_nsmul]`. Simplify using the standard rewrite rules. Establish `hwell : ∀ (ψ₀ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N) x b, φ x = N • b → ψ₀ x = 0`. Introduce `ψ₀ x b h`.

Take `⟨x', rfl⟩` from `hφ2 x b h`. Rewrite using `[map_nsmul]`. Simplify using the standard rewrite rules. Use `⟨fun x => ev (φ x), e, fun x x' => by show ev (φ (x + x')) = ev (φ x) * ev (φ x')` and prove the remaining obligations. Rewrite using `[map_add, hadd], fun a x => by`.

Use `show ev (φ (a • x)) = ev (φ x) ≫ t.act.act a`. Rewrite using `[map_smul, hlin], ?_, ?_, ?_, ?_,`. Use the proof step `?_, ?_⟩`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Establish `h1 : (WeilObj.extPt ξ iK ≫ g) ^ N = 1` using `by rw [← MonObj.comp_pow, hg, MonObj.comp_one]`. Take `⟨a, ha⟩` from `(I.onto N hN0 _).1 h1`. Take `⟨x, b, hb⟩` from `hφ1 a`. Use `⟨x, inj _ _ ?_⟩` and prove the remaining obligations.

Use `show WeilObj.extPt ξ iK ≫ ev (φ x) = _`. Rewrite using `[← hkill x b, ← hb, hev, ha]`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `hevN _`. Introduce `x x' show ew (ev (φ x)) (ev (φ x')) = ζ ^ (e x x').val`.

Establish `h1 : ((I.ζ N ^ D.EF (φ x) (φ x') : kˣ) : k) = iK (ew (ev (φ x)) (ev (φ x')))` using `(hew.weil _ _ (hevN _) (hevN _) k iK (I.ev N (φ x)) (I.ev N (φ x')) (I.ζ N ^ D.EF (φ x) (φ x')) (hevk _) (hevk _)).1 (I.isom N hN0 _ _)`. Establish `hζN : ζ ^ N = 1` using `hζ.pow_eq_one`. Establish `h2 : e x x' = (((u : ℤ) * D.EF (φ x) (φ x') : ℤ) : ZMod N)`. Rewrite using `[he]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[h2, pow_val_intCast ζ N hζN]`. Establish `h3 : I.ζ N = Units.map iK.toMonoidHom ζ ^ u` using `Units.ext (by simpa using hu.symm)`. Apply `Units.map_injective (f := iK.toMonoidHom) iK.injective` to reduce the goal to its premises. Rewrite using `[map_zpow, zpow_mul, zpow_natCast, ← h3]`.

Conclude with `Units.ext (by simpa using h1.symm)`. Introduce `x`. Rewrite using `[he, D.alt]`. Simplify using the standard rewrite rules. Introduce `a x x'`.

Establish `hbar : RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a`. Use `ext`. Rewrite using `[H.bar_eq]`. Both sides reduce to the same expression. Rewrite using `[he, he, hbar, φ.map_smul, φ.map_smul, D.adj]`.

Introduce `ψ₀ choose s b hsb using hφ1`. Establish `hsub : ∀ x x' c, φ x = φ x' + N • c → ψ₀ x = ψ₀ x'`. Introduce `x x' c h`. Establish `h0 : ψ₀ (x - x') = 0` using `hwell ψ₀ _ c (by rw [map_sub, h]; abel)`. Rewrite `h0` using `[map_sub]`.

Conclude with `sub_eq_zero.1 h0`. Set `ψ : D.La →+ ZMod N` to `AddMonoidHom.mk' (fun m => ψ₀ (s m)) fun m m' => by`. Rewrite using `[← map_add]`. Use `hsub _ _ (b m + b m' - b (m + m')) ?_` and prove the remaining obligations. Establish `h1` using `hsb (m + m')`.

Establish `h2` using `hsb m`. Establish `h3` using `hsb m'`. Rewrite using `[map_add]`. Rewrite using `[smul_sub, smul_add]`. Establish `h4 : φ (s (m + m')) = m + m' - N • b (m + m')` using `by rw [eq_sub_iff_add_eq]; exact h1.symm`.

Rewrite using `[h4]`. Use `nth_rw 1 [h2]`. Use `nth_rw 1 [h3]`. Normalize the expressions using the abelian group laws. Establish `hψφ : ∀ y, ψ (φ y) = ψ₀ y` using `fun y => hsub _ _ (-(b (φ y))) (by`.

Establish `h1` using `hsb (φ y)`. Rewrite using `[smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]`. Conclude with `h1.symm)`. Use `haveI : Module.Projective (𝓞 E) D.La := D.proj`. Use `haveI : Module.Finite (𝓞 E) D.La := D.fin`.

Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La`. Use `haveI : Module.Free ℤ D.La := inferInstance`. Take `⟨h, hh⟩` from `Module.projective_lifting_property (Int.castAddHom (ZMod N)).toIntLinearMap ((AddMonoidHom.mulLeft v).comp ψ).toIntLinearMap (fun z => by`. Take `⟨w, hw⟩` from `ZMod.intCast_surjective z`.

Conclude with `⟨w, hw⟩)`. Take `⟨a, ha⟩` from `D.unimod.2 h`. Take `⟨x, hx⟩ : ∃ x, a = φ x + N • b a` from `⟨s a, hsb a⟩`. Use `⟨s a, AddMonoidHom.ext fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : ((h (φ y) : ℤ) : ZMod N) = v * ψ₀ y`.

Use `LinearMap.congr_fun hh (φ y)` as an intermediate fact. Simplify `this` using `[hψφ]`. Establish `h2` using `hcastL (φ (s a)) (b a) (φ y)`. Rewrite `h2` using `[← hsb a, ha, h1]`. Rewrite using `[he, ← h2, ← _root_.mul_assoc, hv, _root_.one_mul]`.

Introduce `x hx`. Establish `hd : ∀ c, (N : ℤ) ∣ D.EF (φ x) c`. Introduce `c`. Take `⟨y, hy, -⟩` from `hcast (φ x) c`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd, hy]`.

Establish `h1 : e x y = 0` using `by rw [hx]; rfl`. Rewrite `h1` using `[he]`. Take the linear combination `v * h1 - ((D.EF (φ x) (φ y) : ℤ) : ZMod N) * hv`. Take `⟨a', ha'⟩` from `(WeilObj.ef_dvd E H D N).1 (φ x) hd`. Conclude with `hφ2 x a' ha'`.
-/
theorem torsion_of_tate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (hN0 : 0 < N) (ζ : Ωˣ)
    (hζ : IsPrimitiveRoot ζ N) (k : Type) [Field k] [IsAlgClosed k] (iK : Ω →+* k)
    (I : XR.TateIsoAt D t (spMap iK ≫ ξ)) (hFT : FullTorsion t.G ξ N)
    (ew : (Over.mk ξ ⟶ t.G) → (Over.mk ξ ⟶ t.G) → Ωˣ) (hew : GenWeil t.G t.PP.L ξ N ew) :
    ∃ (τ : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk ξ ⟶ t.G))
      (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N),
      (∀ x x', τ (x + x') = τ x * τ x') ∧ (∀ (a : 𝓞 E) x, τ (a • x) = τ x ≫ t.act.act a) ∧
      (∀ g, g ^ N = 1 ↔ ∃ x, τ x = g) ∧ (∀ x x', ew (τ x) (τ x') = ζ ^ (e x x').val) ∧ (∀ x, e x x = 0) ∧
      (∀ (a : 𝓞 E) x x', e (a • x) x' = e x (RingOfIntegers.mapRingEquiv (HT.cmConj E) a • x')) ∧
      (∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N, ∃ x, e x = φ) ∧ ∀ x, e x = 0 → ∃ x', x = N • x' := by
  classical
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : Epi (spMap iK) := WeilObj.epi_spMap_field Ω k iK
  have inj : ∀ x x' : Over.mk ξ ⟶ t.G, WeilObj.extPt ξ iK ≫ x = WeilObj.extPt ξ iK ≫ x' → x = x' :=
    fun x x' h => by
      have h' : spMap iK ≫ x.left = spMap iK ≫ x'.left := congrArg CommaMorphism.left h
      exact Over.OverMorphism.ext ((cancel_epi (spMap iK)).1 h')
  have lift : ∀ a, ∃ x : Over.mk ξ ⟶ t.G, x ^ N = 1 ∧ WeilObj.extPt ξ iK ≫ x = I.ev N a := by
    intro a
    have ht : (I.ev N a) ^ N = 1 := (I.onto N hN0 _).2 ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hFT k iK (I.ev N a) ht
    have hxe : WeilObj.extPt ξ iK ≫ x = I.ev N a := Over.OverMorphism.ext hx.symm
    refine ⟨x, inj _ _ ?_, hxe⟩
    rw [MonObj.comp_pow, hxe, ht, MonObj.comp_one]
  choose ev hevN hev using lift
  have hadd : ∀ a b, ev (a + b) = ev a * ev b := fun a b => inj _ _ (by
    rw [MonObj.comp_mul, hev, hev, hev, I.add])
  have hlin : ∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ t.act.act c := fun c a => inj _ _ (by
    rw [← Category.assoc, hev, hev]; exact I.lin N c a)
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.projective_module_mod_N_basis E D.La D.fin D.proj (D.p + D.q) N D.rank hN0

  have hζΩ : IsPrimitiveRoot (ζ : Ω) N := hζ.map_of_injective (f := Units.coeHom Ω) Units.val_injective
  have hζK : IsPrimitiveRoot (iK ζ) N := hζΩ.map_of_injective iK.injective
  have hIK : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N :=
    (I.ζ_prim N hN0).map_of_injective (f := Units.coeHom k) Units.val_injective
  obtain ⟨u, -, hu⟩ := hζK.eq_pow_of_pow_eq_one (ξ := ((I.ζ N : kˣ) : k)) hIK.pow_eq_one
  have hcop : u.Coprime N := by
    have h1 : IsPrimitiveRoot (iK ζ ^ u) N := by rw [hu]; exact hIK
    exact (hζK.pow_iff_coprime hN0 u).1 h1
  obtain ⟨v, hv⟩ : ∃ v : ZMod N, (u : ZMod N) * v = 1 := by
    obtain ⟨w, hw⟩ := (ZMod.isUnit_iff_coprime u N).2 hcop
    exact ⟨((w⁻¹ : (ZMod N)ˣ) : ZMod N), by rw [← hw]; exact w.mul_inv⟩
  let e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun x' => (u : ZMod N) * ((D.EF (φ x) (φ x') : ℤ) : ZMod N))
      fun a b => by simp only [map_add, Int.cast_add, mul_add]) fun a b => by
      ext y
      simp [map_add, mul_add, LinearMap.add_apply]
  have he : ∀ x x', e x x' = (u : ZMod N) * ((D.EF (φ x) (φ x') : ℤ) : ZMod N) := fun _ _ => rfl
  have hevk : ∀ a, (I.ev N a).left = spMap iK ≫ (ev a).left := fun a => by rw [← hev a]; rfl
  have hkill : ∀ (x : Fin (D.p + D.q) → 𝓞 E), ∀ b, ev (φ x + N • b) = ev (φ x) := by
    intro x b
    refine inj _ _ ?_
    rw [hev, hev, I.add, ((I.ker N hN0 (N • b)).2 ⟨b, rfl⟩), _root_.mul_one]
  have hcast : ∀ x c, ∃ y, ((D.EF x c : ℤ) : ZMod N) = ((D.EF x (φ y) : ℤ) : ZMod N) ∧ ∃ b, c = φ y + N • b := by
    intro x c
    obtain ⟨y, b, hb⟩ := hφ1 c
    refine ⟨y, ?_, b, hb⟩
    rw [hb, map_add, map_nsmul]
    simp
  have hcastL : ∀ x b c, ((D.EF (x + N • b) c : ℤ) : ZMod N) = ((D.EF x c : ℤ) : ZMod N) := by
    intro x b c
    rw [map_add, map_nsmul]
    simp
  have hwell : ∀ (ψ₀ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod N) x b, φ x = N • b → ψ₀ x = 0 := by
    intro ψ₀ x b h
    obtain ⟨x', rfl⟩ := hφ2 x b h
    rw [map_nsmul]
    simp
  refine ⟨fun x => ev (φ x), e, fun x x' => by
    show ev (φ (x + x')) = ev (φ x) * ev (φ x')
    rw [map_add, hadd], fun a x => by
    show ev (φ (a • x)) = ev (φ x) ≫ t.act.act a
    rw [map_smul, hlin], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      have h1 : (WeilObj.extPt ξ iK ≫ g) ^ N = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
      obtain ⟨a, ha⟩ := (I.onto N hN0 _).1 h1
      obtain ⟨x, b, hb⟩ := hφ1 a
      refine ⟨x, inj _ _ ?_⟩
      show WeilObj.extPt ξ iK ≫ ev (φ x) = _
      rw [← hkill x b, ← hb, hev, ha]
    · rintro ⟨x, rfl⟩
      exact hevN _
  · intro x x'
    show ew (ev (φ x)) (ev (φ x')) = ζ ^ (e x x').val
    have h1 : ((I.ζ N ^ D.EF (φ x) (φ x') : kˣ) : k) = iK (ew (ev (φ x)) (ev (φ x'))) :=
      (hew.weil _ _ (hevN _) (hevN _) k iK (I.ev N (φ x)) (I.ev N (φ x')) (I.ζ N ^ D.EF (φ x) (φ x'))
        (hevk _) (hevk _)).1 (I.isom N hN0 _ _)
    have hζN : ζ ^ N = 1 := hζ.pow_eq_one
    have h2 : e x x' = (((u : ℤ) * D.EF (φ x) (φ x') : ℤ) : ZMod N) := by
      rw [he]; push_cast; rfl
    rw [h2, pow_val_intCast ζ N hζN]
    have h3 : I.ζ N = Units.map iK.toMonoidHom ζ ^ u := Units.ext (by simpa using hu.symm)
    apply Units.map_injective (f := iK.toMonoidHom) iK.injective
    rw [map_zpow, zpow_mul, zpow_natCast, ← h3]
    exact Units.ext (by simpa using h1.symm)
  · intro x
    rw [he, D.alt]
    simp
  · intro a x x'
    have hbar : RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := by
      ext
      rw [H.bar_eq]
      rfl
    rw [he, he, hbar, φ.map_smul, φ.map_smul, D.adj]
  · intro ψ₀
    choose s b hsb using hφ1
    have hsub : ∀ x x' c, φ x = φ x' + N • c → ψ₀ x = ψ₀ x' := by
      intro x x' c h
      have h0 : ψ₀ (x - x') = 0 := hwell ψ₀ _ c (by rw [map_sub, h]; abel)
      rw [map_sub] at h0
      exact sub_eq_zero.1 h0
    let ψ : D.La →+ ZMod N := AddMonoidHom.mk' (fun m => ψ₀ (s m)) fun m m' => by
      rw [← map_add]
      refine hsub _ _ (b m + b m' - b (m + m')) ?_
      have h1 := hsb (m + m')
      have h2 := hsb m
      have h3 := hsb m'
      rw [map_add]
      rw [smul_sub, smul_add]
      have h4 : φ (s (m + m')) = m + m' - N • b (m + m') := by rw [eq_sub_iff_add_eq]; exact h1.symm
      rw [h4]
      nth_rw 1 [h2]
      nth_rw 1 [h3]
      abel
    have hψφ : ∀ y, ψ (φ y) = ψ₀ y := fun y => hsub _ _ (-(b (φ y))) (by
      have h1 := hsb (φ y)
      rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
      exact h1.symm)
    haveI : Module.Projective (𝓞 E) D.La := D.proj
    haveI : Module.Finite (𝓞 E) D.La := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
    haveI : Module.Free ℤ D.La := inferInstance
    obtain ⟨h, hh⟩ := Module.projective_lifting_property (Int.castAddHom (ZMod N)).toIntLinearMap
      ((AddMonoidHom.mulLeft v).comp ψ).toIntLinearMap (fun z => by
        obtain ⟨w, hw⟩ := ZMod.intCast_surjective z
        exact ⟨w, hw⟩)
    obtain ⟨a, ha⟩ := D.unimod.2 h
    obtain ⟨x, hx⟩ : ∃ x, a = φ x + N • b a := ⟨s a, hsb a⟩
    refine ⟨s a, AddMonoidHom.ext fun y => ?_⟩
    have h1 : ((h (φ y) : ℤ) : ZMod N) = v * ψ₀ y := by
      have := LinearMap.congr_fun hh (φ y)
      simpa [hψφ] using this
    have h2 := hcastL (φ (s a)) (b a) (φ y)
    rw [← hsb a, ha, h1] at h2
    rw [he, ← h2, ← _root_.mul_assoc, hv, _root_.one_mul]
  · intro x hx
    have hd : ∀ c, (N : ℤ) ∣ D.EF (φ x) c := by
      intro c
      obtain ⟨y, hy, -⟩ := hcast (φ x) c
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hy]
      have h1 : e x y = 0 := by rw [hx]; rfl
      rw [he] at h1
      linear_combination v * h1 - ((D.EF (φ x) (φ y) : ℤ) : ZMod N) * hv
    obtain ⟨a', ha'⟩ := (WeilObj.ef_dvd E H D N).1 (φ x) hd
    exact hφ2 x a' ha'

/- English proof (translation)
Introduce `hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 y₀ p ζ hp hξ hζ`. Establish `hN0 : 0 < p ^ 𝔐.R p` using `pow_pos (𝔐.S_prime p hp).pos _`. Establish `hFT0 : FullTorsion Y.t.G (y₀ ≫ Y.j) (p ^ 𝔐.R p)` using `fullTorsion_push Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ _ hξ.symm _ (𝔐.tors p hp)`. Establish `hζΩ : IsPrimitiveRoot (ζ : Ω) (p ^ 𝔐.R p)` using `hζ.map_of_injective (f := Units.coeHom Ω) Units.val_injective`. Take `⟨e₀, he₀⟩` from `WeilObj.genWeil_of_obj hW E H D l (KA l) (baseKA l) (Xo.XF c) Y.X _ Y.oF Y.t Y.j Y.m Ω y₀ (p ^ 𝔐.R p) hN0 hFT0 ⟨ζ, hζΩ⟩`.

Take `⟨ew, hew⟩` from `genWeil_move Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ (y₀ ≫ Y.j) hξ.symm _ e₀ he₀`. Set `iK : Ω →+* AlgebraicClosure Ω` to `algebraMap Ω (AlgebraicClosure Ω)`. Establish `hI : Nonempty (XR.TateIsoAt D 𝔐.t (spMap iK ≫ 𝔐.ξ))`. Set `s₀` to `pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s`. Set `β₀ : KA l →+* Ω` to `(Spec.preimage (y₀ ≫ s₀)).hom`.

Establish `h1 : spMap β₀ = y₀ ≫ s₀`. Simplify using `only [β₀, spMap, CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hβ : (spMap iK ≫ y₀) ≫ s₀ = spMap (iK.comp β₀)`. Rewrite using `[Category.assoc, WeilObj.spMap_comp_of, h1]`. Take `⟨-, I₀, -, -, -⟩` from `Y.oF.geom (AlgebraicClosure Ω) (spMap iK ≫ y₀) (iK.comp β₀) hβ`.

Take `⟨I₁, -, -⟩` from `(XR.tateIsoAt_move E H D Y.X (Xo.XF c) Y.t Y.oF.t Y.j Y.m (AlgebraicClosure Ω) (spMap iK ≫ y₀) (spMap iK ≫ y₀ ≫ Y.j) (Category.assoc _ _ _).symm).2 I₀`. Take `⟨I, -, -⟩` from `(XR.tateIsoAt_move E H D Y.X 𝔐.X Y.t 𝔐.t 𝔐.f 𝔐.m (AlgebraicClosure Ω) (spMap iK ≫ 𝔐.ξ) (spMap iK ≫ y₀ ≫ Y.j) (by rw [Category.assoc, hξ])).1 I₁`. Conclude with `⟨I⟩`. Take `⟨I⟩` from `hI`. Take `⟨τ, e, h1, h2, h3, h4, h5, h6, h7, h8⟩` from `torsion_of_tate H D 𝔐.t 𝔐.ξ _ hN0 ζ hζ (AlgebraicClosure Ω) iK I (𝔐.tors p hp) ew hew`.

Conclude with `⟨τ, ew, e, h1, h2, h3, hew, h4, h5, h6, h7, h8⟩`.
-/
theorem generic_torsion : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ) (ζ : Ωˣ), p ∈ S → 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → IsPrimitiveRoot ζ (p ^ 𝔐.R p) → ∃ (τ : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G)) (ew : (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → Ωˣ) (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p)), (∀ x x', τ (x + x') = τ x * τ x') ∧ (∀ (a : 𝓞 E) x, τ (a • x) = τ x ≫ 𝔐.t.act.act a) ∧ (∀ g, g ^ (p ^ 𝔐.R p) = 1 ↔ ∃ x, τ x = g) ∧ GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ (p ^ 𝔐.R p) ew ∧ (∀ x x', ew (τ x) (τ x') = ζ ^ (e x x').val) ∧ (∀ x, e x x = 0) ∧ (∀ (a : 𝓞 E) x x', e (a • x) x' = e x (RingOfIntegers.mapRingEquiv (HT.cmConj E) a • x')) ∧ (∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p), ∃ x, e x = φ) ∧ ∀ x, e x = 0 → ∃ x', x = (p ^ 𝔐.R p) • x' := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 y₀ p ζ hp hξ hζ
  have hN0 : 0 < p ^ 𝔐.R p := pow_pos (𝔐.S_prime p hp).pos _
  have hFT0 : FullTorsion Y.t.G (y₀ ≫ Y.j) (p ^ 𝔐.R p) :=
    fullTorsion_push Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ _ hξ.symm _ (𝔐.tors p hp)
  have hζΩ : IsPrimitiveRoot (ζ : Ω) (p ^ 𝔐.R p) := hζ.map_of_injective (f := Units.coeHom Ω) Units.val_injective
  obtain ⟨e₀, he₀⟩ := WeilObj.genWeil_of_obj hW E H D l (KA l) (baseKA l) (Xo.XF c) Y.X _ Y.oF Y.t Y.j Y.m Ω y₀
    (p ^ 𝔐.R p) hN0 hFT0 ⟨ζ, hζΩ⟩
  obtain ⟨ew, hew⟩ := genWeil_move Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ (y₀ ≫ Y.j) hξ.symm _ e₀ he₀
  let iK : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  have hI : Nonempty (XR.TateIsoAt D 𝔐.t (spMap iK ≫ 𝔐.ξ)) := by
    let s₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
    let β₀ : KA l →+* Ω := (Spec.preimage (y₀ ≫ s₀)).hom
    have h1 : spMap β₀ = y₀ ≫ s₀ := by
      simp only [β₀, spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ : (spMap iK ≫ y₀) ≫ s₀ = spMap (iK.comp β₀) := by
      rw [Category.assoc, WeilObj.spMap_comp_of, h1]
    obtain ⟨-, I₀, -, -, -⟩ := Y.oF.geom (AlgebraicClosure Ω) (spMap iK ≫ y₀) (iK.comp β₀) hβ
    obtain ⟨I₁, -, -⟩ := (XR.tateIsoAt_move E H D Y.X (Xo.XF c) Y.t Y.oF.t Y.j Y.m (AlgebraicClosure Ω)
      (spMap iK ≫ y₀) (spMap iK ≫ y₀ ≫ Y.j) (Category.assoc _ _ _).symm).2 I₀
    obtain ⟨I, -, -⟩ := (XR.tateIsoAt_move E H D Y.X 𝔐.X Y.t 𝔐.t 𝔐.f 𝔐.m (AlgebraicClosure Ω)
      (spMap iK ≫ 𝔐.ξ) (spMap iK ≫ y₀ ≫ Y.j) (by rw [Category.assoc, hξ])).1 I₁
    exact ⟨I⟩
  obtain ⟨I⟩ := hI
  obtain ⟨τ, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ := torsion_of_tate H D 𝔐.t 𝔐.ξ _ hN0 ζ hζ (AlgebraicClosure Ω) iK I
    (𝔐.tors p hp) ew hew
  exact ⟨τ, ew, e, h1, h2, h3, hew, h4, h5, h6, h7, h8⟩

end GlobalTheory.CompanionTheory.Ar.HF
