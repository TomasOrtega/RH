import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section Cart

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Set `x₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) (by`. Establish `e` using `Over.w (1 : T ⟶ G')`. Simplify using `only [Over.mk_hom, Category.assoc, hp.1.w]`. Rewrite using `[← Category.assoc, e])`. Establish `h` using `hp.2 T 1 1 x₀ x₀ rfl rfl`.

Rewrite `h` using `[_root_.mul_one]`. Establish `h2 : x₀ * x₀ = x₀` using `Over.OverMorphism.ext h`. Establish `h3 : x₀ = 1` using `by simpa using h2`. Conclude with `congrArg (fun g => g.left) h3`.
-/
private theorem one_left_cart (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    have e := Over.w (1 : T ⟶ G')
    simp only [Over.mk_hom, Category.assoc, hp.1.w]
    rw [← Category.assoc, e])
  have h := hp.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have h2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have h3 : x₀ = 1 := by simpa using h2
  exact congrArg (fun g => g.left) h3

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `one_left_cart hp T`. Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `hp.1.hom_ext` to reduce the goal to its premises. Rewrite using `[h, one_left_cart hp T]`. Rewrite using `[Over.w x, Over.w (1 : T ⟶ G')]`.
-/
private theorem kill_iff (hp : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') :
    x = 1 ↔ x.left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  constructor
  · rintro rfl
    exact one_left_cart hp T
  · intro h
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · rw [h, one_left_cart hp T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end Cart

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem one_left_congr {X Y : Scheme.{0}} {G : Over Y} [GrpObj G] {g g' : X ⟶ Y} (e : g = g') :
    (1 : Over.mk g ⟶ G).left = (1 : Over.mk g' ⟶ G).left := by
  subst e; rfl

/- English proof (translation)
Substitute `e` using the available equality. Take `rfl : b = b'` from `Over.OverMorphism.ext hl`. Both sides reduce to the same expression.
-/
private theorem kill_transfer {X Y : Scheme.{0}} {A B : Over Y} [GrpObj B] {g g' : X ⟶ Y} (e : g = g')
    (b : Over.mk g ⟶ A) (b' : Over.mk g' ⟶ A) (hl : b.left = b'.left) (ψ : A ⟶ B) :
    b ≫ ψ = 1 ↔ b' ≫ ψ = 1 := by
  subst e
  obtain rfl : b = b' := Over.OverMorphism.ext hl
  rfl

/- English proof (translation)
Simplify using `using Over.w (toUnit (Over.mk e))`.
-/
private theorem unit_left {X Y : Scheme.{0}} (e : Y ⟶ X) : (toUnit (Over.mk e)).left = e := by
  simpa using Over.w (toUnit (Over.mk e))

/- English proof (translation)
Establish `L : (b ≫ ψ₀).left ≫ mt = (a ≫ ψW).left ≫ φ ≫ cm`. Simplify using `only [Over.comp_left, Category.assoc, hb]`. Rewrite using `[hmt]`. Establish `E : (Over.mk (e ≫ y)).hom ≫ tt = (Over.mk e).hom ≫ π ≫ j`. Simplify using `only [Over.mk_hom, Category.assoc, hyt]`.

Rewrite using `[kill_iff h1, kill_iff (h2.comp h3), L, one_left_congr E]`.
-/
private theorem kill_chain {X' Z EX X P : Scheme.{0}} {A' Wo : Over X'} {o o' : Over Z} {U : Over EX} {B : Over X}
    [GrpObj o'] [GrpObj U] [GrpObj B] [GrpObj Wo]
    {y : X' ⟶ Z} {tt : Z ⟶ EX} {π : X' ⟶ X} {j : X ⟶ EX} {mφ : A'.left ⟶ o.left} {ψ₀ : o ⟶ o'}
    {mt : o'.left ⟶ U.left} {ψW : A' ⟶ Wo} {φ : Wo.left ⟶ B.left} {cm : B.left ⟶ U.left}
    (h1 : IsGrpPullback o' U tt mt) (h2 : IsGrpPullback Wo B π φ) (h3 : IsGrpPullback B U j cm)
    (hyt : y ≫ tt = π ≫ j) (hmt : mφ ≫ ψ₀.left ≫ mt = ψW.left ≫ φ ≫ cm)
    (e : P ⟶ X') (a : Over.mk e ⟶ A') (b : Over.mk (e ≫ y) ⟶ o) (hb : b.left = a.left ≫ mφ) :
    b ≫ ψ₀ = 1 ↔ a ≫ ψW = 1 := by
  have L : (b ≫ ψ₀).left ≫ mt = (a ≫ ψW).left ≫ φ ≫ cm := by
    simp only [Over.comp_left, Category.assoc, hb]
    rw [hmt]
  have E : (Over.mk (e ≫ y)).hom ≫ tt = (Over.mk e).hom ≫ π ≫ j := by
    simp only [Over.mk_hom, Category.assoc, hyt]
  rw [kill_iff h1, kill_iff (h2.comp h3), L, one_left_congr E]

section Grp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

/- English proof (translation)
Take `⟨d, rfl⟩` from `hd`. Introduce `v hv`. Take `⟨v', hv', e⟩` from `hb (d • v) (nsmul_mem hv d)`. Use `⟨L.actG g⁻¹ v', integ_of_mem (inv_mem hg) _ hv', ?_⟩` and prove the remaining obligations. Establish `e1 : L.actG (h * g) (L.actG g⁻¹ v') = L.actG h v'`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]`. Rewrite using `[e1, e, mul_smul]`.
-/
private theorem back_mul {h g : G.GAf} {m M : ℕ} (hb : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = m • v)
    (hd : m ∣ M) (hg : g ∈ L.KN 1) : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * g) v' = M • v := by
  obtain ⟨d, rfl⟩ := hd
  intro v hv
  obtain ⟨v', hv', e⟩ := hb (d • v) (nsmul_mem hv d)
  refine ⟨L.actG g⁻¹ v', integ_of_mem (inv_mem hg) _ hv', ?_⟩
  have e1 : L.actG (h * g) (L.actG g⁻¹ v') = L.actG h v' := by
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
  rw [e1, e, mul_smul]

/- English proof (translation)
Rewrite using `[hgg, map_add, map_nsmul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, e⟩`. Conclude with `⟨v + L.actG g w, add_mem hv (hg w hw), by rw [e, smul_add]⟩`. Introduce and unpack `⟨v, hv, e⟩`.

Use `⟨v - L.actG g w, sub_mem hv (hg w hw), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← e, add_sub_cancel_right]`.
-/
private theorem mod_iff {g g' : G.GAf} {M : ℕ} {x' : D.La} {x : D.La} {w : AfP p ⊗[ℚ] VQ D} (hg : Integ L g)
    (hw : w ∈ LaHat D) (hgg : L.actG (g * g') (inAf D x) = L.actG g (inAf D x' + M • w)) :
    (∃ v ∈ LaHat D, L.actG g (inAf D x') = M • v) ↔ ∃ v ∈ LaHat D, L.actG (g * g') (inAf D x) = M • v := by
  rw [hgg, map_add, map_nsmul]
  constructor
  · rintro ⟨v, hv, e⟩
    exact ⟨v + L.actG g w, add_mem hv (hg w hw), by rw [e, smul_add]⟩
  · rintro ⟨v, hv, e⟩
    refine ⟨v - L.actG g w, sub_mem hv (hg w hw), ?_⟩
    rw [smul_sub, ← e, add_sub_cancel_right]

end Grp

/- English proof (translation)
Introduce `hNum hBI hTr hPt hCRT hLat hCong p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN hNumN C' C hdvd u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ W₁ W₂ V₁ V₂ l₁ l₂ Ω _ _ z hz`. Establish `hpos : 0 < N'.1` using `by have := N'.2.1; omega`. Establish `hKN : ∀ {g}, g ∈ K₀ → g ∈ L.KN 1` using `fun hg => ((hLev _).1 hg).1`. Establish `hNum' : S.Num N'.1 (c * t) (t * a)`. Rewrite using `[hN]`.

Conclude with `(hNum p D E gb w q r 𝔴 𝔫 S N.1 (by have := N.2.1; omega)).2 c a t hNumN`. Choose the witnesses or unpack the hypotheses as in `⟨C₂, hC₂⟩ : ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C'.m.φ := by`. Establish `: ∀ (c₁ : ℕ) (a₁ : 𝓞 D.F), c₁ = c * t * 1 → a₁ = ((1 : ℕ) : 𝓞 D.F) * (t * a) → ∀ C₁ : S.Cl (T.M N').univ c₁ a₁, ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C₁.m.φ`. Introduce and unpack `_ _ rfl rfl C₁`. Conclude with `⟨C₁, rfl⟩`.

Conclude with `this _ _ (by simp) (by simp) C'`. Establish `step : ∀ (u v : G.GAf), u ∈ K₀ → v ∈ K₀ → ∀ (W : Wit T (h * u) N' N) (V : Wit T v N' N') (l : Lift S T Lj W C' C) (x : D.La), ∃ b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A, b.left ≫ Lj.ms.φ = z ≫ ((T.M N').univ.eta x).left ≫ C'.m.φ ∧ (b ≫ Lj.ψ = 1 ↔ ∃ v' ∈ LaHat D, L.actG (h * u * v) …`. Introduce `u v hu hv W V l x`. Take `⟨x', w', hw', e⟩` from `GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N'.1 hpos N'.2.2 (L.actG v (inAf D x)) (integ_of_mem (hKN hv) _ (AddSubgroup.subset_closure ⟨1, x, fun v => by simp, rfl⟩))`. Establish `hinv` using `(hBI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N' N' 1 (c * t) (t * a) (by simp) hNum' C₂ C' v hv V).2`.

Rewrite `hinv` using `[hC₂]`. Establish `htr` using `hTr p D G L E gb v (T.M N').X (T.M N').s N' N' (T.M N').univ V.o V.ψ V.trans N'.1 1 1 (by simp) (by simp) x x' ⟨w', hw', e⟩`. Simplify using `only [one_smul] at htr`. Establish `hugInt : Integ L (h * u)` using `hInt.mul (integ_of_mem (hKN hu))`. Set `a₀ : Over.mk (z ≫ V.π) ⟶ (T.M N').univ.A` to `toUnit _ ≫ (T.M N').univ.eta x'`.

Establish `ha₀ : a₀.left = (z ≫ V.π) ≫ ((T.M N').univ.eta x').left`. Simplify using `only [a₀, Over.comp_left, unit_left]`. Set `b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A` to `Over.homMk (a₀.left ≫ l.m.φ) (by`. Establish `e1` using `l.m.cart.1.w`. Establish `e2` using `Over.w a₀`.

Simplify using `only [Over.mk_hom, Category.assoc] at e2 ⊢`. Rewrite using `[e1, ← Category.assoc, e2, Category.assoc])`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Establish `e3` using `V.φ.eta x'`. Establish `e4` using `congrArg (fun g => g.left) htr`.

Simplify using `only [Over.comp_left] at e4`. Use `show (a₀.left ≫ l.m.φ) ≫ Lj.ms.φ = _`. Rewrite using `[Category.assoc, l.ms, ha₀, Category.assoc, Category.assoc, ← Category.assoc V.π, ← e3, ← e4]`. Simplify using `only [Category.assoc, hinv]`. Establish `hc` using `kill_chain (ψ₀ := Lj.ψ) (ψW := W.ψ) Lj.mt.cart W.φ.cart C.m.cart l.yt l.mt (z ≫ V.π) a₀ b rfl`.

Rewrite using `[hc]`. Use `(hPt p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans Ω (z ≫ V.π) x').1` as an intermediate fact. Rewrite using `[show a₀ ≫ W.ψ = _ from Category.assoc _ _ _, this]`. Conclude with `mod_iff hugInt hw' (by rw [map_mul, Module.End.mul_apply, e])`. Establish `key : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG (h * u₁ * v₁) (inAf D x) = N'.1 • v) ↔ ∃ v ∈ LaHat D, L.actG (h * u₂ * v₂) (inAf D x) = N'.1 • v`.

Introduce `x`. Take `⟨b₁, e₁, k₁⟩` from `step u₁ v₁ hu₁ hv₁ W₁ V₁ l₁ x`. Take `⟨b₂, e₂, k₂⟩` from `step u₂ v₂ hu₂ hv₂ W₂ V₂ l₂ x`. Establish `hy : (z ≫ V₁.π) ≫ l₁.y = (z ≫ V₂.π) ≫ l₂.y`. Simplify `hz` using `only [Category.assoc]`.

Establish `hl : b₁.left = b₂.left`. Apply `Lj.ms.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[e₁, e₂]`. Rewrite using `[Over.w b₁, Over.w b₂]`. Conclude with `hy`.

Rewrite using `[← k₁, ← k₂]`. Conclude with `kill_transfer hy b₁ b₂ hl Lj.ψ`. Establish `hI₁ : Integ L (h * u₁ * v₁)` using `(hInt.mul (integ_of_mem (hKN hu₁))).mul (integ_of_mem (hKN hv₁))`. Establish `hI₂ : Integ L (h * u₂ * v₂)` using `(hInt.mul (integ_of_mem (hKN hu₂))).mul (integ_of_mem (hKN hv₂))`. Establish `hB₁ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₁ * v₁) v' = N'.1 • v`.

Rewrite using `[_root_.mul_assoc]`. Conclude with `back_mul hTj.back hdvd (mul_mem (hKN hu₁) (hKN hv₁))`. Establish `hB₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₂ * v₂) v' = N'.1 • v`. Rewrite using `[_root_.mul_assoc]`. Conclude with `back_mul hTj.back hdvd (mul_mem (hKN hu₂) (hKN hv₂))`.

Establish `hlat` using `hLat p D G L N'.1 hpos N'.2.2 (h * u₁ * v₁) (h * u₂ * v₂) hI₁ hI₂ hB₁ hB₂ key`. Establish `hcg : CongId L 𝔫 h`. Rewrite using `[S.lev]`. Conclude with `(hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow h hInt).1.2 ⟨hTj.away _ S.std.cop, hTj.other _ S.sup S.upow⟩`. Establish `heq : h * (u₁ * v₁ * (u₂ * v₂)⁻¹) * h⁻¹ = h * u₁ * v₁ * (h * u₂ * v₂)⁻¹` using `by group`.

Conclude with `hCong p D G L 𝔫 K₀ hLev h _ hInt hcg (mul_mem (mul_mem hu₁ hv₁) (inv_mem (mul_mem hu₂ hv₂))) (heq ▸ hlat)`.
-/
theorem UpperTheory.hecke_lift_separated_of_lattice_congruence :
    NumEx → BaseInv → TrEta → TrEtaPt → CongCRT → GrpLat → GrpCong → LiftSep := by
  intro hNum hBI hTr hPt hCRT hLat hCong p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N
    t c a hN hNumN C' C hdvd u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ W₁ W₂ V₁ V₂ l₁ l₂ Ω _ _ z hz
  have hpos : 0 < N'.1 := by have := N'.2.1; omega
  have hKN : ∀ {g}, g ∈ K₀ → g ∈ L.KN 1 := fun hg => ((hLev _).1 hg).1
  have hNum' : S.Num N'.1 (c * t) (t * a) := by
    rw [hN]
    exact (hNum p D E gb w q r 𝔴 𝔫 S N.1 (by have := N.2.1; omega)).2 c a t hNumN

  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C'.m.φ := by
    have : ∀ (c₁ : ℕ) (a₁ : 𝓞 D.F), c₁ = c * t * 1 → a₁ = ((1 : ℕ) : 𝓞 D.F) * (t * a) → ∀ C₁ : S.Cl (T.M N').univ c₁ a₁,
        ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C₁.m.φ := by
      rintro _ _ rfl rfl C₁
      exact ⟨C₁, rfl⟩
    exact this _ _ (by simp) (by simp) C'
  have step : ∀ (u v : G.GAf), u ∈ K₀ → v ∈ K₀ → ∀ (W : Wit T (h * u) N' N) (V : Wit T v N' N') (l : Lift S T Lj W C' C) (x : D.La),
      ∃ b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A, b.left ≫ Lj.ms.φ = z ≫ ((T.M N').univ.eta x).left ≫ C'.m.φ ∧
        (b ≫ Lj.ψ = 1 ↔ ∃ v' ∈ LaHat D, L.actG (h * u * v) (inAf D x) = N'.1 • v') := by
    intro u v hu hv W V l x
    obtain ⟨x', w', hw', e⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N'.1 hpos N'.2.2 (L.actG v (inAf D x))
      (integ_of_mem (hKN hv) _ (AddSubgroup.subset_closure ⟨1, x, fun v => by simp, rfl⟩))
    have hinv := (hBI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N' N' 1 (c * t) (t * a) (by simp) hNum' C₂ C' v hv V).2
    rw [hC₂] at hinv
    have htr := hTr p D G L E gb v (T.M N').X (T.M N').s N' N' (T.M N').univ V.o V.ψ V.trans N'.1 1 1 (by simp) (by simp) x x'
      ⟨w', hw', e⟩
    simp only [one_smul] at htr
    have hugInt : Integ L (h * u) := hInt.mul (integ_of_mem (hKN hu))
    let a₀ : Over.mk (z ≫ V.π) ⟶ (T.M N').univ.A := toUnit _ ≫ (T.M N').univ.eta x'
    have ha₀ : a₀.left = (z ≫ V.π) ≫ ((T.M N').univ.eta x').left := by
      simp only [a₀, Over.comp_left, unit_left]
    let b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A := Over.homMk (a₀.left ≫ l.m.φ) (by
      have e1 := l.m.cart.1.w
      have e2 := Over.w a₀
      simp only [Over.mk_hom, Category.assoc] at e2 ⊢
      rw [e1, ← Category.assoc, e2, Category.assoc])
    refine ⟨b, ?_, ?_⟩
    · have e3 := V.φ.eta x'
      have e4 := congrArg (fun g => g.left) htr
      simp only [Over.comp_left] at e4
      show (a₀.left ≫ l.m.φ) ≫ Lj.ms.φ = _
      rw [Category.assoc, l.ms, ha₀, Category.assoc, Category.assoc, ← Category.assoc V.π, ← e3, ← e4]
      simp only [Category.assoc, hinv]
    · have hc := kill_chain (ψ₀ := Lj.ψ) (ψW := W.ψ) Lj.mt.cart W.φ.cart C.m.cart l.yt l.mt (z ≫ V.π) a₀ b rfl
      rw [hc]
      have := (hPt p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans Ω (z ≫ V.π) x').1
      rw [show a₀ ≫ W.ψ = _ from Category.assoc _ _ _, this]
      exact mod_iff hugInt hw' (by rw [map_mul, Module.End.mul_apply, e])
  have key : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG (h * u₁ * v₁) (inAf D x) = N'.1 • v) ↔
      ∃ v ∈ LaHat D, L.actG (h * u₂ * v₂) (inAf D x) = N'.1 • v := by
    intro x
    obtain ⟨b₁, e₁, k₁⟩ := step u₁ v₁ hu₁ hv₁ W₁ V₁ l₁ x
    obtain ⟨b₂, e₂, k₂⟩ := step u₂ v₂ hu₂ hv₂ W₂ V₂ l₂ x
    have hy : (z ≫ V₁.π) ≫ l₁.y = (z ≫ V₂.π) ≫ l₂.y := by
      simpa only [Category.assoc] using hz
    have hl : b₁.left = b₂.left := by
      apply Lj.ms.cart.1.hom_ext
      · rw [e₁, e₂]
      · rw [Over.w b₁, Over.w b₂]
        exact hy
    rw [← k₁, ← k₂]
    exact kill_transfer hy b₁ b₂ hl Lj.ψ
  have hI₁ : Integ L (h * u₁ * v₁) := (hInt.mul (integ_of_mem (hKN hu₁))).mul (integ_of_mem (hKN hv₁))
  have hI₂ : Integ L (h * u₂ * v₂) := (hInt.mul (integ_of_mem (hKN hu₂))).mul (integ_of_mem (hKN hv₂))
  have hB₁ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₁ * v₁) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₁) (hKN hv₁))
  have hB₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₂ * v₂) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₂) (hKN hv₂))
  have hlat := hLat p D G L N'.1 hpos N'.2.2 (h * u₁ * v₁) (h * u₂ * v₂) hI₁ hI₂ hB₁ hB₂ key
  have hcg : CongId L 𝔫 h := by
    rw [S.lev]
    exact (hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow h hInt).1.2 ⟨hTj.away _ S.std.cop, hTj.other _ S.sup S.upow⟩
  have heq : h * (u₁ * v₁ * (u₂ * v₂)⁻¹) * h⁻¹ = h * u₁ * v₁ * (h * u₂ * v₂)⁻¹ := by group
  exact hCong p D G L 𝔫 K₀ hLev h _ hInt hcg (mul_mem (mul_mem hu₁ hv₁) (inv_mem (mul_mem hu₂ hv₂))) (heq ▸ hlat)
