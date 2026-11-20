import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ c : ℕ}

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨n, rfl⟩`.
-/
private theorem qcast {o' : GObj gb N s'} {o : Obj b N₀ s} {f g : S' ⟶ S} (e : f = g) (n : QMap o' o f c) :
    ∃ n' : QMap o' o g c, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o`.
-/
private theorem qobj' (hObj : QObj) (β : R →+* R') (hm : Match b gb β) (hN : N = N₀ * c) (h0 : 0 < N) (hc : N₀.Coprime q)
    (o : GObj gb N s') {s₀ : S' ⟶ Sp R} (e : s₀ = s' ≫ spMap β) : ∃ o₀ : Obj b N₀ s₀, Nonempty (QMap o o₀ (𝟙 S') c) := by
  subst e
  exact hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o

/- English proof (translation)
Simplify using `using Over.w e`.
-/
private theorem sec_hom {X : Scheme.{0}} {A : Over X} (e : 𝟙_ (Over X) ⟶ A) : e.left ≫ A.hom = 𝟙 X := by
  simpa using Over.w e

/- English proof (translation)
Use `⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem sec_lift {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f : X ⟶ Y} {φ : A.left ⟶ B.left}
    (hc : IsPullback φ A.hom B.hom f) (e : 𝟙_ (Over Y) ⟶ B) : ∃ l : 𝟙_ (Over X) ⟶ A, l.left ≫ φ = f ≫ e.left := by
  refine ⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩
  simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W`. Take `⟨hNc, hGen⟩` from `hNum`. Establish `hN'c : (N' : ℕ) = S.N₀ * (c * t)` using `by rw [hN't, hNc, _root_.mul_assoc]`. Establish `h3 : 3 ≤ S.N₀` using `S.std.three`. Establish `hcq : S.N₀.Coprime q` using `S.std.cop`.

Establish `hNpos : 0 < (N : ℕ)` using `by have := N.2.1; omega`. Establish `hN'pos : 0 < (N' : ℕ)` using `by have := N'.2.1; omega`. Establish `e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E)`. Rewrite using `[Category.assoc, S.ov, C'.ov]`. Take `⟨o₁, ⟨n₁⟩⟩` from `qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0`.

Take `⟨o₂, ⟨n₂⟩⟩` from `qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0`. Take `⟨ψ₀, hψ₀, hiso, htj⟩` from `hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c hN'c hNc W _ o₁ o₂ n₁ n₂`. Take `⟨x1q, hx1q⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ`. Take `⟨x1c, hx1c⟩` from `qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q`. Take `⟨x1, hx1⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1 inferInstance n₁ x1c`.

Establish `hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤))`. Establish `hqE : IsUnit (q : E)` using `(Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit`. Simplify using `using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)`. Take `⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩` from `Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj`. Take `⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀` from `⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩`.

Take `⟨n'c, hn'c⟩` from `qcast hys.symm C'.m`. Take `⟨mm, hmm⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms`. Take `⟨q1, hq1⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁`. Take `⟨q1c, hq1c⟩` from `qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1`. Take `⟨q2, hq2⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'`.

Take `⟨q3, hq3⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt`. Take `⟨qC, hqC⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2 _ _ W.o W.π W.φ C.m`. Take `⟨A1, hA1⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀`. Take `⟨B1, hB1⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀`. Take `⟨B1c, hB1c⟩` from `qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1`.

Establish `I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ`. Rewrite using `[← hA1, ← hB1, ← hB1c]`. Conclude with `hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c`. Establish `I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ`. Apply `Lj.m'.cart.1.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc]`. Rewrite using `[← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]`. Simplify using `only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]`. Rewrite using `[← Category.assoc (Over.Hom.left W.ψ), Over.w]`. Establish `hIu : Integ L u` using `integ_of_mem ((hLev u).mp hu).1`.

Establish `hCu : CongId L S.𝔞 u`. Establish `h1` using `((hLev u).mp hu).2`. Rewrite `h1` using `[S.lev]`. Conclude with `((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2`. Establish `hCh : CongId L S.𝔞 h` using `hTj.other S.𝔞 S.sup S.upow`.

Establish `hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) = inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v`. Introduce `y'`. Take `⟨v₁, hv₁, e₁⟩` from `((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'`. Take `⟨v₂, hv₂, e₂⟩` from `((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'`. Use `⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, Module.End.mul_apply, e₂, map_add, map_nsmul, e₁, smul_add, add_assoc]`. Establish `I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left → ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left`. Introduce `y' l' hl'`. Establish `hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y')`. Rewrite using `[map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]`.

Apply `Lj.ms.cart.1.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`. Rewrite using `[← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]`. Simplify using `only [Category.assoc]`. Rewrite using `[mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']`.

Simplify using the standard rewrite rules. Establish `I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ = (y ≫ Lj.t) ≫ (S.Y.lv y').left`. Introduce `y'`. Take `⟨l', hl'⟩` from `sec_lift Lj.ms.cart.1 (S.Y.lv y')`. Establish `hTE` using `hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't (_root_.mul_one _).symm _ _ (hx y')`.

Rewrite `hTE` using `[one_smul]`. Establish `hlv` using `Lj.lev y' l' hl'`. Rewrite `hlv` using `[Over.comp_left, Category.assoc]`. Rewrite using `[← hTE, Over.comp_left, hq3]`. Simplify using `only [Category.assoc]`.

Rewrite using `[← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]`. Take `⟨l, hlev, hl⟩` from `hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂`. Take `⟨f₀, -, huniq⟩` from `S.Y.rep _ _ o₂ l hlev`. Take `⟨q3c, hq3c⟩` from `qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3`. Take `⟨μ2, hμ2⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1 inferInstance n₂ q3c`.

Take `⟨qCc, hqCc⟩` from `qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC`. Take `⟨μ1, hμ1⟩` from `(hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1 inferInstance n₂ qCc`. Establish `base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s`. Simplify using `only [Category.assoc]`. Rewrite using `[← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]`.

Establish `base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s`. Rewrite using `[e0, Category.assoc, C.ov, reassoc_of% W.ov]`. Establish `eq2` using `huniq _ ⟨base2, μ2, fun y' => by`. Rewrite using `[← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩`. Establish `eq1` using `huniq _ ⟨base1, μ1, fun y' => by`.

Rewrite using `[← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]`. Use `erw [W.φ.eta]`. Rewrite using `[Category.assoc, C.lv, Category.assoc]⟩`. Establish `yt : y ≫ Lj.t = W.π ≫ C.j` using `eq2.trans eq1.symm`. Take `⟨q3y, hq3y⟩` from `qcast yt q3`.

Use `⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hmm, hn'c]`. Rewrite using `[reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]`.
-/
theorem UpperTheory.hecke_lift_exists_of_quotient_level :
    NumEx → QObj → QComp → QUniq → QLev → TjIsog → TrEta → CongCRT → LiftEx := by
  intro hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W
  obtain ⟨hNc, hGen⟩ := hNum
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, S.ov, C'.ov]
  obtain ⟨o₁, ⟨n₁⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0
  obtain ⟨o₂, ⟨n₂⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0
  obtain ⟨ψ₀, hψ₀, hiso, htj⟩ := hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c
    hN'c hNc W _ o₁ o₂ n₁ n₂
  obtain ⟨x1q, hx1q⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ
  obtain ⟨x1c, hx1c⟩ := qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q
  obtain ⟨x1, hx1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1
    inferInstance n₁ x1c
  have hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤)) := by
    have hqE : IsUnit (q : E) := (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit
    simpa using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)
  obtain ⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩ := Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj
  obtain ⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀ :=
    ⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩
  obtain ⟨n'c, hn'c⟩ := qcast hys.symm C'.m
  obtain ⟨mm, hmm⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms
  obtain ⟨q1, hq1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁
  obtain ⟨q1c, hq1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1
  obtain ⟨q2, hq2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'
  obtain ⟨q3, hq3⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨A1, hA1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀
  obtain ⟨B1, hB1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀
  obtain ⟨B1c, hB1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1
  have I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ := by
    rw [← hA1, ← hB1, ← hB1c]
    exact hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c
  have I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ := by
    apply Lj.m'.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]
    · simp only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]
      rw [← Category.assoc (Over.Hom.left W.ψ), Over.w]
  have hIu : Integ L u := integ_of_mem ((hLev u).mp hu).1
  have hCu : CongId L S.𝔞 u := by
    have h1 := ((hLev u).mp hu).2
    rw [S.lev] at h1
    exact ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2
  have hCh : CongId L S.𝔞 h := hTj.other S.𝔞 S.sup S.upow
  have hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) =
      inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v := by
    intro y'
    obtain ⟨v₁, hv₁, e₁⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'
    obtain ⟨v₂, hv₂, e₂⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'
    refine ⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩
    rw [map_mul, Module.End.mul_apply, e₂, map_add, map_nsmul, e₁, smul_add, add_assoc]
  have I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left →
      ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left := by
    intro y' l' hl'
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y') := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    apply Lj.ms.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]
    · simp only [Category.assoc]
      rw [mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']
      simp
  have I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ =
      (y ≫ Lj.t) ≫ (S.Y.lv y').left := by
    intro y'
    obtain ⟨l', hl'⟩ := sec_lift Lj.ms.cart.1 (S.Y.lv y')
    have hTE := hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ (hx y')
    rw [one_smul] at hTE
    have hlv := Lj.lev y' l' hl'
    rw [Over.comp_left, Category.assoc] at hlv
    rw [← hTE, Over.comp_left, hq3]
    simp only [Category.assoc]
    rw [← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]
  obtain ⟨l, hlev, hl⟩ := hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂
  obtain ⟨f₀, -, huniq⟩ := S.Y.rep _ _ o₂ l hlev
  obtain ⟨q3c, hq3c⟩ := qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3
  obtain ⟨μ2, hμ2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1
    inferInstance n₂ q3c
  obtain ⟨qCc, hqCc⟩ := qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC
  obtain ⟨μ1, hμ1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1
    inferInstance n₂ qCc
  have base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    simp only [Category.assoc]
    rw [← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]
  have base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    rw [e0, Category.assoc, C.ov, reassoc_of% W.ov]
  have eq2 := huniq _ ⟨base2, μ2, fun y' => by
    rw [← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩
  have eq1 := huniq _ ⟨base1, μ1, fun y' => by
    rw [← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]⟩
  have yt : y ≫ Lj.t = W.π ≫ C.j := eq2.trans eq1.symm
  obtain ⟨q3y, hq3y⟩ := qcast yt q3
  refine ⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩
  · rw [← hmm, hn'c]
  · rw [reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]
