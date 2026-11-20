import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionSquareOfAxesTrivial
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTLevelLift

/- English proof (translation)
Use `haveI : Smooth A.hom := hA.smooth`. Establish `hn' : IsUnit (n : Γ(Sp C, ⊤))`. Simplify using `using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom`. Use `haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'`. Set `T' : Over (Sp C₀)` to `𝟙_ (Over (Sp C₀))`.

Set `T : Over (Sp C)` to `Over.mk (T'.hom ≫ spMap π)`. Establish `hwi : i ≫ A.hom = A₀.hom ≫ spMap π` using `hpb.1.w`. Establish `hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom`. Introduce `x`. Rewrite using `[Category.assoc, hwi, ← Category.assoc, Over.w x]`.

Both sides reduce to the same expression. Set `pt : (T' ⟶ A₀) → (T ⟶ A)` to `fun x => Over.homMk (x.left ≫ i) (hpt x)`. Establish `hone : pt 1 = 1`. Establish `h` using `hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl`. Rewrite `h` using `[_root_.mul_one]`.

Establish `h2 : pt 1 * pt 1 = pt 1` using `Over.OverMorphism.ext h`. Conclude with `mul_eq_left.mp h2`. Establish `hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => rw [pow_zero, pow_zero, hone]`. Consider the case `succ m ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)`. Establish `hx : (pt s₀) ^ n = 1` using `by rw [hpow, hs₀, hone]`.

Set `f : A.left ⟶ A.left` to `(𝟙 A ^ n).left`. Establish `hf : ∀ {Y : Over (Sp C)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left`. Introduce `Y y`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Establish `hone' : ∀ {Y : Over (Sp C)}, ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left`.

Introduce `Y`. Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`. Establish `hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left`. Use `hf (pt s₀)` as an intermediate fact.

Rewrite `this` using `[hx, hone']`. Simplify `this` using `[pt, T, T']`. Take `⟨l, ⟨hl1, hl2⟩, huniq⟩` from `GlobalTheory.existsUnique_lift_of_etale_of_surjective f (CommRingCat.ofHom π) hπ hnil (s₀.left ≫ i) _ hw`. Establish `hls : l ≫ A.hom = (𝟙_ (Over (Sp C))).hom`. Establish `e : f ≫ A.hom = A.hom` using `Over.w (𝟙 A ^ n)`.

Rewrite using `[← e, ← Category.assoc, hl2]`. Conclude with `Over.w (η[A] : 𝟙_ (Over (Sp C)) ⟶ A)`. Set `s : 𝟙_ (Over (Sp C)) ⟶ A` to `Over.homMk l hls`. Establish `hsn : ∀ s' : 𝟙_ (Over (Sp C)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left`. Introduce `s'`.

Establish `e1 : ((1 : 𝟙_ (Over (Sp C)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left`. Rewrite using `[hone']`. Conclude with `Category.id_comp _`. Rewrite using `[hf]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h, e1]`. Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h, e1]`.

Use `⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `s' ⟨h1, h2⟩`. Conclude with `Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)`.
-/
theorem existsUnique_torsion_lift_thick (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) (n : ℕ) (hn : IsUnit (n : C))
    (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A]
    (i : A₀.left ⟶ A.left) (hA : IsAbelianScheme A) (hpb : IsGrpPullback A₀ A (spMap π) i)
    (s₀ : 𝟙_ (Over (Sp C₀)) ⟶ A₀) (hs₀ : s₀ ^ n = 1) :
    ∃! s : 𝟙_ (Over (Sp C)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp C₀) := 𝟙_ (Over (Sp C₀))
  let T : Over (Sp C) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp C)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp C)}, ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_surjective f (CommRingCat.ofHom π) hπ hnil (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp C))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp C)) ⟶ A)
  let s : 𝟙_ (Over (Sp C)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp C)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp C)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `mul_eq_left.mp h.symm`. Consider the case `succ n ih => rw [succ_nsmul, hf, ih, pow_succ]`.
-/
theorem map_nsmul_pow {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ x y, f (x + y) = f x * f y)
    (n : ℕ) (x : La) : f (n • x) = f x ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

/- English proof (translation)
Introduce `p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hN P φ₂ hP hsqr hLB`. Establish `hnil : IsNilpotent (RingHom.ker π)` using `⟨2, hsq⟩`. Establish `hNu : IsUnit (N : C)` using `by simpa using (b.unit N hN).map tR`. Establish `hlift` using `fun y => existsUnique_torsion_lift_thick C C₀ π hπ hnil N hNu o₀.A A i hA h (o₀.eta y) (by rw [← map_nsmul_pow o₀.eta o₀.eta_add, o₀.eta_ker])`. Use `choose eta hspec huniq using hlift`.

Set `TT : Over (Sp C)` to `Over.mk ((𝟙_ (Over (Sp C₀))).hom ≫ spMap π)`. Set `u : TT ⟶ 𝟙_ (Over (Sp C))` to `toUnit TT`. Establish `hu : u.left = spMap π` using `by simpa [TT] using Over.w u`. Establish `hcomp : ∀ s : 𝟙_ (Over (Sp C)) ⟶ A, (u ≫ s).left = spMap π ≫ s.left` using `fun s => by`. Rewrite using `[Over.comp_left, hu]`.

Establish `hadd : ∀ x y, eta (x + y) = eta x * eta y`. Introduce `x y`. Use `(huniq (x + y) _ ⟨by rw [mul_pow, (hspec x).1, (hspec y).1, _root_.one_mul], ?_⟩).symm` and prove the remaining obligations. Establish `e` using `h.2 (𝟙_ (Over (Sp C₀))) (o₀.eta x) (o₀.eta y) (u ≫ eta x) (u ≫ eta y) (by rw [hcomp, (hspec x).2]) (by rw [hcomp, (hspec y).2])`. Rewrite using `[o₀.eta_add, ← e, ← MonObj.comp_mul, hcomp]`.

Use `⟨eta, hadd, ?_, ?_, ?_, fun y => (hspec y).2⟩` and prove the remaining obligations. Introduce `c x haveI := act.hom c haveI := o₀.act.hom c`. Use `(huniq (c • x) _ ⟨by rw [← MonObj.pow_comp, (hspec x).1, MonObj.one_comp], ?_⟩).symm` and prove the remaining obligations. Rewrite using `[o₀.eta_lin, Over.comp_left, Category.assoc, hact, ← Category.assoc, (hspec x).2, Over.comp_left, Category.assoc]`. Introduce `x`.

Rewrite using `[map_nsmul_pow eta hadd, (hspec x).1]`. Introduce `k _ _ x β hxβ`. Take `⟨φ, hφx⟩` from `Spec.map_surjective x`. Establish `hker : RingHom.ker π ≤ RingHom.ker φ.hom`. Introduce `a ha`.

Establish `h2 : a * a ∈ RingHom.ker π ^ 2` using `by rw [pow_two]; exact Ideal.mul_mem_mul ha ha`. Rewrite `h2` using `[hsq]`. Establish `h3 : φ.hom (a * a) = 0`. Rewrite using `[show a * a = 0 from h2, map_zero]`. Rewrite using `[RingHom.mem_ker]`.

Rewrite `h3` using `[map_mul]`. Conclude with `mul_self_eq_zero.mp h3`. Set `φ₀ : C₀ →+* k` to `π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨φ.hom, hker⟩`. Establish `hφ : φ₀.comp π = φ.hom` using `RingHom.liftOfRightInverse_comp _ _ _ _`. Establish `hx : x = spMap φ₀ ≫ spMap π`.

Rewrite using `[← hφx]`. Use `show Spec.map φ = Spec.map (CommRingCat.ofHom φ₀) ≫ Spec.map (CommRingCat.ofHom π)`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`.

Simplify using `[← hφ]`. Substitute `hx` using the available equality. Take `⟨I₀, hI₀⟩` from `o₀.geom k (spMap φ₀) β (by rw [← Category.assoc]; exact hxβ)`. Take `⟨e, he⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (spMap φ₀)) (spMap φ₀ ≫ spMap π) rfl`. Establish `hd : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ φ₂ = i ≫ (lift (𝟙 A) (𝟙 A)).left` using `GlobalTheory.AxisTrivExt.lift_match hsqr.1 hsqr.2 (𝟙 o₀.A) (𝟙 o₀.A) (𝟙 A) (𝟙 A) (by simp) (by simp)`.

Establish `a3 : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)` using `GenSpread.lbIso_pullback hLB _`. Establish `b1 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)` using `GenSpread.lbIso_pull_pull hP _ hd.symm`. Establish `b2 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i)` using `GenSpread.lbIso_pull_pull hP i rfl`. Establish `iD : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i)` using `LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) a3 b1.symm) b2`. Establish `lin : ∀ (c : D.O) (g : Over.mk (spMap φ₀) ⟶ o₀.A), e (g ≫ o₀.act.act c) = e g ≫ act.act c` using `fun c g => Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])`.

Use `⟨{ ζ := I₀.ζ ζ_prim := I₀.ζ_prim ζ_pow := I₀.ζ_pow ev := fun n y => e (I₀.ev n y) add := fun n y y' => by simp only [I₀.add, map_mul] lin := fun n c y => by simp only [I₀.lin, lin] ker := fun n hn hp y => by` and prove the remaining obligations. Rewrite using `[← I₀.ker n hn hp y]`. Conclude with `⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩`. Use `onto := fun n hn hp q => by`. Take `⟨q, rfl⟩` from `e.surjective q`.

Rewrite using `[← map_pow]`. Use `Iff.trans ?_ ((I₀.onto n hn hp q).trans ?_)` and prove the remaining obligations. Conclude with `⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩`. Conclude with `⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩`. Use `tower := fun n m hn hm hp y => by rw [← map_pow, I₀.tower n m hn hm hp y]`.

Use `isom := fun n hn hp y y' => (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ A o₀.A (spMap π) i _ _ (pull_isLB hP _) (pull_isLB o₀.isLB _) h iD (Over.mk (spMap φ₀)) n _ _ (e (I₀.ev n y)) (e (I₀.ev n y')) _ (he _) (he _)).1 (I₀.isom n hn hp y y') }, fun y => ?_⟩`. Use `show toUnit _ ≫ eta y = e (I₀.ev N y)`. Rewrite using `[← hI₀ y]`. Establish `e₁ : (toUnit (Over.mk (spMap φ₀))).left = spMap φ₀` using `by simpa using Over.w (toUnit (Over.mk (spMap φ₀)))`. Establish `e₂ : (toUnit (Over.mk (spMap φ₀ ≫ spMap π))).left = spMap φ₀ ≫ spMap π`.

Simplify using `using Over.w (toUnit (Over.mk (spMap φ₀ ≫ spMap π)))`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, Over.comp_left, Over.comp_left, Category.assoc, (hspec y).2, e₁, e₂, Category.assoc]`.
-/
theorem level_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → N.Coprime p → ∀ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB → IsSquare i φ₂ → LBIso o₀.P (P.pull φ₂) → ∃ eta : D.La → (𝟙_ (Over (Sp C)) ⟶ A), (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ (∀ x, eta (N • x) = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∃ I : GlobalTheory.UPel.HT.TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) ∧ ∀ y, (o₀.eta y).left ≫ i = spMap π ≫ (eta y).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hN P φ₂ hP hsqr hLB
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, hsq⟩
  have hNu : IsUnit (N : C) := by simpa using (b.unit N hN).map tR
  have hlift := fun y => existsUnique_torsion_lift_thick C C₀ π hπ hnil N hNu o₀.A A i hA h (o₀.eta y)
      (by rw [← map_nsmul_pow o₀.eta o₀.eta_add, o₀.eta_ker])
  choose eta hspec huniq using hlift
  let TT : Over (Sp C) := Over.mk ((𝟙_ (Over (Sp C₀))).hom ≫ spMap π)
  let u : TT ⟶ 𝟙_ (Over (Sp C)) := toUnit TT
  have hu : u.left = spMap π := by simpa [TT] using Over.w u
  have hcomp : ∀ s : 𝟙_ (Over (Sp C)) ⟶ A, (u ≫ s).left = spMap π ≫ s.left := fun s => by
    rw [Over.comp_left, hu]
  have hadd : ∀ x y, eta (x + y) = eta x * eta y := by
    intro x y
    refine (huniq (x + y) _ ⟨by rw [mul_pow, (hspec x).1, (hspec y).1, _root_.one_mul], ?_⟩).symm
    have e := h.2 (𝟙_ (Over (Sp C₀))) (o₀.eta x) (o₀.eta y) (u ≫ eta x) (u ≫ eta y)
      (by rw [hcomp, (hspec x).2]) (by rw [hcomp, (hspec y).2])
    rw [o₀.eta_add, ← e, ← MonObj.comp_mul, hcomp]
  refine ⟨eta, hadd, ?_, ?_, ?_, fun y => (hspec y).2⟩
  · intro c x
    haveI := act.hom c
    haveI := o₀.act.hom c
    refine (huniq (c • x) _ ⟨by rw [← MonObj.pow_comp, (hspec x).1, MonObj.one_comp], ?_⟩).symm
    rw [o₀.eta_lin, Over.comp_left, Category.assoc, hact, ← Category.assoc, (hspec x).2, Over.comp_left,
      Category.assoc]
  · intro x
    rw [map_nsmul_pow eta hadd, (hspec x).1]
  · intro k _ _ x β hxβ
    obtain ⟨φ, hφx⟩ := Spec.map_surjective x
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := by
      intro a ha
      have h2 : a * a ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha ha
      rw [hsq] at h2
      have h3 : φ.hom (a * a) = 0 := by
        rw [show a * a = 0 from h2, map_zero]
      rw [RingHom.mem_ker]
      rw [map_mul] at h3
      exact mul_self_eq_zero.mp h3
    let φ₀ : C₀ →+* k := π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨φ.hom, hker⟩
    have hφ : φ₀.comp π = φ.hom := RingHom.liftOfRightInverse_comp _ _ _ _
    have hx : x = spMap φ₀ ≫ spMap π := by
      rw [← hφx]
      show Spec.map φ = Spec.map (CommRingCat.ofHom φ₀) ≫ Spec.map (CommRingCat.ofHom π)
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [← hφ]
    subst hx
    obtain ⟨I₀, hI₀⟩ := o₀.geom k (spMap φ₀) β (by rw [← Category.assoc]; exact hxβ)
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (spMap φ₀)) (spMap φ₀ ≫ spMap π) rfl
    have hd : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ φ₂ = i ≫ (lift (𝟙 A) (𝟙 A)).left :=
      GlobalTheory.AxisTrivExt.lift_match hsqr.1 hsqr.2 (𝟙 o₀.A) (𝟙 o₀.A) (𝟙 A) (𝟙 A) (by simp) (by simp)
    have a3 : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)
        ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pullback hLB _
    have b1 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pull_pull hP _ hd.symm
    have b2 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      GenSpread.lbIso_pull_pull hP i rfl
    have iD : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
        (LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) a3 b1.symm) b2
    have lin : ∀ (c : D.O) (g : Over.mk (spMap φ₀) ⟶ o₀.A), e (g ≫ o₀.act.act c) = e g ≫ act.act c := fun c g =>
      Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    refine ⟨{ ζ := I₀.ζ
              ζ_prim := I₀.ζ_prim
              ζ_pow := I₀.ζ_pow
              ev := fun n y => e (I₀.ev n y)
              add := fun n y y' => by simp only [I₀.add, map_mul]
              lin := fun n c y => by simp only [I₀.lin, lin]
              ker := fun n hn hp y => by
                rw [← I₀.ker n hn hp y]
                exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              onto := fun n hn hp q => by
                obtain ⟨q, rfl⟩ := e.surjective q
                rw [← map_pow]
                refine Iff.trans ?_ ((I₀.onto n hn hp q).trans ?_)
                · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
                · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
              tower := fun n m hn hm hp y => by rw [← map_pow, I₀.tower n m hn hm hp y]
              isom := fun n hn hp y y' =>
                (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ A o₀.A (spMap π) i _ _ (pull_isLB hP _)
                  (pull_isLB o₀.isLB _) h iD (Over.mk (spMap φ₀)) n _ _ (e (I₀.ev n y)) (e (I₀.ev n y')) _
                  (he _) (he _)).1 (I₀.isom n hn hp y y') }, fun y => ?_⟩
    show toUnit _ ≫ eta y = e (I₀.ev N y)
    rw [← hI₀ y]
    have e₁ : (toUnit (Over.mk (spMap φ₀))).left = spMap φ₀ := by simpa using Over.w (toUnit (Over.mk (spMap φ₀)))
    have e₂ : (toUnit (Over.mk (spMap φ₀ ≫ spMap π))).left = spMap φ₀ ≫ spMap π := by
      simpa using Over.w (toUnit (Over.mk (spMap φ₀ ≫ spMap π)))
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, (hspec y).2, e₁, e₂, Category.assoc]

end GlobalTheory.HTLevelLift
