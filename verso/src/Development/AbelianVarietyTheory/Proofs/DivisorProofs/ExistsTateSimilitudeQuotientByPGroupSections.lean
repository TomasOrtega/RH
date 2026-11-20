import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.Hecke.TateQuot

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite `h` using `[Nat.coprime_zero_right]`. Conclude with `⟨1, fun q _ => by rw [h, _root_.one_mul, pow_one]⟩`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Use `⟨(((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val, fun q hq => ?_⟩` and prove the remaining obligations.

Establish `e : (c * (((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val) % n = 1 % n`. Rewrite using `[← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← ZMod.val_one_eq_one_mod]`. Use `congr 1`. Use `(ZMod.unitOfCoprime c h).mul_inv` as an intermediate fact. Rewrite `this` using `[ZMod.coe_unitOfCoprime]`. Then use the resulting hypothesis.

Rewrite using `[pow_eq_pow_mod _ hq, e, ← pow_eq_pow_mod _ hq, pow_one]`.
-/
theorem exists_pow_inv (c n : ℕ) (h : c.Coprime n) :
    ∃ u : ℕ, ∀ {G : Type} [Monoid G] (q : G), q ^ n = 1 → q ^ (c * u) = q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    exact ⟨1, fun q _ => by rw [h, _root_.one_mul, pow_one]⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨(((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val, fun q hq => ?_⟩
  have e : (c * (((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val) % n = 1 % n := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← ZMod.val_one_eq_one_mod]
    congr 1
    have := (ZMod.unitOfCoprime c h).mul_inv
    rwa [ZMod.coe_unitOfCoprime] at this
  rw [pow_eq_pow_mod _ hq, e, ← pow_eq_pow_mod _ hq, pow_one]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.comp_one]`. Consider the case `succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]`.
-/
theorem comp_pow_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T U : Over S} (f : T ⟶ U) (g : U ⟶ A) (m : ℕ) :
    f ≫ g ^ m = (f ≫ g) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

/- English proof (translation)
Introduce `p _ D R _ b N S s o c hc H A' _ _ ψ hA' hψ hGal hHc act' hact P' hP' r₁ r₂ hiso κ _ _ x β hx`. Take `⟨I, hI⟩` from `o.geom κ x β hx`. Take `⟨e₀, rfl⟩` from `hc`. Establish `hcop : ∀ n : ℕ, n.Coprime p → (p ^ e₀).Coprime n` using `fun n hnp => Nat.Coprime.pow_left e₀ hnp.symm`. Set `Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A')` to `MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)`.

Establish `hΨ : ∀ t, Ψ t = t ≫ ψ` using `fun _ => rfl`. Establish `hkill : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 → t ^ (p ^ e₀) = 1`. Introduce `t ht`. Establish `e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]`.

Take `⟨h, hh, -⟩` from `hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm`. Establish `e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1` using `Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)`. Rewrite using `[e2, TateTransl.one_comp_transl_pt, ← comp_pow_pt, hHc h.1 h.2, MonObj.comp_one]`. Establish `hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0` using `fun n hnp => by`. Establish `h` using `(b.unit n hnp).map β`.

Rewrite `h` using `[map_natCast]`. Conclude with `h.ne_zero`. Establish `ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev n y ≫ ψ = 1 ↔ ∃ z, y = n • z`. Introduce `n hn hnp y`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Establish `h2` using `hkill _ h1`. Establish `h3 : I.ev n y ^ n = 1`. Rewrite using `[← TateTransl.ev_nsmul]`. Conclude with `(I.ker n hn hnp _).2 ⟨y, rfl⟩`.

Establish `h4 : I.ev n y ^ (p ^ e₀).gcd n = 1` using `pow_gcd_eq_one.2 ⟨h2, h3⟩`. Rewrite `h4` using `[hcop n hnp, pow_one]`. Conclude with `(I.ker n hn hnp y).1 h4`. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[(I.ker n hn hnp _).2 ⟨z, rfl⟩, MonObj.one_comp]`.

Establish `htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev n y ≫ ψ) ^ n = 1`. Introduce `n hn hnp y`. Rewrite using `[← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul]`. Conclude with `(ker' n hn hnp (n • y)).2 ⟨y, rfl⟩`. Establish `onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev n y ≫ ψ = q`.

Introduce `n hn hnp q`. Prove the components needed by the constructor for the conclusion. Introduce `hq haveI := hGal.fin haveI := hGal.onto`. Take `⟨a₀, ha₀⟩` from `GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left`. Set `a : Over.mk x ⟶ o.A` to `Over.homMk a₀ (by show a₀ ≫ o.A.hom = x`.

Rewrite using `[← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]`. Use the proof step `rfl)`. Establish `ha : a ≫ ψ = q` using `Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)`. Establish `han : (a ^ n) ≫ ψ = 1` using `by rw [← hΨ, map_pow, hΨ, ha, hq]`. Establish `hanc` using `hkill _ han`.

Take `⟨u, hu⟩` from `exists_pow_inv (p ^ e₀) n (hcop n hnp)`. Establish `ha' : (a ^ (p ^ e₀ * u)) ^ n = 1`. Rewrite using `[← pow_mul, show p ^ e₀ * u * n = n * p ^ e₀ * u by ring, pow_mul, pow_mul, hanc, one_pow]`. Take `⟨y, hy⟩` from `(I.onto n hn hnp _).1 ha'`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hy, ← hΨ, map_pow, hΨ, ha, hu q hq]`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `htor n hn hnp y`. Establish `hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e₀)) ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left)`. Use `(GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _), GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]`. Establish `h1` using `(GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso`. Rewrite `h1` using `[GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP']`. Simplify using `only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1`. Establish `h2` using `congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1`.

Rewrite `h2` using `[map_nsmul, ← GlobalTheory.CechPic.pull_comp]`. Rewrite using `[h2]`. Use `congr 1`. Simplify using `only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]`. Use `⟨⟨fun n => I.ζ n ^ (p ^ e₀), fun n hn hnp => (I.ζ_prim n hn hnp).pow_of_coprime _ (hcop n hnp), ?_, fun n y => I.ev n y ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩` and prove the remaining obligations.

Introduce `n m hn hm hnm`. Rewrite using `[← pow_mul, _root_.mul_comm (p ^ e₀) m, pow_mul, I.ζ_pow n m hn hm hnm]`. Introduce `n y y'`. Rewrite using `[I.add, MonObj.mul_comp]`. Introduce `n b' y`.

Rewrite using `[I.lin, Category.assoc, hact, ← Category.assoc]`. Conclude with `fun n hn hnp y => ker' n hn hnp y`. Conclude with `fun n hn hnp q => onto' n hn hnp q`. Introduce `n m hn hm hnm y`. Rewrite using `[← hΨ, ← map_pow, hΨ, I.tower n m hn hm hnm]`.

Introduce `n hn hnp u v`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _ (htor n hn hnp u) (htor n hn hnp v)`. Establish `h3` using `(GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S o.A A' ψ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (P'.pull (lift (𝟙 A') (𝟙 A')).left) (p ^ e₀) n (Over.mk x) (I.ev n u) (I.ev n v) (unitOn (I.ζ n ^ (2 * D.EF u v))) e o.ab hA' (pull_isLB o.isLB _) (pull_isLB hP' _) hψ hi …`. Rewrite `he` using `[h3]`. Use `he using 2` and compare the differences between its conclusion and the goal.

Use `show unitOn ((I.ζ n ^ (p ^ e₀)) ^ (2 * D.EF u v)) = unitOn (I.ζ n ^ (2 * D.EF u v)) ^ (p ^ e₀)`. Rewrite using `[unitOn, unitOn, ← map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`. Use `show toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y ≫ ψ`. Rewrite using `[← Category.assoc, hI]`.
-/
theorem exists_tateIsoO_quot : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ h ∈ H, h ^ c = 1) → ∀ (act' : OActN D.O A'), (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  intro p _ D R _ b N S s o c hc H A' _ _ ψ hA' hψ hGal hHc act' hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  obtain ⟨e₀, rfl⟩ := hc
  have hcop : ∀ n : ℕ, n.Coprime p → (p ^ e₀).Coprime n := fun n hnp => Nat.Coprime.pow_left e₀ hnp.symm
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hkill : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 → t ^ (p ^ e₀) = 1 := by
    intro t ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt, ← comp_pow_pt, hHc h.1 h.2, MonObj.comp_one]
  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev n y ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    constructor
    · intro h1
      have h2 := hkill _ h1
      have h3 : I.ev n y ^ n = 1 := by
        rw [← TateTransl.ev_nsmul]; exact (I.ker n hn hnp _).2 ⟨y, rfl⟩
      have h4 : I.ev n y ^ (p ^ e₀).gcd n = 1 := pow_gcd_eq_one.2 ⟨h2, h3⟩
      rw [hcop n hnp, pow_one] at h4
      exact (I.ker n hn hnp y).1 h4
    · rintro ⟨z, rfl⟩
      rw [(I.ker n hn hnp _).2 ⟨z, rfl⟩, MonObj.one_comp]
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev n y ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev n y ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      have hanc := hkill _ han
      obtain ⟨u, hu⟩ := exists_pow_inv (p ^ e₀) n (hcop n hnp)
      have ha' : (a ^ (p ^ e₀ * u)) ^ n = 1 := by
        rw [← pow_mul, show p ^ e₀ * u * n = n * p ^ e₀ * u by ring, pow_mul, pow_mul, hanc, one_pow]
      obtain ⟨y, hy⟩ := (I.onto n hn hnp _).1 ha'
      refine ⟨y, ?_⟩
      rw [hy, ← hΨ, map_pow, hΨ, ha, hu q hq]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e₀))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨fun n => I.ζ n ^ (p ^ e₀), fun n hn hnp => (I.ζ_prim n hn hnp).pow_of_coprime _ (hcop n hnp), ?_,
    fun n y => I.ev n y ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n m hn hm hnm
    rw [← pow_mul, _root_.mul_comm (p ^ e₀) m, pow_mul, I.ζ_pow n m hn hm hnm]
  · intro n y y'
    rw [I.add, MonObj.mul_comp]
  · intro n b' y
    rw [I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, I.tower n m hn hm hnm]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn
      (hnκ n hnp) _ _ (htor n hn hnp u) (htor n hn hnp v)
    have h3 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S o.A A' ψ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (P'.pull (lift (𝟙 A') (𝟙 A')).left) (p ^ e₀) n (Over.mk x) (I.ev n u) (I.ev n v)
      (unitOn (I.ζ n ^ (2 * D.EF u v))) e o.ab hA' (pull_isLB o.isLB _) (pull_isLB hP' _) hψ hiso2 he).2
      (I.isom n hn hnp u v)
    rw [h3] at he
    convert he using 2
    show unitOn ((I.ζ n ^ (p ^ e₀)) ^ (2 * D.EF u v)) = unitOn (I.ζ n ^ (2 * D.EF u v)) ^ (p ^ e₀)
    rw [unitOn, unitOn, ← map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · show toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateQuot
