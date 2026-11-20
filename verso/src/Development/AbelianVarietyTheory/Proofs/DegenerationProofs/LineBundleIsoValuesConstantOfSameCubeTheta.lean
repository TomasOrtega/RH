import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.IsoValConst
open GlobalTheory.TorusExt GlobalTheory.ArcTransport

/- English proof (translation)
Take `⟨h, hh⟩ : ∃ h : A → U, ∀ x, h x = Ω x / Ω 1` from `⟨_, fun _ => rfl⟩`. Establish `h1 : h 1 = 1` using `by rw [hh, div_self']`. Set `B : A → A →* U` to `fun z => MonoidHom.mk' (fun x => h (x * z) / (h x * h z)) fun x y => by`. Establish `e` using `congrArg Additive.ofMul (hc x y z)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [hh, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one] at e ⊢`. Take the linear combination `(norm := abel) e`. Establish `hB : ∀ z x, B z x = h (x * z) / (h x * h z)` using `fun _ _ => rfl`. Establish `sy : ∀ z x, B z x = B x z` using `fun z x => by rw [hB, hB, mul_comm x, mul_comm (h x)]`. Establish `tors : ∀ t, t ^ n = 1 → ∀ a, h (a * t) = h a * h t` using `fun t ht a => by`.

Take `⟨b, rfl⟩` from `hd a`. Rewrite using `[← div_eq_one, ← hB, map_pow, sy, ← map_pow, ht, map_one]`. Establish `pw : ∀ t, (∀ a, h (a * t) = h a * h t) → ∀ k : ℕ, h (t ^ k) = h t ^ k` using `fun t ht k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, h1]`.

Consider the case `succ k ih => rw [pow_succ, pow_succ, ht, ih]`. Establish `key : ∀ a t, t ^ n = 1 → h (a * t) ^ n = h a ^ n` using `fun a t ht => by`. Rewrite using `[tors t ht, mul_pow, ← pw t (tors t ht), ht, h1, _root_.mul_one]`. Establish `kill : ∀ a, h a ^ n = 1` using `fun a => by`. Take `⟨t, ht, p⟩` from `hg a`.

Take `⟨s, hs, q⟩` from `hg 1`. Rewrite using `[← key a t ht, hh, hP _ _ p q, ← hh, key 1 s hs, h1, one_pow]`. Establish `mul : ∀ t a, h (a * t) = h a * h t` using `fun t a => by`. Take `⟨b, rfl⟩` from `hd a`. Rewrite using `[← div_eq_one, ← hB, map_pow, hB, div_pow, mul_pow, kill, kill, kill, _root_.mul_one, div_one]`.

Take `⟨y, rfl⟩` from `hd x`. Rewrite using `[← div_eq_one, ← hh, pw y (mul y), kill]`.
-/
theorem const_of_cube {A U : Type} [CommGroup A] [CommGroup U] (Ω : A → U)
    (hc : ∀ a b c, Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ = 1)
    (P : A → Prop) (hP : ∀ a b, P a → P b → Ω a = Ω b) (n : ℕ) (hd : ∀ x : A, ∃ y, y ^ n = x)
    (hg : ∀ a : A, ∃ t, t ^ n = 1 ∧ P (a * t)) (x : A) : Ω x = Ω 1 := by
  obtain ⟨h, hh⟩ : ∃ h : A → U, ∀ x, h x = Ω x / Ω 1 := ⟨_, fun _ => rfl⟩
  have h1 : h 1 = 1 := by rw [hh, div_self']
  let B : A → A →* U := fun z => MonoidHom.mk' (fun x => h (x * z) / (h x * h z)) fun x y => by
    have e := congrArg Additive.ofMul (hc x y z)
    apply Additive.ofMul.injective
    simp only [hh, ofMul_mul, ofMul_div, ofMul_inv, ofMul_one] at e ⊢
    linear_combination (norm := abel) e
  have hB : ∀ z x, B z x = h (x * z) / (h x * h z) := fun _ _ => rfl
  have sy : ∀ z x, B z x = B x z := fun z x => by rw [hB, hB, mul_comm x, mul_comm (h x)]
  have tors : ∀ t, t ^ n = 1 → ∀ a, h (a * t) = h a * h t := fun t ht a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, sy, ← map_pow, ht, map_one]
  have pw : ∀ t, (∀ a, h (a * t) = h a * h t) → ∀ k : ℕ, h (t ^ k) = h t ^ k := fun t ht k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ k ih => rw [pow_succ, pow_succ, ht, ih]
  have key : ∀ a t, t ^ n = 1 → h (a * t) ^ n = h a ^ n := fun a t ht => by
    rw [tors t ht, mul_pow, ← pw t (tors t ht), ht, h1, _root_.mul_one]
  have kill : ∀ a, h a ^ n = 1 := fun a => by
    obtain ⟨t, ht, p⟩ := hg a
    obtain ⟨s, hs, q⟩ := hg 1
    rw [← key a t ht, hh, hP _ _ p q, ← hh, key 1 s hs, h1, one_pow]
  have mul : ∀ t a, h (a * t) = h a * h t := fun t a => by
    obtain ⟨b, rfl⟩ := hd a
    rw [← div_eq_one, ← hB, map_pow, hB, div_pow, mul_pow, kill, kill, kill, _root_.mul_one, div_one]
  obtain ⟨y, rfl⟩ := hd x
  rw [← div_eq_one, ← hh, pw y (mul y), kill]

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
The claim follows from `((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm`.
-/
theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

/- English proof (translation)
The claim follows from `(gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm`.
-/
theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm
end Val

/- English proof (translation)
Establish `le : ∀ p : (PUnit → L.ι) × (PUnit → L'.ι), (L.pull (h ≫ Φ)).U p.1 ⊓ (L'.pull h).U p.2 ≤ h ⁻¹ᵁ ((L.pull Φ).U p.1 ⊓ L'.U (p.2 PUnit.unit))` using `fun p y hy => ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (h ≫ Φ)).U p.1 from hy.1) :), mem_pull.1 hy.2⟩`. Set `w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ))` to `⟨fun p => res (le p) (pullU h _ (w.s (p.1, p.2 PUnit.unit)))⟩`. Establish `v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j (k : PUnit → L'.ι), Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U (k PUnit.unit) → gw w' r z j k = gw w (r ≫ h) z j (k PUnit.unit)` using `fun Z r z j k hj hk =>`. Establish `m : r z ∈ (L.pull (h ≫ Φ)).U (fun _ => j) ⊓ (L'.pull h).U k` using `⟨mem_pull.2 hj, mem_pull.2 hk⟩`. Use the proof step `(gm_res r z (le (fun _ => j, k)) m _).trans (gm_pull r h z _ (le (fun _ => j, k) m) _)`.

Use `⟨w', (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k => v Z r z j fun _ => k⟩` and prove the remaining obligations. Rewrite using `[v Z r z j k hj (mem_pull.1 hk), v Z r z j' k' hj' (mem_pull.1 hk'), gm_pull_g L' h r z k k' hk hk', ← Category.assoc]`. Conclude with `(isGen_iff _).1 hw Z (r ≫ h) z j j' _ _ hj hj' (mem_pull.1 hk :) (mem_pull.1 hk' :)`.
-/
theorem exists_iso_pull {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {w : LB.Iso L' (L.pull Φ)}
    (hw : w.IsGen) (h : Y ⟶ X') : ∃ w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U k →
        gw w' r z j (fun _ => k) = gw w (r ≫ h) z j k := by
  have le : ∀ p : (PUnit → L.ι) × (PUnit → L'.ι), (L.pull (h ≫ Φ)).U p.1 ⊓ (L'.pull h).U p.2 ≤
      h ⁻¹ᵁ ((L.pull Φ).U p.1 ⊓ L'.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (h ≫ Φ)).U p.1 from hy.1) :), mem_pull.1 hy.2⟩
  let w' : LB.Iso (L'.pull h) (L.pull (h ≫ Φ)) := ⟨fun p => res (le p) (pullU h _ (w.s (p.1, p.2 PUnit.unit)))⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j (k : PUnit → L'.ι), Φ (h (r z)) ∈ L.U j → h (r z) ∈ L'.U (k PUnit.unit) →
      gw w' r z j k = gw w (r ≫ h) z j (k PUnit.unit) := fun Z r z j k hj hk =>
    have m : r z ∈ (L.pull (h ≫ Φ)).U (fun _ => j) ⊓ (L'.pull h).U k := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
    (gm_res r z (le (fun _ => j, k)) m _).trans (gm_pull r h z _ (le (fun _ => j, k) m) _)
  refine ⟨w', (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k => v Z r z j fun _ => k⟩
  rw [v Z r z j k hj (mem_pull.1 hk), v Z r z j' k' hj' (mem_pull.1 hk'), gm_pull_g L' h r z k k' hk hk',
    ← Category.assoc]
  exact (isGen_iff _).1 hw Z (r ≫ h) z j j' _ _ hj hj' (mem_pull.1 hk :) (mem_pull.1 hk' :)

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

/- English proof (translation)
Introduce `ψ` and use `ν.good ψ trivial`.
-/
theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

/- English proof (translation)
The claim follows from `Units.ext ((congrArg (stalkConst z) (ν.θ_eq x y u)).trans (const_vF _ _ (good ν z)))`.
-/
theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  Units.ext ((congrArg (stalkConst z) (ν.θ_eq x y u)).trans (const_vF _ _ (good ν z)))

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun x => (congrArg _ (const_vF _ _ (good ν z)).symm).trans ((map_mul _ _ _).symm.trans ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))⟩`.
-/
theorem stalk_th : ∃ ρ : ((Sp F).presheaf.stalk z)ˣ, ∀ x : N.A,
    stalkConst z (N.th x) * ρ.val = sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  ⟨_, fun x => (congrArg _ (const_vF _ _ (good ν z)).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `ν.th_gen s`. Use `⟨gs (Y := Sp F) (TF (R := R) F).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r), fun x => ?_⟩` and prove the remaining obligations. Establish `m` using `(good ν z).mem (fun _ : Fin 1 => 𝟙 D.P.A.left) (show Sp F ⟶ _ from x.left)`. Use `(congrArg (gs _ z _) (hr _)).trans ((gs_mul _ z _ m _ _).trans (congrArg₂ (· * ·) ?_ rfl))` and prove the remaining obligations. Use `(gs_res _ z le_top m _).trans ?_` and prove the remaining obligations.

Rewrite using `[← Over.w x]`. Conclude with `gs_pull (show Sp F ⟶ _ from x.left) D.P.A.hom z ⊤ trivial _`.
-/
theorem sval_eq (s : H0 D.P.L 1) : ∃ κ : (Sp F).presheaf.stalk z, ∀ x : TF (R := R) F ⟶ D.P.A,
    sval (Z := Sp F) s x.left z ν.J = κ * sval (Z := Sp F) ν.th x.left z ν.J := by
  obtain ⟨r, hr⟩ := ν.th_gen s
  refine ⟨gs (Y := Sp F) (TF (R := R) F).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r), fun x => ?_⟩
  have m := (good ν z).mem (fun _ : Fin 1 => 𝟙 D.P.A.left) (show Sp F ⟶ _ from x.left)
  refine (congrArg (gs _ z _) (hr _)).trans ((gs_mul _ z _ m _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  refine (gs_res _ z le_top m _).trans ?_
  rw [← Over.w x]
  exact gs_pull (show Sp F ⟶ _ from x.left) D.P.A.hom z ⊤ trivial _
end Num

/- English proof (translation)
Introduce `hL R R' _ _ _ _ f D D' F _ _ _ N k β u ν ν' φ w gp hw he n hd hg`. Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Establish `hJ'` using `good ν' z`. Establish `hT : (TF (R` using `R) F).hom ≫ spMap f = (TF (R := R') F).hom := by`.

Rewrite using `[← Over.w (ν.eA 1), ← Over.w (ν'.eA 1), Category.assoc]`. Conclude with `(congrArg _ gp.1.w.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D'.P.A.hom) (he 1)))`. Establish `hp : ∀ x : N.A, pushF gp hT (ν.eA x) = ν'.eA x` using `fun x => Over.OverMorphism.ext (he x)`. Set `Ω : N.A → ((Sp F).presheaf.stalk z)ˣ` to `fun x => wVal w z ν'.J ν.J (ν.eA x)`. Establish `em : ∀ a b : N.A, ν.eA (a * b) = ν.eA a * ν.eA b` using `fun a b => map_mul ν.eA a b`.

Establish `e1 : ν.eA (1 : N.A) = 1` using `map_one ν.eA`. Establish `hΩ : ∀ x, Ω x = Ω 1`. Use `const_of_cube Ω (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ n hd hg` and prove the remaining obligations. Establish `e` using `thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ' hJ (ν.eA a) (ν.eA b) (ν.eA c)`. Rewrite `e` using `[hp, hp, hp, ← em, ← em, ← em, ← em, ← e1]`.

Conclude with `mul_eq_right.1 (e.symm.trans ((stalk_θ ν' z a b c).symm.trans (stalk_θ ν z a b c)))`. Take `⟨s, hs⟩` from `ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (φ := fun _ : Fin 1 => 𝟙 D'.P.A.left) (h := φ) hw D'.P.isLB D.P.isLB (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν'.th`. Take `⟨κ, hκ⟩` from `sval_eq ν z s`. Take `⟨ρ, hρ⟩` from `stalk_th ν z`. Take `⟨ρ', hρ'⟩` from `stalk_th ν' z`.

Establish `key : ∀ a : N.A, N.th a ≠ 0 → ρ'.val = (Ω a).val * (κ * ρ.val)` using `fun a ha => by`. Establish `e` using `hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) (show Sp F ⟶ _ from (ν.eA a).left) hJ' hJ`. Rewrite `e` using `[Fin.prod_univ_one, Category.comp_id]`. Use `replace e := e.trans (congrArg (fun q : ((Sp F).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))`. Establish `e' : stalkConst z (N.th a) * ρ'.val = (Ω a).val * (κ * (stalkConst z (N.th a) * ρ.val))` using `(hρ' a).trans ((congrArg (fun q => sval (Z := Sp F) ν'.th q z ν'.J) (he a).symm).trans (e.trans (congrArg _ ((hκ _).trans (congrArg _ (hρ a).symm)))))`.

Use `((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `a b ha hb`. Establish `hu : IsUnit (κ * ρ.val)` using `isUnit_of_mul_isUnit_right (key a ha ▸ ρ'.isUnit)`. Conclude with `Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))`.

Take `⟨w', hw', hv⟩` from `exists_iso_pull hw (snd (TF (R := R) F) D.P.A).left`. Use `⟨w', (stalkUnits z).symm (Ω 1), hw', fun x => (stalkConst z).injective ?_⟩` and prove the remaining obligations. Establish `l : (lift (𝟙 (TF (R` using `R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by`. Rewrite using `[← Over.comp_left, lift_snd]`. Establish `m₁ : ((lift (𝟙 (TF (R` using `R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈ D.P.L.U (ν.J (ν.eA x).left) := by rw [l]; exact hJ _`.

Establish `m₂ : (((lift (𝟙 (TF (R` using `R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) ≫ φ) z ∈ D'.P.L.U (ν'.J (ν'.eA x).left) := by rw [l, he]; exact hJ' _`. Use `(toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ((D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ)).U (fun _ => ν'.J (ν'.eA x).left) ⊓ (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_` and prove the remaining obligations. Rewrite using `[← stalkUnits_val, MulEquiv.apply_symm_apply, ← hΩ x]`. Use `congrArg Units.val ((hv (Sp F) _ z _ _ m₂ m₁).trans ?_)` and prove the remaining obligations. Rewrite using `[l, ← he]`.

Both sides reduce to the same expression.
-/
theorem exists_iso_val_const : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (f : R' →+* R) (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N : NumD F) (k : ℕ) (β : N.Form k) (u : Fˣ) (ν : NumOf D F (N.twist β u)) (ν' : NumOf D' F N) (φ : D.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D.P.L (D'.P.L.pull φ)), IsGrpPullback D.P.A D'.P.A (spMap f) φ → w.IsGen → (∀ x, (ν.eA x).left ≫ φ = (ν'.eA x).left) → ∀ n : ℕ, (∀ x : N.A, ∃ y, y ^ n = x) → (∀ a : N.A, ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0) → ∃ (w' : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ))) (c : Fˣ), w'.IsGen ∧ ∀ x, valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w'.s (fun _ => ν'.J (ν'.eA x).left, fun _ => ν.J (ν.eA x).left)).val = c := by
  intro hL R R' _ _ _ _ f D D' F _ _ _ N k β u ν ν' φ w gp hw he n hd hg
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) F).hom ≫ spMap f = (TF (R := R') F).hom := by
    rw [← Over.w (ν.eA 1), ← Over.w (ν'.eA 1), Category.assoc]
    exact (congrArg _ gp.1.w.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D'.P.A.hom) (he 1)))
  have hp : ∀ x : N.A, pushF gp hT (ν.eA x) = ν'.eA x := fun x => Over.OverMorphism.ext (he x)
  let Ω : N.A → ((Sp F).presheaf.stalk z)ˣ := fun x => wVal w z ν'.J ν.J (ν.eA x)
  have em : ∀ a b : N.A, ν.eA (a * b) = ν.eA a * ν.eA b := fun a b => map_mul ν.eA a b
  have e1 : ν.eA (1 : N.A) = 1 := map_one ν.eA
  have hΩ : ∀ x, Ω x = Ω 1 := by
    refine const_of_cube Ω (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ n hd hg
    · have e := thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ' hJ (ν.eA a) (ν.eA b) (ν.eA c)
      rw [hp, hp, hp, ← em, ← em, ← em, ← em, ← e1] at e
      exact mul_eq_right.1 (e.symm.trans ((stalk_θ ν' z a b c).symm.trans (stalk_θ ν z a b c)))
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D'.P.A.left) (h := φ) hw D'.P.isLB D.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν'.th
      obtain ⟨κ, hκ⟩ := sval_eq ν z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 → ρ'.val = (Ω a).val * (κ * ρ.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp F ⟶ _ from (ν.eA a).left) hJ' hJ
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp F).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ'.val = (Ω a).val * (κ * (stalkConst z (N.th a) * ρ.val)) :=
          (hρ' a).trans ((congrArg (fun q => sval (Z := Sp F) ν'.th q z ν'.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ a).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        ring
      intro a b ha hb
      have hu : IsUnit (κ * ρ.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ'.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
  obtain ⟨w', hw', hv⟩ := exists_iso_pull hw (snd (TF (R := R) F) D.P.A).left
  refine ⟨w', (stalkUnits z).symm (Ω 1), hw', fun x => (stalkConst z).injective ?_⟩
  have l : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [l]; exact hJ _
  have m₂ : (((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) ≫ φ) z ∈
      D'.P.L.U (ν'.J (ν'.eA x).left) := by rw [l, he]; exact hJ' _
  refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
    ((D'.P.L.pull ((snd (TF (R := R) F) D.P.A).left ≫ φ)).U (fun _ => ν'.J (ν'.eA x).left) ⊓
      (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply, ← hΩ x]
  refine congrArg Units.val ((hv (Sp F) _ z _ _ m₂ m₁).trans ?_)
  rw [l, ← he]
  rfl

end GlobalTheory.IsoValConst
end
