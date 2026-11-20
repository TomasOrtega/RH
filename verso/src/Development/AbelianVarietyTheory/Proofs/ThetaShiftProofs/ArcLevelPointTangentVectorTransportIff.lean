import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelTransport

section Val

variable {X X' Z Z' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {R : Type} [CommRing R]

def wv (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (j : L.ι) (j' : L'.ι) : R :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, j')) (w.s (fun _ => j, j')).val

/- English proof (translation)
Introduce `_ hz` and use `⟨mem_pull.2 (hj hz), hj' hz⟩`.
-/
theorem le_div {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') :=
  fun _ hz => ⟨mem_pull.2 (hj hz), hj' hz⟩

/- English proof (translation)
The claim follows from `FormalValue.isUnit_valR x _ (le_div hj hj') _`.
-/
theorem isUnit_wv (w : LB.Iso L' (L.pull F)) {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') : IsUnit (wv w x j j') :=
  FormalValue.isUnit_valR x _ (le_div hj hj') _

/- English proof (translation)
The claim follows from `toStkA_valR x _ z (le_div hj hj') _`.
-/
theorem toStkA_wv (w : LB.Iso L' (L.pull F)) {x : Sp R ⟶ X'} {j : L.ι} {j' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') (z : Sp R) :
    toStkA z (wv w x j j') = (gw w x z j j').val :=
  toStkA_valR x _ z (le_div hj hj') _

def secSub {M : LB X} (a b : M.Sec) : M.Sec where
  f i := a.f i - b.f i
  compat i j := by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

variable [IsLocalRing R]

/- English proof (translation)
The claim follows from `Points.exists_le_preimage_of_iSup_eq_top x hL.cover`.
-/
theorem exists_chart_pt (hL : L.IsLB) (x : Sp R ⟶ X) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j :=
  Points.exists_le_preimage_of_iSup_eq_top x hL.cover

/- English proof (translation)
Apply `toStkA_injective` to reduce the goal to its premises. Establish `t : cpt R ∈ (⊤ : (Sp R).Opens)` using `trivial`. Rewrite using `[map_mul, map_mul, toStkA_wv w hj hj', toStkA_wv w hk hk', toStkA_valR x (L'.U j' ⊓ L'.U k') _ (fun _ hz => ⟨hj' hz, hk' hz⟩), toStkA_valR (x ≫ F) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩), (isGen_iff w).1 hw _ x (cpt R) j k j' k' (hj t) (hk t) (hj' t) (hk' t), ← Units.val_m …`.
-/
theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) {x : Sp R ⟶ X'} {j k : L.ι} {j' k' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U k) (hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j') (hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k') :
    wv w x j j' * valR x (L'.U j' ⊓ L'.U k') (L'.g j' k').val =
      valR (x ≫ F) (L.U j ⊓ L.U k) (L.g j k).val * wv w x k k' := by
  apply toStkA_injective
  have t : cpt R ∈ (⊤ : (Sp R).Opens) := trivial
  rw [map_mul, map_mul, toStkA_wv w hj hj', toStkA_wv w hk hk',
    toStkA_valR x (L'.U j' ⊓ L'.U k') _ (fun _ hz => ⟨hj' hz, hk' hz⟩),
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩),
    (isGen_iff w).1 hw _ x (cpt R) j k j' k' (hj t) (hk t) (hj' t) (hk' t), ← Units.val_mul, ← Units.val_mul,
    mul_right_comm, inv_mul_cancel_right]

/- English proof (translation)
Apply `toStkA_injective` to reduce the goal to its premises. Rewrite using `[toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩), gm_self hL x _ (hj trivial), map_one, Units.val_one]`.
-/
theorem valR_g_self (hL : L.IsLB) {x : Sp R ⟶ X} {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩), gm_self hL x _ (hj trivial), map_one, Units.val_one]

def FrmRel (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (τ : L.ι → R) (τ' : L'.ι → R) : Prop :=
  ∀ j j', ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ x ⁻¹ᵁ L'.U j' → τ j = wv w x j j' * τ' j'

/- English proof (translation)
Take `⟨k', hk'⟩` from `exists_chart_pt hL' x`. Use `⟨fun j => wv w x j k' * τ' k', ⟨fun j hj => (isUnit_wv w hj hk').mul (h.1 k' hk'), fun j k hjk => ?_⟩, fun j j' hj hj' => ?_⟩` and prove the remaining obligations. Establish `e` using `wv_trans hw (fun _ hz => (hjk hz).1) (fun _ hz => (hjk hz).2) hk' hk'`. Rewrite `e` using `[valR_g_self hL' hk', _root_.mul_one]`. Simplify using `only [e, _root_.mul_assoc]`.

Establish `e` using `wv_trans hw hj hj hj' hk'`. Rewrite `e` using `[valR_g_self hL hj, _root_.one_mul]`. Rewrite using `[h.2 j' k' (fun _ hz => ⟨hj' hz, hk' hz⟩), ← _root_.mul_assoc, e]`.
-/
theorem exists_frm_up {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {x : Sp R ⟶ X'}
    {τ' : L'.ι → R} (h : IsFrm L' x τ') : ∃ τ, IsFrm L (x ≫ F) τ ∧ FrmRel w x τ τ' := by
  obtain ⟨k', hk'⟩ := exists_chart_pt hL' x
  refine ⟨fun j => wv w x j k' * τ' k', ⟨fun j hj => (isUnit_wv w hj hk').mul (h.1 k' hk'), fun j k hjk => ?_⟩,
    fun j j' hj hj' => ?_⟩
  · have e := wv_trans hw (fun _ hz => (hjk hz).1) (fun _ hz => (hjk hz).2) hk' hk'
    rw [valR_g_self hL' hk', _root_.mul_one] at e
    simp only [e, _root_.mul_assoc]
  · have e := wv_trans hw hj hj hj' hk'
    rw [valR_g_self hL hj, _root_.one_mul] at e
    rw [h.2 j' k' (fun _ hz => ⟨hj' hz, hk' hz⟩), ← _root_.mul_assoc, e]

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_chart_pt hL (x ≫ F)`. Establish `hi : ∀ j', ⊤ ≤ x ⁻¹ᵁ L'.U j' → wv w x k j' * (Ring.inverse (wv w x k j') * τ k) = τ k` using `fun j' hj' => by`. Rewrite using `[← _root_.mul_assoc, Ring.mul_inverse_cancel _ (isUnit_wv w hk hj'), _root_.one_mul]`. Use `⟨fun j' => Ring.inverse (wv w x k j') * τ k, ⟨fun j' hj' => ?_, fun j' k' hjk => ?_⟩, fun j j' hj hj' => ?_⟩` and prove the remaining obligations. Conclude with `isUnit_of_mul_isUnit_right ((hi j' hj').symm ▸ h.1 k hk)`.

Establish `hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j'` using `fun _ hz => (hjk hz).1`. Establish `hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k'` using `fun _ hz => (hjk hz).2`. Establish `e` using `wv_trans hw hk hk hj' hk'`. Rewrite `e` using `[valR_g_self hL hk, _root_.one_mul]`. Use `(isUnit_wv w hk hj').mul_left_cancel ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[hi j' hj', ← _root_.mul_assoc, e, hi k' hk']`. Establish `e` using `wv_trans hw hj hk hj' hj'`. Rewrite `e` using `[valR_g_self hL' hj', _root_.mul_one]`. Use `beta_reduce`.

Rewrite using `[e, _root_.mul_assoc, hi j' hj']`. Conclude with `h.2 j k (fun _ hz => ⟨hj hz, hk hz⟩)`.
-/
theorem exists_frm_down {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {x : Sp R ⟶ X'}
    {τ : L.ι → R} (h : IsFrm L (x ≫ F) τ) : ∃ τ', IsFrm L' x τ' ∧ FrmRel w x τ τ' := by
  obtain ⟨k, hk⟩ := exists_chart_pt hL (x ≫ F)
  have hi : ∀ j', ⊤ ≤ x ⁻¹ᵁ L'.U j' → wv w x k j' * (Ring.inverse (wv w x k j') * τ k) = τ k := fun j' hj' => by
    rw [← _root_.mul_assoc, Ring.mul_inverse_cancel _ (isUnit_wv w hk hj'), _root_.one_mul]
  refine ⟨fun j' => Ring.inverse (wv w x k j') * τ k, ⟨fun j' hj' => ?_, fun j' k' hjk => ?_⟩,
    fun j j' hj hj' => ?_⟩
  · exact isUnit_of_mul_isUnit_right ((hi j' hj').symm ▸ h.1 k hk)
  · have hj' : ⊤ ≤ x ⁻¹ᵁ L'.U j' := fun _ hz => (hjk hz).1
    have hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k' := fun _ hz => (hjk hz).2
    have e := wv_trans hw hk hk hj' hk'
    rw [valR_g_self hL hk, _root_.one_mul] at e
    refine (isUnit_wv w hk hj').mul_left_cancel ?_
    beta_reduce
    rw [hi j' hj', ← _root_.mul_assoc, e, hi k' hk']
  · have e := wv_trans hw hj hk hj' hj'
    rw [valR_g_self hL' hj', _root_.mul_one] at e
    beta_reduce
    rw [e, _root_.mul_assoc, hi j' hj']
    exact h.2 j k (fun _ hz => ⟨hj hz, hk hz⟩)

variable {w : LB.Iso L' (L.pull F)} {p : Z ⟶ X} {p' : Z' ⟶ X'} {h : Z' ⟶ Z} {k : ℕ} {a : SecP L' p' k} {t : SecP L p k}

/- English proof (translation)
Apply `toStkA_injective` to reduce the goal to its premises. Establish `hj₂ : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j` using `by rwa [Category.assoc, ← hψ, ← Category.assoc]`. Establish `m₁ : ⊤ ≤ (r ≫ h) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)` using `fun _ hz => Set.mem_iInter.2 fun _ => hj₂ hz`. Establish `m₂ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => p') (fun _ => j')` using `fun _ hz => Set.mem_iInter.2 fun _ => hj' hz`. Rewrite using `[map_mul, map_pow, toStkA_wv w hj hj']`.

Use `(FormalValue.toStkA_valR_eq_gs _ _ _ m₁ _).trans ((H _ r (cpt R) (fun _ => j) (fun _ => j') (fun _ => hj trivial) (fun _ => hj' trivial)).trans (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs _ _ _ m₂ _).symm))` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem sval_through (hψ : p' ≫ F = h ≫ p)
    (H : ConstFam.SecThrough w (fun _ : Fin 1 => p') (fun _ => p) (fun _ => (k : ℤ)) a t h) (r : Sp R ⟶ Z')
    {j : L.ι} {j' : L'.ι} (hj : ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U j') :
    ArcPts.sval t (r ≫ h) j = wv w (r ≫ p') j j' ^ k * ArcPts.sval a r j' := by
  apply toStkA_injective
  have hj₂ : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j := by rwa [Category.assoc, ← hψ, ← Category.assoc]
  have m₁ : ⊤ ≤ (r ≫ h) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun _ hz => Set.mem_iInter.2 fun _ => hj₂ hz
  have m₂ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => p') (fun _ => j') :=
    fun _ hz => Set.mem_iInter.2 fun _ => hj' hz
  rw [map_mul, map_pow, toStkA_wv w hj hj']
  refine (FormalValue.toStkA_valR_eq_gs _ _ _ m₁ _).trans
    ((H _ r (cpt R) (fun _ => j) (fun _ => j') (fun _ => hj trivial) (fun _ => hj' trivial)).trans
      (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs _ _ _ m₂ _).symm))
  simp

/- English proof (translation)
Establish `e : (r ≫ h) ≫ p = (r ≫ p') ≫ F` using `by rw [Category.assoc, ← hψ, Category.assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `ha j hj`. Rewrite `hj` using `[e]`. Take `⟨j', hj'⟩` from `exists_chart_pt hL' (r ≫ p')`.

Rewrite using `[sval_through hψ H r hj hj', ha j' hj', hτ j j' hj hj']`. Expand and normalize the polynomial expressions, which then agree. Introduce `ht j' hj'`. Take `⟨j, hj⟩` from `exists_chart_pt hL ((r ≫ p') ≫ F)`. Use `((isUnit_wv w hj hj').pow k).mul_left_cancel ?_` and prove the remaining obligations.

Rewrite using `[← sval_through hψ H r hj hj', ht j (e ▸ hj), hτ j j' hj hj']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) (hψ : p' ≫ F = h ≫ p)
    (H : ConstFam.SecThrough w (fun _ : Fin 1 => p') (fun _ => p) (fun _ => (k : ℤ)) a t h) (r : Sp R ⟶ Z')
    {τ : L.ι → R} {τ' : L'.ι → R} (hτ : FrmRel w (r ≫ p') τ τ') (c : R) :
    ArcPts.HasVal a r τ' c ↔ ArcPts.HasVal t (r ≫ h) τ c := by
  have e : (r ≫ h) ≫ p = (r ≫ p') ≫ F := by rw [Category.assoc, ← hψ, Category.assoc]
  constructor
  · intro ha j hj
    rw [e] at hj
    obtain ⟨j', hj'⟩ := exists_chart_pt hL' (r ≫ p')
    rw [sval_through hψ H r hj hj', ha j' hj', hτ j j' hj hj']
    ring
  · intro ht j' hj'
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((r ≫ p') ≫ F)
    refine ((isUnit_wv w hj hj').pow k).mul_left_cancel ?_
    rw [← sval_through hψ H r hj hj', ht j (e ▸ hj), hτ j j' hj hj']
    ring

omit [IsLocalRing R] in
/- English proof (translation)
Introduce `j hj`. Establish `hm : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)` using `fun _ hz => Set.mem_iInter.2 fun _ => hj hz`. Establish `e₁` using `(Points.valR_eq _ _ hm _).symm.trans (ha j hj)`. Establish `e₂` using `(Points.valR_eq _ _ hm _).symm.trans (hb j hj)`. Rewrite using `[zero_mul]`.

Conclude with `(Points.valR_eq _ _ hm _).trans ((map_sub _ _ _).trans (sub_eq_zero.2 (e₁.trans e₂.symm)))`.
-/
theorem hasVal_secSub {a b : SecP L p k} {r : Sp R ⟶ Z} {τ : L.ι → R} {c : R} (ha : ArcPts.HasVal a r τ c)
    (hb : ArcPts.HasVal b r τ c) : ArcPts.HasVal (secSub a b) r τ 0 := by
  intro j hj
  have hm : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := fun _ hz => Set.mem_iInter.2 fun _ => hj hz
  have e₁ := (Points.valR_eq _ _ hm _).symm.trans (ha j hj)
  have e₂ := (Points.valR_eq _ _ hm _).symm.trans (hb j hj)
  rw [zero_mul]
  exact (Points.valR_eq _ _ hm _).trans ((map_sub _ _ _).trans (sub_eq_zero.2 (e₁.trans e₂.symm)))

end Val

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S S' : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
  {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {y' : Sp ℂ⸨X⸩ ⟶ S'} {y : Sp ℂ⸨X⸩ ⟶ S}
  {Φ' : GenPts A t' y'} {Φ : GenPts A t y} {h : pullback t'.G.hom y' ⟶ pullback t.G.hom y}

omit [StarRing (𝓞 E)] in
/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← h₁, fib, fib, pullback.lift_fst_assoc, pullback.lift_fst, e]`. Rewrite using `[Category.assoc, h₂, fib, fib, pullback.lift_snd, pullback.lift_snd]`.
-/
theorem fib_comp (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _) (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _)
    {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ t.G} (e : p'.left ≫ m.φ = p.left) : fib p' ≫ h = fib p := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← h₁, fib, fib, pullback.lift_fst_assoc, pullback.lift_fst, e]
  · rw [Category.assoc, h₂, fib, fib, pullback.lift_snd, pullback.lift_snd]

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem fib_fst {R : Type} [CommRing R] {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

/- English proof (translation)
Take `⟨a, ha⟩` from `ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => pullback.fst t'.G.hom y') hw t.PP.isLB t'.PP.isLB (fun _ => h₁) (Φ.sig k α th)`. Establish `hv : ∀ v, ArcPts.HasVal (m` using `k) a (fib (Φ'.x v)) (Φ'.τ v) (A.FSum k α th v) := fun v => by`. Use `(hasVal_iff t.PP.isLB t'.PP.isLB h₁ ha _ (τ := Φ.τ v) ?_ _).2 ?_` and prove the remaining obligations. Rewrite using `[fib_fst]`. Conclude with `fun j j' hj hj' => (hR.2 v).2 j j' (le_div hj hj')`.

Rewrite using `[fib_comp h₁ h₂ (hR.2 v).1]`. Conclude with `Φ.val k α th hth v`. Establish `e : a.f = (Φ'.sig k α th).f` using `funext fun i => sub_eq_zero.1 (Φ'.sep k (secSub a (Φ'.sig k α th)) (fun v => hasVal_secSub (hv v) (Φ'.val k α th hth v)) i)`. Introduce `Z r z p q hp hq`. Rewrite using `[← e]`.

Conclude with `ha Z r z p q hp hq`.
-/
theorem sig_through (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ)
    (hth : th ∈ A.Theta k α) :
    ConstFam.SecThrough w (fun _ : Fin 1 => pullback.fst t'.G.hom y') (fun _ => pullback.fst t.G.hom y)
      (fun _ => (k : ℤ)) (Φ'.sig k α th) (Φ.sig k α th) h := by
  obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => pullback.fst t'.G.hom y')
    hw t.PP.isLB t'.PP.isLB (fun _ => h₁) (Φ.sig k α th)
  have hv : ∀ v, ArcPts.HasVal (m := k) a (fib (Φ'.x v)) (Φ'.τ v) (A.FSum k α th v) := fun v => by
    refine (hasVal_iff t.PP.isLB t'.PP.isLB h₁ ha _ (τ := Φ.τ v) ?_ _).2 ?_
    · rw [fib_fst]
      exact fun j j' hj hj' => (hR.2 v).2 j j' (le_div hj hj')
    · rw [fib_comp h₁ h₂ (hR.2 v).1]
      exact Φ.val k α th hth v
  have e : a.f = (Φ'.sig k α th).f := funext fun i => sub_eq_zero.1
    (Φ'.sep k (secSub a (Φ'.sig k α th)) (fun v => hasVal_secSub (hv v) (Φ'.val k α th hth v)) i)
  intro Z r z p q hp hq
  rw [← e]
  exact ha Z r z p q hp hq

/- English proof (translation)
Take `⟨π, hπ⟩` from `LiePull.exists_pushEquiv m.cart (Over.mk y') y hR.1.symm`. Take `rfl : π p' = p` from `Over.OverMorphism.ext ((hπ p').trans e)`. Establish `hx : ∀ z, (Φ'.x z * p').left ≫ m.φ = (Φ.x z * π p').left` using `fun z => by`. Establish `: π (Φ'.x z) = Φ.x z` using `Over.OverMorphism.ext ((hπ _).trans (hR.2 z).1)`. Rewrite using `[← this, ← map_mul, hπ]`.

Establish `key : ∀ (α α' : A.X), ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α', ∀ (z : A.V) (F F' : ℂ⸨X⸩) j j', ⊤ ≤ (Φ.x z * π p').left ⁻¹ᵁ t.PP.L.U j → ⊤ ≤ (Φ'.x z * p').left ⁻¹ᵁ t'.PP.L.U j' → (ArcPts.sval (Φ'.sig k α th) (fib (Φ'.x z * p')) j' * F' = ArcPts.sval (Φ'.sig k α' th') (fib (Φ'.x z …`. Introduce `α α' th hth th' hth' z F F' j j' hj hj'`. Rewrite `hj` using `[← hx, ← fib_fst]`. Rewrite `hj'` using `[← fib_fst]`. Rewrite using `[← fib_comp h₁ h₂ (hx z), sval_through h₁ (sig_through hw hR h₁ h₂ k α th hth) _ hj hj', sval_through h₁ (sig_through hw hR h₁ h₂ k α' th' hth') _ hj hj', _root_.mul_assoc, _root_.mul_assoc]`.

Conclude with `((isUnit_wv w hj hj').pow k).mul_right_inj.symm`. Use `and_congr (by rw [← map_pow, MulEquiv.map_eq_one_iff]) (and_congr Iff.rfl ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `H α α' th hth th' hth' z F F' j hF hF' hj`. Take `⟨j', hj'⟩` from `exists_chart_pt t'.PP.isLB (R := ℂ⸨X⸩) (Φ'.x z * p').left`. Conclude with `(key α α' th hth th' hth' z F F' j j' hj hj').1 (H α α' th hth th' hth' z F F' j' hF hF' hj')`.

Introduce `H α α' th hth th' hth' z F F' j' hF hF' hj'`. Take `⟨j, hj⟩` from `exists_chart_pt t.PP.isLB (R := ℂ⸨X⸩) (Φ.x z * π p').left`. Conclude with `(key α α' th hth th' hth' z F F' j j' hj hj').2 (H α α' th hth th' hth' z F F' j hF hF' hj)`.
-/
theorem levelPt_iff (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G)
    (p : Over.mk y ⟶ t.G) (la : A.La) (e : p'.left ≫ m.φ = p.left) : Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la := by
  obtain ⟨π, hπ⟩ := LiePull.exists_pushEquiv m.cart (Over.mk y') y hR.1.symm
  obtain rfl : π p' = p := Over.OverMorphism.ext ((hπ p').trans e)
  have hx : ∀ z, (Φ'.x z * p').left ≫ m.φ = (Φ.x z * π p').left := fun z => by
    have : π (Φ'.x z) = Φ.x z := Over.OverMorphism.ext ((hπ _).trans (hR.2 z).1)
    rw [← this, ← map_mul, hπ]
  have key : ∀ (α α' : A.X), ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α', ∀ (z : A.V) (F F' : ℂ⸨X⸩) j j',
      ⊤ ≤ (Φ.x z * π p').left ⁻¹ᵁ t.PP.L.U j → ⊤ ≤ (Φ'.x z * p').left ⁻¹ᵁ t'.PP.L.U j' →
      (ArcPts.sval (Φ'.sig k α th) (fib (Φ'.x z * p')) j' * F' =
          ArcPts.sval (Φ'.sig k α' th') (fib (Φ'.x z * p')) j' * F ↔
        ArcPts.sval (Φ.sig k α th) (fib (Φ.x z * π p')) j * F' =
          ArcPts.sval (Φ.sig k α' th') (fib (Φ.x z * π p')) j * F) := by
    intro α α' th hth th' hth' z F F' j j' hj hj'
    rw [← hx, ← fib_fst] at hj
    rw [← fib_fst] at hj'
    rw [← fib_comp h₁ h₂ (hx z), sval_through h₁ (sig_through hw hR h₁ h₂ k α th hth) _ hj hj',
      sval_through h₁ (sig_through hw hR h₁ h₂ k α' th' hth') _ hj hj', _root_.mul_assoc, _root_.mul_assoc]
    exact ((isUnit_wv w hj hj').pow k).mul_right_inj.symm
  refine and_congr (by rw [← map_pow, MulEquiv.map_eq_one_iff]) (and_congr Iff.rfl ⟨?_, ?_⟩)
  · intro H α α' th hth th' hth' z F F' j hF hF' hj
    obtain ⟨j', hj'⟩ := exists_chart_pt t'.PP.isLB (R := ℂ⸨X⸩) (Φ'.x z * p').left
    exact (key α α' th hth th' hth' z F F' j j' hj hj').1 (H α α' th hth th' hth' z F F' j' hF hF' hj')
  · intro H α α' th hth th' hth' z F F' j' hF hF' hj'
    obtain ⟨j, hj⟩ := exists_chart_pt t.PP.isLB (R := ℂ⸨X⸩) (Φ.x z * π p').left
    exact (key α α' th hth th' hth' z F F' j j' hj hj').2 (H α α' th hth th' hth' z F F' j hF hF' hj)

/- English proof (translation)
Establish `inj : ∀ {T : Scheme.{0}} (a b : T ⟶ pullback t'.G.hom y'), a ≫ h = b ≫ h → a = b` using `fun a b e => by`. Establish `e₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _` using `by rw [← h₂, reassoc_of% e]`. Use `pullback.hom_ext (m.cart.1.hom_ext ?_ ?_) e₂` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, h₁, reassoc_of% e]`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, reassoc_of% e₂]`.

Establish `e : (ν' ≫ h) ≫ pullback.fst _ _ = (ν' ≫ pullback.fst _ _) ≫ m.φ`. Rewrite using `[Category.assoc, Category.assoc, h₁]`. Use `and_congr (by rw [Category.assoc, h₂]) (and_congr ?_ ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[← fib_comp h₁ h₂ (hR.2 0).1, ← Category.assoc]`. Conclude with `⟨fun c => by rw [c], inj _ _⟩`.

Introduce and unpack `⟨τ', hτ', H⟩`. Take `⟨τ, hτ, hr⟩` from `exists_frm_up hw t.PP.isLB t'.PP.isLB hτ'`. Conclude with `⟨τ, e ▸ hτ, fun j _ α th hth F hF => (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).1 (H j α th hth F hF)⟩`. Introduce and unpack `⟨τ, hτ, H⟩`. Rewrite `hτ` using `[e]`.

Take `⟨τ', hτ', hr⟩` from `exists_frm_down hw t.PP.isLB t'.PP.isLB hτ`. Conclude with `⟨τ', hτ', fun j _ α th hth F hF => (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).2 (H j α th hth F hF)⟩`.
-/
theorem isTan_iff (hw : w.IsGen) (hR : GenPts.Rel m w Φ' Φ) (h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _)
    (h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _) (z₀ : A.V) (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') :
    Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ (ν' ≫ h) := by
  have inj : ∀ {T : Scheme.{0}} (a b : T ⟶ pullback t'.G.hom y'), a ≫ h = b ≫ h → a = b := fun a b e => by
    have e₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by rw [← h₂, reassoc_of% e]
    refine pullback.hom_ext (m.cart.1.hom_ext ?_ ?_) e₂
    · rw [Category.assoc, Category.assoc, h₁, reassoc_of% e]
    · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% e₂]
  have e : (ν' ≫ h) ≫ pullback.fst _ _ = (ν' ≫ pullback.fst _ _) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, h₁]
  refine and_congr (by rw [Category.assoc, h₂]) (and_congr ?_ ⟨?_, ?_⟩)
  · rw [← fib_comp h₁ h₂ (hR.2 0).1, ← Category.assoc]
    exact ⟨fun c => by rw [c], inj _ _⟩
  · rintro ⟨τ', hτ', H⟩
    obtain ⟨τ, hτ, hr⟩ := exists_frm_up hw t.PP.isLB t'.PP.isLB hτ'
    exact ⟨τ, e ▸ hτ, fun j _ α th hth F hF =>
      (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).1 (H j α th hth F hF)⟩
  · rintro ⟨τ, hτ, H⟩
    rw [e] at hτ
    obtain ⟨τ', hτ', hr⟩ := exists_frm_down hw t.PP.isLB t'.PP.isLB hτ
    exact ⟨τ', hτ', fun j _ α th hth F hF =>
      (hasVal_iff t.PP.isLB t'.PP.isLB h₁ (sig_through hw hR h₁ h₂ j α th hth) ν' hr _).2 (H j α th hth F hF)⟩

end Main

/- English proof (translation)
Introduce `E _ _ _ H _ S S' A t t' f m w y' y Φ' Φ hw hR`. Set `h : pullback t'.G.hom y' ⟶ pullback t.G.hom y` to `pullback.lift (pullback.fst _ _ ≫ m.φ) (pullback.snd _ _) (by`. Rewrite using `[Category.assoc, m.cart.1.w, pullback.condition_assoc, hR.1])`. Establish `h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _` using `(pullback.lift_fst _ _ _).symm`. Establish `h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`.

Use `⟨fun k _ p' p la e => levelPt_iff hw hR h₁ h₂ k p' p la e, fun z₀ ν' ν e₁ e₂ => ?_⟩` and prove the remaining obligations. Take `rfl : ν' ≫ h = ν` from `pullback.hom_ext (by rw [Category.assoc, ← h₁, e₁]) (by rw [Category.assoc, h₂, e₂])`. Conclude with `isTan_iff hw hR h₁ h₂ z₀ ν'`.
-/
theorem levelPt_isTan_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S) (Φ' : GenPts A t' y') (Φ : GenPts A t y), w.IsGen → GenPts.Rel m w Φ' Φ → (∀ (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G) (p : Over.mk y ⟶ t.G) la, p'.left ≫ m.φ = p.left → (Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la)) ∧ ∀ z₀ (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y), ν' ≫ pullback.fst _ _ ≫ m.φ = ν ≫ pullback.fst _ _ → ν' ≫ pullback.snd _ _ = ν ≫ pullback.snd _ _ → (Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ ν) := by
  intro E _ _ _ H _ S S' A t t' f m w y' y Φ' Φ hw hR
  let h : pullback t'.G.hom y' ⟶ pullback t.G.hom y := pullback.lift (pullback.fst _ _ ≫ m.φ) (pullback.snd _ _) (by
    rw [Category.assoc, m.cart.1.w, pullback.condition_assoc, hR.1])
  have h₁ : pullback.fst _ _ ≫ m.φ = h ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨fun k _ p' p la e => levelPt_iff hw hR h₁ h₂ k p' p la e, fun z₀ ν' ν e₁ e₂ => ?_⟩
  obtain rfl : ν' ≫ h = ν := pullback.hom_ext (by rw [Category.assoc, ← h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
  exact isTan_iff hw hR h₁ h₂ z₀ ν'

end GlobalTheory.LevelTransport
