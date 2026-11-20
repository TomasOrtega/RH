import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToOverSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTateWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLatHTIffNormTanEvLe

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open scoped NNReal TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatModel GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetHT.Bridge

section General

variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]

/- English proof (translation)
Establish `h1 : v z = 1`. Establish `: v z ^ m = 1` using `by rw [← map_pow, h]; exact hv.one_of_isUnit a.isUnit`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le' hm).1 this`. Take `⟨b, hb⟩` from `hv.exists_of_le_one h1.le`. Conclude with `⟨(hv.isUnit_of_one' (x := b) (hb ▸ h1)).unit, hb⟩`.
-/
theorem exists_unit (hv : v.Integers O) {m : ℕ} (hm : m ≠ 0) {z : C} {a : Oˣ} (h : z ^ m = algebraMap O C a) :
    ∃ w : Oˣ, algebraMap O C w = z := by
  have h1 : v z = 1 := by
    have : v z ^ m = 1 := by rw [← map_pow, h]; exact hv.one_of_isUnit a.isUnit
    exact (pow_eq_one_iff_of_nonneg zero_le' hm).1 this
  obtain ⟨b, hb⟩ := hv.exists_of_le_one h1.le
  exact ⟨(hv.isUnit_of_one' (x := b) (hb ▸ h1)).unit, hb⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hn)`. Take `⟨b, hb⟩` from `exists_unit hv hn hz`. Conclude with `⟨b, Units.ext (hv.hom_inj (by rw [Units.val_pow_eq_pow_val, map_pow, hb, hz]))⟩`.
-/
theorem units_root [IsAlgClosed C] (hv : v.Integers O) (n : ℕ) (hn : n ≠ 0) (a : Oˣ) : ∃ b : Oˣ, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hn)
  obtain ⟨b, hb⟩ := exists_unit hv hn hz
  exact ⟨b, Units.ext (hv.hom_inj (by rw [Units.val_pow_eq_pow_val, map_pow, hb, hz]))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [Fact p.Prime] [IsAlgClosed C] [CharZero C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  {P : Point p v O Λ} {z : Sp O ⟶ X} {φ : P.G.left ⟶ t.G.left}

/- English proof (translation)
Establish `hq : p ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Establish `hk : 1 ≤ p ^ n` using `GlobalTheory.HTLat.one_le_ppow p n`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.WeilTorsChar.exists_mulEquiv_points z t.G P.G φ hφ (specO O O)`. Take `⟨j, -, hj⟩` from `P.exists_generic`. Set `ψ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) →* GlobalTheory.ChTor.Pts P.A.A` to `j.comp Φ.symm.toMonoidHom`.

Establish `hψ : ∀ w, w ^ (p ^ n) = 1 → ψ w ^ (p ^ n) = 1` using `fun w h => by rw [← map_pow, h, map_one]`. Establish `hroot : ∀ w, w ^ (p ^ n) = 1 → (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C) ^ (p ^ n) = algebraMap O C (1 : Oˣ)` using `fun w h => by`. Rewrite using `[← Units.val_pow_eq_pow_val, ← GlobalTheory.HTLat.weil_pow_left hk (hψ w h) (s.lev_pow n), hψ w h]`. Simplify using `using GlobalTheory.HTLat.weil_pow_left hk (one_pow (p ^ n)) (s.lev_pow n) 0`. Set `χ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) → Oˣ` to `fun w => if h : w ^ (p ^ n) = 1 then (exists_unit P.integers hq (hroot w h)).choose else 1`.

Establish `hχ : ∀ w (h : w ^ (p ^ n) = 1), algebraMap O C (χ w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C)` using `fun w h => by`. Simplify using `only [χ, dif_pos h]`. Conclude with `(exists_unit P.integers hq (hroot w h)).choose_spec`. Establish `hmul : ∀ w w', w ^ (p ^ n) = 1 → w' ^ (p ^ n) = 1 → χ (w * w') = χ w * χ w'`. Introduce `w w' h h'`.

Establish `h'' : (w * w') ^ (p ^ n) = 1` using `by rw [mul_pow, h, h', _root_.one_mul]`. Apply `Units.ext` to reduce the goal to its premises. Apply `P.integers.hom_inj` to reduce the goal to its premises. Rewrite using `[Units.val_mul, map_mul, hχ (w * w') h'', hχ w h, hχ w' h', map_mul, GlobalTheory.HTLat.weil_mul_left hk (hψ w h) (hψ w' h') (s.lev_pow n), Units.val_mul]`. Use `haveI : CharZero O := (algebraMap O C).charZero`.

Use `haveI : IsAlgClosed (FractionRing O) := IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv`. Take `⟨κ, hκ⟩` from `GlobalTheory.TorsCharExt.exists_hom_extend (units_root P.integers) (p ^ n) χ hmul`. Take `⟨c, hc⟩` from `GlobalTheory.TorsCharExt.exists_char t z (p ^ n) hq κ`. Use `⟨c, fun w a hw ha => ?_⟩` and prove the remaining obligations. Establish `hA : a = ψ w`.

Use `(hj (Φ.symm w) a).1 ?_` and prove the remaining obligations. Apply `hφ.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ha, Category.assoc, ← hΦ, MulEquiv.apply_symm_apply]`. Rewrite using `[Category.assoc, Category.assoc, Over.w (Φ.symm w), P.gen_pull.1.w, ← Category.assoc, Over.w a]`. Express the relevant statement in the definitionally equal form `𝟙 _ ≫ spMap (algebraMap O C) = spMap (algebraMap O C) ≫ spMap (algebraMap O O)`.

Rewrite using `[Algebra.algebraMap_self, GlobalTheory.TorsCharExt.sp_id, Category.comp_id, Category.id_comp]`. Rewrite using `[hc w hw, hκ w hw, hA]`. Conclude with `hχ w hw`.
-/
theorem exists_torsChar [IsLocallyNoetherian X] [IsDomain O] [IsFractionRing O C] [IsIntegrallyClosed O] [IsLocalRing O]
    (hφ : IsGrpPullback P.G t.G z φ) (n : ℕ) (s : P.T) :
    ∃ c : TorsChar t z (p ^ n), ∀ (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) (a : GlobalTheory.ChTor.Pts P.A.A),
      w ^ (p ^ n) = 1 → a.left ≫ P.gen ≫ φ = spMap (algebraMap O C) ≫ w.left →
        algebraMap O C (c.χ O w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) a (s.lev n) : C) := by
  classical
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hk : 1 ≤ p ^ n := GlobalTheory.HTLat.one_le_ppow p n
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points z t.G P.G φ hφ (specO O O)
  obtain ⟨j, -, hj⟩ := P.exists_generic
  let ψ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) →* GlobalTheory.ChTor.Pts P.A.A := j.comp Φ.symm.toMonoidHom
  have hψ : ∀ w, w ^ (p ^ n) = 1 → ψ w ^ (p ^ n) = 1 := fun w h => by rw [← map_pow, h, map_one]
  have hroot : ∀ w, w ^ (p ^ n) = 1 → (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C) ^ (p ^ n) =
      algebraMap O C (1 : Oˣ) := fun w h => by
    rw [← Units.val_pow_eq_pow_val, ← GlobalTheory.HTLat.weil_pow_left hk (hψ w h) (s.lev_pow n), hψ w h]
    simpa using GlobalTheory.HTLat.weil_pow_left hk (one_pow (p ^ n)) (s.lev_pow n) 0
  let χ : (Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) → Oˣ := fun w =>
    if h : w ^ (p ^ n) = 1 then (exists_unit P.integers hq (hroot w h)).choose else 1
  have hχ : ∀ w (h : w ^ (p ^ n) = 1),
      algebraMap O C (χ w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) (ψ w) (s.lev n) : C) := fun w h => by
    simp only [χ, dif_pos h]
    exact (exists_unit P.integers hq (hroot w h)).choose_spec
  have hmul : ∀ w w', w ^ (p ^ n) = 1 → w' ^ (p ^ n) = 1 → χ (w * w') = χ w * χ w' := by
    intro w w' h h'
    have h'' : (w * w') ^ (p ^ n) = 1 := by rw [mul_pow, h, h', _root_.one_mul]
    apply Units.ext
    apply P.integers.hom_inj
    rw [Units.val_mul, map_mul, hχ (w * w') h'', hχ w h, hχ w' h', map_mul,
      GlobalTheory.HTLat.weil_mul_left hk (hψ w h) (hψ w' h') (s.lev_pow n), Units.val_mul]
  haveI : CharZero O := (algebraMap O C).charZero
  haveI : IsAlgClosed (FractionRing O) := IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := GlobalTheory.TorsCharExt.exists_hom_extend (units_root P.integers) (p ^ n) χ hmul
  obtain ⟨c, hc⟩ := GlobalTheory.TorsCharExt.exists_char t z (p ^ n) hq κ
  refine ⟨c, fun w a hw ha => ?_⟩
  have hA : a = ψ w := by
    refine (hj (Φ.symm w) a).1 ?_
    apply hφ.1.hom_ext
    · rw [Category.assoc, ha, Category.assoc, ← hΦ, MulEquiv.apply_symm_apply]
    · rw [Category.assoc, Category.assoc, Over.w (Φ.symm w), P.gen_pull.1.w, ← Category.assoc, Over.w a]
      change 𝟙 _ ≫ spMap (algebraMap O C) = spMap (algebraMap O C) ≫ spMap (algebraMap O O)
      rw [Algebra.algebraMap_self, GlobalTheory.TorsCharExt.sp_id, Category.comp_id, Category.id_comp]
  rw [hc w hw, hκ w hw, hA]
  exact hχ w hw

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h s`. Take `⟨c, hc⟩` from `exists_torsChar hφ k s`. Take `⟨g, hg⟩` from `GlobalTheory.HTLevel.red_ex (Ideal.span {(p : O) ^ k}) (TanPair.isTanAtG_lieG hφ (P.lieCmp x))`. Establish `h1` using `h k c g hg`.

Establish `h2 : (p : O ⧸ Ideal.span {(p : O) ^ k}) ^ k = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk _), ← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Rewrite `h1` using `[GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ k c s hc x g hg, h2, Ideal.span_singleton_zero, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Introduce `h n c g hg`.

Take `⟨s, hs⟩` from `GlobalTheory.CharWeil.exists_tate_gen t P z φ hφ n c`. Take `⟨b, hb⟩` from `h s`. Rewrite using `[GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ n c s hs x g hg, hb, map_mul, map_pow, map_natCast]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem dlogDvd_iff [IsLocallyNoetherian X] [IsDomain O] [IsFractionRing O C] [IsIntegrallyClosed O]
    [HenselianLocalRing O] [Algebra ℤ_[p] O] (hφ : IsGrpPullback P.G t.G z φ) (x : LieG P.Gt) (k : ℕ) :
    DlogDvd t z p k ((P.lieCmp x).1.left ≫ φ) ↔ ∀ s : P.T, (p : O) ^ k ∣ (P.al₀ s).1 x := by
  constructor
  · intro h s
    obtain ⟨c, hc⟩ := exists_torsChar hφ k s
    obtain ⟨g, hg⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : O) ^ k}) (TanPair.isTanAtG_lieG hφ (P.lieCmp x))
    have h1 := h k c g hg
    have h2 : (p : O ⧸ Ideal.span {(p : O) ^ k}) ^ k = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rwa [GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ k c s hc x g hg, h2, Ideal.span_singleton_zero, Ideal.mem_bot,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  · intro h n c g hg
    obtain ⟨s, hs⟩ := GlobalTheory.CharWeil.exists_tate_gen t P z φ hφ n c
    obtain ⟨b, hb⟩ := h s
    rw [GlobalTheory.TorsCharDlog.snd_chi_eq t P z φ hφ n c s hs x g hg, hb, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

omit [IsAlgClosed C] [CharZero C] in

/- English proof (translation)
Establish `key : ∀ u, LieTie P (P.gen ≫ π) x u → spMap (dualMap (algebraMap O C)) ≫ (P.lieCmp x).1.left ≫ π = u`. Introduce and unpack `u ⟨xG, u', h1, h2, h3⟩`. Rewrite using `[← (P.eq_lieCmp_iff x _).2 h1, ← Category.assoc, ← h3, Category.assoc, h2]`. Use `⟨key u, fun h => ?_⟩` and prove the remaining obligations. Take `⟨u', h'⟩` from `exists_lieTie P (P.gen ≫ π) x`.

Rewrite using `[← h, key u' h']` and apply the resulting hypothesis.
-/
theorem lieTie_iff {Y : Scheme.{0}} (π : P.G.left ⟶ Y) (x : LieG P.Gt) (u : Sp (DualNumber C) ⟶ Y) :
    LieTie P (P.gen ≫ π) x u ↔ spMap (dualMap (algebraMap O C)) ≫ (P.lieCmp x).1.left ≫ π = u := by
  have key : ∀ u, LieTie P (P.gen ≫ π) x u → spMap (dualMap (algebraMap O C)) ≫ (P.lieCmp x).1.left ≫ π = u := by
    rintro u ⟨xG, u', h1, h2, h3⟩
    rw [← (P.eq_lieCmp_iff x _).2 h1, ← Category.assoc, ← h3, Category.assoc, h2]
  refine ⟨key u, fun h => ?_⟩
  obtain ⟨u', h'⟩ := exists_lieTie P (P.gen ≫ π) x
  rwa [← h, key u' h']

end General

/- English proof (translation)
Rewrite using `[spMap_spMap]`. Use `congr 1`. Apply the tactic sequence `ext s <;> simp [epsMul, mul_assoc]`.
-/
theorem epsMul_comp {S : Type} [CommRing S] (a b : S) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b)) := by
  rw [spMap_spMap]
  congr 1
  ext s <;> simp [epsMul, mul_assoc]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Set `d : tEpsG x ⟶ tEpsG x` to `Over.homMk (spMap (epsMul c)) (by`. Express the relevant statement in the definitionally equal form `spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x`. Rewrite using `[← Category.assoc, spMap_spMap]`. Use `congr 2`.

Apply the tactic sequence `ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])`. Set `f : (tEpsG x ⟶ t.G) →* (tEpsG x ⟶ t.G)` to `MonoidHom.mk' (fun g => d ≫ g) fun g g' => MonObj.comp_mul d g g'`. Use `⟨fun i => f (y i), fun i => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap (epsMul c) ≫ (y i).left = _`. Rewrite using `[hy, ← Category.assoc, epsMul_comp]`.

Establish `e : (List.ofFn fun i => f (y i)).prod = f (List.ofFn y).prod`. Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem isCombAtG_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x u a w) (c : S) : IsCombAtG t x u (fun i => c * a i) (spMap (epsMul c) ≫ w) := by
  obtain ⟨y, hy, rfl⟩ := h
  let d : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul c)) (by
    change spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  let f : (tEpsG x ⟶ t.G) →* (tEpsG x ⟶ t.G) := MonoidHom.mk' (fun g => d ≫ g) fun g g' => MonObj.comp_mul d g g'
  refine ⟨fun i => f (y i), fun i => ?_, ?_⟩
  · change spMap (epsMul c) ≫ (y i).left = _
    rw [hy, ← Category.assoc, epsMul_comp]
  · have e : (List.ofFn fun i => f (y i)).prod = f (List.ofFn y).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [e]
    rfl

def latOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {C : Type} [Field C] (S : Subring C) (p : ℕ) (x : Sp C ⟶ X) : Set (Sp (DualNumber C) ⟶ t.G.left) :=
  {v | ∃ xO : Sp ↥S ⟶ X, spMap S.subtype ≫ xO = x ∧ ∃ (m : ℕ) (vO : Sp (DualNumber ↥S) ⟶ t.G.left),
    IsTanAtG t xO vO ∧ spMap (dualMap S.subtype) ≫ vO = spMap (epsMul ((p : C) ^ m)) ≫ v ∧ DlogDvd t xO p m vO}

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

/- English proof (translation)
Establish `e : intO ℂ_[p] = (𝓞_ℂ_[p]).toSubring` using `Subring.ext fun a => (GlobalTheory.PadicComplexHost.mem_iff_norm p a).symm`. Express the relevant statement in the definitionally equal form `w ∈ latOf t (intO ℂ_[p]) p x ↔ _`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem mem_latHT_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left) :
    w ∈ latHT t p x ↔ ∃ xO : Sp 𝓞_ℂ_[p] ⟶ X, spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ xO = x ∧
      ∃ (m : ℕ) (vO : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left), IsTanAtG t xO vO ∧
        spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ vO = spMap (epsMul ((p : ℂ_[p]) ^ m)) ≫ w ∧ DlogDvd t xO p m vO := by
  have e : intO ℂ_[p] = (𝓞_ℂ_[p]).toSubring := Subring.ext fun a => (GlobalTheory.PadicComplexHost.mem_iff_norm p a).symm
  change w ∈ latOf t (intO ℂ_[p]) p x ↔ _
  rw [e]
  rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => Q.bLie_zero.trans (Finset.sum_of_isEmpty _).symm | m + 1, a, x => by rw [lieComb_succ, Q.bLie_add, Q.bLie_scale, bLie_lieComb Q m, Fin.sum_univ_succ] rfl`.
-/
theorem bLie_lieComb {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (Q : PtP E p) :
    ∀ (m : ℕ) (a : Fin m → 𝓞_ℂ_[p]) (x : Fin m → LieG Q.Gt), Q.bLie (lieComb Q.Gt a x) = ∑ i, a i • Q.bLie (x i)
  | 0, _, _ => Q.bLie_zero.trans (Finset.sum_of_isEmpty _).symm
  | m + 1, a, x => by
    rw [lieComb_succ, Q.bLie_add, Q.bLie_scale, bLie_lieComb Q m, Fin.sum_univ_succ]
    rfl

/- English proof (translation)
Establish `hp : ‖(p : ℂ_[p])‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, ∀ l, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1 := by`. Establish `(l : Fin n) : ∀ᶠ k : ℕ in Filter.atTop, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1`.

Use `((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).mul_const (a l)).norm` as an intermediate fact. Rewrite `this` using `[zero_mul, norm_zero]`. Conclude with `this.eventually_le_const zero_lt_one`. Conclude with `(Filter.eventually_all.2 this).exists`. Conclude with `⟨k, fun i => ⟨_, (GlobalTheory.PadicComplexHost.mem_iff_norm p _).2 (hk i)⟩, fun _ => rfl⟩`.
-/
theorem exists_pow_mul_integral {p : ℕ} [Fact p.Prime] {n : ℕ} (a : Fin n → ℂ_[p]) :
    ∃ (k : ℕ) (b : Fin n → 𝓞_ℂ_[p]), ∀ i, algebraMap 𝓞_ℂ_[p] ℂ_[p] (b i) = (p : ℂ_[p]) ^ k * a i := by
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ l, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1 := by
    have (l : Fin n) : ∀ᶠ k : ℕ in Filter.atTop, ‖(p : ℂ_[p]) ^ k * a l‖ ≤ 1 := by
      have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).mul_const (a l)).norm
      rw [zero_mul, norm_zero] at this
      exact this.eventually_le_const zero_lt_one
    exact (Filter.eventually_all.2 this).exists
  exact ⟨k, fun i => ⟨_, (GlobalTheory.PadicComplexHost.mem_iff_norm p _).2 (hk i)⟩, fun _ => rfl⟩

/- English proof (translation)
Introduce `E _ _ _ H X _ _ t p hp _ Q yb π hπ n x u hu a w hw`. Use `haveI : HenselianLocalRing 𝓞_ℂ_[p] := GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed _ ℂ_[p]`. Establish `hp0 : (p : ℂ_[p]) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`. Establish `hψ` using `Q.gen_pull.comp hπ`. Establish `hpow : ∀ k : ℕ, algebraMap 𝓞_ℂ_[p] ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ k) = (p : ℂ_[p]) ^ k` using `fun k => by`.

Rewrite using `[map_pow, map_natCast]`. Take `⟨k, b, hb⟩` from `exists_pow_mul_integral a`. Establish `h₀ : LieTie Q (Q.gen ≫ π) (lieComb Q.Gt b x) (spMap (epsMul ((p : ℂ_[p]) ^ k)) ≫ w)` using `lieTie_lieComb E H X t p Q _ _ hψ n x u b _ hu (by simpa only [hb] using isCombAtG_scale hw _)`. Establish `e₀ : Q.bLie (lieComb Q.Gt b x) = (p : ℂ_[p]) ^ k • ∑ j, a j • Q.bLie (x j)`. Rewrite using `[bLie_lieComb, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [smul_smul, ← hb, algebraMap_smul]`. Establish `hd : ∀ (m : ℕ) (y : LieG Q.Gt), Q.bLie y = (p : ℂ_[p]) ^ m • ∑ j, a j • Q.bLie (x j) → (DlogDvd t yb p m ((Q.lieCmp y).1.left ≫ π) ↔ ∑ j, a j • Q.bLie (x j) ∈ Q.latT)` using `fun m y hy => by`. Rewrite using `[dlogDvd_iff hπ, Q.mem_latT_iff]`. Use `forall_congr' fun s => exists_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← Q.integers.hom_inj.eq_iff, ← Q.pairV_bLie, hy, map_smul, LinearMap.smul_apply, map_mul, hpow, smul_eq_mul, mul_right_inj' (pow_ne_zero m hp0), eq_comm]`.

Rewrite using `[mem_latHT_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, m, vO, hO, hs, hD⟩ haveI : IsDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 Q.integers.hom_inj).le.trans bot_le)⟩`. Take `rfl : z = yb` from `ext_of_isDominant _ hz`. Take `⟨y', rfl⟩` from `TanPair.exists_lieG hπ hO`.

Take `⟨y, rfl⟩` from `Q.lieCmp.surjective y'`. Establish `h₁` using `((lieTie_iff π y _).2 hs).scale ((p : 𝓞_ℂ_[p]) ^ k)`. Establish `h₂` using `h₀.scale ((p : 𝓞_ℂ_[p]) ^ m)`. Rewrite `h₁`, `h₂` using `[← Category.assoc, epsMul_comp, hpow]`. Rewrite `h₂` using `[mul_comm]`.

Establish `e` using `congrArg Q.bLie (h₁.unique hψ.1 h₂)`. Rewrite `e` using `[Q.bLie_scale, Q.bLie_scale, e₀, ← algebraMap_smul ℂ_[p], ← algebraMap_smul ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ m), hpow, hpow, smul_comm]`. Conclude with `(hd m y (smul_right_injective _ (pow_ne_zero k hp0) e)).1 hD`. Introduce `h`. Conclude with `⟨yb, rfl, k, _, TanPair.isTanAtG_lieG hπ (Q.lieCmp _), (lieTie_iff π _ _).1 h₀, (hd k _ e₀).2 h⟩`.
-/
theorem bridge : BridgeSt := by
  intro E _ _ _ H X _ _ t p hp _ Q yb π hπ n x u hu a w hw
  haveI : HenselianLocalRing 𝓞_ℂ_[p] := GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed _ ℂ_[p]
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hψ := Q.gen_pull.comp hπ
  have hpow : ∀ k : ℕ, algebraMap 𝓞_ℂ_[p] ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ k) = (p : ℂ_[p]) ^ k := fun k => by
    rw [map_pow, map_natCast]
  obtain ⟨k, b, hb⟩ := exists_pow_mul_integral a
  have h₀ : LieTie Q (Q.gen ≫ π) (lieComb Q.Gt b x) (spMap (epsMul ((p : ℂ_[p]) ^ k)) ≫ w) :=
    lieTie_lieComb E H X t p Q _ _ hψ n x u b _ hu (by simpa only [hb] using isCombAtG_scale hw _)
  have e₀ : Q.bLie (lieComb Q.Gt b x) = (p : ℂ_[p]) ^ k • ∑ j, a j • Q.bLie (x j) := by
    rw [bLie_lieComb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, ← hb, algebraMap_smul]
  have hd : ∀ (m : ℕ) (y : LieG Q.Gt), Q.bLie y = (p : ℂ_[p]) ^ m • ∑ j, a j • Q.bLie (x j) →
      (DlogDvd t yb p m ((Q.lieCmp y).1.left ≫ π) ↔ ∑ j, a j • Q.bLie (x j) ∈ Q.latT) := fun m y hy => by
    rw [dlogDvd_iff hπ, Q.mem_latT_iff]
    refine forall_congr' fun s => exists_congr fun c => ?_
    rw [← Q.integers.hom_inj.eq_iff, ← Q.pairV_bLie, hy, map_smul, LinearMap.smul_apply, map_mul, hpow, smul_eq_mul,
      mul_right_inj' (pow_ne_zero m hp0), eq_comm]
  rw [mem_latHT_iff]
  constructor
  · rintro ⟨z, hz, m, vO, hO, hs, hD⟩
    haveI : IsDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 Q.integers.hom_inj).le.trans bot_le)⟩
    obtain rfl : z = yb := ext_of_isDominant _ hz
    obtain ⟨y', rfl⟩ := TanPair.exists_lieG hπ hO
    obtain ⟨y, rfl⟩ := Q.lieCmp.surjective y'
    have h₁ := ((lieTie_iff π y _).2 hs).scale ((p : 𝓞_ℂ_[p]) ^ k)
    have h₂ := h₀.scale ((p : 𝓞_ℂ_[p]) ^ m)
    rw [← Category.assoc, epsMul_comp, hpow] at h₁ h₂
    rw [mul_comm] at h₂
    have e := congrArg Q.bLie (h₁.unique hψ.1 h₂)
    rw [Q.bLie_scale, Q.bLie_scale, e₀, ← algebraMap_smul ℂ_[p], ← algebraMap_smul ℂ_[p] ((p : 𝓞_ℂ_[p]) ^ m), hpow, hpow,
      smul_comm] at e
    exact (hd m y (smul_right_injective _ (pow_ne_zero k hp0) e)).1 hD
  · intro h
    exact ⟨yb, rfl, k, _, TanPair.isTanAtG_lieG hπ (Q.lieCmp _), (lieTie_iff π _ _).1 h₀, (hd k _ e₀).2 h⟩

end GlobalTheory.DetHT.Bridge

end
