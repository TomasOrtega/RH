import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

namespace KumUniq

/- English proof (translation)
Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`. Establish `e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M)` using `fun x => map_intCast _ x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, h1, map_one]`.

Rewrite using `[← e, h2, map_zero]`. Rewrite using `[← e, h3, map_zero]`. Rewrite using `[← e, h4, map_one]`.
-/
theorem gamma_mem_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

end KumUniq

open KumUniq

/- English proof (translation)
Introduce `Ω _ _ ε X l _ n x χ χ' hK hK'`. Take `⟨hH, hmul, hone, hdiff, -, -⟩` from `GlobalTheory.T.glTwoPosRatMobius_basic_laws`. Take `⟨G1, G2, G3, -, G5⟩` from `GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties`. Take `⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hχ⟩` from `hK`. Take `⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hab'⟩, hχ'⟩` from `hK'`.

Establish `hl : l.Prime` using `Fact.out`. Establish `hm : 0 < l ^ n` using `pow_pos hl.pos n`. Take `⟨g, hfg⟩` from `((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.1 f f').1 (hx.symm.trans hx')`. Take `⟨p, q, hp, hq, hq0, hpq⟩` from `X.an_mero (g : X.K)`. Take `⟨M'', hM'', hlev⟩` from `X.level (g : X.K)`.

Establish `nz : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → ∃ z ∈ Hs, u z ≠ 0`. Introduce `u hu hu0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hu0 (((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 hc).trans Filter.Germ.coe_zero)`.

Establish `unz : ∀ (h : X.Kˣ) (u : ℂ → ℂ) (v : Mero) (k : ℕ), k ≠ 0 → X.an (h : X.K) * (u : Mero) ^ k = v → DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → v ≠ 0`. Introduce `h u v k hk heq hu hu0 hv0`. Establish `h0 : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero)`. Establish `e : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = (u : Mero) ^ k` using `Filter.Germ.coe_pow u k`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `(G1 _ _ (hu.pow k) (differentiableOn_const 0)).1 h0`. Apply `hu0` to reduce the goal to its premises. Use `((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 fun z hz => ?_).trans Filter.Germ.coe_zero` and prove the remaining obligations. Conclude with `pow_eq_zero_iff hk |>.1 (h1 z hz)`.

Establish `nzmul : ∀ u v : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ v Hs → (∃ z ∈ Hs, u z ≠ 0) → (∃ z ∈ Hs, v z ≠ 0) → ∃ z ∈ Hs, u z * v z ≠ 0`. Introduce and unpack `u v hu hv ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Break down `G2 u v hu hv hc with h | h` into its components or cases.

Conclude with `h1 (h z1 hz1)`. Conclude with `h2 (h z2 hz2)`. Establish `hf : X.an (f : X.K) = X.an (f' : X.K) * X.an (g : X.K) ^ (l ^ n)`. Rewrite using `[hfg, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Establish `key : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero)`.

Establish `e1 : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a : Mero) * b' * q) ^ (l ^ n)`. Rewrite using `[← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]`. Both sides reduce to the same expression. Establish `e2 : ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a' : Mero) * b * p) ^ (l ^ n)`. Rewrite using `[← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, ← hpq]`. Take the linear combination `(-((b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n))) * hab + ((b : Mero) ^ (l ^ n) * (b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hf + ((b : Mero) ^ (l ^ n) * (X.an (g : X.K)) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hab'`. Establish `key'` using `(G1 _ _ (((ha.mul hb').mul hq).pow (l ^ n)) (((ha'.mul hb).mul hp).pow (l ^ n))).1 key`. Take `⟨k, hk⟩` from `G5 (l ^ n) (fun z => a z * b' z * q z) (fun z => a' z * b z * p z) hm ((ha.mul hb').mul hq) ((ha'.mul hb).mul hp) key'`.

Take `⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (g : X.K) = (φ : Mero)` from `Filter.Germ.inductionOn (X.an (g : X.K)) (p := fun F => ∃ φ : ℂ → ℂ, F = (φ : Mero)) fun φ => ⟨φ, rfl⟩`. Establish `hmap : ∀ γ : SL(2, ℤ), Set.MapsTo (mob (ofSL γ)) Hs Hs` using `fun γ z hz => hH _ z hz`. Establish `hpqδ : ∀ δ ∈ CongruenceSubgroup.Gamma M'', ∀ z ∈ Hs, p (mob (ofSL δ) z) * q z = p z * q (mob (ofSL δ) z)`. Introduce `δ hδ`. Establish `h1 : (φ : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero)`.

Rewrite using `[← hφ, ← X.an_sl (ofSL δ) _ φ hφ, hlev δ hδ]`. Establish `h2 : ((fun z => φ z * q z : ℂ → ℂ) : Mero) = (p : Mero)`. Rewrite using `[← hpq, hφ]`. Conclude with `Filter.Germ.coe_mul φ q`. Establish `h3` using `G3 (ofSL δ) _ _ h2`.

Establish `e3 : ((fun z => φ (mob (ofSL δ) z) * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero)` using `Filter.Germ.coe_mul _ _`. Establish `h2' : (φ : Mero) * (q : Mero) = (p : Mero)` using `by rw [← h2]; exact (Filter.Germ.coe_mul φ q).symm`. Establish `h3' : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero)` using `by rw [← e3]; exact h3`. Establish `hpδ : DifferentiableOn ℂ (fun z => p (mob (ofSL δ) z)) Hs` using `hp.comp (hdiff _) (hmap δ)`. Establish `hqδ : DifferentiableOn ℂ (fun z => q (mob (ofSL δ) z)) Hs` using `hq.comp (hdiff _) (hmap δ)`.

Use `(G1 (fun z => p (mob (ofSL δ) z) * q z) (fun z => p z * q (mob (ofSL δ) z)) (hpδ.mul hq) (hp.mul hqδ)).1 ?_` and prove the remaining obligations. Establish `e4 : ((fun z => p (mob (ofSL δ) z) * q z : ℂ → ℂ) : Mero) = ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * (q : Mero)` using `Filter.Germ.coe_mul _ _`. Establish `e5 : ((fun z => p z * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = (p : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero)` using `Filter.Germ.coe_mul _ _`. Rewrite using `[e4, e5]`. Take the linear combination `(-((q : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero))) * h1 + ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * h2' + (-(q : Mero)) * h3'`.

Use `⟨M * M' * M'', by positivity, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `hδ1 : δ ∈ CongruenceSubgroup.Gamma M` using `gamma_mem_of_dvd (Dvd.intro (M' * M'') (by ring)) hδ`. Establish `hδ2 : δ ∈ CongruenceSubgroup.Gamma M'` using `gamma_mem_of_dvd (Dvd.intro (M * M'') (by ring)) hδ`. Establish `hδ3 : δ ∈ CongruenceSubgroup.Gamma M''` using `gamma_mem_of_dvd (Dvd.intro_left (M * M') rfl) hδ`. Use `set e1 := Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) with he1`.

Use `set e2 := Complex.exp (2 * Real.pi * Complex.I * ((χ' δ).val : ℂ) / ((l : ℂ) ^ n)) with he2`. Use `set ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) with hζ`. Establish `hP : ∀ z ∈ Hs, (e1 - e2) * (a z * a' z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * p (mob (ofSL δ) z) * q z) = 0`. Introduce `z hz`. Establish `hw` using `hH (ofSL δ) z hz`.

Establish `K1` using `hχ δ hδ1 z hz`. Establish `K2` using `hχ' δ hδ2 z hz`. Establish `K3` using `hpqδ δ hδ3 z hz`. Establish `Dz : a z * b' z * q z = ζ * (a' z * b z * p z)` using `hk z hz`. Establish `Dw : a (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) = ζ * (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z))` using `hk _ hw`.

Take the linear combination `(a' z * b z * p z) * Dw - (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * Dz - (b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) * a' z * p z) * K1 + e1 * (a z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * a' z) * K3 + (a z * q z * b (mob (ofSL δ) z) * p (mob (ofSL δ) z) …`. Establish `nzδ : ∀ u : ℂ → ℂ, (∃ z ∈ Hs, u z ≠ 0) → ∃ z ∈ Hs, u (mob (ofSL δ) z) ≠ 0`. Introduce and unpack `u ⟨z, hz, hu⟩`. Use `⟨mob (ofSL δ⁻¹) z, hH _ z hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmul _ _ z hz, ← map_mul, mul_inv_cancel, map_one, hone]` and apply the resulting hypothesis.

Establish `dδ : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ (fun z => u (mob (ofSL δ) z)) Hs` using `fun u hu => hu.comp (hdiff _) (hmap δ)`. Establish `na : ∃ z ∈ Hs, a z ≠ 0` using `nz a ha fun h0 => unz f b _ (l ^ n) hm.ne' hab hb hb0 (by rw [h0, zero_pow hm.ne'])`. Establish `na' : ∃ z ∈ Hs, a' z ≠ 0` using `nz a' ha' fun h0 => unz f' b' _ (l ^ n) hm.ne' hab' hb' hb0' (by rw [h0, zero_pow hm.ne'])`. Establish `np : ∃ z ∈ Hs, p z ≠ 0` using `nz p hp (unz g q _ 1 one_ne_zero (by rw [pow_one]; exact hpq) hq hq0)`. Take `⟨z0, hz0, hne⟩` from `nzmul _ _ ((((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')).mul (dδ p hp)) hq (nzmul _ _ (((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')) (dδ p hp) (nzmul _ _ ((ha.mul ha').mul (dδ b hb)) (dδ b' hb') (nzmul _ _ (ha.mul ha') (dδ b hb) (nzmul _ _ ha ha' na na') (nzδ b (nz b hb hb0))) ( …`.

Establish `he : e1 = e2`. Break down `mul_eq_zero.1 (hP z0 hz0) with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hne`. Use `haveI : NeZero (l ^ n) := ⟨hm.ne'⟩`.

Establish `hprim` using `Complex.isPrimitiveRoot_exp (l ^ n) hm.ne'`. Establish `ex : ∀ v : ℕ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ n)) = (Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ))) ^ v`. Introduce `v`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply `ZMod.val_injective (l ^ n)` to reduce the goal to its premises. Conclude with `hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← ex, ← ex]; exact he)`.
-/
theorem kum_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  intro Ω _ _ ε X l _ n x χ χ' hK hK'
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨G1, G2, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hχ⟩ := hK
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hab'⟩, hχ'⟩ := hK'
  have hl : l.Prime := Fact.out
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨g, hfg⟩ := ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.1 f f').1 (hx.symm.trans hx')
  obtain ⟨p, q, hp, hq, hq0, hpq⟩ := X.an_mero (g : X.K)
  obtain ⟨M'', hM'', hlev⟩ := X.level (g : X.K)

  have nz : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → ∃ z ∈ Hs, u z ≠ 0 := by
    intro u hu hu0
    by_contra hc
    push_neg at hc
    exact hu0 (((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 hc).trans Filter.Germ.coe_zero)

  have unz : ∀ (h : X.Kˣ) (u : ℂ → ℂ) (v : Mero) (k : ℕ), k ≠ 0 → X.an (h : X.K) * (u : Mero) ^ k = v →
      DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → v ≠ 0 := by
    intro h u v k hk heq hu hu0 hv0
    have h0 : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := by
      have e : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = (u : Mero) ^ k := Filter.Germ.coe_pow u k
      rw [e]
      calc (u : Mero) ^ k = X.an (((h⁻¹ : X.Kˣ) : X.K) * (h : X.K)) * (u : Mero) ^ k := by simp
        _ = X.an ((h⁻¹ : X.Kˣ) : X.K) * (X.an (h : X.K) * (u : Mero) ^ k) := by rw [map_mul, mul_assoc]
        _ = 0 := by rw [heq, hv0, mul_zero]
        _ = _ := Filter.Germ.coe_zero.symm
    have h1 := (G1 _ _ (hu.pow k) (differentiableOn_const 0)).1 h0
    apply hu0
    refine ((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 fun z hz => ?_).trans Filter.Germ.coe_zero
    exact pow_eq_zero_iff hk |>.1 (h1 z hz)

  have nzmul : ∀ u v : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ v Hs → (∃ z ∈ Hs, u z ≠ 0) →
      (∃ z ∈ Hs, v z ≠ 0) → ∃ z ∈ Hs, u z * v z ≠ 0 := by
    rintro u v hu hv ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    by_contra hc
    push_neg at hc
    rcases G2 u v hu hv hc with h | h
    · exact h1 (h z1 hz1)
    · exact h2 (h z2 hz2)

  have hf : X.an (f : X.K) = X.an (f' : X.K) * X.an (g : X.K) ^ (l ^ n) := by
    rw [hfg, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have key : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) =
      ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
    have e1 : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a : Mero) * b' * q) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    have e2 : ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a' : Mero) * b * p) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    rw [e1, e2, ← hpq]
    linear_combination (-((b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n))) * hab +
      ((b : Mero) ^ (l ^ n) * (b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hf +
      ((b : Mero) ^ (l ^ n) * (X.an (g : X.K)) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hab'
  have key' := (G1 _ _ (((ha.mul hb').mul hq).pow (l ^ n)) (((ha'.mul hb).mul hp).pow (l ^ n))).1 key
  obtain ⟨k, hk⟩ := G5 (l ^ n) (fun z => a z * b' z * q z) (fun z => a' z * b z * p z) hm
    ((ha.mul hb').mul hq) ((ha'.mul hb).mul hp) key'

  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (g : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (g : X.K)) (p := fun F => ∃ φ : ℂ → ℂ, F = (φ : Mero)) fun φ => ⟨φ, rfl⟩
  have hmap : ∀ γ : SL(2, ℤ), Set.MapsTo (mob (ofSL γ)) Hs Hs := fun γ z hz => hH _ z hz
  have hpqδ : ∀ δ ∈ CongruenceSubgroup.Gamma M'', ∀ z ∈ Hs,
      p (mob (ofSL δ) z) * q z = p z * q (mob (ofSL δ) z) := by
    intro δ hδ
    have h1 : (φ : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by
      rw [← hφ, ← X.an_sl (ofSL δ) _ φ hφ, hlev δ hδ]
    have h2 : ((fun z => φ z * q z : ℂ → ℂ) : Mero) = (p : Mero) := by
      rw [← hpq, hφ]; exact Filter.Germ.coe_mul φ q
    have h3 := G3 (ofSL δ) _ _ h2
    have e3 : ((fun z => φ (mob (ofSL δ) z) * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) :=
      Filter.Germ.coe_mul _ _
    have h2' : (φ : Mero) * (q : Mero) = (p : Mero) := by rw [← h2]; exact (Filter.Germ.coe_mul φ q).symm
    have h3' : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by rw [← e3]; exact h3
    have hpδ : DifferentiableOn ℂ (fun z => p (mob (ofSL δ) z)) Hs := hp.comp (hdiff _) (hmap δ)
    have hqδ : DifferentiableOn ℂ (fun z => q (mob (ofSL δ) z)) Hs := hq.comp (hdiff _) (hmap δ)
    refine (G1 (fun z => p (mob (ofSL δ) z) * q z) (fun z => p z * q (mob (ofSL δ) z))
      (hpδ.mul hq) (hp.mul hqδ)).1 ?_
    have e4 : ((fun z => p (mob (ofSL δ) z) * q z : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * (q : Mero) := Filter.Germ.coe_mul _ _
    have e5 : ((fun z => p z * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        (p : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := Filter.Germ.coe_mul _ _
    rw [e4, e5]
    linear_combination (-((q : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero))) * h1 +
      ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * h2' + (-(q : Mero)) * h3'

  refine ⟨M * M' * M'', by positivity, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ CongruenceSubgroup.Gamma M :=
    gamma_mem_of_dvd (Dvd.intro (M' * M'') (by ring)) hδ
  have hδ2 : δ ∈ CongruenceSubgroup.Gamma M' :=
    gamma_mem_of_dvd (Dvd.intro (M * M'') (by ring)) hδ
  have hδ3 : δ ∈ CongruenceSubgroup.Gamma M'' := gamma_mem_of_dvd (Dvd.intro_left (M * M') rfl) hδ
  set e1 := Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) with he1
  set e2 := Complex.exp (2 * Real.pi * Complex.I * ((χ' δ).val : ℂ) / ((l : ℂ) ^ n)) with he2
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) with hζ
  have hP : ∀ z ∈ Hs, (e1 - e2) * (a z * a' z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) *
      p (mob (ofSL δ) z) * q z) = 0 := by
    intro z hz
    have hw := hH (ofSL δ) z hz
    have K1 := hχ δ hδ1 z hz
    have K2 := hχ' δ hδ2 z hz
    have K3 := hpqδ δ hδ3 z hz
    have Dz : a z * b' z * q z = ζ * (a' z * b z * p z) := hk z hz
    have Dw : a (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) =
        ζ * (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) := hk _ hw
    linear_combination (a' z * b z * p z) * Dw
      - (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * Dz
      - (b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) * a' z * p z) * K1
      + e1 * (a z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * a' z) * K3
      + (a z * q z * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * K2

  have nzδ : ∀ u : ℂ → ℂ, (∃ z ∈ Hs, u z ≠ 0) → ∃ z ∈ Hs, u (mob (ofSL δ) z) ≠ 0 := by
    rintro u ⟨z, hz, hu⟩
    refine ⟨mob (ofSL δ⁻¹) z, hH _ z hz, ?_⟩
    rwa [← hmul _ _ z hz, ← map_mul, mul_inv_cancel, map_one, hone]
  have dδ : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ (fun z => u (mob (ofSL δ) z)) Hs :=
    fun u hu => hu.comp (hdiff _) (hmap δ)
  have na : ∃ z ∈ Hs, a z ≠ 0 := nz a ha fun h0 => unz f b _ (l ^ n) hm.ne' hab hb hb0 (by rw [h0, zero_pow hm.ne'])
  have na' : ∃ z ∈ Hs, a' z ≠ 0 := nz a' ha' fun h0 => unz f' b' _ (l ^ n) hm.ne' hab' hb' hb0' (by rw [h0, zero_pow hm.ne'])
  have np : ∃ z ∈ Hs, p z ≠ 0 := nz p hp (unz g q _ 1 one_ne_zero (by rw [pow_one]; exact hpq) hq hq0)
  obtain ⟨z0, hz0, hne⟩ := nzmul _ _ ((((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')).mul (dδ p hp)) hq
    (nzmul _ _ (((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')) (dδ p hp)
      (nzmul _ _ ((ha.mul ha').mul (dδ b hb)) (dδ b' hb')
        (nzmul _ _ (ha.mul ha') (dδ b hb) (nzmul _ _ ha ha' na na') (nzδ b (nz b hb hb0)))
        (nzδ b' (nz b' hb' hb0'))) (nzδ p np)) (nz q hq hq0)
  have he : e1 = e2 := by
    rcases mul_eq_zero.1 (hP z0 hz0) with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne

  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  have hprim := Complex.isPrimitiveRoot_exp (l ^ n) hm.ne'
  have ex : ∀ v : ℕ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ n)) =
      (Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ))) ^ v := by
    intro v
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply ZMod.val_injective (l ^ n)
  exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← ex, ← ex]; exact he)

end GlobalTheory.KZ.H3
