import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator
import Formalism.FrobeniusOrbits.HostCorollaries

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

namespace D7

def sgnN {p N : ℕ} (hp : p.Prime) (h : p ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  haveI := Fact.mk hp
  (quadraticChar (ZMod p)).toUnitHom.comp (ZMod.unitsMap h)

/- English proof (translation)
Rewrite using `[ZMod.unitsMap_def, Units.coe_map]`. Use `show ZMod.castHom h (ZMod M) (u : ZMod N) = _`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val]`.
-/
theorem unitsMap_val {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (((u : ZMod N).val : ℕ) : ZMod M) := by
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[ZMod.unitsMap_def, Units.coe_map]`. Use `show ZMod.castHom h (ZMod M) (-1) = -1`. Rewrite using `[map_neg, map_one]`.
-/
theorem unitsMap_neg_one {M N : ℕ} (h : M ∣ N) : ZMod.unitsMap h (-1) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (-1) = -1
  rw [map_neg, map_one]

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← unitsMap_val h u]`. Conclude with `MulChar.coe_toUnitHom _ _`.
-/
theorem sgnN_val {p N : ℕ} [NeZero N] (hp : p.Prime) (h : p ∣ N) (u : (ZMod N)ˣ) :
    ((sgnN hp h u : ℤˣ) : ℤ) = jacobiSym (((u : ZMod N).val : ℕ) : ℤ) p := by
  have := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← unitsMap_val h u]
  exact MulChar.coe_toUnitHom _ _

/- English proof (translation)
Use `set w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv with hw`. Establish `hwv : (w : ZMod p) = (v : ZMod p)` using `ZMod.coe_unitOfCoprime v hv`. Establish `hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx ((w : ZMod p) * a)`. Introduce `a`. Rewrite using `[AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]`.

Establish `: (w : ZMod p) * a = (((v * a.val : ℕ)) : ZMod p)` using `by push_cast; rw [hwv, ZMod.natCast_zmod_val]`. Rewrite using `[this, AddChar.zmodChar_apply']`. Establish `hχ : ∀ a : ZMod p, σ (Cond.chi p K a) = Cond.chi p K a`. Introduce `a`. Simplify using `[Cond.chi, MulChar.ringHomComp_apply]`.

Establish `h1 : σ (Cond.gs p hx) = gaussSum (Cond.chi p K) (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p))`. Simplify using `only [Cond.gs, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]`. Establish `h2` using `gaussSum_mulShift (Cond.chi p K) (AddChar.zmodChar p hx) w`. Establish `h3 : Cond.chi p K (w : ZMod p) = ((jacobiSym (v : ℤ) p : ℤ) : K)`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hwv]`.

Both sides reduce to the same expression. Establish `h4 : jacobiSym (v : ℤ) p ^ 2 = 1` using `jacobiSym.sq_one (by simpa using hv)`. Establish `h5 : ((jacobiSym (v : ℤ) p : ℤ) : K) ^ 2 = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → K) h4`. Rewrite `h2` using `[h3, ← h1]`. Establish `h6 : Cond.gs p hx = ((jacobiSym (v : ℤ) p : ℤ) : K) * σ (Cond.gs p hx)` using `h2.symm`.

Take the linear combination `(-σ (Cond.gs p hx)) * h5 - ((jacobiSym (v : ℤ) p : ℤ) : K) * h6`.
-/
theorem gs_act {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : Nat.Coprime v p) :
    σ (Cond.gs p hx) = ((jacobiSym (v : ℤ) p : ℤ) : K) * Cond.gs p hx := by
  set w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv with hw
  have hwv : (w : ZMod p) = (v : ZMod p) := ZMod.coe_unitOfCoprime v hv
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx ((w : ZMod p) * a) := by
    intro a
    rw [AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]
    have : (w : ZMod p) * a = (((v * a.val : ℕ)) : ZMod p) := by
      push_cast; rw [hwv, ZMod.natCast_zmod_val]
    rw [this, AddChar.zmodChar_apply']
  have hχ : ∀ a : ZMod p, σ (Cond.chi p K a) = Cond.chi p K a := by
    intro a; simp [Cond.chi, MulChar.ringHomComp_apply]
  have h1 : σ (Cond.gs p hx) = gaussSum (Cond.chi p K) (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := by
    simp only [Cond.gs, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]
  have h2 := gaussSum_mulShift (Cond.chi p K) (AddChar.zmodChar p hx) w
  have h3 : Cond.chi p K (w : ZMod p) = ((jacobiSym (v : ℤ) p : ℤ) : K) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hwv]
    rfl
  have h4 : jacobiSym (v : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa using hv)
  have h5 : ((jacobiSym (v : ℤ) p : ℤ) : K) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) h4
  rw [h3, ← h1] at h2
  have h6 : Cond.gs p hx = ((jacobiSym (v : ℤ) p : ℤ) : K) * σ (Cond.gs p hx) := h2.symm
  linear_combination (-σ (Cond.gs p hx)) * h5 - ((jacobiSym (v : ℤ) p : ℤ) : K) * h6

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hx` using `Cond.prim_pow (N := N) h`. Establish `hxN : (Cond.z N ^ (N / p)) ^ N = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, (Cond.z_spec N).pow_eq_one, one_pow]`. Establish `hg` using `gs_act hx.pow_eq_one (τ : Cond.Cyc N →+* Cond.Cyc N) _ (hτ _ hxN) ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h)`.

Establish `hg' : τ (Cond.gs p hx.pow_eq_one) = _` using `hg`. Rewrite using `[sgnN_val]`. Establish `hsq : y ^ 2 = Cond.gs p hx.pow_eq_one ^ 2` using `by rw [hy, Cond.gs_sq hp4 hx]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1` into its components or cases. Rewrite using `[h1, hg']`.

Rewrite using `[h1, map_neg, hg']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrt_act {p N : ℕ} [NeZero N] (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) (u : (ZMod N)ˣ)
    (τ : Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) (hτ : ∀ w : Cond.Cyc N, w ^ N = 1 → τ w = w ^ (u : ZMod N).val)
    (y : Cond.Cyc N) (hy : y ^ 2 = -(p : Cond.Cyc N)) :
    τ y = (((sgnN hp h u : ℤˣ) : ℤ) : Cond.Cyc N) * y := by
  have := Fact.mk hp
  have hx := Cond.prim_pow (N := N) h
  have hxN : (Cond.z N ^ (N / p)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (Cond.z_spec N).pow_eq_one, one_pow]
  have hg := gs_act hx.pow_eq_one (τ : Cond.Cyc N →+* Cond.Cyc N) _ (hτ _ hxN)
    ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h)
  have hg' : τ (Cond.gs p hx.pow_eq_one) = _ := hg
  rw [sgnN_val]
  have hsq : y ^ 2 = Cond.gs p hx.pow_eq_one ^ 2 := by rw [hy, Cond.gs_sq hp4 hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · rw [h1, hg']
  · rw [h1, map_neg, hg']; ring

variable (φ : Frame) (hinj : Function.Injective φ.h)

def hIso : φ.MA ≃* HGrp φ.e :=
  MulEquiv.ofBijective φ.hH
    ⟨fun _ _ hab => Multiplicative.toAdd.injective (hinj (Additive.toMul.injective hab)),
     fun y => by
      obtain ⟨t, ht⟩ := φ.h_surj (Additive.ofMul y)
      exact ⟨Multiplicative.ofAdd t, congrArg Additive.toMul ht⟩⟩

def ggIso : FrobeniusOrbits.GG φ.e ≃* φ.GG := MulEquiv.prodCongr (MulEquiv.refl G0) (hIso φ hinj).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ggIso_fst (g : FrobeniusOrbits.GG φ.e) : (ggIso φ hinj g).1 = g.1 := rfl

/- English proof (translation)
The claim follows from `(hIso φ hinj).apply_symm_apply g.2`.
-/
theorem hH_ggIso (g : FrobeniusOrbits.GG φ.e) : φ.hH (ggIso φ hinj g).2 = g.2 := (hIso φ hinj).apply_symm_apply g.2

/- English proof (translation)
The claim follows from `Prod.ext rfl (map_one (hIso φ hinj).symm)`.
-/
theorem ggIso_mk_one (s : G0) : ggIso φ hinj (s, 1) = (s, 1) :=
  Prod.ext rfl (map_one (hIso φ hinj).symm)

/- English proof (translation)
Rewrite using `[← ggIso_mk_one φ hinj s]`. Conclude with `(ggIso φ hinj).injective.eq_iff`.
-/
theorem ggIso_eq_iff (g : FrobeniusOrbits.GG φ.e) (s : G0) : ggIso φ hinj g = (s, 1) ↔ g = (s, 1) := by
  rw [← ggIso_mk_one φ hinj s]
  exact (ggIso φ hinj).injective.eq_iff

include hinj in
/- English proof (translation)
Establish `h1` using `Nat.card_congr (hIso φ hinj).toEquiv`. Rewrite `h1` using `[(hostGroup φ.e).2.2.2.2.2.2.1]`. Rewrite using `[← h1, ← φ.natCard_A]`. Conclude with `Nat.card_congr Multiplicative.ofAdd`.
-/
theorem ord_eq : φ.ord = 2 ^ φ.e := by
  have h1 := Nat.card_congr (hIso φ hinj).toEquiv
  rw [(hostGroup φ.e).2.2.2.2.2.2.1] at h1
  rw [← h1, ← φ.natCard_A]
  exact Nat.card_congr Multiplicative.ofAdd

section Art

variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)

/- English proof (translation)
The claim follows from `Dvd.intro _ (mul_assoc _ _ _).symm`.
-/
theorem two_dvd (q d : ℕ) : 2 ^ (e + 2) ∣ 2 ^ (e + 2) * q * d := Dvd.intro _ (mul_assoc _ _ _).symm
/- English proof (translation)
The claim follows from `Dvd.dvd.mul_right (dvd_mul_left _ _) _`.
-/
theorem q_dvd (q d : ℕ) : q ∣ 2 ^ (e + 2) * q * d := Dvd.dvd.mul_right (dvd_mul_left _ _) _
/- English proof (translation)
The claim follows from `dvd_mul_left _ _`.
-/
theorem d_dvd (q d : ℕ) : d ∣ 2 ^ (e + 2) * q * d := dvd_mul_left _ _

include hH in
/- English proof (translation)
Assemble the required witnesses or components as `⟨by have := hH.1.pos; have := hH.2.1.pos; positivity⟩`.
-/
theorem neZeroN : NeZero (2 ^ (e + 2) * q * d) :=
  ⟨by have := hH.1.pos; have := hH.2.1.pos; positivity⟩

def art0 : (ZMod (2 ^ (e + 2) * q * d))ˣ →* FrobeniusOrbits.GG e :=
  ((sgnN hH.1 (q_dvd e q d)).prod (sgnN hH.2.1 (d_dvd e q d))).prod
    ((QuotientGroup.mk' _).comp (ZMod.unitsMap (two_dvd e q d)))

/- English proof (translation)
The claim follows from `haveI := neZeroN e hH sgnN_val hH.1 (q_dvd e q d) u`.
-/
theorem artinMap_first_eq_jacobiSym (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) :
    (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ℤ) q :=
  haveI := neZeroN e hH
  sgnN_val hH.1 (q_dvd e q d) u

/- English proof (translation)
The claim follows from `haveI := neZeroN e hH sgnN_val hH.2.1 (d_dvd e q d) u`.
-/
theorem artinMap_second_eq_jacobiSym (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) :
    (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ℤ) d :=
  haveI := neZeroN e hH
  sgnN_val hH.2.1 (d_dvd e q d) u

/- English proof (translation)
Use `neZeroN e hH` as an intermediate fact. Establish `h1 : v = ZMod.unitsMap (two_dvd e q d) u` using `Units.ext (by rw [hv, unitsMap_val])`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem artinMap_dyadic_eq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ZMod (2 ^ (e + 2)))) :
    (art0 e hH u).2 = hcl e v := by
  have := neZeroN e hH
  have h1 : v = ZMod.unitsMap (two_dvd e q d) u := Units.ext (by rw [hv, unitsMap_val])
  rw [h1]; rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[artinMap_first_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]`. Both sides reduce to the same expression.
-/
theorem artinMap_first_eq_one (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q]) :
    (art0 e hH u).1.1 = 1 := by
  apply Units.ext
  rw [artinMap_first_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[artinMap_second_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]`. Both sides reduce to the same expression.
-/
theorem artinMap_second_eq_one (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d]) :
    (art0 e hH u).1.2 = 1 := by
  apply Units.ext
  rw [artinMap_second_eq_jacobiSym, jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr hu), jacobiSym.one_left]
  rfl

/- English proof (translation)
Rewrite using `[artinMap_dyadic_eq e hH u 1 (by rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hu]; simp), hcl_one]`.
-/
theorem artinMap_dyadic_eq_one (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)]) : (art0 e hH u).2 = 1 := by
  rw [artinMap_dyadic_eq e hH u 1 (by rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hu]; simp), hcl_one]

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) = -1`. Rewrite using `[unitsMap_neg_one]`. Both sides reduce to the same expression.

Establish `h2 : ((sgnN hp h (-1) : ℤˣ) : ℤ) = quadraticChar (ZMod p) ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p)` using `MulChar.coe_toUnitHom _ _`. Rewrite using `[h2, h1, quadraticChar_neg_one (Cond.ringChar_ne_two hp4), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]`. Both sides reduce to the same expression.
-/
theorem sgnN_neg_one {p N : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) : sgnN hp h (-1) = -1 := by
  have := Fact.mk hp
  apply Units.ext
  have h1 : ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [unitsMap_neg_one]; rfl
  have h2 : ((sgnN hp h (-1) : ℤˣ) : ℤ) = quadraticChar (ZMod p) ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) :=
    MulChar.coe_toUnitHom _ _
  rw [h2, h1, quadraticChar_neg_one (Cond.ringChar_ne_two hp4), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  rfl

/- English proof (translation)
Establish `hq4 : q % 4 = 3` using `by have := hH.2.2.1; omega`. Establish `hd4 : d % 4 = 3` using `by have := hH.2.2.2.1; omega`. Use `Prod.ext (Prod.ext (sgnN_neg_one hH.1 hq4 _) (sgnN_neg_one hH.2.1 hd4 _)) ?_` and prove the remaining obligations. Establish `h1 : ZMod.unitsMap (two_dvd e q d) (-1) = -1` using `unitsMap_neg_one _`. Use `show hcl e (ZMod.unitsMap (two_dvd e q d) (-1)) = 1`.

Rewrite using `[h1, hcl_neg_one]`.
-/
theorem artinMap_neg_one : art0 e hH (-1) = cc e := by
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  refine Prod.ext (Prod.ext (sgnN_neg_one hH.1 hq4 _) (sgnN_neg_one hH.2.1 hd4 _)) ?_
  have h1 : ZMod.unitsMap (two_dvd e q d) (-1) = -1 := unitsMap_neg_one _
  show hcl e (ZMod.unitsMap (two_dvd e q d) (-1)) = 1
  rw [h1, hcl_neg_one]

variable {e} {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b)

def layerEmb : L →ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d) :=
  haveI := neZeroN e hH
  haveI := Fact.mk hH.1
  haveI := Fact.mk hH.2.1
  Classical.choice (Cond.layer_emb (by have := hH.2.2.1; omega) (by have := hH.2.2.2.1; omega) h
    (two_dvd e q d) (q_dvd e q d) (d_dvd e q d))

include h in
/- English proof (translation)
Use `neZeroN e hH` as an intermediate fact. Establish `hqd` using `hH.toHypOdd`. Establish `hq4 : q % 4 = 3` using `by have := hH.2.2.1; omega`. Establish `hd4 : d % 4 = 3` using `by have := hH.2.2.2.1; omega`. Establish `key : (ι.comp (hostE ζ a b).val).comp (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b) = (τ : _ →ₐ[ℚ] _).comp (ι.comp (hostE ζ a b).val)`.

Use `algHom_ext_of_eq_adjoin ℚ (S := hostE ζ a b) (s := {ζ + ζ⁻¹, a, b}) (hostFixed e q d hqd L ζ a b h).1 ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy`. Break down `hy with rfl | hy | hy` into its components or cases. Use `show ι ((σ (thE ζ a b) : hostE ζ a b) : L) = τ (ι (ζ + ζ⁻¹)) set v := ZMod.unitsMap (two_dvd e q d) u with hv`.

Establish `h1` using `(galE_snd_eq_hcl_iff hqd h σ v).mp (by rw [hσ]; rfl)`. Establish `hz : ζ ^ 2 ^ (e + 2) = 1` using `h.1.pow_eq_one`. Establish `hz' : ζ⁻¹ ^ 2 ^ (e + 2) = 1` using `by rw [inv_pow, hz, inv_one]`. Establish `hval : (v : ZMod (2 ^ (e + 2))).val = (u : ZMod (2 ^ (e + 2) * q * d)).val % 2 ^ (e + 2)`. Rewrite using `[hv, unitsMap_val, ZMod.val_natCast]`.

Establish `hN : ∀ w : L, w ^ 2 ^ (e + 2) = 1 → ι w ^ (2 ^ (e + 2) * q * d) = 1`. Introduce `w hw`. Rewrite using `[pow_mul, pow_mul, ← map_pow, hw, map_one, one_pow, one_pow]`. Rewrite using `[h1, hval, Cond.pow_mod_of hz, Cond.pow_mod_of hz', map_add, map_add, map_add, map_pow, map_pow, hτ _ (hN _ hz), hτ _ (hN _ hz')]`. Substitute `hy show ι ((σ (aE ζ y b) : hostE ζ y b) : L) = τ (ι y)` using the available equality.

Rewrite using `[galE_aE hqd h σ, hσ, map_mul, map_intCast, sqrt_act hH.1 hq4 (q_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.1, map_neg, map_natCast])]`. Both sides reduce to the same expression. Substitute `hy show ι ((σ (bE ζ a y) : hostE ζ a y) : L) = τ (ι y)` using the available equality. Rewrite using `[galE_bE hqd h σ, hσ, map_mul, map_intCast, sqrt_act hH.2.1 hd4 (d_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.2.1, map_neg, map_natCast])]`. Both sides reduce to the same expression.

Conclude with `DFunLike.congr_fun key x`.
-/
theorem algEquiv_apply_eq_tau_of_galE_eq_art0 (ι : L →ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d)) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (τ : Cond.Cyc (2 ^ (e + 2) * q * d) ≃ₐ[ℚ] Cond.Cyc (2 ^ (e + 2) * q * d))
    (hτ : ∀ w : Cond.Cyc (2 ^ (e + 2) * q * d), w ^ (2 ^ (e + 2) * q * d) = 1 →
      τ w = w ^ (u : ZMod (2 ^ (e + 2) * q * d)).val)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ = art0 e hH u) (x : hostE ζ a b) :
    ι ((σ x : hostE ζ a b) : L) = τ (ι (x : L)) := by
  have := neZeroN e hH
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have key : (ι.comp (hostE ζ a b).val).comp (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b) =
      (τ : _ →ₐ[ℚ] _).comp (ι.comp (hostE ζ a b).val) := by
    refine algHom_ext_of_eq_adjoin ℚ (S := hostE ζ a b) (s := {ζ + ζ⁻¹, a, b})
      (hostFixed e q d hqd L ζ a b h).1 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | hy | hy
    · show ι ((σ (thE ζ a b) : hostE ζ a b) : L) = τ (ι (ζ + ζ⁻¹))
      set v := ZMod.unitsMap (two_dvd e q d) u with hv
      have h1 := (galE_snd_eq_hcl_iff hqd h σ v).mp (by rw [hσ]; rfl)
      have hz : ζ ^ 2 ^ (e + 2) = 1 := h.1.pow_eq_one
      have hz' : ζ⁻¹ ^ 2 ^ (e + 2) = 1 := by rw [inv_pow, hz, inv_one]
      have hval : (v : ZMod (2 ^ (e + 2))).val = (u : ZMod (2 ^ (e + 2) * q * d)).val % 2 ^ (e + 2) := by
        rw [hv, unitsMap_val, ZMod.val_natCast]
      have hN : ∀ w : L, w ^ 2 ^ (e + 2) = 1 → ι w ^ (2 ^ (e + 2) * q * d) = 1 := by
        intro w hw
        rw [pow_mul, pow_mul, ← map_pow, hw, map_one, one_pow, one_pow]
      rw [h1, hval, Cond.pow_mod_of hz, Cond.pow_mod_of hz', map_add, map_add, map_add, map_pow, map_pow,
        hτ _ (hN _ hz), hτ _ (hN _ hz')]
    · subst hy
      show ι ((σ (aE ζ y b) : hostE ζ y b) : L) = τ (ι y)
      rw [galE_aE hqd h σ, hσ, map_mul, map_intCast,
        sqrt_act hH.1 hq4 (q_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.1, map_neg, map_natCast])]
      rfl
    · subst hy
      show ι ((σ (bE ζ a y) : hostE ζ a y) : L) = τ (ι y)
      rw [galE_bE hqd h σ, hσ, map_mul, map_intCast,
        sqrt_act hH.2.1 hd4 (d_dvd e q d) u τ hτ (ι y) (by rw [← map_pow, h.2.2.1, map_neg, map_natCast])]
      rfl
  exact DFunLike.congr_fun key x

end Art

/- English proof (translation)
Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_two_left, Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]`. Use `hH.2.2.1` as an intermediate fact. Use `hH.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem coprime_two {q d : ℕ} (hH : HostHyp q d) (k : ℕ) : Nat.Coprime (2 ^ k) (q * d) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_two_left, Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega

variable {q d : ℕ} (hH : HostHyp q d) (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (φ.e + 2) q d ζ a b)

def hostRaw : HostRaw φ where
  q := q
  d := d
  QS := 2 ^ (φ.e + 2)
  hyp := hH
  two_le_e := he
  QS_pos := by positivity
  tower_dvd := dvd_rfl
  QS_coprime := coprime_two hH _
  QS_split := fun l hl hl2 hd => absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hd)) hl2
  E := hostE ζ a b
  galois := hostE_isGalois hH.toHypOdd h
  gal := (galEquiv hH.toHypOdd h).trans (ggIso φ hinj)
  sqd := bE ζ a b
  sqd_sq := by
    apply Subtype.ext
    push_cast
    exact h.2.2.1
  gal_sqd := fun σ => by
    apply Subtype.ext
    push_cast
    exact galE_bE hH.toHypOdd h σ
  cycEmb := (layerEmb hH h).comp (hostE ζ a b).val
  cycZeta := haveI := neZeroN φ.e hH; Cond.z _
  cycZeta_prim := haveI := neZeroN φ.e hH; Cond.z_spec _
  art := (ggIso φ hinj).toMonoidHom.comp (art0 φ.e hH)
  art_spec := fun u τ hτ x => by
    have := neZeroN φ.e hH
    refine algEquiv_apply_eq_tau_of_galE_eq_art0 hH h (layerEmb hH h) u τ (fun w hw => ?_) _ ?_ x
    · obtain ⟨i, -, rfl⟩ := (Cond.z_spec _).eq_pow_of_pow_eq_one hw
      rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm i]
    · apply (ggIso φ hinj).injective
      exact ((galEquiv hH.toHypOdd h).trans (ggIso φ hinj)).apply_symm_apply _
  art_neg_one := by
    show ggIso φ hinj (art0 φ.e hH (-1)) = _
    rw [artinMap_neg_one]
    exact ggIso_mk_one φ hinj c0
  art_h := fun u v hv => (hH_ggIso φ hinj _).trans (artinMap_dyadic_eq φ.e hH u v hv)
  art_d := fun u hu => by
    have h1 := artinMap_first_eq_one φ.e hH u (hu.of_dvd (dvd_mul_left _ _))
    have h2 := artinMap_dyadic_eq_one φ.e hH u (hu.of_dvd (dvd_mul_right _ _))
    rcases Int.units_eq_one_or (art0 φ.e hH u).1.2 with h3 | h3
    · exact Or.inl ((ggIso_eq_iff φ hinj _ 1).mpr (Prod.ext (Prod.ext h1 h3) h2))
    · exact Or.inr ((ggIso_eq_iff φ hinj _ (1, -1)).mpr (Prod.ext (Prod.ext h1 h3) h2))
  art_q := fun u hu => by
    have h2 := artinMap_dyadic_eq_one φ.e hH u (hu.of_dvd (dvd_mul_right _ _))
    show ggIso φ hinj (art0 φ.e hH u) ^ 2 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (art0 φ.e hH u).2 ^ 2 = 1
    rw [h2, one_pow]

end D7

end Formalism.HC

end
