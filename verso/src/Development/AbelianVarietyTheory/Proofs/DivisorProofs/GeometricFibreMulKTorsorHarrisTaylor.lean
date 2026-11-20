import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.FibreMulK

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `h` using `I.add n 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, _root_.pow_zero]`.

Conclude with `mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)`. Consider the case `succ j ih => rw [succ_nsmul, I.add, ih, _root_.pow_succ]`.
-/
private theorem ev_nsmul' {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n j : ℕ) (y : D.La) :
    I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, _root_.pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, _root_.pow_succ]

/- English proof (translation)
Establish `hk' : (k : ℤ) ≠ 0` using `by exact_mod_cast hk.ne'`. Apply `smul_right_injective M hk'` to reduce the goal to its premises. Simplify `h` using `only [natCast_zsmul]`.
-/
private theorem nsmul_cancel {M : Type} [AddCommGroup M] [Module.Free ℤ M] {k : ℕ} (hk : 0 < k) {x y : M}
    (h : k • x = k • y) : x = y := by
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  apply smul_right_injective M hk'
  simpa only [natCast_zsmul] using h

/- English proof (translation)
Introduce `p _ D R _ b k N hk hN hkp hNp S s o K _ _ y y' hyy`. Use `set x : Sp K ⟶ S := y ≫ o.A.hom with hx`. Establish `hx' : y' ≫ o.A.hom = x`. Establish `e` using `congrArg (· ≫ o.A.hom) hyy`. Simplify using `only [Category.assoc, Over.w] at e`.

Conclude with `e.symm`. Set `T : Over S` to `Over.mk x`. Set `yt : T ⟶ o.A` to `Over.homMk y rfl`. Set `yt' : T ⟶ o.A` to `Over.homMk y' hx'`. Establish `hpow : yt ^ k = yt' ^ k`.

Establish `e : yt ≫ (𝟙 o.A) ^ k = yt' ≫ (𝟙 o.A) ^ k` using `Over.OverMorphism.ext hyy`. Rewrite `e` using `[comp_pow, comp_pow, Category.comp_id, Category.comp_id]`. Then use the resulting hypothesis. Use `set d : T ⟶ o.A := yt⁻¹ * yt' with hd`. Establish `hdk : d ^ k = 1` using `by rw [hd, mul_pow, inv_pow, hpow, inv_mul_cancel]`. Establish `hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom` using `(Spec.map_preimage _).symm`.

Take `⟨I, hI⟩` from `o.geom K x _ hβ`. Establish `hcop : (N * k * k).Coprime p` using `Nat.Coprime.mul (Nat.Coprime.mul hNp hkp) hkp`. Establish `hpos : 0 < N * k * k` using `Nat.mul_pos (Nat.mul_pos hN hk) hk`. Take `⟨z, hz⟩` from `(I.onto (N * k * k) hpos hcop d).1 (by`. Rewrite using `[pow_mul, pow_right_comm, hdk, one_pow])`.

Establish `hkz : I.ev (N * k * k) (k • z) = 1` using `by rw [ev_nsmul', hz, hdk]`. Take `⟨w, hw⟩` from `(I.ker (N * k * k) hpos hcop _).1 hkz`. Use `haveI := D.freeLa`. Establish `hzw : z = (N * k) • w`. Apply `nsmul_cancel hk` to reduce the goal to its premises.

Rewrite using `[hw, smul_smul, show k * (N * k) = N * k * k by ring]`. Establish `key : ∀ a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y' ↔ toUnit T ≫ a.1 = d`. Introduce `a`. Establish `e1 : yt ≫ transl a.1 = yt * (toUnit T ≫ a.1)`. Rewrite using `[transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (yt ≫ toUnit o.A) (toUnit T)]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e2 : yt ≫ transl a.1 = yt'` using `Over.OverMorphism.ext h`. Rewrite `e2` using `[e1]`. Rewrite using `[hd, ← e2, inv_mul_cancel_left]`.

Introduce `h`. Establish `e2 : yt ≫ transl a.1 = yt'` using `by rw [e1, h, hd, mul_inv_cancel_left]`. Conclude with `congrArg CommaMorphism.left e2`. Establish `hmem : o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) ∈ heckeSub o LinearMap.id (N * k)` using `mem_heckeSub o _ _ w`. Use `⟨⟨_, hmem⟩, (key _).2 ?_, ?_⟩` and prove the remaining obligations.

Use `show toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d`. Rewrite using `[LinearMap.id_apply, hI, ← hzw, hz]`. Introduce `a ha`. Establish `h1 : toUnit T ≫ a.1 = d` using `(key a).1 ha`. Establish `h2 : toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d`.

Rewrite using `[LinearMap.id_apply, hI, ← hzw, hz]`. Establish `hm : a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ ∈ heckeSub o LinearMap.id (N * k)` using `Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ hmem)`. Establish `h3 : toUnit T ≫ (a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹) = 1`. Establish `hi : toUnit T ≫ (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ = d⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[← h2, ← comp_mul, inv_mul_cancel, comp_one]`. Rewrite using `[comp_mul, h1, hi, mul_inv_cancel]`. Establish `h4` using `(heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp (Nat.Coprime.mul hNp hkp) S s o).2 K x _ hm h3`. Conclude with `Subtype.ext (mul_inv_eq_one.mp h4)`.
-/
theorem fibre_mulK : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  intro p _ D R _ b k N hk hN hkp hNp S s o K _ _ y y' hyy
  set x : Sp K ⟶ S := y ≫ o.A.hom with hx
  have hx' : y' ≫ o.A.hom = x := by
    have e := congrArg (· ≫ o.A.hom) hyy
    simp only [Category.assoc, Over.w] at e
    exact e.symm
  let T : Over S := Over.mk x
  let yt : T ⟶ o.A := Over.homMk y rfl
  let yt' : T ⟶ o.A := Over.homMk y' hx'
  have hpow : yt ^ k = yt' ^ k := by
    have e : yt ≫ (𝟙 o.A) ^ k = yt' ≫ (𝟙 o.A) ^ k := Over.OverMorphism.ext hyy
    rwa [comp_pow, comp_pow, Category.comp_id, Category.comp_id] at e
  set d : T ⟶ o.A := yt⁻¹ * yt' with hd
  have hdk : d ^ k = 1 := by rw [hd, mul_pow, inv_pow, hpow, inv_mul_cancel]
  have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
  obtain ⟨I, hI⟩ := o.geom K x _ hβ
  have hcop : (N * k * k).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hkp) hkp
  have hpos : 0 < N * k * k := Nat.mul_pos (Nat.mul_pos hN hk) hk
  obtain ⟨z, hz⟩ := (I.onto (N * k * k) hpos hcop d).1 (by
    rw [pow_mul, pow_right_comm, hdk, one_pow])
  have hkz : I.ev (N * k * k) (k • z) = 1 := by rw [ev_nsmul', hz, hdk]
  obtain ⟨w, hw⟩ := (I.ker (N * k * k) hpos hcop _).1 hkz
  haveI := D.freeLa
  have hzw : z = (N * k) • w := by
    apply nsmul_cancel hk
    rw [hw, smul_smul, show k * (N * k) = N * k * k by ring]
  have key : ∀ a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y' ↔ toUnit T ≫ a.1 = d := by
    intro a
    have e1 : yt ≫ transl a.1 = yt * (toUnit T ≫ a.1) := by
      rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (yt ≫ toUnit o.A) (toUnit T)]
    constructor
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := Over.OverMorphism.ext h
      rw [e1] at e2
      rw [hd, ← e2, inv_mul_cancel_left]
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := by rw [e1, h, hd, mul_inv_cancel_left]
      exact congrArg CommaMorphism.left e2
  have hmem : o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) ∈ heckeSub o LinearMap.id (N * k) :=
    mem_heckeSub o _ _ w
  refine ⟨⟨_, hmem⟩, (key _).2 ?_, ?_⟩
  · show toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d
    rw [LinearMap.id_apply, hI, ← hzw, hz]
  · intro a ha
    have h1 : toUnit T ≫ a.1 = d := (key a).1 ha
    have h2 : toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d := by
      rw [LinearMap.id_apply, hI, ← hzw, hz]
    have hm : a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ ∈ heckeSub o LinearMap.id (N * k) :=
      Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ hmem)
    have h3 : toUnit T ≫ (a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹) = 1 := by
      have hi : toUnit T ≫ (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ = d⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← h2, ← comp_mul, inv_mul_cancel, comp_one]
      rw [comp_mul, h1, hi, mul_inv_cancel]
    have h4 := (heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul hNp hkp) S s o).2 K x _ hm h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)

end GlobalTheory.UPel.HT.Hecke.FibreMulK
