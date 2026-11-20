import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SimilitudeLevel

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Set `red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N)` to `fun a i => (a i : ZMod N)`. Establish `red_zero : ∀ a : Fin h ⊕ Fin h → ℤ, red a = 0 ↔ ∃ b, a = N • b`. Introduce `a`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Use `⟨fun i => a i / N, funext fun i => ?_⟩` and prove the remaining obligations. Establish `hd : (N : ℤ) ∣ a i` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (a i) N).1 (congrFun ha i)`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Conclude with `(Int.mul_ediv_cancel' hd).symm`.

Introduce and unpack `⟨b, rfl⟩`. Use function extensionality and compare the values at `i`. Simplify using `[red]`. Establish `omega_smul : ∀ (b y : Fin h ⊕ Fin h → ℤ), omegaStd (N • b) y = N * omegaStd b y`. Introduce `b y`.

Simplify using `only [omegaStd, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul]`. Use `congr 1`. Use extensionality with `i`. Expand and normalize the polynomial expressions, which then agree. Establish `omega_inr : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i)`.

Introduce `a i`. Simplify using `[omegaStd, Pi.single_apply]`. Establish `omega_inl : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inl i) 1) = - a (Sum.inr i)`. Introduce `a i`. Simplify using `[omegaStd, Pi.single_apply]`.

Establish `hmN : IsCoprime (N : ℤ) m` using `Nat.isCoprime_iff_coprime.2 hm.symm`. Establish `kerN : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b`. Introduce and unpack `a ⟨b, hb⟩`. Establish `hdiv : ∀ y, (N : ℤ) ∣ omegaStd a y`. Introduce `y`.

Establish `h1 : (N : ℤ) ∣ omegaStd (T a) (T y)` using `by rw [hb, omega_smul]; exact dvd_mul_right _ _`. Establish `h2 : (N : ℤ) ∣ m * omegaStd a y`. Use `dvd_add (hT a y).dvd h1` as an intermediate fact. Simplify using `using this`. Conclude with `hmN.dvd_of_dvd_mul_left h2`.

Rewrite using `[← red_zero]`. Use function extensionality and compare the values at `j`. Break down `j with i | i` into its components or cases. Use `hdiv (Pi.single (Sum.inr i) 1)` as an intermediate fact. Rewrite `this` using `[omega_inr]`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this`. Use `hdiv (Pi.single (Sum.inl i) 1)` as an intermediate fact. Rewrite `this` using `[omega_inl, dvd_neg]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this`. Set `M : Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N` to `fun j i => (T (Pi.single j 1) i : ZMod N)`.

Set `TN : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ZMod N)` to `fun v i => ∑ j, v j * M j i`. Establish `hT_sum : ∀ a : Fin h ⊕ Fin h → ℤ, T a = ∑ j, a j • T (Pi.single j 1)`. Introduce `a`. Use `conv_lhs => rw [← Finset.univ_sum_single a]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Pi.single j (a j) = a j • (Pi.single j 1 : Fin h ⊕ Fin h → ℤ) by`. Apply the tactic sequence `ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi], map_smul]`. Establish `reduction_uniformizerPoint : ∀ a, red (T a) = TN (red a)`. Introduce `a`.

Use function extensionality and compare the values at `i`. Simplify using `only [red, TN, M]`. Rewrite using `[hT_sum a]`. Simplify using `[Finset.sum_apply]`. Set `lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ)` to `fun v i => ((v i).val : ℤ)`.

Establish `red_lift : ∀ v, red (lift v) = v` using `fun v => funext fun i => by simp [red, lift]`. Establish `TN_sub : ∀ v w, TN (v - w) = TN v - TN w`. Introduce `v w`. Use function extensionality and compare the values at `i`. Simplify using `only [TN, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`.

Establish `TN_inj : Function.Injective TN`. Introduce `v w hvw`. Establish `h0 : red (T (lift (v - w))) = 0` using `by rw [reduction_uniformizerPoint, red_lift, TN_sub, hvw, sub_self]`. Take `⟨b, hb⟩` from `kerN _ ((red_zero _).1 h0)`. Use `(red_zero _).2 ⟨b, hb⟩` as an intermediate fact.

Rewrite `this` using `[red_lift]`. Conclude with `sub_eq_zero.1 this`. Establish `TN_surj : Function.Surjective TN` using `Finite.injective_iff_surjective.1 TN_inj`. Use `⟨fun a => ⟨kerN a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun a' => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `TN_surj (red a')`.

Take `⟨c, hc⟩` from `(red_zero (a' - T (lift v))).1 (by`. Use function extensionality and compare the values at `i`. Use `congrFun (reduction_uniformizerPoint (lift v)) i` as an intermediate fact. Rewrite `this` using `[red_lift, hv]`. Simplify using `only [red, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at this ⊢`.

Rewrite using `[this, sub_self])`. Conclude with `⟨lift v, c, by rw [← hc]; abel⟩`.
-/
theorem similitude_bij_mod (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (hN : 0 < N)
    (hm : m.Coprime N) (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    (∀ a, (∃ b, T a = N • b) ↔ ∃ b, a = N • b) ∧ ∀ a', ∃ a c, a' = T a + N • c := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a i => (a i : ZMod N)
  have red_zero : ∀ a : Fin h ⊕ Fin h → ℤ, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    constructor
    · intro ha
      refine ⟨fun i => a i / N, funext fun i => ?_⟩
      have hd : (N : ℤ) ∣ a i := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) N).1 (congrFun ha i)
      simp only [Pi.smul_apply, nsmul_eq_mul]
      exact (Int.mul_ediv_cancel' hd).symm
    · rintro ⟨b, rfl⟩
      funext i
      simp [red]
  have omega_smul : ∀ (b y : Fin h ⊕ Fin h → ℤ), omegaStd (N • b) y = N * omegaStd b y := by
    intro b y
    simp only [omegaStd, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul]
    congr 1; ext i; ring
  have omega_inr : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have omega_inl : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inl i) 1) = - a (Sum.inr i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have hmN : IsCoprime (N : ℤ) m := Nat.isCoprime_iff_coprime.2 hm.symm
  have kerN : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hdiv : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have h1 : (N : ℤ) ∣ omegaStd (T a) (T y) := by rw [hb, omega_smul]; exact dvd_mul_right _ _
      have h2 : (N : ℤ) ∣ m * omegaStd a y := by
        have := dvd_add (hT a y).dvd h1
        simpa using this
      exact hmN.dvd_of_dvd_mul_left h2
    rw [← red_zero]
    funext j
    rcases j with i | i
    · have := hdiv (Pi.single (Sum.inr i) 1)
      rw [omega_inr] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
    · have := hdiv (Pi.single (Sum.inl i) 1)
      rw [omega_inl, dvd_neg] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
  let M : Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N := fun j i => (T (Pi.single j 1) i : ZMod N)
  let TN : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ZMod N) := fun v i => ∑ j, v j * M j i
  have hT_sum : ∀ a : Fin h ⊕ Fin h → ℤ, T a = ∑ j, a j • T (Pi.single j 1) := by
    intro a
    conv_lhs => rw [← Finset.univ_sum_single a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Pi.single j (a j) = a j • (Pi.single j 1 : Fin h ⊕ Fin h → ℤ) by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi], map_smul]
  have reduction_uniformizerPoint : ∀ a, red (T a) = TN (red a) := by
    intro a; funext i
    simp only [red, TN, M]
    rw [hT_sum a]
    simp [Finset.sum_apply]
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v i => ((v i).val : ℤ)
  have red_lift : ∀ v, red (lift v) = v := fun v => funext fun i => by simp [red, lift]
  have TN_sub : ∀ v w, TN (v - w) = TN v - TN w := by
    intro v w; funext i; simp only [TN, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have TN_inj : Function.Injective TN := by
    intro v w hvw
    have h0 : red (T (lift (v - w))) = 0 := by rw [reduction_uniformizerPoint, red_lift, TN_sub, hvw, sub_self]
    obtain ⟨b, hb⟩ := kerN _ ((red_zero _).1 h0)
    have := (red_zero _).2 ⟨b, hb⟩
    rw [red_lift] at this
    exact sub_eq_zero.1 this
  have TN_surj : Function.Surjective TN := Finite.injective_iff_surjective.1 TN_inj
  refine ⟨fun a => ⟨kerN a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun a' => ?_⟩
  obtain ⟨v, hv⟩ := TN_surj (red a')
  obtain ⟨c, hc⟩ := (red_zero (a' - T (lift v))).1 (by
    funext i
    have := congrFun (reduction_uniformizerPoint (lift v)) i
    rw [red_lift, hv] at this
    simp only [red, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at this ⊢
    rw [this, sub_self])
  exact ⟨lift v, c, by rw [← hc]; abel⟩

section Push

variable {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `GlobalTheory.SiegelDescent.exists_liftHom hp T T (𝟙 _) (by simp)`. Establish `key : ∀ u, (ρ u).left ≫ φ = u.left` using `fun u => ((hρ u (ρ u)).1 rfl).trans (Category.id_comp _)`. Establish `inj : Function.Injective ρ` using `fun u v e => Over.OverMorphism.ext ((key u).symm.trans (e ▸ key v))`. Establish `surj : Function.Surjective ρ` using `fun p => ⟨Over.homMk (p.left ≫ φ) (by`. Rewrite using `[Category.assoc, hp.1.w, Category.comp_id, Over.w]), (hρ _ p).2 (by simp)⟩`.

Set `e` to `MulEquiv.ofBijective ρ ⟨inj, surj⟩`. Use `⟨e.symm.toMonoidHom, fun p => ?_⟩` and prove the remaining obligations. Establish `h1 : ρ (e.symm p) = p` using `e.apply_symm_apply p`. Establish `h2` using `key (e.symm p)`. Rewrite `h2` using `[h1]`.

Conclude with `h2.symm`.
-/
theorem exists_push (hp : IsGrpPullback G' G (𝟙 S) φ) (T : Over S) :
    ∃ ψ : (T ⟶ G') →* (T ⟶ G), ∀ p, (ψ p).left = p.left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom hp T T (𝟙 _) (by simp)
  have key : ∀ u, (ρ u).left ≫ φ = u.left := fun u => ((hρ u (ρ u)).1 rfl).trans (Category.id_comp _)
  have inj : Function.Injective ρ := fun u v e => Over.OverMorphism.ext ((key u).symm.trans (e ▸ key v))
  have surj : Function.Surjective ρ := fun p => ⟨Over.homMk (p.left ≫ φ) (by
      rw [Category.assoc, hp.1.w, Category.comp_id, Over.w]), (hρ _ p).2 (by simp)⟩
  let e := MulEquiv.ofBijective ρ ⟨inj, surj⟩
  refine ⟨e.symm.toMonoidHom, fun p => ?_⟩
  have h1 : ρ (e.symm p) = p := e.apply_symm_apply p
  have h2 := key (e.symm p)
  rw [h1] at h2
  exact h2.symm

end Push

/- English proof (translation)
Use `C.lev_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_left_cancel (a := C.lev 0) (by rw [← this, _root_.mul_one])`.
-/
theorem lev_zero {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := C.lev 0) (by rw [← this, _root_.mul_one])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, lev_zero]`. Consider the case `succ n ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]`.
-/
theorem lev_nsmul {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) (n : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (n • a) = C.lev a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ n ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

/- English proof (translation)
Take `⟨hinj, hsurj⟩` from `similitude_bij_mod h N m T hN.pos hm hT`. Establish `lev_mod : ∀ a c, C.lev (a + N • c) = C.lev a`. Introduce `a c`. Rewrite using `[C.lev_add, lev_nsmul, C.lev_tors, _root_.mul_one]`. Use `⟨{ C with lev := fun a => C.lev (T a), lev_add := fun a c => (by rw [map_add]; exact C.lev_add _ _), lev_tors := fun a => C.lev_tors _, geom := ?_ }, 𝟙 _, 𝟙 _, ?_, ⟨by simp, by simp⟩, GlobalTheory.ThetaAffineGlue.lbIso_pull_id C.isLB, fun x => Category.comp_id _⟩` and prove the remaining obligations.

Introduce `k _ _ x β z hx hz`. Set `z₀ : kˣ` to `Units.map β.toMonoidHom b.ζ`. Establish `hzz : z = z₀ ^ m` using `Units.ext (by rw [hz, map_pow, Units.val_pow_eq_pow_val]; rfl)`. Take `⟨ga, gb, gc⟩` from `C.geom k x β z₀ hx rfl`. Establish `hprim : IsPrimitiveRoot z₀ N` using `IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)`.

Use `⟨fun a => (ga (T a)).trans (hinj a), fun g hg => ?_, fun a c => ?_⟩` and prove the remaining obligations. Take `⟨a', ha'⟩` from `gb g hg`. Take `⟨a, c, rfl⟩` from `hsurj a'`. Conclude with `⟨a, by rw [← ha', lev_mod]⟩`. Establish `e : z ^ (2 * omegaStd a c) = z₀ ^ (2 * omegaStd (T a) (T c))`.

Rewrite using `[hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd]`. Take `⟨q, hq⟩` from `(hT a c).dvd`. Conclude with `⟨2 * q, by linear_combination 2 * hq⟩`. Rewrite using `[e]`. Conclude with `gc (T a) (T c)`.

Conclude with `@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl C.A) (inferInstanceAs (IsMonHom (𝟙 C.A)))`.
-/
theorem part_one (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (hm : m.Coprime N)
    (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left),
      IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧
        ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  obtain ⟨hinj, hsurj⟩ := similitude_bij_mod h N m T hN.pos hm hT
  have lev_mod : ∀ a c, C.lev (a + N • c) = C.lev a := by
    intro a c; rw [C.lev_add, lev_nsmul, C.lev_tors, _root_.mul_one]
  refine ⟨{ C with
      lev := fun a => C.lev (T a), lev_add := fun a c => (by rw [map_add]; exact C.lev_add _ _),
      lev_tors := fun a => C.lev_tors _, geom := ?_ }, 𝟙 _, 𝟙 _, ?_, ⟨by simp, by simp⟩,
      GlobalTheory.ThetaAffineGlue.lbIso_pull_id C.isLB, fun x => Category.comp_id _⟩
  · intro k _ _ x β z hx hz
    let z₀ : kˣ := Units.map β.toMonoidHom b.ζ
    have hzz : z = z₀ ^ m := Units.ext (by rw [hz, map_pow, Units.val_pow_eq_pow_val]; rfl)
    obtain ⟨ga, gb, gc⟩ := C.geom k x β z₀ hx rfl
    have hprim : IsPrimitiveRoot z₀ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
    refine ⟨fun a => (ga (T a)).trans (hinj a), fun g hg => ?_, fun a c => ?_⟩
    · obtain ⟨a', ha'⟩ := gb g hg
      obtain ⟨a, c, rfl⟩ := hsurj a'
      exact ⟨a, by rw [← ha', lev_mod]⟩
    · have e : z ^ (2 * omegaStd a c) = z₀ ^ (2 * omegaStd (T a) (T c)) := by
        rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd]
        obtain ⟨q, hq⟩ := (hT a c).dvd
        exact ⟨2 * q, by linear_combination 2 * hq⟩
      rw [e]
      exact gc (T a) (T c)
  · exact @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl C.A) (inferInstanceAs (IsMonHom (𝟙 C.A)))

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory.SimilitudeLevel

/- English proof (translation)
Set `K` to `AlgebraicClosure (IsLocalRing.ResidueField R)`. Set `jr : R →+* K` to `(algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R)`. Set `x : Sp K ⟶ Sp R` to `spMap jr`. Establish `hx : ∀ g₀ : B →+* R, x ≫ spMap g₀ = spMap (jr.comp g₀)` using `fun g₀ => by`. Simplify using `only [x, spMap, ← Spec.map_comp]`.

Both sides reduce to the same expression. Set `Tx : Over (Sp R)` to `Over.mk x`. Take `⟨ψ, hψ⟩` from `exists_push hpb Tx`. Set `p : (Fin h ⊕ Fin h → ℤ) → (Tx ⟶ C'.A)` to `fun a => toUnit Tx ≫ C'.lev a`. Establish `p_add : ∀ a c, p (a + c) = p a * p c` using `fun a c => by simp only [p, C'.lev_add, MonObj.comp_mul]`.

Set `z : Kˣ` to `Units.map (jr.comp β).toMonoidHom b.ζ`. Establish `gC` using `C.geom K x (jr.comp β) z (hx β) rfl`. Establish `hprim : IsPrimitiveRoot z N` using `IsPrimitiveRoot.coe_units_iff.1 (b.prim K (jr.comp β))`. Establish `hpN : ∀ a, ψ (p a) ^ N = 1` using `fun a => by`. Rewrite using `[← map_pow, show p a ^ N = 1 by rw [← MonObj.comp_pow, C'.lev_tors, MonObj.comp_one], map_one]`.

Use `choose a' ha' using fun i => gC.2.1 (ψ (p (Pi.single i 1))) (hpN _)`. Set `T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)` to `(Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr ℤ a'`. Establish `hq : ∀ a, ψ (p a) = toUnit Tx ≫ C.lev (T a)`. Set `f₁ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (ψ (p a))) (fun a c => by rw [p_add, map_mul]; rfl)`. Set `f₂ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A)` to `AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit Tx ≫ C.lev (T a))) (fun a c => by rw [map_add, C.lev_add, MonObj.comp_mul]; rfl)`.

Establish `hext : f₁ = f₂`. Use `AddMonoidHom.functions_ext _ _ _ fun i k => ?_` and prove the remaining obligations. Rewrite using `[show (Pi.single i k : Fin h ⊕ Fin h → ℤ) = k • Pi.single i 1 by`. Apply the tactic sequence `ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj], map_zsmul, map_zsmul]`. Use `congr 1`.

Use `show Additive.ofMul (ψ (p (Pi.single i 1))) = Additive.ofMul (toUnit Tx ≫ C.lev (T (Pi.single i 1)))`. Rewrite using `[← ha' i]`. Use `congr 3`. Use `(Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr_basis ℤ a' i` as an intermediate fact. Rewrite `this` using `[Pi.basisFun_apply]`.

Conclude with `this.symm`. Introduce `a`. Conclude with `congrArg Additive.toMul (DFunLike.congr_fun hext a)`. Establish `hdiag : LBIso C'.diag (C.diag.pull φ)` using `GlobalTheory.SiegelDescent.lbIso_square C'.isLB C.isLB hP (GlobalTheory.SiegelDescent.lift_square (T := C'.A) (T₀ := C.A) (τ := φ) (a := 𝟙 _) (b := 𝟙 _) (a₀ := 𝟙 _) (b₀ := 𝟙 _) hsq (by simp) (by simp))`. Set `z' : Kˣ` to `Units.map (jr.comp β').toMonoidHom b.ζ`.

Establish `hzz : z' = z ^ m` using `Units.ext (by simp [z, z', hζ])`. Establish `gC'` using `C'.geom K x (jr.comp β') z' (hx β') rfl`. Use `⟨T, fun a c => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `w1` using `gC'.2.2 a c`. Establish `w2 : Out.WeilIs C.A C.diag N (ψ (p a)) (ψ (p c)) (unitOn (z' ^ (2 * omegaStd a c)))`.

Use `(GlobalTheory.weilIs_grpPullback_of_comm' _ _ C.A C'.A (𝟙 _) φ C.diag C'.diag (pull_isLB C.isLB _) (pull_isLB C'.isLB _) hpb hdiag Tx N (p a) (p c) (Over.homMk (ψ (p a)).left (by simp)) (Over.homMk (ψ (p c)).left (by simp)) _ (by simp [hψ]) (by simp [hψ])).1 w1` as an intermediate fact. Conclude with `GlobalTheory.SiegelDescent.weilIs_congr (by simp) _ _ _ _ _ _ rfl rfl _ this`. Establish `w3` using `gC.2.2 (T a) (T c)`. Rewrite `w3` using `[← hq, ← hq]`. Establish `e` using `GlobalTheory.weilIs_unique_fieldPoint _ C.A C.diag (pull_isLB C.isLB _) K x N _ _ _ _ w2 w3`.

Rewrite `e` using `[hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd]`. Establish `h2 : IsCoprime (N : ℤ) 2`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Conclude with `Nat.Coprime.symm (Nat.coprime_two_left.2 hN)`. Establish `e' : (N : ℤ) ∣ 2 * (m * omegaStd a c - omegaStd (T a) (T c))`.

Use `e using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `Int.modEq_iff_dvd.2 (h2.dvd_of_dvd_mul_left e')`. Take `⟨ψ₀, hψ₀⟩` from `exists_push hpb (𝟙_ (Over (Sp R)))`. Establish `key` using `GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) C.A (@IsAbelianScheme.smooth _ _ _ C.ab) R (𝟙 _) N (by simpa using b.unit.map β) (ψ₀ (C'.lev a)) (C.lev (T a)) (by rw [← map_pow, C'.lev_tors, C.lev_tors, map_one]) K jr inferInstance ?_`.

Simplify `congrArg (fun u => u.left) key` using `[hψ₀]`. Use `congrArg (fun u => u.left) (hq a)` as an intermediate fact. Simplify using `only [hψ, p, Over.comp_left] at this`. Establish `ht : (toUnit Tx).left = x` using `(Category.comp_id _).symm.trans (Over.w (toUnit Tx))`. Rewrite `this` using `[ht]`.

Rewrite using `[hψ₀]`. Conclude with `this`.
-/
theorem part_two (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N)
    (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R)
    (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β'))
    (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left) (hζ : β' (b.ζ : B) = β (b.ζ : B) ^ m)
    (hpb : IsGrpPullback C'.A C.A (𝟙 _) φ) (hsq : IsSquare φ φ₂) (hP : LBIso C'.P (C.P.pull φ₂)) :
    ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧
      ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let jr : R →+* K := (algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R)
  let x : Sp K ⟶ Sp R := spMap jr
  have hx : ∀ g₀ : B →+* R, x ≫ spMap g₀ = spMap (jr.comp g₀) := fun g₀ => by
    simp only [x, spMap, ← Spec.map_comp]; rfl
  let Tx : Over (Sp R) := Over.mk x
  obtain ⟨ψ, hψ⟩ := exists_push hpb Tx
  let p : (Fin h ⊕ Fin h → ℤ) → (Tx ⟶ C'.A) := fun a => toUnit Tx ≫ C'.lev a
  have p_add : ∀ a c, p (a + c) = p a * p c := fun a c => by simp only [p, C'.lev_add, MonObj.comp_mul]
  let z : Kˣ := Units.map (jr.comp β).toMonoidHom b.ζ
  have gC := C.geom K x (jr.comp β) z (hx β) rfl
  have hprim : IsPrimitiveRoot z N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K (jr.comp β))
  have hpN : ∀ a, ψ (p a) ^ N = 1 := fun a => by
    rw [← map_pow, show p a ^ N = 1 by rw [← MonObj.comp_pow, C'.lev_tors, MonObj.comp_one], map_one]
  choose a' ha' using fun i => gC.2.1 (ψ (p (Pi.single i 1))) (hpN _)
  let T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr ℤ a'
  have hq : ∀ a, ψ (p a) = toUnit Tx ≫ C.lev (T a) := by
    let f₁ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (ψ (p a))) (fun a c => by rw [p_add, map_mul]; rfl)
    let f₂ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit Tx ≫ C.lev (T a)))
        (fun a c => by rw [map_add, C.lev_add, MonObj.comp_mul]; rfl)
    have hext : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun i k => ?_
      rw [show (Pi.single i k : Fin h ⊕ Fin h → ℤ) = k • Pi.single i 1 by
        ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj], map_zsmul, map_zsmul]
      congr 1
      show Additive.ofMul (ψ (p (Pi.single i 1))) = Additive.ofMul (toUnit Tx ≫ C.lev (T (Pi.single i 1)))
      rw [← ha' i]
      congr 3
      have := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr_basis ℤ a' i
      rw [Pi.basisFun_apply] at this
      exact this.symm
    intro a
    exact congrArg Additive.toMul (DFunLike.congr_fun hext a)
  have hdiag : LBIso C'.diag (C.diag.pull φ) :=
    GlobalTheory.SiegelDescent.lbIso_square C'.isLB C.isLB hP
      (GlobalTheory.SiegelDescent.lift_square (T := C'.A) (T₀ := C.A) (τ := φ) (a := 𝟙 _) (b := 𝟙 _) (a₀ := 𝟙 _)
        (b₀ := 𝟙 _) hsq (by simp) (by simp))
  let z' : Kˣ := Units.map (jr.comp β').toMonoidHom b.ζ
  have hzz : z' = z ^ m := Units.ext (by simp [z, z', hζ])
  have gC' := C'.geom K x (jr.comp β') z' (hx β') rfl
  refine ⟨T, fun a c => ?_, fun a => ?_⟩
  · have w1 := gC'.2.2 a c
    have w2 : Out.WeilIs C.A C.diag N (ψ (p a)) (ψ (p c)) (unitOn (z' ^ (2 * omegaStd a c))) := by
      have := (GlobalTheory.weilIs_grpPullback_of_comm' _ _ C.A C'.A (𝟙 _) φ C.diag C'.diag (pull_isLB C.isLB _)
        (pull_isLB C'.isLB _) hpb hdiag Tx N (p a) (p c) (Over.homMk (ψ (p a)).left (by simp))
        (Over.homMk (ψ (p c)).left (by simp)) _ (by simp [hψ]) (by simp [hψ])).1 w1
      exact GlobalTheory.SiegelDescent.weilIs_congr (by simp) _ _ _ _ _ _ rfl rfl _ this
    have w3 := gC.2.2 (T a) (T c)
    rw [← hq, ← hq] at w3
    have e := GlobalTheory.weilIs_unique_fieldPoint _ C.A C.diag (pull_isLB C.isLB _) K x N _ _ _ _ w2 w3
    rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd] at e
    have h2 : IsCoprime (N : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact Nat.Coprime.symm (Nat.coprime_two_left.2 hN)
    have e' : (N : ℤ) ∣ 2 * (m * omegaStd a c - omegaStd (T a) (T c)) := by
      convert e using 1; ring
    exact Int.modEq_iff_dvd.2 (h2.dvd_of_dvd_mul_left e')
  · obtain ⟨ψ₀, hψ₀⟩ := exists_push hpb (𝟙_ (Over (Sp R)))
    have key := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) C.A (@IsAbelianScheme.smooth _ _ _ C.ab) R (𝟙 _) N
      (by simpa using b.unit.map β) (ψ₀ (C'.lev a)) (C.lev (T a))
      (by rw [← map_pow, C'.lev_tors, C.lev_tors, map_one]) K jr inferInstance ?_
    · simpa [hψ₀] using congrArg (fun u => u.left) key
    · have := congrArg (fun u => u.left) (hq a)
      simp only [hψ, p, Over.comp_left] at this
      have ht : (toUnit Tx).left = x := (Category.comp_id _).symm.trans (Over.w (toUnit Tx))
      rw [ht] at this
      rw [hψ₀]
      exact this

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory

/- English proof (translation)
Introduce `h N B _ b hN`. Conclude with `⟨fun S s C T m hm hT => SimilitudeLevel.part_one h N B b hN S s C T m hm hT, fun R _ _ β m β' C C' φ φ₂ hζ hpb hsq hP => SimilitudeLevel.part_two h N B b hN R β m β' C C' φ φ₂ hζ hpb hsq hP⟩`.
-/
theorem siegel_level_change_by_similitude : ∀ (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N), Odd N → (∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ), m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R) (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β')) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), β' (b.ζ : B) = β (b.ζ : B) ^ m → IsGrpPullback C'.A C.A (𝟙 _) φ → IsSquare φ φ₂ → LBIso C'.P (C.P.pull φ₂) → ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  intro h N B _ b hN
  exact ⟨fun S s C T m hm hT => SimilitudeLevel.part_one h N B b hN S s C T m hm hT,
    fun R _ _ β m β' C C' φ φ₂ hζ hpb hsq hP => SimilitudeLevel.part_two h N B b hN R β m β' C C' φ φ₂ hζ hpb hsq hP⟩

end GlobalTheory
