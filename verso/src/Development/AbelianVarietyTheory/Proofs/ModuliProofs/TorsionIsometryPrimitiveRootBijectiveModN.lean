import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsIsometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Set `φ : M →ₗ[ℤ] ℤ` to `{ toFun := fun b => B d b / n map_add' := fun x y => by`. Simplify using `only [map_add]`. Conclude with `Int.add_ediv_of_dvd_left (hd x)`. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [map_zsmul, smul_eq_mul, RingHom.id_apply]`.

Conclude with `Int.mul_ediv_assoc c (hd x) }`. Take `⟨f, hf⟩` from `hB.2 φ`. Use `⟨f, hB.1 ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Simplify using `only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]`.

Conclude with `(Int.mul_ediv_cancel' (hd b)).symm`.
-/
theorem _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Introduce `E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair`. Establish `hev0 : ev 0 = 1`. Establish `h` using `hev 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.1 h.symm)`.

Establish `hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m`. Introduce `m c`. Proceed by induction on `m with`. Consider the case `zero => simp [hev0]`. Consider the case `succ m ih => rw [succ_nsmul, hev, ih, pow_succ]`.

Establish `hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c`. Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Use `_root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_` and prove the remaining obligations.

Establish `h` using `hpair a c`. Rewrite `h` using `[ha]`. Conclude with `(hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)`. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[hevsmul, hevn]`.

Use `⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩` and prove the remaining obligations. Use `swap`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `hevn a`. Use `haveI : NeZero n := ⟨hn.ne'⟩`.

Use `haveI := D.fin`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by`. Distinguish the cases in `hc : c = 0`. Conclude with `Or.inl hc`.

Use `right`. Apply `D.unimod.1` to reduce the goal to its premises. Use extensionality with `b`. Use `congrArg (fun x => D.EF x b) h` as an intermediate fact. Simplify using `only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero, LinearMap.zero_apply] at this`.

Simplify `this⟩` using `[hc]`. Use `haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.finBasis ℤ D.La`. Set `g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1}` to `fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩`. Establish `hinj : Function.Injective g`.

Introduce `t t' htt`. Establish `h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) = ev (b.equivFun.symm fun i => ((t' i).val : ℤ))` using `congrArg Subtype.val htt`. Establish `hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) - b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1`. Establish `h2` using `hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) - b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))`. Rewrite `h2` using `[sub_add_cancel, h]`.

Conclude with `mul_eq_right.1 h2.symm`. Take `⟨c, hc⟩` from `(hker _).1 hdiff`. Use function extensionality and compare the values at `i`. Establish `hi` using `congrArg (fun z => b.equivFun z i) hc`. Simplify using `only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at hi`.

Establish `hcast` using `congrArg (Int.cast : ℤ → ZMod n) hi`. Move the coercions through the operations in `at hcast`. Simplify `hcast` using `[sub_eq_zero]`. Use `haveI : Finite {y : Q // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Establish `hbij : Function.Bijective g` using `hinj.bijective_of_nat_card_le (by`.

Rewrite using `[hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])`. Take `⟨t, ht⟩` from `hbij.2 ⟨y, hy⟩`. Conclude with `⟨_, congrArg Subtype.val ht⟩`.
-/
theorem _root_.GlobalTheory.TorsIsometry.ker_and_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  intro E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m := by
    intro m c
    induction m with
    | zero => simp [hev0]
    | succ m ih => rw [succ_nsmul, hev, ih, pow_succ]
  have hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c := by
    intro a
    constructor
    · intro ha
      refine _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_
      have h := hpair a c
      rw [ha] at h
      exact (hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)
    · rintro ⟨c, rfl⟩
      rw [hevsmul, hevn]
  refine ⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩
  swap
  · rintro ⟨a, rfl⟩
    exact hevn a
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply D.unimod.1
      ext b
      have := congrArg (fun x => D.EF x b) h
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero,
        LinearMap.zero_apply] at this
      simpa [hc] using this⟩
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ D.La
  let g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1} :=
    fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩
  have hinj : Function.Injective g := by
    intro t t' htt
    have h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) =
        ev (b.equivFun.symm fun i => ((t' i).val : ℤ)) := congrArg Subtype.val htt
    have hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1 := by
      have h2 := hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))
      rw [sub_add_cancel, h] at h2
      exact mul_eq_right.1 h2.symm
    obtain ⟨c, hc⟩ := (hker _).1 hdiff
    funext i
    have hi := congrArg (fun z => b.equivFun z i) hc
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul] at hi
    have hcast := congrArg (Int.cast : ℤ → ZMod n) hi
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  haveI : Finite {y : Q // y ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val ht⟩

end GlobalTheory.TorsIsometry
