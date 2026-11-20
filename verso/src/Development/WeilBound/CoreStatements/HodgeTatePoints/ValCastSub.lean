import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValLeOfMem
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDualOf
import Development.WeilBound.CoreStatements.HodgeTatePoints.CompMemAddFun
import ReciprocityTheory.DualLattices.HasLenLeOfSurj

open NumberField ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.Num.FamEx
open PositivityTheory.Xgn.TestGroupPoint
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Sgp

variable {R : Type} [CommRing R]

def qq (p : ℕ) (R : Type) [CommRing R] (g : ℕ) : LieDualModP p R g →ₗ[R] (Fin g → R ⧸ Ideal.span {(p : R)}) :=
  Submodule.liftQ _ (LinearMap.pi fun i => (Ideal.span {(p : R)}).mkQ ∘ₗ LinearMap.proj i)
    (Submodule.smul_le.2 fun _ hr _ _ => LinearMap.mem_ker.2 (funext fun _ =>
      (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right _ _ hr)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qq_mk (p g : ℕ) (u : Fin g → R) :
    qq p R g (Submodule.Quotient.mk u) = fun k => Ideal.Quotient.mk _ (u k) := rfl

variable {C : Type} [Field C] [Algebra R C] {v : Valuation C NNReal}

/- English proof (translation)
Introduce `_ h` and use `h.1`.
-/
theorem aug_le {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) : augIdeal M ≤ M := fun _ h => h.1

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top]`. Use `set L : (Fin g → R) →ₗ[R] (Fin g → R ⧸ Ideal.span {(p : R)}) := qq p R g ∘ₗ (Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R))).mkQ with hL`. Establish `hLu : ∀ u, L u = fun k => Ideal.Quotient.mk _ (u k)`. Introduce `u`. Simplify using `only [hL, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]`.

Conclude with `qq_mk p g u`. Establish `hLs : Function.Surjective L` using `fun w => ⟨fun k => (Ideal.Quotient.mk_surjective (w k)).choose, by`. Rewrite using `[hLu]`. Use function extensionality and compare the values at `k`. Conclude with `(Ideal.Quotient.mk_surjective (w k)).choose_spec⟩`.

Establish `key : Submodule.map L (Submodule.span R S) ≤ LinearMap.range (qq p R g ∘ₗ Dv ∘ₗ Submodule.inclusion (aug_le M))`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Take `⟨f, hf0, hf⟩` from `hs u hu`. Establish `hfa : f.1 ∈ augIdeal M` using `by show f.1 ∈ M ⊓ LinearMap.ker (LinearMap.proj 0)`.

Conclude with `Submodule.mem_inf.2 ⟨f.2, LinearMap.mem_ker.2 hf0⟩`. Use `⟨⟨f.1, hfa⟩, ?_⟩` and prove the remaining obligations. Establish `hinc : Submodule.inclusion (aug_le M) ⟨f.1, hfa⟩ = f` using `rfl`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, hinc, hf, hL, Submodule.mkQ_apply]`. Rewrite `key` using `[hS, ← LinearMap.range_eq_map, LinearMap.range_eq_top.2 hLs]`.

Conclude with `eq_top_iff.2 key`.
-/
theorem surj_aug {N : Type} [AddCommGroup N] {M : Submodule R (N → C)} {p g : ℕ} (Dv : M →ₗ[R] LieDualModP p R g)
    (S : Set (Fin g → R)) (hS : Submodule.span R S = ⊤)
    (hs : ∀ u ∈ S, ∃ f : M, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk u) :
    Function.Surjective (qq p R g ∘ₗ Dv ∘ₗ Submodule.inclusion (aug_le M)) := by
  rw [← LinearMap.range_eq_top]
  set L : (Fin g → R) →ₗ[R] (Fin g → R ⧸ Ideal.span {(p : R)}) :=
    qq p R g ∘ₗ (Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R))).mkQ with hL
  have hLu : ∀ u, L u = fun k => Ideal.Quotient.mk _ (u k) := by
    intro u
    simp only [hL, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    exact qq_mk p g u
  have hLs : Function.Surjective L := fun w =>
    ⟨fun k => (Ideal.Quotient.mk_surjective (w k)).choose, by
      rw [hLu]
      funext k
      exact (Ideal.Quotient.mk_surjective (w k)).choose_spec⟩
  have key : Submodule.map L (Submodule.span R S) ≤
      LinearMap.range (qq p R g ∘ₗ Dv ∘ₗ Submodule.inclusion (aug_le M)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨f, hf0, hf⟩ := hs u hu
    have hfa : f.1 ∈ augIdeal M := by
      show f.1 ∈ M ⊓ LinearMap.ker (LinearMap.proj 0)
      exact Submodule.mem_inf.2 ⟨f.2, LinearMap.mem_ker.2 hf0⟩
    refine ⟨⟨f.1, hfa⟩, ?_⟩
    have hinc : Submodule.inclusion (aug_le M) ⟨f.1, hfa⟩ = f := rfl
    simp only [LinearMap.coe_comp, Function.comp_apply, hinc, hf, hL, Submodule.mkQ_apply]
  rw [hS, ← LinearMap.range_eq_map, LinearMap.range_eq_top.2 hLs] at key
  exact eq_top_iff.2 key

/- English proof (translation)
Use `set F := qq p R g ∘ₗ Dv ∘ₗ Submodule.inclusion (aug_le AA.carrier) with hFdef`. Establish `hF : Function.Surjective F` using `surj_aug Dv S hS hs`. Establish `hsq : sqIdeal (augIdeal AA.carrier) ≤ Submodule.map (augIdeal AA.carrier).subtype (LinearMap.ker F)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, f', hf', rfl⟩`.

Establish `hf2 : f ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0)` using `hf`. Establish `hf'2 : f' ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0)` using `hf'`. Establish `h0 : f 0 = 0` using `by simpa using LinearMap.mem_ker.1 hf2.2`. Establish `h0' : f' 0 = 0` using `by simpa using LinearMap.mem_ker.1 hf'2.2`. Establish `hmul : f * f' ∈ AA.carrier` using `AA.mul_mem f f' hf2.1 hf'2.1`.

Establish `hmem : f * f' ∈ augIdeal AA.carrier` using `by show f * f' ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0)`. Use `Submodule.mem_inf.2 ⟨hmul, LinearMap.mem_ker.2 ?_⟩` and prove the remaining obligations. Simplify using `[h0]`. Use `⟨⟨f * f', hmem⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`.

Establish `hD0` using `hD ⟨f, hf2.1⟩ ⟨f', hf'2.1⟩ ⟨f * f', hmul⟩ 0 0 rfl (by rw [map_zero]; exact h0.symm) (by rw [map_zero]; exact h0'.symm)`. Establish `hinc : Submodule.inclusion (aug_le AA.carrier) ⟨f * f', hmem⟩ = ⟨f * f', hmul⟩` using `rfl`. Simplify using `only [hFdef, LinearMap.coe_comp, Function.comp_apply, hinc, hD0, zero_smul, add_zero, map_zero]`. Establish `hle : Submodule.comap (augIdeal AA.carrier).subtype (sqIdeal (augIdeal AA.carrier)) ≤ LinearMap.ker F`. Introduce `x hx`.

Take `⟨y, hy, hyx⟩` from `hsq hx`. Establish `hyx' : y = x` using `Subtype.ext hyx`. Rewrite using `[← hyx']`. Conclude with `hy`. Use `(hasLen_le_of_surj hv hO (p : R) g (Submodule.liftQ _ F hle) ?_).trans_eq ?_` and prove the remaining obligations.

Introduce `w`. Take `⟨a, ha⟩` from `hF w`. Conclude with `⟨Submodule.Quotient.mk a, by rw [Submodule.liftQ_apply]; exact ha⟩`. Rewrite using `[map_natCast]`.
-/
theorem om_bound (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {p g : ℕ} (Dv : AA.carrier →ₗ[R] LieDualModP p R g) (hD : IsDerAt0 _ Dv)
    (S : Set (Fin g → R)) (hS : Submodule.span R S = ⊤)
    (hs : ∀ u ∈ S, ∃ f : AA.carrier, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk u) {cO : NNReal}
    (hO : HasLen v R (OmAA AA.carrier) cO) : cO ≤ v (p : C) ^ g := by
  set F := qq p R g ∘ₗ Dv ∘ₗ Submodule.inclusion (aug_le AA.carrier) with hFdef
  have hF : Function.Surjective F := surj_aug Dv S hS hs
  have hsq : sqIdeal (augIdeal AA.carrier) ≤
      Submodule.map (augIdeal AA.carrier).subtype (LinearMap.ker F) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    have hf2 : f ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0) := hf
    have hf'2 : f' ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0) := hf'
    have h0 : f 0 = 0 := by simpa using LinearMap.mem_ker.1 hf2.2
    have h0' : f' 0 = 0 := by simpa using LinearMap.mem_ker.1 hf'2.2
    have hmul : f * f' ∈ AA.carrier := AA.mul_mem f f' hf2.1 hf'2.1
    have hmem : f * f' ∈ augIdeal AA.carrier := by
      show f * f' ∈ AA.carrier ⊓ LinearMap.ker (LinearMap.proj 0)
      refine Submodule.mem_inf.2 ⟨hmul, LinearMap.mem_ker.2 ?_⟩
      simp [h0]
    refine ⟨⟨f * f', hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hD0 := hD ⟨f, hf2.1⟩ ⟨f', hf'2.1⟩ ⟨f * f', hmul⟩ 0 0 rfl
      (by rw [map_zero]; exact h0.symm) (by rw [map_zero]; exact h0'.symm)
    have hinc : Submodule.inclusion (aug_le AA.carrier) ⟨f * f', hmem⟩ = ⟨f * f', hmul⟩ := rfl
    simp only [hFdef, LinearMap.coe_comp, Function.comp_apply, hinc, hD0, zero_smul, add_zero, map_zero]
  have hle : Submodule.comap (augIdeal AA.carrier).subtype (sqIdeal (augIdeal AA.carrier)) ≤
      LinearMap.ker F := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hsq hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  refine (hasLen_le_of_surj hv hO (p : R) g (Submodule.liftQ _ F hle) ?_).trans_eq ?_
  · intro w
    obtain ⟨a, ha⟩ := hF w
    exact ⟨Submodule.Quotient.mk a, by rw [Submodule.liftQ_apply]; exact ha⟩
  · rw [map_natCast]

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`. Use `conv_rhs => rw [← Nat.mod_add_div z.val p, pow_add, pow_mul, hζ, one_pow, mul_one]`.
-/
theorem pow_val_cast {U : Type} [Monoid U] {p m : ℕ} [NeZero p] [NeZero m] (h : p ∣ m) {ζ : U} (hζ : ζ ^ p = 1)
    (z : ZMod m) : ζ ^ (ZMod.castHom h (ZMod p) z).val = ζ ^ z.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div z.val p, pow_add, pow_mul, hζ, one_pow, mul_one]

/- English proof (translation)
Establish `key : (z.val : R) = ((z.val % p : ℕ) : R) + (p : R) * ((z.val / p : ℕ) : R)`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, Ideal.mem_span_singleton]`. Use `⟨((z.val / p : ℕ) : R), ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_cast_sub {p m : ℕ} [NeZero p] [NeZero m] (h : p ∣ m) (z : ZMod m) :
    (z.val : R) - ((ZMod.castHom h (ZMod p) z).val : R) ∈ Ideal.span {(p : R)} := by
  have key : (z.val : R) = ((z.val % p : ℕ) : R) + (p : R) * ((z.val / p : ℕ) : R) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, Ideal.mem_span_singleton]
  refine ⟨((z.val / p : ℕ) : R), ?_⟩
  rw [key]
  ring

/- English proof (translation)
Use `conv_rhs => rw [← sum_cz x, ← sum_cz x']`. Simplify using `only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, co_apply, Finset.mul_sum]`. Simplify using `only [Finset.smul_sum, zsmul_eq_mul]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cast_pair {p m : ℕ} (h : p ∣ m) (e : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) →+ ZMod m) (x x' : Fin n → 𝓞 E) :
    co p x ⬝ᵥ (Matrix.of fun a b => ZMod.castHom h (ZMod p) (e (dl a) (dl b))) *ᵥ co p x' =
      ZMod.castHom h (ZMod p) (e x x') := by
  conv_rhs => rw [← sum_cz x, ← sum_cz x']
  simp only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply,
    dotProduct, Matrix.mulVec, Matrix.of_apply, co_apply, Finset.mul_sum]
  simp only [Finset.smul_sum, zsmul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
The claim follows from `Submodule.mem_map`.
-/
theorem mem_pull {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X] [AddCommGroup Y] [Fintype Y]
    [DecidableEq Y] (φ : X ≃+ Y) (AA : HopfOrder (C := C) R Y) (g : X → C) :
    g ∈ (hopfPull φ AA).carrier ↔ ∃ f ∈ AA.carrier, (fun x => f (φ x)) = g := Submodule.mem_map

/- English proof (translation)
Use `set P : (Y → C) ≃ₗ[R] (X → C) := pbE φ with hP`. Establish `key : ∀ (SX : Submodule R (X → C)) (SY : Submodule R (Y → C)), (∀ y, y ∈ SY ↔ P y ∈ SX) → Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C)) SX = SY`. Introduce `SX SY hS`. Use extensionality with `y`. Rewrite using `[Submodule.mem_map_equiv, LinearEquiv.symm_symm, hS]`.

Establish `hint : ∀ y : Y → C, y ∈ intFun R Y ↔ P y ∈ intFun R X`. Introduce `y`. Use `show (∀ u, ∃ r, algebraMap R C r = y u) ↔ (∀ x, ∃ r, algebraMap R C r = y (φ x))`. Conclude with `⟨fun hy x => hy (φ x), fun hy u => by simpa using hy (φ.symm u)⟩`. Establish `hadd : ∀ y : Y → C, y ∈ addFun R p Y ↔ P y ∈ addFun R p X`.

Introduce `y`. Use `show (∀ a b : Y, y (a + b) - y a - y b ∈ pInt R p) ↔ (∀ a b : X, y (φ (a + b)) - y (φ a) - y (φ b) ∈ pInt R p)`. Prove the components needed by the constructor for the conclusion. Introduce `hy a b`. Rewrite using `[map_add]`.

Conclude with `hy _ _`. Introduce `hy a b`. Establish `hab` using `hy (φ.symm a) (φ.symm b)`. Simplify using `only [map_add, AddEquiv.apply_symm_apply] at hab`. Conclude with `hab`.

Establish `hpf : ∀ y : Y → C, y ∈ pFun R p Y ↔ P y ∈ pFun R p X`. Introduce `y`. Use `show (∀ u ∈ Set.univ, y u ∈ pInt R p) ↔ (∀ x ∈ Set.univ, y (φ x) ∈ pInt R p)`. Conclude with `⟨fun hy x _ => hy (φ x) trivial, fun hy u _ => by simpa using hy (φ.symm u) trivial⟩`. Establish `hM : ∀ y : Y → C, y ∈ M ↔ P y ∈ Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M`.

Introduce `y`. Rewrite using `[Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]`. Establish `h1 : Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C)) (linFun R p X) = linFun R p Y`. Use `key _ _ fun y => ?_` and prove the remaining obligations. Use `show y ∈ intFun R Y ⊓ addFun R p Y ↔ P y ∈ intFun R X ⊓ addFun R p X`.

Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, hint, hadd]`. Establish `h2 : Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C)) (afFun p (Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M) ⊔ pFun R p X) = afFun p M ⊔ pFun R p Y`. Rewrite using `[Submodule.map_sup]`. Use `congr 1`. Use `key _ _ fun y => ?_ show y ∈ M ⊓ addFun R p Y ↔ P y ∈ Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M ⊓ addFun R p X` and prove the remaining obligations.

Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, hM, hadd]`. Conclude with `key _ _ hpf`. Set `f` to `P.symm.ofSubmodules (linFun R p X) (linFun R p Y) h1`. Establish `hQ : Submodule.map (f : linFun R p X →ₗ[R] linFun R p Y) (Submodule.comap (linFun R p X).subtype (afFun p (Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M) ⊔ pFun R p X)) = Submodule.comap (linFun R p Y).subtype (afFun p M ⊔ pFun R p Y)`. Use extensionality with `⟨y, hy⟩`.

Rewrite using `[Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, LinearEquiv.ofSubmodules_symm_apply, ← h2, Submodule.mem_map_equiv]`. Conclude with `hasLen_of_equiv (Submodule.Quotient.equiv _ _ f hQ) h`.
-/
private theorem hasLen_AFQuot_map_pbE_of_addEquiv {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (φ : X ≃+ Y) (p : ℕ)
    (M : Submodule R (Y → C)) {c : NNReal} (h : HasLen v R (AFQuot p M) c) :
    HasLen v R (AFQuot p (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M)) c := by
  set P : (Y → C) ≃ₗ[R] (X → C) := pbE φ with hP
  have key : ∀ (SX : Submodule R (X → C)) (SY : Submodule R (Y → C)),
      (∀ y, y ∈ SY ↔ P y ∈ SX) → Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C)) SX = SY := by
    intro SX SY hS
    ext y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, hS]
  have hint : ∀ y : Y → C, y ∈ intFun R Y ↔ P y ∈ intFun R X := by
    intro y
    show (∀ u, ∃ r, algebraMap R C r = y u) ↔ (∀ x, ∃ r, algebraMap R C r = y (φ x))
    exact ⟨fun hy x => hy (φ x), fun hy u => by simpa using hy (φ.symm u)⟩
  have hadd : ∀ y : Y → C, y ∈ addFun R p Y ↔ P y ∈ addFun R p X := by
    intro y
    show (∀ a b : Y, y (a + b) - y a - y b ∈ pInt R p) ↔
      (∀ a b : X, y (φ (a + b)) - y (φ a) - y (φ b) ∈ pInt R p)
    constructor
    · intro hy a b
      rw [map_add]
      exact hy _ _
    · intro hy a b
      have hab := hy (φ.symm a) (φ.symm b)
      simp only [map_add, AddEquiv.apply_symm_apply] at hab
      exact hab
  have hpf : ∀ y : Y → C, y ∈ pFun R p Y ↔ P y ∈ pFun R p X := by
    intro y
    show (∀ u ∈ Set.univ, y u ∈ pInt R p) ↔ (∀ x ∈ Set.univ, y (φ x) ∈ pInt R p)
    exact ⟨fun hy x _ => hy (φ x) trivial, fun hy u _ => by simpa using hy (φ.symm u) trivial⟩
  have hM : ∀ y : Y → C, y ∈ M ↔ P y ∈ Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  have h1 : Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C)) (linFun R p X) = linFun R p Y := by
    refine key _ _ fun y => ?_
    show y ∈ intFun R Y ⊓ addFun R p Y ↔ P y ∈ intFun R X ⊓ addFun R p X
    rw [Submodule.mem_inf, Submodule.mem_inf, hint, hadd]
  have h2 : Submodule.map (P.symm : (X → C) →ₗ[R] (Y → C))
      (afFun p (Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M) ⊔ pFun R p X) = afFun p M ⊔ pFun R p Y := by
    rw [Submodule.map_sup]
    congr 1
    · refine key _ _ fun y => ?_
      show y ∈ M ⊓ addFun R p Y ↔ P y ∈ Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M ⊓ addFun R p X
      rw [Submodule.mem_inf, Submodule.mem_inf, hM, hadd]
    · exact key _ _ hpf
  let f := P.symm.ofSubmodules (linFun R p X) (linFun R p Y) h1
  have hQ : Submodule.map (f : linFun R p X →ₗ[R] linFun R p Y)
      (Submodule.comap (linFun R p X).subtype
        (afFun p (Submodule.map (P : (Y → C) →ₗ[R] (X → C)) M) ⊔ pFun R p X)) =
      Submodule.comap (linFun R p Y).subtype (afFun p M ⊔ pFun R p Y) := by
    ext ⟨y, hy⟩
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, LinearEquiv.ofSubmodules_symm_apply, ← h2, Submodule.mem_map_equiv]
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ f hQ) h

/- English proof (translation)
Establish `hle : Submodule.map (LinearMap.funLeft R C (Prod.map φ φ)) (tens M M) ≤ tens (Submodule.map (pbE (R` using `R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M) (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M) := by`. Unfold `tens`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨F, ⟨g, hg, h, hh, rfl⟩, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨pbE φ g, Submodule.mem_map_of_mem hg, pbE φ h, Submodule.mem_map_of_mem hh, rfl⟩`. Conclude with `hle (Submodule.mem_map_of_mem hK)`.
-/
private theorem comp_mem_tens_map_pbE_of_addEquiv {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (φ : X ≃+ Y)
    (M : Submodule R (Y → C)) {K : Y × Y → C} (hK : K ∈ tens M M) :
    (fun z : X × X => K (φ z.1, φ z.2)) ∈
      tens (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M)
        (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M) := by
  have hle : Submodule.map (LinearMap.funLeft R C (Prod.map φ φ)) (tens M M) ≤
      tens (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M)
        (Submodule.map (pbE (R := R) (C := C) φ : (Y → C) →ₗ[R] (X → C)) M) := by
    unfold tens
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨pbE φ g, Submodule.mem_map_of_mem hg, pbE φ h, Submodule.mem_map_of_mem hh, rfl⟩
  exact hle (Submodule.mem_map_of_mem hK)

/- English proof (translation)
Substitute `hM` using the available equality. Use `haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩`. Take `⟨cA, cN, cO, hA, hN, hO, hAN, hON⟩` from `ht`. Establish `hcardN : Fintype.card (Ix E n → ZMod p) = Fintype.card (TestPt.NAdd E n p)` using `Fintype.card_congr φ.toEquiv`. Establish `hOb : cO ≤ v (p : C) ^ g` using `om_bound hv AA Dv hD S hS hs hO`.

Establish `hOA : cO = cA ^ (p - 1)`. Establish `hne : Fintype.card (TestPt.NAdd E n p) ≠ 0` using `Fintype.card_ne_zero`. Establish `hpow : cO ^ Fintype.card (TestPt.NAdd E n p) = (cA ^ (p - 1)) ^ Fintype.card (TestPt.NAdd E n p)`. Rewrite using `[hON, ← hAN, ← pow_mul, mul_comm]`. Conclude with `(pow_left_inj₀ zero_le zero_le hne).1 hpow`.

Use `set T : AA.carrier ≃ₗ[R] (hopfPull φ AA).carrier := (pbE φ).submoduleMap AA.carrier with hTdef`. Establish `hT : ∀ (f : (hopfPull φ AA).carrier) (y : TestPt.NAdd E n p), (T.symm f).1 y = f.1 (φ.symm y)`. Introduce `f y`. Use `conv_rhs => rw [← T.apply_symm_apply f]`. Use `show _ = (T.symm f).1 (φ (φ.symm y))`.

Rewrite using `[AddEquiv.apply_symm_apply]`. Set `Dv' : (hopfPull φ AA).carrier →ₗ[R] (Fin g → R ⧸ Ideal.span {(p : R)})` to `qq p R g ∘ₗ Dv ∘ₗ T.symm.toLinearMap`. Establish `hD' : IsDerAt0 _ Dv'`. Introduce `f f2 h a b hh ha hb`. Establish `hh' : (T.symm h).1 = (T.symm f).1 * (T.symm f2).1`.

Use function extensionality and compare the values at `y`. Rewrite using `[Pi.mul_apply, hT, hT, hT, hh, Pi.mul_apply]`. Establish `ha' : algebraMap R C a = (T.symm f).1 0` using `by rw [hT, map_zero, ha]`. Establish `hb' : algebraMap R C b = (T.symm f2).1 0` using `by rw [hT, map_zero, hb]`. Use `show qq p R g (Dv (T.symm h)) = a • qq p R g (Dv (T.symm f2)) + b • qq p R g (Dv (T.symm f))`.

Rewrite using `[hD _ _ _ a b hh' ha' hb', map_add, map_smul, map_smul]`. Establish `hsurj : Function.Surjective Dv'`. Introduce `w`. Take `⟨a, ha⟩` from `surj_aug Dv S hS hs w`. Use `⟨T (Submodule.inclusion (aug_le AA.carrier) a), ?_⟩` and prove the remaining obligations.

Use `show qq p R g (Dv (T.symm (T _))) = w`. Rewrite using `[T.symm_apply_apply]`. Conclude with `ha`. Take `⟨Kf, hKf, hKv⟩` from `hK`. Establish `hK'` using `comp_mem_tens_map_pbE_of_addEquiv φ AA.carrier hKf`.

Establish `hfun : (fun z : (Ix E n → ZMod p) × (Ix E n → ZMod p) => ζ ^ (z.1 ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z.2).val) = fun z => Kf (φ z.1, φ z.2)`. Use function extensionality and compare the values at `z`. Break down `z with ⟨z1, z2⟩` into its components or cases. Take `⟨x, rfl⟩` from `co_surj p z1`. Take `⟨x', rfl⟩` from `co_surj p z2`.

Simplify using `only [hφ, hKv, cast_pair hm e x x', pow_val_cast hm hζ.pow_eq_one]`. Establish `htens : (fun z : (Ix E n → ZMod p) × (Ix E n → ZMod p) => ζ ^ (z.1 ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z.2).val) ∈ tens (hopfPull φ AA).carrier (hopfPull φ AA).carrier`. Rewrite using `[hfun]`. Conclude with `hK'`. Establish `hEg : ∀ a b, Eg a b - ((((Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) : Matrix (Ix E n) (Ix E n) (ZMod p)) a b).val : R) ∈ Ideal.span {(p : R)}`.

Introduce `a b`. Rewrite using `[Matrix.of_apply]`. Establish `hsum` using `Ideal.add_mem _ (hE a b) (val_cast_sub (R := R) hm (e (dl a) (dl b)))`. Rewrite `hsum` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hchar : ∀ (x : Ix E n → ZMod p) (f : (hopfPull φ AA).carrier), (∀ z, f.1 z = ζ ^ (x ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z).val) → Dv' f = fun k => Ideal.Quotient.mk (Ideal.span {(p : R)}) (∑ m, Hm k m * ((x m).val : R))`.

Introduce `x f hf`. Take `⟨x0, rfl⟩` from `co_surj p x`. Establish `h1 : ∀ x', (T.symm f).1 (mkN p x') = ζ ^ (e x0 x').val`. Introduce `x'`. Rewrite using `[← hφ, hT, AddEquiv.symm_apply_apply, hf, cast_pair hm e x0 x', pow_val_cast hm hζ.pow_eq_one]`.

Establish `h2` using `hch x0 (T.symm f) h1`. Use `show qq p R g (Dv (T.symm f)) = _`. Rewrite using `[h2, qq_mk]`. Use function extensionality and compare the values at `k`. Rewrite using `[Ideal.Quotient.eq]`.

Establish `hih : ih x0 k = ∑ m, ih (dl m) k * (cz x0 m : R)` using `by conv_lhs => rw [← sum_cz x0]`. Simplify using `only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [zsmul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun m _ => mul_comm _ _`. Establish `hA'` using `sum_co_sub p (Hm k) x0`.

Establish `hB : ∑ m, (Hm k m - ih (dl m) k) * (cz x0 m : R) ∈ Ideal.span {(p : R)}` using `Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hH m k)`. Establish `heq : ih x0 k - ∑ m, Hm k m * (((co p x0) m).val : R) = -(∑ m, Hm k m * (((co p x0) m).val : R) - ∑ m, Hm k m * (cz x0 m : R)) - ∑ m, (Hm k m - ih (dl m) k) * (cz x0 m : R)`. Rewrite using `[hih]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 hA') hB`. Conclude with `core hv hp hp2 (hopfPull φ AA) hcard (hasLen_AFQuot_map_pbE_of_addEquiv φ p AA.carrier hA) (hasColen_map v φ AA.carrier cN hN) (by rw [hcardN]; exact hAN) (by rw [← hOA]; exact hOb) hζ _ htens Dv' hD' hsurj Hm Eg Ei hEt hEi hiso hEg hchar`.
-/
theorem core_pull {p : ℕ} [Fact p.Prime] [IsAlgClosed C] [CharZero C] (hv : v.Integers R) (hp : v (p : C) < 1)
    (hp2 : p ≠ 2) [Fintype (TestPt.NAdd E n p)] [DecidableEq (TestPt.NAdd E n p)]
    (φ : (Ix E n → ZMod p) ≃+ TestPt.NAdd E n p) (hφ : ∀ x, φ (co p x) = mkN p x)
    (AA : HopfOrder (C := C) R (TestPt.NAdd E n p)) (M : Submodule R (TestPt.NAdd E n p → C)) (hM : AA.carrier = M)
    (ht : IsTight v p M) {g : ℕ} (hcard : Fintype.card (Ix E n) = g + g)
    {m : ℕ} [NeZero m] (hm : p ∣ m) (e : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) →+ ZMod m)
    {ζ : C} (hζ : IsPrimitiveRoot ζ p)
    (hK : ∃ Kf ∈ tens M M, ∀ x x' : Fin n → 𝓞 E, Kf (mkN p x, mkN p x') = ζ ^ (e x x').val)
    (Dv : M →ₗ[R] LieDualModP p R g) (hD : IsDerAt0 _ Dv)
    (S : Set (Fin g → R)) (hS : Submodule.span R S = ⊤)
    (hs : ∀ u ∈ S, ∃ f : M, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk u)
    (ih : (Fin n → 𝓞 E) →+ (Fin g → R))
    (hch : ∀ (x : Fin n → 𝓞 E) (f : M), (∀ x', f.1 (mkN p x') = ζ ^ (e x x').val) →
      Dv f = Submodule.Quotient.mk (ih x))
    (Hm : Matrix (Fin g) (Ix E n) R) (Eg Ei : Matrix (Ix E n) (Ix E n) R)
    (hEt : Egᵀ = -Eg) (hEi : Ei * Eg = 1) (hiso : Hm * Ei * Hmᵀ = 0)
    (hE : ∀ a b, Eg a b - ((e (dl a) (dl b)).val : R) ∈ Ideal.span {(p : R)})
    (hH : ∀ a k, Hm k a - ih (dl a) k ∈ Ideal.span {(p : R)}) :
    ∃ c : R, v (algebraMap R C c) ^ (p - 1) = v (p : C) ∧ (∀ l, c • l ∈ afLat p (hopfPull φ AA).carrier) ∧
      (∀ k, Hm k ∈ afLat p (hopfPull φ AA).carrier) ∧
      (∀ y, y ᵥ* Eg ∈ afLat p (hopfPull φ AA).carrier → ∃ u, Hm *ᵥ y = c • u) ∧
      (∀ u : Fin g → R, ∃ (y : Ix E n → R) (u' : Fin g → R), y ᵥ* Eg ∈ afLat p (hopfPull φ AA).carrier ∧
        Hm *ᵥ y = c • u + (p : R) • u') ∧
      ∀ u : Fin g → R, ∃ x : Ix E n → C,
        (∀ l ∈ afLat p (hopfPull φ AA).carrier, v (∑ j, algebraMap R C (l j) * x j) ≤ 1) ∧
        Hm.map (algebraMap R C) *ᵥ x = fun k => algebraMap R C (u k) := by
  subst hM
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨cA, cN, cO, hA, hN, hO, hAN, hON⟩ := ht
  have hcardN : Fintype.card (Ix E n → ZMod p) = Fintype.card (TestPt.NAdd E n p) :=
    Fintype.card_congr φ.toEquiv
  have hOb : cO ≤ v (p : C) ^ g := om_bound hv AA Dv hD S hS hs hO
  have hOA : cO = cA ^ (p - 1) := by
    have hne : Fintype.card (TestPt.NAdd E n p) ≠ 0 := Fintype.card_ne_zero
    have hpow : cO ^ Fintype.card (TestPt.NAdd E n p) =
        (cA ^ (p - 1)) ^ Fintype.card (TestPt.NAdd E n p) := by
      rw [hON, ← hAN, ← pow_mul, mul_comm]
    exact (pow_left_inj₀ zero_le zero_le hne).1 hpow
  set T : AA.carrier ≃ₗ[R] (hopfPull φ AA).carrier := (pbE φ).submoduleMap AA.carrier with hTdef
  have hT : ∀ (f : (hopfPull φ AA).carrier) (y : TestPt.NAdd E n p), (T.symm f).1 y = f.1 (φ.symm y) := by
    intro f y
    conv_rhs => rw [← T.apply_symm_apply f]
    show _ = (T.symm f).1 (φ (φ.symm y))
    rw [AddEquiv.apply_symm_apply]
  let Dv' : (hopfPull φ AA).carrier →ₗ[R] (Fin g → R ⧸ Ideal.span {(p : R)}) :=
    qq p R g ∘ₗ Dv ∘ₗ T.symm.toLinearMap
  have hD' : IsDerAt0 _ Dv' := by
    intro f f2 h a b hh ha hb
    have hh' : (T.symm h).1 = (T.symm f).1 * (T.symm f2).1 := by
      funext y
      rw [Pi.mul_apply, hT, hT, hT, hh, Pi.mul_apply]
    have ha' : algebraMap R C a = (T.symm f).1 0 := by rw [hT, map_zero, ha]
    have hb' : algebraMap R C b = (T.symm f2).1 0 := by rw [hT, map_zero, hb]
    show qq p R g (Dv (T.symm h)) = a • qq p R g (Dv (T.symm f2)) + b • qq p R g (Dv (T.symm f))
    rw [hD _ _ _ a b hh' ha' hb', map_add, map_smul, map_smul]
  have hsurj : Function.Surjective Dv' := by
    intro w
    obtain ⟨a, ha⟩ := surj_aug Dv S hS hs w
    refine ⟨T (Submodule.inclusion (aug_le AA.carrier) a), ?_⟩
    show qq p R g (Dv (T.symm (T _))) = w
    rw [T.symm_apply_apply]
    exact ha
  obtain ⟨Kf, hKf, hKv⟩ := hK
  have hK' := comp_mem_tens_map_pbE_of_addEquiv φ AA.carrier hKf
  have hfun : (fun z : (Ix E n → ZMod p) × (Ix E n → ZMod p) =>
      ζ ^ (z.1 ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z.2).val) =
      fun z => Kf (φ z.1, φ z.2) := by
    funext z
    rcases z with ⟨z1, z2⟩
    obtain ⟨x, rfl⟩ := co_surj p z1
    obtain ⟨x', rfl⟩ := co_surj p z2
    simp only [hφ, hKv, cast_pair hm e x x', pow_val_cast hm hζ.pow_eq_one]
  have htens : (fun z : (Ix E n → ZMod p) × (Ix E n → ZMod p) =>
      ζ ^ (z.1 ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z.2).val) ∈
      tens (hopfPull φ AA).carrier (hopfPull φ AA).carrier := by
    rw [hfun]
    exact hK'
  have hEg : ∀ a b, Eg a b - ((((Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) :
      Matrix (Ix E n) (Ix E n) (ZMod p)) a b).val : R) ∈ Ideal.span {(p : R)} := by
    intro a b
    rw [Matrix.of_apply]
    have hsum := Ideal.add_mem _ (hE a b) (val_cast_sub (R := R) hm (e (dl a) (dl b)))
    rwa [sub_add_sub_cancel] at hsum
  have hchar : ∀ (x : Ix E n → ZMod p) (f : (hopfPull φ AA).carrier),
      (∀ z, f.1 z = ζ ^ (x ⬝ᵥ (Matrix.of fun a b => ZMod.castHom hm (ZMod p) (e (dl a) (dl b))) *ᵥ z).val) →
      Dv' f = fun k => Ideal.Quotient.mk (Ideal.span {(p : R)}) (∑ m, Hm k m * ((x m).val : R)) := by
    intro x f hf
    obtain ⟨x0, rfl⟩ := co_surj p x
    have h1 : ∀ x', (T.symm f).1 (mkN p x') = ζ ^ (e x0 x').val := by
      intro x'
      rw [← hφ, hT, AddEquiv.symm_apply_apply, hf, cast_pair hm e x0 x', pow_val_cast hm hζ.pow_eq_one]
    have h2 := hch x0 (T.symm f) h1
    show qq p R g (Dv (T.symm f)) = _
    rw [h2, qq_mk]
    funext k
    rw [Ideal.Quotient.eq]
    have hih : ih x0 k = ∑ m, ih (dl m) k * (cz x0 m : R) := by
      conv_lhs => rw [← sum_cz x0]
      simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    have hA' := sum_co_sub p (Hm k) x0
    have hB : ∑ m, (Hm k m - ih (dl m) k) * (cz x0 m : R) ∈ Ideal.span {(p : R)} :=
      Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hH m k)
    have heq : ih x0 k - ∑ m, Hm k m * (((co p x0) m).val : R) =
        -(∑ m, Hm k m * (((co p x0) m).val : R) - ∑ m, Hm k m * (cz x0 m : R)) -
          ∑ m, (Hm k m - ih (dl m) k) * (cz x0 m : R) := by
      rw [hih]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 hA') hB
  exact core hv hp hp2 (hopfPull φ AA) hcard (hasLen_AFQuot_map_pbE_of_addEquiv φ p AA.carrier hA)
    (hasColen_map v φ AA.carrier cN hN) (by rw [hcardN]; exact hAN) (by rw [← hOA]; exact hOb) hζ _ htens
    Dv' hD' hsurj Hm Eg Ei hEt hEi hiso hEg hchar

end PositivityTheory.HtPt.Sgp
