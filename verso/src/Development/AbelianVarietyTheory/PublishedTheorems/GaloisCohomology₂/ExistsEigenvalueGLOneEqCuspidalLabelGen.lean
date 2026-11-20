import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

noncomputable section
namespace GlobalTheory.Published.GreenModel
open Polynomial Formalism.CyclotomicNorms GlobalTheory.GLq GlobalTheory.GLq.Model CategoryTheory

open Polynomial CategoryTheory in
/- English proof (translation)
Set `V : FDRep ℂ G` to `FDRep.of ((Algebra.lmul ℂ ℂ).toMonoidHom.comp φ)`. Establish `hV : ∀ x, V.character x = φ x` using `fun x => Algebra.trace_self_apply (φ x)`. Use `⟨V, ?_, hV⟩` and prove the remaining obligations. Rewrite using `[FDRep.simple_iff_char_is_norm_one]`. Simplify using `only [hV, ← map_mul, mul_inv_cancel, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x => φ x) := by
  let V : FDRep ℂ G := FDRep.of ((Algebra.lmul ℂ ℂ).toMonoidHom.comp φ)
  have hV : ∀ x, V.character x = φ x := fun x => Algebra.trace_self_apply (φ x)
  refine ⟨V, ?_, hV⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp only [hV, ← map_mul, mul_inv_cancel, map_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/- English proof (translation)
Take `⟨V, hV, hχ⟩` from `h`. Establish `h1 : ∀ y : G, ∃ c : ℂ, V.ρ y = c • (1 : Module.End ℂ V)` using `fun y => PI.CharIdemW.schur_scalar V _ fun x => by rw [← map_mul, ← map_mul, hG]`. Use `choose c hc using h1`. Establish `hne` using `PI.CharIdemW.end_one_ne_zero V`. Establish `inj : ∀ a b : ℂ, a • (1 : Module.End ℂ V) = b • 1 → a = b` using `fun a b hab => smul_left_injective ℂ hne hab`.

Establish `c1 : c 1 = 1` using `inj _ _ (by rw [← hc, map_one, one_smul])`. Establish `cm : ∀ x y, c (x * y) = c x * c y` using `fun x y => inj _ _ (by`. Rewrite using `[← hc, map_mul, hc x, hc y, smul_mul_smul_comm, one_mul])`. Establish `hch : ∀ x, V.character x = c x * (Module.finrank ℂ V : ℂ)` using `fun x => by`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ V (V.ρ x) = _`.

Rewrite using `[hc x, map_smul, LinearMap.trace_one, smul_eq_mul]`. Establish `hn` using `(FDRep.simple_iff_char_is_norm_one V).1 hV`. Establish `e : ∀ x, V.character x * V.character x⁻¹ = (Module.finrank ℂ V : ℂ) ^ 2` using `fun x => by`. Rewrite using `[hch, hch]`. Establish `: c x * c x⁻¹ = 1` using `by rw [← cm, mul_inv_cancel, c1]`.

Take the linear combination `(Module.finrank ℂ V : ℂ) ^ 2 * this`. Simplify using `only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card] at hn`. Establish `hcard : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `h2 : (Module.finrank ℂ V : ℂ) ^ 2 = 1` using `mul_left_cancel₀ hcard (by rw [hn, mul_one])`. Establish `h3 : Module.finrank ℂ V = 1`.

Establish `: Module.finrank ℂ V ^ 2 = 1` using `by exact_mod_cast h2`. Conclude with `(Nat.pow_eq_one.1 this).resolve_right (by norm_num)`. Use `⟨⟨⟨c, c1⟩, cm⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hχ, hch, h3]`. Simplify using the standard rewrite rules.
-/
theorem hom_of_isIrr {G : Type} [Group G] [Fintype G] (hG : ∀ x y : G, x * y = y * x) {χ : G → ℂ}
    (h : IsIrr χ) : ∃ φ : G →* ℂ, ∀ x, χ x = φ x := by
  obtain ⟨V, hV, hχ⟩ := h
  have h1 : ∀ y : G, ∃ c : ℂ, V.ρ y = c • (1 : Module.End ℂ V) := fun y =>
    PI.CharIdemW.schur_scalar V _ fun x => by rw [← map_mul, ← map_mul, hG]
  choose c hc using h1
  have hne := PI.CharIdemW.end_one_ne_zero V
  have inj : ∀ a b : ℂ, a • (1 : Module.End ℂ V) = b • 1 → a = b := fun a b hab =>
    smul_left_injective ℂ hne hab
  have c1 : c 1 = 1 := inj _ _ (by rw [← hc, map_one, one_smul])
  have cm : ∀ x y, c (x * y) = c x * c y := fun x y => inj _ _ (by
    rw [← hc, map_mul, hc x, hc y, smul_mul_smul_comm, one_mul])
  have hch : ∀ x, V.character x = c x * (Module.finrank ℂ V : ℂ) := fun x => by
    change LinearMap.trace ℂ V (V.ρ x) = _
    rw [hc x, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hn := (FDRep.simple_iff_char_is_norm_one V).1 hV
  have e : ∀ x, V.character x * V.character x⁻¹ = (Module.finrank ℂ V : ℂ) ^ 2 := fun x => by
    rw [hch, hch]
    have : c x * c x⁻¹ = 1 := by rw [← cm, mul_inv_cancel, c1]
    linear_combination (Module.finrank ℂ V : ℂ) ^ 2 * this
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card] at hn
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Module.finrank ℂ V : ℂ) ^ 2 = 1 := mul_left_cancel₀ hcard (by rw [hn, mul_one])
  have h3 : Module.finrank ℂ V = 1 := by
    have : Module.finrank ℂ V ^ 2 = 1 := by exact_mod_cast h2
    exact (Nat.pow_eq_one.1 this).resolve_right (by norm_num)
  refine ⟨⟨⟨c, c1⟩, cm⟩, fun x => ?_⟩
  rw [← hχ, hch, h3]; simp

variable {g : ℕ} [hg : Fact g.Prime]

def ev : Gn g 1 →* Fbar g where
  toFun y := algebraMap (ZMod g) (Fbar g) ((y : Mt g 1) 0 0)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.mul_apply]

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Introduce `x y h`. Establish `h' : (x : _root_.GlobalTheory.GLq.Mt g 1) 0 0 = (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0` using `(algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective h`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Conclude with `h'`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.ev_inj :
    Function.Injective (_root_.GlobalTheory.Published.GreenModel.ev (g := g)) := by
  intro x y h
  have h' : (x : _root_.GlobalTheory.GLq.Mt g 1) 0 0 = (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0 :=
    (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective h
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact h'

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Rewrite using `[← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hb, map_one]`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.alg_pow {b : ZMod g} (hb : b ≠ 0) :
    algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) b ^ (g ^ 1 - 1) = 1 := by
  rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hb, map_one]

/- English proof (translation)
The claim follows from `alg_pow (by simpa [Matrix.det_fin_one] using y.det_ne_zero)`.
-/
theorem ev_pow (y : Gn g 1) : ev y ^ (g ^ 1 - 1) = 1 :=
  alg_pow (by simpa [Matrix.det_fin_one] using y.det_ne_zero)

/- English proof (translation)
Take `⟨r, hr⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)`. Establish `h0 : IsPrimitiveRoot r (g ^ 1 - 1)`. Establish `: g ^ 1 - 1 = orderOf r`. Rewrite using `[hr, Nat.card_eq_fintype_card, ZMod.card_units, pow_one]`. Rewrite using `[this]`.

Conclude with `IsPrimitiveRoot.orderOf r`. Establish `h1 : IsPrimitiveRoot (algebraMap (ZMod g) (Fbar g) r) (g ^ 1 - 1)` using `(IsPrimitiveRoot.coe_units_iff.2 h0).map_of_injective (algebraMap (ZMod g) (Fbar g)).injective`. Use `haveI : NeZero (g ^ 1 - 1) := ⟨(N_pos g one_pos).ne'⟩`. Take `⟨k, -, rfl⟩` from `h1.eq_pow_of_pow_eq_one hx`. Conclude with `⟨(r : ZMod g) ^ k, pow_ne_zero _ r.ne_zero, map_pow _ _ _⟩`.
-/
theorem exists_pre {x : Fbar g} (hx : x ^ (g ^ 1 - 1) = 1) :
    ∃ b : ZMod g, b ≠ 0 ∧ algebraMap (ZMod g) (Fbar g) b = x := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)
  have h0 : IsPrimitiveRoot r (g ^ 1 - 1) := by
    have : g ^ 1 - 1 = orderOf r := by
      rw [hr, Nat.card_eq_fintype_card, ZMod.card_units, pow_one]
    rw [this]; exact IsPrimitiveRoot.orderOf r
  have h1 : IsPrimitiveRoot (algebraMap (ZMod g) (Fbar g) r) (g ^ 1 - 1) :=
    (IsPrimitiveRoot.coe_units_iff.2 h0).map_of_injective (algebraMap (ZMod g) (Fbar g)).injective
  haveI : NeZero (g ^ 1 - 1) := ⟨(N_pos g one_pos).ne'⟩
  obtain ⟨k, -, rfl⟩ := h1.eq_pow_of_pow_eq_one hx
  exact ⟨(r : ZMod g) ^ k, pow_ne_zero _ r.ne_zero, map_pow _ _ _⟩

/- English proof (translation)
The claim follows from `L.gen_order 1 one_pos ▸ IsPrimitiveRoot.orderOf _`.
-/
theorem gen_prim' (L : LabelDatum g) : IsPrimitiveRoot (L.gen 1) (g ^ 1 - 1) :=
  L.gen_order 1 one_pos ▸ IsPrimitiveRoot.orderOf _

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Use `hg.out.two_le` as an intermediate fact. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem pow_one_sub_one_pos : 0 < g ^ 1 - 1 := by
  have := hg.out.two_le
  rw [pow_one]
  omega

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Rewrite using `[← L.gen_order 1 one_pos]`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
private theorem isPrimitiveRoot_gen_one (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    IsPrimitiveRoot (L.gen 1) (g ^ 1 - 1) := by
  rw [← L.gen_order 1 one_pos]
  exact IsPrimitiveRoot.orderOf _

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Establish `h : IsUnit (y : Matrix (Fin 1) (Fin 1) (ZMod g)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit`. Rewrite `h` using `[Matrix.det_fin_one]`. Conclude with `h.ne_zero`.
-/
private theorem gn_one_entry_zero_zero_ne_zero (y : _root_.GlobalTheory.GLq.Gn g 1) :
    (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0 ≠ 0 := by
  have h : IsUnit (y : Matrix (Fin 1) (Fin 1) (ZMod g)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  rw [Matrix.det_fin_one] at h
  exact h.ne_zero

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Use `haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩`. Take `⟨i, -, hi⟩` from `(isPrimitiveRoot_gen_one L).eq_pow_of_pow_eq_one (_root_.GlobalTheory.Published.GreenModel.alg_pow (gn_one_entry_zero_zero_ne_zero y))`. Conclude with `⟨i, hi.symm⟩`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.ev_eq (L : _root_.GlobalTheory.GLq.LabelDatum g) (y : _root_.GlobalTheory.GLq.Gn g 1) :
    ∃ n, _root_.GlobalTheory.Published.GreenModel.ev y = L.gen 1 ^ n := by
  haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩
  obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_gen_one L).eq_pow_of_pow_eq_one
    (_root_.GlobalTheory.Published.GreenModel.alg_pow (gn_one_entry_zero_zero_ne_zero y))
  exact ⟨i, hi.symm⟩

/- English proof (translation)
Take `⟨b, hb, h⟩` from `exists_pre (gen_prim' L).pow_eq_one`. Conclude with `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => b) (by rw [Matrix.det_fin_one]; exact hb), h⟩`.
-/
theorem exists_eigenvalueGLOne_eq_cuspidalLabel_gen (L : LabelDatum g) : ∃ y : Gn g 1, ev y = L.gen 1 := by
  obtain ⟨b, hb, h⟩ := exists_pre (gen_prim' L).pow_eq_one
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => b) (by rw [Matrix.det_fin_one]; exact hb), h⟩

def th (L : LabelDatum g) {b : ZMod g} (hb : b ≠ 0) : Gn g 1 →* ℂ where
  toFun y := thetaOf L 1 (algebraMap (ZMod g) (Fbar g) b) (ev y)
  map_one' := by
    have := thetaOf_gen_pow L one_pos (alg_pow hb) 0
    simpa using this
  map_mul' x y := by
    obtain ⟨m, hm⟩ := ev_eq L x
    obtain ⟨n, hn⟩ := ev_eq L y
    rw [map_mul, hm, hn, ← pow_add]
    simp only [thetaOf_gen_pow L one_pos (alg_pow hb)]
    rw [pow_add]

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Rewrite using `[map_neg, sub_neg_eq_add]`. Conclude with `h.1.eq_X_add_C h.2.2.2`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.lab_eq {P : (ZMod g)[X]}
    (h : _root_.GlobalTheory.GLq.IsPrimeLab 1 P) : P = X - C (-P.coeff 0) := by
  rw [map_neg, sub_neg_eq_add]
  exact h.1.eq_X_add_C h.2.2.2

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
Use `haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩`. Take `⟨u, hu⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)`. Establish `hu' : IsPrimitiveRoot (u : ZMod g) (g ^ 1 - 1)`. Rewrite using `[IsPrimitiveRoot.coe_units_iff, pow_one, ← ZMod.card_units g, ← Nat.card_eq_fintype_card, ← hu]`. Conclude with `IsPrimitiveRoot.orderOf u`.

Take `⟨i, -, hi⟩` from `(hu'.map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective).eq_pow_of_pow_eq_one (isPrimitiveRoot_gen_one L).pow_eq_one`. Establish `hc : (u : ZMod g) ^ i ≠ 0` using `pow_ne_zero _ u.ne_zero`. Set `y : GL (Fin 1) (ZMod g)` to `Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Matrix (Fin 1) (Fin 1) (ZMod g)).toMonoidHom (Units.mk0 _ hc)`. Establish `hy : (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0 = (u : ZMod g) ^ i`. Simplify using `[y, Matrix.scalar_apply]`.

Use `⟨_, hc, y, hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) ((y : _root_.GlobalTheory.GLq.Mt g 1) 0 0) = _`. Rewrite using `[hy, map_pow, hi]`.
-/
private theorem exists_ne_zero_gn_one_ev_eq_gen_one (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ c : ZMod g, c ≠ 0 ∧ ∃ y : _root_.GlobalTheory.GLq.Gn g 1,
      (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0 = c ∧ _root_.GlobalTheory.Published.GreenModel.ev y = L.gen 1 := by
  haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)
  have hu' : IsPrimitiveRoot (u : ZMod g) (g ^ 1 - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, pow_one, ← ZMod.card_units g, ← Nat.card_eq_fintype_card,
      ← hu]
    exact IsPrimitiveRoot.orderOf u
  obtain ⟨i, -, hi⟩ := (hu'.map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective).eq_pow_of_pow_eq_one
    (isPrimitiveRoot_gen_one L).pow_eq_one
  have hc : (u : ZMod g) ^ i ≠ 0 := pow_ne_zero _ u.ne_zero
  let y : GL (Fin 1) (ZMod g) :=
    Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Matrix (Fin 1) (Fin 1) (ZMod g)).toMonoidHom
      (Units.mk0 _ hc)
  have hy : (y : _root_.GlobalTheory.GLq.Mt g 1) 0 0 = (u : ZMod g) ^ i := by
    simp [y, Matrix.scalar_apply]
  refine ⟨_, hc, y, hy, ?_⟩
  change algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) ((y : _root_.GlobalTheory.GLq.Mt g 1) 0 0) = _
  rw [hy, map_pow, hi]

open Polynomial CategoryTheory in
/- English proof (translation)
Establish `hscalar : ∀ h : G, ∃ c : ℂ, V.ρ h = c • 1` using `fun h => _root_.PI.CharIdemW.schur_scalar V (V.ρ h) fun k => by rw [← map_mul, ← map_mul, hcomm]`. Use `choose c hc using hscalar`. Establish `hne : (1 : Module.End ℂ V.V) ≠ 0` using `_root_.PI.CharIdemW.end_one_ne_zero V`. Establish `hinj : Function.Injective fun t : ℂ => t • (1 : Module.End ℂ V.V)` using `smul_left_injective ℂ hne`. Establish `hmul : ∀ a b, c (a * b) = c a * c b`.

Introduce `a b`. Apply `hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← hc, map_mul, hc, hc, smul_mul_smul_comm, one_mul]`. Establish `hone : c 1 = 1`.

Apply `hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← hc, map_one, one_smul]`. Establish `hchar : ∀ h, V.character h = c h * (Module.finrank ℂ V.V : ℂ)`. Introduce `h`.

Rewrite using `[FDRep.character, hc, map_smul, LinearMap.trace_one, smul_eq_mul]`. Establish `hnorm` using `(FDRep.simple_iff_char_is_norm_one V).1 inferInstance`. Establish `hsum : ∀ h : G, V.character h * V.character h⁻¹ = (Module.finrank ℂ V.V : ℂ) ^ 2`. Introduce `h`. Rewrite using `[hchar, hchar]`.

Establish `: c h * c h⁻¹ = 1` using `by rw [← hmul, mul_inv_cancel, hone]`. Take the linear combination `(Module.finrank ℂ V.V : ℂ) ^ 2 * this`. Simplify using `only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card] at hnorm`. Establish `hcard : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `hsq : ((Module.finrank ℂ V.V ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ)`.

Use `push_cast`. Conclude with `(mul_eq_left₀ hcard).1 hnorm`. Establish `hn : Module.finrank ℂ V.V = 1`. Use `Nat.cast_injective hsq` as an intermediate fact. Simplify using `using this`.

Use `⟨by rw [hchar, hone, hn]; simp, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hchar, hchar, hchar, hmul, hn]`. Simplify using the standard rewrite rules.
-/
private theorem character_one_and_mul_of_simple_of_comm {G : Type} [Group G] [Fintype G]
    (hcomm : ∀ a b : G, a * b = b * a) (V : FDRep ℂ G) [Simple V] :
    V.character 1 = 1 ∧ ∀ a b, V.character (a * b) = V.character a * V.character b := by
  have hscalar : ∀ h : G, ∃ c : ℂ, V.ρ h = c • 1 := fun h =>
    _root_.PI.CharIdemW.schur_scalar V (V.ρ h) fun k => by rw [← map_mul, ← map_mul, hcomm]
  choose c hc using hscalar
  have hne : (1 : Module.End ℂ V.V) ≠ 0 := _root_.PI.CharIdemW.end_one_ne_zero V
  have hinj : Function.Injective fun t : ℂ => t • (1 : Module.End ℂ V.V) :=
    smul_left_injective ℂ hne
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hinj
    simp only
    rw [← hc, map_mul, hc, hc, smul_mul_smul_comm, one_mul]
  have hone : c 1 = 1 := by
    apply hinj
    simp only
    rw [← hc, map_one, one_smul]
  have hchar : ∀ h, V.character h = c h * (Module.finrank ℂ V.V : ℂ) := by
    intro h
    rw [FDRep.character, hc, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hnorm := (FDRep.simple_iff_char_is_norm_one V).1 inferInstance
  have hsum : ∀ h : G, V.character h * V.character h⁻¹ = (Module.finrank ℂ V.V : ℂ) ^ 2 := by
    intro h
    rw [hchar, hchar]
    have : c h * c h⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    linear_combination (Module.finrank ℂ V.V : ℂ) ^ 2 * this
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card] at hnorm
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsq : ((Module.finrank ℂ V.V ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    push_cast
    exact (mul_eq_left₀ hcard).1 hnorm
  have hn : Module.finrank ℂ V.V = 1 := by
    have := Nat.cast_injective hsq
    simpa using this
  refine ⟨by rw [hchar, hone, hn]; simp, fun a b => ?_⟩
  rw [hchar, hchar, hchar, hmul, hn]
  simp

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.Published.GreenModel.ev_inj (by rw [map_mul, map_mul, mul_comm])`.
-/
private theorem gn_one_mul_comm (x y : _root_.GlobalTheory.GLq.Gn g 1) : x * y = y * x :=
  _root_.GlobalTheory.Published.GreenModel.ev_inj (by rw [map_mul, map_mul, mul_comm])

open Polynomial CategoryTheory in
variable {g : ℕ} [hg : Fact g.Prime] in

/- English proof (translation)
Establish `hlab : ∀ {P : (ZMod g)[X]}, _root_.GlobalTheory.GLq.IsPrimeLab 1 P → -P.coeff 0 ≠ 0` using `fun h => neg_ne_zero.mpr h.2.2.1`. Use `⟨fun P => if h : _root_.GlobalTheory.GLq.IsPrimeLab 1 P then ⇑(_root_.GlobalTheory.Published.GreenModel.th L (hlab h)) else fun _ => 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Simplify using `only [dif_pos hP]`. Use `⟨⟨hP, ⟨one_pos, _root_.GlobalTheory.Published.GreenModel.isIrr_hom _, fun a ha ha' => absurd ha' (by omega)⟩, ?_⟩, by simp⟩` and prove the remaining obligations.

Introduce `x hx y _ z hz`. Establish `hPe` using `_root_.GlobalTheory.Published.GreenModel.lab_eq hP`. Establish `hx' : x = algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)`. Unfold `_root_.Formalism.CyclotomicNorms.rootsBar at hx`. Rewrite `hx` using `[hPe, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.mem_singleton]`.

Conclude with `hx`. Establish `hcp : (y : Matrix (Fin 1) (Fin 1) (ZMod g)).charpoly = X - C ((y : Matrix (Fin 1) (Fin 1) (ZMod g)) 0 0)`. Rewrite using `[Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]`. Establish `hz' : z = _root_.GlobalTheory.Published.GreenModel.ev y`. Unfold `_root_.Formalism.CyclotomicNorms.rootsBar at hz`.

Rewrite `hz` using `[hcp, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.mem_singleton]`. Conclude with `hz`. Substitute `hx' hz'` using the available equality. Simplify using `only [Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one]`. Both sides reduce to the same expression.

Introduce `P P' hP hP' he`. Take `⟨c, hc, y0, -, hy0⟩` from `exists_ne_zero_gn_one_ev_eq_gen_one L`. Establish `h1` using `congrFun he y0`. Simplify using `only [dif_pos hP, dif_pos hP'] at h1`. Establish `key : ∀ {b : ZMod g} (hb : b ≠ 0), _root_.GlobalTheory.Published.GreenModel.th L hb y0 = L.teich (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) b)`.

Introduce `b hb`. Express the relevant statement in the definitionally equal form `_root_.GlobalTheory.GLq.thetaOf L 1 _ (_root_.GlobalTheory.Published.GreenModel.ev y0) = _`. Rewrite using `[hy0, ← pow_one (L.gen 1), _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (_root_.GlobalTheory.Published.GreenModel.alg_pow hb), pow_one]`. Rewrite `h1` using `[key, key]`. Establish `h2` using `L.teich_inj _ _ ((_root_.map_ne_zero _).2 (hlab hP)) ((_root_.map_ne_zero _).2 (hlab hP')) h1`.

Establish `hb` using `(algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective h2`. Rewrite using `[_root_.GlobalTheory.Published.GreenModel.lab_eq hP, _root_.GlobalTheory.Published.GreenModel.lab_eq hP', hb]`. Introduce `χ hχ`. Take `⟨-, ⟨V, hVs, hV⟩, -⟩` from `hχ`. Use `haveI := hVs`.

Establish `hm` using `character_one_and_mul_of_simple_of_comm gn_one_mul_comm V`. Set `ψ : _root_.GlobalTheory.GLq.Gn g 1 →* ℂ` to `{ toFun := χ map_one' := by rw [← hV]; exact hm.1 map_mul' := fun a b => by simp only [← hV]; exact hm.2 a b }`. Take `⟨c, hc, y0, hyc, hy0⟩` from `exists_ne_zero_gn_one_ev_eq_gen_one L`. Establish `hcg : algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) c = L.gen 1`. Rewrite using `[← hyc]`.

Conclude with `hy0`. Establish `hgen0 : L.gen 1 ≠ 0`. Rewrite using `[← hcg]`. Conclude with `(_root_.map_ne_zero _).2 hc`. Establish `hζ : IsPrimitiveRoot (L.teich (L.gen 1)) (g ^ 1 - 1)`.

Use `IsPrimitiveRoot.mk_of_lt _ pow_one_sub_one_pos ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, (isPrimitiveRoot_gen_one L).pow_eq_one, map_one]`. Introduce `l hl hl' h`. Rewrite `h` using `[← map_pow, ← map_one L.teich]`. Use `L.teich_inj _ _ (pow_ne_zero _ hgen0) one_ne_zero h` as an intermediate fact.

Use `pow_ne_one_of_lt_orderOf hl.ne' ?_ this` and prove the remaining obligations. Rewrite using `[L.gen_order 1 one_pos]`. Conclude with `hl'`. Establish `hy0pow : y0 ^ (g ^ 1 - 1) = 1` using `_root_.GlobalTheory.Published.GreenModel.ev_inj (by`. Rewrite using `[map_pow, hy0, (isPrimitiveRoot_gen_one L).pow_eq_one, map_one])`.

Use `haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩`. Take `⟨k, -, hk⟩` from `hζ.eq_pow_of_pow_eq_one (show ψ y0 ^ (g ^ 1 - 1) = 1 by rw [← map_pow, hy0pow, map_one])`. Establish `hck : c ^ k ≠ 0` using `pow_ne_zero _ hc`. Establish `hP : _root_.GlobalTheory.GLq.IsPrimeLab 1 (X - C (c ^ k))` using `⟨monic_X_sub_C _, irreducible_X_sub_C _, by`. Rewrite using `[coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_ne_zero]`.

Conclude with `hck,`. Use `natDegree_X_sub_C _⟩`. Use `⟨X - C (c ^ k), hP, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `only [dif_pos hP]`.

Take `⟨n, hn⟩` from `_root_.GlobalTheory.Published.GreenModel.ev_eq L y`. Establish `hy : y = y0 ^ n` using `_root_.GlobalTheory.Published.GreenModel.ev_inj (by rw [hn, map_pow, hy0])`. Express the relevant statement in the definitionally equal form `χ y = _root_.GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) (-(X - C (c ^ k) : (ZMod g)[X]).coeff 0)) (_root_.GlobalTheory.Published.GreenModel.ev y)`. Rewrite using `[hn, _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (_root_.GlobalTheory.Published.GreenModel.alg_pow (hlab hP))]`. Establish `hcoef : -(X - C (c ^ k) : (ZMod g)[X]).coeff 0 = c ^ k`.

Rewrite using `[coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg]`. Rewrite using `[hcoef, map_pow, hcg, map_pow, hk, hy]`. Conclude with `map_pow ψ y0 n`.
-/
theorem _root_.GlobalTheory.Published.GreenModel.green_one (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ τ : (ZMod g)[X] → _root_.GlobalTheory.GLq.Gn g 1 → ℂ,
    (∀ P, _root_.GlobalTheory.GLq.IsPrimeLab 1 P → _root_.GlobalTheory.GLq.IsCuspOf L P (τ P) ∧
      τ P 1 = ∏ i ∈ Finset.Ico 1 1, ((g : ℂ) ^ i - 1)) ∧
    (∀ P P', _root_.GlobalTheory.GLq.IsPrimeLab 1 P → _root_.GlobalTheory.GLq.IsPrimeLab 1 P' →
      τ P = τ P' → P = P') ∧
    ∀ χ : _root_.GlobalTheory.GLq.Gn g 1 → ℂ, _root_.GlobalTheory.GLq.IsCusp χ →
      ∃ P, _root_.GlobalTheory.GLq.IsPrimeLab 1 P ∧ χ = τ P := by
  classical
  have hlab : ∀ {P : (ZMod g)[X]}, _root_.GlobalTheory.GLq.IsPrimeLab 1 P → -P.coeff 0 ≠ 0 :=
    fun h => neg_ne_zero.mpr h.2.2.1
  refine ⟨fun P => if h : _root_.GlobalTheory.GLq.IsPrimeLab 1 P then
      ⇑(_root_.GlobalTheory.Published.GreenModel.th L (hlab h)) else fun _ => 0, ?_, ?_, ?_⟩
  · intro P hP
    simp only [dif_pos hP]
    refine ⟨⟨hP, ⟨one_pos, _root_.GlobalTheory.Published.GreenModel.isIrr_hom _,
      fun a ha ha' => absurd ha' (by omega)⟩, ?_⟩, by simp⟩
    intro x hx y _ z hz
    have hPe := _root_.GlobalTheory.Published.GreenModel.lab_eq hP
    have hx' : x = algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) := by
      unfold _root_.Formalism.CyclotomicNorms.rootsBar at hx
      rw [hPe, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.mem_singleton] at hx
      exact hx
    have hcp : (y : Matrix (Fin 1) (Fin 1) (ZMod g)).charpoly =
        X - C ((y : Matrix (Fin 1) (Fin 1) (ZMod g)) 0 0) := by
      rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    have hz' : z = _root_.GlobalTheory.Published.GreenModel.ev y := by
      unfold _root_.Formalism.CyclotomicNorms.rootsBar at hz
      rw [hcp, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.mem_singleton] at hz
      exact hz
    subst hx' hz'
    simp only [Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one]
    rfl
  · intro P P' hP hP' he
    obtain ⟨c, hc, y0, -, hy0⟩ := exists_ne_zero_gn_one_ev_eq_gen_one L
    have h1 := congrFun he y0
    simp only [dif_pos hP, dif_pos hP'] at h1
    have key : ∀ {b : ZMod g} (hb : b ≠ 0), _root_.GlobalTheory.Published.GreenModel.th L hb y0 =
        L.teich (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) b) := by
      intro b hb
      change _root_.GlobalTheory.GLq.thetaOf L 1 _ (_root_.GlobalTheory.Published.GreenModel.ev y0) = _
      rw [hy0, ← pow_one (L.gen 1),
        _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (_root_.GlobalTheory.Published.GreenModel.alg_pow hb), pow_one]
    rw [key, key] at h1
    have h2 := L.teich_inj _ _ ((_root_.map_ne_zero _).2 (hlab hP))
      ((_root_.map_ne_zero _).2 (hlab hP')) h1
    have hb := (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective h2
    rw [_root_.GlobalTheory.Published.GreenModel.lab_eq hP,
      _root_.GlobalTheory.Published.GreenModel.lab_eq hP', hb]
  · intro χ hχ
    obtain ⟨-, ⟨V, hVs, hV⟩, -⟩ := hχ
    haveI := hVs
    have hm := character_one_and_mul_of_simple_of_comm gn_one_mul_comm V
    let ψ : _root_.GlobalTheory.GLq.Gn g 1 →* ℂ :=
      { toFun := χ
        map_one' := by rw [← hV]; exact hm.1
        map_mul' := fun a b => by simp only [← hV]; exact hm.2 a b }
    obtain ⟨c, hc, y0, hyc, hy0⟩ := exists_ne_zero_gn_one_ev_eq_gen_one L
    have hcg : algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) c = L.gen 1 := by
      rw [← hyc]; exact hy0
    have hgen0 : L.gen 1 ≠ 0 := by
      rw [← hcg]; exact (_root_.map_ne_zero _).2 hc
    have hζ : IsPrimitiveRoot (L.teich (L.gen 1))
        (g ^ 1 - 1) := by
      refine IsPrimitiveRoot.mk_of_lt _ pow_one_sub_one_pos ?_ ?_
      · rw [← map_pow, (isPrimitiveRoot_gen_one L).pow_eq_one, map_one]
      · intro l hl hl' h
        rw [← map_pow, ← map_one L.teich] at h
        have := L.teich_inj _ _ (pow_ne_zero _ hgen0) one_ne_zero h
        refine pow_ne_one_of_lt_orderOf hl.ne' ?_ this
        rw [L.gen_order 1 one_pos]
        exact hl'
    have hy0pow : y0 ^ (g ^ 1 - 1) = 1 := _root_.GlobalTheory.Published.GreenModel.ev_inj (by
      rw [map_pow, hy0, (isPrimitiveRoot_gen_one L).pow_eq_one, map_one])
    haveI : NeZero (g ^ 1 - 1) := ⟨pow_one_sub_one_pos.ne'⟩
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one
      (show ψ y0 ^ (g ^ 1 - 1) = 1 by rw [← map_pow, hy0pow, map_one])
    have hck : c ^ k ≠ 0 := pow_ne_zero _ hc
    have hP : _root_.GlobalTheory.GLq.IsPrimeLab 1 (X - C (c ^ k)) :=
      ⟨monic_X_sub_C _, irreducible_X_sub_C _, by
        rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_ne_zero]; exact hck,
      natDegree_X_sub_C _⟩
    refine ⟨X - C (c ^ k), hP, ?_⟩
    funext y
    simp only [dif_pos hP]
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.Published.GreenModel.ev_eq L y
    have hy : y = y0 ^ n := _root_.GlobalTheory.Published.GreenModel.ev_inj (by rw [hn, map_pow, hy0])
    change χ y = _root_.GlobalTheory.GLq.thetaOf L 1
      (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) (-(X - C (c ^ k) : (ZMod g)[X]).coeff 0))
      (_root_.GlobalTheory.Published.GreenModel.ev y)
    rw [hn, _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (_root_.GlobalTheory.Published.GreenModel.alg_pow (hlab hP))]
    have hcoef : -(X - C (c ^ k) : (ZMod g)[X]).coeff 0 = c ^ k := by
      rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg]
    rw [hcoef, map_pow, hcg, map_pow, hk, hy]
    exact map_pow ψ y0 n

/- English proof (translation)
Use `and_congr ⟨fun h => h 1 0 (by simp) (by simp), fun h i j hj hi => ?_⟩ (and_congr ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h => ?_, fun h => ?_⟩)` and prove the remaining obligations. Establish `h1 : i = 1` using `Fin.ext (by have := i.2; simp; omega)`. Establish `h2 : j = 0` using `Fin.ext (by simp; omega)`. Rewrite using `[h1, h2, h]`. Simplify `congrFun (congrFun h 0) 0` using `[tl, Formalism.MainNotions.ArithmeticCylinders.entN]`.

Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify `h` using `[tl, Formalism.MainNotions.ArithmeticCylinders.entN]`. Simplify `congrFun (congrFun h 0) 0` using `[br, Formalism.MainNotions.ArithmeticCylinders.entN]`. Use extensionality with `i j`.

Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify `h` using `[br, Formalism.MainNotions.ArithmeticCylinders.entN]`.
-/
theorem unip_two (x : Mt g 2) :
    (InPar 1 x ∧ tl 1 x = ((1 : Gn g 1) : Mt g 1) ∧ br 1 1 x = ((1 : Gn g 1) : Mt g 1)) ↔
      x 1 0 = 0 ∧ x 0 0 = 1 ∧ x 1 1 = 1 := by
  refine and_congr ⟨fun h => h 1 0 (by simp) (by simp), fun h i j hj hi => ?_⟩ (and_congr ⟨fun h => ?_, fun h => ?_⟩
    ⟨fun h => ?_, fun h => ?_⟩)
  · have h1 : i = 1 := Fin.ext (by have := i.2; simp; omega)
    have h2 : j = 0 := Fin.ext (by simp; omega)
    rw [h1, h2, h]
  · simpa [tl, Formalism.MainNotions.ArithmeticCylinders.entN] using congrFun (congrFun h 0) 0
  · ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simpa [tl, Formalism.MainNotions.ArithmeticCylinders.entN] using h
  · simpa [br, Formalism.MainNotions.ArithmeticCylinders.entN] using congrFun (congrFun h 0) 0
  · ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simpa [br, Formalism.MainNotions.ArithmeticCylinders.entN] using h

/- English proof (translation)
Introduce `h`. Establish `h1` using `h.2.2 1 one_pos (by norm_num)`. Unfold `res at h1`. Establish `hg0 : ((g : ℂ) ^ (1 * (2 - 1)))⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hg.out.ne_zero))`. Establish `h2` using `(mul_eq_zero.1 h1).resolve_left hg0`.

Rewrite `h2` using `[Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `h2 (Finset.mem_univ 1) ((unip_two _).2 (by simp))`.
-/
theorem not_isCusp_one_two : ¬ IsCusp (fun _ : Gn g 2 => (1 : ℂ)) := by
  classical
  intro h
  have h1 := h.2.2 1 one_pos (by norm_num)
  unfold res at h1
  have hg0 : ((g : ℂ) ^ (1 * (2 - 1)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hg.out.ne_zero))
  have h2 := (mul_eq_zero.1 h1).resolve_left hg0
  rw [Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h2
  exact h2 (Finset.mem_univ 1) ((unip_two _).2 (by simp))

/- English proof (translation)
Assemble the required witnesses or components as `⟨datum g⟩`.
-/
theorem datum_nonempty : Nonempty (LabelDatum g) := ⟨datum g⟩

end GlobalTheory.Published.GreenModel
