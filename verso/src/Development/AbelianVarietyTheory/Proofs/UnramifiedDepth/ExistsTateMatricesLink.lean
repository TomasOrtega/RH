import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.DualLattices.CharR
import ReciprocityTheory.DualLattices.SubMemSpan
import ReciprocityTheory.DualLattices.ThmAAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory

namespace TateMatrices

section Pairing

variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

/- English proof (translation)
Take `⟨z, hz⟩` from `B.pairing_exists N 0 y (smul_zero N) hy`. Establish `h2` using `B.isPairingValue_add_left N 0 0 y z z hz hz`. Rewrite `h2` using `[add_zero]`. Establish `h3 : z * z = z` using `B.pairing_unique N 0 y _ _ h2 hz`. Establish `h4 : z = 1` using `mul_eq_left.1 h3`.

Rewrite `hz` using `[h4]`. Then use the resulting hypothesis.
-/
lemma pairing_zero_left (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_nsmul, pow_zero]`. Conclude with `pairing_zero_left B N y h.2.1`. Consider the case `succ n ih`.

Rewrite using `[succ_nsmul, pow_succ]`. Conclude with `B.isPairingValue_add_left N _ _ _ _ _ ih h`.
-/
lemma pairing_nsmul_left (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, pow_zero]`. Conclude with `pairing_zero_left B N y hy`. Consider the case `insert b s hb ih`.

Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb, pow_add, mul_comm (a b), pow_mul]`. Conclude with `B.isPairingValue_add_left N _ _ _ _ _ (pairing_nsmul_left B N _ _ _ (h b) _) ih`.
-/
lemma pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (ζ : (R : Type)ˣ) (a e : ι → ℕ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (ζ ^ e i)) :
    B.IsPairing N (∑ i ∈ s, a i • x i) y (ζ ^ ∑ i ∈ s, a i * e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, pow_zero]
    exact pairing_zero_left B N y hy
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, pow_add, mul_comm (a b), pow_mul]
    exact B.isPairingValue_add_left N _ _ _ _ _ (pairing_nsmul_left B N _ _ _ (h b) _) ih

/- English proof (translation)
Establish `h1` using `pairing_sum_left B s N x y ζ⁻¹ a e hy fun i => by`. Rewrite using `[inv_pow]`. Conclude with `B.pairing_sw N _ _ _ (h i)`. Establish `h2` using `B.pairing_sw N _ _ _ h1`. Rewrite `h2` using `[inv_pow, inv_inv]`.

Simplify `h2` using `only [mul_comm]`.
-/
lemma pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (ζ : (R : Type)ˣ) (a e : ι → ℕ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N y (x i) (ζ ^ e i)) :
    B.IsPairing N y (∑ i ∈ s, a i • x i) (ζ ^ ∑ i ∈ s, e i * a i) := by
  have h1 := pairing_sum_left B s N x y ζ⁻¹ a e hy fun i => by
    rw [inv_pow]; exact B.pairing_sw N _ _ _ (h i)
  have h2 := B.pairing_sw N _ _ _ h1
  rw [inv_pow, inv_inv] at h2
  simpa only [mul_comm] using h2

/- English proof (translation)
Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => simp [BX.ev]`. Consider the case `tmul x r`. Simplify using `only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply, TensorProduct.comm_tmul, Module.Basis.baseChange_repr_tmul]`. Use `conv_lhs => rw [← gb.sum_repr x]`.

Rewrite using `[map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add a b ha hb`.

Simplify using `only [BX.ev, map_add] at *`. Rewrite using `[ha, hb, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by rw [Finsupp.add_apply]; ring`.
-/
lemma ev_expand {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, (Module.Basis.baseChange (O : Type) gb).repr
      (TensorProduct.comm R₀ B.gg (O : Type) b) a * h (gb a) := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      TensorProduct.comm_tmul, Module.Basis.baseChange_repr_tmul]
    conv_lhs => rw [← gb.sum_repr x]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [Finsupp.add_apply]; ring

end Pairing

section Padic

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`.
-/
lemma sub_val_mem (n : ℕ) (c : ℤ_[p]) :
    c - ((PadicInt.toZModPow n c).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
    sub_self]

/- English proof (translation)
Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (sub_val_mem n c)`. Establish `h2` using `congrArg φ hb`. Rewrite `h2` using `[map_mul, map_pow, map_natCast, h, mul_zero, map_sub, map_natCast]`. Conclude with `(sub_eq_zero.1 h2.symm)`.
-/
lemma map_eq_val {S : Type} [CommRing S] (φ : ℤ_[p] →+* S) (n : ℕ) (h : (p : S) ^ n = 0)
    (c : ℤ_[p]) : φ c = ((PadicInt.toZModPow n c).val : S) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (sub_val_mem n c)
  have h2 := congrArg φ hb
  rw [map_mul, map_pow, map_natCast, h, mul_zero, map_sub, map_natCast] at h2
  exact (sub_eq_zero.1 h2.symm)

/- English proof (translation)
Rewrite using `[ZMod.val_natCast]`. Use `conv_rhs => rw [← Nat.mod_add_div m N, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]`.
-/
lemma val_natCast_smul {Γ : Type} [AddCommGroup Γ] (N m : ℕ) (x : Γ) (hx : N • x = 0) :
    (m : ZMod N).val • x = m • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div m N, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]

/- English proof (translation)
Rewrite using `[map_eq_val (PadicInt.toZMod (p := p)) (0 + 1) (by simp) c, val_natCast_smul p _ x hx]`.
-/
lemma toZMod_val_smul {Γ : Type} [AddCommGroup Γ] (c : ℤ_[p]) (x : Γ) (hx : p • x = 0) :
    (PadicInt.toZMod c).val • x = (PadicInt.toZModPow (0 + 1) c).val • x := by
  rw [map_eq_val (PadicInt.toZMod (p := p)) (0 + 1) (by simp) c, val_natCast_smul p _ x hx]

/- English proof (translation)
Rewrite using `[← add_nsmul, ← val_natCast_smul p (a.val + b.val) x hx]`. Simplify using the standard rewrite rules.
-/
lemma val_add_smul {Γ : Type} [AddCommGroup Γ] (a b : ZMod p) (x : Γ) (hx : p • x = 0) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [← add_nsmul, ← val_natCast_smul p (a.val + b.val) x hx]
  simp

/- English proof (translation)
Rewrite using `[← mul_nsmul', ← val_natCast_smul p (a.val * b.val) x hx]`. Simplify using the standard rewrite rules.
-/
lemma val_mul_smul {Γ : Type} [AddCommGroup Γ] (a b : ZMod p) (x : Γ) (hx : p • x = 0) :
    (a * b).val • x = a.val • b.val • x := by
  rw [← mul_nsmul', ← val_natCast_smul p (a.val * b.val) x hx]
  simp

/- English proof (translation)
Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`. Break down `n with _ | n` into its components or cases. Use `haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance`. Conclude with `Subsingleton.elim _ _`.

Establish `h1` using `h n`. Rewrite `h1` using `[pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf, ← ZMod.natCast_eq_natCast_iff]`. Simplify using `using h1`.
-/
lemma eq_of_zeta_pow {G : Type} [CommGroup G] {κ : Type} [Fintype κ] (ζ : ℕ → G)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (p ^ (n + 1))) (a b c d : κ → ℤ_[p])
    (h : ∀ n, ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (a k)).val * (PadicInt.toZModPow (n + 1) (b k)).val) =
      ζ n ^ (∑ k, (PadicInt.toZModPow (n + 1) (c k)).val * (PadicInt.toZModPow (n + 1) (d k)).val)) :
    ∑ k, a k * b k = ∑ k, c k * d k := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rcases n with _ | n
  · haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  · have h1 := h n
    rw [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf, ← ZMod.natCast_eq_natCast_iff] at h1
    simpa using h1

end Padic

section Heights

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀)

/- English proof (translation)
Rewrite using `[← gb.sum_repr v, TensorProduct.sum_tmul, map_sum, map_sum, map_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul, map_smul, Module.Basis.constr_basis, map_smul, map_sum, Finset.smul_sum, hM l _ (fun k => gb.repr v l • Dp.ηmap (s.1 (M k l))) (fun k => by`. Simplify using `only [DualPair.ηmap, DualPair.ηk, LHom.comp, LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, AlgHom.comp_apply, mul_smul_comm])]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.lTensor_tmul, TensorProduct.tmul_smul]`.
-/
lemma tangent_eq {O R : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg) (f : OEnd B O)
    (M : Matrix (Fin g) (Fin g) (O : Type)) (s : LHom O R) (Dp : DualPair R)
    (hM : ∀ (l : Fin g) (i : Dp.π.ker) (m : Fin g → Dp.π.ker),
      (∀ k, (m k : (Dp.D : Type)) = (Dp.σ.comp s).1 (M k l) * i) →
      f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] i)) =
        B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] m k)) (v : B.gg) :
    f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap
        (gb.constr R₀ (fun l => ∑ k, gb k ⊗ₜ[R₀] s.1 (M k l)) v)) := by
  rw [← gb.sum_repr v, TensorProduct.sum_tmul, map_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.smul_tmul, map_smul, Module.Basis.constr_basis, map_smul, map_sum,
    Finset.smul_sum,
    hM l _ (fun k => gb.repr v l • Dp.ηmap (s.1 (M k l))) (fun k => by
      simp only [DualPair.ηmap, DualPair.ηk, LHom.comp, LinearMap.coe_mk, AddHom.coe_mk,
        SetLike.val_smul, AlgHom.comp_apply, mul_smul_comm])]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.lTensor_tmul, TensorProduct.tmul_smul]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `Tw.sep _ fun n => ?_` and prove the remaining obligations. Establish `hchar` using `Tw.char_R n`. Establish `hy : (p ^ (n + 1)) • B.map (Tw.q n) (τ j n) = 0` using `by rw [← map_nsmul, hτ, map_zero]`. Establish `H1` using `linHt B Tw.O A (Tw.R n) (Tw.q n) (Dp n) _ _ _ _ hy (hht j n) (tangent_eq B gb A.ab M (Tw.q n) (Dp n) (fun l i m h => hM _ _ _ l i m h))`.

Establish `H2` using `htLin B (pairingProperties B) Tw Dp κ τ ht (fun k n => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ)) (fun k => algebraMap ℤ_[p] (Tw.O : Type) (c k)) hτ hht (fun k n => by`. Use `map_eq_val (((Tw.q n).1 : (Tw.O : Type) →+* (Tw.R n : Type)).comp (algebraMap ℤ_[p] (Tw.O : Type))) (n + 1) (by exact_mod_cast Tw.char_R n) (c k)` as an intermediate fact. Rewrite using `[Int.cast_natCast]`. Conclude with `this) n`. Simplify using `only [natCast_zsmul] at H2`.

Rewrite `H2` using `[← hc n, ← A.a.nat]`. Establish `hya : (p ^ (n + 1)) • A.a.f (Tw.q n) (B.map (Tw.q n) (τ j n)) = 0`. Rewrite using `[← map_nsmul, hy, map_zero]`. Establish `H3` using `B.isHeight_unique (pairingProperties B) (Dp n) _ hchar _ hya _ _ H1 H2`. Establish `H4` using `LinearMap.congr_fun H3 (gb l)`.

Simplify using `only [LinearMap.comp_apply, Module.Basis.constr_basis, map_sum, hext_tmul, AlgHom.toLinearMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul] at H4`. Simplify using `only [map_sub, map_sum, map_mul]`. Rewrite using `[sub_eq_zero]`. Simplify using `only [mul_comm] at H4 ⊢`. Conclude with `H4.symm`.
-/
lemma height_eq (Tw : ATower R₀ p) [Algebra ℤ_[p] (Tw.O : Type)] (Dp : ∀ n, DualPair (Tw.R n))
    (gb : Module.Basis (Fin g) R₀ B.gg) (A : OAdj B Tw.O) (M : Matrix (Fin g) (Fin g) (Tw.O : Type))
    (hM : ∀ {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (M k l) * i) →
      A.ab.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))
    {κ : Type} [Fintype κ] (τ : κ → ℕ → B.G Tw.O) (hτ : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (ht : κ → B.gg →ₗ[R₀] (Tw.O : Type))
    (hht : ∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (j : κ) (c : κ → ℤ_[p])
    (hc : ∀ n, A.a.f (LHom.id Tw.O) (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n)
    (l : Fin g) :
    ∑ k, ht k (gb l) * algebraMap ℤ_[p] (Tw.O : Type) (c k) = ∑ k, M k l * ht j (gb k) := by
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => ?_
  have hchar := Tw.char_R n
  have hy : (p ^ (n + 1)) • B.map (Tw.q n) (τ j n) = 0 := by rw [← map_nsmul, hτ, map_zero]
  have H1 := linHt B Tw.O A (Tw.R n) (Tw.q n) (Dp n) _ _ _ _ hy (hht j n)
    (tangent_eq B gb A.ab M (Tw.q n) (Dp n) (fun l i m h => hM _ _ _ l i m h))
  have H2 := htLin B (pairingProperties B) Tw Dp κ τ ht
    (fun k n => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ))
    (fun k => algebraMap ℤ_[p] (Tw.O : Type) (c k)) hτ hht (fun k n => by
      have := map_eq_val (((Tw.q n).1 : (Tw.O : Type) →+* (Tw.R n : Type)).comp
        (algebraMap ℤ_[p] (Tw.O : Type))) (n + 1) (by exact_mod_cast Tw.char_R n) (c k)
      rw [Int.cast_natCast]
      exact this) n
  simp only [natCast_zsmul] at H2
  rw [← hc n, ← A.a.nat] at H2
  have hya : (p ^ (n + 1)) • A.a.f (Tw.q n) (B.map (Tw.q n) (τ j n)) = 0 := by
    rw [← map_nsmul, hy, map_zero]
  have H3 := B.isHeight_unique (pairingProperties B) (Dp n) _ hchar _ hya _ _ H1 H2
  have H4 := LinearMap.congr_fun H3 (gb l)
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis, map_sum, hext_tmul,
    AlgHom.toLinearMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul] at H4
  simp only [map_sub, map_sum, map_mul]
  rw [sub_eq_zero]
  simp only [mul_comm] at H4 ⊢
  exact H4.symm

end Heights

section Action

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {B : BX R₀} {O : LAlg R₀}
  {O₀ : Type} [CommRing O₀]

def pointAction (f : O₀ → OEnd B O)
    (hf : ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b,
      (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧ (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    O₀ →+* AddMonoid.End (B.G O) :=
  RingHom.mk'
    { toFun := fun a => (f a).f (LHom.id O)
      map_one' := AddMonoidHom.ext fun x => (hf _ x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => ((hf _ x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => ((hf _ x).2 a b).1

def padicExtension {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : O₀ →+* Matrix κ κ ℤ_[p]) :
    ℤ_[p] ⊗[ℤ] O₀ →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p] :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] _) ρ.toIntAlgHom
    fun x y => Algebra.commutes x (ρ y)

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ c a`.
-/
lemma padicExtension_tmul {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : O₀ →+* Matrix κ κ ℤ_[p])
    (c : ℤ_[p]) (a : O₀) : padicExtension ρ (c ⊗ₜ[ℤ] a) = c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a

end Action

end TateMatrices

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open TateMatrices in

/- English proof (translation)
Introduce `hTate hGram hAct R₀ _ p _ g B Tw _ _ Dt gb O₀ _ cj Ad dL hsurj hab hcj hAd hdL hker hprim hζ τ hτ hτp hbas hperf`. Take `⟨E, hEalt, hEdet, hE⟩` from `hGram B Tw hker hprim hζ τ hτ hτp hbas hperf`. Take `⟨A, ρL, hρL, hρLs, hAa⟩` from `hAct B Tw.O gb O₀ (fun a => (Ad a).a) p dL hsurj hAd hdL`. Take `⟨-, ρE, hρE⟩` from `hTate p (Ix g) (B.G Tw.O) τ hτ hτp hbas`. Take `⟨ht, bt, hht, hbt⟩` from `lim B (pairingProperties B) Tw Dt (Ix g) τ hτ hτp`.

Set `ρ₀ : O₀ →+* Matrix (Ix g) (Ix g) ℤ_[p]` to `ρE.comp (pointAction (fun a => (Ad a).a) hAd)`. Establish `hρ₀ : ∀ a j n, (Ad a).a.f (LHom.id Tw.O) (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ₀ a k j)).val • τ k n` using `fun a j n => hρE (pointAction (fun a => (Ad a).a) hAd a) j n`. Establish `hτ0 : ∀ j, p • τ j 0 = 0` using `fun j => by`. Establish `h` using `hτ j 0`. Rewrite `h` using `[zero_add, pow_one]`. Then use the resulting hypothesis.

Establish `hEspec : ∀ i j n, ∃ k : ℕ, (Tw.q n).1 (algebraMap ℤ_[p] (Tw.O : Type) (E i j)) = k ∧ B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)` using `fun i j n => ⟨_, map_eq_val (((Tw.q n).1 : (Tw.O : Type) →+* (Tw.R n : Type)).comp (algebraMap ℤ_[p] (Tw.O : Type))) (n + 1) (by exact_mod_cast Tw.toATower.char_R n) (E i j), hE i j n⟩`. Establish `hinv₀ : ∀ a, (ρ₀ a)ᵀ * E = E * ρ₀ (cj a)`. Introduce `a`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`.

Use `eq_of_zeta_pow Tw.ζ hprim _ _ _ _ fun n => ?_` and prove the remaining obligations. Establish `h1` using `pairing_sum_left B Finset.univ (p ^ (n + 1)) (fun k => τ k n) (τ j n) (Tw.ζ n) (fun k => (PadicInt.toZModPow (n + 1) (ρ₀ a k i)).val) _ (hτ j n) (fun k => hE k j n)`. Establish `h2` using `pairing_sum_right B Finset.univ (p ^ (n + 1)) (fun k => τ k n) (τ i n) (Tw.ζ n) (fun k => (PadicInt.toZModPow (n + 1) (ρ₀ (cj a) k j)).val) _ (hτ i n) (fun k => hE i k n)`. Rewrite `h1`, `h2` using `[← hρ₀]`. Establish `h3` using `(Ad a).pairing_of _ _ _ _ _ (hτ i n) h1`.

Rewrite `h3` using `[hab a]`. Conclude with `B.pairing_unique _ _ _ _ _ h3 h2`. Set `Ht : Matrix (Fin g) (Ix g) (Tw.O : Type)` to `Matrix.of fun k i => ht i (gb k)`. Set `Bt : Matrix (Fin g) (Ix g) (Tw.O : Type)` to `Matrix.of fun k i => (Module.Basis.baseChange (Tw.O : Type) gb).repr (TensorProduct.comm R₀ B.gg (Tw.O : Type) (bt i)) k`. Establish `hHt₀ : ∀ a, Ht * (ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type)) = (dL (cj a))ᵀ * Ht`.

Introduce `a`. Use extensionality with `l j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Ht, Matrix.of_apply]`. Use `height_eq B Tw.toATower Dt.Dp gb (Ad a) (dL (cj a)) ?_ τ hτ ht hht j _ (hρ₀ a j) l` and prove the remaining obligations. Introduce `R S s π hπ l i m h`.

Rewrite using `[hab a]`. Conclude with `hdL (cj a) s π hπ l i m h`. Set `H : HodgeTateData p g (Tw.O : Type) (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) Tw.c` to `{ ρ := padicExtension ρ₀ ρL := ρL P := 0 PL := 0 E := E E_alternating := hEalt isUnit_det_E := hEdet E_equivariant := fun a => by`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c a`. Rewrite using `[Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, padicExtension_tmul, padicExtension_tmul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hinv₀]`. Both sides reduce to the same expression. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, map_add, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, ha, hb]`.

Use `projectors := by simp`. Use `Ht := Ht`. Use `Bt := Bt`. Use `Ht_equivariant := ⟨fun a => by`. Proceed by induction on `a using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c a`. Rewrite using `[Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, padicExtension_tmul, hρL, Matrix.transpose_smul, Matrix.smul_mul]`. Establish `e : (c • ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type)) = algebraMap ℤ_[p] (Tw.O : Type) c • (ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type))`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mul_smul, hHt₀]`. Both sides reduce to the same expression. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, map_add, Matrix.transpose_add, Matrix.add_mul, Matrix.map_add _ (map_add _), Matrix.mul_add, ha, hb], by simp⟩`.

Use `form_eq_alt := by`. Use extensionality with `i j`. Establish `h4` using `bx_towerPairing B Tw.toATower Dt.Dp (Ix g) τ (fun i j => algebraMap ℤ_[p] (Tw.O : Type) (E i j)) ht bt hEspec hht hbt i j`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Ht, Bt, Matrix.of_apply]`. Rewrite using `[h4, ev_expand B gb, ev_expand B gb]`.

Simplify using `only [mul_comm] }`. Set `L : Link B Tw Dt H gb A` to `{ τ := τ τ_tors := hτ τ_compat := hτp τ_basis := by`. Rewrite using `[Function.bijective_iff_existsUnique]`. Introduce `x`. Simplify `hbas x.1 x.2` using `only [Subtype.ext_iff, eq_comm]`.

Use `ht := ht`. Use `bt := bt`. Use `ht_spec := hht`. Use `bt_spec := hbt`. Use `Ht_eq := fun _ _ => rfl`.

Use `Bt_eq := fun _ _ => rfl`. Use `E_spec := hEspec`. Use `ρ_spec := fun a j => by`. Express the relevant statement in the definitionally equal form `_ = ∑ k, (PadicInt.toZMod (padicExtension ρ₀ a k j)).val • τ k 0`. Proceed by induction on `a using TensorProduct.induction_on with`.

Consider the case `zero`. Establish `h` using `hAa 0 0 Tw.O (LHom.id Tw.O) ⟨τ j 0, (mem_torP B p _).2 (hτ0 j)⟩`. Rewrite `h` using `[TensorProduct.zero_tmul]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Consider the case `tmul c a`. Rewrite using `[hAa, padicExtension_tmul, hρ₀, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul, val_mul_smul _ _ _ (hτ0 k), toZMod_val_smul (ρ₀ a k j) _ (hτ0 k)]`. Consider the case `add a b ha hb`.

Rewrite using `[A.act_add, AddSubgroup.coe_add, ha, hb, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, Matrix.add_apply, map_add, val_add_smul _ _ _ (hτ0 k)]`. Use `ρL_spec := hρLs }`. Use `⟨A, H, L, rfl, rfl, rfl, fun a => ?_, fun a j n => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ρL _ = _`. Rewrite using `[hρL, map_one, one_smul]`. Express the relevant statement in the definitionally equal form `_ = ∑ k, (PadicInt.toZModPow (n + 1) (padicExtension ρ₀ (1 ⊗ₜ[ℤ] a) k j)).val • τ k n`. Rewrite using `[padicExtension_tmul, one_smul, hρ₀]`.
-/
theorem exists_tateMatrices_link :
  (∀ (p : ℕ) [Fact p.Prime] (κ Γ : Type) [Fintype κ] [DecidableEq κ] [AddCommGroup Γ] (τ : κ → ℕ → Γ),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) →
    (∀ n (x : Γ), (p ^ (n + 1)) • x = 0 → ∃! t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n) ∧
    ∃ ρ : AddMonoid.End Γ →+* Matrix κ κ ℤ_[p], ∀ (f : AddMonoid.End Γ) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)] (Dt : DualTower Tw) (gb : Module.Basis (Fin g) R₀ B.gg)
    (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B Tw.O) (dL : O₀ →+* Matrix (Fin g) (Fin g) (Tw.O : Type)),
    Function.Surjective (algebraMap R₀ (Tw.O : Type)) →
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg R₀} (s : LHom Tw.O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (Ad a).a.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ (A : OAct B Tw.O p (ℤ_[p] ⊗[ℤ] O₀))
      (H : HodgeTateData p g (Tw.O : Type) (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) Tw.c)
      (L : Link B Tw Dt H gb A), H.P = 0 ∧ H.PL = 0 ∧ L.τ = τ ∧ (∀ a, H.ρL (1 ⊗ₜ[ℤ] a) = dL a) ∧
      ∀ a j n, (Ad a).a.f (LHom.id Tw.O) (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • τ k n) := by
  intro hTate hGram hAct R₀ _ p _ g B Tw _ _ Dt gb O₀ _ cj Ad dL hsurj hab hcj hAd hdL hker hprim
    hζ τ hτ hτp hbas hperf
  classical
  obtain ⟨E, hEalt, hEdet, hE⟩ := hGram B Tw hker hprim hζ τ hτ hτp hbas hperf
  obtain ⟨A, ρL, hρL, hρLs, hAa⟩ := hAct B Tw.O gb O₀ (fun a => (Ad a).a) p dL hsurj hAd hdL
  obtain ⟨-, ρE, hρE⟩ := hTate p (Ix g) (B.G Tw.O) τ hτ hτp hbas
  obtain ⟨ht, bt, hht, hbt⟩ := lim B (pairingProperties B) Tw Dt (Ix g) τ hτ hτp
  let ρ₀ : O₀ →+* Matrix (Ix g) (Ix g) ℤ_[p] := ρE.comp (pointAction (fun a => (Ad a).a) hAd)
  have hρ₀ : ∀ a j n, (Ad a).a.f (LHom.id Tw.O) (τ j n) =
      ∑ k, (PadicInt.toZModPow (n + 1) (ρ₀ a k j)).val • τ k n := fun a j n =>
    hρE (pointAction (fun a => (Ad a).a) hAd a) j n
  have hτ0 : ∀ j, p • τ j 0 = 0 := fun j => by
    have h := hτ j 0
    rwa [zero_add, pow_one] at h
  have hEspec : ∀ i j n, ∃ k : ℕ, (Tw.q n).1 (algebraMap ℤ_[p] (Tw.O : Type) (E i j)) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := fun i j n =>
    ⟨_, map_eq_val (((Tw.q n).1 : (Tw.O : Type) →+* (Tw.R n : Type)).comp
        (algebraMap ℤ_[p] (Tw.O : Type))) (n + 1) (by exact_mod_cast Tw.toATower.char_R n) (E i j),
      hE i j n⟩
  have hinv₀ : ∀ a, (ρ₀ a)ᵀ * E = E * ρ₀ (cj a) := by
    intro a
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine eq_of_zeta_pow Tw.ζ hprim _ _ _ _ fun n => ?_
    have h1 := pairing_sum_left B Finset.univ (p ^ (n + 1)) (fun k => τ k n) (τ j n) (Tw.ζ n)
      (fun k => (PadicInt.toZModPow (n + 1) (ρ₀ a k i)).val) _ (hτ j n) (fun k => hE k j n)
    have h2 := pairing_sum_right B Finset.univ (p ^ (n + 1)) (fun k => τ k n) (τ i n) (Tw.ζ n)
      (fun k => (PadicInt.toZModPow (n + 1) (ρ₀ (cj a) k j)).val) _ (hτ i n) (fun k => hE i k n)
    rw [← hρ₀] at h1 h2
    have h3 := (Ad a).pairing_of _ _ _ _ _ (hτ i n) h1
    rw [hab a] at h3
    exact B.pairing_unique _ _ _ _ _ h3 h2
  let Ht : Matrix (Fin g) (Ix g) (Tw.O : Type) := Matrix.of fun k i => ht i (gb k)
  let Bt : Matrix (Fin g) (Ix g) (Tw.O : Type) := Matrix.of fun k i =>
    (Module.Basis.baseChange (Tw.O : Type) gb).repr
      (TensorProduct.comm R₀ B.gg (Tw.O : Type) (bt i)) k
  have hHt₀ : ∀ a, Ht * (ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type)) = (dL (cj a))ᵀ * Ht := by
    intro a
    ext l j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Ht, Matrix.of_apply]
    refine height_eq B Tw.toATower Dt.Dp gb (Ad a) (dL (cj a)) ?_ τ hτ ht hht j _ (hρ₀ a j) l
    intro R S s π hπ l i m h
    rw [hab a]
    exact hdL (cj a) s π hπ l i m h
  let H : HodgeTateData p g (Tw.O : Type) (ℤ_[p] ⊗[ℤ] O₀)
      (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) Tw.c :=
    { ρ := padicExtension ρ₀
      ρL := ρL
      P := 0
      PL := 0
      E := E
      E_alternating := hEalt
      isUnit_det_E := hEdet
      E_equivariant := fun a => by
        induction a using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
            padicExtension_tmul, padicExtension_tmul, Matrix.transpose_smul, Matrix.smul_mul,
            Matrix.mul_smul, hinv₀]
          rfl
        | add a b ha hb =>
          rw [map_add, map_add, map_add, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, ha, hb]
      projectors := by simp
      Ht := Ht
      Bt := Bt
      Ht_equivariant := ⟨fun a => by
        induction a using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
            padicExtension_tmul, hρL, Matrix.transpose_smul, Matrix.smul_mul]
          have e : (c • ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type)) =
              algebraMap ℤ_[p] (Tw.O : Type) c • (ρ₀ a).map (algebraMap ℤ_[p] (Tw.O : Type)) := by
            ext i j; simp
          rw [e, Matrix.mul_smul, hHt₀]
          rfl
        | add a b ha hb =>
          rw [map_add, map_add, map_add, Matrix.transpose_add, Matrix.add_mul,
            Matrix.map_add _ (map_add _), Matrix.mul_add, ha, hb], by simp⟩
      form_eq_alt := by
        ext i j
        have h4 := bx_towerPairing B Tw.toATower Dt.Dp (Ix g) τ
          (fun i j => algebraMap ℤ_[p] (Tw.O : Type) (E i j)) ht bt hEspec hht hbt i j
        simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, Ht, Bt, Matrix.of_apply]
        rw [h4, ev_expand B gb, ev_expand B gb]
        simp only [mul_comm] }
  let L : Link B Tw Dt H gb A :=
    { τ := τ
      τ_tors := hτ
      τ_compat := hτp
      τ_basis := by
        rw [Function.bijective_iff_existsUnique]
        intro x
        simpa only [Subtype.ext_iff, eq_comm] using hbas x.1 x.2
      ht := ht
      bt := bt
      ht_spec := hht
      bt_spec := hbt
      Ht_eq := fun _ _ => rfl
      Bt_eq := fun _ _ => rfl
      E_spec := hEspec
      ρ_spec := fun a j => by
        change _ = ∑ k, (PadicInt.toZMod (padicExtension ρ₀ a k j)).val • τ k 0
        induction a using TensorProduct.induction_on with
        | zero =>
          have h := hAa 0 0 Tw.O (LHom.id Tw.O) ⟨τ j 0, (mem_torP B p _).2 (hτ0 j)⟩
          rw [TensorProduct.zero_tmul] at h
          rw [h]
          simp
        | tmul c a =>
          rw [hAa, padicExtension_tmul, hρ₀, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_apply, smul_eq_mul, map_mul, val_mul_smul _ _ _ (hτ0 k),
            toZMod_val_smul (ρ₀ a k j) _ (hτ0 k)]
        | add a b ha hb =>
          rw [A.act_add, AddSubgroup.coe_add, ha, hb, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_add, Matrix.add_apply, map_add, val_add_smul _ _ _ (hτ0 k)]
      ρL_spec := hρLs }
  refine ⟨A, H, L, rfl, rfl, rfl, fun a => ?_, fun a j n => ?_⟩
  · change ρL _ = _
    rw [hρL, map_one, one_smul]
  · change _ = ∑ k, (PadicInt.toZModPow (n + 1) (padicExtension ρ₀ (1 ⊗ₜ[ℤ] a) k j)).val • τ k n
    rw [padicExtension_tmul, one_smul, hρ₀]

end GlobalTheory
