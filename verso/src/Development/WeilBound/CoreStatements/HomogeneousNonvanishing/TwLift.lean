import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Use `TensorProduct.induction_on (motive := fun w : ℤ_[p] ⊗[ℤ] M => ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w') w ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨0, 0, by simp⟩`. Introduce `a m`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)`. Establish `ha : a = ((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c`.

Rewrite using `[smul_eq_mul, ← hc, zsmul_eq_mul, mul_one, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((PadicInt.appr a k : ℕ) : ℤ) • m, c ⊗ₜ[ℤ] m, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[TensorProduct.add_tmul, TensorProduct.smul_tmul ((PadicInt.appr a k : ℕ) : ℤ) (1 : ℤ_[p]) m, ← TensorProduct.smul_tmul' ((p : ℤ_[p]) ^ k) c m]`.

Introduce and unpack `w1 w2 ⟨y1, w1', rfl⟩ ⟨y2, w2', rfl⟩`. Conclude with `⟨y1 + y2, w1' + w2', by rw [TensorProduct.tmul_add, smul_add]; abel⟩`.
-/
theorem lift_dense (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (k : ℕ) (w : ℤ_[p] ⊗[ℤ] M) :
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w' := by
  refine TensorProduct.induction_on (motive := fun w : ℤ_[p] ⊗[ℤ] M =>
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w') w ?_ ?_ ?_
  · exact ⟨0, 0, by simp⟩
  · intro a m
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c := by
      rw [smul_eq_mul, ← hc, zsmul_eq_mul, mul_one, Int.cast_natCast]
      ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • m, c ⊗ₜ[ℤ] m, ?_⟩
    calc a ⊗ₜ[ℤ] m = (((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c) ⊗ₜ[ℤ] m :=
          congrArg (· ⊗ₜ[ℤ] m) ha
      _ = 1 ⊗ₜ[ℤ] (((PadicInt.appr a k : ℕ) : ℤ) • m) + (p : ℤ_[p]) ^ k • c ⊗ₜ[ℤ] m := by
          rw [TensorProduct.add_tmul, TensorProduct.smul_tmul ((PadicInt.appr a k : ℕ) : ℤ) (1 : ℤ_[p]) m,
            ← TensorProduct.smul_tmul' ((p : ℤ_[p]) ^ k) c m]
  · rintro w1 w2 ⟨y1, w1', rfl⟩ ⟨y2, w2', rfl⟩
    exact ⟨y1 + y2, w1' + w2', by rw [TensorProduct.tmul_add, smul_add]; abel⟩

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ M`. Establish `hdiv : ∀ i, (p : ℤ) ^ k ∣ b.repr y i`. Introduce `i`. Establish `h1` using `congrArg (fun z => (b.baseChange ℤ_[p]).repr z i) h`. Rewrite using `[← PadicInt.pow_p_dvd_int_iff]`.

Use `Dvd.intro ((b.baseChange ℤ_[p]).repr w i) ?_` and prove the remaining obligations. Simplify `h1.symm` using `[Module.Basis.baseChange_repr_tmul]`. Use `choose c hc using hdiv`. Use `⟨∑ i, c i • b i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr y]`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hc i, mul_smul, ← Nat.cast_pow, natCast_zsmul]`.
-/
theorem lift_sat (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] (k : ℕ)
    (y : M) (w : ℤ_[p] ⊗[ℤ] M) (h : 1 ⊗ₜ y = (p : ℤ_[p]) ^ k • w) : ∃ e, y = p ^ k • e := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hdiv : ∀ i, (p : ℤ) ^ k ∣ b.repr y i := by
    intro i
    have h1 := congrArg (fun z => (b.baseChange ℤ_[p]).repr z i) h
    rw [← PadicInt.pow_p_dvd_int_iff]
    refine Dvd.intro ((b.baseChange ℤ_[p]).repr w i) ?_
    simpa [Module.Basis.baseChange_repr_tmul] using h1.symm
  choose c hc using hdiv
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, ← Nat.cast_pow, natCast_zsmul]

/- English proof (translation)
Introduce `p _ O _ L L' _ _ _ _ B B' _ _ _ _ _ φ hO hB`. Establish `htm : ∀ (n : ℕ) (y : L'), (1 : ℤ_[p]) ⊗ₜ[ℤ] (n • y) = (n : ℤ_[p]) • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y)`. Introduce `n y`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `map_nsmul (TensorProduct.mk ℤ ℤ_[p] L' 1) n y`.

Establish `hls : ∀ (c : O) (y : L'), LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) = (1 : ℤ_[p]) ⊗ₜ[ℤ] (c • y)`. Introduce `c y`. Rewrite using `[LinearMap.baseChange_tmul]`. Both sides reduce to the same expression. Take `⟨G, hG⟩ : ∃ G : ℕ → Submodule O (L' × L), ∀ k z, z ∈ G k ↔ ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w` from `⟨fun k => { carrier := {z | ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w} add_mem' := by`.

Introduce and unpack `z1 z2 ⟨w1, hw1⟩ ⟨w2, hw2⟩`. Use `show ∃ w : ℤ_[p] ⊗[ℤ] L', _`. Use `⟨w1 + w2, ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, hw1, hw2, smul_add]`. Normalize the expressions using the abelian group laws.

Use the proof step `zero_mem' := by show ∃ w : ℤ_[p] ⊗[ℤ] L', _`. Conclude with `⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c z ⟨w, hw⟩`. Use `show ∃ w : ℤ_[p] ⊗[ℤ] L', _`.

Use `⟨LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap w, ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.smul_fst, Prod.smul_snd, hO c z.2, ← hls c z.1, hw, map_add, map_smul] },`. Use `fun k z => Iff.rfl⟩`. Establish `hsurj : ∀ k, Function.Surjective ((LinearMap.snd O L' L).comp (G k).subtype)`. Introduce `k x`.

Take `⟨y, w, hw⟩` from `PositivityTheory.UnitarySelfGeneration.lift_dense p L' k (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x))`. Use `⟨⟨(y, x), (hG k (y, x)).mpr ⟨-w, ?_⟩⟩, rfl⟩` and prove the remaining obligations. Use `show (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • -w`. Rewrite using `[hw, smul_neg]`. Normalize the expressions using the abelian group laws.

Use `choose h hh using fun k => Module.projective_lifting_property ((LinearMap.snd O L' L).comp (G k).subtype) LinearMap.id (hsurj k)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ℕ → L →ₗ[O] L', ∀ k x, ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] a k x = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • w := by`. Use `⟨fun k => (LinearMap.fst O L' L).comp ((G k).subtype.comp (h k)), fun k x => ?_⟩` and prove the remaining obligations. Establish `h2 : (h k x : L' × L).2 = x` using `LinearMap.congr_fun (hh k) x`. Establish `hmem` using `(hG k _).mp (h k x).prop`.

Rewrite `hmem` using `[h2]`. Conclude with `hmem`. Use `⟨⟨a, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `k x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy⟩`. Take `⟨w, hw⟩` from `ha k x`. Rewrite `hw` using `[hy, htm, Nat.cast_pow]`. Establish `h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = (p : ℤ_[p]) ^ k • φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y - w)`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, smul_sub, hw]`. Normalize the expressions using the abelian group laws. Conclude with `PositivityTheory.UnitarySelfGeneration.lift_sat p L k x _ h1`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨a k y, map_nsmul (a k) (p ^ k) y⟩`.

Introduce `k y`. Take `⟨x, v, hv⟩` from `PositivityTheory.UnitarySelfGeneration.lift_dense p L k (φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y))`. Take `⟨w, hw⟩` from `ha k x`. Establish `h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • φ v`. Rewrite using `[← map_smul, ← map_add, ← hv, LinearEquiv.apply_symm_apply]`.

Establish `h2 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (y - a k x) = (p : ℤ_[p]) ^ k • (φ v - w)`. Rewrite using `[TensorProduct.tmul_sub, h1, hw, smul_sub]`. Normalize the expressions using the abelian group laws. Take `⟨e, he⟩` from `PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h2`. Conclude with `⟨x, e, by rw [← he]; abel⟩`.

Introduce `k x y`. Take `⟨w1, hw1⟩` from `ha k x`. Take `⟨w2, hw2⟩` from `ha k y`. Rewrite using `[← PadicInt.pow_p_dvd_int_iff, Int.cast_sub]`. Establish `e1 : ((B' (a k x) (a k y) : ℤ) : ℤ_[p]) = B'.baseChange ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k x) ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k y)`.

Rewrite using `[LinearMap.BilinForm.baseChange_tmul]`. Simplify using the standard rewrite rules. Establish `e2 : ((B x y : ℤ) : ℤ_[p]) = B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y))`. Rewrite using `[hB, LinearMap.BilinForm.baseChange_tmul]`. Simplify using the standard rewrite rules.

Rewrite using `[e1, e2, hw1, hw2]`. Use `Dvd.intro (B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) w2 + B'.baseChange ℤ_[p] w1 (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) + (p : ℤ_[p]) ^ k • w2)) ?_` and prove the remaining obligations. Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `k x`.

Take `⟨w1, hw1⟩` from `ha (k + 1) x`. Take `⟨w2, hw2⟩` from `ha k x`. Establish `h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (a (k + 1) x - a k x) = (p : ℤ_[p]) ^ k • ((p : ℤ_[p]) • w1 - w2)`. Rewrite using `[TensorProduct.tmul_sub, hw1, hw2, smul_sub, smul_smul, ← pow_succ]`. Normalize the expressions using the abelian group laws.

Take `⟨e, he⟩` from `PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h1`. Conclude with `⟨e, by rw [← he]; abel⟩`.
-/
theorem tw_lift : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  intro p _ O _ L L' _ _ _ _ B B' _ _ _ _ _ φ hO hB
  have htm : ∀ (n : ℕ) (y : L'),
      (1 : ℤ_[p]) ⊗ₜ[ℤ] (n • y) = (n : ℤ_[p]) • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
    intro n y
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul (TensorProduct.mk ℤ ℤ_[p] L' 1) n y
  have hls : ∀ (c : O) (y : L'),
      LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap
        ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) = (1 : ℤ_[p]) ⊗ₜ[ℤ] (c • y) := by
    intro c y
    rw [LinearMap.baseChange_tmul]
    rfl
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule O (L' × L), ∀ k z, z ∈ G k ↔
      ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w :=
    ⟨fun k =>
      { carrier := {z | ∃ w : ℤ_[p] ⊗[ℤ] L',
          (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w}
        add_mem' := by
          rintro z1 z2 ⟨w1, hw1⟩ ⟨w2, hw2⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨w1 + w2, ?_⟩
          rw [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add,
            hw1, hw2, smul_add]
          abel
        zero_mem' := by
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          exact ⟨0, by simp⟩
        smul_mem' := by
          rintro c z ⟨w, hw⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap w,
            ?_⟩
          rw [Prod.smul_fst, Prod.smul_snd, hO c z.2, ← hls c z.1, hw, map_add, map_smul] },
      fun k z => Iff.rfl⟩
  have hsurj : ∀ k, Function.Surjective ((LinearMap.snd O L' L).comp (G k).subtype) := by
    intro k x
    obtain ⟨y, w, hw⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L' k (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x))
    refine ⟨⟨(y, x), (hG k (y, x)).mpr ⟨-w, ?_⟩⟩, rfl⟩
    show (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • -w
    rw [hw, smul_neg]
    abel
  choose h hh using fun k => Module.projective_lifting_property
    ((LinearMap.snd O L' L).comp (G k).subtype) LinearMap.id (hsurj k)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → L →ₗ[O] L', ∀ k x, ∃ w : ℤ_[p] ⊗[ℤ] L',
      (1 : ℤ_[p]) ⊗ₜ[ℤ] a k x = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • w := by
    refine ⟨fun k => (LinearMap.fst O L' L).comp ((G k).subtype.comp (h k)), fun k x => ?_⟩
    have h2 : (h k x : L' × L).2 = x := LinearMap.congr_fun (hh k) x
    have hmem := (hG k _).mp (h k x).prop
    rw [h2] at hmem
    exact hmem
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro k x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, hw⟩ := ha k x
      rw [hy, htm, Nat.cast_pow] at hw
      have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = (p : ℤ_[p]) ^ k • φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y - w) := by
        apply φ.injective
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_sub, hw]
        abel
      exact PositivityTheory.UnitarySelfGeneration.lift_sat p L k x _ h1
    · rintro ⟨y, rfl⟩
      exact ⟨a k y, map_nsmul (a k) (p ^ k) y⟩
  · intro k y
    obtain ⟨x, v, hv⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L k (φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y))
    obtain ⟨w, hw⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • φ v := by
      rw [← map_smul, ← map_add, ← hv, LinearEquiv.apply_symm_apply]
    have h2 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (y - a k x) = (p : ℤ_[p]) ^ k • (φ v - w) := by
      rw [TensorProduct.tmul_sub, h1, hw, smul_sub]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h2
    exact ⟨x, e, by rw [← he]; abel⟩
  · intro k x y
    obtain ⟨w1, hw1⟩ := ha k x
    obtain ⟨w2, hw2⟩ := ha k y
    rw [← PadicInt.pow_p_dvd_int_iff, Int.cast_sub]
    have e1 : ((B' (a k x) (a k y) : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k x) ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k y) := by
      rw [LinearMap.BilinForm.baseChange_tmul]
      simp
    have e2 : ((B x y : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y)) := by
      rw [hB, LinearMap.BilinForm.baseChange_tmul]
      simp
    rw [e1, e2, hw1, hw2]
    refine Dvd.intro (B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) w2 +
      B'.baseChange ℤ_[p] w1 (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) + (p : ℤ_[p]) ^ k • w2)) ?_
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro k x
    obtain ⟨w1, hw1⟩ := ha (k + 1) x
    obtain ⟨w2, hw2⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (a (k + 1) x - a k x) =
        (p : ℤ_[p]) ^ k • ((p : ℤ_[p]) • w1 - w2) := by
      rw [TensorProduct.tmul_sub, hw1, hw2, smul_sub, smul_smul, ← pow_succ]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h1
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
