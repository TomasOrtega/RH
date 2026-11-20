import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply, Fintype.sum_prod_type]`.
-/
theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [res, Matrix.of_apply, Matrix.one_apply]`. Distinguish the cases in `h : p.1 = q.1`. Rewrite using `[if_pos h, map_one, Matrix.one_apply]`. Distinguish the cases in `h' : p.2 = q.2`.

Rewrite using `[if_pos h', if_pos (Prod.ext h h')]`. Rewrite using `[if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]`. Rewrite using `[if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]`.
-/
theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

/- English proof (translation)
Establish `hsum : x = ∑ i, b.repr 1 i • (x * b i)` using `by conv_lhs => rw [← mul_one x, ← b.sum_repr 1]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _`. Establish `hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i` using `by conv_lhs => rw [hsum]`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]`.

Rewrite using `[hk]`. Conclude with `Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)`.
-/
theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

/- English proof (translation)
Establish `hadj : N = N.det • M.adjugate`. Establish `h1 : N * M * M.adjugate = M.adjugate` using `by rw [hNM, Matrix.one_mul]`. Rewrite `h1` using `[Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Establish `hd1 : N.det * M.det = 1` using `by rw [← Matrix.det_mul, hNM, Matrix.det_one]`. Rewrite using `[← h1, smul_smul, hd1, one_smul]`.

Set `M' : Matrix ι ι R₀` to `Matrix.of fun p q => ⟨M p q, hM p q⟩`. Establish `hM' : R₀.subtype.mapMatrix M' = M` using `by ext; rfl`. Establish `hA : M.adjugate p q = R₀.subtype (M'.adjugate p q)`. Rewrite using `[← hM', ← RingHom.map_adjugate]`. Both sides reduce to the same expression.

Rewrite using `[hadj, Matrix.smul_apply, smul_eq_mul, hA]`. Conclude with `Subring.mul_mem _ hd (M'.adjugate p q).2`.
-/
theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

/- English proof (translation)
Establish `hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c)` using `fun c => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R)) ((algebraMap F A).comp (algebraMap ℚ F))) c`. Establish `hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i` using `by conv_lhs => rw [← ω.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]`.

Rewrite using `[hx, Module.Basis.repr_sum_self]`.
-/
theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul]`. Conclude with `repr_map ω b hb _ _`.
-/
theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

/- English proof (translation)
Use `⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_, fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩` and prove the remaining obligations. Establish `hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀` using `fun p q => by`. Simplify `he (Sum.inl p) (Sum.inl q)` using `[emb]`. Establish `hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀`. Simplify `he (Sum.inr ()) (Sum.inr ())` using `[emb]`.

Establish `hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1`. Rewrite using `[← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']`. Establish `hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀` using `fun p q => inv_mem R₀ _ _ hinv hres hdet p q`. Conclude with `⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k, repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩`. Establish `hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) : Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A)` using `rfl`.

Establish `hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) : Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A)`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Unfold `emb`. Rewrite using `[hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]`.

Apply the tactic sequence `ext (x | x) (y | y) <;> simp [RingHom.map_det]`.
-/
theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
