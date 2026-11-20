import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SupportFreeOfBlockSubstInvariant

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Establish `key : ∀ (y : TVar D N → K) (R : KTp K D N), MvPolynomial.eval y R = MvPolynomial.eval y ((MvPolynomial.aeval (fun v : TVar D N => if v.1 = 0 then MvPolynomial.C (y (0, v.2)) else MvPolynomial.X v) : KTp K D N →ₐ[K] KTp K D N) R)`. Introduce `y R`. Proceed by induction on `R using MvPolynomial.induction_on`. Simplify using the standard rewrite rules. Name the introduced variables `p q hp hq`.

Simplify using `only [map_add, hp, hq]`. Name the introduced variables `p v hp`. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Rewrite using `[hp]`. Use `congr 1`.

Take `⟨b, j⟩` from `v`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hb]`.

Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[key y P, key y Q]`. Conclude with `congrArg _ (hPQ fun j => y (0, j))`.
-/
private theorem eq_of_aeval_block_zero_eq {D N : ℕ} (P Q : KTp K D N)
    (hPQ : ∀ x : Fin (N + 1) → K,
      (MvPolynomial.aeval (fun v : TVar D N => if v.1 = 0 then MvPolynomial.C (x v.2)
        else MvPolynomial.X v) : KTp K D N →ₐ[K] KTp K D N) P =
      (MvPolynomial.aeval (fun v : TVar D N => if v.1 = 0 then MvPolynomial.C (x v.2)
        else MvPolynomial.X v) : KTp K D N →ₐ[K] KTp K D N) Q) :
    P = Q := by
  have key : ∀ (y : TVar D N → K) (R : KTp K D N), MvPolynomial.eval y R =
      MvPolynomial.eval y ((MvPolynomial.aeval (fun v : TVar D N =>
        if v.1 = 0 then MvPolynomial.C (y (0, v.2)) else MvPolynomial.X v) :
          KTp K D N →ₐ[K] KTp K D N) R) := by
    intro y R
    induction R using MvPolynomial.induction_on
    · simp
    · rename_i p q hp hq
      simp only [map_add, hp, hq]
    · rename_i p v hp
      simp only [map_mul, MvPolynomial.aeval_X]
      rw [hp]
      congr 1
      obtain ⟨b, j⟩ := v
      by_cases hb : b = 0
      · subst hb
        simp
      · simp [hb]
  apply MvPolynomial.funext
  intro y
  rw [key y P, key y Q]
  exact congrArg _ (hPQ fun j => y (0, j))

/- English proof (translation)
Use `choose T hTX hTz using ht`. Take `⟨S, hS⟩ : ∃ S : (Fin (N + 1) → K) → (KTp K D N →ₐ[K] KTp K D N), ∀ x, S x = MvPolynomial.aeval (fun v : TVar D N => if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v)` from `⟨_, fun _ => rfl⟩`. Establish `F1h : ∀ x t, (S x).comp (T t) = S (x + t)`. Introduce `x t`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `v`. Distinguish the cases in `hv : v.1 = 0`. Simplify using `[hS, hTX, hv]`. Simplify using `[hS, hTX, hv]`. Establish `F2h : ∀ x y, (S x).comp (S y) = S y`.

Introduce `x y`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Distinguish the cases in `hv : v.1 = 0`. Simplify using `[hS, hv]`.

Simplify using `[hS, hv]`. Establish `F1 : ∀ x t p, S x (T t p) = S (x + t) p` using `fun x t p => AlgHom.congr_fun (F1h x t) p`. Establish `F2 : ∀ x y p, S x (S y p) = S y p` using `fun x y p => AlgHom.congr_fun (F2h x y) p`. Establish `cross : ∀ (t : Fin (N + 1) → K) (p q : KTp K D N), algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q → T t p * q = p * T t q`. Introduce `t p q hpq`.

Apply `IsFractionRing.injective (KTp K D N) (KTf K D N)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hTz t p q hpq, hpq]`. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨p0, q0, hq0, hpq0⟩ : ∃ p q : KTp K D N, q ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q := by`. Take `⟨p, q, hq, hz⟩` from `IsFractionRing.div_surjective (A := KTp K D N) z`.

Establish `hq' : algebraMap (KTp K D N) (KTf K D N) q ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr (nonZeroDivisors.ne_zero hq)`. Use `⟨p, q, nonZeroDivisors.ne_zero hq, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz]`. Use `first`. Consider the case `exact (div_mul_cancel₀ _ hq').symm`.

Consider the case `field_simp`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : Fin (N + 1) → K, S a q0 ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hq0 (eq_of_aeval_block_zero_eq q0 0 fun x => by rw [← hS x, hall x, map_zero])`.

Establish `hid : S a p0 * q0 = p0 * S a q0`. Apply `eq_of_aeval_block_zero_eq` to reduce the goal to its premises. Introduce `b`. Rewrite using `[← hS b, map_mul, map_mul, F2, F2]`. Establish `hc` using `congrArg (S a) (cross (b - a) p0 q0 hpq0)`.

Rewrite `hc` using `[map_mul, map_mul, F1, F1, show a + (b - a) = b by abel]`. Conclude with `hc.symm`. Establish `hq0' : algebraMap (KTp K D N) (KTf K D N) q0 ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr hq0`. Use `⟨S a p0, S a q0, ha, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ hq0'` to reduce the goal to its premises.

Rewrite using `[← map_mul, hid, map_mul, hpq0]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `support_free_of_block_subst_invariant _ fun x => by rw [← hS x, F2]`. Conclude with `support_free_of_block_subst_invariant _ fun x => by rw [← hS x, F2]`.
-/
private theorem exists_fraction_free_of_block_zero {D N : ℕ} (z : KTf K D N)
    (ht : ∀ t : Fin (N + 1) → K, ∃ T : KTp K D N →ₐ[K] KTp K D N,
      (∀ v, T (MvPolynomial.X v) =
        if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (t v.2) else MvPolynomial.X v) ∧
      ∀ p q : KTp K D N,
        algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q →
        algebraMap (KTp K D N) (KTf K D N) (T p) = z * algebraMap (KTp K D N) (KTf K D N) (T q)) :
    ∃ p q : KTp K D N, q ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q ∧
      (∀ s ∈ p.support, degB 0 s = 0) ∧ (∀ s ∈ q.support, degB 0 s = 0) := by
  choose T hTX hTz using ht
  obtain ⟨S, hS⟩ : ∃ S : (Fin (N + 1) → K) → (KTp K D N →ₐ[K] KTp K D N), ∀ x, S x =
      MvPolynomial.aeval (fun v : TVar D N => if v.1 = 0 then MvPolynomial.C (x v.2)
        else MvPolynomial.X v) := ⟨_, fun _ => rfl⟩
  have F1h : ∀ x t, (S x).comp (T t) = S (x + t) := by
    intro x t
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = 0
    · simp [hS, hTX, hv]
    · simp [hS, hTX, hv]
  have F2h : ∀ x y, (S x).comp (S y) = S y := by
    intro x y
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = 0
    · simp [hS, hv]
    · simp [hS, hv]
  have F1 : ∀ x t p, S x (T t p) = S (x + t) p := fun x t p => AlgHom.congr_fun (F1h x t) p
  have F2 : ∀ x y p, S x (S y p) = S y p := fun x y p => AlgHom.congr_fun (F2h x y) p
  have cross : ∀ (t : Fin (N + 1) → K) (p q : KTp K D N),
      algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q →
      T t p * q = p * T t q := by
    intro t p q hpq
    apply IsFractionRing.injective (KTp K D N) (KTf K D N)
    rw [map_mul, map_mul, hTz t p q hpq, hpq]
    ring
  obtain ⟨p0, q0, hq0, hpq0⟩ : ∃ p q : KTp K D N, q ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q := by
    obtain ⟨p, q, hq, hz⟩ := IsFractionRing.div_surjective (A := KTp K D N) z
    have hq' : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
        (nonZeroDivisors.ne_zero hq)
    refine ⟨p, q, nonZeroDivisors.ne_zero hq, ?_⟩
    rw [← hz]
    first
    | exact (div_mul_cancel₀ _ hq').symm
    | field_simp
  obtain ⟨a, ha⟩ : ∃ a : Fin (N + 1) → K, S a q0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hq0 (eq_of_aeval_block_zero_eq q0 0 fun x => by rw [← hS x, hall x, map_zero])
  have hid : S a p0 * q0 = p0 * S a q0 := by
    apply eq_of_aeval_block_zero_eq
    intro b
    rw [← hS b, map_mul, map_mul, F2, F2]
    have hc := congrArg (S a) (cross (b - a) p0 q0 hpq0)
    rw [map_mul, map_mul, F1, F1, show a + (b - a) = b by abel] at hc
    exact hc.symm
  have hq0' : algebraMap (KTp K D N) (KTf K D N) q0 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr hq0
  refine ⟨S a p0, S a q0, ha, ?_, ?_, ?_⟩
  · apply mul_right_cancel₀ hq0'
    rw [← map_mul, hid, map_mul, hpq0]
    ring
  · exact support_free_of_block_subst_invariant _ fun x => by rw [← hS x, F2]
  · exact support_free_of_block_subst_invariant _ fun x => by rw [← hS x, F2]

/- English proof (translation)
Take `⟨e, he⟩ : ∃ e : KTf K d.D d.N ≃+* KTf K d.D d.N, e = IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv` from `⟨_, rfl⟩`. Rewrite using `[← he]`. Unfold `De`. Rewrite using `[show ∀ M : Matrix (Fin d.del) (Fin d.del) (KTf K d.D d.N), e M.det = (e : KTf K d.D d.N →+* KTf K d.D d.N) M.det from fun _ => rfl, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `k l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, RingEquiv.coe_toRingHom]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Take `⟨τ, hτ⟩ : ∃ τ : OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N, τ = IsFractionRing.ringEquivOfRingEquiv (β c).toRingEquiv` from `⟨_, rfl⟩`. Establish `hτΩ : ∀ ω : Ω c, τ (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ω) = algebraMap (Ω c) (OmS (Ω c) d.D d.N) ω`.

Introduce `ω`. Rewrite using `[hτ, IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N), IsFractionRing.ringEquivOfRingEquiv_algebraMap]`. Conclude with `congrArg _ ((β c).commutes ω)`. Establish `hK : ∀ a : K, τ (algebraMap K (OmS (Ω c) d.D d.N) a) = algebraMap K _ a`. Introduce `a`.

Rewrite using `[IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N), hτΩ]`. Establish `hsX : ∀ v, d.sH c (MvPolynomial.X v) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (Fin.succAboveCases (α` using `fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) (if v.1 = 0 then MvPolynomial.X (Sum.inl ()) else -∑ k, MvPolynomial.X (Sum.inr (v.1, k)) * MvPolynomial.C (d.x c k)) (fun k => MvPolynomial.X (Sum.inr (v.1, k))) v.2) := fun v => MvPolynomial.aeval_X _ v`. Establish `hXc : ∀ v, d.sH c (eα (MvPolynomial.X v)) = τ (d.sH c (MvPolynomial.X v))`. Introduce `v`. Rewrite using `[hX c v, hsX v, hτ, IsFractionRing.ringEquivOfRingEquiv_algebraMap]`.

Apply the tactic sequence `try rfl`. Establish `hP : ∀ p : KTp K d.D d.N, d.sH c (eα p) = τ (d.sH c p)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on`. Name the introduced variables `a`.

Rewrite using `[← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes, hK]`. Name the introduced variables `p q hp hq`. Simplify using `only [map_add, hp, hq]`. Name the introduced variables `p v hp`. Simplify using `only [map_mul, hp, hXc v]`.

Establish `hL : ∀ q : KTp K d.D d.N, d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) = d.sH c q` using `fun q => IsFractionRing.lift_algebraMap _ _`. Establish `hR : (d.KTtoS h c).comp (e : KTf K d.D d.N →+* KTf K d.D d.N) = (τ : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp (d.KTtoS h c)`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (KTp K d.D d.N))` to reduce the goal to its premises. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, RingEquiv.coe_toRingHom]`.

Rewrite using `[he, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hL, hL]`. Conclude with `hP p`. Establish `hy : τ (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c) = d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c`. Simplify using `only [bvecG, map_mul, hτΩ]`. Use `letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra`.

Establish `key` using `Algebra.trace_eq_of_equiv_equiv e τ hR (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c)`. Rewrite `key` using `[hy]`. Conclude with `(congrArg e key).trans (e.apply_symm_apply _)`.
-/
private theorem sH_comp_eq_of_X_eq (hd : d.AxH 𝒜) (h : d.S1)
    (eα : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N)
    (β : ∀ c, MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c] MvPolynomial (SVar d.D d.N) (Ω c))
    (hX : ∀ c v, d.sH c (eα (MvPolynomial.X v)) =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
        (β c (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
          (if v.1 = 0 then MvPolynomial.X (Sum.inl ())
            else -∑ k, MvPolynomial.X (Sum.inr (v.1, k)) * MvPolynomial.C (d.x c k))
          (fun k => MvPolynomial.X (Sum.inr (v.1, k))) v.2))) :
    (IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv : KTf K d.D d.N ≃+* KTf K d.D d.N)
      (d.De hd h) = d.De hd h := by
  obtain ⟨e, he⟩ : ∃ e : KTf K d.D d.N ≃+* KTf K d.D d.N,
      e = IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv := ⟨_, rfl⟩
  rw [← he]
  unfold De
  rw [show ∀ M : Matrix (Fin d.del) (Fin d.del) (KTf K d.D d.N),
    e M.det = (e : KTf K d.D d.N →+* KTf K d.D d.N) M.det from fun _ => rfl, RingHom.map_det]
  congr 1
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum,
    RingEquiv.coe_toRingHom]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨τ, hτ⟩ : ∃ τ : OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N,
      τ = IsFractionRing.ringEquivOfRingEquiv (β c).toRingEquiv := ⟨_, rfl⟩
  have hτΩ : ∀ ω : Ω c, τ (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ω) =
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) ω := by
    intro ω
    rw [hτ, IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg _ ((β c).commutes ω)
  have hK : ∀ a : K, τ (algebraMap K (OmS (Ω c) d.D d.N) a) = algebraMap K _ a := by
    intro a
    rw [IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N), hτΩ]
  have hsX : ∀ v, d.sH c (MvPolynomial.X v) =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
        (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
          (if v.1 = 0 then MvPolynomial.X (Sum.inl ())
            else -∑ k, MvPolynomial.X (Sum.inr (v.1, k)) * MvPolynomial.C (d.x c k))
          (fun k => MvPolynomial.X (Sum.inr (v.1, k))) v.2) := fun v =>
    MvPolynomial.aeval_X _ v
  have hXc : ∀ v, d.sH c (eα (MvPolynomial.X v)) = τ (d.sH c (MvPolynomial.X v)) := by
    intro v
    rw [hX c v, hsX v, hτ, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    try rfl
  have hP : ∀ p : KTp K d.D d.N, d.sH c (eα p) = τ (d.sH c p) := by
    intro p
    induction p using MvPolynomial.induction_on
    · rename_i a
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes, hK]
    · rename_i p q hp hq
      simp only [map_add, hp, hq]
    · rename_i p v hp
      simp only [map_mul, hp, hXc v]
  have hL : ∀ q : KTp K d.D d.N,
      d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) = d.sH c q :=
    fun q => IsFractionRing.lift_algebraMap _ _
  have hR : (d.KTtoS h c).comp (e : KTf K d.D d.N →+* KTf K d.D d.N) =
      (τ : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp (d.KTtoS h c) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (KTp K d.D d.N))
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [he, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hL, hL]
    exact hP p
  have hy : τ (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c) =
      d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c := by
    simp only [bvecG, map_mul, hτΩ]
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have key := Algebra.trace_eq_of_equiv_equiv e τ hR
    (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c)
  rw [hy] at key
  exact (congrArg e key).trans (e.apply_symm_apply _)

/- English proof (translation)
Use `⟨AlgEquiv.ofAlgHom (MvPolynomial.aeval fun w => MvPolynomial.X w + MvPolynomial.C (s w)) (MvPolynomial.aeval fun w => MvPolynomial.X w - MvPolynomial.C (s w)) ?_ ?_, fun w => ?_⟩` and prove the remaining obligations. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `w`. Simplify using the standard rewrite rules. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `w`. Simplify using the standard rewrite rules. Conclude with `MvPolynomial.aeval_X _ w`.
-/
private theorem exists_algEquiv_X_add_C' {σ R : Type} [CommRing R] (s : σ → R) :
    ∃ e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R,
      ∀ w, e (MvPolynomial.X w) = MvPolynomial.X w + MvPolynomial.C (s w) := by
  refine ⟨AlgEquiv.ofAlgHom (MvPolynomial.aeval fun w => MvPolynomial.X w + MvPolynomial.C (s w))
    (MvPolynomial.aeval fun w => MvPolynomial.X w - MvPolynomial.C (s w)) ?_ ?_, fun w => ?_⟩
  · apply MvPolynomial.algHom_ext
    intro w
    simp
  · apply MvPolynomial.algHom_ext
    intro w
    simp
  · exact MvPolynomial.aeval_X _ w

/- English proof (translation)
Establish `hKC : ∀ c (a : K), algebraMap K (OmS (Ω c) d.D d.N) a = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (MvPolynomial.C (algebraMap K (Ω c) a))`. Introduce `c a`. Rewrite using `[IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N), IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq]`. Establish `hsH : ∀ c (P : KTp K d.D d.N), d.sH c P = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (MvPolynomial.aeval (fun w : TVar d.D d.N => Fin.succAboveCases (α` using `fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) (if w.1 = 0 then MvPolynomial.X (Sum.inl ()) else -∑ k, MvPolynomial.X (Sum.inr (w.1, k)) * MvPolynomial.C (d.x c k)) (fun k => MvPolynomial.X (Sum.inr (w.1, k))) w.2) P) := by`. Introduce `c P`.

Proceed by induction on `P using MvPolynomial.induction_on`. Name the introduced variables `a`. Rewrite using `[show d.sH c (MvPolynomial.C a) = algebraMap K (OmS (Ω c) d.D d.N) a from MvPolynomial.aeval_C _ _, hKC, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]`. Name the introduced variables `p q hp hq`. Simplify using `only [map_add, hp, hq]`.

Name the introduced variables `p v hp`. Rewrite using `[map_mul (d.sH c), hp]`. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Use `congr 1`. Conclude with `MvPolynomial.aeval_X _ v`.

Establish `hsa : ∀ c (P0 : MvPolynomial (SVar d.D d.N) (Ω c)) (Pk : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)), Fin.succAboveCases (α` using `fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk (d.jc c) = P0 := fun c P0 Pk => Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk`. Establish `hsb : ∀ c (P0 : MvPolynomial (SVar d.D d.N) (Ω c)) (Pk : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)) (k : Fin d.N), Fin.succAboveCases (α` using `fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk ((d.jc c).succAbove k) = Pk k := fun c P0 Pk k => Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk k`. Establish `hz : ∀ (b : Fin (d.D + 1)) (u : Kˣ), sigF (K` using `K) (D := d.D) (N := d.N) b u (d.De hd h) = d.De hd h := by`. Introduce `b u`. Take `⟨β, hβ, hβC⟩ : ∃ β : ∀ c, MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c] MvPolynomial (SVar d.D d.N) (Ω c), (∀ c w, β c (MvPolynomial.X w) = if Sum.elim (fun _ : Unit => b = 0) (fun q : Fin (d.D + 1) × Fin d.N => q.1 = b) w then MvPolynomial.C (algebraMap K (Ω c) (u : K)) * MvPolynomi …` from `⟨fun c => scaleEquiv (Sum.elim (fun _ : Unit => b = 0) (fun q : Fin (d.D + 1) × Fin d.N => q.1 = b)) (Units.map (algebraMap K (Ω c)).toMonoidHom u), fun c w => by beta_reduce; exact MvPolynomial.aeval_X _ _, fun c ω => AlgEquiv.commutes _ ω⟩`.

Use `sH_comp_eq_of_X_eq d hd h (sigP (N := d.N) b u) β ?_` and prove the remaining obligations. Introduce `c v`. Take `⟨b', j⟩` from `v`. Establish `hs : (sigP (N` using `d.N) b u) (MvPolynomial.X (b', j)) = if b' = b then MvPolynomial.C (u : K) * MvPolynomial.X (b', j) else MvPolynomial.X (b', j) := MvPolynomial.aeval_X _ _`. Rewrite using `[hsH, hs]`.

Use `congr 1`. Use `clear hKC hsH`. Distinguish the cases in `hbb : b' = b`. Substitute `hbb` using the available equality. Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases.

Distinguish the cases in `h0 : b' = 0`. Substitute `h0` using the available equality. Simplify using `[hsa, hβ, MvPolynomial.algebraMap_apply]`. Simplify using `[hsa, hβ, hβC, h0, Finset.mul_sum, mul_assoc, MvPolynomial.algebraMap_apply]`. Simplify using `[hsb, hβ, MvPolynomial.algebraMap_apply]`.

Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases. Distinguish the cases in `h0 : b' = 0`. Substitute `h0` using the available equality. Simplify using `[hsa, hβ, hbb, Ne.symm hbb]`. Simplify using `[hsa, hβ, hβC, h0, hbb]`.

Simplify using `[hsb, hβ, hbb]`. Establish `ht : ∀ t : Fin (d.N + 1) → K, ∃ T : KTp K d.D d.N →ₐ[K] KTp K d.D d.N, (∀ v, T (MvPolynomial.X v) = if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (t v.2) else MvPolynomial.X v) ∧ ∀ p q : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p = d.De hd h * algebraMap (KTp …`. Introduce `t`. Take `⟨eα, heα⟩` from `exists_algEquiv_X_add_C' (σ := TVar d.D d.N) (R := K) (fun v => if v.1 = 0 then t v.2 else 0)`. Use `choose β hβ using fun c : ι => exists_algEquiv_X_add_C' (σ := SVar d.D d.N) (R := Ω c) (Sum.elim (fun _ => algebraMap K (Ω c) (t (d.jc c))) (fun q : Fin (d.D + 1) × Fin d.N => if q.1 = 0 then algebraMap K (Ω c) (t ((d.jc c).succAbove q.2)) else 0))`.

Establish `hinv : (IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv : KTf K d.D d.N ≃+* KTf K d.D d.N) (d.De hd h) = d.De hd h`. Use `sH_comp_eq_of_X_eq d hd h eα β ?_` and prove the remaining obligations. Introduce `c v`. Take `⟨b', j⟩` from `v`. Establish `hβC : ∀ ω : Ω c, β c (MvPolynomial.C ω) = MvPolynomial.C ω` using `fun ω => AlgEquiv.commutes _ ω`.

Rewrite using `[hsH, heα]`. Use `congr 1`. Use `clear hKC hsH hz`. Distinguish the cases in `h0 : b' = 0`. Substitute `h0` using the available equality.

Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases. Simplify using `[hsa, hβ]`. Simplify using `[hsb, hβ]`. Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases. Simplify using `[hsa, hβ, hβC, h0]`.

Simplify using `[hsb, hβ, h0]`. Use `⟨eα.toAlgHom, fun v => ?_, fun p q hpq => ?_⟩` and prove the remaining obligations. Use `show eα (MvPolynomial.X v) = _`. Rewrite using `[heα]`. Distinguish the cases in `hv : v.1 = 0`.

Simplify using `[hv]`. Simplify using `[hv]`. Establish `hc` using `congrArg (IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv : KTf K d.D d.N ≃+* KTf K d.D d.N) hpq`. Rewrite `hc` using `[map_mul, hinv, IsFractionRing.ringEquivOfRingEquiv_algebraMap, IsFractionRing.ringEquivOfRingEquiv_algebraMap]`. Conclude with `hc`.

Take `⟨p, q, hq, hpq, hp0, hq0⟩` from `exists_fraction_free_of_block_zero (d.De hd h) ht`. Take `⟨a, b, hab⟩` from `multi_pres (d.De hd h) hz p q hq hpq hp0 hq0`. Conclude with `⟨a, b, hab⟩`.
-/
theorem de_pres (hd : d.AxH 𝒜) (h : d.S1) : ∃ a b : KTp K d.D d.N, d.IsPres hd h a b := by
  classical
  have hKC : ∀ c (a : K), algebraMap K (OmS (Ω c) d.D d.N) a =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
        (MvPolynomial.C (algebraMap K (Ω c) a)) := by
    intro c a
    rw [IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N),
      IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
        (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq]
  have hsH : ∀ c (P : KTp K d.D d.N), d.sH c P =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
        (MvPolynomial.aeval (fun w : TVar d.D d.N =>
          Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
            (if w.1 = 0 then MvPolynomial.X (Sum.inl ())
              else -∑ k, MvPolynomial.X (Sum.inr (w.1, k)) * MvPolynomial.C (d.x c k))
            (fun k => MvPolynomial.X (Sum.inr (w.1, k))) w.2) P) := by
    intro c P
    induction P using MvPolynomial.induction_on
    · rename_i a
      rw [show d.sH c (MvPolynomial.C a) = algebraMap K (OmS (Ω c) d.D d.N) a from
        MvPolynomial.aeval_C _ _, hKC, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]
    · rename_i p q hp hq
      simp only [map_add, hp, hq]
    · rename_i p v hp
      rw [map_mul (d.sH c), hp]
      simp only [map_mul, MvPolynomial.aeval_X]
      congr 1
      exact MvPolynomial.aeval_X _ v
  have hsa : ∀ c (P0 : MvPolynomial (SVar d.D d.N) (Ω c))
      (Pk : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
      Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk
        (d.jc c) = P0 :=
    fun c P0 Pk =>
      Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk
  have hsb : ∀ c (P0 : MvPolynomial (SVar d.D d.N) (Ω c))
      (Pk : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)) (k : Fin d.N),
      Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk
        ((d.jc c).succAbove k) = Pk k :=
    fun c P0 Pk k =>
      Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) P0 Pk k
  have hz : ∀ (b : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) b u (d.De hd h) = d.De hd h := by
    intro b u
    obtain ⟨β, hβ, hβC⟩ : ∃ β : ∀ c, MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c]
        MvPolynomial (SVar d.D d.N) (Ω c),
        (∀ c w, β c (MvPolynomial.X w) =
          if Sum.elim (fun _ : Unit => b = 0) (fun q : Fin (d.D + 1) × Fin d.N => q.1 = b) w then
            MvPolynomial.C (algebraMap K (Ω c) (u : K)) * MvPolynomial.X w
          else MvPolynomial.X w) ∧
        ∀ c (ω : Ω c), β c (MvPolynomial.C ω) = MvPolynomial.C ω :=
      ⟨fun c => scaleEquiv
        (Sum.elim (fun _ : Unit => b = 0) (fun q : Fin (d.D + 1) × Fin d.N => q.1 = b))
        (Units.map (algebraMap K (Ω c)).toMonoidHom u),
        fun c w => by beta_reduce; exact MvPolynomial.aeval_X _ _,
        fun c ω => AlgEquiv.commutes _ ω⟩
    refine sH_comp_eq_of_X_eq d hd h (sigP (N := d.N) b u) β ?_
    intro c v
    obtain ⟨b', j⟩ := v
    have hs : (sigP (N := d.N) b u) (MvPolynomial.X (b', j)) =
        if b' = b then MvPolynomial.C (u : K) * MvPolynomial.X (b', j)
        else MvPolynomial.X (b', j) := MvPolynomial.aeval_X _ _
    rw [hsH, hs]
    congr 1
    clear hKC hsH
    by_cases hbb : b' = b
    · subst hbb
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases h0 : b' = 0
        · subst h0
          simp [hsa, hβ, MvPolynomial.algebraMap_apply]
        · simp [hsa, hβ, hβC, h0, Finset.mul_sum, mul_assoc, MvPolynomial.algebraMap_apply]
      · simp [hsb, hβ, MvPolynomial.algebraMap_apply]
    · rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases h0 : b' = 0
        · subst h0
          simp [hsa, hβ, hbb, Ne.symm hbb]
        · simp [hsa, hβ, hβC, h0, hbb]
      · simp [hsb, hβ, hbb]
  have ht : ∀ t : Fin (d.N + 1) → K, ∃ T : KTp K d.D d.N →ₐ[K] KTp K d.D d.N,
      (∀ v, T (MvPolynomial.X v) =
        if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (t v.2) else MvPolynomial.X v) ∧
      ∀ p q : KTp K d.D d.N,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p =
          d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q →
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (T p) =
          d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (T q) := by
    intro t
    obtain ⟨eα, heα⟩ := exists_algEquiv_X_add_C' (σ := TVar d.D d.N) (R := K)
      (fun v => if v.1 = 0 then t v.2 else 0)
    choose β hβ using fun c : ι => exists_algEquiv_X_add_C' (σ := SVar d.D d.N) (R := Ω c)
      (Sum.elim (fun _ => algebraMap K (Ω c) (t (d.jc c)))
        (fun q : Fin (d.D + 1) × Fin d.N =>
          if q.1 = 0 then algebraMap K (Ω c) (t ((d.jc c).succAbove q.2)) else 0))
    have hinv : (IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv :
        KTf K d.D d.N ≃+* KTf K d.D d.N) (d.De hd h) = d.De hd h := by
      refine sH_comp_eq_of_X_eq d hd h eα β ?_
      intro c v
      obtain ⟨b', j⟩ := v
      have hβC : ∀ ω : Ω c, β c (MvPolynomial.C ω) = MvPolynomial.C ω :=
        fun ω => AlgEquiv.commutes _ ω
      rw [hsH, heα]
      congr 1
      clear hKC hsH hz
      by_cases h0 : b' = 0
      · subst h0
        rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
        · simp [hsa, hβ]
        · simp [hsb, hβ]
      · rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
        · simp [hsa, hβ, hβC, h0]
        · simp [hsb, hβ, h0]
    refine ⟨eα.toAlgHom, fun v => ?_, fun p q hpq => ?_⟩
    · show eα (MvPolynomial.X v) = _
      rw [heα]
      by_cases hv : v.1 = 0
      · simp [hv]
      · simp [hv]
    · have hc := congrArg (IsFractionRing.ringEquivOfRingEquiv eα.toRingEquiv :
        KTf K d.D d.N ≃+* KTf K d.D d.N) hpq
      rw [map_mul, hinv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap] at hc
      exact hc
  obtain ⟨p, q, hq, hpq, hp0, hq0⟩ := exists_fraction_free_of_block_zero (d.De hd h) ht
  obtain ⟨a, b, hab⟩ := multi_pres (d.De hd h) hz p q hq hpq hp0 hq0
  exact ⟨a, b, hab⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
