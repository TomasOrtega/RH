import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise S (fun m => (QuotientGroup.mk m : G ⧸ K)) T]`. Use `hsum _ _ _ fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ m ∈ S, (QuotientGroup.mk m : G ⧸ K) = q`. Take `⟨m, hm, rfl⟩` from `h`. Establish `e : ∑ k : K, T (m * k) = ∑ i ∈ S with (QuotientGroup.mk i : G ⧸ K) = QuotientGroup.mk m, T i`.

Use `Finset.sum_bij (fun k _ => m * (k : G)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `k _`. Conclude with `Finset.mem_filter.2 ⟨hS m hm k k.2, QuotientGroup.mk_mul_of_mem m k.2⟩`. Introduce `k _ k' _ hk`. Conclude with `Subtype.ext (mul_left_cancel hk)`.

Introduce `i hi`. Use `⟨⟨m⁻¹ * i, QuotientGroup.eq.1 (Finset.mem_filter.1 hi).2.symm⟩, Finset.mem_univ _, by simp⟩` and prove the remaining obligations. Introduce `k _`. Both sides reduce to the same expression. Rewrite using `[← e]`.

Conclude with `ho m hm`. Rewrite using `[Finset.filter_eq_empty_iff.2 fun m hm e => h ⟨m, hm, e⟩]`. Conclude with `hsum _ _ _ fun i hi => absurd hi (Finset.notMem_empty i)`.
-/
private theorem orbit_sum {G V : Type} [Group G] [Fintype G] [AddCommMonoid V] (K : Subgroup G) (S : Finset G)
    (hS : ∀ m ∈ S, ∀ k ∈ K, m * k ∈ S) (T : G → V) (Q : V → Prop)
    (hsum : ∀ (ι : Type) (s : Finset ι) (a : ι → V), (∀ i ∈ s, Q (a i)) → Q (∑ i ∈ s, a i))
    (ho : ∀ m ∈ S, Q (∑ k : K, T (m * k))) : Q (∑ m ∈ S, T m) := by
  rw [← Finset.sum_fiberwise S (fun m => (QuotientGroup.mk m : G ⧸ K)) T]
  refine hsum _ _ _ fun q _ => ?_
  by_cases h : ∃ m ∈ S, (QuotientGroup.mk m : G ⧸ K) = q
  · obtain ⟨m, hm, rfl⟩ := h
    have e : ∑ k : K, T (m * k) = ∑ i ∈ S with (QuotientGroup.mk i : G ⧸ K) = QuotientGroup.mk m, T i := by
      refine Finset.sum_bij (fun k _ => m * (k : G)) ?_ ?_ ?_ ?_
      · intro k _
        exact Finset.mem_filter.2 ⟨hS m hm k k.2, QuotientGroup.mk_mul_of_mem m k.2⟩
      · intro k _ k' _ hk
        exact Subtype.ext (mul_left_cancel hk)
      · intro i hi
        refine ⟨⟨m⁻¹ * i, QuotientGroup.eq.1 (Finset.mem_filter.1 hi).2.symm⟩, Finset.mem_univ _, by simp⟩
      · intro k _; rfl
    rw [← e]; exact ho m hm
  · rw [Finset.filter_eq_empty_iff.2 fun m hm e => h ⟨m, hm, e⟩]
    exact hsum _ _ _ fun i hi => absurd hi (Finset.notMem_empty i)

private def rho (M : ℕ) : SL(2, ℤ) →* GL (Fin 2) (ZMod M) :=
  Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem rho_coe (M : ℕ) (γ : SL(2, ℤ)) :
    (rho M γ : Matrix (Fin 2) (Fin 2) (ZMod M)) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) := rfl

/- English proof (translation)
Use `ext`. Conclude with `(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ).2`.
-/
private theorem rho_det (M : ℕ) (γ : SL(2, ℤ)) : Matrix.GeneralLinearGroup.det (rho M γ) = 1 := by
  ext
  exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ).2

/- English proof (translation)
Rewrite using `[CongruenceSubgroup.Gamma_mem']`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Subtype.ext (congrArg Units.val h)`. Introduce `h`.

Simplify using `[rho, h]`.
-/
private theorem rho_one (M : ℕ) (γ : SL(2, ℤ)) : rho M γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  constructor
  · intro h
    exact Subtype.ext (congrArg Units.val h)
  · intro h
    simp [rho, h]

/- English proof (translation)
Establish `hv : ∀ z : ZMod M, (z.val : ZMod k) = ZMod.castHom h (ZMod k) z` using `fun z => by`. Rewrite using `[ZMod.natCast_val, ZMod.castHom_apply]`. Rewrite using `[hv, hv, hv, Units.val_mul, rho_coe, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `only [Matrix.map_apply, eq_intCast, map_add, map_mul, map_intCast]`.
-/
private theorem val_mul {M : ℕ} [NeZero M] (k : ℕ) (h : k ∣ M) (m : GL (Fin 2) (ZMod M)) (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i j).val : ZMod k) =
      (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0).val : ZMod k) * (γ 0 j : ℤ) +
        (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1).val : ZMod k) * (γ 1 j : ℤ) := by
  have hv : ∀ z : ZMod M, (z.val : ZMod k) = ZMod.castHom h (ZMod k) z := fun z => by
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [hv, hv, hv, Units.val_mul, rho_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.map_apply, eq_intCast, map_add, map_mul, map_intCast]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hγ`. Establish `h1` using `(CongruenceSubgroup.Gamma1_mem N γ).1 h1`. Establish `h2 : ((γ 1 0 : ℤ) : ZMod l) = 0` using `CongruenceSubgroup.Gamma0_mem.1 h2`. Take `⟨a, b, c⟩` from `hm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[val_mul N hN, a, h1.2.2]`. Simplify using the standard rewrite rules. Rewrite using `[val_mul N hN, b, h1.1, h1.2.2]`. Simplify using the standard rewrite rules. Rewrite using `[val_mul l hl, val_mul l hl, h2]`.

Take the linear combination `((γ 0 0 : ℤ) : ZMod l) * c`.
-/
private theorem cnd_mul {l N M : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (m : GL (Fin 2) (ZMod M))
    (hm : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    Cnd l N g ((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  obtain ⟨h1, h2⟩ := hγ
  have h1 := (CongruenceSubgroup.Gamma1_mem N γ).1 h1
  have h2 : ((γ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 h2
  obtain ⟨a, b, c⟩ := hm
  refine ⟨?_, ?_, ?_⟩
  · rw [val_mul N hN, a, h1.2.2]; simp
  · rw [val_mul N hN, b, h1.1, h1.2.2]; simp
  · rw [val_mul l hl, val_mul l hl, h2]
    linear_combination ((γ 0 0 : ℤ) : ZMod l) * c

/- English proof (translation)
Establish `key : ∀ k, k ∣ M → CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma k`. Introduce `k hk γ hγ`. Rewrite `hγ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨a, b, c, d⟩` from `hγ`. Establish `a` using `congrArg (ZMod.castHom hk (ZMod k)) a`.

Establish `b` using `congrArg (ZMod.castHom hk (ZMod k)) b`. Establish `c` using `congrArg (ZMod.castHom hk (ZMod k)) c`. Establish `d` using `congrArg (ZMod.castHom hk (ZMod k)) d`. Simplify using `only [map_intCast, map_one, map_zero] at a b c d`. Conclude with `⟨a, b, c, d⟩`.

Introduce `γ hγ`. Establish `h1` using `CongruenceSubgroup.Gamma_mem.1 (key N hN hγ)`. Establish `h2` using `CongruenceSubgroup.Gamma_mem.1 (key l hl hγ)`. Conclude with `⟨⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩, key _ hn hγ⟩`.
-/
private theorem gam_le {l n N M : ℕ} (hN : N ∣ M) (hl : l ∣ M) (hn : l ^ n ∣ M) :
    CongruenceSubgroup.Gamma M ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) := by
  have key : ∀ k, k ∣ M → CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma k := by
    intro k hk γ hγ
    rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
    obtain ⟨a, b, c, d⟩ := hγ
    have a := congrArg (ZMod.castHom hk (ZMod k)) a
    have b := congrArg (ZMod.castHom hk (ZMod k)) b
    have c := congrArg (ZMod.castHom hk (ZMod k)) c
    have d := congrArg (ZMod.castHom hk (ZMod k)) d
    simp only [map_intCast, map_one, map_zero] at a b c d
    exact ⟨a, b, c, d⟩
  intro γ hγ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (key N hN hγ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (key l hl hγ)
  exact ⟨⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩,
    key _ hn hγ⟩

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private def FU (X : Tower Ω ε) (N M₀ : ℕ) {M : ℕ} (x y : Row M₀) (a : Fam X M₀) (m : GL (Fin 2) (ZMod M)) : X.Kˣ :=
  slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
    (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))))

/- English proof (translation)
Take `⟨c1, -, c2, c3⟩` from `sCdFacts N M₀ M hM`. Take `⟨-, s1, s2, -, s3, -⟩` from `sSlD Ω ε X N (NeZero.pos N)`. Take `⟨e1, e2⟩` from `ha _ _ (c2 m hm x y hxy)`. Use `⟨s3 _ _ _ e1, fun γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ`.

Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Set `γ' : SL(2, ℤ)` to `⟨!![γ 0 0, N * γ 0 1; t, γ 1 1], by`. Rewrite using `[Matrix.det_fin_two_of]`.

Rewrite `hdet` using `[ht]`. Take the linear combination `hdet⟩`. Establish `hc : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [γ', Matrix.mul_apply, Fin.sum_univ_two, ht, mul_comm]`.

Establish `hN : N ∣ M` using `⟨_, hM⟩`. Establish `hr : (((rho M γ : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0`. Use `val_mul N hN 1 γ 1 0` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[this, hγ]`.

Simplify using the standard rewrite rules. Establish `hcd : cD N M₀ ((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)) * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M₀))`. Rewrite using `[Units.val_mul, c1 _ _ hm hr, rho_coe, c3 _ _ hc]`. Take `⟨h, hh⟩` from `e2 γ'`. Use `⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩` and prove the remaining obligations.

Unfold `FU`. Rewrite using `[hcd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← map_pow, ← map_mul]`. Unfold `rt at hh`. Rewrite using `[← hh]`. Use `ext`.

Use `s1 _ _ (by rw [γ.2]; exact one_pos) hc (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K)` as an intermediate fact. Rewrite `this` using `[s2, s2]`. Conclude with `this`.
-/
private theorem FU_act (X : Tower Ω ε) {k N M₀ M : ℕ} [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀)
    (x y : Row M₀) (hxy : Ok x y) (a : Fam X M₀) (ha : Eqv X k M₀ a) (m : GL (Fin 2) (ZMod M))
    (hm : (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0) :
    FU X N M₀ x y a m ∈ X.Un k ∧ ∀ γ : SL(2, ℤ), ((γ 1 0 : ℤ) : ZMod N) = 0 →
      Cgr k (slU X (ofSL γ) (FU X N M₀ x y a m)) (FU X N M₀ x y a (m * rho M γ)) := by
  obtain ⟨c1, -, c2, c3⟩ := sCdFacts N M₀ M hM
  obtain ⟨-, s1, s2, -, s3, -⟩ := sSlD Ω ε X N (NeZero.pos N)
  obtain ⟨e1, e2⟩ := ha _ _ (c2 m hm x y hxy)
  refine ⟨s3 _ _ _ e1, fun γ hγ => ?_⟩
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, N * γ 0 1; t, γ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [ht] at hdet; linear_combination hdet⟩
  have hc : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ', Matrix.mul_apply, Fin.sum_univ_two, ht, mul_comm]
  have hN : N ∣ M := ⟨_, hM⟩
  have hr : (((rho M γ : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0 := by
    have := val_mul N hN 1 γ 1 0
    rw [one_mul] at this
    rw [this, hγ]; simp
  have hcd : cD N M₀ ((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)) * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M₀)) := by
    rw [Units.val_mul, c1 _ _ hm hr, rho_coe, c3 _ _ hc]
  obtain ⟨h, hh⟩ := e2 γ'
  refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
  unfold FU
  rw [hcd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← map_pow, ← map_mul]
  unfold rt at hh
  rw [← hh]
  ext
  have := s1 _ _ (by rw [γ.2]; exact one_pos) hc
    (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K)
  rw [s2, s2] at this
  exact this

private def lamOf {M : ℕ} (m : GL (Fin 2) (ZMod M)) : Fin 2 → ℤ :=
  fun j => (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 j).val : ℤ)

/- English proof (translation)
Take `⟨-, -, -, -, a1, -⟩` from `sApi Ω ε X l n`. Take `⟨c1, -, -, c2, c3, -⟩` from `sCls Ω ε X l n`. Take `⟨-, -, s2, -⟩` from `sSlD Ω ε X 1 one_pos`. Introduce `u`. Establish `hd : ∀ j, (l : ℤ_[l]) ^ n ∣ ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ℤ_[l])`.

Introduce `j`. Establish `h : ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ZMod (l ^ n)) = 0`. Use `val_mul (l ^ n) hn m γ 0 j` as an intermediate fact. Simplify using `only [lamOf, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]`. Rewrite using `[this, sub_self]`.

Take `⟨t, ht⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h`. Conclude with `⟨t, by rw [ht]; push_cast; rfl⟩`. Establish `hk` using `c2 _ _ _ _ (c3 (X.sl (ofSL γ)).toRingEquiv f _ (c1 f)) (c1 f') hf`. Use `set A := X.kmap l (X.sl (ofSL γ)).toRingEquiv (clsK X l n (f : X.K)) with hA`. Use `set B := clsK X l n (f' : X.K)`.

Use `set k : ℤ_[l] := (lamOf m 0 : ℤ_[l]) * (mZl l γ *ᵥ u) 0 + (lamOf m 1 : ℤ_[l]) * (mZl l γ *ᵥ u) 1 with hk1`. Use `set k' : ℤ_[l] := (lamOf (m * rho M γ) 0 : ℤ_[l]) * u 0 + (lamOf (m * rho M γ) 1 : ℤ_[l]) * u 1 with hk2`. Establish `hkk : (l : ℤ_[l]) ^ n ∣ k ^ w - k' ^ w`. Use `dvd_trans ?_ (sub_dvd_pow_sub_pow k k' w)` and prove the remaining obligations. Use `dvd_add (Dvd.dvd.mul_right (hd 0) (u 0)) (Dvd.dvd.mul_right (hd 1) (u 1))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [hk1, hk2, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w (lamOf m) (clsK X l n (f : X.K))) u - sec X l w (lamOf (m * rho M γ)) B u = (k ^ w • A - k' ^ w • A) + k' ^ w • (A - B)` using `by show X.kmap l (X.sl (toGQ γ)).toRingEquiv (k ^ w • clsK X l n (f : X.K)) - k' ^ w • B = _`.

Rewrite using `[s2, map_smul, ← hA, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, map_add, a1 _ _ _ hkk, map_smul, hk, smul_zero, add_zero]`.
-/
private theorem sec_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} [NeZero M] (w : ℕ) (hn : l ^ n ∣ M)
    (m : GL (Fin 2) (ZMod M)) (γ : SL(2, ℤ)) (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL γ) f) f') :
    CgF X l n (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w (lamOf m) (clsK X l n (f : X.K))))
      (sec X l w (lamOf (m * rho M γ)) (clsK X l n (f' : X.K))) := by
  obtain ⟨-, -, -, -, a1, -⟩ := sApi Ω ε X l n
  obtain ⟨c1, -, -, c2, c3, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, s2, -⟩ := sSlD Ω ε X 1 one_pos
  intro u
  have hd : ∀ j, (l : ℤ_[l]) ^ n ∣ ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ℤ_[l]) := by
    intro j
    have h : ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ZMod (l ^ n)) = 0 := by
      have := val_mul (l ^ n) hn m γ 0 j
      simp only [lamOf, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [this, sub_self]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  have hk := c2 _ _ _ _ (c3 (X.sl (ofSL γ)).toRingEquiv f _ (c1 f)) (c1 f') hf
  set A := X.kmap l (X.sl (ofSL γ)).toRingEquiv (clsK X l n (f : X.K)) with hA
  set B := clsK X l n (f' : X.K)
  set k : ℤ_[l] := (lamOf m 0 : ℤ_[l]) * (mZl l γ *ᵥ u) 0 + (lamOf m 1 : ℤ_[l]) * (mZl l γ *ᵥ u) 1 with hk1
  set k' : ℤ_[l] := (lamOf (m * rho M γ) 0 : ℤ_[l]) * u 0 + (lamOf (m * rho M γ) 1 : ℤ_[l]) * u 1 with hk2
  have hkk : (l : ℤ_[l]) ^ n ∣ k ^ w - k' ^ w := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow k k' w)
    have := dvd_add (Dvd.dvd.mul_right (hd 0) (u 0)) (Dvd.dvd.mul_right (hd 1) (u 1))
    convert this using 1
    simp only [hk1, hk2, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast]
    push_cast
    ring
  have e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w (lamOf m) (clsK X l n (f : X.K))) u -
      sec X l w (lamOf (m * rho M γ)) B u = (k ^ w • A - k' ^ w • A) + k' ^ w • (A - B) := by
    show X.kmap l (X.sl (toGQ γ)).toRingEquiv (k ^ w • clsK X l n (f : X.K)) - k' ^ w • B = _
    rw [s2, map_smul, ← hA, smul_sub]; abel
  rw [e, map_add, a1 _ _ _ hkk, map_smul, hk, smul_zero, add_zero]

end UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy P a ha`. Establish `hN : N ∣ M` using `⟨_, hL.eq⟩`. Establish `hn : l ^ n ∣ M` using `hL.eq ▸ Dvd.dvd.mul_left hL.dl N`. Establish `hl : l ∣ M` using `(dvd_pow_self l (Nat.one_le_iff_ne_zero.1 hL.pos)).trans hn`. Take `⟨-, -, i1, i2, i3, -⟩` from `sInvApi Ω ε X l N w n`.

Take `⟨eqv, -, a1, a2, -⟩` from `sApi Ω ε X l n`. Take `⟨c1, -⟩` from `sCls Ω ε X l n`. Set `T : GL (Fin 2) (ZMod M) → X.Fn l` to `fun m => ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) • sec X l w (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K))`. Establish `hX : Xi X l n N M₀ M w g x y P a = ∑ m ∈ Finset.univ.filter (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)), T m`. Use function extensionality and compare the values at `u`.

Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [T, Pi.smul_apply, sec, lamOf, Int.cast_natCast, smul_smul]`. Both sides reduce to the same expression. Rewrite using `[hX]`.

Use `orbit_sum ((Gam N l).map (rho M)) _ ?_ T (InvM X l N w n) i3 ?_` and prove the remaining obligations. Introduce and unpack `m hm _ ⟨γ, hγ, rfl⟩`. Rewrite `hm`, the goal using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, cnd_mul hN hl g m hm.2.1 γ hγ, by rw [map_mul, rho_det, mul_one]; exact hm.2.2⟩`. Introduce `m hm`.

Take `⟨u1, u2⟩` from `FU_act X hL.eq x y hxy a ha m (Finset.mem_filter.1 hm).2.1.1`. Establish `h10 : ∀ γ ∈ Gam N l, ((γ 1 0 : ℤ) : ZMod N) = 0` using `fun γ hγ => ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ.1).2.2`. Use `choose γ hγ hr using fun k : (Gam N l).map (rho M) => k.2`. Establish `hle` using `gam_le hN hl hn`. Establish `htr : IsTr (CongruenceSubgroup.Gamma M) (Gam N l) γ`.

Use `⟨hγ, fun δ hδ => ⟨⟨rho M δ, δ, hδ, rfl⟩, ?_, fun k hk => ?_⟩⟩` and prove the remaining obligations. Use `show _ ∈ _`. Rewrite using `[← rho_one, map_mul, map_inv, hr, mul_inv_cancel]`. Establish `hk : _ ∈ _` using `hk`. Rewrite `hk` using `[← rho_one, map_mul, map_inv, hr, mul_inv_eq_one]`.

Conclude with `Subtype.ext hk.symm`. Establish `hinv : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (FU X N M₀ x y a m)`. Introduce `δ hδ`. Take `⟨h, hh⟩` from `u2 δ (h10 δ (hle hδ).1)`. Rewrite `hh` using `[(rho_one M δ).2 hδ, mul_one]`.

Establish `h2` using `congrArg Units.val hh`. Rewrite `h2` using `[Units.val_mul, Units.val_pow_eq_pow_val]`. Conclude with `⟨h, h2⟩`. Take `⟨t1, t2, -⟩` from `trc ε X l N w n _ hle _ γ htr (lamOf m) _ _ (c1 (FU X N M₀ x y a m))`. Establish `hI : InvM X l N w n (trH X l w γ (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K)))` using `⟨⟨_, t1 u1, eqv.refl _⟩, t2 hinv, hW n _ M (NeZero.pos M) le_rfl hle _ γ htr _ _ _ u1 hinv (c1 _)⟩`.

Use `i2 _ _ ?_ (i1 ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) _ hI)` and prove the remaining obligations. Unfold `trH`. Rewrite using `[Finset.smul_sum]`. Use `a2 _ _ _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hr k]`.

Simplify using `only [T]`. Rewrite using `[map_mul, rho_det, mul_one]`. Conclude with `a1 _ _ _ (eqv.symm (sec_act X l w hn m (γ k) _ _ (u2 _ (h10 _ (hγ k)))))`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sXiInv :
    UpperTheory.V.Z.Kato.Nb.SXiInv := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy P a ha
  have hN : N ∣ M := ⟨_, hL.eq⟩
  have hn : l ^ n ∣ M := hL.eq ▸ Dvd.dvd.mul_left hL.dl N
  have hl : l ∣ M := (dvd_pow_self l (Nat.one_le_iff_ne_zero.1 hL.pos)).trans hn
  obtain ⟨-, -, i1, i2, i3, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨eqv, -, a1, a2, -⟩ := sApi Ω ε X l n
  obtain ⟨c1, -⟩ := sCls Ω ε X l n
  let T : GL (Fin 2) (ZMod M) → X.Fn l := fun m =>
    ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) •
      sec X l w (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K))
  have hX : Xi X l n N M₀ M w g x y P a = ∑ m ∈ Finset.univ.filter (fun m : GL (Fin 2) (ZMod M) =>
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)), T m := by
    funext u
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [T, Pi.smul_apply, sec, lamOf, Int.cast_natCast, smul_smul]
    rfl
  rw [hX]
  refine orbit_sum ((Gam N l).map (rho M)) _ ?_ T (InvM X l N w n) i3 ?_
  · rintro m hm _ ⟨γ, hγ, rfl⟩
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_univ _, cnd_mul hN hl g m hm.2.1 γ hγ, by rw [map_mul, rho_det, mul_one]; exact hm.2.2⟩
  · intro m hm
    obtain ⟨u1, u2⟩ := FU_act X hL.eq x y hxy a ha m (Finset.mem_filter.1 hm).2.1.1
    have h10 : ∀ γ ∈ Gam N l, ((γ 1 0 : ℤ) : ZMod N) = 0 := fun γ hγ => ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ.1).2.2
    choose γ hγ hr using fun k : (Gam N l).map (rho M) => k.2
    have hle := gam_le hN hl hn
    have htr : IsTr (CongruenceSubgroup.Gamma M) (Gam N l) γ := by
      refine ⟨hγ, fun δ hδ => ⟨⟨rho M δ, δ, hδ, rfl⟩, ?_, fun k hk => ?_⟩⟩
      · show _ ∈ _
        rw [← rho_one, map_mul, map_inv, hr, mul_inv_cancel]
      · have hk : _ ∈ _ := hk
        rw [← rho_one, map_mul, map_inv, hr, mul_inv_eq_one] at hk
        exact Subtype.ext hk.symm
    have hinv : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (FU X N M₀ x y a m) := by
      intro δ hδ
      obtain ⟨h, hh⟩ := u2 δ (h10 δ (hle hδ).1)
      rw [(rho_one M δ).2 hδ, mul_one] at hh
      have h2 := congrArg Units.val hh
      rw [Units.val_mul, Units.val_pow_eq_pow_val] at h2
      exact ⟨h, h2⟩
    obtain ⟨t1, t2, -⟩ := trc ε X l N w n _ hle _ γ htr (lamOf m) _ _ (c1 (FU X N M₀ x y a m))
    have hI : InvM X l N w n (trH X l w γ (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K))) :=
      ⟨⟨_, t1 u1, eqv.refl _⟩, t2 hinv, hW n _ M (NeZero.pos M) le_rfl hle _ γ htr _ _ _ u1 hinv (c1 _)⟩
    refine i2 _ _ ?_ (i1 ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) _ hI)
    unfold trH
    rw [Finset.smul_sum]
    refine a2 _ _ _ _ fun k _ => ?_
    rw [← hr k]
    simp only [T]
    rw [map_mul, rho_det, mul_one]
    exact a1 _ _ _ (eqv.symm (sec_act X l w hn m (γ k) _ _ (u2 _ (h10 _ (hγ k)))))

end
