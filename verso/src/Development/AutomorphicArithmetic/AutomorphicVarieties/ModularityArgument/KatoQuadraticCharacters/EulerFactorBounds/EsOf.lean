import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SEsT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerFunctionUniformExceptionalPrStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

/- English proof (translation)
The claim follows from `h ▸ dvd_add (ha.mul_right x) (hb.mul_right y)`.
-/
private theorem dvd2 {R : Type} [CommRing R] {d a b x y z : R} (ha : d ∣ a) (hb : d ∣ b) (h : z = a * x + b * y) : d ∣ z :=
  h ▸ dvd_add (ha.mul_right x) (hb.mul_right y)

/- English proof (translation)
Introduce `l hl Ω _ _ _ ε X ho N w hN`. Establish `hM0 : 0 < 6 * l * N` using `by have := hl.out.pos; positivity`. Take `⟨φ, hφ1, hφ2⟩` from `X.j_hol`. Take `⟨S, hS⟩` from `hU ε X ⟨φ, hφ2, hφ1⟩ l (6 * l * N) hl.out hM0 ⟨6 * N, by ring⟩`. Use `⟨S ∪ (6 * l * N).primeFactors, fun v B σ hv hq hB hσ b hb => ?_⟩` and prove the remaining obligations.

Use `set q := normV v with hqdef`. Rewrite `hv` using `[Finset.mem_union, not_or]`. Establish `hc : Nat.Coprime q (6 * l * N)` using `(Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hv.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0.ne'⟩)`. Establish `hcl : Nat.Coprime q l` using `hc.coprime_dvd_right ⟨6 * N, by ring⟩`. Establish `hql : q ≠ l` using `fun h => by`.

Rewrite `hcl` using `[h, Nat.coprime_self]`. Conclude with `hl.out.ne_one hcl`. Take `⟨hF, hχ⟩` from `h2 Ω l v B σ hq hql hB hσ`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]`. Normalize the expressions using the abelian group laws. Consider the case `smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]`. Consider the case `mem b hb`. Use function extensionality and compare the values at `u`.

Rewrite using `[← sub_eq_zero]`. Establish `sep : ∀ x : X.Khat l, (∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0) → x = 0` using `fun x h => AdicCompletion.ext fun n => by simpa [AdicCompletion.eval_apply] using h n`. Use `sep _ fun n => ?_` and prove the remaining obligations. Take `⟨c1, c2, c3⟩` from `h1 Ω ε X l N w hN b hb n`. Take `⟨k, F, hk, hFu, hFl, hR⟩` from `c3 ![u 0, (q : ℤ_[l]) * u 1]`.

Use `set M := 6 * l * N * l ^ k with hM`. Establish `hMpos : 0 < M` using `by have := hl.out.pos; positivity`. Establish `hcM : Nat.Coprime q M` using `Nat.Coprime.mul_right hc (hcl.pow_right k)`. Take `⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), DiagMod M q γ` from `by haveI : NeZero M := ⟨hMpos.ne'⟩`. Set `t` to `ZMod.unitOfCoprime q hcM`.

Take `⟨γ, hγ⟩` from `GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective M (⟨!![((t⁻¹ : (ZMod M)ˣ) : ZMod M), 0; 0, (t : ZMod M)], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ZMod M))`. Establish `e` using `fun i j => congrArg (fun m : SL(2, ZMod M) => (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) hγ`. Conclude with `⟨γ, by simpa [en] using e 0 1, by simpa [en] using e 1 0, by simpa [en, t] using e 1 1⟩`. Take `⟨g, hg⟩` from `hS q hq hv.1 B σ hF n k F hFu hFl γ hγ`. Take `⟨t1, t2⟩` from `h3 Ω ε X l N w q M hN hq (hc.coprime_dvd_right ⟨6, by ring⟩) hcM ⟨6 * l ^ k, by rw [hM]; ring⟩ γ hγ b hb`.

Take `⟨-, r2, r3, r4, r5, -, -⟩` from `sCls Ω ε X l n`. Establish `hd : ∀ z : ℤ, (M : ℤ) ∣ z → (l : ℤ_[l]) ^ n ∣ (z : ℤ_[l])` using `fun z hz => by`. Establish `: ((l ^ n : ℕ) : ℤ) ∣ z` using `(Int.natCast_dvd_natCast.2 ((pow_dvd_pow l hk).mul_left _)).trans hz`. Simplify using `using (Int.castRingHom ℤ_[l]).map_dvd this`. Establish `d01` using `hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.1)`.

Establish `d10` using `hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.2.1)`. Establish `d11` using `hd (en γ 1 1 - q) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [hγ.2.2, sub_self]))`. Establish `dM` using `hd M dvd_rfl`. Establish `hdet : ((en γ 0 0 : ℤ) : ℤ_[l]) * (en γ 1 1 : ℤ) - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1`. Use `γ.det_coe` as an intermediate fact.

Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `congrArg (Int.cast : ℤ → ℤ_[l]) this` after adjusting the coercions. Move the coercions through the operations in `at d11 dM`. Establish `d00 : (l : ℤ_[l]) ^ n ∣ ((en γ 0 0 : ℤ) : ℤ_[l]) * q - 1` using `dvd2 (x := -((en γ 0 0 : ℤ) : ℤ_[l])) (y := ((en γ 1 0 : ℤ) : ℤ_[l])) d11 d01 (by linear_combination hdet)`. Establish `near : ∀ u' : Fin 2 → ℤ_[l], (l : ℤ_[l]) ^ n ∣ u' 0 - u 0 → (l : ℤ_[l]) ^ n ∣ u' 1 - q * u 1 → Rep X l n F ((4 : ℤ_[l]) • b u')` using `fun u' a0 a1 => by`.

Use `c1 u' ![u 0, (q : ℤ_[l]) * u 1] (Fin.forall_fin_two.2 ⟨a0, a1⟩)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Unfold `UpperTheory.Kd.K4.Rep at hR ⊢`. Rewrite using `[map_smul, this, ← map_smul, hR]`. Establish `one : Rep X l n 1 0` using `by simpa using (r2 _ _ _ _ hR hR).2`.

Establish `A : ∀ s : Finset ℕ, Rep X l n (∏ j ∈ s, Units.map ((X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv : X.K →* X.K) F) (∑ j ∈ s, (4 : ℤ_[l]) • X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u)` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using one`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`.

Use `(r2 _ _ _ _ ?_ ih).1` and prove the remaining obligations. Use `r5 (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv _ _ (near (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) (dvd2 (x := j * u 1) (y := 0) dM dM (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)) (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]))` as an intermediate fact. Rewrite `this` using `[map_smul]`. Then use the resulting hypothesis. Establish `Bq` using `r5 (X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv _ _ (near (mZl l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) *ᵥ u) (dvd2 (x := u 0) (y := u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply …`. Establish `Cq` using `r5 (X.gal σ) _ _ hR`.

Use `set χ' : ℤ_[l] := (cyclotomicCharacter Ω l (σ⁻¹).toRingEquiv : ℤ_[l]) with hχ'`. Establish `hχq : (q : ℤ_[l]) * χ' = 1`. Rewrite using `[← hχ, hχ', ← Units.val_mul, ← map_mul]`. Establish `: σ.toRingEquiv * (σ⁻¹).toRingEquiv = 1`. Use extensionality with `z`.

Conclude with `σ.apply_symm_apply z`. Rewrite using `[this, map_one, Units.val_one]`. Establish `D0` using `near ((q : ℤ_[l]) • (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ' * u 1])) (dvd2 (x := u 0) (y := q * χ' * u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)) (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by`. Simplify using `[mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Take the linear combination `(((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℤ_[l]) * u 1 * hχq))`.

Rewrite `D0` using `[c2]`. Establish `D` using `r3 _ _ q (r5 (X.gal σ⁻¹) _ _ (r5 (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ D0))`. Establish `fin` using `r4 _ _ _ _ (r2 _ _ _ _ (A (Finset.range q)) Bq).1 (r2 _ _ _ _ Cq D).1 ⟨g, Units.ext (by`. Rewrite using `[(sSlD Ω ε X N hN).2.2.1 γ]`. Establish `hg' : Nq X M q F * _ = X.gal σ F * (X.gal σ⁻¹ _) ^ q * _` using `hg`.

Use `clear_value M`. Simplify `hg')⟩` using `[Nq, Units.coe_prod]`. Establish `h4 : IsUnit (4 : ℤ_[l])`. Establish `: IsUnit ((4 : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`.

Conclude with `((Nat.coprime_primes hl.out Nat.prime_two).2 ho).pow_right 2`. Simplify using `using this`. Rewrite using `[← h4.smul_eq_zero, ← map_smul, ← fin, t1, t2]`. Use `congr 1`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_sub, smul_add, Finset.smul_sum, map_smul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `_ + (4 : ℤ_[l]) • (q : ℤ_[l]) ^ (w + 1) • X.kmap l (X.gal σ⁻¹) (X.kmap l _ (b _)) = _`. Rewrite using `[smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(4 : ℤ_[l]) • X.kmap l (X.gal σ) (b _) = _`.

Rewrite using `[hχ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem es_of (h1 : SEsLev) (h2 : SEsFrob) (h3 : SEsT)
    (hU : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → ES.Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n)) :
    SEs := by
  intro l hl Ω _ _ _ ε X ho N w hN
  have hM0 : 0 < 6 * l * N := by have := hl.out.pos; positivity
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  obtain ⟨S, hS⟩ := hU ε X ⟨φ, hφ2, hφ1⟩ l (6 * l * N) hl.out hM0 ⟨6 * N, by ring⟩
  refine ⟨S ∪ (6 * l * N).primeFactors, fun v B σ hv hq hB hσ b hb => ?_⟩
  set q := normV v with hqdef
  rw [Finset.mem_union, not_or] at hv
  have hc : Nat.Coprime q (6 * l * N) := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h =>
    hv.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0.ne'⟩)
  have hcl : Nat.Coprime q l := hc.coprime_dvd_right ⟨6 * N, by ring⟩
  have hql : q ≠ l := fun h => by
    rw [h, Nat.coprime_self] at hcl
    exact hl.out.ne_one hcl
  obtain ⟨hF, hχ⟩ := h2 Ω l v B σ hq hql hB hσ
  induction hb using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]
  | mem b hb =>
  funext u
  rw [← sub_eq_zero]
  have sep : ∀ x : X.Khat l, (∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0) → x = 0 := fun x h =>
    AdicCompletion.ext fun n => by simpa [AdicCompletion.eval_apply] using h n
  refine sep _ fun n => ?_
  obtain ⟨c1, c2, c3⟩ := h1 Ω ε X l N w hN b hb n
  obtain ⟨k, F, hk, hFu, hFl, hR⟩ := c3 ![u 0, (q : ℤ_[l]) * u 1]
  set M := 6 * l * N * l ^ k with hM
  have hMpos : 0 < M := by have := hl.out.pos; positivity
  have hcM : Nat.Coprime q M := Nat.Coprime.mul_right hc (hcl.pow_right k)
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), DiagMod M q γ := by
    haveI : NeZero M := ⟨hMpos.ne'⟩
    let t := ZMod.unitOfCoprime q hcM
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective M (⟨!![((t⁻¹ : (ZMod M)ˣ) : ZMod M), 0; 0, (t : ZMod M)], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ZMod M))
    have e := fun i j => congrArg (fun m : SL(2, ZMod M) => (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) hγ
    exact ⟨γ, by simpa [en] using e 0 1, by simpa [en] using e 1 0, by simpa [en, t] using e 1 1⟩
  obtain ⟨g, hg⟩ := hS q hq hv.1 B σ hF n k F hFu hFl γ hγ
  obtain ⟨t1, t2⟩ := h3 Ω ε X l N w q M hN hq (hc.coprime_dvd_right ⟨6, by ring⟩) hcM ⟨6 * l ^ k, by rw [hM]; ring⟩ γ hγ b hb
  obtain ⟨-, r2, r3, r4, r5, -, -⟩ := sCls Ω ε X l n
  have hd : ∀ z : ℤ, (M : ℤ) ∣ z → (l : ℤ_[l]) ^ n ∣ (z : ℤ_[l]) := fun z hz => by
    have : ((l ^ n : ℕ) : ℤ) ∣ z := (Int.natCast_dvd_natCast.2 ((pow_dvd_pow l hk).mul_left _)).trans hz
    simpa using (Int.castRingHom ℤ_[l]).map_dvd this
  have d01 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.1)
  have d10 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.2.1)
  have d11 := hd (en γ 1 1 - q) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [hγ.2.2, sub_self]))
  have dM := hd M dvd_rfl
  have hdet : ((en γ 0 0 : ℤ) : ℤ_[l]) * (en γ 1 1 : ℤ) - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[l]) this
  push_cast at d11 dM
  have d00 : (l : ℤ_[l]) ^ n ∣ ((en γ 0 0 : ℤ) : ℤ_[l]) * q - 1 :=
    dvd2 (x := -((en γ 0 0 : ℤ) : ℤ_[l])) (y := ((en γ 1 0 : ℤ) : ℤ_[l])) d11 d01 (by linear_combination hdet)
  have near : ∀ u' : Fin 2 → ℤ_[l], (l : ℤ_[l]) ^ n ∣ u' 0 - u 0 → (l : ℤ_[l]) ^ n ∣ u' 1 - q * u 1 →
      Rep X l n F ((4 : ℤ_[l]) • b u') := fun u' a0 a1 => by
    have := c1 u' ![u 0, (q : ℤ_[l]) * u 1] (Fin.forall_fin_two.2 ⟨a0, a1⟩)
    rw [map_sub, sub_eq_zero] at this
    unfold UpperTheory.Kd.K4.Rep at hR ⊢
    rw [map_smul, this, ← map_smul, hR]
  have one : Rep X l n 1 0 := by simpa using (r2 _ _ _ _ hR hR).2
  have A : ∀ s : Finset ℕ, Rep X l n (∏ j ∈ s, Units.map ((X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv : X.K →* X.K) F)
      (∑ j ∈ s, (4 : ℤ_[l]) • X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine (r2 _ _ _ _ ?_ ih).1
      have := r5 (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv _ _
        (near (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u)
          (dvd2 (x := j * u 1) (y := 0) dM dM (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
          (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]))
      rwa [map_smul] at this
  have Bq := r5 (X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv _ _
    (near (mZl l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) *ᵥ u)
      (dvd2 (x := u 0) (y := u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring))
      (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring)))
  have Cq := r5 (X.gal σ) _ _ hR
  set χ' : ℤ_[l] := (cyclotomicCharacter Ω l (σ⁻¹).toRingEquiv : ℤ_[l]) with hχ'
  have hχq : (q : ℤ_[l]) * χ' = 1 := by
    rw [← hχ, hχ', ← Units.val_mul, ← map_mul]
    have : σ.toRingEquiv * (σ⁻¹).toRingEquiv = 1 := by
      ext z; exact σ.apply_symm_apply z
    rw [this, map_one, Units.val_one]
  have D0 := near ((q : ℤ_[l]) • (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ' * u 1]))
    (dvd2 (x := u 0) (y := q * χ' * u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
    (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by
      simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℤ_[l]) * u 1 * hχq))
  rw [c2] at D0
  have D := r3 _ _ q (r5 (X.gal σ⁻¹) _ _ (r5 (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ D0))
  have fin := r4 _ _ _ _ (r2 _ _ _ _ (A (Finset.range q)) Bq).1 (r2 _ _ _ _ Cq D).1 ⟨g, Units.ext (by
    rw [(sSlD Ω ε X N hN).2.2.1 γ]
    have hg' : Nq X M q F * _ = X.gal σ F * (X.gal σ⁻¹ _) ^ q * _ := hg
    clear_value M
    simpa [Nq, Units.coe_prod] using hg')⟩
  have h4 : IsUnit (4 : ℤ_[l]) := by
    have : IsUnit ((4 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact ((Nat.coprime_primes hl.out Nat.prime_two).2 ho).pow_right 2
    simpa using this
  rw [← h4.smul_eq_zero, ← map_smul, ← fin, t1, t2]
  congr 1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_sub, smul_add, Finset.smul_sum, map_smul]
  congr 1
  change _ + (4 : ℤ_[l]) • (q : ℤ_[l]) ^ (w + 1) • X.kmap l (X.gal σ⁻¹) (X.kmap l _ (b _)) = _
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  · change (4 : ℤ_[l]) • X.kmap l (X.gal σ) (b _) = _
    rw [hχ]
  · congr 1
    ring

/- English proof (translation)
The claim follows from `es_of sEsLev sEsFrob sEsT @GlobalTheory.T.eichlerShimura_kummer_function_uniform_exceptional_primes`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sEs : UpperTheory.V.Z.Kato.Nb.SEs := es_of sEsLev sEsFrob sEsT @GlobalTheory.T.eichlerShimura_kummer_function_uniform_exceptional_primes
