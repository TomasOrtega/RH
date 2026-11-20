import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClassStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescentStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

/- English proof (translation)
Unfold `SEsLev`. Introduce `Ω _ _ _ ε X l _ N w hN b hb n`. Establish `hl : Nat.Prime l` using `Fact.out`. Take `⟨⟨c, hcA, hbu⟩, hinv⟩` from `hb`. Establish `api` using `sApi Ω ε X l n`.

Establish `cls` using `sCls Ω ε X l n`. Establish `ev` using `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n`. Establish `hsub : ∀ (x y x' y' : ℤ_[l]) (a e : ℕ), (l : ℤ_[l]) ^ n ∣ x - x' → (l : ℤ_[l]) ^ n ∣ y - y' → (l : ℤ_[l]) ^ n ∣ x ^ a * y ^ e - x' ^ a * y' ^ e`. Introduce `x y x' y' a e hx hy`. Establish `h : x ^ a * y ^ e - x' ^ a * y' ^ e = (x ^ a - x' ^ a) * y ^ e + x' ^ a * (y ^ e - y' ^ e)` using `by ring`.

Rewrite using `[h]`. Conclude with `dvd_add (dvd_mul_of_dvd_left (hx.trans (sub_dvd_pow_sub_pow x x' a)) _) (dvd_mul_of_dvd_right (hy.trans (sub_dvd_pow_sub_pow y y' e)) _)`. Establish `cong : ∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) → (AdicCompletion.eval (idl l) (X.Kl l) n) (b u - b u') = 0`. Introduce `u u' h`. Rewrite using `[hbu u, hbu u', ← Finset.sum_sub_distrib, map_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Conclude with `api.2.2.2.2.1 _ _ _ (hsub _ _ _ _ _ _ (h 0) (h 1))`. Use `⟨cong, ?_, ?_⟩` and prove the remaining obligations. Introduce `t u`. Rewrite using `[hbu, hbu, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Establish `hi : (i : ℕ) + (w - i) = w` using `Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow]`.

Rewrite using `[show t ^ w = t ^ (i : ℕ) * t ^ (w - i) by rw [← pow_add, hi]]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u`. Establish `hbA : b u ∈ X.A l`. Rewrite using `[hbu]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcA i)`. Take `⟨φ0, hφ, hd⟩` from `X.j_hol`. Take `⟨f, hfU, hf⟩` from `GlobalTheory.T.exists_unit_eval_eq_kummer_class ε X ⟨φ0, hd, hφ⟩ l n (b u) hbA`. Take `⟨M, hM⟩ : ∃ M : ℕ, M = 6 * l * N * l ^ n` from `⟨_, rfl⟩`. Establish `hMpos : 0 < M`.

Rewrite using `[hM]`. Conclude with `Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hl.pos) hN) (pow_pos hl.pos n)`. Establish `hMd : 6 * l ∣ M` using `⟨N * l ^ n, by rw [hM]; ring⟩`. Establish `hNM : (N : ℤ) ∣ (M : ℤ)` using `⟨6 * l * l ^ n, by rw [hM]; push_cast; ring⟩`. Establish `hlM : (l : ℤ) ∣ (M : ℤ)` using `⟨6 * N * l ^ n, by rw [hM]; push_cast; ring⟩`.

Establish `hlnM : (l : ℤ) ^ n ∣ (M : ℤ)` using `⟨6 * l * N, by rw [hM]; push_cast; ring⟩`. Establish `key : ∀ (d : ℕ) (x y : ℤ), (d : ℤ) ∣ y - x → ((x : ZMod d) = (y : ZMod d))` using `fun d x y h => (ZMod.intCast_eq_intCast_iff_dvd_sub x y d).mpr h`. Establish `hdl : ∀ x : ℤ, (M : ℤ) ∣ x → (l : ℤ_[l]) ^ n ∣ (x : ℤ_[l])`. Introduce `x hx`. Take `⟨e, he⟩` from `hlnM.trans hx`.

Conclude with `⟨(e : ℤ_[l]), by rw [he]; push_cast; ring⟩`. Establish `hγ : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, (X.sl (ofSL γ)) (f : X.K) = (f : X.K) * (g : X.K) ^ l ^ n`. Introduce `γ hγM`. Rewrite `hγM` using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h00, h01, h10, h11⟩` from `hγM`.

Establish `d00 : (M : ℤ) ∣ 1 - γ 0 0` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h00)`. Establish `d01 : (M : ℤ) ∣ 0 - γ 0 1` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h01)`. Establish `d10 : (M : ℤ) ∣ 0 - γ 1 0` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h10)`. Establish `d11 : (M : ℤ) ∣ 1 - γ 1 1` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h11)`. Establish `hG : γ ∈ Gam N l` using `by show γ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l`.

Use `Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩, CongruenceSubgroup.Gamma0_mem.mpr ?_⟩` and prove the remaining obligations. Simplify using `using key N _ _ (hNM.trans d00)`. Simplify using `using key N _ _ (hNM.trans d11)`. Simplify using `using key N _ _ (hNM.trans d10)`. Simplify using `using key l _ _ (hlM.trans d10)`.

Establish `hact` using `congrFun (hinv γ hG) u`. Simplify using `only [GlobalTheory.KZ.Tower.act, LinearMap.coe_mk, AddHom.coe_mk] at hact`. Rewrite `hact` using `[Betti.toGQ_sl]`. Establish `hcu : ∀ i, (l : ℤ_[l]) ^ n ∣ (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) i - u i`. Use `Fin.forall_fin_two.mpr ⟨?_, ?_⟩` and prove the remaining obligations.

Establish `e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0 = ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1`. Simplify using `[mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d00)) _) (dvd_mul_of_dvd_left (hdl _ (by simpa using d01)) _)`.

Establish `e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 - u 1 = ((γ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((γ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1`. Simplify using `[mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left (hdl _ (by simpa using d10)) _) (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d11)) _)`.

Establish `heq : (AdicCompletion.eval (idl l) (X.Kl l) n) (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = X.cls l n f`. Rewrite using `[← hf, ← sub_eq_zero, ← map_sub]`. Conclude with `cong _ u hcu`. Establish `h2` using `KmapA.eval_kmap X l (X.sl (ofSL γ)).toRingEquiv n _ f heq`. Rewrite `h2` using `[hact, hf]`.

Take `⟨g, hg⟩` from `(ev.2.1 _ _).mp h2.symm`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val hg` as an intermediate fact. Simplify using `using this`. Take `⟨k', h, hlev⟩` from `GlobalTheory.T.exists_level_pow_prime_fourth_power_descent ε X l n M hl hMpos hMd f hγ`.

Use `⟨n + k', f ^ 4 * h ^ l ^ n, Nat.le_add_right _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `W hW`. Take `⟨g, hg⟩` from `hfU W hW`. Use `⟨g ^ 4 * h, ?_⟩` and prove the remaining obligations. Establish `hg0 : (g : X.K) ≠ 0` using `g.ne_zero`.

Establish `hh0 : (h : X.K) ≠ 0` using `h.ne_zero`. Establish `e : ((f ^ 4 * h ^ l ^ n : X.Kˣ) : X.K) / ((g ^ 4 * h : X.Kˣ) : X.K) ^ l ^ n = ((f : X.K) / (g : X.K) ^ l ^ n) ^ 4`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, map_pow, hg, one_pow]`. Establish `e : M * l ^ k' = 6 * l * N * l ^ (n + k')` using `by rw [hM, pow_add]; ring`. Rewrite using `[← e]`. Use `push_cast`. Conclude with `hlev`.

Establish `r1 : UpperTheory.Kd.K4.Rep X l n f (b u)` using `hf`. Establish `r2` using `cls.2.2.1 f (b u) 4 r1`. Establish `r3 : UpperTheory.Kd.K4.Rep X l n (h ^ l ^ n) 0` using `by show _ = _`. Rewrite using `[map_zero]`. Establish `h3` using `(ev.2.1 (h ^ l ^ n) 1).mpr ⟨h, by simp⟩`.

Rewrite using `[h3, ev.2.2.2.1]`. Establish `h4` using `(cls.2.1 _ _ _ _ r2 r3).1`. Simplify using `using h4`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sEsLev : UpperTheory.V.Z.Kato.Nb.SEsLev := by
  unfold SEsLev
  intro Ω _ _ _ ε X l _ N w hN b hb n
  have hl : Nat.Prime l := Fact.out
  obtain ⟨⟨c, hcA, hbu⟩, hinv⟩ := hb
  have api := sApi Ω ε X l n
  have cls := sCls Ω ε X l n
  have ev := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  have hsub : ∀ (x y x' y' : ℤ_[l]) (a e : ℕ), (l : ℤ_[l]) ^ n ∣ x - x' → (l : ℤ_[l]) ^ n ∣ y - y' →
      (l : ℤ_[l]) ^ n ∣ x ^ a * y ^ e - x' ^ a * y' ^ e := by
    intro x y x' y' a e hx hy
    have h : x ^ a * y ^ e - x' ^ a * y' ^ e = (x ^ a - x' ^ a) * y ^ e + x' ^ a * (y ^ e - y' ^ e) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left (hx.trans (sub_dvd_pow_sub_pow x x' a)) _)
      (dvd_mul_of_dvd_right (hy.trans (sub_dvd_pow_sub_pow y y' e)) _)
  have cong : ∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      (AdicCompletion.eval (idl l) (X.Kl l) n) (b u - b u') = 0 := by
    intro u u' h
    rw [hbu u, hbu u', ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact api.2.2.2.2.1 _ _ _ (hsub _ _ _ _ _ _ (h 0) (h 1))
  refine ⟨cong, ?_, ?_⟩
  · intro t u
    rw [hbu, hbu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [show t ^ w = t ^ (i : ℕ) * t ^ (w - i) by rw [← pow_add, hi]]
    ring
  · intro u
    have hbA : b u ∈ X.A l := by
      rw [hbu]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcA i)
    obtain ⟨φ0, hφ, hd⟩ := X.j_hol
    obtain ⟨f, hfU, hf⟩ := GlobalTheory.T.exists_unit_eval_eq_kummer_class ε X ⟨φ0, hd, hφ⟩ l n (b u) hbA
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 6 * l * N * l ^ n := ⟨_, rfl⟩
    have hMpos : 0 < M := by
      rw [hM]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hl.pos) hN) (pow_pos hl.pos n)
    have hMd : 6 * l ∣ M := ⟨N * l ^ n, by rw [hM]; ring⟩
    have hNM : (N : ℤ) ∣ (M : ℤ) := ⟨6 * l * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlM : (l : ℤ) ∣ (M : ℤ) := ⟨6 * N * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlnM : (l : ℤ) ^ n ∣ (M : ℤ) := ⟨6 * l * N, by rw [hM]; push_cast; ring⟩
    have key : ∀ (d : ℕ) (x y : ℤ), (d : ℤ) ∣ y - x → ((x : ZMod d) = (y : ZMod d)) :=
      fun d x y h => (ZMod.intCast_eq_intCast_iff_dvd_sub x y d).mpr h
    have hdl : ∀ x : ℤ, (M : ℤ) ∣ x → (l : ℤ_[l]) ^ n ∣ (x : ℤ_[l]) := by
      intro x hx
      obtain ⟨e, he⟩ := hlnM.trans hx
      exact ⟨(e : ℤ_[l]), by rw [he]; push_cast; ring⟩
    have hγ : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
        (X.sl (ofSL γ)) (f : X.K) = (f : X.K) * (g : X.K) ^ l ^ n := by
      intro γ hγM
      rw [CongruenceSubgroup.Gamma_mem] at hγM
      obtain ⟨h00, h01, h10, h11⟩ := hγM
      have d00 : (M : ℤ) ∣ 1 - γ 0 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h00)
      have d01 : (M : ℤ) ∣ 0 - γ 0 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h01)
      have d10 : (M : ℤ) ∣ 0 - γ 1 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h10)
      have d11 : (M : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h11)
      have hG : γ ∈ Gam N l := by
        show γ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
        refine Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩,
          CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
        · simpa using key N _ _ (hNM.trans d00)
        · simpa using key N _ _ (hNM.trans d11)
        · simpa using key N _ _ (hNM.trans d10)
        · simpa using key l _ _ (hlM.trans d10)
      have hact := congrFun (hinv γ hG) u
      simp only [GlobalTheory.KZ.Tower.act, LinearMap.coe_mk, AddHom.coe_mk] at hact
      rw [Betti.toGQ_sl] at hact
      have hcu : ∀ i, (l : ℤ_[l]) ^ n ∣ (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) i - u i := by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0
              = ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d00)) _)
            (dvd_mul_of_dvd_left (hdl _ (by simpa using d01)) _)
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 - u 1
              = ((γ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((γ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (by simpa using d10)) _)
            (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d11)) _)
      have heq : (AdicCompletion.eval (idl l) (X.Kl l) n) (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
          = X.cls l n f := by
        rw [← hf, ← sub_eq_zero, ← map_sub]
        exact cong _ u hcu
      have h2 := KmapA.eval_kmap X l (X.sl (ofSL γ)).toRingEquiv n _ f heq
      rw [hact, hf] at h2
      obtain ⟨g, hg⟩ := (ev.2.1 _ _).mp h2.symm
      refine ⟨g, ?_⟩
      have := congrArg Units.val hg
      simpa using this
    obtain ⟨k', h, hlev⟩ := GlobalTheory.T.exists_level_pow_prime_fourth_power_descent ε X l n M hl hMpos hMd f hγ
    refine ⟨n + k', f ^ 4 * h ^ l ^ n, Nat.le_add_right _ _, ?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨g, hg⟩ := hfU W hW
      refine ⟨g ^ 4 * h, ?_⟩
      have hg0 : (g : X.K) ≠ 0 := g.ne_zero
      have hh0 : (h : X.K) ≠ 0 := h.ne_zero
      have e : ((f ^ 4 * h ^ l ^ n : X.Kˣ) : X.K) / ((g ^ 4 * h : X.Kˣ) : X.K) ^ l ^ n
          = ((f : X.K) / (g : X.K) ^ l ^ n) ^ 4 := by
        push_cast
        field_simp
        ring
      rw [e, map_pow, hg, one_pow]
    · have e : M * l ^ k' = 6 * l * N * l ^ (n + k') := by rw [hM, pow_add]; ring
      rw [← e]
      push_cast
      exact hlev
    · have r1 : UpperTheory.Kd.K4.Rep X l n f (b u) := hf
      have r2 := cls.2.2.1 f (b u) 4 r1
      have r3 : UpperTheory.Kd.K4.Rep X l n (h ^ l ^ n) 0 := by
        show _ = _
        rw [map_zero]
        have h3 := (ev.2.1 (h ^ l ^ n) 1).mpr ⟨h, by simp⟩
        rw [h3, ev.2.2.2.1]
      have h4 := (cls.2.1 _ _ _ _ r2 r3).1
      simpa using h4
