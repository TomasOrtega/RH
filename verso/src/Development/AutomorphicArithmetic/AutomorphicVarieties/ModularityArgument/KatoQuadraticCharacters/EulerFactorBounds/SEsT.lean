import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeActionStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb`. Establish `hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b`. Unfold `Tower.BSet at hb`. Conclude with `hb.2`. Establish `hN0 : N ≠ 0` using `by omega`.

Establish `hl0 : l ≠ 0` using `(Fact.out : Nat.Prime l).ne_zero`. Establish `hqN : q.Coprime N` using `(Nat.coprime_mul_iff_right.mp hqlN).2`. Establish `hSD` using `Betti.isDiam_sgD (l := l) hN0 hl0 hqN`. Unfold `IsDiam at hSD`. Take `⟨hSmem, hSq⟩` from `hSD`.

Take `⟨hS0N, hS0l⟩` from `Subgroup.mem_inf.mp hSmem`. Rewrite `hS0N`, `hS0l` using `[CongruenceSubgroup.Gamma0_mem]`. Unfold `en at hSq`. Unfold `DiagMod at hγ`. Take `⟨-, hγc, hγd⟩` from `hγ`.

Unfold `en at hγc hγd`. Establish `hNM : N ∣ M` using `(dvd_mul_left N l).trans hM`. Establish `hlM : l ∣ M` using `(dvd_mul_right l N).trans hM`. Establish `hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0`. Simplify using `using congrArg (ZMod.castHom hNM (ZMod N)) hγc`.

Establish `hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0`. Simplify using `using congrArg (ZMod.castHom hlM (ZMod l)) hγc`. Establish `hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q`. Simplify using `using congrArg (ZMod.castHom hNM (ZMod N)) hγd`. Establish `hδ : sgD N l q * γ⁻¹ ∈ Gam N l`.

Establish `hS` using `congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))`. Establish `hG` using `congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)`. Rewrite `hS`, `hG` using `[Matrix.det_fin_two]`. Move the coercions through the operations in `at hS hG`. Unfold `Gam`.

Rewrite using `[Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using the standard rewrite rules. Use `push_cast`. Generalize the expression as in `(sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *`.

Generalize the expression as in `(γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Take the linear combination `(↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN`. Take the linear combination `(↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N`. Take the linear combination `(↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN`.

Take the linear combination `(↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl`. Establish `hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b` using `by conv_lhs => rw [← hb' _ hδ]`. Rewrite using `[Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]`. Establish `hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1]`. Simplify `hq.pos` using `[Matrix.det_fin_two]`.

Use `⟨?_, fun s => ?_⟩` and prove the remaining obligations. Unfold `Tower.heckeT`. Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply]`. Use `congr 1`. Use `symm`.

Establish `hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a'`. Introduce `a ha a' ha' h`. Rewrite `ha`, `ha'` using `[Finset.mem_range]`. Establish `h' : a ≡ a' [MOD q]` using `Nat.ModEq.cancel_right_of_coprime hqM h`. Unfold `Nat.ModEq at h'`.

Rewrite `h'` using `[Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha']`. Then use the resulting hypothesis. Use `Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_` and prove the remaining obligations. Introduce `k hk`. Take `⟨a, ha, h⟩` from `Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h) le_rfl k (Finset.mem_coe.mp hk)`. Conclude with `⟨a, Finset.mem_coe.mpr ha, h.symm⟩`.

Introduce `a _`. Establish `hdm` using `Nat.mod_add_div (a * M) q`. Generalize the expression as in `a * M % q = r at hdm ⊢`. Generalize the expression as in `a * M / q = t at hdm`. Set `T : SL(2, ℤ)` to `⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩`.

Establish `hT : T ∈ Gam N l`. Unfold `Gam`. Rewrite using `[Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]`. Simplify using `[T]`. Establish `hz : (a : ℤ) * M = r + q * t` using `by exact_mod_cast hdm.symm`.

Establish `hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz`. Rewrite using `[hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]`. Rewrite using `[← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]`.

Unfold `Tower.diam`. Rewrite using `[GlobalTheory.T.galois_commutes_hecke_action ε X N l w hN b hb _ hSmem s, hAct]`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sEsT : UpperTheory.V.Z.Kato.Nb.SEsT := by
  intro Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb
  have hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b := by
    unfold Tower.BSet at hb
    exact hb.2
  have hN0 : N ≠ 0 := by omega
  have hl0 : l ≠ 0 := (Fact.out : Nat.Prime l).ne_zero
  have hqN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hqlN).2
  have hSD := Betti.isDiam_sgD (l := l) hN0 hl0 hqN
  unfold IsDiam at hSD
  obtain ⟨hSmem, hSq⟩ := hSD
  obtain ⟨hS0N, hS0l⟩ := Subgroup.mem_inf.mp hSmem
  rw [CongruenceSubgroup.Gamma0_mem] at hS0N hS0l
  unfold en at hSq
  unfold DiagMod at hγ
  obtain ⟨-, hγc, hγd⟩ := hγ
  unfold en at hγc hγd
  have hNM : N ∣ M := (dvd_mul_left N l).trans hM
  have hlM : l ∣ M := (dvd_mul_right l N).trans hM
  have hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγc
  have hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom hlM (ZMod l)) hγc
  have hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγd
  have hδ : sgD N l q * γ⁻¹ ∈ Gam N l := by
    have hS := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))
    have hG := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)
    rw [Matrix.det_fin_two] at hS hG
    push_cast at hS hG
    unfold Gam
    rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    push_cast
    generalize (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *
    generalize (γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linear_combination (↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS
        + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN
    · linear_combination (↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG
        + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N
    · linear_combination (↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN
    · linear_combination (↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl
  have hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b := by
    conv_lhs => rw [← hb' _ hδ]
    rw [Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  have hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1] := by
    simpa [Matrix.det_fin_two] using hq.pos
  refine ⟨?_, fun s => ?_⟩
  · unfold Tower.heckeT
    simp only [LinearMap.add_apply, LinearMap.sum_apply]
    congr 1
    · symm
      have hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a' := by
        intro a ha a' ha' h
        rw [Finset.mem_range] at ha ha'
        have h' : a ≡ a' [MOD q] := Nat.ModEq.cancel_right_of_coprime hqM h
        unfold Nat.ModEq at h'
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      refine Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
        (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_
      · intro k hk
        obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q)
          (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h)
          le_rfl k (Finset.mem_coe.mp hk)
        exact ⟨a, Finset.mem_coe.mpr ha, h.symm⟩
      · intro a _
        have hdm := Nat.mod_add_div (a * M) q
        generalize a * M % q = r at hdm ⊢
        generalize a * M / q = t at hdm
        let T : SL(2, ℤ) := ⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
        have hT : T ∈ Gam N l := by
          unfold Gam
          rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
          simp [T]
        have hz : (a : ℤ) * M = r + q * t := by exact_mod_cast hdm.symm
        have hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz
        rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
          (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]
    · rw [← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq,
        ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]
  · unfold Tower.diam
    rw [GlobalTheory.T.galois_commutes_hecke_action ε X N l w hN b hb _ hSmem s, hAct]
