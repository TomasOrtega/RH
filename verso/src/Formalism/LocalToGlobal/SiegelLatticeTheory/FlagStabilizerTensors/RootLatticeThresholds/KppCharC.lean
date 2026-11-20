import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharN

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Take `⟨c, hc, ht⟩` from `h`. Rewrite `hc` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨q, rfl⟩` from `hc`. Establish `: ((((p : ℤ) * q : ℤ)) : I.E ⊗[I.F] Af I.F) ∈ Wq I w`. Use `push_cast`.

Conclude with `Wq_mul' (natCast_Wq hp hcard) (intCast_mem _ q)`. Use `add_mem ht this` as an intermediate fact. Simplify using `using this`.
-/
theorem Wq_of_congW_zero {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} (h : CongW (w := w) p t 0) : t ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨q, rfl⟩ := hc
  have : ((((p : ℤ) * q : ℤ)) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_mem _ q)
  have := add_mem ht this
  simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty, Finset.prod_empty]`. Unfold `divN`. Rewrite using `[mul_zero]`.

Conclude with `X.psiEf_int 0 (zero_mem _)`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, divN_add, X.psiEf_add, ih]`.
-/
theorem psi_sum {ι : Type*} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.psiEf (divN X.B.I X.B.g (∑ i ∈ s, f i)) = ∏ i ∈ s, X.psiEf (divN X.B.I X.B.g (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, divN_add, X.psiEf_add, ih]

/- English proof (translation)
Use `⟨m, rfl, ?_⟩` and prove the remaining obligations. Use `iE_mem (I := I) h` as an intermediate fact. Simplify `this` using `[iE]`.
-/
theorem congW_iE {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} {a : 𝓞 I.E} {m : ℤ}
    (h : a - (m : 𝓞 I.E) ∈ w.asIdeal) : CongW (w := w) p (iE I a) (m : ZMod p) := by
  refine ⟨m, rfl, ?_⟩
  have := iE_mem (I := I) h
  simpa [iE] using this

variable (ε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), 𝓞 X.B.I.E)

/- English proof (translation)
Use `set T : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ kv, (iE X.B.I (ε kv) * (((t1 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) + iE X.B.I (sigO X.B.I (ε kv)) * (((t2 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) with hT`. Establish `hTint : T ∈ IntAf X.B.I.F X.B.I.E` using `sum_mem fun kv _ => add_mem (mul_mem (iE_int _ _) (natCast_mem _ _)) (mul_mem (iE_int _ _) (natCast_mem _ _))`. Establish `hgP : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal` using `fun kv => level_mem_wB' X kv`. Establish `hgPc : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal` using `fun kv => natCast_mem_wc X.B.I (level_mem_wB' X kv)`. Establish `hΔ : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → C - T ∈ Wq X.B.I P`.

Introduce `P hP`. Take `⟨kv0, hP0 | hP0⟩` from `over_g X P hP`. Substitute `hP0` using the available equality. Establish `hp` using `D.host.g_prime kv0.1`. Establish `: NeZero (D.host.g kv0.1)` using `⟨hp.ne_zero⟩`.

Establish `hTc : CongW (w` using `wK X kv0) (D.host.g kv0.1) T (t1 kv0) := by`. Establish `h3 : CongW (w` using `wK X kv0) (D.host.g kv0.1) T (∑ kv, ((if kv = kv0 then 1 else 0) * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) + 0 * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by`. Use `congW_sum _ fun kv _ => congW_add ?_ ?_` and prove the remaining obligations. Use `congW_mul (natCast_mem _ _) ?_ (congW_natCast _)` and prove the remaining obligations. Distinguish the cases in `hk : kv = kv0`.

Substitute `hk` using the available equality. Rewrite using `[if_pos rfl]`. Use `congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hε1 kv)` as an intermediate fact. Simplify using `using this`. Rewrite using `[if_neg hk]`.

Use `congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk)))` as an intermediate fact. Simplify using `using this`. Use `congW_mul (natCast_mem _ _) ?_ (congW_natCast _)` and prove the remaining obligations. Establish `hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal` using `hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm`. Rewrite `hm` using `[mem_wc]`.

Use `congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)` as an intermediate fact. Simplify using `using this`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `[Finset.sum_ite_eq']`. Use `congW_sub (h1 kv0) hTc` as an intermediate fact.

Rewrite `this` using `[sub_self]`. Conclude with `Wq_of_congW_zero hp (card_wK X kv0) this`. Substitute `hP0` using the available equality. Establish `hp` using `D.host.g_prime kv0.1`. Establish `: NeZero (D.host.g kv0.1)` using `⟨hp.ne_zero⟩`.

Establish `hTc : CongW (w` using `wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (t2 kv0) := by`. Establish `h3 : CongW (w` using `wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (∑ kv, (0 * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) + (if kv = kv0 then 1 else 0) * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by`. Use `congW_sum _ fun kv _ => congW_add ?_ ?_` and prove the remaining obligations. Use `congW_mul (natCast_mem _ _) ?_ (congW_natCast _)` and prove the remaining obligations. Establish `hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal` using `hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm`.

Use `congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)` as an intermediate fact. Simplify using `using this`. Use `congW_mul (natCast_mem _ _) ?_ (congW_natCast _)` and prove the remaining obligations. Distinguish the cases in `hk : kv = kv0`. Substitute `hk` using the available equality.

Rewrite using `[if_pos rfl]`. Establish `hm : sigO X.B.I (ε kv) - 1 ∈ (wc X.B.I (wK X kv)).asIdeal`. Rewrite using `[mem_wc, map_sub, sigO_sigO, map_one]`. Conclude with `hε1 kv`. Use `congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hm)` as an intermediate fact.

Simplify using `using this`. Rewrite using `[if_neg hk]`. Establish `hm : sigO X.B.I (ε kv) ∈ (wc X.B.I (wK X kv0)).asIdeal`. Rewrite using `[mem_wc, sigO_sigO]`. Conclude with `hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk))`.

Use `congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)` as an intermediate fact. Simplify using `using this`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `[Finset.sum_ite_eq']`. Use `congW_sub (h2 kv0) hTc` as an intermediate fact.

Rewrite `this` using `[sub_self]`. Conclude with `Wq_of_congW_zero hp (card_wKc X kv0) this`. Take `⟨a, r', hr', hr⟩` from `PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g (g_pos X) (C - T) (sub_mem hC hTint)`. Establish `ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal`. Introduce `P hP`.

Establish `hgW : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I P`. Use `iE_mem (I := X.B.I) hP` as an intermediate fact. Simplify `this` using `[iE]`. Establish `hiE : iE X.B.I a ∈ Wq X.B.I P`. Use `sub_mem (hΔ P hP) (Wq_mul' hgW hr')` as an intermediate fact.

Rewrite `this` using `[hr]`. Simplify `this` using `[iE]`. Take `⟨kv0, hP0 | hP0⟩` from `over_g X P hP`. Substitute `hP0` using the available equality. Conclude with `int_of_Wq (D.host.g_prime kv0.1) (card_wK X kv0) hn hiE`.

Substitute `hP0` using the available equality. Conclude with `int_of_Wq (D.host.g_prime kv0.1) (card_wKc X kv0) hn hiE`. Take `⟨c, hc⟩` from `mem_g_of_all X ha`. Establish `hCT : C = T + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r')`. Establish `: C - T = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r')`.

Rewrite using `[hr, hc]`. Simplify using `[iE]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hCT, psi_modg X _ (add_mem (iE_int _ c) hr'), hT, psi_sum]`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations. Rewrite using `[divN_add, X.psiEf_add, psi_sig, AddChar.map_add_eq_mul, psiK_apply, psiK_apply]`.
-/
theorem chi_split (hε1 : ∀ kv, ε kv - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ kv (P : HeightOneSpectrum (𝓞 X.B.I.E)), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv →
      ε kv ∈ P.asIdeal)
    (hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (hn : 0 < X.B.I.n) {C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hC : C ∈ IntAf X.B.I.F X.B.I.E)
    (t1 t2 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1))
    (h1 : ∀ kv, CongW (w := wK X kv) (D.host.g kv.1) C (t1 kv))
    (h2 : ∀ kv, CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) C (t2 kv)) :
    X.psiEf (divN X.B.I X.B.g C) = ∏ kv, psiK X (ε kv) (hε kv) (t1 kv + t2 kv) := by
  classical
  set T : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ kv, (iE X.B.I (ε kv) * (((t1 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
    iE X.B.I (sigO X.B.I (ε kv)) * (((t2 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) with hT
  have hTint : T ∈ IntAf X.B.I.F X.B.I.E :=
    sum_mem fun kv _ => add_mem (mul_mem (iE_int _ _) (natCast_mem _ _)) (mul_mem (iE_int _ _) (natCast_mem _ _))

  have hgP : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := fun kv => level_mem_wB' X kv
  have hgPc : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
    fun kv => natCast_mem_wc X.B.I (level_mem_wB' X kv)
  have hΔ : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → C - T ∈ Wq X.B.I P := by
    intro P hP
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wK X kv0) (D.host.g kv0.1) T (t1 kv0) := by
        have h3 : CongW (w := wK X kv0) (D.host.g kv0.1) T
            (∑ kv, ((if kv = kv0 then 1 else 0) * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              0 * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hε1 kv)
              simpa using this
            · rw [if_neg hk]
              have := congW_iE (p := D.host.g kv0.1) (m := 0)
                (by simpa using hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk)))
              simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            rw [mem_wc] at hm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h1 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wK X kv0) this
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (t2 kv0) := by
        have h3 : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T
            (∑ kv, (0 * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              (if kv = kv0 then 1 else 0) * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have hm : sigO X.B.I (ε kv) - 1 ∈ (wc X.B.I (wK X kv)).asIdeal := by
                rw [mem_wc, map_sub, sigO_sigO, map_one]; exact hε1 kv
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hm)
              simpa using this
            · rw [if_neg hk]
              have hm : sigO X.B.I (ε kv) ∈ (wc X.B.I (wK X kv0)).asIdeal := by
                rw [mem_wc, sigO_sigO]; exact hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk))
              have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
              simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h2 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wKc X kv0) this

  obtain ⟨a, r', hr', hr⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g (g_pos X) (C - T) (sub_mem hC hTint)
  have ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal := by
    intro P hP
    have hgW : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I P := by
      have := iE_mem (I := X.B.I) hP; simpa [iE] using this
    have hiE : iE X.B.I a ∈ Wq X.B.I P := by
      have := sub_mem (hΔ P hP) (Wq_mul' hgW hr')
      rw [hr] at this
      simpa [iE] using this
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wK X kv0) hn hiE
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wKc X kv0) hn hiE
  obtain ⟨c, hc⟩ := mem_g_of_all X ha
  have hCT : C = T + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
    have : C - T = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
      rw [hr, hc]; simp [iE]; ring
    rw [← this]; ring
  rw [hCT, psi_modg X _ (add_mem (iE_int _ c) hr'), hT, psi_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [divN_add, X.psiEf_add, psi_sig, AddChar.map_add_eq_mul, psiK_apply, psiK_apply]

end Formalism.L2.SG.Pf.KppChar
