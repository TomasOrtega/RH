import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.ProjectionKernelEqFunctional
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TNotinSq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun h i`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_natCast] at hi`. Conclude with `mul_left_cancel₀ hN hi`.
-/
theorem natS_cancel (N : ℕ) (hN : (N : E) ≠ 0) (a b : Fin n → E)
    (h : ((N : ℕ) : 𝓞 E) • a = ((N : ℕ) : 𝓞 E) • b) : a = b := by
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def, map_natCast] at hi
  exact mul_left_cancel₀ hN hi

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def, hN]`.
-/
theorem natS_inv (N : ℕ) (hN : (N : E) ≠ 0) (w : Fin n → E) : ((N : ℕ) : 𝓞 E) • ((N : E)⁻¹ • w) = w := by
  funext i
  simp [Algebra.smul_def, hN]

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun q => ∃ d' ∈ N, σ • q = τ • d') hq (fun p hp n hn => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Take `⟨e, he⟩` from `hσT p hp`. Conclude with `⟨e • n, N.smul_mem e hn, by rw [smul_smul, he, mul_comm e τ, mul_smul]⟩`. Take `⟨d1, h1, e1⟩` from `hx`. Take `⟨d2, h2, e2⟩` from `hy`.

Conclude with `⟨d1 + d2, N.add_mem h1 h2, by rw [smul_add, e1, e2, smul_add]⟩`.
-/
theorem smul_T_of (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) (σ τ : 𝓞 E)
    (hσT : ∀ p ∈ P, ∃ e : 𝓞 E, σ * p = e * τ) (q : Fin n → E) (hq : q ∈ P • N) :
    ∃ d' ∈ N, σ • q = τ • d' := by
  refine Submodule.smul_induction_on (p := fun q => ∃ d' ∈ N, σ • q = τ • d') hq
    (fun p hp n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨e, he⟩ := hσT p hp
    exact ⟨e • n, N.smul_mem e hn, by rw [smul_smul, he, mul_comm e τ, mul_smul]⟩
  · obtain ⟨d1, h1, e1⟩ := hx
    obtain ⟨d2, h2, e2⟩ := hy
    exact ⟨d1 + d2, N.add_mem h1 h2, by rw [smul_add, e1, e2, smul_add]⟩

end Gen

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `v c w1 w3 s1 s3 hz1 hz3 hs1 hs3 y hy1 hy3`. Establish `hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast (D.mem u).A.T_prime.ne_zero`. Establish `hdm : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ Lk T.atT 0 (Nat.zero_le _) v c` using `sub_mem (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz3)`. Establish `hd0 : T.lv0.prk v c ⟨_, hdm⟩ = 0`. Establish `e0 : (⟨_, hdm⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = s3 • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - s1 • (⟨_, hz3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c))` using `Subtype.ext rfl`.

Rewrite using `[e0, map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy1, hy3, smul_smul, smul_smul, mul_comm, sub_self]`. Establish `hdP : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c` using `(T.lv0.prk_ker v c _).1 hd0`. Take `⟨σ, hσ, hσT⟩` from `exists_not_mem_Pv_mul_mem_span_T T v c`. Take `⟨d', hd'L, hd'⟩` from `smul_T_of _ _ σ _ hσT _ hdP`. Establish `hW : (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) = d' + (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3)`.

Rewrite using `[← sub_eq_iff_eq_add]`. Apply `natS_cancel _ hTne` to reduce the goal to its premises. Rewrite using `[← hd', smul_sub, smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3), smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3), natS_inv _ hTne, natS_inv _ hTne, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, mul_right_comm σ s3 s1]`. Establish `hd'loc` using `CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hd'L)`. Take `⟨t', ht', ht'd⟩` from `(rlv_mem_locP _ _ _).1 hd'loc`.

Introduce `x hx`. Take `⟨t, ht, htx⟩` from `(rlv_mem_locP _ _ _).1 hx`. Take `⟨l, hl, m, hm, em⟩` from `Submodule.mem_sup.1 htx`. Take `⟨e, rfl⟩` from `Submodule.mem_span_singleton.1 hm`. Establish `hP : (T.atT.Pv v).IsPrime` using `inferInstance`.

Use `(rlv_mem_locP _ _ _).2 ⟨t' * (σ * s1 * s3) * t, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Break down `hP.mem_or_mem h with h | h` into its components or cases. Break down `hP.mem_or_mem h with h | h` into its components or cases. Conclude with `ht' h`.

Break down `hP.mem_or_mem h with h | h` into its components or cases. Break down `hP.mem_or_mem h with h | h` into its components or cases. Conclude with `hσ h`. Conclude with `hs1 h`. Conclude with `hs3 h`.

Conclude with `ht h`. Rewrite using `[mul_smul, ← em, smul_add]`. Use `add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)) ?_` and prove the remaining obligations. Rewrite using `[smul_comm (t' * (σ * s1 * s3)) e, mul_smul t' (σ * s1 * s3), hW, smul_add, smul_add]`. Conclude with `add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ ht'd)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))))`.
-/
theorem ptLat_holds (T : Forms0 D u) : PtLatF T := by
  intro v c w1 w3 s1 s3 hz1 hz3 hs1 hs3 y hy1 hy3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hdm : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    sub_mem (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz3)
  have hd0 : T.lv0.prk v c ⟨_, hdm⟩ = 0 := by
    have e0 : (⟨_, hdm⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) =
        s3 • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - s1 • (⟨_, hz3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :=
      Subtype.ext rfl
    rw [e0, map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy1, hy3, smul_smul, smul_smul, mul_comm, sub_self]
  have hdP : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    (T.lv0.prk_ker v c _).1 hd0
  obtain ⟨σ, hσ, hσT⟩ := exists_not_mem_Pv_mul_mem_span_T T v c
  obtain ⟨d', hd'L, hd'⟩ := smul_T_of _ _ σ _ hσT _ hdP
  have hW : (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) =
      d' + (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3) := by
    rw [← sub_eq_iff_eq_add]
    apply natS_cancel _ hTne
    rw [← hd', smul_sub, smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3),
      smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3), natS_inv _ hTne, natS_inv _ hTne, smul_sub,
      smul_smul, smul_smul, smul_smul, smul_smul, mul_right_comm σ s3 s1]
  have hd'loc := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hd'L)
  obtain ⟨t', ht', ht'd⟩ := (rlv_mem_locP _ _ _).1 hd'loc
  intro x hx
  obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨l, hl, m, hm, em⟩ := Submodule.mem_sup.1 htx
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hP : (T.atT.Pv v).IsPrime := inferInstance
  refine (rlv_mem_locP _ _ _).2 ⟨t' * (σ * s1 * s3) * t, ?_, ?_⟩
  · intro h
    rcases hP.mem_or_mem h with h | h
    · rcases hP.mem_or_mem h with h | h
      · exact ht' h
      · rcases hP.mem_or_mem h with h | h
        · rcases hP.mem_or_mem h with h | h
          · exact hσ h
          · exact hs1 h
        · exact hs3 h
    · exact ht h
  · rw [mul_smul, ← em, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)) ?_
    rw [smul_comm (t' * (σ * s1 * s3)) e, mul_smul t' (σ * s1 * s3), hW, smul_add, smul_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ ht'd))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))))

/- English proof (translation)
The claim follows from `valDia_of_lat T (ptLat_holds T)`.
-/
theorem valDia_holds (T : Forms0 D u) : ValDia T :=
  valDia_of_lat T (ptLat_holds T)

/- English proof (translation)
The claim follows from `dUAll_of_vals fun D u T => ⟨(h D u T).1, (h D u T).2, valDia_holds T⟩`.
-/
theorem dUAll_of_same_te (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  dUAll_of_vals fun D u T => ⟨(h D u T).1, (h D u T).2, valDia_holds T⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
