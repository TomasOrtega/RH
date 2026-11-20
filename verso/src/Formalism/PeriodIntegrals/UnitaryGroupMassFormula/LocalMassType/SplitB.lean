import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SplitA

noncomputable section

namespace PI.LocMassTypS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v hStd _ hEta`. Establish `hCM` using `hStd.1`. Establish `h2` using `finrank_tens (E := E) v hCM.2.2.1`. Use `finDim_tens (E := E) v` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨e, he, h0, h1⟩ : ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by`.

Unfold `etaV at hEta`. Use `split_ifs at hEta with h`. Conclude with `h`. Apply the tactic sequence `all_goals norm_num at hEta`. Use `set π₁ := p1 h2 he h0 h1 with hπ₁`.

Use `set π₂ := p2 h2 he h0 h1 with hπ₂`. Establish `hm1 : ∀ x, x * e = π₁ x • e` using `mul_e h2 he h0 h1`. Establish `hm2 : ∀ x, x * (1 - e) = π₂ x • (1 - e)` using `mul_ce h2 he h0 h1`. Establish `hdec : ∀ x, x = π₁ x • e + π₂ x • (1 - e)` using `decomp h2 he h0 h1`. Establish `hσσ` using `sigma_invol σ hCM`.

Use `set f := sigR (Fv F v) σ e with hf`. Establish `hff : f * f = f` using `by rw [hf, ← map_mul, he]`. Establish `hfe : f = 1 - e`. Establish `c1` using `idem_cases (show π₁ f * π₁ f = π₁ f by rw [← map_mul, hff])`. Establish `c2` using `idem_cases (show π₂ f * π₂ f = π₂ f by rw [← map_mul, hff])`.

Establish `hfd` using `hdec f`. Apply the tactic sequence `rcases c1 with a | a <;> rcases c2 with b | b <;> rw [a, b] at hfd`. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises. Rewrite using `[← sigR_sigR σ v hσσ e, ← hf, hfd]`.

Simplify using the standard rewrite rules. Simplify using `using hfd`. It suffices to derive a contradiction. Take `⟨y, hy⟩` from `sigma_ne_id σ hCM`. Establish `hfe : f = e` using `by simpa using hfd`.

Establish `hid : ∀ x, sigR (Fv F v) σ x = x`. Introduce `x`. Use `conv_lhs => rw [hdec x]`. Rewrite using `[map_add, sigR_smul, sigR_smul, map_sub, map_one, ← hf, hfe]`. Conclude with `(hdec x).symm`.

Apply `hy` to reduce the goal to its premises. Apply `inclR_injective (E := E) v` to reduce the goal to its premises. Rewrite using `[← sigR_inclR, hid]`. It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises.

Rewrite using `[← sigR_sigR σ v hσσ e, ← hf, hfd]`. Simplify using the standard rewrite rules. Establish `hσe : sigR (Fv F v) σ e = 1 - e` using `hfe`. Establish `hσ1 : sigR (Fv F v) σ (1 - e) = e`. Rewrite using `[map_sub, map_one, hσe, sub_sub_cancel]`.

Establish `hp2σ : ∀ x, π₂ (sigR (Fv F v) σ x) = π₁ x`. Introduce `x`. Apply `uniq2 h1 (K := Fv F v)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hp1σ : ∀ x, π₁ (sigR (Fv F v) σ x) = π₂ x`.

Introduce `x`. Apply `uniq1 h0 (K := Fv F v)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hsc : ∀ c : Fv F v, π₁ (sc (E` using `E) v c) = c ∧ π₂ (sc (E := E) v c) = c := by`. Introduce `c`.

Use `⟨uniq1 h0 (K := Fv F v) ?_, uniq2 h1 (K := Fv F v) ?_⟩` and prove the remaining obligations. Rewrite using `[← hm1, PI.LocMassTypU.sc_mul_eq_smul]`. Rewrite using `[← hm2, PI.LocMassTypU.sc_mul_eq_smul]`. Establish `he1 : π₁ e = 1` using `uniq1 h0 (K := Fv F v) (by rw [← hm1, he, one_smul])`. Establish `he2 : π₂ e = 0` using `uniq2 h1 (K := Fv F v) (by rw [← hm2, idem_mul_compl he, zero_smul])`.

Establish `hce1 : π₁ (1 - e) = 0` using `by rw [map_sub, map_one, he1, sub_self]`. Establish `hce2 : π₂ (1 - e) = 1` using `by rw [map_sub, map_one, he2, sub_zero]`. Set `φ : (Fv F v ⊗[F] E) →+* Fv F v × Fv F v` to `RingHom.prod π₁ π₂`. Establish `hbij : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion.

Introduce `x y hxy`. Establish `h1' : π₁ x = π₁ y` using `congrArg Prod.fst hxy`. Establish `h2' : π₂ x = π₂ y` using `congrArg Prod.snd hxy`. Rewrite using `[hdec x, hdec y, h1', h2']`. Introduce and unpack `⟨a, b⟩`.

Use `⟨sc (E := E) v a * e + sc (E := E) v b * (1 - e), ?_⟩` and prove the remaining obligations. Use `show (π₁ _, π₂ _) = (a, b)`. Rewrite using `[map_add, map_add, map_mul, map_mul, map_mul, map_mul, (hsc a).1, (hsc b).1, (hsc a).2, (hsc b).2, he1, he2, hce1, hce2]`. Simplify using the standard rewrite rules. Set `spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v` to `(cm (E := E) v).toRingEquiv.trans (RingEquiv.ofBijective φ hbij)`.

Establish `hspl_apply : ∀ y, spl y = (π₁ (cm (E` using `E) v y), π₂ (cm (E := E) v y)) := fun _ => rfl`. Establish `hspl : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)`. Introduce `a`. Rewrite using `[hspl_apply]`. Establish `e1 : cm (E` using `E) v ((1 : E) ⊗ₜ[F] a) = sc (E := E) v a := by`.

Simplify using `[cm, sc]`. Rewrite using `[e1, (hsc a).1, (hsc a).2]`. Establish `hOE : ∀ x, x ∈ OEv (E` using `E) v ↔ π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F := by`. Introduce `x`. Rewrite using `[oev_iff_tensInt, split_integral_local F E v spl hspl, hspl_apply]`.

Simplify using the standard rewrite rules. Use `⟨e, π₁, π₂, he, hσe, fun x => ?_, fun x => ?_, he1, he2, hsc, hp2σ, hp1σ, hOE⟩` and prove the remaining obligations. Rewrite using `[PI.LocMassTypU.sc_mul_eq_smul]`. Conclude with `hm1 x`. Rewrite using `[PI.LocMassTypU.sc_mul_eq_smul]`.

Conclude with `hm2 x`.
-/
theorem split_reduction : SplitR := by
  intro F E _ _ _ _ _ σ n J ψ v hStd _ hEta
  have hCM := hStd.1
  have h2 := finrank_tens (E := E) v hCM.2.2.1
  have := finDim_tens (E := E) v
  obtain ⟨e, he, h0, h1⟩ : ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    unfold etaV at hEta
    split_ifs at hEta with h
    · exact h
    all_goals norm_num at hEta
  set π₁ := p1 h2 he h0 h1 with hπ₁
  set π₂ := p2 h2 he h0 h1 with hπ₂
  have hm1 : ∀ x, x * e = π₁ x • e := mul_e h2 he h0 h1
  have hm2 : ∀ x, x * (1 - e) = π₂ x • (1 - e) := mul_ce h2 he h0 h1
  have hdec : ∀ x, x = π₁ x • e + π₂ x • (1 - e) := decomp h2 he h0 h1
  have hσσ := sigma_invol σ hCM
  set f := sigR (Fv F v) σ e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hfe : f = 1 - e := by
    have c1 := idem_cases (show π₁ f * π₁ f = π₁ f by rw [← map_mul, hff])
    have c2 := idem_cases (show π₂ f * π₂ f = π₂ f by rw [← map_mul, hff])
    have hfd := hdec f
    rcases c1 with a | a <;> rcases c2 with b | b <;> rw [a, b] at hfd
    · exfalso
      apply h0
      rw [← sigR_sigR σ v hσσ e, ← hf, hfd]
      simp
    · simpa using hfd
    · exfalso
      obtain ⟨y, hy⟩ := sigma_ne_id σ hCM
      have hfe : f = e := by simpa using hfd
      have hid : ∀ x, sigR (Fv F v) σ x = x := by
        intro x
        conv_lhs => rw [hdec x]
        rw [map_add, sigR_smul, sigR_smul, map_sub, map_one, ← hf, hfe]
        exact (hdec x).symm
      apply hy
      apply inclR_injective (E := E) v
      rw [← sigR_inclR, hid]
    · exfalso
      apply h1
      rw [← sigR_sigR σ v hσσ e, ← hf, hfd]
      simp
  have hσe : sigR (Fv F v) σ e = 1 - e := hfe
  have hσ1 : sigR (Fv F v) σ (1 - e) = e := by
    rw [map_sub, map_one, hσe, sub_sub_cancel]
  have hp2σ : ∀ x, π₂ (sigR (Fv F v) σ x) = π₁ x := by
    intro x
    apply uniq2 h1 (K := Fv F v)
    calc π₂ (sigR (Fv F v) σ x) • (1 - e) = sigR (Fv F v) σ x * (1 - e) := (hm2 _).symm
      _ = sigR (Fv F v) σ x * sigR (Fv F v) σ e := by rw [hσe]
      _ = sigR (Fv F v) σ (x * e) := (map_mul _ _ _).symm
      _ = sigR (Fv F v) σ (π₁ x • e) := by rw [hm1]
      _ = π₁ x • sigR (Fv F v) σ e := sigR_smul σ v _ _
      _ = π₁ x • (1 - e) := by rw [hσe]
  have hp1σ : ∀ x, π₁ (sigR (Fv F v) σ x) = π₂ x := by
    intro x
    apply uniq1 h0 (K := Fv F v)
    calc π₁ (sigR (Fv F v) σ x) • e = sigR (Fv F v) σ x * e := (hm1 _).symm
      _ = sigR (Fv F v) σ x * sigR (Fv F v) σ (1 - e) := by rw [hσ1]
      _ = sigR (Fv F v) σ (x * (1 - e)) := (map_mul _ _ _).symm
      _ = sigR (Fv F v) σ (π₂ x • (1 - e)) := by rw [hm2]
      _ = π₂ x • sigR (Fv F v) σ (1 - e) := sigR_smul σ v _ _
      _ = π₂ x • e := by rw [hσ1]
  have hsc : ∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c := by
    intro c
    refine ⟨uniq1 h0 (K := Fv F v) ?_, uniq2 h1 (K := Fv F v) ?_⟩
    · rw [← hm1, PI.LocMassTypU.sc_mul_eq_smul]
    · rw [← hm2, PI.LocMassTypU.sc_mul_eq_smul]
  have he1 : π₁ e = 1 := uniq1 h0 (K := Fv F v) (by rw [← hm1, he, one_smul])
  have he2 : π₂ e = 0 := uniq2 h1 (K := Fv F v) (by rw [← hm2, idem_mul_compl he, zero_smul])
  have hce1 : π₁ (1 - e) = 0 := by rw [map_sub, map_one, he1, sub_self]
  have hce2 : π₂ (1 - e) = 1 := by rw [map_sub, map_one, he2, sub_zero]

  let φ : (Fv F v ⊗[F] E) →+* Fv F v × Fv F v := RingHom.prod π₁ π₂
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1' : π₁ x = π₁ y := congrArg Prod.fst hxy
      have h2' : π₂ x = π₂ y := congrArg Prod.snd hxy
      rw [hdec x, hdec y, h1', h2']
    · rintro ⟨a, b⟩
      refine ⟨sc (E := E) v a * e + sc (E := E) v b * (1 - e), ?_⟩
      show (π₁ _, π₂ _) = (a, b)
      rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, (hsc a).1, (hsc b).1, (hsc a).2,
        (hsc b).2, he1, he2, hce1, hce2]
      simp
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (cm (E := E) v).toRingEquiv.trans (RingEquiv.ofBijective φ hbij)
  have hspl_apply : ∀ y, spl y = (π₁ (cm (E := E) v y), π₂ (cm (E := E) v y)) := fun _ => rfl
  have hspl : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    rw [hspl_apply]
    have e1 : cm (E := E) v ((1 : E) ⊗ₜ[F] a) = sc (E := E) v a := by
      simp [cm, sc]
    rw [e1, (hsc a).1, (hsc a).2]
  have hOE : ∀ x, x ∈ OEv (E := E) v ↔
      π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F := by
    intro x
    rw [oev_iff_tensInt, split_integral_local F E v spl hspl, hspl_apply]
    simp
  refine ⟨e, π₁, π₂, he, hσe, fun x => ?_, fun x => ?_, he1, he2, hsc, hp2σ, hp1σ, hOE⟩
  · rw [PI.LocMassTypU.sc_mul_eq_smul]
    exact hm1 x
  · rw [PI.LocMassTypU.sc_mul_eq_smul]
    exact hm2 x

end PI.LocMassTypS
