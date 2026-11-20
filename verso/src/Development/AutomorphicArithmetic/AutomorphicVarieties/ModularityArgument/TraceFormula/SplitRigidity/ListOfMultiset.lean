import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.SR Formalism.L2.Host

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `h π`. Conclude with `(GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep UpperTheory.V.Af.formsFiniteGL E m π).mono fun w ⟨B, hB⟩ => ⟨B, hB⟩`.
-/
private theorem cg_sat_ev {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : CG E m) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B := by
  induction π using Quotient.inductionOn with
  | h π =>
    exact (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep UpperTheory.V.Af.formsFiniteGL E m π).mono
      fun w ⟨B, hB⟩ => ⟨B, hB⟩

/- English proof (translation)
Proceed by induction on `B using Quot.inductionOn with`. Consider the case `h l`. Establish `hl : l.length = d` using `by simpa using hB`. Substitute `hl` using the available equality. Conclude with `⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩`.
-/
private theorem list_of_multiset {d : ℕ} (B : Multiset ℂˣ) (hB : Multiset.card B = d) :
    ∃ f : Fin d → ℂˣ, Finset.univ.val.map f = B := by
  induction B using Quot.inductionOn with
  | h l =>
    have hl : l.length = d := by simpa using hB
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

/- English proof (translation)
Rewrite using `[Multiset.map_map, Finset.sum_eq_multiset_sum]`. Both sides reduce to the same expression.
-/
private theorem power_sum_map {d : ℕ} (f : Fin d → ℂˣ) (k : ℕ) :
    ((Finset.univ.val.map f).map fun z : ℂˣ => (z : ℂ) ^ k).sum = ∑ a, (f a : ℂ) ^ k := by
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

open PositivityTheory.RgJS in
/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simpa [CG.twist_one] using hB`. Consider the case `succ i ih`. Establish `h` using `satake_twist_holds E m _ χ w _ hχ ih`. Rewrite `h` using `[← CG.twist_mul, Multiset.map_map]`.

Rewrite using `[pow_succ]`. Simplify `h` using `[Function.comp_def, pow_succ, mul_assoc]`.
-/
private theorem sat_pow {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : CG E m) (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w) (hB : π.HasSat w B) (i : ℕ) :
    (π.twist (χ ^ i)).HasSat w (B.map (· * χ.val w ^ i)) := by
  induction i with
  | zero => simpa [CG.twist_one] using hB
  | succ i ih =>
    have h := satake_twist_holds E m _ χ w _ hχ ih
    rw [← CG.twist_mul, Multiset.map_map] at h
    rw [pow_succ]
    simpa [Function.comp_def, pow_succ, mul_assoc] using h

open PositivityTheory.RgJS in
/- English proof (translation)
Introduce `E _ _ _ hE n hn π hπu J _ a P ha1 hPu hev`. Take `⟨χ, hπt, hχ⟩` from `hTw E hE`. Take `⟨hχu, hχi⟩` from `hχ n π hn hπu`. Take `⟨M, hM⟩ : ∃ M : ℕ, M = 16 * (Fintype.card J + 1) ^ 2` from `⟨_, rfl⟩`. Establish `hM1 : 1 ≤ M` using `by rw [hM]; exact Nat.succ_le_of_lt (by positivity)`.

Establish `e00 : π.twist (χ ^ 0) = π` using `by rw [pow_zero, CG.twist_one]`. Establish `hRSU : RSU` using `rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole`. Establish `hBd : GlobalTheory.Published.JacquetShalikaBound` using `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound`. Set `u : Fin M ⊕ J → Σ m, CG E m` to `Sum.elim (fun i => ⟨n, π.twist (χ ^ i.val)⟩) fun j => ⟨a j, P j⟩`. Set `X : Type` to `↥(Set.range u)`.

Establish `: Fintype X` using `Fintype.ofFinite X`. Establish `hX : ∀ x : X, 1 ≤ x.1.1 ∧ x.1.2.IsUnitary`. Introduce and unpack `⟨p, ⟨o, rfl⟩⟩`. Consider the cases of `o with`. Consider the case `inl i => exact ⟨hn, hχu i.val⟩`.

Consider the case `inr j => exact ⟨ha1 j, hPu j⟩`. Set `z : Fin M → X` to `fun i => ⟨u (.inl i), .inl i, rfl⟩`. Set `x₀ : X` to `z ⟨0, hM1⟩`. Set `y : J → X` to `fun j => ⟨u (.inr j), .inr j, rfl⟩`. Use `choose S0 hS0 using fun x y : X => hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x).1 (hX y).1 (hX x).2 (hX y).2`.

Set `S1 : Finset (HeightOneSpectrum (𝓞 E))` to `(Filter.eventually_cofinite.1 hev).toFinset`. Set `S2 : Finset (HeightOneSpectrum (𝓞 E))` to `(Filter.eventually_cofinite.1 hπt).toFinset`. Set `S3 : Finset (HeightOneSpectrum (𝓞 E))` to `Finset.univ.biUnion fun x : X => (Filter.eventually_cofinite.1 (cg_sat_ev x.1.2)).toFinset`. Set `S : Finset (HeightOneSpectrum (𝓞 E))` to `S1 ∪ S2 ∪ S3 ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2)`. Establish `hS1 : ∀ w : Off E S, IsSplitAt w.1 → ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w.1 (b j)) ∧ π.HasSat w.1 (∑ j, b j)`.

Introduce `w`. Assume the negation of the conclusion as `h`. Use `w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `h`.

Establish `hS2 : ∀ w : Off E S, χ.UnrAt w.1 ∧ ‖((χ.val w.1 : ℂˣ) : ℂ)‖ = 1 ∧ (¬ IsSplitAt w.1 → χ.val w.1 = 1)`. Introduce `w`. Assume the negation of the conclusion as `h`. Use `w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)))` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`.

Conclude with `h`. Establish `hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f)`. Introduce `x w`. Establish `hw : ∃ B, x.1.2.HasSat w.1 B`. Assume the negation of the conclusion as `h`.

Use `w.2 (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, ?_⟩)))` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `h`. Take `⟨B, hB⟩` from `hw`. Take `⟨f, hf⟩` from `list_of_multiset B hB.card`.

Conclude with `⟨f, hf ▸ hB⟩`. Use `choose α hα using hex`. Set `d : X → ℕ` to `fun x => x.1.1`. Set `A : ∀ x : X, Off E S → Fin (d x) → ℂ` to `fun x w i => (α x w i : ℂ)`. Establish `hsub : ∀ x y : X, S0 x y ⊆ S` using `fun x y z hz => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩)`.

Establish `hSys : Sys nq X d A`. Use `⟨prime_sum_converges_and_diverges E S, fun x => (hX x).1, fun x w i => ?_, fun x w => ?_, fun x y => ?_⟩` and prove the remaining obligations. Establish `h` using `(hBd E x.1.1 x.1.2 (hX x).2 w.1 _ (hα x w) (α x w i) (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2 show ‖((α x w i : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)`. Rewrite using `[Real.sqrt_eq_rpow]`. Conclude with `h.le`.

Establish `h` using `determinant_one_condition_holds E x.1.1 x.1.2 w.1 _ (hX x).2 (hα x w)`. Rewrite `h` using `[← Finset.prod_eq_multiset_prod, Units.coe_prod]`. Conclude with `h`. Take `⟨F, σ₀, hF, hFe⟩` from `hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)`. Use `⟨F, σ₀, hF, fun σ hσ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hFe σ hσ]`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Both sides reduce to the same expression.

Rewrite using `[if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]`. Both sides reduce to the same expression. Set `I : Set (Off E S)` to `{w | ¬ IsSplitAt w.1}`. Establish `hx₀ : ∀ w : Off E S, π.HasSat w.1 (Finset.univ.val.map (α x₀ w))` using `fun w => by`. Establish `h : (π.twist (χ ^ 0)).HasSat w.1 (Finset.univ.val.map (α x₀ w))` using `hα x₀ w`.

Rewrite `h` using `[e00]`. Then use the resulting hypothesis. Establish `hz : Function.Injective z` using `fun i i' h => by`. Establish `h1 : (⟨n, π.twist (χ ^ i.val)⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ i'.val)⟩` using `congrArg Subtype.val h`. Conclude with `Fin.ext (hχi (eq_of_heq (Sigma.mk.inj h1).2))`. Establish `hzp : ∀ (i : Fin M) (w : Off E S) (k : ℕ), ∑ b, A (z i) w b ^ k = ((χ.val w.1 : ℂˣ) : ℂ) ^ (i.val * k) * ∑ a, A x₀ w a ^ k`.

Introduce `i w k`. Establish `h1 : (π.twist (χ ^ i.val)).HasSat w.1 (Finset.univ.val.map (α (z i) w))` using `hα (z i) w`. Establish `h2` using `h1.unique (sat_pow π χ w.1 _ (hS2 w).1 (hx₀ w) i.val)`. Establish `h3` using `congrArg (fun M : Multiset ℂˣ => (M.map fun t : ℂˣ => (t : ℂ) ^ k).sum) h2`. Simplify using `only [Multiset.map_map] at h3`.

Rewrite using `[Finset.mul_sum]`. Use `h3.trans ?_` and prove the remaining obligations. Use `congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]`. Conclude with `mul_comm _ _`.

Take `⟨C, hC⟩` from `hSh (Off E S) nq X d A hSys x₀ I M z (fun w => ((χ.val w.1 : ℂˣ) : ℂ)) hM1 hz (fun w => (hS2 w).2.1) (fun w hw => by rw [(hS2 w).2.2 hw, Units.val_one]) hzp`. Establish `hpow : ∀ w, w ∉ I → ∀ k : ℕ, ∑ i, A x₀ w i ^ k = ∑ j, ∑ i, A (y j) w i ^ k`. Introduce `w hwI k`. Establish `hsp : IsSplitAt w.1`. Assume the negation of the conclusion as `h`.

Conclude with `hwI h`. Take `⟨b, hb, hπb⟩` from `hS1 w hsp`. Establish `e1 : ∀ j, b j = Finset.univ.val.map (α (y j) w)` using `fun j => (hb j).unique (hα (y j) w)`. Establish `e0 : ∑ j, b j = Finset.univ.val.map (α x₀ w)` using `hπb.unique (hx₀ w)`. Set `φ : Multiset ℂˣ →+ ℂ` to `Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ) ^ k)`.

Establish `hφ : ∀ M : Multiset ℂˣ, φ M = (M.map fun z : ℂˣ => (z : ℂ) ^ k).sum` using `fun M => rfl`. Establish `h` using `congrArg φ e0`. Rewrite `h` using `[map_sum]`. Simplify using `only [hφ, e1, power_sum_map] at h`. Conclude with `h.symm`.

Take `⟨j, hj⟩` from `hAS (Off E S) nq X d A hSys x₀ I J y M C hM.ge hC hpow`. Establish `h1 : (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ 0)⟩` using `congrArg Subtype.val hj`. Conclude with `⟨j, by rw [h1, e00]⟩`.
-/
theorem UpperTheory.V.Z.Tf.SR.splitRigid_of (hSh : ShareBd) (hAS : AbsShare) (hTw : AntiTw) : SplitRigid := by
  intro E _ _ _ hE n hn π hπu J _ a P ha1 hPu hev
  classical
  obtain ⟨χ, hπt, hχ⟩ := hTw E hE
  obtain ⟨hχu, hχi⟩ := hχ n π hn hπu
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 16 * (Fintype.card J + 1) ^ 2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.succ_le_of_lt (by positivity)
  have e00 : π.twist (χ ^ 0) = π := by rw [pow_zero, CG.twist_one]
  have hRSU : RSU := rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole
  have hBd : GlobalTheory.Published.JacquetShalikaBound := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
  let u : Fin M ⊕ J → Σ m, CG E m := Sum.elim (fun i => ⟨n, π.twist (χ ^ i.val)⟩) fun j => ⟨a j, P j⟩
  let X : Type := ↥(Set.range u)
  have : Fintype X := Fintype.ofFinite X
  have hX : ∀ x : X, 1 ≤ x.1.1 ∧ x.1.2.IsUnitary := by
    rintro ⟨p, ⟨o, rfl⟩⟩
    cases o with
    | inl i => exact ⟨hn, hχu i.val⟩
    | inr j => exact ⟨ha1 j, hPu j⟩
  let z : Fin M → X := fun i => ⟨u (.inl i), .inl i, rfl⟩
  let x₀ : X := z ⟨0, hM1⟩
  let y : J → X := fun j => ⟨u (.inr j), .inr j, rfl⟩
  choose S0 hS0 using fun x y : X => hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x).1 (hX y).1 (hX x).2 (hX y).2
  let S1 : Finset (HeightOneSpectrum (𝓞 E)) := (Filter.eventually_cofinite.1 hev).toFinset
  let S2 : Finset (HeightOneSpectrum (𝓞 E)) := (Filter.eventually_cofinite.1 hπt).toFinset
  let S3 : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.biUnion fun x : X => (Filter.eventually_cofinite.1 (cg_sat_ev x.1.2)).toFinset
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    S1 ∪ S2 ∪ S3 ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2)
  have hS1 : ∀ w : Off E S, IsSplitAt w.1 →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w.1 (b j)) ∧ π.HasSat w.1 (∑ j, b j) := by
    intro w
    by_contra h
    refine w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))
    rw [Set.Finite.mem_toFinset]
    exact h
  have hS2 : ∀ w : Off E S, χ.UnrAt w.1 ∧ ‖((χ.val w.1 : ℂˣ) : ℂ)‖ = 1 ∧ (¬ IsSplitAt w.1 → χ.val w.1 = 1) := by
    intro w
    by_contra h
    refine w.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)))
    rw [Set.Finite.mem_toFinset]
    exact h
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    intro x w
    have hw : ∃ B, x.1.2.HasSat w.1 B := by
      by_contra h
      refine w.2 (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, ?_⟩)))
      rw [Set.Finite.mem_toFinset]
      exact h
    obtain ⟨B, hB⟩ := hw
    obtain ⟨f, hf⟩ := list_of_multiset B hB.card
    exact ⟨f, hf ▸ hB⟩
  choose α hα using hex
  let d : X → ℕ := fun x => x.1.1
  let A : ∀ x : X, Off E S → Fin (d x) → ℂ := fun x w i => (α x w i : ℂ)
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩)
  have hSys : Sys nq X d A := by
    refine ⟨prime_sum_converges_and_diverges E S, fun x => (hX x).1, fun x w i => ?_, fun x w => ?_, fun x y => ?_⟩
    · have h := (hBd E x.1.1 x.1.2 (hX x).2 w.1 _ (hα x w) (α x w i)
        (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
      show ‖((α x w i : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
      rw [Real.sqrt_eq_rpow]
      exact h.le
    · have h := determinant_one_condition_holds E x.1.1 x.1.2 w.1 _ (hX x).2 (hα x w)
      rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
      exact h
    · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
      refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
      rw [hFe σ hσ]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
        rfl
  let I : Set (Off E S) := {w | ¬ IsSplitAt w.1}
  have hx₀ : ∀ w : Off E S, π.HasSat w.1 (Finset.univ.val.map (α x₀ w)) := fun w => by
    have h : (π.twist (χ ^ 0)).HasSat w.1 (Finset.univ.val.map (α x₀ w)) := hα x₀ w
    rwa [e00] at h
  have hz : Function.Injective z := fun i i' h => by
    have h1 : (⟨n, π.twist (χ ^ i.val)⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ i'.val)⟩ := congrArg Subtype.val h
    exact Fin.ext (hχi (eq_of_heq (Sigma.mk.inj h1).2))
  have hzp : ∀ (i : Fin M) (w : Off E S) (k : ℕ),
      ∑ b, A (z i) w b ^ k = ((χ.val w.1 : ℂˣ) : ℂ) ^ (i.val * k) * ∑ a, A x₀ w a ^ k := by
    intro i w k
    have h1 : (π.twist (χ ^ i.val)).HasSat w.1 (Finset.univ.val.map (α (z i) w)) := hα (z i) w
    have h2 := h1.unique (sat_pow π χ w.1 _ (hS2 w).1 (hx₀ w) i.val)
    have h3 := congrArg (fun M : Multiset ℂˣ => (M.map fun t : ℂˣ => (t : ℂ) ^ k).sum) h2
    simp only [Multiset.map_map] at h3
    rw [Finset.mul_sum]
    refine h3.trans ?_
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
    exact mul_comm _ _
  obtain ⟨C, hC⟩ := hSh (Off E S) nq X d A hSys x₀ I M z (fun w => ((χ.val w.1 : ℂˣ) : ℂ)) hM1 hz (fun w => (hS2 w).2.1)
    (fun w hw => by rw [(hS2 w).2.2 hw, Units.val_one]) hzp
  have hpow : ∀ w, w ∉ I → ∀ k : ℕ, ∑ i, A x₀ w i ^ k = ∑ j, ∑ i, A (y j) w i ^ k := by
    intro w hwI k
    have hsp : IsSplitAt w.1 := by
      by_contra h
      exact hwI h
    obtain ⟨b, hb, hπb⟩ := hS1 w hsp
    have e1 : ∀ j, b j = Finset.univ.val.map (α (y j) w) := fun j => (hb j).unique (hα (y j) w)
    have e0 : ∑ j, b j = Finset.univ.val.map (α x₀ w) := hπb.unique (hx₀ w)
    let φ : Multiset ℂˣ →+ ℂ :=
      Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ) ^ k)
    have hφ : ∀ M : Multiset ℂˣ, φ M = (M.map fun z : ℂˣ => (z : ℂ) ^ k).sum := fun M => rfl
    have h := congrArg φ e0
    rw [map_sum] at h
    simp only [hφ, e1, power_sum_map] at h
    exact h.symm
  obtain ⟨j, hj⟩ := hAS (Off E S) nq X d A hSys x₀ I J y M C hM.ge hC hpow
  have h1 : (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π.twist (χ ^ 0)⟩ := congrArg Subtype.val hj
  exact ⟨j, by rw [h1, e00]⟩
