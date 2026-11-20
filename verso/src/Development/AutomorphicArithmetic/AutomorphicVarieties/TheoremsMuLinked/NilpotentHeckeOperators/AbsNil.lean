import Mathlib

/- English proof (translation)
Establish `hc : ∀ (s u : T) (x : W), (θ s : Module.End ℂ W) ((θ u : Module.End ℂ W) x) = (θ u : Module.End ℂ W) ((θ s : Module.End ℂ W) x)`. Introduce `s u x`. Use `show ((θ s : Module.End ℂ W) * θ u) x = ((θ u : Module.End ℂ W) * θ s) x`. Rewrite using `[← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]`. Establish `key : ∀ n : ℕ, ∀ S : Submodule ℂ W, Module.finrank ℂ S = n → S ≠ ⊥ → (∀ t, ∀ v ∈ S, (θ t : Module.End ℂ W) v ∈ S) → ∃ v ∈ S, v ≠ 0 ∧ ∀ t, ∃ μ : ℂ, (θ t : Module.End ℂ W) v = μ • v`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `S hn hS hinv`. Distinguish the cases in `hsc : ∀ t, ∃ μ : ℂ, ∀ v ∈ S, (θ t : Module.End ℂ W) v = μ • v`.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS`. Conclude with `⟨v, hv, hv0, fun t => (hsc t).imp fun μ h => h v hv⟩`. Use `push_neg at hsc`. Take `⟨t0, ht0⟩` from `hsc`. Use `haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS`.

Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue ((θ t0 : Module.End ℂ W).restrict (fun v hv => hinv t0 v hv))`. Take `⟨w, hw⟩` from `hμ.exists_hasEigenvector`. Establish `hw1 : (θ t0 : Module.End ℂ W) w = μ • (w : W)`. Use `congrArg Subtype.val hw.apply_eq_smul` as an intermediate fact. Simplify `this` using `[LinearMap.restrict_apply]`.

Establish `hw0 : (w : W) ≠ 0`. Introduce `h`. Conclude with `hw.2 (Subtype.ext h)`. Use `set S1 := S ⊓ (θ t0 : Module.End ℂ W).eigenspace μ with hS1`. Establish `hwS1 : (w : W) ∈ S1` using `⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩`.

Establish `hS1b : S1 ≠ ⊥`. Introduce `h`. Rewrite `hwS1` using `[h, Submodule.mem_bot]`. Conclude with `hw0 hwS1`. Establish `hlt : S1 < S`.

Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `h`. Take `⟨v, hv, hv1⟩` from `ht0 μ`. Establish `: v ∈ S1` using `h ▸ hv`. Conclude with `hv1 (Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 this).2)`.

Establish `hrank : Module.finrank ℂ S1 < n` using `hn ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hinv1 : ∀ t, ∀ v ∈ S1, (θ t : Module.End ℂ W) v ∈ S1`. Introduce `t v hv`. Rewrite `hv`, the goal using `[Submodule.mem_inf]`. Use `⟨hinv t v hv.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.End.mem_eigenspace_iff, hc t0 t, Module.End.mem_eigenspace_iff.1 hv.2, map_smul]`. Take `⟨v, hv, hv0, hμv⟩` from `ih _ hrank S1 rfl hS1b hinv1`. Conclude with `⟨v, (Submodule.mem_inf.1 hv).1, hv0, hμv⟩`. Take `⟨v, hv, hv0, hμ⟩` from `key _ S0 rfl h0 h1`. Use `choose μ hμ using hμ`.

Establish `hinj : ∀ a b : ℂ, a • v = b • v → a = b` using `fun a b h => smul_left_injective ℂ hv0 h`. Establish `hmul : ∀ s u, μ (s * u) = μ s * μ u`. Introduce `s u`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hμ, map_mul, Units.val_mul, Module.End.mul_apply, hμ u, map_smul, hμ s, smul_smul, mul_comm]`.

Establish `hone : μ 1 = 1` using `hinj _ _ (by rw [← hμ, map_one, Units.val_one, Module.End.one_apply, one_smul])`. Establish `hne : ∀ s, μ s ≠ 0`. Introduce `s h`. Use `hmul s s⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hone, h, zero_mul]`.

Conclude with `one_ne_zero this`. Use `⟨{ toFun := fun s => Units.mk0 (μ s) (hne s), map_one' := Units.ext hone, map_mul' := fun s u => Units.ext (hmul s u) }, v, hv, hv0, fun s => ?_⟩` and prove the remaining obligations. Simplify using `using hμ s`.
-/
private theorem absNil_eig {T W : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (S0 : Submodule ℂ W) (h0 : S0 ≠ ⊥)
    (h1 : ∀ t, ∀ v ∈ S0, (θ t : Module.End ℂ W) v ∈ S0) :
    ∃ χ : T →* ℂˣ, ∃ v ∈ S0, v ≠ 0 ∧ ∀ t, (θ t : Module.End ℂ W) v = (χ t : ℂ) • v := by
  have hc : ∀ (s u : T) (x : W), (θ s : Module.End ℂ W) ((θ u : Module.End ℂ W) x) = (θ u : Module.End ℂ W) ((θ s : Module.End ℂ W) x) := by
    intro s u x
    show ((θ s : Module.End ℂ W) * θ u) x = ((θ u : Module.End ℂ W) * θ s) x
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]
  have key : ∀ n : ℕ, ∀ S : Submodule ℂ W, Module.finrank ℂ S = n → S ≠ ⊥ →
      (∀ t, ∀ v ∈ S, (θ t : Module.End ℂ W) v ∈ S) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ t, ∃ μ : ℂ, (θ t : Module.End ℂ W) v = μ • v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hn hS hinv
      by_cases hsc : ∀ t, ∃ μ : ℂ, ∀ v ∈ S, (θ t : Module.End ℂ W) v = μ • v
      · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
        exact ⟨v, hv, hv0, fun t => (hsc t).imp fun μ h => h v hv⟩
      · push_neg at hsc
        obtain ⟨t0, ht0⟩ := hsc
        haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
        obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((θ t0 : Module.End ℂ W).restrict (fun v hv => hinv t0 v hv))
        obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
        have hw1 : (θ t0 : Module.End ℂ W) w = μ • (w : W) := by
          have := congrArg Subtype.val hw.apply_eq_smul
          simpa [LinearMap.restrict_apply] using this
        have hw0 : (w : W) ≠ 0 := by
          intro h
          exact hw.2 (Subtype.ext h)
        set S1 := S ⊓ (θ t0 : Module.End ℂ W).eigenspace μ with hS1
        have hwS1 : (w : W) ∈ S1 := ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩
        have hS1b : S1 ≠ ⊥ := by
          intro h
          rw [h, Submodule.mem_bot] at hwS1
          exact hw0 hwS1
        have hlt : S1 < S := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro h
          obtain ⟨v, hv, hv1⟩ := ht0 μ
          have : v ∈ S1 := h ▸ hv
          exact hv1 (Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 this).2)
        have hrank : Module.finrank ℂ S1 < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
        have hinv1 : ∀ t, ∀ v ∈ S1, (θ t : Module.End ℂ W) v ∈ S1 := by
          intro t v hv
          rw [Submodule.mem_inf] at hv ⊢
          refine ⟨hinv t v hv.1, ?_⟩
          rw [Module.End.mem_eigenspace_iff, hc t0 t, Module.End.mem_eigenspace_iff.1 hv.2, map_smul]
        obtain ⟨v, hv, hv0, hμv⟩ := ih _ hrank S1 rfl hS1b hinv1
        exact ⟨v, (Submodule.mem_inf.1 hv).1, hv0, hμv⟩
  obtain ⟨v, hv, hv0, hμ⟩ := key _ S0 rfl h0 h1
  choose μ hμ using hμ
  have hinj : ∀ a b : ℂ, a • v = b • v → a = b := fun a b h => smul_left_injective ℂ hv0 h
  have hmul : ∀ s u, μ (s * u) = μ s * μ u := by
    intro s u
    apply hinj
    rw [← hμ, map_mul, Units.val_mul, Module.End.mul_apply, hμ u, map_smul, hμ s, smul_smul, mul_comm]
  have hone : μ 1 = 1 := hinj _ _ (by rw [← hμ, map_one, Units.val_one, Module.End.one_apply, one_smul])
  have hne : ∀ s, μ s ≠ 0 := by
    intro s h
    have := hmul s s⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨{ toFun := fun s => Units.mk0 (μ s) (hne s), map_one' := Units.ext hone, map_mul' := fun s u => Units.ext (hmul s u) }, v, hv, hv0, fun s => ?_⟩
  simpa using hμ s

/- English proof (translation)
Establish `hsep : (Polynomial.X ^ m - Polynomial.C (1 : ℂ)).Separable` using `Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 hm.ne') one_ne_zero`. Establish `hss : u.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hu])`. Rewrite `hv` using `[hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]`. Conclude with `Module.End.mem_eigenspace_iff.1 hv`.
-/
private theorem absNil_fin {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (u : Module.End ℂ W) (m : ℕ) (hm : 0 < m) (hu : u ^ m = 1) (c : ℂ) (v : W)
    (hv : v ∈ u.maxGenEigenspace c) : u v = c • v := by
  have hsep : (Polynomial.X ^ m - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have hss : u.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hu])
  rw [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hv
  exact Module.End.mem_eigenspace_iff.1 hv

/- English proof (translation)
Rewrite `hv` using `[Module.End.maxGenEigenspace_eq_genEigenspace_finrank, ← Module.End.genEigenspace_eq_genEigenspace_finrank_of_le u c hN, Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]`. Conclude with `hv`.
-/
private theorem absNil_pow {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (u : Module.End ℂ W) (c : ℂ) (v : W) (hv : v ∈ u.maxGenEigenspace c) (N : ℕ)
    (hN : Module.finrank ℂ W ≤ N) : ((u - c • 1) ^ N) v = 0 := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, ← Module.End.genEigenspace_eq_genEigenspace_finrank_of_le u c hN, Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hv
  exact hv

/- English proof (translation)
Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace u c v).1 hv`. Establish `h : ∀ n : ℕ, ((u - c • 1) ^ n) v = (d - c) ^ n • v`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[pow_succ' (u - c • 1) n, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hd, ← sub_smul, smul_smul, pow_succ (d - c) n]`. Rewrite `hk` using `[h k]`. Break down `smul_eq_zero.1 hk with h1 | h1` into its components or cases. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1`.

Conclude with `absurd h1 h0`.
-/
private theorem absNil_uniq {W : Type} [AddCommGroup W] [Module ℂ W]
    (u : Module.End ℂ W) (c d : ℂ) (v : W) (h0 : v ≠ 0) (hv : v ∈ u.maxGenEigenspace c) (hd : u v = d • v) :
    d = c := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace u c v).1 hv
  have h : ∀ n : ℕ, ((u - c • 1) ^ n) v = (d - c) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' (u - c • 1) n, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hd, ← sub_smul, smul_smul, pow_succ (d - c) n]
  rw [h k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1
  · exact absurd h1 h0

/- English proof (translation)
Introduce `T W κ _ _ _ _ θ t act hact hfin N hN F hF`. Establish `hcomm : ∀ s u : T, Commute (θ s : Module.End ℂ W) (θ u : Module.End ℂ W)`. Introduce `s u`. Use `show (θ s : Module.End ℂ W) * θ u = θ u * θ s`. Rewrite using `[← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]`.

Establish `htop : (⨆ χ : T → ℂ, ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s)) = ⊤` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute (fun s : T => (θ s : Module.End ℂ W)) (fun s u _ => hcomm s u) (fun s => Module.End.iSup_maxGenEigenspace_eq_top _)`. Establish `key : ∀ χ : T → ℂ, ∀ v ∈ ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s), act F v = 0`. Introduce `χ v hv`. Use `set V := ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s) with hV`. Distinguish the cases in `hV0 : V = ⊥`.

Rewrite `hv` using `[hV0, Submodule.mem_bot]`. Rewrite using `[hv, map_zero]`. Establish `hinv : ∀ u, ∀ w ∈ V, (θ u : Module.End ℂ W) w ∈ V`. Introduce `u w hw`. Rewrite `hw`, the goal using `[hV, Submodule.mem_iInf]`.

Introduce `s`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm s u) (χ s) (hw s)`. Take `⟨χ', w, hw, hw0, hwχ⟩` from `absNil_eig θ V hV0 hinv`. Establish `hχ : ∀ s, (χ' s : ℂ) = χ s` using `fun s => absNil_uniq _ _ _ w hw0 ((Submodule.mem_iInf _).1 hw s) (hwχ s)`. Establish `hVeq : V = ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ' s : ℂ)`.

Rewrite using `[hV]`. Simplify using `only [hχ]`. Set `I : Ideal (MvPolynomial (κ ⊕ κ) ℂ)` to `{ carrier := {p | ∀ x ∈ V, act p x = 0} add_mem' := by`. Introduce `p q hp hq x hx`. Use `show act (p + q) x = 0`.

Rewrite using `[map_add, LinearMap.add_apply, hp x hx, hq x hx, add_zero]`. Use the proof step `zero_mem' := by`. Introduce `x hx`. Use `show act 0 x = 0`. Rewrite using `[map_zero, LinearMap.zero_apply]`.

Use the proof step `smul_mem' := by`. Introduce `c p hp x hx`. Use `show act (c * p) x = 0`. Rewrite using `[map_mul, Module.End.mul_apply, hp x hx, map_zero] }`. Establish `hmemI : ∀ p, p ∈ I ↔ ∀ x ∈ V, act p x = 0` using `fun p => Iff.rfl`.

Establish `hFI : F ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk ℂ]`. Use `hF χ' ?_ _ (Ideal.Quotient.mkₐ ℂ I) ?_ ?_` and prove the remaining obligations. Rewrite using `[← hVeq]`. Conclude with `hV0`.

Introduce `a`. Rewrite using `[← AlgHom.commutes (Ideal.Quotient.mkₐ ℂ I), ← map_sub, ← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hmemI]`. Introduce `x hx`. Rewrite using `[map_pow, map_sub, AlgHom.commutes, hact, Algebra.algebraMap_eq_smul_one, hχ]`. Conclude with `absNil_pow _ _ x ((Submodule.mem_iInf _).1 hx _) N hN`.

Introduce `a`. Rewrite using `[← AlgHom.commutes (Ideal.Quotient.mkₐ ℂ I), ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hmemI]`. Introduce `x hx`. Take `⟨m, hm, hm1⟩` from `hfin a`. Rewrite using `[map_sub, AlgHom.commutes, hact, Algebra.algebraMap_eq_smul_one, hχ, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Use `absNil_fin _ m hm ?_ _ x ((Submodule.mem_iInf _).1 hx _)` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, hm1, Units.val_one]`. Conclude with `(hmemI F).1 hFI v hv`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`.

Establish `hw : w ∈ ⨆ χ : T → ℂ, ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s)`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `Submodule.iSup_induction (motive := fun x => act F x = 0) _ hw (fun χ x hx => key χ x hx) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])`.
-/
theorem UpperTheory.V.Th.absNil :
    ∀ (T W κ : Type) [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (θ : T →* (Module.End ℂ W)ˣ) (t : κ ⊕ κ → T) (act : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] Module.End ℂ W), (∀ a, act (MvPolynomial.X a) = θ (t a)) → (∀ a, ∃ m : ℕ, 0 < m ∧ θ (t (.inr a)) ^ m = 1) → ∀ (N : ℕ), Module.finrank ℂ W ≤ N → ∀ F : MvPolynomial (κ ⊕ κ) ℂ, (∀ χ : T →* ℂˣ, (⨅ s, Module.End.maxGenEigenspace (θ s : Module.End ℂ W) (χ s : ℂ)) ≠ ⊥ → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (φ : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] S), (∀ a, (φ (MvPolynomial.X (.inl a)) - algebraMap ℂ S (χ (t (.inl a)) : ℂ)) ^ N = 0) → (∀ a, φ (MvPolynomial.X (.inr a)) = algebraMap ℂ S (χ (t (.inr a)) : ℂ)) → φ F = 0) → act F = 0 := by
  intro T W κ _ _ _ _ θ t act hact hfin N hN F hF
  have hcomm : ∀ s u : T, Commute (θ s : Module.End ℂ W) (θ u : Module.End ℂ W) := by
    intro s u
    show (θ s : Module.End ℂ W) * θ u = θ u * θ s
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]
  have htop : (⨆ χ : T → ℂ, ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s)) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun s : T => (θ s : Module.End ℂ W)) (fun s u _ => hcomm s u)
      (fun s => Module.End.iSup_maxGenEigenspace_eq_top _)
  have key : ∀ χ : T → ℂ, ∀ v ∈ ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s), act F v = 0 := by
    intro χ v hv
    set V := ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s) with hV
    by_cases hV0 : V = ⊥
    · rw [hV0, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    have hinv : ∀ u, ∀ w ∈ V, (θ u : Module.End ℂ W) w ∈ V := by
      intro u w hw
      rw [hV, Submodule.mem_iInf] at hw ⊢
      intro s
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm s u) (χ s) (hw s)
    obtain ⟨χ', w, hw, hw0, hwχ⟩ := absNil_eig θ V hV0 hinv
    have hχ : ∀ s, (χ' s : ℂ) = χ s := fun s =>
      absNil_uniq _ _ _ w hw0 ((Submodule.mem_iInf _).1 hw s) (hwχ s)
    have hVeq : V = ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ' s : ℂ) := by
      rw [hV]
      simp only [hχ]
    let I : Ideal (MvPolynomial (κ ⊕ κ) ℂ) :=
      { carrier := {p | ∀ x ∈ V, act p x = 0}
        add_mem' := by
          intro p q hp hq x hx
          show act (p + q) x = 0
          rw [map_add, LinearMap.add_apply, hp x hx, hq x hx, add_zero]
        zero_mem' := by
          intro x hx
          show act 0 x = 0
          rw [map_zero, LinearMap.zero_apply]
        smul_mem' := by
          intro c p hp x hx
          show act (c * p) x = 0
          rw [map_mul, Module.End.mul_apply, hp x hx, map_zero] }
    have hmemI : ∀ p, p ∈ I ↔ ∀ x ∈ V, act p x = 0 := fun p => Iff.rfl
    have hFI : F ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk ℂ]
      refine hF χ' ?_ _ (Ideal.Quotient.mkₐ ℂ I) ?_ ?_
      · rw [← hVeq]
        exact hV0
      · intro a
        rw [← AlgHom.commutes (Ideal.Quotient.mkₐ ℂ I), ← map_sub, ← map_pow, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem, hmemI]
        intro x hx
        rw [map_pow, map_sub, AlgHom.commutes, hact, Algebra.algebraMap_eq_smul_one, hχ]
        exact absNil_pow _ _ x ((Submodule.mem_iInf _).1 hx _) N hN
      · intro a
        rw [← AlgHom.commutes (Ideal.Quotient.mkₐ ℂ I), ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem, hmemI]
        intro x hx
        obtain ⟨m, hm, hm1⟩ := hfin a
        rw [map_sub, AlgHom.commutes, hact, Algebra.algebraMap_eq_smul_one, hχ, LinearMap.sub_apply,
          LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
        refine absNil_fin _ m hm ?_ _ x ((Submodule.mem_iInf _).1 hx _)
        rw [← Units.val_pow_eq_pow_val, hm1, Units.val_one]
    exact (hmemI F).1 hFI v hv
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.zero_apply]
  have hw : w ∈ ⨆ χ : T → ℂ, ⨅ s, (θ s : Module.End ℂ W).maxGenEigenspace (χ s) := by
    rw [htop]
    trivial
  exact Submodule.iSup_induction (motive := fun x => act F x = 0) _ hw (fun χ x hx => key χ x hx) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
