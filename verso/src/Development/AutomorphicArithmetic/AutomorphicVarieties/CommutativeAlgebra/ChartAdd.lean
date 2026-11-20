import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `h` using `coeff_embDomain_rename ε.toEmbedding p (Finsupp.mapDomain ε.symm n)`. Rewrite `h` using `[Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]`. Establish `h2 : (ε.toEmbedding : τ → τ') ∘ ε.symm = id` using `funext fun x => ε.apply_symm_apply x`. Rewrite `h` using `[h2, Finsupp.mapDomain_id]`. Conclude with `h`.
-/
private theorem chart_add_coeff {K τ τ' : Type} [CommRing K] (ε : τ ≃ τ') (p : MvPowerSeries τ K) (n : τ' →₀ ℕ) :
    coeff n (rename ε p) = coeff (Finsupp.mapDomain ε.symm n) p := by
  have h := coeff_embDomain_rename ε.toEmbedding p (Finsupp.mapDomain ε.symm n)
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp] at h
  have h2 : (ε.toEmbedding : τ → τ') ∘ ε.symm = id := funext fun x => ε.apply_symm_apply x
  rw [h2, Finsupp.mapDomain_id] at h
  exact h

/- English proof (translation)
Proceed by induction on `n using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]`. Consider the case `single a b => simp [Finsupp.weight_single]`.
-/
private theorem chart_add_weight {τ τ' X : Type} [AddCommGroup X] (g : τ' → τ) (wt : τ → X) (n : τ' →₀ ℕ) :
    Finsupp.weight wt (Finsupp.mapDomain g n) = Finsupp.weight (fun s => wt (g s)) n := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
  | single a b => simp [Finsupp.weight_single]

/- English proof (translation)
Use `show coeff n (rename ε (φ f)) = 0`. Rewrite using `[chart_add_coeff]`. Use `h.graded j f hf _ ?_` and prove the remaining obligations. Rewrite using `[chart_add_weight, ← funext hw]` and apply the resulting hypothesis. Use `const f := by show constantCoeff (rename ε (φ f)) = _`.

Rewrite using `[constantCoeff_rename, h.const]`. Use `onto i := by`. Take `⟨f, h1, h2⟩` from `h.onto (ε.symm i)`. Use `⟨f, ?_, fun i' hi' => ?_⟩` and prove the remaining obligations. Use `show coeff _ (rename ε (φ f)) ≠ 0`.

Rewrite using `[chart_add_coeff, Finsupp.mapDomain_single]` and apply the resulting hypothesis. Use `show coeff _ (rename ε (φ f)) = 0`. Rewrite using `[chart_add_coeff, Finsupp.mapDomain_single]`. Conclude with `h2 _ fun h3 => hi' (ε.symm.injective h3)`. Use `inj f hx hf := by`.

Use `h.inj f hx fun i => ?_` and prove the remaining obligations. Establish `h1 : coeff _ (rename ε (φ f)) = 0` using `hf (ε i)`. Rewrite `h1` using `[chart_add_coeff, Finsupp.mapDomain_single, ε.symm_apply_apply]`. Then use the resulting hypothesis.
-/
private theorem chart_add_rename {O A X τ τ' : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    [AddCommGroup X] {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (ε : τ ≃ τ') (wt' : τ' → X)
    (hw : ∀ s, wt' s = wt (ε.symm s)) :
    IsChart 𝒜 x wt' (((rename ε).restrictScalars O).comp φ) where
  graded j f hf n hn := by
    show coeff n (rename ε (φ f)) = 0
    rw [chart_add_coeff]
    refine h.graded j f hf _ ?_
    rwa [chart_add_weight, ← funext hw]
  const f := by
    show constantCoeff (rename ε (φ f)) = _
    rw [constantCoeff_rename, h.const]
  onto i := by
    obtain ⟨f, h1, h2⟩ := h.onto (ε.symm i)
    refine ⟨f, ?_, fun i' hi' => ?_⟩
    · show coeff _ (rename ε (φ f)) ≠ 0
      rwa [chart_add_coeff, Finsupp.mapDomain_single]
    · show coeff _ (rename ε (φ f)) = 0
      rw [chart_add_coeff, Finsupp.mapDomain_single]
      exact h2 _ fun h3 => hi' (ε.symm.injective h3)
  inj f hx hf := by
    refine h.inj f hx fun i => ?_
    have h1 : coeff _ (rename ε (φ f)) = 0 := hf (ε i)
    rwa [chart_add_coeff, Finsupp.mapDomain_single, ε.symm_apply_apply] at h1

private def chart_add_equiv (F : Bool → Type) : (Σ v, F v) ≃ F true ⊕ F false where
  toFun
    | ⟨true, s⟩ => .inl s
    | ⟨false, s⟩ => .inr s
  invFun
    | .inl s => ⟨true, s⟩
    | .inr s => ⟨false, s⟩
  left_inv
    | ⟨true, _⟩ => rfl
    | ⟨false, _⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

private def chart_add_fam (A B : Type) : Bool → Type := fun v => Bool.rec B A v

/- English proof (translation)
Introduce `O X R _ _ _ _ iR aR W h τ fτ wt φ hφ R' _ _ W' τ' fτ' e hwt hker`. Set `W0 : WPres O X (MvPowerSeries τ' O)` to `WPres.free O fun s : τ' => W'.wt (e (.inr s))`. Establish `h0 : W0.HasOrigin` using `fun f hf => by`. Establish `: f = 0` using `hf`. Rewrite using `[this, map_zero]`.

Take `⟨φ0, hφ0, hz0⟩` from `chart_free O X (MvPowerSeries τ' O) W0 h0 Function.injective_id`. Set `B : Bool → Type` to `chart_add_fam R (MvPowerSeries τ' O)`. Use `letI iB : ∀ v : Bool, CommRing (B v) := fun v => Bool.rec (motive := fun v : Bool => CommRing (B v)) (inferInstance : CommRing (MvPowerSeries τ' O)) iR v`. Use `letI aB : ∀ v : Bool, Algebra O (B v) := fun v => Bool.rec (motive := fun v : Bool => @Algebra O (B v) _ (iB v).toCommSemiring.toSemiring) (inferInstance : Algebra O (MvPowerSeries τ' O)) aR v`. Set `WB : ∀ v : Bool, WPres O X (B v)` to `fun v => Bool.rec (motive := fun v : Bool => WPres O X (B v)) W0 W v`.

Establish `hB : ∀ v : Bool, (WB v).HasOrigin` using `fun v => Bool.rec (motive := fun v : Bool => (WB v).HasOrigin) h0 h v`. Set `F : Bool → Type` to `chart_add_fam τ τ'`. Use `letI fF : ∀ v : Bool, Fintype (F v) := fun v => Bool.rec (motive := fun v : Bool => Fintype (F v)) fτ' fτ v`. Set `wF : ∀ v : Bool, F v → X` to `fun v => Bool.rec (motive := fun v : Bool => F v → X) W0.wt wt v`. Set `φF : ∀ v : Bool, B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)` to `fun v => Bool.rec (motive := fun v : Bool => B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)) φ0 φ v`.

Establish `hF : ∀ v : Bool, IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)` using `fun v => Bool.rec (motive := fun v : Bool => IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)) hφ0 hφ v`. Set `e' : (Σ v, (WB v).σ) ≃ W'.σ` to `(chart_add_equiv fun v => (WB v).σ).trans e`. Take `⟨h', ψ, hψ, hz⟩` from `chart_sum O X Bool B WB hB F wF φF hF R' W' e' (fun v => Bool.rec (motive := fun v : Bool => ∀ s, W'.wt (e' ⟨v, s⟩) = (WB v).wt s) (fun _ => rfl) hwt v) (by`. Rewrite using `[iSup_bool_eq, hker]`. Establish `h1 : RingHom.ker (WB false).π = ⊥` using `(RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id`.

Rewrite using `[h1, Ideal.map_bot, sup_bot_eq]`. Use the proof step `rfl)`. Set `ε : (Σ v, F v) ≃ τ ⊕ τ'` to `chart_add_equiv F`. Use `⟨h', ((rename ε).restrictScalars O).comp ψ, chart_add_rename hψ ε _ ?_, fun s => ?_, fun s => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro (s | s) <;> rfl`.

Establish `h1` using `congrArg (rename ε) (hz true s)`. Rewrite `h1` using `[rename_rename]`. Conclude with `h1`. Establish `h1` using `congrArg (rename ε) (hz false s)`. Rewrite `h1` using `[rename_rename]`.

Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : φF false ((WB false).z s) = MvPowerSeries.X s` using `hz0 s`. Rewrite using `[h2]`. Conclude with `rename_X _ _`.
-/
theorem UpperTheory.V.Alg.chart_add :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (W' : WPres O X R') (τ' : Type) [Fintype τ'] (e : W.σ ⊕ τ' ≃ W'.σ), (∀ s, W'.wt (e (.inl s)) = W.wt s) →
      RingHom.ker W'.π = (RingHom.ker W.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
      ∃ (h' : W'.HasOrigin) (ψ : R' →ₐ[O] MvPowerSeries (τ ⊕ τ') (FractionRing O)), IsChart W'.part (W'.origin h') (Sum.elim wt fun s => W'.wt (e (.inr s))) ψ ∧
        (∀ s, ψ (W'.z (e (.inl s))) = MvPowerSeries.rename Sum.inl (φ (W.z s))) ∧ ∀ s, ψ (W'.z (e (.inr s))) = MvPowerSeries.X (.inr s) := by
  intro O X R _ _ _ _ iR aR W h τ fτ wt φ hφ R' _ _ W' τ' fτ' e hwt hker
  let W0 : WPres O X (MvPowerSeries τ' O) := WPres.free O fun s : τ' => W'.wt (e (.inr s))
  have h0 : W0.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  obtain ⟨φ0, hφ0, hz0⟩ := chart_free O X (MvPowerSeries τ' O) W0 h0 Function.injective_id
  let B : Bool → Type := chart_add_fam R (MvPowerSeries τ' O)
  letI iB : ∀ v : Bool, CommRing (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => CommRing (B v)) (inferInstance : CommRing (MvPowerSeries τ' O)) iR v
  letI aB : ∀ v : Bool, Algebra O (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => @Algebra O (B v) _ (iB v).toCommSemiring.toSemiring) (inferInstance : Algebra O (MvPowerSeries τ' O)) aR v
  let WB : ∀ v : Bool, WPres O X (B v) := fun v => Bool.rec (motive := fun v : Bool => WPres O X (B v)) W0 W v
  have hB : ∀ v : Bool, (WB v).HasOrigin := fun v => Bool.rec (motive := fun v : Bool => (WB v).HasOrigin) h0 h v
  let F : Bool → Type := chart_add_fam τ τ'
  letI fF : ∀ v : Bool, Fintype (F v) := fun v => Bool.rec (motive := fun v : Bool => Fintype (F v)) fτ' fτ v
  let wF : ∀ v : Bool, F v → X := fun v => Bool.rec (motive := fun v : Bool => F v → X) W0.wt wt v
  let φF : ∀ v : Bool, B v →ₐ[O] MvPowerSeries (F v) (FractionRing O) := fun v =>
    Bool.rec (motive := fun v : Bool => B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)) φ0 φ v
  have hF : ∀ v : Bool, IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v) := fun v =>
    Bool.rec (motive := fun v : Bool => IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)) hφ0 hφ v
  let e' : (Σ v, (WB v).σ) ≃ W'.σ := (chart_add_equiv fun v => (WB v).σ).trans e
  obtain ⟨h', ψ, hψ, hz⟩ := chart_sum O X Bool B WB hB F wF φF hF R' W' e'
    (fun v => Bool.rec (motive := fun v : Bool => ∀ s, W'.wt (e' ⟨v, s⟩) = (WB v).wt s) (fun _ => rfl) hwt v) (by
      rw [iSup_bool_eq, hker]
      have h1 : RingHom.ker (WB false).π = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
      rw [h1, Ideal.map_bot, sup_bot_eq]
      rfl)
  let ε : (Σ v, F v) ≃ τ ⊕ τ' := chart_add_equiv F
  refine ⟨h', ((rename ε).restrictScalars O).comp ψ, chart_add_rename hψ ε _ ?_, fun s => ?_, fun s => ?_⟩
  · rintro (s | s) <;> rfl
  · have h1 := congrArg (rename ε) (hz true s)
    rw [rename_rename] at h1
    exact h1
  · have h1 := congrArg (rename ε) (hz false s)
    rw [rename_rename] at h1
    refine h1.trans ?_
    have h2 : φF false ((WB false).z s) = MvPowerSeries.X s := hz0 s
    rw [h2]
    exact rename_X _ _
