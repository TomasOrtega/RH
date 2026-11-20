import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdJac
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

/- English proof (translation)
Use `choose a ha using h`. Set `χ : G →* ℂ` to `{ toFun := a map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm) map_mul' := fun s t => smul_left_injective ℂ hne (by`. Use `ha (s * t)` as an intermediate fact. Rewrite `this` using `[map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm]`. Conclude with `this.symm) }`.

Conclude with `⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩`.
-/
private theorem char_at {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {F : M} (hne : F ≠ 0) (h : ∀ t, ∃ a : ℂ, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t)
        rw [map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩

/- English proof (translation)
Establish `hP : Pi.mulSingle v a ∈ (piIwa I).P` using `fun w _ => by`. Break down `eq_or_ne w v with rfl | h` into its components or cases. Simplify using `using ha`. Simplify `(I w).P.one_mem` using `[Pi.mulSingle_eq_of_ne h]`. Establish `hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N` using `fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu`.

Establish `hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N` using `fun J b y => ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩`. Introduce `F hF`. Take `⟨⟨s, hs, hs'⟩, hsum⟩` from `uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha`. Establish `key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔ u⁻¹ * y v ∈ (I v).Nconj a` using `fun y hy u => by`. Rewrite using `[hc, hc]`.

Use `⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩` and prove the remaining obligations. Break down `eq_or_ne w v with rfl | e` into its components or cases. Simplify using `using h`. Simplify `hy w trivial` using `[Pi.mulSingle_eq_of_ne e]`. Rewrite using `[(hsum s hs hs').2 F fun u hu => hF _ (hN u hu), ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF, Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]`.

Conclude with `Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl`. Introduce `u hu`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `hN w (hs w hw)`. Introduce `y hy`.

Take `⟨u, ⟨hu, hu'⟩, huq⟩` from `hs' (y v) (hy v trivial)`. Use `⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨hw, hw'⟩`. Take `⟨w, hw₁, rfl⟩` from `Finset.mem_image.1 hw`. Rewrite using `[huq w ⟨hw₁, (key y hy w).1 hw'⟩]`.
-/
private theorem uOp_at {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  intro F hF
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]

/- English proof (translation)
Use `Subgroup.map_mono fun u hu => ?_` and prove the remaining obligations. Rewrite `hu`, the goal using `[MonoidHom.mem_ker, Units.ext_iff]`. Conclude with `(Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))`.
-/
private theorem Uc_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, hgen⟩` from `glBridge k n M ρ`. Take `⟨φ, hφ⟩` from `char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by`. Take `⟨y, hy, -⟩` from `hgen t`. Express the relevant statement in the definitionally equal form `∃ a : ℂ, ρ t F = a • F`. Rewrite using `[hy]`.

Use `List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_` and prove the remaining obligations. Introduce and unpack `g g' ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩`. Introduce `g hg`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hg`.

Conclude with `⟨_, hT i (y i)⟩`. Establish `hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y` using `fun i y => by`. Use `smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))` as an intermediate fact. Rewrite `this` using `[Units.val_inv_eq_inv_val, inv_inj]`. Then use the resulting hypothesis. Take `⟨p, hp, hp0⟩` from `isoSep hσ hFY hF0`.

Establish `hpe : p F ∈ (glIwa k n).eig σ.ρ e φ` using `⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu], fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩`. Take `⟨ω, h1, h2, h3, h4⟩` from `hJ k n σ.V σ.ρ σ.smooth σ.irred e φ (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j => ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans ((congrArg p (ha j).2).trans (map_sm …`. Conclude with `⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩`.
-/
private theorem local_exp (hJ : OrdJac) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    {F : M} (hFY : F ∈ Y) (hF0 : F ≠ 0) (e : ℕ) (f : Fin n → Uo k → ℂ)
    (hN : F ∈ fixd ρ (glIwa k n).N) (hNm : F ∈ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (a : ℕ → ℂ)
    (ha : ∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp ρ (al k n (j + 1)) F = a (j + 1) • F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient σ.ρ (PS ω) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧ ∀ j : Fin n, psEig ω (j + 1) = a (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  obtain ⟨p, hp, hp0⟩ := isoSep hσ hFY hF0
  have hpe : p F ∈ (glIwa k n).eig σ.ρ e φ :=
    ⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu],
      fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩
  obtain ⟨ω, h1, h2, h3, h4⟩ := hJ k n σ.V σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j =>
      ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans
        ((congrArg p (ha j).2).trans (map_smul p _ _))⟩
  exact ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩

/- English proof (translation)
Introduce `hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb`. Establish `hN : F ∈ fixd (H.atV d v) (glIwa _ n).N` using `fun u hu => hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)`. Establish `hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e)` using `fun u hu => hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)`. Establish `hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F` using `fun i y => by`. Use `hF.2.2` as an intermediate fact.

Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this`. Conclude with `this v i y`. Establish `hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F = (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F` using `fun j => congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·) (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)`. Establish `hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0` using `fun j h0 => by`. Use `(hb j).2` as an intermediate fact.

Rewrite `this` using `[hop j, h0, inv_zero, zero_smul]`. Conclude with `smul_ne_zero (hb j).1 hF0 this.symm`. Set `a : ℕ → ℂ` to `fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)`. Establish `ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j` using `fun j => by`. Establish `h : (j : ℕ) + 1 - 1 < n` using `by simpa using j.2`.

Simplify using `only [a, dif_pos h]`. Use `congr 2`. Take `⟨ω, h1, h2, h3, h4⟩` from `local_exp (UpperTheory.V.Z.Ord.ordJac hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j => ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, …`. Establish `h` using `(hop j).symm.trans (hb j).2`. Rewrite `h` using `[inv_smul_eq_iff₀ (hl j), smul_smul]`.

Rewrite using `[ha j]`. Conclude with `h⟩`. Conclude with `⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩`.
-/
theorem UpperTheory.V.Z.Ord.ordScal : GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdScal := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb
  classical
  have hN : F ∈ fixd (H.atV d v) (glIwa _ n).N := fun u hu =>
    hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun u hu =>
    hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun i y => by
    have := hF.2.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun j =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·)
      (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)
  have hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0 := fun j h0 => by
    have := (hb j).2
    rw [hop j, h0, inv_zero, zero_smul] at this
    exact smul_ne_zero (hb j).1 hF0 this.symm
  let a : ℕ → ℂ := fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)
  have ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j := fun j => by
    have h : (j : ℕ) + 1 - 1 < n := by simpa using j.2
    simp only [a, dif_pos h]
    congr 2
  obtain ⟨ω, h1, h2, h3, h4⟩ := local_exp (UpperTheory.V.Z.Ord.ordJac hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT
    (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j =>
      ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, by
        have h := (hop j).symm.trans (hb j).2
        rw [inv_smul_eq_iff₀ (hl j), smul_smul] at h
        rw [ha j]
        exact h⟩
  exact ⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩
