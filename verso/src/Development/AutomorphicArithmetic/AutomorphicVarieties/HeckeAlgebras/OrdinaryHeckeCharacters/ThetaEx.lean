import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨c, hc⟩` from `(glBridge k 1 ℂ 1).2.2.2.1 (W.comap Matrix.GeneralLinearGroup.det) (hW.preimage Matrix.GeneralLinearGroup.continuous_det)`. Use `⟨c, fun d hd => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `h1 : (u : 𝒪[k]) - 1 ∈ maximalIdeal 𝒪[k] ^ c` using `Ideal.pow_le_pow_right hd (Ideal.Quotient.eq.1 (congrArg Units.val hu))`. Establish `h2` using `hc (x := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin 1) fun _ => u)) ⟨_, by`.

Use extensionality with `i j`. Rewrite using `[Subsingleton.elim j i]`. Simplify `Ideal.Quotient.eq.2 h1, rfl⟩` using `[val_diagT]`. Use `Subgroup.mem_comap.1 h2 using 1` and compare the differences between its conclusion and the goal. Use `ext`.

Simplify using `[val_diagT]`.
-/
private theorem th_Uc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (W : Subgroup kˣ) (hW : IsOpen (W : Set kˣ)) : ∃ c, ∀ d, c ≤ d → Uc k d ≤ W := by
  obtain ⟨c, hc⟩ := (glBridge k 1 ℂ 1).2.2.2.1 (W.comap Matrix.GeneralLinearGroup.det)
    (hW.preimage Matrix.GeneralLinearGroup.continuous_det)
  refine ⟨c, fun d hd => ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (u : 𝒪[k]) - 1 ∈ maximalIdeal 𝒪[k] ^ c :=
    Ideal.pow_le_pow_right hd (Ideal.Quotient.eq.1 (congrArg Units.val hu))
  have h2 := hc (x := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin 1) fun _ => u))
    ⟨_, by
      ext i j
      rw [Subsingleton.elim j i]
      simpa [val_diagT] using Ideal.Quotient.eq.2 h1, rfl⟩
  convert Subgroup.mem_comap.1 h2 using 1
  ext
  simp [val_diagT]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

/- English proof (translation)
Use `choose φ hφ using fun b : {b : B // b ≠ 1} => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity B ℂ b.2`. Use `choose χ hχ e using fun b => ha.factor ((φ b).comp f) (hf.of_le fun σ hσ => by simp [hσ])`. Take `⟨c, hc⟩` from `th_Uc (⨅ b, (χ b).ker) (by`. Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite hχ)`.

Use `⟨c, fun d hd σ hσ => by_contra fun h1 => hφ ⟨_, h1⟩ ?_⟩` and prove the remaining obligations. Conclude with `(DFunLike.congr_fun (e ⟨_, h1⟩) σ).trans (Subgroup.mem_iInf.1 (hc d hd hσ) _)`.
-/
private theorem th_fin (ha : IsLocalArtin h a) {B : Type} [CommGroup B] [Finite B] (f : Weil h →* B)
    (hf : GlobalTheory.WeilDeligne.IsSmooth f) : ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → f σ = 1 := by
  choose φ hφ using fun b : {b : B // b ≠ 1} => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity B ℂ b.2
  choose χ hχ e using fun b => ha.factor ((φ b).comp f) (hf.of_le fun σ hσ => by simp [hσ])
  obtain ⟨c, hc⟩ := th_Uc (⨅ b, (χ b).ker) (by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hχ)
  refine ⟨c, fun d hd σ hσ => by_contra fun h1 => hφ ⟨_, h1⟩ ?_⟩
  exact (DFunLike.congr_fun (e ⟨_, h1⟩) σ).trans (Subgroup.mem_iInf.1 (hc d hd hσ) _)

/- English proof (translation)
Set `f` to `ψ.comp (Subgroup.inclusion (Weil_le_Dec h))`. Establish `key : ∀ N, ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → (f σ : R) - 1 ∈ maximalIdeal R ^ N` using `fun N => by haveI : Finite (R ⧸ maximalIdeal R) := IsCNL.finite haveI : Finite (R ⧸ maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N`. Take `⟨c, hc⟩` from `th_fin ha ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom).comp f) (by`. Use `((hψ N).comp_continuous (f := fun σ : Ine (F := F) A => Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) (continuous_subtype_val.subtype_mk _)) {1}` as an intermediate fact. Conclude with `(congrArg IsOpen (Set.ext fun σ => Units.ext_iff)).mpr this)`.

Conclude with `⟨c, fun d hd σ hσ => Ideal.Quotient.eq.1 (congrArg Units.val (hc d hd σ hσ))⟩`. Establish `hk : a.ker ≤ f.ker` using `fun σ hσ => by`. Use `Units.ext (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R).2 fun N => ?_)` and prove the remaining obligations. Take `⟨c, hc⟩` from `key N`. Rewrite using `[smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`.

Conclude with `hc c le_rfl σ (by rw [show a σ = 1 from hσ]; exact one_mem _)`. Establish `hf : ∀ x, a.liftOfSurjective ha.surj ⟨f, hk⟩ (a x) = f x` using `fun x => MonoidHom.liftOfRightInverse_comp_apply a _ _ ⟨f, hk⟩ x`. Use `⟨a.liftOfSurjective ha.surj ⟨f, hk⟩, fun x g e => (hf x).trans (congrArg ψ (Subtype.ext e.symm)), fun N => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `key N`. Use `⟨c, fun d hd y hy => ?_⟩` and prove the remaining obligations.

Take `⟨σ, rfl⟩` from `ha.surj y`. Rewrite using `[hf]`. Conclude with `hc d hd σ hy`.
-/
private theorem th_char (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ, (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → χ (a x) = ψ g) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  let f := ψ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have key : ∀ N, ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → (f σ : R) - 1 ∈ maximalIdeal R ^ N := fun N => by
    haveI : Finite (R ⧸ maximalIdeal R) := IsCNL.finite
    haveI : Finite (R ⧸ maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    obtain ⟨c, hc⟩ := th_fin ha ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom).comp f) (by
      have := ((hψ N).comp_continuous (f := fun σ : Ine (F := F) A => Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ))
        (continuous_subtype_val.subtype_mk _)) {1}
      exact (congrArg IsOpen (Set.ext fun σ => Units.ext_iff)).mpr this)
    exact ⟨c, fun d hd σ hσ => Ideal.Quotient.eq.1 (congrArg Units.val (hc d hd σ hσ))⟩
  have hk : a.ker ≤ f.ker := fun σ hσ => by
    refine Units.ext (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R).2 fun N => ?_)
    obtain ⟨c, hc⟩ := key N
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact hc c le_rfl σ (by rw [show a σ = 1 from hσ]; exact one_mem _)
  have hf : ∀ x, a.liftOfSurjective ha.surj ⟨f, hk⟩ (a x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply a _ _ ⟨f, hk⟩ x
  refine ⟨a.liftOfSurjective ha.surj ⟨f, hk⟩, fun x g e => (hf x).trans (congrArg ψ (Subtype.ext e.symm)), fun N => ?_⟩
  obtain ⟨c, hc⟩ := key N
  refine ⟨c, fun d hd y hy => ?_⟩
  obtain ⟨σ, rfl⟩ := ha.surj y
  rw [hf]
  exact hc d hd σ hy

/- English proof (translation)
Introduce `N` and use `by refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_ have ho : IsOpen {y : Γ | ‖e y - e x‖ < (l : ℝ) ^ (-(N : ℤ))} := isOpen_lt (by fun_prop) continuous_const have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos filter_upwards [ho.mem_nhds (by simpa using p …`.
-/
private theorem th_eps {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] {l : ℕ} [Fact l.Prime]
    (j : ℤ_[l] →+* R) [IsLocalHom j] {e : Γ → ℤ_[l]} (he : Continuous e) :
    Alg.AdicCont (maximalIdeal R) fun g => j (e g) := fun N => by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have ho : IsOpen {y : Γ | ‖e y - e x‖ < (l : ℝ) ^ (-(N : ℤ))} :=
    isOpen_lt (by fun_prop) continuous_const
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  filter_upwards [ho.mem_nhds (by simpa using pow_pos hl N)] with y hy
  refine Ideal.Quotient.eq.2 ?_
  have h1 : e y - e x ∈ maximalIdeal ℤ_[l] ^ N := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hy.le
  rw [← map_sub]
  refine Ideal.pow_right_mono (I := (maximalIdeal ℤ_[l]).map j) ?_ N ?_
  · exact Ideal.map_le_iff_le_comap.2 fun z hz => map_nonunit j z hz
  · rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h1

/- English proof (translation)
Introduce `N` and use `by simp only [map_mul, map_pow] exact (hf N).mul ((hg N).comp (· ^ i))`.
-/
private theorem th_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (i : ℕ) : Alg.AdicCont I fun x => f x * g x ^ i := fun N => by
  simp only [map_mul, map_pow]
  exact (hf N).mul ((hg N).comp (· ^ i))

/- English proof (translation)
Establish `hi : Function.Injective (diagT k (Fin n))` using `fun s t e => by`. Use `congrArg Units.val e` as an intermediate fact. Rewrite `this` using `[val_diagT, val_diagT]`. Conclude with `funext fun i => Units.ext (congrFun (Matrix.diagonal_injective this) i)`. Set `D : (glIwa k n).T →* (Fin n → kˣ)` to `(MonoidHom.ofInjective hi).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)`.

Establish `hD : ∀ t, diagT k (Fin n) (D t) = t` using `fun t => MonoidHom.apply_ofInjective_symm hi _`. Use `⟨D, fun i y => hi (hD _), fun c t ht i => ?_⟩` and prove the remaining obligations. Take `⟨y, e, hy⟩` from `(glBridge k n ℂ 1).2.2.2.2.2.2.2.2.2 t`. Establish `e2 : D t = fun i => (y i : kˣ)` using `hi <| by`. Rewrite using `[hD, e]`.

Use `show (List.ofFn (diagT k (Fin n) ∘ fun i => Pi.mulSingle i (y i : kˣ))).prod = _`. Rewrite using `[← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]`. Rewrite using `[e2]`. Conclude with `hy c ht i`.
-/
private theorem th_diag (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ D : (glIwa k n).T →* (Fin n → kˣ), (∀ i y, D (eT k n i y) = Pi.mulSingle i (y : kˣ)) ∧
      ∀ c (t : (glIwa k n).T), (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, D t i ∈ Uc k (c + 1) := by
  have hi : Function.Injective (diagT k (Fin n)) := fun s t e => by
    have := congrArg Units.val e
    rw [val_diagT, val_diagT] at this
    exact funext fun i => Units.ext (congrFun (Matrix.diagonal_injective this) i)
  let D : (glIwa k n).T →* (Fin n → kˣ) :=
    (MonoidHom.ofInjective hi).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)
  have hD : ∀ t, diagT k (Fin n) (D t) = t := fun t => MonoidHom.apply_ofInjective_symm hi _
  refine ⟨D, fun i y => hi (hD _), fun c t ht i => ?_⟩
  obtain ⟨y, e, hy⟩ := (glBridge k n ℂ 1).2.2.2.2.2.2.2.2.2 t
  have e2 : D t = fun i => (y i : kˣ) := hi <| by
    rw [hD, e]
    show (List.ofFn (diagT k (Fin n) ∘ fun i => Pi.mulSingle i (y i : kˣ))).prod = _
    rw [← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  rw [e2]
  exact hy c ht i

/- English proof (translation)
Take `⟨χ, h1, h2⟩` from `th_char ha (ψ * ε ^ i)⁻¹ fun N => by`. Use `(congrArg IsLocallyConstant (funext fun g => ?_)).mpr ((th_mul hψ hε i N).comp_continuous continuous_inv)` and prove the remaining obligations. Use `congrArg (Ideal.Quotient.mk _) ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.inv_apply, ← map_inv]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]`.

Conclude with `⟨χ, fun x g e => by rw [h1 x g e]; exact mul_inv_cancel _, h2⟩`.
-/
private theorem th_char' (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ ε : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) (hε : Alg.AdicCont (maximalIdeal R) fun g => (ε g : R)) (i : ℕ) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ,
      (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → ψ g * ε g ^ i * χ (a x) = 1) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  obtain ⟨χ, h1, h2⟩ := th_char ha (ψ * ε ^ i)⁻¹ fun N => by
    refine (congrArg IsLocallyConstant (funext fun g => ?_)).mpr ((th_mul hψ hε i N).comp_continuous continuous_inv)
    refine congrArg (Ideal.Quotient.mk _) ?_
    simp only [MonoidHom.inv_apply, ← map_inv]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  exact ⟨χ, fun x g e => by rw [h1 x g e]; exact mul_inv_cancel _, h2⟩

/- English proof (translation)
Use `choose D hD hDc using fun v => th_diag ((S v).adicCompletion F) n`. Set `p : ∀ v, (iwS n S).T →* (glIwa ((S v).adicCompletion F) n).T` to `fun v => ((Pi.evalMonoidHom (fun v => GLw n (S v)) v).comp (iwS n S).T.subtype).codRestrict _ fun t => t.2 v trivial`. Set `θ : (iwS n S).T →* Rˣ` to `∏ v, ∏ i, (χ v i).comp ((Pi.evalMonoidHom _ i).comp ((D v).comp (p v)))`. Establish `hθ : ∀ t, θ t = ∏ v, ∏ i, χ v i (D v (p v t) i)` using `fun t => by`. Simplify using `only [θ, MonoidHom.finset_prod_apply]`.

Both sides reduce to the same expression. Use `⟨θ, fun v i y => ?_, fun N => ?_⟩` and prove the remaining obligations. Establish `e : D v (p v (eV n S v i y)) = Pi.mulSingle i (y : ((S v).adicCompletion F)ˣ)` using `(congrArg (D v) (Subtype.ext (Pi.mulSingle_eq_same (M := fun v => GLw n (S v)) _ _))).trans (hD v i y)`. Rewrite using `[hθ, Finset.prod_eq_single v, Finset.prod_eq_single i]`. Rewrite using `[e, Pi.mulSingle_eq_same]`.

Introduce `j _ hj`. Rewrite using `[e, Pi.mulSingle_eq_of_ne hj, map_one]`. Simplify using the standard rewrite rules. Introduce `v' _ hv`. Rewrite using `[show p v' (eV n S v i y) = 1 from Subtype.ext (Pi.mulSingle_eq_of_ne (M := fun v => GLw n (S v)) hv _)]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use `choose d hd using fun x : V × Fin n => hc x.1 x.2 N`. Use `⟨Finset.univ.sup d, fun t ht => ?_⟩` and prove the remaining obligations. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations.

Rewrite using `[hθ]`. Simplify using `only [Units.coe_prod, map_prod, map_one]`. Use `Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq.2 (hd (v, i) _ ((Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)) _ (hDc v _ (p v t) (ht v trivial) i))`.
-/
private theorem th_torus (n : ℕ) {V : Type} [Fintype V] (S : V → Plc F) {R : Type} [CommRing R] [IsLocalRing R]
    (χ : ∀ v, Fin n → ((S v).adicCompletion F)ˣ →* Rˣ)
    (hc : ∀ v i N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ v i y : R) - 1 ∈ maximalIdeal R ^ N) :
    ∃ θ : (iwS n S).T →* Rˣ, (∀ v i y, θ (eV n S v i y) = χ v i y) ∧ (iwS n S).ContChar θ := by
  classical
  choose D hD hDc using fun v => th_diag ((S v).adicCompletion F) n
  let p : ∀ v, (iwS n S).T →* (glIwa ((S v).adicCompletion F) n).T := fun v =>
    ((Pi.evalMonoidHom (fun v => GLw n (S v)) v).comp (iwS n S).T.subtype).codRestrict _ fun t => t.2 v trivial
  let θ : (iwS n S).T →* Rˣ := ∏ v, ∏ i, (χ v i).comp ((Pi.evalMonoidHom _ i).comp ((D v).comp (p v)))
  have hθ : ∀ t, θ t = ∏ v, ∏ i, χ v i (D v (p v t) i) := fun t => by
    simp only [θ, MonoidHom.finset_prod_apply]
    rfl
  refine ⟨θ, fun v i y => ?_, fun N => ?_⟩
  · have e : D v (p v (eV n S v i y)) = Pi.mulSingle i (y : ((S v).adicCompletion F)ˣ) :=
      (congrArg (D v) (Subtype.ext (Pi.mulSingle_eq_same (M := fun v => GLw n (S v)) _ _))).trans (hD v i y)
    rw [hθ, Finset.prod_eq_single v, Finset.prod_eq_single i]
    · rw [e, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [e, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
    · intro v' _ hv
      rw [show p v' (eV n S v i y) = 1 from Subtype.ext (Pi.mulSingle_eq_of_ne (M := fun v => GLw n (S v)) hv _)]
      simp
    · simp
  · choose d hd using fun x : V × Fin n => hc x.1 x.2 N
    refine ⟨Finset.univ.sup d, fun t ht => ?_⟩
    refine Ideal.Quotient.eq.1 ?_
    rw [hθ]
    simp only [Units.coe_prod, map_prod, map_one]
    refine Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun i _ => ?_
    exact Ideal.Quotient.eq.2 (hd (v, i) _ ((Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)) _
      (hDc v _ (p v t) (ht v trivial) i))

/- English proof (translation)
Introduce `g γ u hu b hb e`. Take `⟨rfl, rfl⟩` from `hU g γ u hu b hb e`. Use `⟨one_mem _, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[show (⟨1, one_mem _⟩ : X.I.T) = 1 from rfl, map_one, map_one]`. Simplify using the standard rewrite rules.
-/
private theorem th_free {Γ Ga Gp A : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) {U : Subgroup X.Ub} (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  rw [show (⟨1, one_mem _⟩ : X.I.T) = 1 from rfl, map_one, map_one]
  simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ r Λ`. Use `haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1`. Use `haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (abelian₂.dvr_finite l c.O).2.2.2.2.2`. Use `haveI : IsCNL Λ.Λ := IsCNL.ofCO c.O Λ.Λ`. Use `choose ψ hψ hκ using Λ.inert`.

Establish `ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1))` using `fun v => Classical.epsilon_spec (Loc.localArtinReciprocity H (s.hw v.1))`. Use `choose χ hχ hc using fun (v : V.frame.Vl) (i : Fin n) => th_char' (ha v) (ψ v i) ((hset Q τ₀).epsV Λ.Λ v) (hψ v i).cont (th_eps ((algebraMap c.O Λ.Λ).comp (algebraMap ℤ_[l] c.O)) (e := fun g : Dec (F := L) (s.A v.1) => (cycZ L Ω l g : ℤ_[l])) (Units.continuous_val.comp ((continuo …`. Take `⟨θ, h1, h2⟩` from `th_torus n (fun v : V.frame.Vl => s.w v.1) χ hc`. Use `⟨θ, fun v i x g hg y e1 e2 => ?_, h2, fun K => th_free _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩` and prove the remaining obligations. Establish `e3` using `hχ v i x g e1`.

Rewrite `e3` using `[e2, ← h1]`. Rewrite using `[hκ]`. Conclude with `e3`.
-/
theorem UpperTheory.V.Hi.thetaEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (Λ : LamObj r), ∃ θ : (hset Q τ₀).X.I.T →* Λ.Λˣ, IsTheta Q τ₀ Λ θ ∧ (hset Q τ₀).IsWt θ := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ r Λ
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (abelian₂.dvr_finite l c.O).2.2.2.2.2
  haveI : IsCNL Λ.Λ := IsCNL.ofCO c.O Λ.Λ
  choose ψ hψ hκ using Λ.inert
  have ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (Loc.localArtinReciprocity H (s.hw v.1))
  choose χ hχ hc using fun (v : V.frame.Vl) (i : Fin n) =>
    th_char' (ha v) (ψ v i) ((hset Q τ₀).epsV Λ.Λ v) (hψ v i).cont
      (th_eps ((algebraMap c.O Λ.Λ).comp (algebraMap ℤ_[l] c.O))
        (e := fun g : Dec (F := L) (s.A v.1) => (cycZ L Ω l g : ℤ_[l]))
        (Units.continuous_val.comp ((continuous_cycZ L Ω l).comp continuous_subtype_val))) i
  obtain ⟨θ, h1, h2⟩ := th_torus n (fun v : V.frame.Vl => s.w v.1) χ hc
  refine ⟨θ, fun v i x g hg y e1 e2 => ?_, h2, fun K => th_free _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  have e3 := hχ v i x g e1
  rw [e2, ← h1] at e3
  rw [hκ]
  exact e3
