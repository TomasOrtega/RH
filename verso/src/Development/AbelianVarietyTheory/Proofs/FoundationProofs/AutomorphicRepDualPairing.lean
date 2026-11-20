import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleEquivariantProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutRepUSpanValues
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S]

def forms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

variable (E n S) in

def post : Representation ℂ (finU E n) (S →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem post_apply (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ)) (v : S) :
    post E n S k f v = RU E n k (f v) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by rw [post_apply, post_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩`.
-/
theorem post_mem (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ))
    (h : f ∈ forms ρ) : post E n S k f ∈ forms ρ :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [post_apply, post_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def rep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU E n) (forms ρ) :=
  GlobalTheory.PRep.sub (post E n S) (forms ρ) (post_mem ρ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rep_val (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : forms ρ) :
    (rep ρ k f).1 = post E n S k f.1 := rfl

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

def ev (ρ : Representation ℂ (infU E n) S) (v : S) : forms ρ →ₗ[ℂ] autU E n where
  toFun f := ⟨f.1 v, f.2.1 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def form (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) :
    forms ρ →ₗ⋆[ℂ] forms ρ →ₗ[ℂ] ℂ :=
  ∑ i, (B.comp (ev ρ (Module.finBasis ℂ S i))).compl₂ (ev ρ (Module.finBasis ℂ S i))

/- English proof (translation)
Simplify using `[form, LinearMap.sum_apply]`.
-/
theorem form_apply (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) :
    form B ρ f g = ∑ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g) := by
  simp [form, LinearMap.sum_apply]

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

/- English proof (translation)
Rewrite using `[form_apply, form_apply, star_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hh _ _`.
-/
theorem form_herm (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) : star (form B ρ f g) = form B ρ g f := by
  rw [form_apply, form_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hh _ _

/- English proof (translation)
Rewrite using `[form_apply, Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun i _ => hp _`.
-/
theorem form_nonneg (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hp : ∀ v, 0 ≤ (B v v).re)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) : 0 ≤ (form B ρ f f).re := by
  rw [form_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hp _

/- English proof (translation)
Rewrite `h0` using `[form_apply]`. Establish `hre : ∑ i, (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).re = 0`. Rewrite using `[← Complex.re_sum, h0, Complex.zero_re]`. Establish `hz : ∀ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f) = 0`. Introduce `i`.

Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _)).1 hre i (Finset.mem_univ i)`. Establish `h2 : (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).im = 0`. Use `congrArg Complex.im (hh (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f))` as an intermediate fact. Rewrite `this` using `[Complex.star_def, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `Complex.ext h1 h2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `(Module.finBasis ℂ S).ext fun i => ?_` and prove the remaining obligations. Use `congrArg Subtype.val (hd _ (hz i))` as an intermediate fact. Simplify `this` using `[ev]`.
-/
theorem form_def (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) (h0 : form B ρ f f = 0) : f = 0 := by
  rw [form_apply] at h0
  have hre : ∑ i, (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).re = 0 := by
    rw [← Complex.re_sum, h0, Complex.zero_re]
  have hz : ∀ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f) = 0 := by
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _)).1 hre i (Finset.mem_univ i)
    have h2 : (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).im = 0 := by
      have := congrArg Complex.im (hh (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f))
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext h1 h2
  apply Subtype.ext
  refine (Module.finBasis ℂ S).ext fun i => ?_
  have := congrArg Subtype.val (hd _ (hz i))
  simpa [ev] using this

/- English proof (translation)
Rewrite using `[form_apply, form_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `hi (k : UA E n) (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g)`.
-/
theorem form_inv (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ)
    (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f g : forms ρ) :
    form B ρ (rep ρ k f) (rep ρ k g) = form B ρ f g := by
  rw [form_apply, form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hi (k : UA E n) (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g)

/- English proof (translation)
Set `b` to `Module.finBasis ℂ S`. Use `isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Rewrite using `[Set.mem_iInter]`. Conclude with `⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩`.
-/
theorem rep_smooth (ρ : Representation ℂ (infU E n) S) (f : forms ρ) :
    IsOpen {k : finU E n | rep ρ k f = f} := by
  let b := Module.finBasis ℂ S
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

/- English proof (translation)
Establish `hM` using `GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms E n S ρ K hK ((GlobalTheory.PRep.fixed (rep ρ) K).map (forms ρ).subtype) (by`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩` and prove the remaining obligations. Establish `h1 : rep ρ k g = g`. Use `hg ⟨k, hk⟩` as an intermediate fact.

Rewrite `this` using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `this`. Conclude with `LinearMap.congr_fun (congrArg Subtype.val h1) v)`. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (forms ρ).injective_subtype _).symm`.
-/
theorem rep_fd (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (rep ρ) K) := by
  have hM := GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms E n S ρ K hK ((GlobalTheory.PRep.fixed (rep ρ) K).map (forms ρ).subtype) (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩
    have h1 : rep ρ k g = g := by
      have := hg ⟨k, hk⟩
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this
      exact this
    exact LinearMap.congr_fun (congrArg Subtype.val h1) v)
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (forms ρ).injective_subtype _).symm

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

/- English proof (translation)
Introduce `E _ _ _ n B hh hp hd hi S _ _ _ ρ hsp f hf0 hfa hfe`. Establish `hfA : f ∈ forms ρ` using `⟨fun v => hfa v, hfe⟩`. Establish `hx : (⟨f, hfA⟩ : forms ρ) ≠ 0` using `fun h => hf0 (congrArg Subtype.val h)`. Take `⟨U, P, hU0, hUst, hUirr, hPU, hPeq, hPx⟩` from `GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection (finU E n) (forms ρ) (rep ρ) (form B ρ) (form_herm B hh ρ) (form_nonneg B hp ρ) (form_def B hh hp hd ρ) (form_inv B hi ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) …`. Set `M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ))` to `U.map (forms ρ).subtype`.

Establish `hM0 : M ≠ ⊥`. Introduce `h`. Apply `hU0` to reduce the goal to its premises. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `u hu`.

Establish `: u.1 ∈ M` using `⟨u, hu, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Establish `hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v)`. Introduce and unpack `_ ⟨u, -, rfl⟩`.

Conclude with `⟨fun v => u.2.1 v, u.2.2⟩`. Establish `hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M`. Introduce and unpack `k hk _ ⟨u, hu, rfl⟩`. Conclude with `⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩`. Establish `hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M`.

Introduce `N hNM hN`. Set `N' : Submodule ℂ (forms ρ)` to `N.comap (forms ρ).subtype`. Establish `hN'U : N' ≤ U`. Introduce `u hu`. Take `⟨w, hw, hwu⟩` from `hNM hu`.

Rewrite using `[← Subtype.ext hwu]`. Conclude with `hw`. Establish `hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N'` using `fun g u hu => hN g.1 g.2 u.1 hu`. Establish `hNe : N'.map (forms ρ).subtype = N`. Rewrite using `[Submodule.map_comap_subtype]`.

Conclude with `inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))`. Break down `hUirr N' hN'U hN'st with h | h` into its components or cases. Use `left`. Rewrite using `[← hNe, h, Submodule.map_bot]`. Use `right`.

Rewrite using `[← hNe, h]`. Establish `hπ` using `GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n S ρ hsp M hM0 hMf hMk hMirr`. Use `⟨_, hπ, (P ⟨f, hfA⟩).1, fun h => hPx (Subtype.ext h), fun v => Submodule.subset_span ⟨(P ⟨f, hfA⟩).1, ⟨_, hPU _, rfl⟩, v, rfl⟩, (P ⟨f, hfA⟩).2.2, ?_⟩` and prove the remaining obligations. Introduce `κ R s c hs hsum v`. Establish `hA : ∑ i ∈ R.attach, rep ρ ⟨s i.1, hs i.1 i.2⟩ ⟨f, hfA⟩ = c • (⟨f, hfA⟩ : forms ρ)`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply, ← hsum w]`. Conclude with `Finset.sum_attach R (fun i => RU E n (s i) (f w))`. Establish `hB` using `congrArg P hA`.

Rewrite `hB` using `[map_sum, map_smul]`. Simplify using `only [hPeq] at hB`. Use `LinearMap.congr_fun (congrArg Subtype.val hB) v` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply]`. Rewrite using `[← this]`.

Conclude with `(Finset.sum_attach R (fun i => RU E n (s i) ((P ⟨f, hfA⟩).1 v))).symm`.
-/
theorem exists_autRep_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∃ π, IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧ (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ v, ∑ i ∈ R, RU E n (s i) (f v) = c • f v) → ∀ v, ∑ i ∈ R, RU E n (s i) (f' v) = c • f' v := by
  intro E _ _ _ n B hh hp hd hi S _ _ _ ρ hsp f hf0 hfa hfe
  classical
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  have hx : (⟨f, hfA⟩ : forms ρ) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨U, P, hU0, hUst, hUirr, hPU, hPeq, hPx⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection (finU E n) (forms ρ) (rep ρ)
      (form B ρ) (form_herm B hh ρ) (form_nonneg B hp ρ) (form_def B hh hp hd ρ) (form_inv B hi ρ)
      (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ) ⟨f, hfA⟩ hx
  let M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n S ρ hsp M hM0 hMf hMk hMirr
  refine ⟨_, hπ, (P ⟨f, hfA⟩).1, fun h => hPx (Subtype.ext h), fun v => Submodule.subset_span
    ⟨(P ⟨f, hfA⟩).1, ⟨_, hPU _, rfl⟩, v, rfl⟩, (P ⟨f, hfA⟩).2.2, ?_⟩
  intro κ R s c hs hsum v
  have hA : ∑ i ∈ R.attach, rep ρ ⟨s i.1, hs i.1 i.2⟩ ⟨f, hfA⟩ = c • (⟨f, hfA⟩ : forms ρ) := by
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    rw [Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply, ← hsum w]
    exact Finset.sum_attach R (fun i => RU E n (s i) (f w))
  have hB := congrArg P hA
  rw [map_sum, map_smul] at hB
  simp only [hPeq] at hB
  have := LinearMap.congr_fun (congrArg Subtype.val hB) v
  rw [Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply] at this
  rw [← this]
  exact (Finset.sum_attach R (fun i => RU E n (s i) ((P ⟨f, hfA⟩).1 v))).symm

end GlobalTheory.FrameAut.VecProj

end
