import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.CuspRep.LocUniq

/- English proof (translation)
Set `s : Set (Submodule R M)` to `{m | Nonempty (m ≃ₗ[R] S)}`. Establish `: ∀ m : s, IsSimpleModule R m` using `fun m => m.2.elim fun e => IsSimpleModule.congr e`. Establish `e0` using `LinearEquiv.ofInjective g hg`. Establish `: IsSimpleModule R (LinearMap.range g)` using `IsSimpleModule.congr e0.symm`. Establish `hle : LinearMap.range g ≤ sSup s` using `fun x _ => by`.

Use `(iSup_le (a := sSup s) fun f => ?_) (h x)` and prove the remaining obligations. Break down `LinearMap.injective_or_eq_zero f with hf | rfl` into its components or cases. Conclude with `le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩`. Simplify using the standard rewrite rules. Take `⟨m, ⟨e⟩, ⟨e'⟩⟩` from `(LinearMap.range g).linearEquiv_of_le_sSup s hle`.

Conclude with `⟨(e0.trans (e'.trans e)).symm⟩`.
-/
theorem equiv_of_iSup_range {R M S S' : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] [IsSimpleModule R S] [IsSimpleModule R S']
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (g : S' →ₗ[R] M) (hg : Function.Injective g) :
    Nonempty (S ≃ₗ[R] S') := by
  let s : Set (Submodule R M) := {m | Nonempty (m ≃ₗ[R] S)}
  have : ∀ m : s, IsSimpleModule R m := fun m => m.2.elim fun e => IsSimpleModule.congr e
  have e0 := LinearEquiv.ofInjective g hg
  have : IsSimpleModule R (LinearMap.range g) := IsSimpleModule.congr e0.symm
  have hle : LinearMap.range g ≤ sSup s := fun x _ => by
    refine (iSup_le (a := sSup s) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp
  obtain ⟨m, ⟨e⟩, ⟨e'⟩⟩ := (LinearMap.range g).linearEquiv_of_le_sSup s hle
  exact ⟨(e0.trans (e'.trans e)).symm⟩

section Rep

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def isoPart (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

/- English proof (translation)
Use `(iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩`.
-/
theorem isoPart_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ∈ isoPart σ ρ) :
    ρ g x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

/- English proof (translation)
Use `(iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Use `Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ) ⟨v, rfl⟩` and prove the remaining obligations. Conclude with `(congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)`.
-/
theorem isoPart_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ isoPart σ ρ) : T x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ)
    ⟨v, rfl⟩
  exact (congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)

/- English proof (translation)
Establish `hi` using `(Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'`. Take `⟨e⟩` from `equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by`. Establish `hx : ρ.asModuleEquiv x ∈ isoPart σ ρ` using `h ▸ Submodule.mem_top`. Establish `hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap`. Use `iSup_le fun f => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `: Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈ ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f` using `Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩`. Conclude with `this`. Conclude with `hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi`. Conclude with `⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩`.
-/
theorem equiv_of_isoPart (σ : Representation ℂ G W) (σ' : Representation ℂ G W') (ρ : Representation ℂ G V)
    [σ.IsIrreducible] [σ'.IsIrreducible] (h : isoPart σ ρ = ⊤) (f' : σ'.IntertwiningMap ρ) (hf' : f' ≠ 0) :
    Nonempty (σ.Equiv σ') := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'
  obtain ⟨e⟩ := equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by
    have hx : ρ.asModuleEquiv x ∈ isoPart σ ρ := h ▸ Submodule.mem_top
    have hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule,
        LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      have : Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈
          ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f :=
        Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩
      exact this
    exact hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi
  exact ⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)`.
-/
theorem gl_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)

/- English proof (translation)
Use `gl_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[hk, one_mul, mul_one]`.

Rewrite using `[pLoc_locGL_of_ne h, one_mul, mul_one]`.
-/
theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k` from `⟨_, rfl⟩`. Establish `hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1`. Rewrite using `[map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]`. Establish `h1` using `isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by`. Simplify using `only [MonoidHom.comp_apply]`.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)`. Rewrite `h1` using `[MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem isoPart_fin {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (k : GL (Fin a) (Af E)) {x : V}
    (hx : x ∈ isoPart σ (τ.comp (locGL E a w))) : τ k x ∈ isoPart σ (τ.comp (locGL E a w)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
  have hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]
  have h1 := isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by
    simp only [MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)
  rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1

variable [IsTotallyComplex E]

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Conclude with `isoPart_fin π.finPart w σ k hx`. Consider the case `cpt k`. Use `isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 = (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X`. Use `isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1`.
-/
theorem isoPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : π.V}
    (hx : x ∈ isoPart σ (π.locRep w)) : π.op o x ∈ isoPart σ (π.locRep w) := by
  cases o with
  | fin k =>
    exact isoPart_fin π.finPart w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

/- English proof (translation)
Take `⟨f, h0, hf⟩` from `h`. Take `⟨f', h0', hf'⟩` from `h'`. Use `σ.irred` as an intermediate fact. Use `σ'.irred` as an intermediate fact. Use `equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩ fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)` and prove the remaining obligations.

Establish `hi` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Break down `π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1`. Use `absurd (LinearMap.ext fun v => ?_) h0` and prove the remaining obligations.

Establish `h2 : isoPart σ.ρ (π.locRep w) = ⊥` using `hi (h1.trans (Submodule.map_bot _).symm)`. Establish `h3 : f v ∈ isoPart σ.ρ (π.locRep w)` using `Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩`. Rewrite `h3` using `[h2]`. Conclude with `h3`. Conclude with `hi (h1.trans (Submodule.map_subtype_top _).symm)`.
-/
theorem isLocComp_unique (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : π.IsLocComp w σ) (h' : π.IsLocComp w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨f', h0', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  refine equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩
    fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1
  · refine absurd (LinearMap.ext fun v => ?_) h0
    have h2 : isoPart σ.ρ (π.locRep w) = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    have h3 : f v ∈ isoPart σ.ρ (π.locRep w) :=
      Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩
    rw [h2] at h3
    exact h3
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.CuspRep.LocUniq

/- English proof (translation)
Introduce `E _ _ _ a π w σ σ' h h'`. Proceed by induction on `π using Quotient.inductionOn`. Proceed by induction on `σ using Quotient.inductionOn`. Proceed by induction on `σ' using Quotient.inductionOn`. Conclude with `Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')`.
-/
theorem GlobalTheory.CuspRep.CG.IsLoc.unique : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin a) (w.adicCompletion E))), π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ a π w σ σ' h h'
  induction π using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  exact Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')
