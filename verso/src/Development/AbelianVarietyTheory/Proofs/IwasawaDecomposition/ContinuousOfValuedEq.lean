import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

/- English proof (translation)
Use `continuous_of_continuousAt_zero f ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]`. Introduce `γ _`. Take `⟨a, ha⟩` from `hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)`. Establish `ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0`.

Simplify using `[ha]`. Use `⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx`. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]`. Rewrite using `[hf, ← ha]`.

Conclude with `hx`.
-/
theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

variable {L : Type} [Field L] [NumberField L]

open scoped WithZeroTopology in

/- English proof (translation)
Establish `hc : Continuous (WithVal.map (v.valuation L) (v'.valuation L) (c : L →+* L))` using `continuous_of_valued_eq (fun γ => by`. Take `⟨k, hk⟩` from `v.valuation_surjective L γ`. Conclude with `⟨WithVal.toVal _ k, hk⟩) _ fun x => h x.ofVal`. Set `φ : v.adicCompletion L →+* v'.adicCompletion L` to `((HeightOneSpectrum.adicCompletion.equiv L v').symm.toRingHom.comp (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom`. Establish `h1 : Continuous φ` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion L v').comp (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))`.

Establish `h2 : ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k)` using `fun k => by`. Apply `HeightOneSpectrum.adicCompletion.ext` to reduce the goal to its premises. Conclude with `UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ k)`. Use `⟨φ, h1, h2, fun x => ?_⟩` and prove the remaining obligations. Use `(HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x (isClosed_eq ((Valued.continuous_valuation_of_surjective (v'.valuedAdicCompletion_surjective L)).comp h1) (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_su …` and prove the remaining obligations.

Rewrite using `[h2]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v' _).trans ((h k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm)`.
-/
theorem exists_finCompl_map (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') :
    ∃ φ : v.adicCompletion L →+* v'.adicCompletion L, Continuous φ ∧
      (∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k)) ∧ ∀ x, Valued.v (φ x) = Valued.v x := by
  have hc : Continuous (WithVal.map (v.valuation L) (v'.valuation L) (c : L →+* L)) :=
    continuous_of_valued_eq (fun γ => by
      obtain ⟨k, hk⟩ := v.valuation_surjective L γ
      exact ⟨WithVal.toVal _ k, hk⟩) _ fun x => h x.ofVal
  let φ : v.adicCompletion L →+* v'.adicCompletion L :=
    ((HeightOneSpectrum.adicCompletion.equiv L v').symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  have h1 : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L v').comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  have h2 : ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := fun k => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ k)
  refine ⟨φ, h1, h2, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective (v'.valuedAdicCompletion_surjective L)).comp h1)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [h2]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v' _).trans
    ((h k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm)

omit [NumberField L] in

/- English proof (translation)
Establish `hc : Continuous (WithAbs.map (w.comap (c : L →+* L)).1 w.1 (c : L →+* L))` using `(AddMonoidHomClass.isometry_of_norm _ fun x => rfl).continuous`. Use `⟨((InfinitePlace.Completion.equiv w).symm.toRingHom.comp (UniformSpace.Completion.mapRingHom _ hc)).comp (InfinitePlace.Completion.equiv _).toRingHom, (InfinitePlace.Completion.continuous_ofCompletion w).comp (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion. …` and prove the remaining obligations. Apply `InfinitePlace.Completion.ext` to reduce the goal to its premises. Conclude with `UniformSpace.Completion.mapRingHom_coe hc (WithAbs.toAbs _ k)`.
-/
theorem exists_infCompl_map (c : L ≃+* L) (w : InfinitePlace L) :
    ∃ φ : (w.comap (c : L →+* L)).Completion →+* w.Completion, Continuous φ ∧
      ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := by
  have hc : Continuous (WithAbs.map (w.comap (c : L →+* L)).1 w.1 (c : L →+* L)) :=
    (AddMonoidHomClass.isometry_of_norm _ fun x => rfl).continuous
  refine ⟨((InfinitePlace.Completion.equiv w).symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (InfinitePlace.Completion.equiv _).toRingHom,
    (InfinitePlace.Completion.continuous_ofCompletion w).comp
      (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion _)), fun k => ?_⟩
  apply InfinitePlace.Completion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithAbs.toAbs _ k)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h x => by simpa using (h (c x)).symm, fun h x => by simpa using (h (c.symm x)).symm⟩`.
-/
theorem conjPl_symm_iff (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : ConjPl c.symm v' v ↔ ConjPl c v v' :=
  ⟨fun h x => by simpa using (h (c x)).symm, fun h x => by simpa using (h (c.symm x)).symm⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hi, Function.update_of_ne (hf.ne hi), map_one]`.
-/
theorem map_update_one {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Ring (M i)] {f : ι → ι}
    (hf : Function.Injective f) (φ : ∀ j, M (f j) →+* M j) (j : ι) (x : M (f j)) :
    (fun i => φ i (Function.update (fun i => (1 : M i)) (f j) x (f i))) =
      Function.update (fun i => (1 : M i)) j (φ j x) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne (hf.ne hi), map_one]

end General

open Classical in

/- English proof (translation)
Introduce `L _ _ c`. Use `choose f hf hfu using fun v => existsUnique_conjPl c.symm v`. Establish `hf' : ∀ v, ConjPl c (f v) v` using `fun v => (conjPl_symm_iff c _ _).1 (hf v)`. Establish `hfe : ∀ {v v'}, ConjPl c v v' → v = f v'` using `fun h => hfu _ _ ((conjPl_symm_iff c _ _).2 h)`. Establish `hfi : Function.Injective f` using `fun a b hab => (existsUnique_conjPl c (f a)).unique (hf' a) (hab ▸ hf' b)`.

Use `choose φ φc φk φv using fun v => exists_finCompl_map c (hf' v)`. Use `choose ψ ψc ψk using exists_infCompl_map c`. Establish `hg : ∀ w : InfinitePlace L, (w.comap (c.symm : L →+* L)).comap (c : L →+* L) = w` using `fun w => by`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hgi : Function.Injective fun w : InfinitePlace L => w.comap (c : L →+* L)` using `fun a b hab => by`. Use extensionality with `x`. Simplify using `using congrArg (fun w : InfinitePlace L => w (c.symm x)) hab`. Establish `hφ : ∀ᶠ j in Filter.cofinite, Set.MapsTo (φ j) ((f j).adicCompletionIntegers L) (j.adicCompletionIntegers L)` using `Filter.Eventually.of_forall fun j x hx => (φv j x).trans_le hx`. Set `Φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L` to `RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite φ hφ`.

Establish `Φc : Continuous Φ` using `RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite (fun j r => φ j r) hφ φc`. Set `Ψ : InfiniteAdeleRing L →+* InfiniteAdeleRing L` to `RingHom.pi fun w => (ψ w).comp (Pi.evalRingHom (fun w : InfinitePlace L => w.Completion) (w.comap (c : L →+* L)))`. Establish `Ψc : Continuous Ψ` using `continuous_pi fun w => (ψc w).comp (continuous_apply _)`. Set `A : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L` to `RingHom.prodMap Ψ Φ`. Establish `Ac : Continuous A` using `Ψc.prodMap Φc`.

Set `C : Ideles L →* Ideles L` to `Units.map A.toMonoidHom`. Establish `hinf : ∀ (w w' : InfinitePlace L) (e : w'.comap (c : L →+* L) = w), ∃ θ : w.Completion →+* w'.Completion, (∀ k : L, θ (algebraMap L _ k) = algebraMap L _ (c k)) ∧ ∀ y, C (infIdele L w y) = infIdele L w' (Units.map θ.toMonoidHom y)`. Introduce and unpack `_ w' rfl`. Conclude with `⟨ψ w', ψk w', fun y => Units.ext (Prod.ext (map_update_one hgi ψ w' y) (map_one Φ))⟩`. Establish `hloc : ∀ v (y : ((f v).adicCompletion L)ˣ), C (localIdele L (f v) y) = localIdele L v (Units.map (φ v).toMonoidHom y)` using `fun v y => Units.ext (Prod.ext (map_one Ψ) (Subtype.ext (map_update_one hfi φ v y)))`.

Use `⟨C, Continuous.units_map _ Ac, fun k => ?_, fun w k => ?_, fun w y => ?_, fun v v' h k => ?_, fun v v' h x => ?_, fun v v' h a => ?_⟩` and prove the remaining obligations. Conclude with `Units.ext (Prod.ext (funext fun w => ψk w k) (FiniteAdeleRing.ext _ fun v => φk v k))`. Take `⟨θ, h1, h2⟩` from `hinf w _ (hg w)`. Rewrite using `[h2]`. Conclude with `congrArg _ (Units.ext (h1 k))`.

Take `⟨θ, -, h2⟩` from `hinf w _ (hg w)`. Conclude with `⟨_, h2 y⟩`. Take `rfl` from `hfe h`. Rewrite using `[hloc]`. Conclude with `congrArg _ (Units.ext (φk v' k))`.

Take `rfl` from `hfe h`. Conclude with `⟨_, hloc v' x⟩`. Take `rfl` from `hfe h`. Use `⟨φv v' _, ?_⟩` and prove the remaining obligations. Rewrite using `[← φv v' (_ - 1), map_sub (φ v'), map_one (φ v')]`.

Both sides reduce to the same expression.
-/
theorem exists_isConjI : ∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L), ∃ C : Ideles L →* Ideles L, IsConjI c C := by
  intro L _ _ c
  choose f hf hfu using fun v => existsUnique_conjPl c.symm v
  have hf' : ∀ v, ConjPl c (f v) v := fun v => (conjPl_symm_iff c _ _).1 (hf v)
  have hfe : ∀ {v v'}, ConjPl c v v' → v = f v' := fun h => hfu _ _ ((conjPl_symm_iff c _ _).2 h)
  have hfi : Function.Injective f := fun a b hab =>
    (existsUnique_conjPl c (f a)).unique (hf' a) (hab ▸ hf' b)
  choose φ φc φk φv using fun v => exists_finCompl_map c (hf' v)
  choose ψ ψc ψk using exists_infCompl_map c
  have hg : ∀ w : InfinitePlace L, (w.comap (c.symm : L →+* L)).comap (c : L →+* L) = w := fun w => by
    ext x
    simp
  have hgi : Function.Injective fun w : InfinitePlace L => w.comap (c : L →+* L) := fun a b hab => by
    ext x
    simpa using congrArg (fun w : InfinitePlace L => w (c.symm x)) hab
  have hφ : ∀ᶠ j in Filter.cofinite, Set.MapsTo (φ j) ((f j).adicCompletionIntegers L) (j.adicCompletionIntegers L) :=
    Filter.Eventually.of_forall fun j x hx => (φv j x).trans_le hx
  let Φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite φ hφ
  have Φc : Continuous Φ :=
    RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) f hfi.tendsto_cofinite (fun j r => φ j r) hφ φc
  let Ψ : InfiniteAdeleRing L →+* InfiniteAdeleRing L :=
    RingHom.pi fun w => (ψ w).comp (Pi.evalRingHom (fun w : InfinitePlace L => w.Completion) (w.comap (c : L →+* L)))
  have Ψc : Continuous Ψ := continuous_pi fun w => (ψc w).comp (continuous_apply _)
  let A : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L := RingHom.prodMap Ψ Φ
  have Ac : Continuous A := Ψc.prodMap Φc
  let C : Ideles L →* Ideles L := Units.map A.toMonoidHom
  have hinf : ∀ (w w' : InfinitePlace L) (e : w'.comap (c : L →+* L) = w), ∃ θ : w.Completion →+* w'.Completion,
      (∀ k : L, θ (algebraMap L _ k) = algebraMap L _ (c k)) ∧
      ∀ y, C (infIdele L w y) = infIdele L w' (Units.map θ.toMonoidHom y) := by
    rintro _ w' rfl
    exact ⟨ψ w', ψk w', fun y => Units.ext (Prod.ext (map_update_one hgi ψ w' y) (map_one Φ))⟩
  have hloc : ∀ v (y : ((f v).adicCompletion L)ˣ),
      C (localIdele L (f v) y) = localIdele L v (Units.map (φ v).toMonoidHom y) := fun v y =>
    Units.ext (Prod.ext (map_one Ψ) (Subtype.ext (map_update_one hfi φ v y)))
  refine ⟨C, Continuous.units_map _ Ac, fun k => ?_, fun w k => ?_, fun w y => ?_, fun v v' h k => ?_,
    fun v v' h x => ?_, fun v v' h a => ?_⟩
  · exact Units.ext (Prod.ext (funext fun w => ψk w k) (FiniteAdeleRing.ext _ fun v => φk v k))
  · obtain ⟨θ, h1, h2⟩ := hinf w _ (hg w)
    rw [h2]
    exact congrArg _ (Units.ext (h1 k))
  · obtain ⟨θ, -, h2⟩ := hinf w _ (hg w)
    exact ⟨_, h2 y⟩
  · obtain rfl := hfe h
    rw [hloc]
    exact congrArg _ (Units.ext (φk v' k))
  · obtain rfl := hfe h
    exact ⟨_, hloc v' x⟩
  · obtain rfl := hfe h
    refine ⟨φv v' _, ?_⟩
    rw [← φv v' (_ - 1), map_sub (φ v'), map_one (φ v')]
    rfl

end GlobalTheory.Mem.Chr
