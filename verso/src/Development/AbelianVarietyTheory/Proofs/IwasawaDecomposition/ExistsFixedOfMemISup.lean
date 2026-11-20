import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix Filter

namespace GlobalTheory.CuspRep.LocSph

/- English proof (translation)
Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hφ`. Establish `key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W → φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1`.

Consider the case `insert i s _ ih`. Introduce `W hW h1 h2`. Rewrite `h2` using `[Finset.iSup_insert, ← sup_assoc]`. Distinguish the cases in `h3 : φ ∈ W ⊔ LinearMap.range (f i)`. Take `⟨x, hx, _, ⟨v, rfl⟩, e⟩` from `Submodule.mem_sup.1 h3`.

Establish `hv : f i v ∉ W` using `fun h => h1 (e ▸ add_mem hx h)`. Establish `hc : W.comap (f i) = ⊥`. Use `(((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hf]`. Conclude with `hW g _ hu`.

Establish `: v ∈ W.comap (f i)` using `h ▸ Submodule.mem_top`. Conclude with `this`. Use `⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩` and prove the remaining obligations. Establish `h4 : σ k v - v ∈ W.comap (f i)`. Establish `h5` using `hK k hk`.

Rewrite `h5` using `[← e, map_add]`. Establish `h6 : f i (σ k v - v) = x - ρ k x`. Rewrite using `[map_sub, hf]`. Take the linear combination `(norm := module) h5`. Rewrite using `[Submodule.mem_comap, h6]`.

Conclude with `sub_mem hx (hW k x hx)`. Rewrite `h4` using `[hc, Submodule.mem_bot]`. Conclude with `sub_eq_zero.1 h4`. Use `ih _ (fun g y hy => ?_) h3 h2` and prove the remaining obligations. Take `⟨x, hx, _, ⟨v, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add, ← hf]`. Conclude with `Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩`. Conclude with `key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)`.
-/
theorem exists_fixed_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (φ : V) (h0 : φ ≠ 0) (hK : ∀ k ∈ K, ρ k φ = φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add] at h5
          have h6 : f i (σ k v - v) = x - ρ k x := by
            rw [map_sub, hf]; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem hx (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)`.
-/
theorem gl_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

/- English proof (translation)
Use `gl_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[hk, one_mul, mul_one]`.

Rewrite using `[pLoc_locGL_of_ne h, one_mul, mul_one]`.
-/
theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

/- English proof (translation)
Establish `h` using `(GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)`. Rewrite `h` using `[sub_self]`. Use `h.congr fun w => ?_` and prove the remaining obligations. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v - Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v = (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v`.

Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem tendsto_sLoc (y : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E)
    (hy : ∀ v, y v ∈ v.adicCompletionIntegers E) : Tendsto (fun v => sLoc E v (y v)) cofinite (𝓝 0) := by
  classical
  have h := (GlobalTheory.Mem.UnrAe.tendsto_finSingle y hy).sub
    (GlobalTheory.Mem.UnrAe.tendsto_finSingle (L := E) (fun _ => 0) fun _ => by simp)
  rw [sub_self] at h
  refine h.congr fun w => ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  change Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w (y w) v -
      Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w 0 v =
      (Pi.single w (y w) : ∀ v : HeightOneSpectrum (𝓞 E), v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

/- English proof (translation)
Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Establish `h` using `((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _])).add`.

Use the proof step `(tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)`. Rewrite `h` using `[sub_zero, add_zero]`. Conclude with `h`.
-/
theorem tendsto_corner (y : ∀ v : HeightOneSpectrum (𝓞 E), Matrix (Fin a) (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => corner (matN a (sLoc E v)) ((y v).map (v.adicCompletionIntegers E).subtype)) cofinite (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((tendsto_const_nhds (x := (1 : Matrix (Fin a) (Fin a) (Af E)) i j)).sub
    (tendsto_sLoc (E := E) (fun v => (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) fun v => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])).add
    (tendsto_sLoc (fun v => (y v i j : v.adicCompletion E)) fun v => (y v i j).2)
  rw [sub_zero, add_zero] at h
  exact h

/- English proof (translation)
Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Conclude with `(tendsto_corner fun v => (y v).val).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))`.
-/
theorem tendsto_locGL (y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletionIntegers E)) :
    Tendsto (fun v => locGL E a v (GeneralLinearGroup.map (v.adicCompletionIntegers E).subtype (y v))) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (tendsto_corner fun v => (y v).val).prodMk_nhds
    ((MulOpposite.continuous_op.tendsto _).comp (tendsto_corner fun v => ((y v)⁻¹).val))

/- English proof (translation)
Establish `h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E), locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U → ∀ g : GL (Fin a) (w.adicCompletionIntegers E), locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subt …` using `fun w => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨-, g, hg⟩` from `hc 1`. Conclude with `hg (hc g).1`.

Use `choose y hy using h`. Conclude with `((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw`.
-/
theorem eventually_mem {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 1) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype y) ∈ U →
      ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
        locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ U := fun w => by
    by_contra hc
    push Not at hc
    obtain ⟨-, g, hg⟩ := hc 1
    exact hg (hc g).1
  choose y hy using h
  exact ((tendsto_locGL y).eventually_mem hU).mono fun w hw => hy w hw

variable [IsTotallyComplex E]

def Maps (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ π.V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

/- English proof (translation)
Establish `comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) → ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1` using `fun o ho f v => Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by`. Rewrite using `[LinearMap.comp_apply, f.2.2]`. Conclude with `LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩`. Use `(π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `f.2.1 v`. Establish `: (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o)`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Submodule.mem_comap]`.

Consider the cases of `o with`. Consider the case `fin k`. Set `g` to `GeneralLinearGroup.map (pLoc E w) k`. Establish `h1` using `comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by`. Express the relevant statement in the definitionally equal form `finRep E a _ * _ = _ * finRep E a _`.

Rewrite using `[← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)`. Establish `h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v)`. Rewrite using `[f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Consider the case `cpt k`.

Use `comm (.cpt k) (fun g => ?_) f v` and prove the remaining obligations. Establish `h2` using `congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))`. Rewrite `h2` using `[map_mul, map_mul]`. Conclude with `h2`. Consider the case `lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v`.

Conclude with `this hφ`. Take `⟨f, h0, hf⟩` from `h`. Use `h0 (LinearMap.ext fun v => Subtype.ext ?_)` and prove the remaining obligations. Establish `: (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1` using `Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ : Maps π w σ) ⟨v, rfl⟩`. Rewrite `this` using `[hb]`.

Conclude with `this`.
-/
theorem iSup_range_eq (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : π.IsLocComp w σ) : ⨆ f : Maps π w σ, LinearMap.range f.1 = π.V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps π w σ) v, act o (f.1 v) ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => π.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps π w σ) ⟨v, rfl⟩
  refine (π.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps π w σ, LinearMap.range f.1) ≤ (⨆ f : Maps π w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hf⟩ := h
    refine h0 (LinearMap.ext fun v => Subtype.ext ?_)
    have : (f v).1 ∈ ⨆ f : Maps π w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨π.V.subtype ∘ₗ f, fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩ :
        Maps π w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

/- English proof (translation)
Introduce `E _ _ _ a π`. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Use `filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ`. Take `⟨v, h1, h2⟩` from `exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred (fun f : Maps π w σ => f.1) (fun f => f.2.2) (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0 (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)`. Conclude with `⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩`.
-/
theorem locComp_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → ∃ v : σ.V, v ≠ 0 ∧ ∀ g : GL (Fin a) (w.adicCompletionIntegers E), σ.ρ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) v = v := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨v, h1, h2⟩ := exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
    (fun f : Maps π w σ => f.1) (fun f => f.2.2)
    (Set.range (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype)) φ h0
    (by rintro _ ⟨g, rfl⟩; exact hw g) (by rw [iSup_range_eq π w σ hσ]; exact hφ)
  exact ⟨v, h1, fun g => h2 _ ⟨g, rfl⟩⟩

end GlobalTheory.CuspRep.LocSph
