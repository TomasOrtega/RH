import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.TyDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Lit.Ty
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lit.Ty.IotaTransfer

variable {k k' G V V' W W' : Type} [Field k] [Field k'] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k' V']
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k' W']

/- English proof (translation)
Introduce `z v`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
private theorem semi_symm {ι : k ≃+* k'} {e : V ≃+ V'} (he : ∀ (z : k) v, e (z • v) = ι z • e v) :
    ∀ (z : k') v, e.symm (z • v) = ι.symm z • e.symm v := by
  intro z v
  apply e.injective
  rw [he]; simp

/- English proof (translation)
Introduce `g v`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
private theorem int_symm {e : V ≃+ V'} {ρ : Representation k G V} {ρ' : Representation k' G V'}
    (h : ∀ g v, e (ρ g v) = ρ' g (e v)) : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := by
  intro g v
  apply e.injective
  rw [h]; simp

/- English proof (translation)
Use `⟨{ toFun := fun w => e'.symm (F (e w)) map_add' := by intro a b; simp map_smul' := by intro z v; rw [he, map_smul, semi_symm he']; simp }, ?_⟩` and prove the remaining obligations. Introduce `w`. Simplify using the standard rewrite rules.
-/
private theorem exists_map {ι : k ≃+* k'} {e : W ≃+ W'} (he : ∀ (z : k) v, e (z • v) = ι z • e v)
    {e' : V ≃+ V'} (he' : ∀ (z : k) v, e' (z • v) = ι z • e' v) (F : W' →ₗ[k'] V') :
    ∃ f : W →ₗ[k] V, ∀ w, e' (f w) = F (e w) := by
  refine ⟨{ toFun := fun w => e'.symm (F (e w))
            map_add' := by intro a b; simp
            map_smul' := by intro z v; rw [he, map_smul, semi_symm he']; simp }, ?_⟩
  intro w
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⊥ : Subrepresentation ρ) = ⊤` using `Subrepresentation.ext (Subsingleton.elim _ _)`. Conclude with `bot_ne_top this`.
-/
private theorem nontrivial_of_irr {ρ : Representation k G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim _ _)
  exact bot_ne_top this

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_map he he' F`. Use `⟨f.intertwiningMap_of_isIntertwiningMap σ π ?_, hf⟩` and prove the remaining obligations. Introduce `g v`. Apply `e'.injective` to reduce the goal to its premises. Rewrite using `[hf, h, hF, h', hf]`.
-/
private theorem maps {ι : k ≃+* k'} {e : W ≃+ W'} (he : ∀ (z : k) v, e (z • v) = ι z • e v)
    {e' : V ≃+ V'} (he' : ∀ (z : k) v, e' (z • v) = ι z • e' v)
    {σ : Representation k G W} {ξ : Representation k' G W'} (h : ∀ g v, e (σ g v) = ξ g (e v))
    {π : Representation k G V} {π' : Representation k' G V'} (h' : ∀ g v, e' (π g v) = π' g (e' v))
    (F : W' →ₗ[k'] V') (hF : ∀ g v, F (ξ g v) = π' g (F v)) :
    ∃ f : σ.IntertwiningMap π, ∀ w, e' (f w) = F (e w) := by
  obtain ⟨f, hf⟩ := exists_map he he' F
  refine ⟨f.intertwiningMap_of_isIntertwiningMap σ π ?_, hf⟩
  intro g v
  apply e'.injective
  rw [hf, h, hF, h', hf]

/- English proof (translation)
Establish `hn : Nontrivial W` using `nontrivial_of_irr hi`. Establish `nz : ∀ (F : W' →ₗ[k'] V') (f : σ.IntertwiningMap π), (∀ w, e' (f w) = F (e w)) → F ≠ 0 → f ≠ 0`. Introduce `F f hf hF h0`. Apply `hF` to reduce the goal to its premises. Use extensionality with `w`.

Take `⟨w, rfl⟩` from `e.surjective w`. Rewrite using `[← hf, h0]`. Simplify using the standard rewrite rules. Establish `back : ∀ f : W →ₗ[k] V, f ≠ 0 → (∀ g v, f (σ g v) = π g (f v)) → ∃ f : W' →ₗ[k'] V', f ≠ 0 ∧ ∀ g v, f (ξ g v) = π' g (f v)`. Introduce `f h0 hf`.

Take `⟨F, hF⟩` from `maps (semi_symm he) (semi_symm he') (int_symm h) (int_symm h') f hf`. Use `⟨F.toLinearMap, fun h1 => h0 ?_, fun g v => F.isIntertwining _ _ g v⟩` and prove the remaining obligations. Use extensionality with `w`. Take `⟨w, rfl⟩` from `e.symm.surjective w`. Establish `h2 : F w = 0` using `congrArg (fun φ : W' →ₗ[k'] V' => φ w) h1`.

Rewrite using `[← hF, h2]`. Simplify using the standard rewrite rules. Use `⟨⟨?_, ?_⟩, fun h1 => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨F, h0, hF⟩`. Take `⟨f, hf⟩` from `maps he he' h h' F hF`.

Conclude with `⟨f.toLinearMap, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right (nz F f hf h0), fun g v => f.isIntertwining _ _ g v⟩`. Introduce and unpack `⟨f, hinj, hf⟩`. Use `back f ?_ hf` and prove the remaining obligations. Introduce and unpack `rfl`. Take `⟨a, b, hab⟩` from `exists_pair_ne W`.

Conclude with `hab (hinj rfl)`. Establish `: Nontrivial (σ.IntertwiningMap π)` using `Module.nontrivial_of_finrank_eq_succ h1`. Take `⟨f, hf⟩` from `exists_ne (0 : σ.IntertwiningMap π)`. Conclude with `back f.toLinearMap (fun h2 => hf (Representation.IntertwiningMap.ext h2)) (fun g v => f.isIntertwining _ _ g v)`. Introduce `F F' h0 hF hF'`.

Take `⟨f, hf⟩` from `maps he he' h h' F hF`. Take `⟨f', hf'⟩` from `maps he he' h h' F' hF'`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' f (nz F f hf h0)).1 h1 f'`. Use `⟨ι c, ?_⟩` and prove the remaining obligations. Use extensionality with `w`.

Take `⟨w, rfl⟩` from `e.surjective w`. Rewrite using `[LinearMap.smul_apply, ← hf, ← hf', ← he', ← hc]`. Both sides reduce to the same expression.
-/
private theorem main {ι : k ≃+* k'} {e : W ≃+ W'} (he : ∀ (z : k) v, e (z • v) = ι z • e v)
    {e' : V ≃+ V'} (he' : ∀ (z : k) v, e' (z • v) = ι z • e' v)
    {σ : Representation k G W} {ξ : Representation k' G W'} (h : ∀ g v, e (σ g v) = ξ g (e v))
    {π : Representation k G V} {π' : Representation k' G V'} (h' : ∀ g v, e' (π g v) = π' g (e' v))
    (hi : σ.IsIrreducible) :
    ((∃ f : W' →ₗ[k'] V', f ≠ 0 ∧ ∀ g v, f (ξ g v) = π' g (f v)) ↔
      ∃ f : W →ₗ[k] V, Function.Injective f ∧ ∀ g v, f (σ g v) = π g (f v)) ∧
    (Module.finrank k (σ.IntertwiningMap π) = 1 →
      (∃ f : W' →ₗ[k'] V', f ≠ 0 ∧ ∀ g v, f (ξ g v) = π' g (f v)) ∧
      ∀ f f' : W' →ₗ[k'] V', f ≠ 0 → (∀ g v, f (ξ g v) = π' g (f v)) → (∀ g v, f' (ξ g v) = π' g (f' v)) →
        ∃ c : k', f' = c • f) := by
  have hn : Nontrivial W := nontrivial_of_irr hi
  have nz : ∀ (F : W' →ₗ[k'] V') (f : σ.IntertwiningMap π), (∀ w, e' (f w) = F (e w)) → F ≠ 0 → f ≠ 0 := by
    intro F f hf hF h0
    apply hF
    ext w
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [← hf, h0]
    simp
  have back : ∀ f : W →ₗ[k] V, f ≠ 0 → (∀ g v, f (σ g v) = π g (f v)) →
      ∃ f : W' →ₗ[k'] V', f ≠ 0 ∧ ∀ g v, f (ξ g v) = π' g (f v) := by
    intro f h0 hf
    obtain ⟨F, hF⟩ := maps (semi_symm he) (semi_symm he') (int_symm h) (int_symm h') f hf
    refine ⟨F.toLinearMap, fun h1 => h0 ?_, fun g v => F.isIntertwining _ _ g v⟩
    ext w
    obtain ⟨w, rfl⟩ := e.symm.surjective w
    have h2 : F w = 0 := congrArg (fun φ : W' →ₗ[k'] V' => φ w) h1
    rw [← hF, h2]
    simp
  refine ⟨⟨?_, ?_⟩, fun h1 => ⟨?_, ?_⟩⟩
  · rintro ⟨F, h0, hF⟩
    obtain ⟨f, hf⟩ := maps he he' h h' F hF
    exact ⟨f.toLinearMap, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right (nz F f hf h0),
      fun g v => f.isIntertwining _ _ g v⟩
  · rintro ⟨f, hinj, hf⟩
    refine back f ?_ hf
    rintro rfl
    obtain ⟨a, b, hab⟩ := exists_pair_ne W
    exact hab (hinj rfl)
  · have : Nontrivial (σ.IntertwiningMap π) := Module.nontrivial_of_finrank_eq_succ h1
    obtain ⟨f, hf⟩ := exists_ne (0 : σ.IntertwiningMap π)
    exact back f.toLinearMap (fun h2 => hf (Representation.IntertwiningMap.ext h2)) (fun g v => f.isIntertwining _ _ g v)
  · intro F F' h0 hF hF'
    obtain ⟨f, hf⟩ := maps he he' h h' F hF
    obtain ⟨f', hf'⟩ := maps he he' h h' F' hF'
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f (nz F f hf h0)).1 h1 f'
    refine ⟨ι c, ?_⟩
    ext w
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [LinearMap.smul_apply, ← hf, ← hf', ← he', ← hc]
    rfl

end UpperTheory.V.Lit.Ty.IotaTransfer
