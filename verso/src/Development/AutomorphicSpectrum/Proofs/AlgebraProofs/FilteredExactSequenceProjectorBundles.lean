import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

/- English proof (translation)
Introduce `K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom`. Take `⟨hinj, hex, hsurj, hL, hL''⟩` from `hSE`. Establish `mP : ∀ v ∈ LinearMap.range P, P v = v`. Introduce `v hv`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.1 hv`.

Conclude with `hP u`. Establish `mP' : ∀ v ∈ LinearMap.range P', P' v = v`. Introduce `v hv`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.1 hv`. Conclude with `hP' u`.

Establish `mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v`. Introduce `v hv`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.1 hv`. Conclude with `hP'' u`. Set `f₀ : LinearMap.range P →ₗ[K] LinearMap.range P'` to `LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v => LinearMap.mem_range.2 ⟨f v, by show P' (f v) = f v`.

Rewrite using `[← hfP, mP _ v.2]⟩)`. Set `g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P''` to `LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v => LinearMap.mem_range.2 ⟨g v, by show P'' (g v) = g v`. Rewrite using `[← hgP, mP' _ v.2]⟩)`. Establish `hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P'')) f₀ g₀`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Conclude with `congrArg Subtype.val h`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy' : g (y : V') = 0` using `congrArg Subtype.val hy`. Take `⟨x, hx⟩` from `(hex (y : V')).1 hy'`. Use `⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show f (P x) = (y : V')`. Rewrite using `[hfP, hx, mP' _ y.2]`. Introduce and unpack `⟨x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show g (f (x : V)) = 0`. Conclude with `(hex _).2 ⟨x, rfl⟩`. Introduce `z`. Take `⟨y, hy⟩` from `hsurj (z : V'')`. Use `⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show g (P' y) = (z : V'')`. Rewrite using `[hgP, hy, mP'' _ z.2]`. Introduce `i x show (x : V) ∈ L i ↔ f (x : V) ∈ L' i`. Conclude with `hL i x`.

Introduce `i z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨y, hyL, hy⟩` from `(hL'' i z).1 hz`. Use `⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show g (P' y) = (z : V'')`. Rewrite using `[hgP, hy, mP'' _ z.2]`. Introduce and unpack `⟨y, hyL, rfl⟩`. Conclude with `(hL'' i _).2 ⟨y, hyL, rfl⟩`.

Establish `hBW : IsBun C (sub C L' (LinearMap.range P'))` using `(SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1`. Conclude with `(deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'') (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P'')) f₀ g₀ hBW hSE0).2.2`.
-/
theorem subDeg_range_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom
  obtain ⟨hinj, hex, hsurj, hL, hL''⟩ := hSE
  have mP : ∀ v ∈ LinearMap.range P, P v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP u
  have mP' : ∀ v ∈ LinearMap.range P', P' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP' u
  have mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP'' u
  let f₀ : LinearMap.range P →ₗ[K] LinearMap.range P' :=
    LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v =>
      LinearMap.mem_range.2 ⟨f v, by
        show P' (f v) = f v
        rw [← hfP, mP _ v.2]⟩)
  let g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P'' :=
    LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v =>
      LinearMap.mem_range.2 ⟨g v, by
        show P'' (g v) = g v
        rw [← hgP, mP' _ v.2]⟩)
  have hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P'))
      (sub C L'' (LinearMap.range P'')) f₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val h
    · intro y
      constructor
      · intro hy
        have hy' : g (y : V') = 0 := congrArg Subtype.val hy
        obtain ⟨x, hx⟩ := (hex (y : V')).1 hy'
        refine ⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩
        apply Subtype.ext
        show f (P x) = (y : V')
        rw [hfP, hx, mP' _ y.2]
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        show g (f (x : V)) = 0
        exact (hex _).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hsurj (z : V'')
      refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩
      apply Subtype.ext
      show g (P' y) = (z : V'')
      rw [hgP, hy, mP'' _ z.2]
    · intro i x
      show (x : V) ∈ L i ↔ f (x : V) ∈ L' i
      exact hL i x
    · intro i z
      constructor
      · intro hz
        obtain ⟨y, hyL, hy⟩ := (hL'' i z).1 hz
        refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩
        apply Subtype.ext
        show g (P' y) = (z : V'')
        rw [hgP, hy, mP'' _ z.2]
      · rintro ⟨y, hyL, rfl⟩
        exact (hL'' i _).2 ⟨y, hyL, rfl⟩
  have hBW : IsBun C (sub C L' (LinearMap.range P')) :=
    (SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1
  exact (deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'')
    (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P''))
    f₀ g₀ hBW hSE0).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
