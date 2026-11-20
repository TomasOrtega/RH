import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.RrCompCastSucc

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

/- English proof (translation)
Establish `hT : ∀ (s : ℂ) (i j : Fin n) (y : V), f (Tm E s i j y) = Tm E' s i j (f y)`. Introduce `s i j y`. Unfold `Tm`. Apply the tactic sequence `split_ifs <;> simp [hf, Module.algebraMap_end_apply]`. Establish `hP : ∀ (m : ℕ) (g : Fin m → Module.End ℂ V) (g' : Fin m → Module.End ℂ V'), (∀ k y, f (g k y) = g' k (f y)) → ∀ y, f ((List.ofFn g).prod y) = (List.ofFn g').prod (f y)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro g g' _ y`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `g g' h y`. Simplify using `only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]`. Rewrite using `[h, ih (fun k => g k.succ) (fun k => g' k.succ) (fun k y => h k.succ y)]`. Unfold `qminor`. Simplify using `only [LinearMap.sum_apply, map_sum, Module.End.mul_apply]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul, hP _ _ _ (fun k y => hT _ _ _ y)]`.
-/
theorem qminor_int {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n t : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  have hT : ∀ (s : ℂ) (i j : Fin n) (y : V), f (Tm E s i j y) = Tm E' s i j (f y) := by
    intro s i j y
    unfold Tm
    split_ifs <;> simp [hf, Module.algebraMap_end_apply]
  have hP : ∀ (m : ℕ) (g : Fin m → Module.End ℂ V) (g' : Fin m → Module.End ℂ V'),
      (∀ k y, f (g k y) = g' k (f y)) → ∀ y, f ((List.ofFn g).prod y) = (List.ofFn g').prod (f y) := by
    intro m
    induction m with
    | zero => intro g g' _ y; simp
    | succ m ih =>
      intro g g' h y
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      rw [h, ih (fun k => g k.succ) (fun k => g' k.succ) (fun k y => h k.succ y)]
  unfold qminor
  simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul,
    hP _ _ _ (fun k y => hT _ _ _ y)]

/- English proof (translation)
Introduce `V V' _ _ _ _ N E E' f hf u X x`. Use `⟨?_, qminor_int f hf _ _ _ _⟩` and prove the remaining obligations. Simplify using `only [Th, LinearMap.pi_apply, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, qminor_int f hf]`.
-/
theorem thMap : ThMap := by
  intro V V' _ _ _ _ N E E' f hf u X x
  refine ⟨?_, qminor_int f hf _ _ _ _⟩
  simp only [Th, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, qminor_int f hf]

/- English proof (translation)
Introduce `V V' _ _ _ _ N E E' ι z f hE hι hz hf w cG hdet h0 v`. Establish `h` using `congrArg f (algId V N E ι z hE hι hz (w + 1) v)`. Rewrite `h` using `[hdet]`. Establish `hw : w + 1 - 1 = w` using `by ring`. Rewrite `h` using `[hw]`.

Establish `hT` using `thMap V V' N (fun a b => E (ι a) (ι b)) E' f hf w`. Establish `hq : ∀ y, f (qdet (fun a b => E (ι a) (ι b)) w y) = 0`. Introduce `y`. Rewrite using `[(hT (fun _ => y) 0).2]`. Conclude with `h0 _`.

Rewrite using `[← LinearMap.map_smul, h, map_sub, map_sum, hq, zero_sub]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Conclude with `(hT _ c).1`.
-/
theorem keyId : KeyId := by
  intro V V' _ _ _ _ N E E' ι z f hE hι hz hf w cG hdet h0 v
  have h := congrArg f (algId V N E ι z hE hι hz (w + 1) v)
  rw [hdet] at h
  have hw : w + 1 - 1 = w := by ring
  rw [hw] at h
  have hT := thMap V V' N (fun a b => E (ι a) (ι b)) E' f hf w
  have hq : ∀ y, f (qdet (fun a b => E (ι a) (ι b)) w y) = 0 := by
    intro y
    rw [(hT (fun _ => y) 0).2]
    exact h0 _
  rw [← LinearMap.map_smul, h, map_sub, map_sum, hq, zero_sub]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hT _ c).1

end PositivityTheory.RgHe.SM
