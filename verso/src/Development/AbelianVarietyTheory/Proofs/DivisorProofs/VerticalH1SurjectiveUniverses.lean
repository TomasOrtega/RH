import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.VertSurj

universe a b

/- English proof (translation)
Take `⟨G, a0, a1, a2, a3, compDegreeZero_natural, compDegreeOne_natural, compDegreeTwo_natural, comp_commutes_diffZero, comp_commutes_diffOne, comp_commutes_diffTwo⟩` from `m`. Simplify using `only at hG`. Substitute `hG` using the available equality. Simplify using `only [Functor.id_obj, Functor.id_map] at compDegreeZero_natural compDegreeOne_natural comp_commutes_diffZero comp_commutes_diffOne`. Simplify using `only [CxMap.QAll, Functor.id_obj] at hQ`.

Introduce `c`. Take `⟨⟨⟨f', ω'⟩, hc⟩, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Establish `hc' : K'.D1 (f', ω') = 0` using `hc`. Establish `hA : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), K'.M0.map ψ (f' T T' φ) - f' T T'' (φ ≫ ψ) + f' T' T'' ψ = 0` using `fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hc') T) T') T'') φ) ψ`. Establish `hB : ∀ T T' (φ : T ⟶ T'), ω' T' - K'.M1.map φ (ω' T) - K'.d0 T' (f' T T' φ) = 0` using `fun T T' φ ↦ congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hc') T) T') φ`.

Establish `hC : ∀ T, K'.d1 T (ω' T) = 0` using `fun T ↦ congrFun (congrArg (fun x ↦ x.2.2) hc') T`. Use `choose ω w hω hωw using fun T ↦ (hQ T).surj1 (ω' T) (hC T)`. Establish `hE : ∀ T T' (φ : T ⟶ T'), a1 T' (ω T' - K.M1.map φ (ω T)) = K'.d0 T' (f' T T' φ - (w T' - K'.M0.map φ (w T)))`. Introduce `T T' φ`. Establish `h1` using `hωw T'`.

Establish `h2` using `hωw T`. Establish `h3` using `hB T T' φ`. Rewrite using `[map_sub, compDegreeOne_natural]`. Establish `e1 : a1 T' (ω T') = ω' T' - K'.d0 T' (w T')` using `by rw [h1]; abel`. Establish `e2 : a1 T (ω T) = ω' T - K'.d0 T (w T)` using `by rw [h2]; abel`.

Rewrite using `[e1, e2]`. Simplify using `only [map_sub]`. Rewrite using `[← K'.diffZero_natural]`. Establish `e3 : ω' T' = K'.M1.map φ (ω' T) + K'.d0 T' (f' T T' φ)` using `by rw [← sub_eq_zero, ← h3]; abel`. Rewrite using `[e3]`.

Normalize the expressions using the abelian group laws. Use `choose f₁ hf₁ using fun T T' (φ : T ⟶ T') ↦ (hQ T').inj1 (ω T' - K.M1.map φ (ω T)) (f' T T' φ - (w T' - K'.M0.map φ (w T))) (by rw [map_sub, K.diffOne_natural, hω, hω, map_zero, sub_zero]) (hE T T' φ)`. Use `choose f₂ hf₂0 hf₂ using fun T T' (φ : T ⟶ T') ↦ (hQ T').surj0 (f' T T' φ - (w T' - K'.M0.map φ (w T)) - a0 T' (f₁ T T' φ)) (by rw [map_sub, ← comp_commutes_diffZero, hf₁, hE, sub_self])`. Establish `hfa : ∀ T T' (φ : T ⟶ T'), a0 T' (f₁ T T' φ + f₂ T T' φ) = f' T T' φ - (w T' - K'.M0.map φ (w T))`. Introduce `T T' φ`.

Rewrite using `[map_add, hf₂]`. Normalize the expressions using the abelian group laws. Establish `hfd : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f₁ T T' φ + f₂ T T' φ) = ω T' - K.M1.map φ (ω T)`. Introduce `T T' φ`. Rewrite using `[map_add, hf₁, hf₂0, add_zero]`.

Set `f : K.M0.c1` to `fun T T' φ ↦ f₁ T T' φ + f₂ T T' φ`. Establish `hfa' : ∀ T T' (φ : T ⟶ T'), a0 T' (f T T' φ) = f' T T' φ - (w T' - K'.M0.map φ (w T))` using `hfa`. Establish `hfd' : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ) = ω T' - K.M1.map φ (ω T)` using `hfd`. Use `clear_value f`. Establish `hZ : ((f, ω) : K.T1) ∈ K.Z1` using `by show K.D1 (f, ω) = 0`.

Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `T T' T'' φ ψ show K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0`. Apply `(hQ T'').inj0` to reduce the goal to its premises. Simplify using `only [map_add, map_sub, K.diffZero_natural, hfd', K.M1.map_comp]`. Normalize the expressions using the abelian group laws.

Rewrite using `[map_add, map_sub, compDegreeZero_natural, hfa', hfa', hfa']`. Simplify using `only [map_sub, K'.M0.map_comp]`. Take the linear combination `(norm := abel1) hA T T' T'' φ ψ`. Use function extensionality and compare the values at `T T' φ show ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = 0`. Rewrite using `[hfd', sub_self]`.

Use function extensionality and compare the values at `T`. Conclude with `hω T`. Use `⟨QuotientAddGroup.mk ⟨(f, ω), hZ⟩, ?_⟩` and prove the remaining obligations. Use `show QuotientAddGroup.mk (CxMap.z1 _ ⟨(f, ω), hZ⟩) = QuotientAddGroup.mk _`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Use `⟨w, Prod.ext ?_ ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ show w T' - K'.M0.map φ (w T) = -(a0 T' (f T T' φ)) + f' T T' φ`. Rewrite using `[hfa']`. Normalize the expressions using the abelian group laws. Use function extensionality and compare the values at `T show K'.d0 T (w T) = -(a1 T (ω T)) + ω' T`.

Rewrite using `[hωw T]`. Normalize the expressions using the abelian group laws.
-/
theorem surj_of_id {C' : Type b} [Category.{0} C'] {K K' : Cx C'} (m : CxMap K K')
    (hG : m.G = 𝟭 C') (hQ : m.QAll) : Function.Surjective m.h1 := by
  obtain ⟨G, a0, a1, a2, a3, compDegreeZero_natural, compDegreeOne_natural, compDegreeTwo_natural, comp_commutes_diffZero, comp_commutes_diffOne, comp_commutes_diffTwo⟩ := m
  dsimp only at hG
  subst hG
  simp only [Functor.id_obj, Functor.id_map] at compDegreeZero_natural compDegreeOne_natural comp_commutes_diffZero comp_commutes_diffOne
  dsimp only [CxMap.QAll, Functor.id_obj] at hQ
  intro c
  obtain ⟨⟨⟨f', ω'⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hc' : K'.D1 (f', ω') = 0 := hc
  have hA : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K'.M0.map ψ (f' T T' φ) - f' T T'' (φ ≫ ψ) + f' T' T'' ψ = 0 :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hc') T) T') T'') φ) ψ
  have hB : ∀ T T' (φ : T ⟶ T'), ω' T' - K'.M1.map φ (ω' T) - K'.d0 T' (f' T T' φ) = 0 :=
    fun T T' φ ↦ congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hc') T) T') φ
  have hC : ∀ T, K'.d1 T (ω' T) = 0 := fun T ↦ congrFun (congrArg (fun x ↦ x.2.2) hc') T
  choose ω w hω hωw using fun T ↦ (hQ T).surj1 (ω' T) (hC T)

  have hE : ∀ T T' (φ : T ⟶ T'), a1 T' (ω T' - K.M1.map φ (ω T)) =
      K'.d0 T' (f' T T' φ - (w T' - K'.M0.map φ (w T))) := by
    intro T T' φ
    have h1 := hωw T'
    have h2 := hωw T
    have h3 := hB T T' φ
    rw [map_sub, compDegreeOne_natural]
    have e1 : a1 T' (ω T') = ω' T' - K'.d0 T' (w T') := by rw [h1]; abel
    have e2 : a1 T (ω T) = ω' T - K'.d0 T (w T) := by rw [h2]; abel
    rw [e1, e2]; simp only [map_sub]; rw [← K'.diffZero_natural]
    have e3 : ω' T' = K'.M1.map φ (ω' T) + K'.d0 T' (f' T T' φ) := by rw [← sub_eq_zero, ← h3]; abel
    rw [e3]; abel
  choose f₁ hf₁ using fun T T' (φ : T ⟶ T') ↦ (hQ T').inj1 (ω T' - K.M1.map φ (ω T))
    (f' T T' φ - (w T' - K'.M0.map φ (w T)))
    (by rw [map_sub, K.diffOne_natural, hω, hω, map_zero, sub_zero]) (hE T T' φ)
  choose f₂ hf₂0 hf₂ using fun T T' (φ : T ⟶ T') ↦ (hQ T').surj0
    (f' T T' φ - (w T' - K'.M0.map φ (w T)) - a0 T' (f₁ T T' φ))
    (by rw [map_sub, ← comp_commutes_diffZero, hf₁, hE, sub_self])
  have hfa : ∀ T T' (φ : T ⟶ T'), a0 T' (f₁ T T' φ + f₂ T T' φ) =
      f' T T' φ - (w T' - K'.M0.map φ (w T)) := by
    intro T T' φ; rw [map_add, hf₂]; abel
  have hfd : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f₁ T T' φ + f₂ T T' φ) = ω T' - K.M1.map φ (ω T) := by
    intro T T' φ; rw [map_add, hf₁, hf₂0, add_zero]
  let f : K.M0.c1 := fun T T' φ ↦ f₁ T T' φ + f₂ T T' φ
  have hfa' : ∀ T T' (φ : T ⟶ T'), a0 T' (f T T' φ) = f' T T' φ - (w T' - K'.M0.map φ (w T)) := hfa
  have hfd' : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ) = ω T' - K.M1.map φ (ω T) := hfd
  clear_value f
  have hZ : ((f, ω) : K.T1) ∈ K.Z1 := by
    show K.D1 (f, ω) = 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      show K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0
      apply (hQ T'').inj0
      · simp only [map_add, map_sub, K.diffZero_natural, hfd', K.M1.map_comp]; abel
      · rw [map_add, map_sub, compDegreeZero_natural, hfa', hfa', hfa']
        simp only [map_sub, K'.M0.map_comp]
        linear_combination (norm := abel1) hA T T' T'' φ ψ
    · funext T T' φ
      show ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = 0
      rw [hfd', sub_self]
    · funext T
      exact hω T
  refine ⟨QuotientAddGroup.mk ⟨(f, ω), hZ⟩, ?_⟩
  show QuotientAddGroup.mk (CxMap.z1 _ ⟨(f, ω), hZ⟩) = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨w, Prod.ext ?_ ?_⟩
  · funext T T' φ
    show w T' - K'.M0.map φ (w T) = -(a0 T' (f T T' φ)) + f' T T' φ
    rw [hfa']; abel
  · funext T
    show K'.d0 T (w T) = -(a1 T (ω T)) + ω' T
    rw [hωw T]; abel

/- English proof (translation)
Introduce `C _ C' _ K K' m hQ`. Conclude with `surj_of_id m.vert rfl hQ`.
-/
theorem main : VertHas.{a, b} (fun m ↦ Function.Surjective m.h1) := by
  intro C _ C' _ K K' m hQ
  exact surj_of_id m.vert rfl hQ

/- English proof (translation)
Assemble the required witnesses or components as `⟨main, main, main⟩`.
-/
theorem instances : VertHas.{1,1} (fun m ↦ Function.Surjective m.h1) ∧
    VertHas.{1,0} (fun m ↦ Function.Surjective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h1) :=
  ⟨main, main, main⟩

end GlobalTheory.CxCoh.VertSurj
