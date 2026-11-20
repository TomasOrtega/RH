import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Introduce `ι M _ _ _ _ s F M' _ _ F' f U hF hU`. Take `⟨hfd, hst, ip, hherm, hpos, hadj⟩` from `hU`. Set `K : Submodule ℂ M` to `U ⊓ LinearMap.ker f`. Establish `hKU : ∀ k ∈ K, k ∈ U` using `fun k hk => (Submodule.mem_inf.mp hk).1`. Establish `hKf : ∀ k ∈ K, f k = 0` using `fun k hk => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hk).2`.

Use `haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le (inf_le_left : K ≤ U)`. Set `n` to `Module.finrank ℂ K`. Set `b` to `Module.finBasis ℂ K`. Set `ψ : M →ₗ[ℂ] (Fin n → ℂ)` to `LinearMap.pi (fun i => ip (b i : M))`. Set `U1 : Submodule ℂ M` to `U ⊓ LinearMap.ker ψ`.

Establish `hU1U : ∀ w ∈ U1, w ∈ U` using `fun w hw => (Submodule.mem_inf.mp hw).1`. Establish `hA : ∀ w ∈ U1, ∀ k ∈ K, ip k w = 0`. Introduce `w hw k hk`. Establish `hw' : ∀ i, ip (b i : M) w = 0` using `fun i => by`. Use `congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2) i` as an intermediate fact.

Simplify `this` using `[ψ]`. Establish `h0 : ((ip.flip w).comp K.subtype) = 0` using `b.ext (fun i => by simpa using hw' i)`. Use `LinearMap.congr_fun h0 ⟨k, hk⟩` as an intermediate fact. Simplify using `using this`. Establish `hA' : ∀ w ∈ U1, ∀ k ∈ K, ip w k = 0`.

Introduce `w hw k hk`. Use `hherm k (hKU k hk) w (hU1U w hw)` as an intermediate fact. Rewrite `this` using `[hA w hw k hk, star_zero]`. Conclude with `this.symm`. Establish `hinj : Function.Injective (ψ.comp K.subtype)`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `k hk`. Establish `hk1 : (k : M) ∈ U1` using `Submodule.mem_inf.mpr ⟨hKU k k.2, LinearMap.mem_ker.mpr (by simpa using hk)⟩`. Establish `h0` using `hA _ hk1 _ k.2`. Assume the negation of the conclusion as `hne`.

Establish `hne' : (k : M) ≠ 0` using `fun h => hne (Subtype.ext h)`. Use `hpos _ (hKU k k.2) hne'` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `hsurj : Function.Surjective (ψ.comp K.subtype)` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [n])).mp hinj`.

Establish `hdec : ∀ u ∈ U, ∃ k ∈ K, u - k ∈ U1`. Introduce `u hu`. Take `⟨k, hk⟩` from `hsurj (ψ u)`. Use `⟨k, k.2, Submodule.mem_inf.mpr ⟨U.sub_mem hu (hKU k k.2), LinearMap.mem_ker.mpr ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_sub]`.

Conclude with `sub_eq_zero.mpr (by simpa using hk.symm)`. Establish `hinj1 : LinearMap.ker (f.comp U1.subtype) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `w hw`. Establish `hwK : (w : M) ∈ K` using `Submodule.mem_inf.mpr ⟨hU1U w w.2, LinearMap.mem_ker.mpr (by simpa using hw)⟩`.

Establish `h0` using `hA _ w.2 _ hwK`. Assume the negation of the conclusion as `hne`. Establish `hne' : (w : M) ≠ 0` using `fun h => hne (Subtype.ext h)`. Use `hpos _ (hU1U w w.2) hne'` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Take `⟨h, hh⟩` from `LinearMap.exists_leftInverse_of_injective (f.comp U1.subtype) hinj1`. Set `g : M' →ₗ[ℂ] M` to `U1.subtype.comp h`. Establish `hg : ∀ w ∈ U1, g (f w) = w`. Introduce `w hw`.

Use `congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩)` as an intermediate fact. Simplify `this` using `[g]`. Establish `hkey : ∀ u ∈ U, g (f u) ∈ U1 ∧ u - g (f u) ∈ K`. Introduce `u hu`. Take `⟨k, hk, hw⟩` from `hdec u hu`.

Establish `hfu : f u = f (u - k)` using `by rw [map_sub, hKf k hk, sub_zero]`. Rewrite using `[hfu, hg _ hw, sub_sub_cancel]`. Conclude with `⟨hw, hk⟩`. Establish `hgU1 : ∀ x ∈ U.map f, g x ∈ U1`. Introduce and unpack `x ⟨u, hu, rfl⟩`.

Conclude with `(hkey u hu).1`. Establish `hfg : ∀ x ∈ U.map f, f (g x) = x`. Introduce and unpack `x ⟨u, hu, rfl⟩`. Use `hKf _ (hkey u hu).2` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`.

Conclude with `this.symm`. Use `haveI := hfd`. Use `⟨inferInstance, ?_, (ip.comp g).compl₂ g, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b hab _ ⟨u, hu, rfl⟩`. Conclude with `⟨F a b u, hst a b hab u hu, hF a b hab u hu⟩`.

Introduce `x hx y hy`. Conclude with `hherm _ (hU1U _ (hgU1 x hx)) _ (hU1U _ (hgU1 y hy))`. Introduce `x hx hne`. Apply `hpos _ (hU1U _ (hgU1 x hx))` to reduce the goal to its premises. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hfg x hx]`. Express the relevant statement in the definitionally equal form `f (g x) = 0`. Rewrite using `[h0, map_zero]`. Introduce `a b hab x hx y hy`.

Establish `hu0` using `hgU1 x hx`. Establish `hv0` using `hgU1 y hy`. Establish `e1 : F' a b x = f (F a b (g x))` using `by rw [hF a b hab _ (hU1U _ hu0), hfg x hx]`. Establish `e2 : F' b a y = f (F b a (g y))` using `by rw [hF b a hab.symm _ (hU1U _ hv0), hfg y hy]`. Express the relevant statement in the definitionally equal form `ip (g (F' a b x)) (g y) = ip (g x) (g (F' b a y))`.

Rewrite using `[e1, e2]`. Establish `hk1` using `(hkey _ (hst a b hab _ (hU1U _ hu0))).2`. Establish `hk2` using `(hkey _ (hst b a hab.symm _ (hU1U _ hv0))).2`. Establish `l1 : ip (g (f (F a b (g x)))) (g y) = ip (F a b (g x)) (g y)`. Use `hA (g y) hv0 _ hk1` as an intermediate fact.

Rewrite `this` using `[map_sub, LinearMap.sub_apply]`. Conclude with `(sub_eq_zero.mp this).symm`. Establish `l2 : ip (g x) (g (f (F b a (g y)))) = ip (g x) (F b a (g y))`. Use `hA' (g x) hu0 _ hk2` as an intermediate fact. Rewrite `this` using `[map_sub]`.

Conclude with `(sub_eq_zero.mp this).symm`. Rewrite using `[l1, l2]`. Conclude with `hadj a b hab _ (hU1U _ hu0) _ (hU1U _ hv0)`.
-/
theorem unitOn_map : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) →
    UnitOn s F U → UnitOn s F' (U.map f) := by
  intro ι M _ _ _ _ s F M' _ _ F' f U hF hU
  obtain ⟨hfd, hst, ip, hherm, hpos, hadj⟩ := hU
  let K : Submodule ℂ M := U ⊓ LinearMap.ker f
  have hKU : ∀ k ∈ K, k ∈ U := fun k hk => (Submodule.mem_inf.mp hk).1
  have hKf : ∀ k ∈ K, f k = 0 := fun k hk => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hk).2
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le (inf_le_left : K ≤ U)
  let n := Module.finrank ℂ K
  let b := Module.finBasis ℂ K
  let ψ : M →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => ip (b i : M))
  let U1 : Submodule ℂ M := U ⊓ LinearMap.ker ψ
  have hU1U : ∀ w ∈ U1, w ∈ U := fun w hw => (Submodule.mem_inf.mp hw).1
  have hA : ∀ w ∈ U1, ∀ k ∈ K, ip k w = 0 := by
    intro w hw k hk
    have hw' : ∀ i, ip (b i : M) w = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2) i
      simpa [ψ] using this
    have h0 : ((ip.flip w).comp K.subtype) = 0 := b.ext (fun i => by simpa using hw' i)
    have := LinearMap.congr_fun h0 ⟨k, hk⟩
    simpa using this
  have hA' : ∀ w ∈ U1, ∀ k ∈ K, ip w k = 0 := by
    intro w hw k hk
    have := hherm k (hKU k hk) w (hU1U w hw)
    rw [hA w hw k hk, star_zero] at this
    exact this.symm
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have hk1 : (k : M) ∈ U1 := Submodule.mem_inf.mpr ⟨hKU k k.2, LinearMap.mem_ker.mpr (by simpa using hk)⟩
    have h0 := hA _ hk1 _ k.2
    by_contra hne
    have hne' : (k : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hKU k k.2) hne'
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective (ψ.comp K.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [n])).mp hinj
  have hdec : ∀ u ∈ U, ∃ k ∈ K, u - k ∈ U1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hsurj (ψ u)
    refine ⟨k, k.2, Submodule.mem_inf.mpr ⟨U.sub_mem hu (hKU k k.2), LinearMap.mem_ker.mpr ?_⟩⟩
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa using hk.symm)
  have hinj1 : LinearMap.ker (f.comp U1.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwK : (w : M) ∈ K := Submodule.mem_inf.mpr ⟨hU1U w w.2, LinearMap.mem_ker.mpr (by simpa using hw)⟩
    have h0 := hA _ w.2 _ hwK
    by_contra hne
    have hne' : (w : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hU1U w w.2) hne'
    rw [h0] at this
    simp at this
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (f.comp U1.subtype) hinj1
  let g : M' →ₗ[ℂ] M := U1.subtype.comp h
  have hg : ∀ w ∈ U1, g (f w) = w := by
    intro w hw
    have := congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩)
    simpa [g] using this
  have hkey : ∀ u ∈ U, g (f u) ∈ U1 ∧ u - g (f u) ∈ K := by
    intro u hu
    obtain ⟨k, hk, hw⟩ := hdec u hu
    have hfu : f u = f (u - k) := by rw [map_sub, hKf k hk, sub_zero]
    rw [hfu, hg _ hw, sub_sub_cancel]
    exact ⟨hw, hk⟩
  have hgU1 : ∀ x ∈ U.map f, g x ∈ U1 := by
    rintro x ⟨u, hu, rfl⟩
    exact (hkey u hu).1
  have hfg : ∀ x ∈ U.map f, f (g x) = x := by
    rintro x ⟨u, hu, rfl⟩
    have := hKf _ (hkey u hu).2
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  haveI := hfd
  refine ⟨inferInstance, ?_, (ip.comp g).compl₂ g, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨u, hu, rfl⟩
    exact ⟨F a b u, hst a b hab u hu, hF a b hab u hu⟩
  · intro x hx y hy
    exact hherm _ (hU1U _ (hgU1 x hx)) _ (hU1U _ (hgU1 y hy))
  · intro x hx hne
    apply hpos _ (hU1U _ (hgU1 x hx))
    intro h0
    apply hne
    rw [← hfg x hx]
    change f (g x) = 0
    rw [h0, map_zero]
  · intro a b hab x hx y hy
    have hu0 := hgU1 x hx
    have hv0 := hgU1 y hy
    have e1 : F' a b x = f (F a b (g x)) := by rw [hF a b hab _ (hU1U _ hu0), hfg x hx]
    have e2 : F' b a y = f (F b a (g y)) := by rw [hF b a hab.symm _ (hU1U _ hv0), hfg y hy]
    change ip (g (F' a b x)) (g y) = ip (g x) (g (F' b a y))
    rw [e1, e2]
    have hk1 := (hkey _ (hst a b hab _ (hU1U _ hu0))).2
    have hk2 := (hkey _ (hst b a hab.symm _ (hU1U _ hv0))).2
    have l1 : ip (g (f (F a b (g x)))) (g y) = ip (F a b (g x)) (g y) := by
      have := hA (g y) hv0 _ hk1
      rw [map_sub, LinearMap.sub_apply] at this
      exact (sub_eq_zero.mp this).symm
    have l2 : ip (g x) (g (f (F b a (g y)))) = ip (g x) (F b a (g y)) := by
      have := hA' (g x) hu0 _ hk2
      rw [map_sub] at this
      exact (sub_eq_zero.mp this).symm
    rw [l1, l2]
    exact hadj a b hab _ (hU1U _ hu0) _ (hU1U _ hv0)

end GlobalTheory.HoweR
