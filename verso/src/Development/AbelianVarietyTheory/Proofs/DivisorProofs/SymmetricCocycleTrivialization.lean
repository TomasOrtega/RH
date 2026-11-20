import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary

namespace GlobalTheory.CubeCoc

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.symm_cocycle_isCoboundary X (Multiplicative A) (fun a b => Multiplicative.ofAdd (f a b)) (fun a b => by rw [hs]) (fun a b c => by show Multiplicative.ofAdd (f (a + b) c + f a b) = Multiplicative.ofAdd (f a (b + c) + f b c)`. Rewrite using `[hc])`. Use `⟨fun x => Multiplicative.toAdd (g x), fun a b => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Multiplicative.toAdd (hg a b)`. Simplify `h` using `[sub_eq_add_neg]`.
-/
theorem symm_cocycle_add (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [AddCommGroup A]
    (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c + f a b = f a (b + c) + f b c) :
    ∃ g : X → A, ∀ a b, f a b = g (a + b) - g a - g b := by
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cocycle_isCoboundary X (Multiplicative A)
    (fun a b => Multiplicative.ofAdd (f a b)) (fun a b => by rw [hs]) (fun a b c => by
      show Multiplicative.ofAdd (f (a + b) c + f a b) = Multiplicative.ofAdd (f a (b + c) + f b c)
      rw [hc])
  refine ⟨fun x => Multiplicative.toAdd (g x), fun a b => ?_⟩
  have h := congrArg Multiplicative.toAdd (hg a b)
  simpa [sub_eq_add_neg] using h

/- English proof (translation)
Establish `e` using `bs.ext (f₁ := (AddMonoidHom.mk' φ hφ).toIntLinearMap) (f₂ := (AddMonoidHom.mk' ψ hψ).toIntLinearMap) h`. Introduce `a`. Conclude with `LinearMap.congr_fun e a`.
-/
theorem ext_of_basis {X : Type} [AddCommGroup X] {ι : Type} (bs : Module.Basis ι ℤ X)
    {M : Type} [AddCommGroup M] (φ ψ : X → M) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (hψ : ∀ a b, ψ (a + b) = ψ a + ψ b) (h : ∀ i, φ (bs i) = ψ (bs i)) : ∀ a, φ a = ψ a := by
  have e := bs.ext (f₁ := (AddMonoidHom.mk' φ hφ).toIntLinearMap)
    (f₂ := (AddMonoidHom.mk' ψ hψ).toIntLinearMap) h
  intro a
  exact LinearMap.congr_fun e a

variable {X : Type} [AddCommGroup X] {A : Type} [AddCommGroup A]

/- English proof (translation)
Establish `hcyc : ∀ a b c, f a b c = f b c a` using `fun a b c => by rw [hs1, hs2]`. Take `⟨T, hT⟩` from `symm_cocycle_add X (X → A) (fun a a' b => f a a' b) (fun a b => funext fun c => hs1 a b c) (fun a b c => funext fun y => by simpa using hc a b c y)`. Establish `ht1 : ∀ a a' b, f a a' b = T (a + a') b - T a b - T a' b` using `fun a a' b => by`. Simplify using `using congrFun (hT a a') b`. Establish `hcomp : ∀ a a' b b', f a a' (b + b') + f a b b' + f a' b b' = f (a + a') b b' + f a a' b + f a a' b'` using `fun a a' b b' => by`.

Establish `c1` using `hc a a' b b'`. Establish `c2` using `hc a' b b' a`. Establish `e1 : f a (a' + b) b' = f (a' + b) b' a` using `hcyc _ _ _`. Establish `e2 : f a' b a = f a a' b` using `(hcyc _ _ _).symm`. Establish `e3 : f a' (b + b') a = f a a' (b + b')` using `(hcyc _ _ _).symm`.

Establish `e4 : f b b' a = f a b b'` using `(hcyc _ _ _).symm`. Take the linear combination `(norm := module) -c1 - c2 - e1 + e2 - e3 - e4`. Set `d : X → X → X → A` to `fun a b b' => T a (b + b') - T a b - T a b' - f a b b'`. Establish `hd_add : ∀ a a' b b', d (a + a') b b' = d a b b' + d a' b b'` using `fun a a' b b' => by`. Establish `u1` using `ht1 a a' (b + b')`.

Establish `u2` using `ht1 a a' b`. Establish `u3` using `ht1 a a' b'`. Establish `u4` using `hcomp a a' b b'`. Simplify using `only [d]`. Take the linear combination `(norm := module) -u1 + u2 + u3 + u4`.

Establish `hd_cob : ∀ a, ∃ h : X → A, ∀ b b', d a b b' = h (b + b') - h b - h b'` using `fun a => by`. Use `symm_cocycle_add X A (d a) (fun b b' => by simp only [d]; rw [add_comm b b', hs2]; abel) (fun b b' b'' => ?_)` and prove the remaining obligations. Establish `c` using `hc b b' b'' a`. Establish `e1 : f (b + b') b'' a = f a (b + b') b''` using `(hcyc _ _ _).symm`. Establish `e2 : f b b' a = f a b b'` using `(hcyc _ _ _).symm`.

Establish `e3 : f b (b' + b'') a = f a b (b' + b'')` using `(hcyc _ _ _).symm`. Establish `e4 : f b' b'' a = f a b' b''` using `(hcyc _ _ _).symm`. Simplify using `only [d]`. Rewrite using `[add_assoc b b' b'']`. Take the linear combination `(norm := module) -c + e1 + e2 - e3 - e4`.

Set `bs` to `Module.Free.chooseBasis ℤ X`. Use `choose h hh using fun i => hd_cob (bs i)`. Set `H : X →ₗ[ℤ] (X → A)` to `bs.constr ℤ h`. Establish `hHb : ∀ i, H (bs i) = h i` using `fun i => bs.constr_basis ℤ h i`. Establish `hH : ∀ a b b', d a b b' = H a (b + b') - H a b - H a b'` using `fun a b b' => by`.

Use `ext_of_basis bs (fun a => d a b b') (fun a => H a (b + b') - H a b - H a b') (fun a a' => hd_add a a' b b') (fun a a' => ?_) (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [map_add, Pi.add_apply]`. Normalize the expressions using the abelian group laws. Simplify using `only [hHb]`. Conclude with `hh i b b'`.

Set `t' : X → X → A` to `fun a b => T a b - H a b`. Establish `hL1 : ∀ a a' b, f a a' b = t' (a + a') b - t' a b - t' a' b` using `fun a a' b => by`. Simplify using `only [t', map_add, Pi.add_apply]`. Rewrite using `[ht1]`. Normalize the expressions using the abelian group laws.

Establish `hL2 : ∀ a b b', f a b b' = t' a (b + b') - t' a b - t' a b'` using `fun a b b' => by`. Use `hH a b b'` as an intermediate fact. Simplify using `only [d] at this`. Simplify using `only [t']`. Take the linear combination `(norm := module) -this`.

Set `s : X → X → A` to `fun a b => t' a b - t' b a`. Establish `hs_l : ∀ a a' b, s (a + a') b = s a b + s a' b` using `fun a a' b => by`. Establish `e : f b a a' = f a a' b` using `hcyc b a a'`. Establish `u1` using `hL1 a a' b`. Establish `u2` using `hL2 b a a'`.

Simplify using `only [s]`. Take the linear combination `(norm := module) -u1 + u2 - e`. Establish `hs_r : ∀ a b b', s a (b + b') = s a b + s a b'` using `fun a b b' => by`. Establish `e : f b b' a = f a b b'` using `(hcyc a b b').symm`. Establish `u1` using `hL2 a b b'`.

Establish `u2` using `hL1 b b' a`. Simplify using `only [s]`. Take the linear combination `(norm := module) -u1 + u2 - e`. Set `v : Module.Free.ChooseBasisIndex ℤ X → Module.Free.ChooseBasisIndex ℤ X → A` to `fun i j => if WellOrderingRel i j then s (bs i) (bs j) else 0`. Set `U : X →ₗ[ℤ] X →ₗ[ℤ] A` to `bs.constr ℤ (fun i => bs.constr ℤ (v i))`.

Establish `hU : ∀ i j, U (bs i) (bs j) = v i j`. Introduce `i j`. Simplify using `only [U, Module.Basis.constr_basis]`. Establish `hi : ∀ i b, s (bs i) b = U (bs i) b - U b (bs i)`. Introduce `i b`.

Use `ext_of_basis bs (fun b => s (bs i) b) (fun b => U (bs i) b - U b (bs i)) (fun b b' => hs_r _ b b') (fun b b' => by simp only [map_add, LinearMap.add_apply]; abel) (fun j => ?_) b` and prove the remaining obligations. Use `show s (bs i) (bs j) = U (bs i) (bs j) - U (bs j) (bs i)`. Rewrite using `[hU, hU]`. Break down `trichotomous_of WellOrderingRel i j with h | h | h` into its components or cases. Establish `h' : ¬ WellOrderingRel j i` using `asymm h`.

Simplify using `only [v, if_pos h, if_neg h', sub_zero]`. Substitute `h` using the available equality. Simplify using `only [s, sub_self]`. Establish `h' : ¬ WellOrderingRel i j` using `asymm h`. Simplify using `only [v, if_pos h, if_neg h', s]`.

Normalize the expressions using the abelian group laws. Establish `hsu : ∀ a b, s a b = U a b - U b a` using `fun a b => ext_of_basis bs (fun a => s a b) (fun a => U a b - U b a) (fun a a' => hs_l a a' b) (fun a a' => by simp only [map_add, LinearMap.add_apply]; abel) (fun i => hi i b) a`. Set `t'' : X → X → A` to `fun a b => t' a b - U a b`. Establish `hsym : ∀ a b, t'' a b = t'' b a` using `fun a b => by`. Use `hsu a b` as an intermediate fact.

Simplify using `only [s] at this`. Simplify using `only [t'']`. Take the linear combination `(norm := module) this`. Establish `hM1 : ∀ a a' b, f a a' b = t'' (a + a') b - t'' a b - t'' a' b` using `fun a a' b => by`. Simplify using `only [t'', map_add, LinearMap.add_apply]`.

Rewrite using `[hL1]`. Normalize the expressions using the abelian group laws. Establish `hM2 : ∀ a b b', f a b b' = t'' a (b + b') - t'' a b - t'' a b'` using `fun a b b' => by`. Simplify using `only [t'', map_add]`. Rewrite using `[hL2]`.

Normalize the expressions using the abelian group laws. Establish `hcoc : ∀ a b c, t'' (a + b) c + t'' a b = t'' a (b + c) + t'' b c` using `fun a b c => by`. Establish `u1` using `hM1 a b c`. Establish `u2` using `hM2 a b c`. Take the linear combination `(norm := module) u2 - u1`.

Take `⟨g, hg⟩` from `symm_cocycle_add X A t'' hsym hcoc`. Use `⟨g, fun a a' b => ?_⟩` and prove the remaining obligations. Rewrite using `[hM1 a a' b, hg (a + a') b, hg a b, hg a' b]`. Normalize the expressions using the abelian group laws.
-/
theorem cubical_add [Module.Free ℤ X] (f : X → X → X → A)
    (hs1 : ∀ a b c, f a b c = f b a c) (hs2 : ∀ a b c, f a b c = f a c b)
    (hc : ∀ x x' x'' y, f (x + x') x'' y + f x x' y = f x (x' + x'') y + f x' x'' y) :
    ∃ g : X → A, ∀ a a' b, f a a' b + (g (a + a') + g (a + b) + g (a' + b))
      = g (a + a' + b) + g a + g a' + g b := by
  have hcyc : ∀ a b c, f a b c = f b c a := fun a b c => by rw [hs1, hs2]

  obtain ⟨T, hT⟩ := symm_cocycle_add X (X → A) (fun a a' b => f a a' b)
    (fun a b => funext fun c => hs1 a b c)
    (fun a b c => funext fun y => by simpa using hc a b c y)
  have ht1 : ∀ a a' b, f a a' b = T (a + a') b - T a b - T a' b := fun a a' b => by
    simpa using congrFun (hT a a') b

  have hcomp : ∀ a a' b b', f a a' (b + b') + f a b b' + f a' b b'
      = f (a + a') b b' + f a a' b + f a a' b' := fun a a' b b' => by
    have c1 := hc a a' b b'
    have c2 := hc a' b b' a
    have e1 : f a (a' + b) b' = f (a' + b) b' a := hcyc _ _ _
    have e2 : f a' b a = f a a' b := (hcyc _ _ _).symm
    have e3 : f a' (b + b') a = f a a' (b + b') := (hcyc _ _ _).symm
    have e4 : f b b' a = f a b b' := (hcyc _ _ _).symm
    linear_combination (norm := module) -c1 - c2 - e1 + e2 - e3 - e4

  let d : X → X → X → A := fun a b b' => T a (b + b') - T a b - T a b' - f a b b'
  have hd_add : ∀ a a' b b', d (a + a') b b' = d a b b' + d a' b b' := fun a a' b b' => by
    have u1 := ht1 a a' (b + b')
    have u2 := ht1 a a' b
    have u3 := ht1 a a' b'
    have u4 := hcomp a a' b b'
    simp only [d]
    linear_combination (norm := module) -u1 + u2 + u3 + u4
  have hd_cob : ∀ a, ∃ h : X → A, ∀ b b', d a b b' = h (b + b') - h b - h b' := fun a => by
    refine symm_cocycle_add X A (d a) (fun b b' => by simp only [d]; rw [add_comm b b', hs2]; abel)
      (fun b b' b'' => ?_)
    have c := hc b b' b'' a
    have e1 : f (b + b') b'' a = f a (b + b') b'' := (hcyc _ _ _).symm
    have e2 : f b b' a = f a b b' := (hcyc _ _ _).symm
    have e3 : f b (b' + b'') a = f a b (b' + b'') := (hcyc _ _ _).symm
    have e4 : f b' b'' a = f a b' b'' := (hcyc _ _ _).symm
    simp only [d]
    rw [add_assoc b b' b'']
    linear_combination (norm := module) -c + e1 + e2 - e3 - e4
  let bs := Module.Free.chooseBasis ℤ X
  choose h hh using fun i => hd_cob (bs i)
  let H : X →ₗ[ℤ] (X → A) := bs.constr ℤ h
  have hHb : ∀ i, H (bs i) = h i := fun i => bs.constr_basis ℤ h i
  have hH : ∀ a b b', d a b b' = H a (b + b') - H a b - H a b' := fun a b b' => by
    refine ext_of_basis bs (fun a => d a b b') (fun a => H a (b + b') - H a b - H a b')
      (fun a a' => hd_add a a' b b') (fun a a' => ?_) (fun i => ?_) a
    · simp only [map_add, Pi.add_apply]; abel
    · simp only [hHb]; exact hh i b b'
  let t' : X → X → A := fun a b => T a b - H a b
  have hL1 : ∀ a a' b, f a a' b = t' (a + a') b - t' a b - t' a' b := fun a a' b => by
    simp only [t', map_add, Pi.add_apply]; rw [ht1]; abel
  have hL2 : ∀ a b b', f a b b' = t' a (b + b') - t' a b - t' a b' := fun a b b' => by
    have := hH a b b'
    simp only [d] at this
    simp only [t']
    linear_combination (norm := module) -this

  let s : X → X → A := fun a b => t' a b - t' b a
  have hs_l : ∀ a a' b, s (a + a') b = s a b + s a' b := fun a a' b => by
    have e : f b a a' = f a a' b := hcyc b a a'
    have u1 := hL1 a a' b
    have u2 := hL2 b a a'
    simp only [s]
    linear_combination (norm := module) -u1 + u2 - e
  have hs_r : ∀ a b b', s a (b + b') = s a b + s a b' := fun a b b' => by
    have e : f b b' a = f a b b' := (hcyc a b b').symm
    have u1 := hL2 a b b'
    have u2 := hL1 b b' a
    simp only [s]
    linear_combination (norm := module) -u1 + u2 - e
  classical
  let v : Module.Free.ChooseBasisIndex ℤ X → Module.Free.ChooseBasisIndex ℤ X → A :=
    fun i j => if WellOrderingRel i j then s (bs i) (bs j) else 0
  let U : X →ₗ[ℤ] X →ₗ[ℤ] A := bs.constr ℤ (fun i => bs.constr ℤ (v i))
  have hU : ∀ i j, U (bs i) (bs j) = v i j := by
    intro i j; simp only [U, Module.Basis.constr_basis]
  have hi : ∀ i b, s (bs i) b = U (bs i) b - U b (bs i) := by
    intro i b
    refine ext_of_basis bs (fun b => s (bs i) b) (fun b => U (bs i) b - U b (bs i))
      (fun b b' => hs_r _ b b') (fun b b' => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun j => ?_) b
    show s (bs i) (bs j) = U (bs i) (bs j) - U (bs j) (bs i)
    rw [hU, hU]
    rcases trichotomous_of WellOrderingRel i j with h | h | h
    · have h' : ¬ WellOrderingRel j i := asymm h
      simp only [v, if_pos h, if_neg h', sub_zero]
    · subst h; simp only [s, sub_self]
    · have h' : ¬ WellOrderingRel i j := asymm h
      simp only [v, if_pos h, if_neg h', s]; abel
  have hsu : ∀ a b, s a b = U a b - U b a := fun a b =>
    ext_of_basis bs (fun a => s a b) (fun a => U a b - U b a) (fun a a' => hs_l a a' b)
      (fun a a' => by simp only [map_add, LinearMap.add_apply]; abel) (fun i => hi i b) a
  let t'' : X → X → A := fun a b => t' a b - U a b
  have hsym : ∀ a b, t'' a b = t'' b a := fun a b => by
    have := hsu a b
    simp only [s] at this
    simp only [t'']
    linear_combination (norm := module) this
  have hM1 : ∀ a a' b, f a a' b = t'' (a + a') b - t'' a b - t'' a' b := fun a a' b => by
    simp only [t'', map_add, LinearMap.add_apply]; rw [hL1]; abel
  have hM2 : ∀ a b b', f a b b' = t'' a (b + b') - t'' a b - t'' a b' := fun a b b' => by
    simp only [t'', map_add]; rw [hL2]; abel
  have hcoc : ∀ a b c, t'' (a + b) c + t'' a b = t'' a (b + c) + t'' b c := fun a b c => by
    have u1 := hM1 a b c
    have u2 := hM2 a b c
    linear_combination (norm := module) u2 - u1
  obtain ⟨g, hg⟩ := symm_cocycle_add X A t'' hsym hcoc
  refine ⟨g, fun a a' b => ?_⟩
  rw [hM1 a a' b, hg (a + a') b, hg a b, hg a' b]
  abel

end GlobalTheory.CubeCoc

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ _ A _ f hs1 hs2 hc`. Take `⟨g, hg⟩` from `CubeCoc.cubical_add (A := Additive A) (fun a b c => Additive.ofMul (f a b c)) (fun a b c => by rw [hs1]) (fun a b c => by rw [hs2]) (fun x x' x'' y => by show Additive.ofMul (f (x + x') x'' y * f x x' y) = Additive.ofMul (f x (x' + x'') y * f x' x'' y)`. Rewrite using `[hc])`. Conclude with `⟨fun x => Additive.toMul (g x), fun a a' b => congrArg Additive.toMul (hg a a' b)⟩`.
-/
theorem symm_cubical_cocycle_isThirdDifference : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → X → A), (∀ a b c, f a b c = f b a c) → (∀ a b c, f a b c = f a c b) → (∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y) → ∃ g : X → A, ∀ a a' b, f a a' b * (g (a + a') * g (a + b) * g (a' + b)) = g (a + a' + b) * g a * g a' * g b := by
  intro X _ _ A _ f hs1 hs2 hc
  obtain ⟨g, hg⟩ := CubeCoc.cubical_add (A := Additive A) (fun a b c => Additive.ofMul (f a b c))
    (fun a b c => by rw [hs1]) (fun a b c => by rw [hs2])
    (fun x x' x'' y => by
      show Additive.ofMul (f (x + x') x'' y * f x x' y) = Additive.ofMul (f x (x' + x'') y * f x' x'' y)
      rw [hc])
  exact ⟨fun x => Additive.toMul (g x), fun a a' b => congrArg Additive.toMul (hg a a' b)⟩

end GlobalTheory
