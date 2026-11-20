import Mathlib

namespace FunctorialResolution.EmbeddedResolution

variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

/- English proof (translation)
Establish `hker : s - s' ∈ RingHom.ker f.toRingHom`. Simplify using `[RingHom.mem_ker, h]`. Establish `hD'` using `hD _ hker`. Rewrite `hD'` using `[RingHom.mem_ker, map_sub D s s']`. Establish `h2 : f (D s) - f (D s') = 0`.

Rewrite using `[← map_sub f (D s) (D s')]`. Conclude with `hD'`. Conclude with `eq_of_sub_eq_zero h2`.
-/
theorem map_derivation_eq_of_map_eq (f : S →ₐ[k] T) (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
    {s s' : S} (h : f s = f s') : f (D s) = f (D s') := by
  have hker : s - s' ∈ RingHom.ker f.toRingHom := by
    simp [RingHom.mem_ker, h]
  have hD' := hD _ hker
  rw [RingHom.mem_ker, map_sub D s s'] at hD'
  have h2 : f (D s) - f (D s') = 0 := by
    rw [← map_sub f (D s) (D s')]
    exact hD'
  exact eq_of_sub_eq_zero h2

noncomputable def derivationOfSurjectiveFun (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S) : T → T :=
  fun t => f (D (Function.surjInv hf t))

/- English proof (translation)
Establish `h : f (Function.surjInv hf (f s)) = f s` using `Function.surjInv_eq hf (f s)`. Conclude with `map_derivation_eq_of_map_eq f D hD h`.
-/
theorem derivationOfSurjectiveFun_apply (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjectiveFun f hf D (f s) = f (D s) := by
  have h : f (Function.surjInv hf (f s)) = f s := Function.surjInv_eq hf (f s)
  exact map_derivation_eq_of_map_eq f D hD h

/- English proof (translation)
Introduce `t t'`. Take `⟨a, rfl⟩` from `hf t`. Take `⟨b, rfl⟩` from `hf t'`. Rewrite using `[← map_add f a b]`. Simplify using `only [derivationOfSurjectiveFun_apply f hf D hD]`.

Rewrite using `[map_add D a b, map_add f (D a) (D b)]`.
-/
theorem derivationOfSurjectiveFun_add (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ t t' : T, derivationOfSurjectiveFun f hf D (t + t')
      = derivationOfSurjectiveFun f hf D t + derivationOfSurjectiveFun f hf D t' := by
  intro t t'
  obtain ⟨a, rfl⟩ := hf t
  obtain ⟨b, rfl⟩ := hf t'
  rw [← map_add f a b]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [map_add D a b, map_add f (D a) (D b)]

/- English proof (translation)
Introduce `c t`. Take `⟨a, rfl⟩` from `hf t`. Establish `h1 : f (c • a) = c • f a` using `map_smul f c a`. Establish `h2 : D (c • a) = c • D a`. Simplify using the standard rewrite rules.

Establish `h3 : f (c • D a) = c • f (D a)` using `map_smul f c (D a)`. Rewrite using `[← h1]`. Simplify using `only [derivationOfSurjectiveFun_apply f hf D hD]`. Rewrite using `[h2]`. Conclude with `h3`.
-/
theorem derivationOfSurjectiveFun_smul (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ (c : k) (t : T), derivationOfSurjectiveFun f hf D (c • t) = c • derivationOfSurjectiveFun f hf D t := by
  intro c t
  obtain ⟨a, rfl⟩ := hf t
  have h1 : f (c • a) = c • f a := map_smul f c a
  have h2 : D (c • a) = c • D a := by
    simp
  have h3 : f (c • D a) = c • f (D a) := map_smul f c (D a)
  rw [← h1]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [h2]
  exact h3

noncomputable def derivationOfSurjectiveLinearMap (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) : T →ₗ[k] T where
  toFun := derivationOfSurjectiveFun f hf D
  map_add' := derivationOfSurjectiveFun_add f hf D hD
  map_smul' := derivationOfSurjectiveFun_smul f hf D hD

/- English proof (translation)
Establish `h : (1 : T) = f 1` using `(map_one f).symm`. Rewrite using `[h]`. Rewrite using `[derivationOfSurjectiveFun_apply f hf D hD, D.map_one_eq_zero, map_zero]`.
-/
theorem derivationOfSurjectiveFun_one (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    derivationOfSurjectiveFun f hf D 1 = 0 := by
  have h : (1 : T) = f 1 := (map_one f).symm
  rw [h]
  rw [derivationOfSurjectiveFun_apply f hf D hD, D.map_one_eq_zero, map_zero]

/- English proof (translation)
Introduce `a b`. Take `⟨x, rfl⟩` from `hf a`. Take `⟨y, rfl⟩` from `hf b`. Rewrite using `[← map_mul f x y]`. Simplify using `only [derivationOfSurjectiveFun_apply f hf D hD]`.

Rewrite using `[D.leibniz]`. Simplify using `[smul_eq_mul]`.
-/
theorem derivationOfSurjectiveFun_mul (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ a b : T, derivationOfSurjectiveFun f hf D (a * b)
      = a • derivationOfSurjectiveFun f hf D b + b • derivationOfSurjectiveFun f hf D a := by
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [← map_mul f x y]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [D.leibniz]
  simp [smul_eq_mul]

noncomputable def derivationOfSurjective (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    Derivation k T T where
  toLinearMap := derivationOfSurjectiveLinearMap f hf D hD
  map_one_eq_zero' := derivationOfSurjectiveFun_one f hf D hD
  leibniz' := derivationOfSurjectiveFun_mul f hf D hD

@[simp]
/- English proof (translation)
The claim follows from `derivationOfSurjectiveFun_apply f hf D hD s`.
-/
theorem derivationOfSurjective_apply (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjective f hf D hD (f s) = f (D s) :=
  derivationOfSurjectiveFun_apply f hf D hD s

end FunctorialResolution.EmbeddedResolution
