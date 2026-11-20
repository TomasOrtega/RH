import Mathlib

open TensorProduct WithConv

namespace GlobalTheory.HopfShear

variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]

open Algebra.TensorProduct Bialgebra HopfAlgebra in

@[reducible] noncomputable def pointsGroup : Group (WithConv (A →ₐ[R] X)) where
  __ := (inferInstance : Monoid (WithConv (A →ₐ[R] X)))
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] X)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

attribute [local instance] pointsGroup

noncomputable def pre (f : B →ₐc[R] A) : WithConv (A →ₐ[R] X) →* WithConv (B →ₐ[R] X) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (x.ofConv.comp (f : B →ₐ[R] A))) fun x y => by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

noncomputable def post (h : X →ₐ[R] Y) : WithConv (A →ₐ[R] X) →* WithConv (A →ₐ[R] Y) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (h.comp x.ofConv)) fun x y => by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pre_apply (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem post_apply (h : X →ₐ[R] Y) (x : WithConv (A →ₐ[R] X)) (a : A) :
    (post h x).ofConv a = h (x.ofConv a) := rfl

/- English proof (translation)
The claim follows from `ofConv_injective (AlgHom.ext h)`.
-/
theorem conv_ext {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y :=
  ofConv_injective (AlgHom.ext h)

/- English proof (translation)
Use `set S := AlgHom.range (f : B →ₐ[R] A) with hS`. Use `set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI`. Set `l : WithConv (A →ₐ[R] A ⊗[S] A)` to `toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))`. Set `r : WithConv (A →ₐ[R] A ⊗[S] A)` to `toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)`. Set `l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I))` to `toConv (IsScalarTower.toAlgHom R A _)`.

Set `p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I))` to `toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp (Ideal.Quotient.mkₐ R I))`. Establish `hl : ∀ a, l.ofConv a = a ⊗ₜ 1` using `fun a => rfl`. Establish `hr : ∀ a, r.ofConv a = 1 ⊗ₜ a` using `fun a => rfl`. Establish `hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1` using `fun a => rfl`. Establish `hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a` using `fun a => rfl`.

Establish `hlr : pre f l = pre f r` using `conv_ext fun b => by`. Rewrite using `[pre_apply, pre_apply, hl, hr]`. Use `TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)` as an intermediate fact. Simplify `this` using `[Subalgebra.smul_def]`. Establish `hpf : pre f p = 1` using `conv_ext fun b => by`.

Rewrite using `[pre_apply, hp]`. Establish `hb : b - algebraMap R B (Coalgebra.counit b) ∈ RingHom.ker (Bialgebra.counitAlgHom R B)`. Simplify using `[RingHom.mem_ker]`. Establish `h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b)`. Establish `h2` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)`.

Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero, AlgHom.commutes]`. Conclude with `h2`. Rewrite using `[h1]`. Conclude with `(Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _`. Set `g : A →ₐ[S] A ⊗[R] (A ⧸ I)` to `{ (l' * p).ofConv.toRingHom with commutes' := by`.

Introduce and unpack `⟨_, b, rfl⟩`. Establish `h : pre f (l' * p) = pre f l'` using `by rw [map_mul, hpf, mul_one]`. Establish `h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1` using `congrArg (fun x => x.ofConv b) h`. Conclude with `h2 }`. Set `Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I)` to `Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _`.

Establish `hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0`. Establish `h : pre f (l⁻¹ * r) = 1` using `by rw [map_mul, map_inv, hlr, inv_mul_cancel]`. Establish `: I ≤ RingHom.ker (l⁻¹ * r).ofConv`. Rewrite using `[hI, Ideal.map_le_iff_le_comap]`. Introduce `b hb`.

Establish `h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b)` using `congrArg (fun x => x.ofConv b) h`. Establish `h3 : Coalgebra.counit (R` using `R) b = 0 := hb`. Rewrite `h2` using `[h3, map_zero]`. Conclude with `h2`. Conclude with `fun a ha => this ha`.

Set `k : (A ⧸ I) →ₐ[R] A ⊗[S] A` to `Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk`. Set `Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A` to `Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _`. Establish `hΦl : post (Φ.restrictScalars R) l = l'` using `conv_ext fun a => Φ.commutes a`. Establish `hΦr : post (Φ.restrictScalars R) r = l' * p` using `conv_ext fun a => by`. Express the relevant statement in the definitionally equal form `Φ (1 ⊗ₜ a) = g a`.

Simplify using `[Φ, ← Algebra.TensorProduct.one_def]`. Establish `hΨl : post (Ψ.restrictScalars R) l' = l` using `conv_ext fun a => Ψ.commutes a`. Establish `hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r` using `conv_ext fun a => by`. Express the relevant statement in the definitionally equal form `Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)`. Simplify using `[Ψ, ← Algebra.TensorProduct.one_def]`.

Establish `h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a` using `fun a => by`. Establish `h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p`. Rewrite using `[hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]`. Conclude with `congrArg (fun x => x.ofConv a) h`. Establish `h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a` using `fun a => by`.

Establish `h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r`. Rewrite using `[hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]`. Conclude with `congrArg (fun x => x.ofConv a) h`. Use `⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩` and prove the remaining obligations. Use `Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Conclude with `h1 a`. Conclude with `Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)`.
-/
theorem shear (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by
  set S := AlgHom.range (f : B →ₐ[R] A) with hS
  set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI
  let l : WithConv (A →ₐ[R] A ⊗[S] A) := toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))
  let r : WithConv (A →ₐ[R] A ⊗[S] A) :=
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)
  let l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) := toConv (IsScalarTower.toAlgHom R A _)
  let p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) :=
    toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp
      (Ideal.Quotient.mkₐ R I))
  have hl : ∀ a, l.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hr : ∀ a, r.ofConv a = 1 ⊗ₜ a := fun a => rfl
  have hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a := fun a => rfl
  have hlr : pre f l = pre f r := conv_ext fun b => by
    rw [pre_apply, pre_apply, hl, hr]
    have := TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)
    simpa [Subalgebra.smul_def] using this
  have hpf : pre f p = 1 := conv_ext fun b => by
    rw [pre_apply, hp]
    have hb : b - algebraMap R B (Coalgebra.counit b) ∈
        RingHom.ker (Bialgebra.counitAlgHom R B) := by
      simp [RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)
      rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes] at h2
      exact h2
    rw [h1]
    exact (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _
  let g : A →ₐ[S] A ⊗[R] (A ⧸ I) :=
    { (l' * p).ofConv.toRingHom with
      commutes' := by
        rintro ⟨_, b, rfl⟩
        have h : pre f (l' * p) = pre f l' := by rw [map_mul, hpf, mul_one]
        have h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1 := congrArg (fun x => x.ofConv b) h
        exact h2 }
  let Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _
  have hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0 := by
    have h : pre f (l⁻¹ * r) = 1 := by rw [map_mul, map_inv, hlr, inv_mul_cancel]
    have : I ≤ RingHom.ker (l⁻¹ * r).ofConv := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      have h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b) :=
        congrArg (fun x => x.ofConv b) h
      have h3 : Coalgebra.counit (R := R) b = 0 := hb
      rw [h3, map_zero] at h2
      exact h2
    exact fun a ha => this ha
  let k : (A ⧸ I) →ₐ[R] A ⊗[S] A := Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk
  let Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _
  have hΦl : post (Φ.restrictScalars R) l = l' := conv_ext fun a => Φ.commutes a
  have hΦr : post (Φ.restrictScalars R) r = l' * p := conv_ext fun a => by
    change Φ (1 ⊗ₜ a) = g a
    simp [Φ, ← Algebra.TensorProduct.one_def]
  have hΨl : post (Ψ.restrictScalars R) l' = l := conv_ext fun a => Ψ.commutes a
  have hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r := conv_ext fun a => by
    change Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)
    simp [Ψ, ← Algebra.TensorProduct.one_def]
  have h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a := fun a => by
    have h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p := by
      rw [hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  have h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a := fun a => by
    have h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r := by
      rw [hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  refine ⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact h1 a
  · exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)

end GlobalTheory.HopfShear
