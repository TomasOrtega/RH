import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.PDiv Coalgebra Bialgebra WithConv

section Sep

variable {R : Type} [CommRing R] {M N P M' N' : Type} [CommRing M] [Algebra R M] [CommRing N] [Algebra R N]
  [CommRing P] [Algebra R P] [CommRing M'] [Algebra R M'] [CommRing N'] [Algebra R N']

def pair (x : M →ₐ[R] R) (y : N →ₐ[R] R) : M ⊗[R] N →ₐ[R] R :=
  Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pair_tmul (x : M →ₐ[R] R) (y : N →ₐ[R] R) (a : M) (b : N) : pair x y (a ⊗ₜ b) = x a * y b := rfl

/- English proof (translation)
Apply the tactic sequence `induction z <;> simp_all`.
-/
theorem pair_map (x : M →ₐ[R] R) (y : N →ₐ[R] R) (f : M' →ₐ[R] M) (g : N' →ₐ[R] N) (z : M' ⊗[R] N') :
    pair x y (Algebra.TensorProduct.map f g z) = pair (x.comp f) (y.comp g) z := by
  induction z <;> simp_all

/- English proof (translation)
Establish `: (pair x (pair y w)).comp (Algebra.TensorProduct.assoc R R R M N P).toAlgHom = pair (pair x y) w`. Apply the tactic sequence `ext <;> simp [Algebra.TensorProduct.one_def]`. Conclude with `DFunLike.congr_fun this z`.
-/
theorem pair_assoc (x : M →ₐ[R] R) (y : N →ₐ[R] R) (w : P →ₐ[R] R) (z : (M ⊗[R] N) ⊗[R] P) :
    pair x (pair y w) (Algebra.TensorProduct.assoc R R R M N P z) = pair (pair x y) w z := by
  have : (pair x (pair y w)).comp (Algebra.TensorProduct.assoc R R R M N P).toAlgHom = pair (pair x y) w := by
    ext <;> simp [Algebra.TensorProduct.one_def]
  exact DFunLike.congr_fun this z

/- English proof (translation)
Apply the tactic sequence `induction z <;> simp_all [mul_comm]`.
-/
theorem pair_comm (x : M →ₐ[R] R) (y : N →ₐ[R] R) (z : N ⊗[R] M) :
    pair x y (TensorProduct.comm R N M z) = pair y x z := by
  induction z <;> simp_all [mul_comm]

/- English proof (translation)
Apply the tactic sequence `induction z <;> simp_all`.
-/
theorem comp_lift (x : M →ₐ[R] R) (f : N →ₐ[R] M) (g : P →ₐ[R] M) (h) (z : N ⊗[R] P) :
    x (Algebra.TensorProduct.lift f g h z) = pair (x.comp f) (x.comp g) z := by
  induction z <;> simp_all

def Sep {S : Type} (ev : S → (M →ₐ[R] R)) : Prop := ∀ a b : M, (∀ s, ev s a = ev s b) → a = b

/- English proof (translation)
Use `Fintype.ofFinite S'` as an intermediate fact. Introduce `a b hab`. Set `i : N →ₗ[R] (S' → R)` to `LinearMap.pi fun t => (ev' t).toLinearMap`. Establish `hi : Function.Injective i` using `fun u v huv => h' u v fun t => congrFun huv t`. Apply `Module.Flat.lTensor_preserves_injective_linearMap (M := M) i hi` to reduce the goal to its premises.

Apply `(TensorProduct.piScalarRight R R M S').injective` to reduce the goal to its premises. Use function extensionality and compare the values at `t`. Use `h _ _ fun s => ?_` and prove the remaining obligations. Establish `key : ∀ z : M ⊗[R] N, ev s (TensorProduct.piScalarRight R R M S' (i.lTensor M z) t) = Twpdiv.pair (ev s) (ev' t) z`. Introduce `z`.

Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `tmul u v => simp [i, mul_comm]`. Consider the case `add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv]`. Rewrite using `[key, key]`.

Conclude with `hab (s, t)`.
-/
theorem Sep.pair {S S' : Type} [Finite S'] [Module.Flat R M] {ev : S → (M →ₐ[R] R)} {ev' : S' → (N →ₐ[R] R)}
    (h : Sep ev) (h' : Sep ev') : Sep (fun z : S × S' => pair (ev z.1) (ev' z.2)) := by
  classical
  have := Fintype.ofFinite S'
  intro a b hab
  let i : N →ₗ[R] (S' → R) := LinearMap.pi fun t => (ev' t).toLinearMap
  have hi : Function.Injective i := fun u v huv => h' u v fun t => congrFun huv t
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) i hi
  apply (TensorProduct.piScalarRight R R M S').injective
  funext t
  refine h _ _ fun s => ?_
  have key : ∀ z : M ⊗[R] N, ev s (TensorProduct.piScalarRight R R M S' (i.lTensor M z) t) =
      Twpdiv.pair (ev s) (ev' t) z := by
    intro z
    induction z with
    | zero => simp
    | tmul u v => simp [i, mul_comm]
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv]
  rw [key, key]
  exact hab (s, t)

end Sep

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] {A : Subalgebra R (T → R)}

def Ord (_ : IsHopfOrder A) : Type := A

namespace Ord

variable (h : IsHopfOrder A)

instance : CommRing (Ord h) := inferInstanceAs (CommRing A)
instance : Algebra R (Ord h) := inferInstanceAs (Algebra R A)
instance : Module.Finite R (Ord h) := h.finite
instance : Module.Projective R (Ord h) := h.projective

def equiv : Ord h ≃ₐ[R] A := AlgEquiv.refl

def ev (t : T) : Ord h →ₐ[R] R := (evalAt A t).comp (equiv h).toAlgHom

/- English proof (translation)
Introduce `_ _ hab` and use `(equiv h).injective (Subtype.ext (funext hab))`.
-/
theorem sep : Sep (ev h) := fun _ _ hab => (equiv h).injective (Subtype.ext (funext hab))

def liftTo {B : Type} [CommRing B] [Algebra R B] {S : Type} (e : S → (B →ₐ[R] R)) (he : Sep e)
    {B' : Type} [CommRing B'] [Algebra R B'] (e' : S → (B' →ₐ[R] R)) (H : ∀ f, ∃ g, ∀ s, e s g = e' s f) :
    B' →ₐ[R] B where
  toFun f := (H f).choose
  map_one' := he _ _ fun s => by rw [(H _).choose_spec, map_one, map_one]
  map_mul' a b := he _ _ fun s => by
    rw [map_mul, (H a).choose_spec, (H b).choose_spec, (H _).choose_spec, map_mul]
  map_zero' := he _ _ fun s => by rw [(H _).choose_spec, map_zero, map_zero]
  map_add' a b := he _ _ fun s => by
    rw [map_add, (H a).choose_spec, (H b).choose_spec, (H _).choose_spec, map_add]
  commutes' _ := he _ _ fun s => by rw [(H _).choose_spec, AlgHom.commutes, AlgHom.commutes]

/- English proof (translation)
The claim follows from `AlgHom.ext fun f => (H f).choose_spec s`.
-/
theorem ev_liftTo {B : Type} [CommRing B] [Algebra R B] {S : Type} (e : S → (B →ₐ[R] R)) (he : Sep e)
    {B' : Type} [CommRing B'] [Algebra R B'] (e' : S → (B' →ₐ[R] R)) (H : ∀ f, ∃ g, ∀ s, e s g = e' s f)
    (s : S) : (e s).comp (liftTo e he e' H) = e' s := AlgHom.ext fun f => (H f).choose_spec s

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨a, ha, b, hb, rfl⟩` from `hg`. Conclude with `⟨(equiv h).symm ⟨a, ha⟩ ⊗ₜ (equiv h).symm ⟨b, hb⟩, fun s => rfl⟩`. Consider the case `zero => exact ⟨0, fun s => by simp⟩`.

Consider the case `add u v _ _ hu hv`. Take `⟨a, ha⟩` from `hu`. Take `⟨b, hb⟩` from `hv`. Conclude with `⟨a + b, fun s => by simp [ha, hb]⟩`. Consider the case `smul c u _ hu`.

Take `⟨a, ha⟩` from `hu`. Conclude with `⟨c • a, fun s => by simp [ha]⟩`.
-/
theorem exists_of_mem_prodSpan {g : T × T → R} (hg : g ∈ prodSpan A) :
    ∃ z : Ord h ⊗[R] Ord h, ∀ s : T × T, pair (ev h s.1) (ev h s.2) z = g s := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact ⟨(equiv h).symm ⟨a, ha⟩ ⊗ₜ (equiv h).symm ⟨b, hb⟩, fun s => rfl⟩
  | zero => exact ⟨0, fun s => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, fun s => by simp [ha, hb]⟩
  | smul c u _ hu =>
    obtain ⟨a, ha⟩ := hu
    exact ⟨c • a, fun s => by simp [ha]⟩

def anti : Ord h →ₐ[R] Ord h :=
  liftTo (ev h) (sep h) (fun t => ev h t⁻¹) fun f => ⟨(equiv h).symm ⟨_, h.inv _ (equiv h f).2⟩, fun _ => rfl⟩

/- English proof (translation)
The claim follows from `ev_liftTo _ _ _ _ t`.
-/
theorem ev_anti (t : T) : (ev h t).comp (anti h) = ev h t⁻¹ := ev_liftTo _ _ _ _ t

variable [Finite T]

/- English proof (translation)
The claim follows from `(sep h).pair (sep h)`.
-/
theorem sep₂ : Sep (fun z : T × T => pair (ev h z.1) (ev h z.2)) := (sep h).pair (sep h)

def delta : Ord h →ₐ[R] Ord h ⊗[R] Ord h :=
  liftTo _ (sep₂ h) (fun z => ev h (z.1 * z.2)) fun f => exists_of_mem_prodSpan h (h.comul _ (equiv h f).2)

/- English proof (translation)
The claim follows from `ev_liftTo _ (sep₂ h) _ _ (s, t)`.
-/
theorem pair_comp_delta (s t : T) : (pair (ev h s) (ev h t)).comp (delta h) = ev h (s * t) :=
  ev_liftTo _ (sep₂ h) _ _ (s, t)

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (pair_comp_delta h s t) f`.
-/
theorem pair_delta (s t : T) (f : Ord h) : pair (ev h s) (ev h t) (delta h f) = ev h (s * t) f :=
  DFunLike.congr_fun (pair_comp_delta h s t) f

/- English proof (translation)
Introduce `_ _ h` and use `h ()`.
-/
theorem sep_id : Sep (fun _ : Unit => AlgHom.id R R) := fun _ _ h => h ()

instance : Bialgebra R (Ord h) :=
  Bialgebra.ofAlgHom (delta h) (ev h 1)
    (AlgHom.ext fun f => (sep h).pair (sep₂ h) _ _ fun z => by
      refine (pair_assoc _ _ _ (Algebra.TensorProduct.map (delta h) (AlgHom.id R _) (delta h f))).trans ?_
      simp only [AlgHom.comp_apply, pair_map, pair_comp_delta, AlgHom.comp_id, pair_delta, mul_assoc])
    (AlgHom.ext fun f => sep_id.pair (sep h) _ _ fun z => by
      simp [pair_map, pair_delta])
    (AlgHom.ext fun f => (sep h).pair sep_id _ _ fun z => by
      simp [pair_map, pair_delta])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comul_eq (f : Ord h) : comul (R := R) f = delta h f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem counit_eq (f : Ord h) : counit (R := R) f = ev h 1 f := rfl

instance : HopfAlgebra R (Ord h) :=
  HopfAlgebra.ofAlgHom (anti h)
    (AlgHom.ext fun f => sep h _ _ fun t => by
      refine (comp_lift (ev h t) (anti h) (AlgHom.id R _) (fun _ _ => Commute.all _ _) (delta h f)).trans ?_
      simp [ev_anti, comul_eq, counit_eq, pair_delta, Algebra.ofId_apply])
    (AlgHom.ext fun f => sep h _ _ fun t => by
      refine (comp_lift (ev h t) (AlgHom.id R _) (anti h) (fun _ _ => Commute.all _ _) (delta h f)).trans ?_
      simp [ev_anti, comul_eq, counit_eq, pair_delta, Algebra.ofId_apply])

instance : IsCocomm R (Ord h) :=
  ⟨LinearMap.ext fun f => sep₂ h _ _ fun z => by
    simp [pair_comm, comul_eq, pair_delta, mul_comm]⟩

def evHom : T →* WithConv (Ord h →ₐ[R] R) where
  toFun t := toConv (ev h t)
  map_one' := by ext f; simp [counit_eq]
  map_mul' s t := by
    ext f
    rw [AlgHom.convMul_apply]
    exact (pair_delta h s t f).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evHom_apply (t : T) : evHom h t = toConv (ev h t) := rfl

/- English proof (translation)
Establish `h1` using `comp_mulBy_pts (ev h t) k`. Rewrite `h1` using `[← evHom_apply, ← map_pow]`. Conclude with `DFunLike.congr_fun h1 f`.
-/
theorem ev_mulBy (t : T) (k : ℕ) (f : Ord h) : ev h t (mulBy R (Ord h) k f) = ev h (t ^ k) f := by
  have h1 := comp_mulBy_pts (ev h t) k
  rw [← evHom_apply, ← map_pow] at h1
  exact DFunLike.congr_fun h1 f

/- English proof (translation)
Use `Fintype.ofFinite T` as an intermediate fact. Take `⟨d, hd, hA⟩` from `h.full`. Set `e : T → Ord h` to `fun t => (equiv h).symm ⟨_, hA (Pi.single t 1)⟩`. Establish `he : ∀ s t, ev h s (e t) = if s = t then d else 0` using `fun s t => by`. Express the relevant statement in the definitionally equal form `d • (Pi.single t (1 : R) : T → R) s = _`.

Simplify using `[Pi.single_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `s t hst`. Establish `h1 : ev h s (e t) = ev h t (e t)` using `DFunLike.congr_fun (congrArg ofConv hst) (e t)`. Rewrite `h1` using `[he, he, if_pos rfl]`.

Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[if_neg hne]`. Conclude with `hd h1.symm`. Introduce `x`. Establish `h1 : ∑ t, e t = algebraMap R _ d` using `sep h _ _ fun s => by simp [he]`.

Take `⟨t, ht⟩ : ∃ t, x.ofConv (e t) ≠ 0` from `by by_contra! H`. Use `congrArg x.ofConv h1` as an intermediate fact. Simplify using `[H] at this`. Conclude with `hd this.symm`. Use `⟨t, ofConv_injective (AlgHom.ext fun f => ?_)⟩` and prove the remaining obligations.

Establish `h2 : f * e t = ev h t f • e t` using `sep h _ _ fun s => by`. Apply the tactic sequence `by_cases hs : s = t <;> simp [he, hs]`. Establish `h3` using `congrArg x.ofConv h2`. Rewrite `h3` using `[map_mul, map_smul, smul_eq_mul]`. Conclude with `(mul_right_cancel₀ ht h3).symm`.
-/
theorem evHom_bijective [IsDomain R] : Function.Bijective (evHom h) := by
  classical
  have := Fintype.ofFinite T
  obtain ⟨d, hd, hA⟩ := h.full
  let e : T → Ord h := fun t => (equiv h).symm ⟨_, hA (Pi.single t 1)⟩
  have he : ∀ s t, ev h s (e t) = if s = t then d else 0 := fun s t => by
    change d • (Pi.single t (1 : R) : T → R) s = _
    simp [Pi.single_apply]
  constructor
  · intro s t hst
    have h1 : ev h s (e t) = ev h t (e t) := DFunLike.congr_fun (congrArg ofConv hst) (e t)
    rw [he, he, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact hd h1.symm
  · intro x
    have h1 : ∑ t, e t = algebraMap R _ d := sep h _ _ fun s => by simp [he]
    obtain ⟨t, ht⟩ : ∃ t, x.ofConv (e t) ≠ 0 := by
      by_contra! H
      have := congrArg x.ofConv h1
      simp [H] at this
      exact hd this.symm
    refine ⟨t, ofConv_injective (AlgHom.ext fun f => ?_)⟩
    have h2 : f * e t = ev h t f • e t := sep h _ _ fun s => by
      by_cases hs : s = t <;> simp [he, hs]
    have h3 := congrArg x.ofConv h2
    rw [map_mul, map_smul, smul_eq_mul] at h3
    exact (mul_right_cancel₀ ht h3).symm

/- English proof (translation)
Use `Fintype.ofFinite T` as an intermediate fact. Take `⟨d, hd, hA⟩` from `h.full`. Rewrite using `[Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card R]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap ∘ₗ (equiv h).toLinearMap) (Subtype.val_injective.comp (equiv h).injective)`.

Use `LinearMap.finrank_le_finrank_of_injective (f := (equiv h).symm.toLinearMap ∘ₗ LinearMap.codRestrict A.toSubmodule (d • LinearMap.id) hA) ?_` and prove the remaining obligations. Introduce `u v huv`. Establish `h1 : d • u = d • v` using `congrArg Subtype.val ((equiv h).symm.injective huv)`. Use function extensionality and compare the values at `t`. Conclude with `mul_left_cancel₀ hd (congrFun h1 t)`.
-/
theorem finrank_eq [IsDomain R] : Module.finrank R (Ord h) = Nat.card T := by
  have := Fintype.ofFinite T
  obtain ⟨d, hd, hA⟩ := h.full
  rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card R]
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap ∘ₗ (equiv h).toLinearMap)
      (Subtype.val_injective.comp (equiv h).injective)
  · refine LinearMap.finrank_le_finrank_of_injective (f := (equiv h).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict A.toSubmodule (d • LinearMap.id) hA) ?_
    intro u v huv
    have h1 : d • u = d • v := congrArg Subtype.val ((equiv h).symm.injective huv)
    funext t
    exact mul_left_cancel₀ hd (congrFun h1 t)

/- English proof (translation)
Establish `: Module.Free R (Ord h)` using `Module.free_of_flat_of_isLocalRing`. Rewrite using `[Module.rankAtStalk_eq_finrank_of_free, finrank_eq]`. Both sides reduce to the same expression.
-/
theorem rankAtStalk_eq [IsDomain R] [IsLocalRing R] (q : PrimeSpectrum R) :
    Module.rankAtStalk (Ord h) q = Nat.card T := by
  have : Module.Free R (Ord h) := Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_eq]
  rfl

def comap {T' : Type} [CommGroup T'] [Finite T'] {A' : Subalgebra R (T' → R)} (h' : IsHopfOrder A') (ι : T →* T')
    (H : ∀ f ∈ A', (fun t => f (ι t)) ∈ A) : Ord h' →ₐc[R] Ord h :=
  let φ : Ord h' →ₐ[R] Ord h := liftTo (ev h) (sep h) (fun t => ev h' (ι t)) fun f =>
    ⟨(equiv h).symm ⟨_, H _ (equiv h' f).2⟩, fun _ => rfl⟩
  have hφ : ∀ t, (ev h t).comp φ = ev h' (ι t) := ev_liftTo _ _ _ _
  have hφ' : ∀ t f, ev h t (φ f) = ev h' (ι t) f := fun t f => DFunLike.congr_fun (hφ t) f
  BialgHom.ofAlgHom φ (AlgHom.ext fun f => by simp [counit_eq, hφ'])
    (AlgHom.ext fun f => sep₂ h _ _ fun z => by simp [pair_map, comul_eq, hφ, hφ', pair_delta])

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (ev_liftTo (ev h) (sep h) (fun t => ev h' (ι t)) (fun f => ⟨(equiv h).symm ⟨_, H _ (equiv h' f).2⟩, fun _ => rfl⟩) t) f`.
-/
theorem ev_comap {T' : Type} [CommGroup T'] [Finite T'] {A' : Subalgebra R (T' → R)} (h' : IsHopfOrder A')
    (ι : T →* T') (H : ∀ f ∈ A', (fun t => f (ι t)) ∈ A) (t : T) (f : Ord h') :
    ev h t (comap h h' ι H f) = ev h' (ι t) f :=
  DFunLike.congr_fun (ev_liftTo (ev h) (sep h) (fun t => ev h' (ι t)) (fun f =>
    ⟨(equiv h).symm ⟨_, H _ (equiv h' f).2⟩, fun _ => rfl⟩) t) f

end Ord

end PositivityTheory.HtPt.Twpdiv
