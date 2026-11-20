import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FormalChartOf

variable {R₀ : Type} [CommRing R₀]

/- English proof (translation)
Use `haveI : Nontrivial (DualNumber R₀) := TrivSqZeroExt.inl_injective.nontrivial`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Simplify using `only [TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify using `using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst`.
-/
theorem dual_local [IsLocalRing R₀] : IsLocalRing (DualNumber R₀) := by
  haveI : Nontrivial (DualNumber R₀) := TrivSqZeroExt.inl_injective.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

abbrev dualL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R₀) _ _ dual_local

abbrev baseL (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LAlg R₀ :=
  @LAlg.mk R₀ _ R₀ _ _ _

def dualProj (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : LHom (dualL R₀) (baseL R₀) :=
  ⟨TrivSqZeroExt.fstHom R₀ R₀ R₀, ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

/- English proof (translation)
Use `⟨2, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have : a = TrivSqZeroExt.inr a.snd := by ext <;> simp [h]`. Rewrite using `[this, pow_two, TrivSqZeroExt.inr_mul_inr]`.
-/
theorem tsze_nil {M : Type} [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M]
    (a : TrivSqZeroExt R₀ M) (h : a.fst = 0) : IsNilpotent a := by
  refine ⟨2, ?_⟩
  have : a = TrivSqZeroExt.inr a.snd := by ext <;> simp [h]
  rw [this, pow_two, TrivSqZeroExt.inr_mul_inr]

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[RingHom.mem_ker, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : TrivSqZeroExt.fst a = 0` using `h`.

Use `⟨TrivSqZeroExt.inl (TrivSqZeroExt.snd a), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [h']`. Introduce and unpack `⟨b, rfl⟩`. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.fst (b * DualNumber.eps) = 0`. Simplify using the standard rewrite rules.
-/
theorem dualProj_ker [IsLocalRing R₀] :
    RingHom.ker (dualProj R₀).1 = Ideal.span {(DualNumber.eps : DualNumber R₀)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro h
    have h' : TrivSqZeroExt.fst a = 0 := h
    refine ⟨TrivSqZeroExt.inl (TrivSqZeroExt.snd a), ?_⟩
    ext <;> simp [h']
  · rintro ⟨b, rfl⟩
    change TrivSqZeroExt.fst (b * DualNumber.eps) = 0
    simp

/- English proof (translation)
The claim follows from `LHom.sqZero_of_span _ (DualNumber.eps : DualNumber R₀) (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) dualProj_ker DualNumber.eps_mul_eps`.
-/
theorem dualProj_sqZero [IsLocalRing R₀] : (dualProj R₀).SqZero :=
  LHom.sqZero_of_span _ (DualNumber.eps : DualNumber R₀)
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) dualProj_ker DualNumber.eps_mul_eps

def epsK (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] : (dualProj R₀).ker :=
  ⟨(DualNumber.eps : DualNumber R₀), (rfl : TrivSqZeroExt.fst (DualNumber.eps : DualNumber R₀) = 0)⟩

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩`. Consider the case `tmul w a`. Use `⟨TrivSqZeroExt.snd (a.1 : DualNumber R₀) • w, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h' : TrivSqZeroExt.fst (a.1 : DualNumber R₀) = 0` using `a.2`. Express the relevant statement in the definitionally equal form `(a.1 : DualNumber R₀) = TrivSqZeroExt.snd (a.1 : DualNumber R₀) • (DualNumber.eps : DualNumber R₀)`. Apply the tactic sequence `ext <;> simp [h']`.

Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩`.
-/
theorem tmul_eps_surj [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (v : M ⊗[R₀] (dualProj R₀).ker) : ∃ w : M, v = w ⊗ₜ epsK R₀ := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
  | tmul w a =>
    refine ⟨TrivSqZeroExt.snd (a.1 : DualNumber R₀) • w, ?_⟩
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    have h' : TrivSqZeroExt.fst (a.1 : DualNumber R₀) = 0 := a.2
    change (a.1 : DualNumber R₀) = TrivSqZeroExt.snd (a.1 : DualNumber R₀) • (DualNumber.eps : DualNumber R₀)
    ext <;> simp [h']
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩

/- English proof (translation)
Set `s : (dualProj R₀).ker →ₗ[R₀] R₀` to `(TrivSqZeroExt.sndHom R₀ R₀).comp (dualProj R₀).ker.subtype`. Establish `hs : s (epsK R₀) = 1` using `rfl`. Use `congrArg (fun v => TensorProduct.rid R₀ M (LinearMap.lTensor M s v)) h` as an intermediate fact. Simplify `this` using `[hs]`.
-/
theorem tmul_eps_eq_zero [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (w : M) (h : w ⊗ₜ[R₀] epsK R₀ = 0) : w = 0 := by
  let s : (dualProj R₀).ker →ₗ[R₀] R₀ := (TrivSqZeroExt.sndHom R₀ R₀).comp (dualProj R₀).ker.subtype
  have hs : s (epsK R₀) = 1 := rfl
  have := congrArg (fun v => TensorProduct.rid R₀ M (LinearMap.lTensor M s v)) h
  simpa [hs] using this

def dualTo {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0) : DualNumber R₀ →ₐ[R₀] S :=
  DualNumber.lift ⟨(Algebra.ofId R₀ S, i), hi, fun _ => Commute.all _ _⟩

/- English proof (translation)
Rewrite using `[dualTo, DualNumber.lift_apply_apply, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem dualTo_apply {S : Type} [CommRing S] [Algebra R₀ S] (i : S) (hi : i * i = 0)
    (a : DualNumber R₀) : dualTo i hi a = algebraMap R₀ S a.fst + a.snd • i := by
  rw [dualTo, DualNumber.lift_apply_apply, Algebra.smul_def]
  rfl

def dualToL [IsLocalRing R₀] (S : LAlg R₀) (hS : IsLocalHom (algebraMap R₀ (S : Type)))
    (i : (S : Type)) (hi : i * i = 0) : LHom (dualL R₀) S :=
  ⟨dualTo i hi, ⟨fun a h => by
    have h' : IsUnit (dualTo i hi a) := h
    rw [dualTo_apply] at h'
    have hn : IsNilpotent (-(TrivSqZeroExt.snd a • i)) :=
      (IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _).neg
    have h2 := hn.isUnit_add_left_of_commute h' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (hS.map_nonunit _ h2)⟩⟩

section Coord

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G))
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
    (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)

include h0 hnat hinj hsurj in

/- English proof (translation)
Set `T` to `TrivSqZeroExt R₀ (R₀ × R₀)`. Set `a' : Fin g → T` to `fun k => TrivSqZeroExt.inr (a k, 0)`. Set `b' : Fin g → T` to `fun k => TrivSqZeroExt.inr (0, b k)`. Establish `ha' : ∀ k, IsNilpotent (a' k)` using `fun k => tsze_nil _ rfl`. Establish `hb' : ∀ k, IsNilpotent (b' k)` using `fun k => tsze_nil _ rfl`.

Establish `key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (φ : T →ₐ[R₀] S), spMap φ ≫ (x T a' * x T b') = x S (fun k => φ (a' k)) * x S (fun k => φ (b' k))`. Introduce `S _ _ φ`. Rewrite using `[MonObj.comp_mul, hnat _ _ φ a' ha', hnat _ _ φ b' hb']`. Take `⟨c, hc, hxc⟩` from `hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (R₀ × R₀)) (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun u hu => tsze_nil u hu) (x T a' * x T b') (by`. Rewrite using `[key]`.

Express the relevant statement in the definitionally equal form `x R₀ 0 * x R₀ 0 = 1`. Rewrite using `[h0, _root_.mul_one])`. Establish `hc0 : ∀ k, (c k).fst = 0` using `hc`. Establish `hcn : ∀ k, IsNilpotent (c k)` using `fun k => tsze_nil _ (hc0 k)`. Establish `key2 : ∀ f : (R₀ × R₀) →ₗ[R₀] R₀, x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (a k, 0))) * x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (0, b k))) = x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (c k).snd))`.

Introduce `f`. Establish `h` using `key (DualNumber R₀) (TrivSqZeroExt.map f)`. Rewrite `h` using `[hxc, hnat _ _ _ c hcn]`. Establish `e1 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (a' k)) = fun k => TrivSqZeroExt.inr (f (a k, 0))` using `funext fun k => TrivSqZeroExt.map_inr _ _`. Establish `e2 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (b' k)) = fun k => TrivSqZeroExt.inr (f (0, b k))` using `funext fun k => TrivSqZeroExt.map_inr _ _`.

Establish `e3 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (c k)) = fun k => TrivSqZeroExt.inr (f (c k).snd)` using `funext fun k => by`. Use `ext`. Rewrite using `[TrivSqZeroExt.fst_map, hc0]`. Both sides reduce to the same expression. Rewrite using `[TrivSqZeroExt.snd_map]`.

Both sides reduce to the same expression. Rewrite `h` using `[e1, e2, e3]`. Conclude with `h.symm`. Establish `hz : x (DualNumber R₀) (fun _ => TrivSqZeroExt.inr (0 : R₀)) = 1` using `h0 _`. Establish `k1` using `key2 (LinearMap.fst R₀ R₀ R₀)`.

Establish `k2` using `key2 (LinearMap.snd R₀ R₀ R₀)`. Establish `k3` using `key2 (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀)`. Simplify using `only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at k1 k2 k3`. Rewrite `k1` using `[hz, _root_.mul_one]`. Rewrite `k2` using `[hz, _root_.one_mul]`.

Establish `j1` using `hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k1`. Establish `j2` using `hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k2`. Rewrite using `[k3]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[TrivSqZeroExt.inr_injective (congrFun j1 k), TrivSqZeroExt.inr_injective (congrFun j2 k)]`.
-/
theorem first_order_add (a b : Fin g → R₀) :
    x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k)) *
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (b k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k + b k)) := by
  let T := TrivSqZeroExt R₀ (R₀ × R₀)
  let a' : Fin g → T := fun k => TrivSqZeroExt.inr (a k, 0)
  let b' : Fin g → T := fun k => TrivSqZeroExt.inr (0, b k)
  have ha' : ∀ k, IsNilpotent (a' k) := fun k => tsze_nil _ rfl
  have hb' : ∀ k, IsNilpotent (b' k) := fun k => tsze_nil _ rfl
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (φ : T →ₐ[R₀] S),
      spMap φ ≫ (x T a' * x T b') = x S (fun k => φ (a' k)) * x S (fun k => φ (b' k)) := by
    intro S _ _ φ
    rw [MonObj.comp_mul, hnat _ _ φ a' ha', hnat _ _ φ b' hb']
  obtain ⟨c, hc, hxc⟩ := hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (R₀ × R₀))
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun u hu => tsze_nil u hu) (x T a' * x T b') (by
      rw [key]
      change x R₀ 0 * x R₀ 0 = 1
      rw [h0, _root_.mul_one])
  have hc0 : ∀ k, (c k).fst = 0 := hc
  have hcn : ∀ k, IsNilpotent (c k) := fun k => tsze_nil _ (hc0 k)
  have key2 : ∀ f : (R₀ × R₀) →ₗ[R₀] R₀,
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (a k, 0))) *
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (0, b k))) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (c k).snd)) := by
    intro f
    have h := key (DualNumber R₀) (TrivSqZeroExt.map f)
    rw [hxc, hnat _ _ _ c hcn] at h
    have e1 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (a' k)) =
        fun k => TrivSqZeroExt.inr (f (a k, 0)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e2 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (b' k)) =
        fun k => TrivSqZeroExt.inr (f (0, b k)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e3 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (c k)) =
        fun k => TrivSqZeroExt.inr (f (c k).snd) := funext fun k => by
      ext
      · rw [TrivSqZeroExt.fst_map, hc0]; rfl
      · rw [TrivSqZeroExt.snd_map]; rfl
    rw [e1, e2, e3] at h
    exact h.symm
  have hz : x (DualNumber R₀) (fun _ => TrivSqZeroExt.inr (0 : R₀)) = 1 := h0 _
  have k1 := key2 (LinearMap.fst R₀ R₀ R₀)
  have k2 := key2 (LinearMap.snd R₀ R₀ R₀)
  have k3 := key2 (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at k1 k2 k3
  rw [hz, _root_.mul_one] at k1
  rw [hz, _root_.one_mul] at k2
  have j1 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k1
  have j2 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k2
  rw [k3]
  congr 1
  funext k
  rw [TrivSqZeroExt.inr_injective (congrFun j1 k), TrivSqZeroExt.inr_injective (congrFun j2 k)]

variable [IsLocalRing R₀] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G))
  (he : ∀ R, Function.Bijective (e R)) (hadd : ∀ R x y, e R (x + y) = e R x * e R y)
  (hen : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)

omit [IsLocalRing R₀] in
include hadd in
/- English proof (translation)
Establish `h` using `hadd R 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem e_zero (R : LAlg R₀) : e R 0 = 1 := by
  have h := hadd R 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

include h0 hnat hinj hsurj he hadd hen in

/- English proof (translation)
Establish `hex : ∀ w : B.gg, ∃ t : Fin g → R₀, e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) = x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k))`. Introduce `w`. Take `⟨c, hc, hxc⟩` from `hsurj (DualNumber R₀) R₀ (dualProj R₀).1 dualProj_sqZero.1 (fun u hu => tsze_nil u hu) (e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀))) (by`. Use `(hen (dualProj R₀) _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[(B.tg_ker _ dualProj_sqZero _).2 ⟨_, rfl⟩]`.

Conclude with `e_zero B e hadd _)`. Establish `hc0 : ∀ k, (c k).fst = 0` using `hc`. Use `⟨fun k => (c k).snd, hxc.trans ?_⟩` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `k`.

Apply the tactic sequence `ext <;> simp [hc0]`. Use `choose θ hθ using hex`. Establish `huniq : ∀ s t : Fin g → R₀, x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (s k)) = x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) → s = t` using `fun s t h =>`. Use function extensionality and compare the values at `fun k => TrivSqZeroExt.inr_injective (congrFun (hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) h) k)`. Establish `hθadd : ∀ v w, θ (v + w) = θ v + θ w`.

Introduce `v w`. Apply `huniq` to reduce the goal to its premises. Rewrite using `[← hθ, TensorProduct.add_tmul, map_add, hadd, hθ, hθ, first_order_add x h0 hnat hinj hsurj]`. Both sides reduce to the same expression. Establish `hθsmul : ∀ (r : R₀) w, θ (r • w) = r • θ w`.

Introduce `r w`. Apply `huniq` to reduce the goal to its premises. Establish `hi : (r • DualNumber.eps : DualNumber R₀) * (r • DualNumber.eps) = 0`. Rewrite using `[smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]`. Set `f : LHom (dualL R₀) (dualL R₀)` to `dualToL (dualL R₀) ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h⟩ (r • DualNumber.eps) hi`.

Establish `hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • r • DualNumber.eps` using `fun a => dualTo_apply _ hi a`. Establish `hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ (dualProj R₀).ker`. Introduce `a ha`. Establish `ha' : TrivSqZeroExt.fst a = 0` using `ha`. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.fst (f.1 a) = 0`.

Rewrite using `[hfa, ha']`. Simplify using the standard rewrite rules. Establish `h` using `B.tg_nat _ _ dualProj_sqZero dualProj_sqZero f hf (w ⊗ₜ epsK R₀)`. Establish `h2 : f.1.toLinearMap.restrict hf (epsK R₀) = r • epsK R₀`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `f.1 DualNumber.eps = r • DualNumber.eps`. Rewrite using `[hfa]`. Simplify using the standard rewrite rules. Rewrite `h` using `[LinearMap.lTensor_tmul, h2, ← TensorProduct.smul_tmul]`. Rewrite using `[← hθ, h, hen, hθ]`.

Use `(hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[hfa]`. Apply the tactic sequence `ext <;> simp [mul_comm]`.

Set `L : B.gg →ₗ[R₀] (Fin g → R₀)` to `⟨⟨θ, hθadd⟩, hθsmul⟩`. Establish `hL : Function.Bijective L`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`.

Establish `hw' : θ w = 0` using `hw`. Establish `h` using `hθ w`. Rewrite `h` using `[hw']`. Establish `h1 : e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) = e (dualL R₀) 0`. Rewrite using `[h, e_zero B e hadd]`.

Conclude with `h0 (DualNumber R₀)`. Establish `h2` using `(he _).1 h1`. Rewrite `h2` using `[← map_zero (B.tg (dualProj R₀) dualProj_sqZero)]`. Conclude with `tmul_eps_eq_zero w (B.tg_inj _ _ h2)`. Introduce `t`.

Take `⟨y, hy⟩` from `(he (dualL R₀)).2 (x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)))`. Establish `hy0 : B.map (dualProj R₀) y = 0`. Apply `(he _).1` to reduce the goal to its premises. Rewrite using `[hen, hy, e_zero B e hadd]`. Conclude with `(hnat _ _ (dualProj R₀).1 _ (fun k => tsze_nil _ rfl)).trans (h0 R₀)`.

Take `⟨v, hv⟩` from `(B.tg_ker _ dualProj_sqZero y).1 hy0`. Take `⟨w, rfl⟩` from `tmul_eps_surj v`. Establish `h3 : θ w = t` using `huniq (θ w) t (by rw [← hθ, hv, hy])`. Conclude with `⟨w, h3⟩`. Use `⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL), fun w => ?_⟩` and prove the remaining obligations.

Establish `h4 : ∀ k, (Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL)).repr w k = θ w k` using `fun k => by`. Rewrite using `[Module.Basis.ofEquivFun_repr_apply]`. Both sides reduce to the same expression. Simplify using `only [h4]`. Conclude with `hθ w`.
-/
theorem exists_basis : ∃ gb : Module.Basis (Fin g) R₀ B.gg, ∀ w : B.gg,
    e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (gb.repr w k)) := by
  have hex : ∀ w : B.gg, ∃ t : Fin g → R₀,
      e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) := by
    intro w
    obtain ⟨c, hc, hxc⟩ := hsurj (DualNumber R₀) R₀ (dualProj R₀).1 dualProj_sqZero.1
      (fun u hu => tsze_nil u hu) (e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀))) (by
        refine (hen (dualProj R₀) _).symm.trans ?_
        rw [(B.tg_ker _ dualProj_sqZero _).2 ⟨_, rfl⟩]
        exact e_zero B e hadd _)
    have hc0 : ∀ k, (c k).fst = 0 := hc
    refine ⟨fun k => (c k).snd, hxc.trans ?_⟩
    congr 1
    funext k
    ext <;> simp [hc0]
  choose θ hθ using hex
  have huniq : ∀ s t : Fin g → R₀, x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (s k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) → s = t := fun s t h =>
    funext fun k => TrivSqZeroExt.inr_injective
      (congrFun (hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) h) k)
  have hθadd : ∀ v w, θ (v + w) = θ v + θ w := by
    intro v w
    apply huniq
    rw [← hθ, TensorProduct.add_tmul, map_add, hadd, hθ, hθ, first_order_add x h0 hnat hinj hsurj]
    rfl
  have hθsmul : ∀ (r : R₀) w, θ (r • w) = r • θ w := by
    intro r w
    apply huniq
    have hi : (r • DualNumber.eps : DualNumber R₀) * (r • DualNumber.eps) = 0 := by
      rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]
    let f : LHom (dualL R₀) (dualL R₀) := dualToL (dualL R₀)
      ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h⟩ (r • DualNumber.eps) hi
    have hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • r • DualNumber.eps :=
      fun a => dualTo_apply _ hi a
    have hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ (dualProj R₀).ker := by
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      change TrivSqZeroExt.fst (f.1 a) = 0
      rw [hfa, ha']
      simp
    have h := B.tg_nat _ _ dualProj_sqZero dualProj_sqZero f hf (w ⊗ₜ epsK R₀)
    have h2 : f.1.toLinearMap.restrict hf (epsK R₀) = r • epsK R₀ := by
      apply Subtype.ext
      change f.1 DualNumber.eps = r • DualNumber.eps
      rw [hfa]
      simp
    rw [LinearMap.lTensor_tmul, h2, ← TensorProduct.smul_tmul] at h
    rw [← hθ, h, hen, hθ]
    refine (hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_
    congr 1
    funext k
    rw [hfa]
    ext <;> simp [mul_comm]
  let L : B.gg →ₗ[R₀] (Fin g → R₀) := ⟨⟨θ, hθadd⟩, hθsmul⟩
  have hL : Function.Bijective L := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      have hw' : θ w = 0 := hw
      have h := hθ w
      rw [hw'] at h
      have h1 : e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) = e (dualL R₀) 0 := by
        rw [h, e_zero B e hadd]
        exact h0 (DualNumber R₀)
      have h2 := (he _).1 h1
      rw [← map_zero (B.tg (dualProj R₀) dualProj_sqZero)] at h2
      exact tmul_eps_eq_zero w (B.tg_inj _ _ h2)
    · intro t
      obtain ⟨y, hy⟩ := (he (dualL R₀)).2 (x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)))
      have hy0 : B.map (dualProj R₀) y = 0 := by
        apply (he _).1
        rw [hen, hy, e_zero B e hadd]
        exact (hnat _ _ (dualProj R₀).1 _ (fun k => tsze_nil _ rfl)).trans (h0 R₀)
      obtain ⟨v, hv⟩ := (B.tg_ker _ dualProj_sqZero y).1 hy0
      obtain ⟨w, rfl⟩ := tmul_eps_surj v
      have h3 : θ w = t := huniq (θ w) t (by rw [← hθ, hv, hy])
      exact ⟨w, h3⟩
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL), fun w => ?_⟩
  have h4 : ∀ k, (Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL)).repr w k = θ w k := fun k => by
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  simp only [h4]
  exact hθ w

end Coord

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `: ρ.1 a ∈ maximalIdeal (K : Type)` using `fun h => ha (ρ.2.map_nonunit a h)`. Rewrite `this` using `[hK]`. Conclude with `this`.

Introduce `ha`. Conclude with `(hρ.2 a ha).not_isUnit`.
-/
theorem mem_max_iff {R K : LAlg R₀} (hK : maximalIdeal (K : Type) = ⊥) (ρ : LHom R K)
    (hρ : IsNilOver ρ) (a : (R : Type)) : a ∈ maximalIdeal (R : Type) ↔ a ∈ RingHom.ker ρ.1 := by
  constructor
  · intro ha
    have : ρ.1 a ∈ maximalIdeal (K : Type) := fun h => ha (ρ.2.map_nonunit a h)
    rw [hK] at this
    exact this
  · intro ha
    exact (hρ.2 a ha).not_isUnit

/- English proof (translation)
Establish `: Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ (⟨i, rfl⟩ | ⟨i, rfl⟩)`. Conclude with `mem_nilradical.2 (ha i)`. Conclude with `mem_nilradical.2 (hb i)`.

Conclude with `mem_nilradical.1 (this hc)`.
-/
theorem nil_of_mem_span {S : Type} [CommRing S] {g : ℕ} {a b : Fin g → S} (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) {c : S} (hc : c ∈ Ideal.span (Set.range a ∪ Set.range b)) :
    IsNilpotent c := by
  have : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := by
    rw [Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_nilradical.2 (ha i)
    · exact mem_nilradical.2 (hb i)
  exact mem_nilradical.1 (this hc)

/- English proof (translation)
Introduce `hN hL R₀ _ G _ _ _ g B e he hadd hen hsm K hK hKl`. Take `⟨x, hx⟩` from `hN G g hsm`. Take `⟨F, hF⟩` from `hL G g x hx`. Take `⟨h0, hnat, hinj, hsurj⟩` from `hx`. Take `⟨gb, hgb⟩` from `exists_basis x h0 hnat hinj hsurj B e he hadd hen`.

Establish `hFn : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd F a b k)` using `fun S _ _ a b ha hb k => nil_of_mem_span ha hb ((hF S a b ha hb).1 k)`. Establish `hχ : ∀ {R : LAlg R₀} (ρ : LHom R K), IsNilOver ρ → ∃ χ : {y : B.G R // B.map ρ y = 0} ≃ (Fin g → maximalIdeal (R : Type)), ∀ y, e R y.1 = x R (fun k => (χ y k : (R : Type)))`. Introduce `R ρ hρ`. Establish `hn : ∀ (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type))` using `fun a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)`. Establish `hex : ∀ y : {y : B.G R // B.map ρ y = 0}, ∃ a : Fin g → maximalIdeal (R : Type), e R y.1 = x R (fun k => (a k : (R : Type)))`.

Introduce `y`. Take `⟨c, hc, hxc⟩` from `hsurj R K ρ.1 hρ.1 hρ.2 (e R y.1) (by`. Rewrite using `[← hen, y.2, e_zero B e hadd])`. Conclude with `⟨fun k => ⟨c k, (mem_max_iff hK ρ hρ _).2 (hc k)⟩, hxc⟩`. Use `choose c hc using hex`.

Use `⟨Equiv.ofBijective c ⟨fun y y' h => ?_, fun a => ?_⟩, hc⟩` and prove the remaining obligations. Conclude with `Subtype.ext ((he R).1 (by rw [hc, hc, h]))`. Take `⟨y, hy⟩` from `(he R).2 (x R (fun k => (a k : (R : Type))))`. Establish `hy0 : B.map ρ y = 0`. Apply `(he _).1` to reduce the goal to its premises.

Rewrite using `[hen, hy, e_zero B e hadd, hnat _ _ ρ.1 _ (hn a), ← h0 K]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(mem_max_iff hK ρ hρ _).1 (a k).2`. Use `⟨⟨y, hy0⟩, funext fun k => Subtype.ext ?_⟩` and prove the remaining obligations.

Conclude with `congrFun (hinj _ _ _ (hn _) (hn a) ((hc ⟨y, hy0⟩).symm.trans hy)) k`. Use `choose χ hχ using @hχ`. Establish `hn : ∀ {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type))` using `fun ρ hρ a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)`. Use `⟨⟨F, ?_, ?_, ?_, gb, fun {R} ρ hρ => @χ R ρ hρ, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `S _ _ a ha`.

Establish `hz : ∀ i, IsNilpotent ((0 : Fin g → S) i)` using `fun _ => IsNilpotent.zero`. Apply `hinj S _ _ (hFn S a 0 ha hz) ha` to reduce the goal to its premises. Rewrite using `[← (hF S a 0 ha hz).2, h0, _root_.mul_one]`. Introduce `S _ _ a b ha hb`. Apply `hinj S _ _ (hFn S a b ha hb) (hFn S b a hb ha)` to reduce the goal to its premises.

Rewrite using `[← (hF S a b ha hb).2, ← (hF S b a hb ha).2, _root_.mul_comm]`. Introduce `S _ _ a b c ha hb hc`. Establish `hab` using `hFn S a b ha hb`. Establish `hbc` using `hFn S b c hb hc`. Apply `hinj S _ _ (hFn S _ c hab hc) (hFn S a _ ha hbc)` to reduce the goal to its premises.

Rewrite using `[← (hF S _ c hab hc).2, ← (hF S a _ ha hbc).2, ← (hF S a b ha hb).2, ← (hF S b c hb hc).2, _root_.mul_assoc]`. Introduce `R ρ hρ y z`. Apply `hinj R _ _ (hn ρ hρ _) (hFn R _ _ (hn ρ hρ _) (hn ρ hρ _))` to reduce the goal to its premises. Rewrite using `[← (hF R _ _ (hn ρ hρ _) (hn ρ hρ _)).2, ← hχ, ← hχ, ← hχ, hadd]`. Introduce `R R' ρ ρ' hρ hρ' f hf y k`.

Use `congrFun (hinj R' (fun k => (χ ρ' hρ' ⟨B.map f y.1, map_nat_ker B ρ ρ' f hf y⟩ k : (R' : Type))) (fun k => f.1 (χ ρ hρ y k : (R : Type))) (hn ρ' hρ' _) (fun k => (hn ρ hρ _ k).map f.1) ?_) k` and prove the remaining obligations. Rewrite using `[← hχ, ← hnat _ _ f.1 _ (hn ρ hρ _), ← hχ, hen]`. Introduce `R S ρ hρ π hπ ρS hfac w i k`. Establish `hi : (i : (R : Type)) * i = 0`. Establish `h : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2`.

Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul i.2 i.2`. Rewrite `h` using `[hπ.2]`. Conclude with `h`. Establish `hR : IsLocalHom (algebraMap R₀ (R : Type))` using `⟨fun a h => hKl.map_nonunit a (by`.

Rewrite using `[← ρ.1.commutes]`. Conclude with `h.map ρ.1)⟩`. Set `f : LHom (dualL R₀) R` to `dualToL R hR i hi`. Establish `hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • (i : (R : Type))` using `fun a => dualTo_apply _ hi a`. Establish `hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ π.ker`.

Introduce `a ha`. Establish `ha' : TrivSqZeroExt.fst a = 0` using `ha`. Express the relevant statement in the definitionally equal form `f.1 a ∈ π.ker`. Rewrite using `[hfa, ha', map_zero, zero_add]`. Conclude with `π.ker.smul_mem _ i.2`.

Establish `h` using `B.tg_nat _ _ dualProj_sqZero hπ f hf (w ⊗ₜ epsK R₀)`. Establish `h2 : f.1.toLinearMap.restrict hf (epsK R₀) = i`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f.1 DualNumber.eps = i`. Rewrite using `[hfa]`.

Simplify using the standard rewrite rules. Rewrite `h` using `[LinearMap.lTensor_tmul, h2]`. Use `congrFun (hinj R (fun k => (χ ρ hρ ⟨B.tg π hπ (w ⊗ₜ i), map_tg_ker B ρ π hπ ρS hfac _⟩ k : (R : Type))) (fun k => gb.repr w k • (i : (R : Type))) (hn ρ hρ _) (fun k => IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _) ?_) k` and prove the remaining obligations. Rewrite using `[← hχ]`. Express the relevant statement in the definitionally equal form `e R (B.tg π hπ (w ⊗ₜ i)) = _`.

Rewrite using `[h, hen, hgb]`. Use `(hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[hfa]`.

Simplify using the standard rewrite rules.
-/
theorem exists_formalChart :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → ∀ K : LAlg R₀, maximalIdeal (K : Type) = ⊥ →
    IsLocalHom (algebraMap R₀ (K : Type)) → Nonempty (FormalChartAtZero B K g)) := by
  intro hN hL R₀ _ G _ _ _ g B e he hadd hen hsm K hK hKl
  obtain ⟨x, hx⟩ := hN G g hsm
  obtain ⟨F, hF⟩ := hL G g x hx
  obtain ⟨h0, hnat, hinj, hsurj⟩ := hx
  obtain ⟨gb, hgb⟩ := exists_basis x h0 hnat hinj hsurj B e he hadd hen
  have hFn : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd F a b k) :=
    fun S _ _ a b ha hb k => nil_of_mem_span ha hb ((hF S a b ha hb).1 k)
  have hχ : ∀ {R : LAlg R₀} (ρ : LHom R K), IsNilOver ρ →
      ∃ χ : {y : B.G R // B.map ρ y = 0} ≃ (Fin g → maximalIdeal (R : Type)),
        ∀ y, e R y.1 = x R (fun k => (χ y k : (R : Type))) := by
    intro R ρ hρ
    have hn : ∀ (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type)) :=
      fun a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)
    have hex : ∀ y : {y : B.G R // B.map ρ y = 0}, ∃ a : Fin g → maximalIdeal (R : Type),
        e R y.1 = x R (fun k => (a k : (R : Type))) := by
      intro y
      obtain ⟨c, hc, hxc⟩ := hsurj R K ρ.1 hρ.1 hρ.2 (e R y.1) (by
        rw [← hen, y.2, e_zero B e hadd])
      exact ⟨fun k => ⟨c k, (mem_max_iff hK ρ hρ _).2 (hc k)⟩, hxc⟩
    choose c hc using hex
    refine ⟨Equiv.ofBijective c ⟨fun y y' h => ?_, fun a => ?_⟩, hc⟩
    · exact Subtype.ext ((he R).1 (by rw [hc, hc, h]))
    · obtain ⟨y, hy⟩ := (he R).2 (x R (fun k => (a k : (R : Type))))
      have hy0 : B.map ρ y = 0 := by
        apply (he _).1
        rw [hen, hy, e_zero B e hadd, hnat _ _ ρ.1 _ (hn a), ← h0 K]
        congr 1
        funext k
        exact (mem_max_iff hK ρ hρ _).1 (a k).2
      refine ⟨⟨y, hy0⟩, funext fun k => Subtype.ext ?_⟩
      exact congrFun (hinj _ _ _ (hn _) (hn a) ((hc ⟨y, hy0⟩).symm.trans hy)) k
  choose χ hχ using @hχ
  have hn : ∀ {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
      (a : Fin g → maximalIdeal (R : Type)) k, IsNilpotent (a k : (R : Type)) :=
    fun ρ hρ a k => hρ.2 _ ((mem_max_iff hK ρ hρ _).1 (a k).2)
  refine ⟨⟨F, ?_, ?_, ?_, gb, fun {R} ρ hρ => @χ R ρ hρ, ?_, ?_, ?_⟩⟩
  · intro S _ _ a ha
    have hz : ∀ i, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
    apply hinj S _ _ (hFn S a 0 ha hz) ha
    rw [← (hF S a 0 ha hz).2, h0, _root_.mul_one]
  · intro S _ _ a b ha hb
    apply hinj S _ _ (hFn S a b ha hb) (hFn S b a hb ha)
    rw [← (hF S a b ha hb).2, ← (hF S b a hb ha).2, _root_.mul_comm]
  · intro S _ _ a b c ha hb hc
    have hab := hFn S a b ha hb
    have hbc := hFn S b c hb hc
    apply hinj S _ _ (hFn S _ c hab hc) (hFn S a _ ha hbc)
    rw [← (hF S _ c hab hc).2, ← (hF S a _ ha hbc).2, ← (hF S a b ha hb).2, ← (hF S b c hb hc).2,
      _root_.mul_assoc]
  · intro R ρ hρ y z
    apply hinj R _ _ (hn ρ hρ _) (hFn R _ _ (hn ρ hρ _) (hn ρ hρ _))
    rw [← (hF R _ _ (hn ρ hρ _) (hn ρ hρ _)).2, ← hχ, ← hχ, ← hχ, hadd]
  · intro R R' ρ ρ' hρ hρ' f hf y k
    refine congrFun (hinj R' (fun k => (χ ρ' hρ' ⟨B.map f y.1, map_nat_ker B ρ ρ' f hf y⟩ k : (R' : Type)))
      (fun k => f.1 (χ ρ hρ y k : (R : Type))) (hn ρ' hρ' _) (fun k => (hn ρ hρ _ k).map f.1) ?_) k
    rw [← hχ, ← hnat _ _ f.1 _ (hn ρ hρ _), ← hχ, hen]
  · intro R S ρ hρ π hπ ρS hfac w i k
    have hi : (i : (R : Type)) * i = 0 := by
      have h : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul i.2 i.2
      rw [hπ.2] at h
      exact h
    have hR : IsLocalHom (algebraMap R₀ (R : Type)) := ⟨fun a h => hKl.map_nonunit a (by
      rw [← ρ.1.commutes]
      exact h.map ρ.1)⟩
    let f : LHom (dualL R₀) R := dualToL R hR i hi
    have hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • (i : (R : Type)) :=
      fun a => dualTo_apply _ hi a
    have hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ π.ker := by
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      change f.1 a ∈ π.ker
      rw [hfa, ha', map_zero, zero_add]
      exact π.ker.smul_mem _ i.2
    have h := B.tg_nat _ _ dualProj_sqZero hπ f hf (w ⊗ₜ epsK R₀)
    have h2 : f.1.toLinearMap.restrict hf (epsK R₀) = i := by
      apply Subtype.ext
      change f.1 DualNumber.eps = i
      rw [hfa]
      simp
    rw [LinearMap.lTensor_tmul, h2] at h
    refine congrFun (hinj R
      (fun k => (χ ρ hρ ⟨B.tg π hπ (w ⊗ₜ i), map_tg_ker B ρ π hπ ρS hfac _⟩ k : (R : Type)))
      (fun k => gb.repr w k • (i : (R : Type))) (hn ρ hρ _)
      (fun k => IsNilpotent.smul ⟨2, by rw [pow_two, hi]⟩ _) ?_) k
    rw [← hχ]
    change e R (B.tg π hπ (w ⊗ₜ i)) = _
    rw [h, hen, hgb]
    refine (hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_
    congr 1
    funext k
    rw [hfa]
    simp

end GlobalTheory.FormalChartOf
