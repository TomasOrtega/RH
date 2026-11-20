import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.LinDir

/- English proof (translation)
Unfold `pbT`. Rewrite using `[dif_pos (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]`. Establish `: (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _`. Express the relevant statement in the definitionally equal form `𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dif_pos (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

/- English proof (translation)
Simplify using `[constFn]`.
-/
theorem constFn_lin {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (c x y : K) :
    constFn q O (c * x + y) - constFn q O c * constFn q O x - constFn q O y = constFn q O 0 := by
  simp [constFn]

/- English proof (translation)
Rewrite using `[h.add W hW, h'.add W hW, h''.add W hW]`. Expand and normalize the polynomial expressions, which then agree. Use `mul W hW f f' := by`. Rewrite using `[h.mul W hW, h'.mul W hW, h''.mul W hW]`. Expand and normalize the polynomial expressions, which then agree.

Use `res W W' l hW f := by`. Rewrite using `[h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul, rsT_constFn q (m.preimage_mono l)]`. Use `base W hW r := by`. Rewrite using `[h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]`.
-/
theorem locDerK_comb {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W hW, h'.add W hW, h''.add W hW]; ring
  mul W hW f f' := by
    rw [h.mul W hW, h'.mul W hW, h''.mul W hW]; ring
  res W W' l hW f := by
    rw [h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul,
      rsT_constFn q (m.preimage_mono l)]
  base W hW r := by
    rw [h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]

/- English proof (translation)
Simplify using `mul W hW f f' := by simp res W W' l hW f := by rw [rsT_zero] base W hW r := by simp [constFn]`.
-/
theorem locDerK_zero {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (W₀ : X.Opens) : LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) where
  add W hW f f' := by simp
  mul W hW f f' := by simp
  res W W' l hW f := by rw [rsT_zero]
  base W hW r := by simp [constFn]

/- English proof (translation)
Establish `key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' → ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d → ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, d W f = ∑ a, rsT (c a) _ * …`. Introduce `y m' q' e₁ e₂ d h`. Substitute `e₁ e₂` using the available equality. Conclude with `GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h`. Use `key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h` as an intermediate fact.

Simplify `this` using `only [pbT_id]`.
-/
theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

/- English proof (translation)
Introduce `K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp I W D D' c d d' d'' θ θ' θ'' h h' h'' a`. Establish `hb` using `basis_id K A₀ g v dd hs hv hd R x₀ X p m hp`. Use `choose b hbb using fun i => (hb (W i) _ (locDerK_comb (h.der i) (h'.der i) (h''.der i))).exists`. Use `⟨fun i => b i a, fun i j => ?_⟩` and prove the remaining obligations. Establish `e : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j)` using `rfl`.

Establish `hu` using `(hb (W i ⊓ W j) _ (locDerK_zero A₀.hom p m _)).unique (y₁ := fun a => rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j - (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) _) (y₂ := fun _ => 0) (by`. Introduce `O hO f`. Establish `l : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j` using `(m.preimage_mono hO).trans e.ge`. Establish `h1` using `h.diff i j O hO f`. Establish `h2` using `h'.diff i j O hO f`.

Establish `h3` using `h''.diff i j O hO f`. Establish `h4` using `hbb i O (hO.trans inf_le_left) f`. Establish `h5` using `hbb j O (hO.trans inf_le_right) f`. Establish `: ∀ a, rsT (rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j - (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) (m ⁻¹ᵁ (W i ⊓ W j))) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = rsT (θ'' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) - c …`. Introduce `a`.

Rewrite using `[rsT_rsT e.ge (m.preimage_mono hO), rsT_sub, rsT_sub, rsT_sub, rsT_sub, rsT_mul, rsT_constFn _ l, rsT_rsT inf_le_left l, rsT_rsT inf_le_right l]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Rewrite using `[← h1, ← h2, ← h3, ← h4, ← h5]`. Use the proof step `ring)`.

Use the proof step `(by`. Introduce `O hO f`. Simplify using `only [rsT_zero, zero_mul, Finset.sum_const_zero])`. Establish `h0` using `congrArg (fun s => rsT s (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j)) (congrFun hu a)`. Simplify using `only [] at h0`.

Rewrite `h0` using `[rsT_rsT e.ge e.le, rsT_self, rsT_zero]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem ksCoc_linear : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp I W D D' c d d' d'' θ θ' θ'' h h' h'' a
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose b hbb using fun i => (hb (W i) _ (locDerK_comb (h.der i) (h'.der i) (h''.der i))).exists
  refine ⟨fun i => b i a, fun i j => ?_⟩
  have e : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := rfl
  have hu := (hb (W i ⊓ W j) _ (locDerK_zero A₀.hom p m _)).unique
    (y₁ := fun a => rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
      (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) _) (y₂ := fun _ => 0)
    (by
      intro O hO f
      have l : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j := (m.preimage_mono hO).trans e.ge
      have h1 := h.diff i j O hO f
      have h2 := h'.diff i j O hO f
      have h3 := h''.diff i j O hO f
      have h4 := hbb i O (hO.trans inf_le_left) f
      have h5 := hbb j O (hO.trans inf_le_right) f
      have : ∀ a, rsT (rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
          (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) (m ⁻¹ᵁ (W i ⊓ W j)))
          (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) =
          rsT (θ'' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - constFn A₀.hom (m ⁻¹ᵁ O) c * (rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f))
          - rsT (θ' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - (rsT (b j a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
            - rsT (b i a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) := by
        intro a
        rw [rsT_rsT e.ge (m.preimage_mono hO), rsT_sub, rsT_sub, rsT_sub, rsT_sub, rsT_mul,
          rsT_constFn _ l, rsT_rsT inf_le_left l, rsT_rsT inf_le_right l]
        ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← h1, ← h2, ← h3, ← h4, ← h5]
      ring)
    (by
      intro O hO f
      simp only [rsT_zero, zero_mul, Finset.sum_const_zero])
  have h0 := congrArg (fun s => rsT s (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j)) (congrFun hu a)
  simp only [] at h0
  rw [rsT_rsT e.ge e.le, rsT_self, rsT_zero] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.KS.LinDir
end
