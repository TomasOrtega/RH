import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply stalkLinear)

namespace GlobalTheory.VB.Ker

section Algebra

variable {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

/- English proof (translation)
Establish `h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a = f (Fintype.linearCombination R e fun i => a (.inl i)) + Fintype.linearCombination R t fun j => a (.inr j)`. Simplify using `[Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]`. Establish `h2 (b : κ → R) : g (Fintype.linearCombination R t b) = Fintype.linearCombination R (fun j => g (t j)) b`. Simplify using `[Fintype.linearCombination_apply, map_sum]`. Establish `h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0`.

Use `congrArg g h` as an intermediate fact. Rewrite `this` using `[map_add, hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2]`. Conclude with `ht.1 (this.trans (map_zero _).symm)`. Prove the components needed by the constructor for the conclusion. Use `fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩` and prove the remaining obligations.

Establish `: Sum.elim a (0 : κ → R) = 0` using `H.1 (by`. Rewrite using `[h1, map_zero]`. Express the relevant statement in the definitionally equal form `f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0`. Rewrite using `[ha, map_zero, map_zero, add_zero])`. Conclude with `funext fun i => congrFun this (.inl i)`.

Take `⟨a, ha⟩` from `H.2 (f m)`. Rewrite `ha` using `[h1]`. Rewrite `ha` using `[h3 _ _ _ ha, map_zero, add_zero]`. Conclude with `⟨_, hf ha⟩`. Use `fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[h1, ← map_zero f]`. Establish `hb` using `h3 _ _ _ ha`. Rewrite `ha` using `[hb, map_zero, add_zero]`. Establish `ha'` using `H.1 ((hf ha).trans (map_zero _).symm)`. Use function extensionality and compare the values at `k`.

Break down `k with i | j` into its components or cases. Use `exacts [congrFun ha' i, congrFun hb j]`. Take `⟨b, hb⟩` from `ht.2 (g m)`. Take `⟨n, hn⟩` from `(hfg (m - Fintype.linearCombination R t b)).1 (by`. Rewrite using `[map_sub, h2, hb, sub_self])`.

Take `⟨a, rfl⟩` from `H.2 n`. Conclude with `⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩`.
-/
theorem bijective_sumElim_iff {ι κ : Type} [Fintype ι] [Fintype κ] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (e : ι → M₁) (t : κ → M₂)
    (ht : Function.Bijective (Fintype.linearCombination R fun j => g (t j))) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t)) ↔
      Function.Bijective (Fintype.linearCombination R e) := by
  have h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a =
      f (Fintype.linearCombination R e fun i => a (.inl i)) +
        Fintype.linearCombination R t fun j => a (.inr j) := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]
  have h2 (b : κ → R) : g (Fintype.linearCombination R t b) =
      Fintype.linearCombination R (fun j => g (t j)) b := by
    simp [Fintype.linearCombination_apply, map_sum]
  have h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0 := by
    have := congrArg g h
    rw [map_add, hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2] at this
    exact ht.1 (this.trans (map_zero _).symm)
  constructor
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · have : Sum.elim a (0 : κ → R) = 0 := H.1 (by
        rw [h1, map_zero]
        change f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0
        rw [ha, map_zero, map_zero, add_zero])
      exact funext fun i => congrFun this (.inl i)
    · obtain ⟨a, ha⟩ := H.2 (f m)
      rw [h1] at ha
      rw [h3 _ _ _ ha, map_zero, add_zero] at ha
      exact ⟨_, hf ha⟩
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · rw [h1, ← map_zero f] at ha
      have hb := h3 _ _ _ ha
      rw [hb, map_zero, add_zero] at ha
      have ha' := H.1 ((hf ha).trans (map_zero _).symm)
      funext k
      rcases k with i | j
      exacts [congrFun ha' i, congrFun hb j]
    · obtain ⟨b, hb⟩ := ht.2 (g m)
      obtain ⟨n, hn⟩ := (hfg (m - Fintype.linearCombination R t b)).1 (by
        rw [map_sub, h2, hb, sub_self])
      obtain ⟨a, rfl⟩ := H.2 n
      exact ⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩

/- English proof (translation)
Use `Module.Free.of_basis b` as an intermediate fact. Use `Module.Free.of_basis c` as an intermediate fact. Use `Module.Finite.of_basis b` as an intermediate fact. Use `Module.Finite.of_basis c` as an intermediate fact. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property g LinearMap.id hg`.

Take `⟨φ, hφ, -⟩` from `hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩`. Set `π : M₂ →ₗ[R] M₁` to `LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap`. Establish `hπ : π ∘ₗ f = LinearMap.id`. Use extensionality with `m`. Simplify using `[π, hφ]`.

Establish `: Module.Projective R M₁` using `.of_split f π hπ`. Establish `: Module.Finite R M₁` using `.of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩`. Establish `: Module.Free R M₁` using `Module.free_of_flat_of_isLocalRing`. Establish `h` using `φ.finrank_eq`. Rewrite `h` using `[Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c, Fintype.card_fin, Fintype.card_fin]`.

Conclude with `⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩`.
-/
theorem nonempty_basis_of_exact [IsLocalRing R] {r s : ℕ} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis (Fin (r + s)) R M₂)
    (c : Module.Basis (Fin s) R M₃) : Nonempty (Module.Basis (Fin r) R M₁) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis c
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨φ, hφ, -⟩ := hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩
  let π : M₂ →ₗ[R] M₁ := LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap
  have hπ : π ∘ₗ f = LinearMap.id := by
    ext m
    simp [π, hφ]
  have : Module.Projective R M₁ := .of_split f π hπ
  have : Module.Finite R M₁ := .of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩
  have : Module.Free R M₁ := Module.free_of_flat_of_isLocalRing
  have h := φ.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
    Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩

/- English proof (translation)
Rewrite using `[← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination, ← LinearMap.range_eq_top, Fintype.range_linearCombination]`.
-/
theorem bijective_iff_isUnit_det {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M₁)
    (v : ι → M₁) : Function.Bijective (Fintype.linearCombination R v) ↔ IsUnit (b.det v) := by
  rw [← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.range_eq_top, Fintype.range_linearCombination]

end Algebra

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

/- English proof (translation)
Use `choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)`. Establish `hxV : x ∈ U ⊓ Finset.univ.inf W` using `⟨hx, by`. Rewrite using `[Opens.coe_finset_inf]`. Simplify using `using hW⟩`. Establish `hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i` using `inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))`.

Conclude with `⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩`.
-/
theorem exists_germ_eq_family {x : X} (hx : x ∈ U) (a : ι → (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (e : ι → Γ(F, V)),
      ∀ i, F.presheaf.germ V x hV (e i) = a i := by
  choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)
  have hxV : x ∈ U ⊓ Finset.univ.inf W := ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  exact ⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩

/- English proof (translation)
Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply]`. Use `(RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Module.Basis.toMatrix_apply]`.

Use `conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]`. Simplify using `only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]`. Simplify using `only [← he.stalkBasis_apply x hx]`. Rewrite using `[← map_sum, Module.Basis.repr_sum_self]`. Both sides reduce to the same expression.
-/
theorem germ_det [DecidableEq ι] {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U)) {x : X}
    (hx : x ∈ U) : X.presheaf.germ U x hx ((he.basis le_rfl).det v) =
      (he.stalkBasis x hx).det fun i => F.presheaf.germ U x hx (v i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  refine (RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]
  simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]
  simp only [← he.stalkBasis_apply x hx]
  rw [← map_sum, Module.Basis.repr_sum_self]
  rfl

/- English proof (translation)
Rewrite `hv` using `[bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he]`. Use `⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _, (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩` and prove the remaining obligations. Simplify using `only [resM_resM]`. Rewrite using `[bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)), ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]`. Conclude with `(X.toRingedSpace.isUnit_res_basicOpen _).map _`.
-/
theorem exists_isFrame_of_bijective_stalk {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U))
    {x : X} (hx : x ∈ U) (hv : Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (v i) : (F.presheaf.stalk x :)))) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame fun i => resM F h (v i) := by
  classical
  rw [bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he] at hv
  refine ⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _,
    (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩
  simp only [resM_resM]
  rw [bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)),
    ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _

end GlobalTheory.VB.Ker

namespace GlobalTheory.VB

open Ker

/- English proof (translation)
Introduce `X S r s hS h₂ h₃ x`. Use `hS.mono_f` as an intermediate fact. Use `hS.epi_g` as an intermediate fact. Use `h₂.isQuasicoherent` as an intermediate fact. Use `h₃.isQuasicoherent` as an intermediate fact.

Take `⟨U₀, b₀, hx₀, hb₀⟩` from `h₂ x`. Take `⟨U, c, hU, hx, hle, hc⟩` from `h₃.exists_affine hx₀`. Use `choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)`. Establish `hex` using `(QCoh.exact_iff_stalkLinear S).1 hS.exact x`. Take `⟨β⟩` from `nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)`.

Take `⟨V, hV, hxV, e, he⟩` from `exists_germ_eq_family hx β`. Establish `hb` using `(hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv`. Take `⟨W, hW, hxW, hv⟩` from `exists_isFrame_of_bijective_stalk hb (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by`. Use `(bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β (fun j => S.X₂.presheaf.germ U x hx (t j)) (by` as an intermediate fact. Simplify using `only [QCoh.stalkLinear_germ, ht]`.

Conclude with `hc.bijective_stalk x hx)).2 (by`. Rewrite using `[Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination, ← LinearMap.range_eq_top, Fintype.range_linearCombination]`. Conclude with `⟨β.linearIndependent, β.span_eq⟩)`. Use `this using 3` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.

Use function extensionality and compare the values at `k`. Break down `k with i | j` into its components or cases. Rewrite using `[Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]`. Rewrite using `[Sum.elim_inr, Sum.elim_inr, germ_resM])`. Use `⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩` and prove the remaining obligations.

Use `(bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T) (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _ (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_` and prove the remaining obligations. Simplify using `only [appLinear_apply, app_resM, ht]`. Conclude with `hc T _`. Use `hv T hT using 3` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Break down `k with i | j` into its components or cases. Simplify using `only [Sum.elim_inl, appLinear_apply, app_resM]`. Simplify using `only [Sum.elim_inr, resM_resM]`.
-/
theorem isVB_X₁_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₂ (r + s) → IsVB S.X₃ s → IsVB S.X₁ r := by
  intro X S r s hS h₂ h₃ x
  have := hS.mono_f
  have := hS.epi_g
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  obtain ⟨U₀, b₀, hx₀, hb₀⟩ := h₂ x
  obtain ⟨U, c, hU, hx, hle, hc⟩ := h₃.exists_affine hx₀
  choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)
  have hex := (QCoh.exact_iff_stalkLinear S).1 hS.exact x
  obtain ⟨β⟩ := nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex
    (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)
  obtain ⟨V, hV, hxV, e, he⟩ := exists_germ_eq_family hx β
  have hb := (hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv
  obtain ⟨W, hW, hxW, hv⟩ := exists_isFrame_of_bijective_stalk hb
    (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by
      have := (bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β
        (fun j => S.X₂.presheaf.germ U x hx (t j)) (by
          simp only [QCoh.stalkLinear_germ, ht]
          exact hc.bijective_stalk x hx)).2 (by
          rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
            ← LinearMap.range_eq_top, Fintype.range_linearCombination]
          exact ⟨β.linearIndependent, β.span_eq⟩)
      convert this using 3
      · rfl
      funext k
      rcases k with i | j
      · rw [Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]
      · rw [Sum.elim_inr, Sum.elim_inr, germ_resM])
  refine ⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩
  refine (bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T)
    (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _
    (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_
  · simp only [appLinear_apply, app_resM, ht]
    exact hc T _
  · convert hv T hT using 3
    funext k
    rcases k with i | j
    · simp only [Sum.elim_inl, appLinear_apply, app_resM]
    · simp only [Sum.elim_inr, resM_resM]

end GlobalTheory.VB
